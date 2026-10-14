-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1637
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:59:15.131405+00:00
-- url     : https://prove2.me/submissions/1943f6bf-71ca-4808-b530-6cd5a19f458b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 294244604 ≤ n < 294424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 294245854 1250 294244604 294244607
    0xf090809220e0a020a1a0313061830080c0a020102070203030d0c08162a02040c020105150901150c02150307032c07060f0c02090c0706050c0c03040303030f0e0a0507030b090d 76
    0xf00150031041d6440345070383d074a401c0145a8100c3c07002103541c03c01940743c4101924005121032207d07138bc0e07000d030540c003105040d070b0142c08068a0040c030140707030b559469240c503804001c0c6104d501c160720803011950200051030160310104002d10100b41c421700c0010344214000c00041808101a00b00460b10807035100301e020145d400404400114107030b11a9140e090414064488400d146d203c00035001402d010b0720b490626010b61000d44a0110f250303000203008203000c200a00120b0034001c10501e0500701c103041440e184a45650005c041c03024115200a0003440807003040e5420854010001a03100c280d81c0308816002c13100005601014000c2a03100407031402c10985a40890041004104141401c400300034410f422581e21170f0b40140c102d441900303000740024141d601091050340c3c100e0030940070070a8a803807501202d4891042c84051350420303003107030b030200c0241002d00c5400b42060f4484542129040092001c1d540c500c0c030030750003440356514520341440f80b09001040ca0b13166400002d410010070303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 294247104 1250 294245854 294245857
    0x290406050a05030a0b12070f050301090206120714040f0819110108040519060203090106060c0f0f020a03020603091c05090a0b07060f020a0c060f090809220e0a020a1a 73
    0x200751070911030746943d01d10803140024004901c0481d88101d50200403a444403000c40d104041e02c3c200b030000c50199841e0300a060a03240c4428009404c80700400100003040321070707a03010740c001c48a858444468000c81000062982041d04411881050007804000044040100444c030442c1d042e10041e0614550322800102401001e525050001013000601008010700060712b081d01c080c50040c80c0017445050600080d041120a410103611f80100401d04174040c99070a60003070350120114900840c81d64450703480c3c900482040307030004150b00010005075140006944501c400c00001c0c036454a0080260241c4500884d084c0240030381003041042c0c540f103145950040e245a0304219907188068640b03d001402c6205160b40b00b54408106206416031000b51044480c1c002c03a0180310b58240125940100d40006000900910041000d501c003400d1503030880003040e44411500481d030310099000001d48821003060911b50b00000c41d07003000c5142140741c080162004135840c100400c0c40d8007040c55107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 294248354 1250 294247104 294247117
    0x160906170a02070f081b0618031e0712030b03100501080d030902010e0a060306030308010617070311090307080102031f03020904080702120f0c0a0e0906060613090629040605 76
    0x95000610321081c8245101d0303400d54198041750103a90340185400d4a04400d1000e041e114460280501040c000c10407000340e0f08100d0050400f940c0392035207401e01e0385a02440c100b64100d0000f003e000b400d02141c005461020f00e15540d40300818050b861a04142c01d00d0044140d902d00c5628000c010300a6800006407454414020f0400141e40318642c00182c50020184460382d5012040c00800314402fa4150488400c8034440c8d21040c0650b6242e0744145c40c5061440c48aa0030141080700240503103200313070840921005800300b00d42c5011030810102e420851660003c0b51203a4001040c000035000c02a0b0300c550680d15041e150100c1829940000c501d400040c0c0041c0082002003251303803d5550f0307500c54807004014407003210351070502000415200e0560741081841800021000142c0100043c200c44c03060341c0d07100142c2146c1c1d030307218200001d40c1c00c00e507100f80000141000c0400c1e4000c1c14801d4030068401008801c0d0304410030010740118428403040030301c0842003070000304005600002610706 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 294249604 1250 294248354 294248371
    0x7050c04020d02040e1003021f1b1a070f2303131103060108010605041404050d0c08040b04080102031006020a05030414030c091e011e05041d0616090617 67
    0x2a0b5800145066002e4060b03a040501c880b040e060a00400c400307134821103c00c403032098514a07480ba611215601030310b041040398802091140300411800e501d07041c1403200c110320075842c004c0c2100c0c07142c8507005e0b00d140450b07001000c00c00400704035244035008252111054a14000c10711b981410800800090001070154049549558249002c004000703c450340c0045000d000c80b80c8969403400514040c003100d21460b4022441c0c40c4030792002c02040c410542c0324640180041000740803516044583d43d03a08001965a00c01c00c0c413000c40d0080c2d0302c10040000b049140c0015850f03040c401002d008800d025403113802954015000c4000241000c4196000c07545016603504c18566000d0121341460010035025501803441805c111400104d0140d080c51550a0505400241c1c0c0391000e441c5207807042c0c04c0005814050b851f0400c86490150001850307030f0318882582840020200c040b82c5041c406860016081d07035900e071516143e40d0310024150092007145009802036805004a0010b584003920080c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 294250854 1250 294249604 294249607
    0x108030403060509241b07020a050906030a02041814160b0f0c070609031505060a05040b0102100c05040305060708060a030f051603030e0a06020102120f0403020708070b030a0f0207050c0402 83
    0xb1320402d810b220400d18684038084030785c00049a44400000880111441540d100050701d03010a501086800d407603d50303502404110105042504000600e18020103544c0d140c1718600b42100180c03503a00402a40300300c0b0907400401340b0090324146001070b00540b0104500e80c05030429800180341078008034100c80d40c48400790b80d591071002c000004c2d480380c80402005031003a48000110a0343c88801c11013224060034800c446005030781c41013025030700240c42d81c650140310041c00707220030b140942c440e2400020500407200341c00032448044059032800756044001c204045010003d1280500040760300040c1392512601602d0b11900043d140341a50101500711101e003240682041030800005400e0129102c040003c0b0ba540e01c3c3c010400b0350581101405004000c20000381203005000381c403088002803000360215540c02c619900100001001a803c41c41030500014840d1010310824020340b0041400c140d59180a01e50b400540e18800b101712003862040100b6404a003000c5507443c0001f00496016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 294252104 1250 294250854 294250861
    0xf0103180326010b04181407080601030b030f0c040e030a0207030f080403150608010609021608131703030a140105090711030f130305010e1615021c030506040509030301080304030605 80
    0x4030507200c020504600340d110b0880003c01d5203031403100039008a6081401a03405151041c0c2e02d802551511081c001d0031018480103c0d03400c60080307414070f0344008189000200000003030f0019107040c0a59000c00510380001a0840c49410240601c81441006000039403501c1c01c0120000d640d03500600c80600841030644032001000b4084003120010750700103200000510305540c1302c00007002944900c24956181080000d2800160300176a071249615030702c181802c809a4581800d654000d80d04526030104040c808641400c541e070107040c000312010010340c0c4a1522105000455175104c0004800202640041002d95285050301d54007810501c4c0100181d0200201b00c0d00c0c500501080f05514030300800d4038840d5000032615642103d002d28000c0c440c2c0914164544d840b508410342e0300c0e5610080d5481841004001260405940c10503c11030390820500c4d004500c00100d80fa4000c00065121000e00056103002d01600780c01c000d503040030f145554505140c00f0394920075440010003058480001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 294253354 1250 294252104 294252137
    0x20f120f1e06030c04020a1805090c040513060f08030d06080c06042102100f03060b0412080c0c090408090906100e0d06090c0b07050601090c09030f020616110f01031803 74
    0x2c4d4104448040c10542d140d00862402920718908003c08540103803500000242d1131401500d05401048000085440d19080c641030041070030314000c6100c1d6680d210301000404002290a40c002000c1023000f8586400c3c0c0050301200741c856503408150305900201d042c031091740d10002101c003100c0d0304900545104101c60301d070781c110740c0c800d501c080e500111808140302c11503004040000e41c06206da60400c01a07449000c0f121b0f0302c3c09035005940e04159200301c8400015010070040c4140b01c800d6040340c445800c0940040c072031001c106c0e82100c0501004c02c10072194103040310703c1900000e007241c458900d0600a4001001d01ca491221a449803040d00003031801e1003c00d03440302d0344a641007544003c1d01500d51440c2c40d8943d1020100321050300c11440006251407142c801c20140e10120740d00d2040503413039500c2c2c1d030200f4070640c903060780c1c805010001e1110700320a605040300240d102c2e00711054841840d8040120804082c00380506050421120009226080310308803d076a034107041041c43c41d0b101214 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 294254604 1250 294253354 294253363
    0x2130506092806020c01110a140304030506090d1103091810031509052a1005040905131401090b06130209030a0503123301050d020f120f1e0603 63
    0x1840e07024200484a002c2e504110520002c00342c41c810703022529980700358401168282d2450300e85007060307000705900200080200007420000c04141c0c0450341850b40b00d4440504202c81501c2c1a51954083d5030301c0102a5009101101d00001d403801039410101034001180051006c0d0400c0720505898900044826681c46041300146801881001011282084050040c81c0d883d8040c1c5061251900c00c060300d429200340081d032180c8094915000d5200ba0b420311201e00d641803c0c0e0018841c05100101d141d07407151058910032840031031000c036800b00c00e0506c083c0410400c50fa1000c00e034109442e03100801d0f101c1075242d4203d0f900b40d40050080524107142c40082c01010301c80359241c040c030700c2117a081c080b000000d0006030150032081031a83c0c40b40b400c40402c2007555645508030507200301403802c0c501144007820390301d480c060505514100420048404030707401807082240c4440701107403100c800001c2500540c0d00c5031660701d0054050801100203c0c041c0003410840c8801120a40014a2130700c0500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 294255854 1250 294254604 294254629
    0x90d080c1908180f15060303040308040905040c0509040305070204060f0b1b010905061003060b011e030b03070308130e0f010303020c0603040303020904060e041101020c100e120f06190213050609 85
    0x10f041d280340c48141050561034031030301d80b0026411004d01020404030f1030040210303812a0740c0606035030311b0039207819880009444010000d440340031300700100149a031556a1468070440c42950b03035580d550300a10410049036138507008240d880445003810b20000440c13104803210b443c0400c1c400340744410740e0b0003614054058020001d140703014182c05d02500d405456200019030748103050a08c0155041401141c5001e460840000809680d901e01072540c1e000f544200301d901c0e03000d0140c0740d49a40b281c03241e0358260b01c5007142407035444120604100e250000440f02d078002c038107228043c0c61545036440007590f8040e8092694825000003010030201800b0340d045680b0400007a006001c10307a5a41e0b40301c1440d66089505640071000140800300e80e40c40071a0110000c00700070550418120408021a4840d601890741c0303421485070940c160024600300441c2011070700d50002003400c2d180c852440c47c01000200c1c801c9082c6070041c800405010a80c0391558299501544d446403621114000112180b00c0c28 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 294257104 1250 294255854 294255901
    0x206180106091416030b031f2319060e04082b02180f0a0b0c010207060e06070f0206010e070f0504051804031416020d0812090d080c1908 60
    0x7003c092003540e6580360f9074480c821940102c9104c42d00c04a040d400d46030b071041d0065158020343e80100c030b1400c01c4030542181c0010440005a001e04400f02c07681c0307800d0403c0c0c0d01200080c0b5032040200c40c079604014004900d51981c018000f0a252001c0c902ca801c1c4050b00040c40c08101190702d01015510b0032300a001d4143d00c3c40343e007040030f5080000c90025404402151004d44406031440d156051401d0503002280c0040d00144c001880d10322030004503001141002502d5408220b400d01103402c1d4010b44130070218a001901403810520009011480348640142c10764000c000100020301d2503000c1c0341da1000d001d0819149424017000f04440074030840d04800e80c08841d01040c480c502c443c20742c80c01e00c1284240c48200700c2601642401000c1c1c0689042040459030100c045c40c0141000850b500100b80300d00005400c044c2075158165480d04100d40b01a1107502160000e4071329540b150a603078000120b4100149050035070781040d031810500c40318540910107148003150750100624800640403000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 294258354 1250 294257104 294257111
    0x60203091515010210020f0703030924051f060f0305041e03080702010e06100915030812070f0e010914150f09010e0a05010801030320010207060f1b020618010609 71
    0x3210b004401c2c59070300003101c0c014420170300f051008101e140300310b0b00a00c5003041c0990805c01c4035034044000d44141441147d0480c00c0210040e041010038280c10140070004101042601d0b0140e50030045c0b241d50781b40103401c40c40c41e07481080003541080c1e040070003014a1074046116603a50a06031281d10f02c0598215407011221030807030a145d4004030541c0a20010380c02440310984110044c0c4c0e503060152156502c03250002d07002c200b038482592100d00d00c502170480d100c2c01150b6035254541103030410549a490365020300108110300341c1c014030806da218628103201ca00a41c400d0002888601d00c1e00850091004413221000c00c0d80d9028445a4522035440031a40c1c1c0f034014002c65403c41c0c120030545800701b50354140318503451414007140d0050b504180c1d00c416461f0301e580c90440e10303c02c083e91680c100391115440c241c51048203000405005000f801e01082c0f41b2446918481181c1d2000030b410341c41c846008120241c1c40d408103c0c5a040000340c3c0b40092018076003440c1c0c44c01007000d5881112400d14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 294259604 1250 294258354 294258361
    0x28030f0512040b03071205010503030a0f02010f020a0906080f190207062921060f1f0305010501030c140d02010e01020c030303010e01050916020c0907111929040602030915 75
    0x441d50055105e40c400d80d40e840c42c00c80a4000d07610503502d082c042c0710707403580050101944680c401d02000300b4004140c800481e07601a00017510040368090b000290014402110600240b500300c1040c0e604216050900300003481d01d10b07003100c00d88100042c168010f5800007080010310411750000c510b0041d89080250000001c4105072a074150781d640101c0c01880050300c5580c26055403503103500c03540c550b84090203450f9500c0c0c5040381c450300001c04ea850701c4001c903141c003240f04110f102810701851150000040c25411410005040e503550743c0b00030071640310030781a1382040d200c810200014542c217081c04403483d081c0d000140e0030001840401c03034052201200000f16004d405030707080c0c102c2d6000d8405440b562500c000340c140300364840c01404096070140750110000d0800080c1e6652142d090320b070880b8402c503088805401d02008040d00c2c44004c000a01c0344041c4405500180030207220341e10f854424a160b400c0350b400c9900024130140419a020001403103141003070042d0345403110450070f20700bc1840c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 294260854 1250 294259604 294259619
    0xf050d0b04050711011b0804140a21020106120809011805150d0f1103220204050708061002011e180203060103030903060f02072112020309010b28030f051204 69
    0x461007442e4003a40c20800b40b045100702240e00d450400d45e0347c0d0f03039409042e9503a840e90400b0212020744806540328000056010603d0ba661050240032602c242070f60301c1c100040003d00703481060300b00c1c6258500b110740081c00519101e0881d62100c80c02e0900f07202c501c0255605000d20982c40e8030082c5c00008502d0341d402806070740703401805401c400d41c0e01040844540b11690088611078207000e101800704102268482c0c0c01640c2040c00d5002203ea1000006080e41c00b05007074881c190b0700c0102040045c020f110052500d916440300301c0c01c10388001c0100e41e0900d850003107280ca8110740d542c41c81e80d440b1a144c986510710754080b00d031950060203c8040f965a894020551451484142d400c2d601d005070041482031300e03000310384100d40c11200c100380b42d440c22218205061036545500084c041c14001070000b00c405400a58414540c000c00010900391103400d1043c82011035005e040c08140c406048015000340fa02000203507a00301c000416520700900d0082e2810102505e14a9600360210340010390300b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 294262104 1250 294260854 294260867
    0x6060509040f0624023c030f0a0c061a130b01050d060303110d170408160209010f15020f060c0c03040b0409020a120213090f2304210f050d0b040507 65
    0x440103a00300c6004038076602001c9404803200d07500080000301100c1203400c0040c0d010b4114101a044811f60f4940038540f03080d84125803022040002040540d01c0000511600d4410f03101e000c074505450640302241200042c01081d0340c100110300b0320f646c40ca21407000340d21075000d80b004580d400904004440c0c0303070305001c0c1000360f88940c6a201445550485440316115964001c3e0a042d45401403007541c48035500c0382e40580050f0004903112907044503240261f51036a14103402001c21501c4400c04905101c030030400703440000001015940107205000040c0c00014005900c41840d1021a48034100e50305800d086104550245098050201e0086a400029802009102074684401028420740c419100c1680240d40600c84c90480c43c032000c0100b241d03d034018410b40b00c981c180c0001c0c803241056800a500c03680550303c040242c41c1d2000c110401c400610040c0044005500034850511a81001084214480a020304120307002c14082c0d0010f000780c05c000c01da60001003007030201c1d01d801807004005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 294263354 1250 294262104 294262169
    0x7030b01080f0c0f01030b1c0605060d08070f0c0302030303070503011401030b030a0318080304180c0306080d050c070b301603020c15010b0315030106060509040f06 72
    0x85411080000550241c0003401e04503200608010f01a240d001004101050590741145410b141e1a042042c41c5a6540c0c81c1000d8221002044034452103030f582050300c120f8070024a602d000e00b00b0940711102007101c102c25100607541c49204400403400c51b1414254000345580b00079014400032003486020354010001d54140c0b00c404c82ca1940c521140001181a10588001c071901904131080c05e501191040904170710207542d48550381c03d01941d036003000c2d1642d880b13070f4416000a9100c039071540d550341050090890b940e00c58a010301815040c20841600c620081c01100c00744940040d400c0610702050104030020160301d9445501c603074450002c14404000c05189a03403c00c100c43d20260300514040e0400d000f034154003030075081946040e10540080d40a44076004c181c0c444c2036215100d07040100100740c0030702401000c3c0b644904000281107987e089a807040c51090f41864000c0c02400c1d801801e88078103030700868001c20007200e100241801480b03113400c00440c40c40300110342c0c1c40509028000016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 294264604 1250 294263354 294263363
    0x3060a0e090a12090302060f0901031d1f050408030609070309020a03060b1003110f18060403050c090109020a080a0506010c0b101502070503030d110f03040b0a0b091b0309120c0703 79
    0x4510503102c3c0c0480300845140002540000d013800a41850a40640031b494440c40c1070500080c83c00742100d01e40103d02d00f5000b988469440100c4117400d14060318110000400c03110380c244030074109a96080c1190200a0601e401007803201c0c000394400703109402801e050394028200040141c1c80f410414050318010000d28020001c5510580b0514403e10418100401150b1030506017a800c580c1084941c0c084081e41e0031a0104450100b6a661918001d2004611800042484d10804403e0003400c0005074488220184103000c05e44d12560041583d60703128003400300c0083c0c150750b0040103030f400327881321000076012180c20020069407035061085802504c07000e204040f503440c003400040340c0d2003405000d050f806400a02c031413000070665411030b00d80491651040390404498202c207000035041298207035101c01100050200306a001d2158000b024402d8454a6562500340c0714026141c250b51420303c2c404000000103900c410040c041c81007100c84220096994440c00f20156a840b0a40e000598 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 294265854 1250 294264604 294264623
    0x21c0c05120313090b030f01020d0606031506080408091c060506011e09030f0c0816050f0604122003010c05070b091f02032a0726090603060a0e090a 65
    0x20507180000050b40c01d0b0786114803941d60400d003810380320b01c00703400c1c91580990580320380301d000ea03580ca00138005044010b000c3d034800101d1b545000c1000f0184e5a15101440d081d100e000d200340012540681c01da540650865902d0b5541c00140e03001c100014000c4640942d04001000ca01c402c0081ea5080310b4043d4100b6079610710f604047c1980500f030054488080c002144801c203080000a000d01810f6030100e004492000c0c030349603280c100c6800c0007041c0b011410403147c0c000c014441460490154a0822802c3d42c41504050034210744643c03148040d04040c144e0305038040c03925485840d4100c1c02001c220041d00070b22205401400c09041500140710032104000b154001510000001800c0011203100041c2044d081d40c002500c00e000b540082c180d8030304105000c07640310116100c60020b010500c4d00c007880b0b5640b8507403403c140e4550702c4c2500c0c40300d01407410514a80c0d50100f5240596201650480d4981e90300e1b1501400580561410b9000d9058000140308200e4980b80c0441d503a00050700440108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 294267104 1250 294265854 294265879
    0x307060b1e0d06020706060e01030c0605040315180203031309050a02090105091002150c0408061005030c0103020f041203030207020307060207060c030c02040b0909010e0c0f0a0909021c0c05 83
    0x1081240a07810000c44a079000100615180381c400c000c0d41c03055003d26001480c102654660740d099071219040107000b517682000410810110001040c020001864003d0425085603183c1e1702480c02c0030441d200e2141c84221034400c0d0000031600c0c02800e540101169500c000b6006c0481003461720344265000f50785070900003002094540200c1d407050340165039140c600001d84003044002c3c1c001990010451090f41000210b04440d009880e000b0840461a551902c0c5030031010703890000004c10307240041c00d4250080145842c0010301e4801c003842420302503260320b00c4543c0c01221780511b03444580505c3c0d03030424031000d051f015401003000390700a07001d0321805510351409030ba0701c850b244a0040080d00f03803040d003000300788100b544da43c0f0180300030b001141c41c20030740d00040c4082105940007215659503040740084ea0314208081c0400b0801912050f5444410702d00103400307840540b21790b541c0e55131942400d0007150340e12a4030241d201024083c80c80094a42d04048030301c0b00640c042e1900803190000c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 294268354 1250 294267104 294267109
    0xa0605010e0603012108040e06101107140402070b0114041503080a080402040e0307030f0906091a0a2c0109050904080d0f02040819050c01080c030714070f03020307060b 74
    0x3280712400c0c003070001840c1d0b9207400300140c14800080100381c0c10350700d00c4000a00180220005000400c00ca4000d2646401e10710104445c1d084200805424010400e4152440041c045403007405c80c0c1d0000d82e004030702004000450064071860700000c4c02d40b00100001708003880c00031500c43c50f000e0150b804100700f400000c4580c42c440124040900820004e1050100d01c030f118038910b5500c1480a840480c0052103022414034681041108401190441304504082c03903100145c4d0000700101c0c900314000c603180a000c9030400000c030b00030b03e500f51400241c206e030107800b07071100700081d10f85070844090084d80c1003405a2034801c2c188049000070311a80300004e05141c8004580c5c01942c01c1001c403894859024440401412451f071403075039140d0207201c0060b09540504c400051024803100e640d0808110786881030604610300e80c4241400040c000f441004001c1c3ca0541c0c0d1b1000c8181030092117400141d110514501071950f000b0440100760103507108069020000e40107191060347c092000c15106000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 294269604 1250 294268354 294268367
    0x10030515010525020105040510120b0306060d03051809040f0605090c1c030e0303030c1b01020a0f0f030603080d0c18080c0103090807020d050a200f0d1a0403080a060501 74
    0x880d100344a200303102d04007500780c1a2280a40f544141011464142d880707021504041c0e84402e0003011542c01e4170640400052402281411a401c5015040501e400b4001522403a8100000b80400c100850024900d000c0c0c1811501c00c00e0000380703600d5a500d010b2400300041180030400301d41c0a400c050102d030b4a020001410314150900404084060050704000c000c1d043c8000c609404004038480f4130646e5460500007540640080c404640d80c421401d0380f140751940d144001c4051503072040145041d01584500d455801c1c6d03816261078007030500c44043c01c9000d02841e40018040c8038000440300480003803036201e221701840546410001c00c64080c41d9215007480c4d031052108940140c1c100d024158841d07801220000c2c07280c002d2a00f80552034001c100e441d447e228089502c0e500403c200b0007440b8800e41c18103e822881c4088100c80d4400e0004035240170016040305d030140c44024103841c1044005140c0000c50b524004040076a03180c02d00b0010840c1c14191800da04152901d2004240c40d48900c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 294270854 1250 294269604 294269617
    0x305122e030309060f12060807050118120308060d0501020d09060c0c02030604351b070b070609030c050303070201051f0503120c03070f050c090705030108061302010509100305150105 80
    0x310b502d001246008815070703801702c00d03008000c100102c0c11241003150380d0500c2a04080e106210003814928103210000d01007103c200072246416011080401030b0a48040d920008564145000380f07403511980c0104010f000051341c01481940085000300c04107a203980004c600030300415042c03150b0b20500d1400d8a180d800043c0c06034154004d040010041124162004124212000c601d603038400c004d40300c00804d54500c0050701143c880040d991a01400d003409803003480901c9030180200a02d800c000050a20034a4402440b00d03880b0780040050501031071f03410f9403090f00001940e0352071800d610000d0081404988550f40482c0450142c4804040ca40c07810050392070242c0107007407181506034525083d810070568140d540c0301c01c002c048001581510043ca11324030070401410403449400401070400001880382003041000d0004005a84000420b990072900b9003014540ca503182d800121034500c107402a16811890b242e100114455140e07000e10302c01c00300741c03c04242c2c2624040045480b03100c0d41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 294272104 1250 294270854 294270857
    0x603020715181b090c020c0901060314070e1302180a0f060c0803041110050c0d081302060307030b0618090a0902030a14070312030e060603280305122e0303 68
    0xa0401c2c00002d00d0f0f2042c1c00350030b0710408100381800d55580c00d260003139407080284200180c00842c0000306d0707810076040d964054032046c20107102d41410908031002c80a001016001040240280341041d51924a01415440080c400c255031761642081c0403004291a60034407409000c1d240c40001d0701c0c42d40882c400701954810b41e01c07100b030401c1544924815030005042603910882c0d04541c1600e53b960050f42c101c1c51011500da0359250714070b800b1031600701503403060542e0174801c0100c100150f024039103c4825056504440e080d40360b444405048008200d60541d01d6000000000c4044a000c400c5591420b100c208840c46003017552214601c8040e1021008001c1d01607000402050000d00100309615908d000c007021140440c1d41c079101d402c0002250030701c080c0880d81ea408400030f400024880280d2180b02900100300841002c1c0d00c1585112a03640360218000c0b2003141407007054803031030441c1c038040c080300c03401d985130b003001454481c8000d0400a1529005031040d9010448006443d0403000c480d0503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 294273354 1250 294272104 294272141
    0xd2018010206010b0a180e01060807020f06060901050111011506120608010b0d0204020715050708101203021b0d05161e0321200105060102070b070809040b0a050a0603020715 76
    0x2441016201e1207843d103d0750204411481000c07e01c044100c0000380200035903940c001840c1021940641054004035040b485904081c0401086494103803080381100c07000c1c60000103085c403030001c00f40141300d1030b00f4201d40725242c460001506988144a4000034280003801c00c12540e40d038096900721151881000c1c1c11442c4a404500940b03442d5029203a07242c0502c403000e801c038030b070418460215070040b109100400d03003c0303080c4292903080702006005044204217510003c60356440103036071504002140c244a17400a60540410380700d12481b141c0c1c803503201c400c4401c80607003448000100c8040d809040381103045520304800d20681c0800710421244c0207003416134124440d000d0810120040070041c1c0620510302007488001c258020414446901c0c030b0000102401d0450009062040c071368805481d02d0070602c414804103001008aa40029041750005030024a00c4089801e80c00d03a6440641d1003200c1e0b007000114250150001c0211604c11003200f503144041c41e01e0b207070880d458043c0300000b03e0380 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 294274604 1250 294273354 294273367
    0x10509031303120e0d03030510050901060203030f0a1805060a110307120905150f0f070f0f1b0c0807080f0a0816020109051005180f09040201050d2018010206010b 71
    0x1140700c2003c615081d901d02035982c9452480480e8010342d00b001c0c1200025070b038108102c0d00c484100013800240900f25401e40f07880d45002002503890201802c0411910342550105070510750560124815400f00300007506074003a5410119101d41085540703003600c40c103000d07809000002041c02c43c0c0c07050302c61340c542c46541062210890003c0020403001c517402e100c1c1e0118551400b080c4c0b203001c0c2c86189012106901881d1884a42c0c4501c0300c003411060070300021100307400e48541c1048454601c0152860b06511900d640c1c0c1120422280707040c1c028002d0005c01c9000300c0c80d18008039910040e03807020021541c100260b402d540d643d40c40c80540140c26103006100000040141c801c03d40d0031180145440508107880c1c8000401c10a8801900c00100d07000054440241c01d400e000800c0314941118644401700c1220081850008010f01c024100000000c45c2509425160b110755072090141002c0101c00150b0340f0114080c2e400060180d8006002c1603850b000c030b602c0059603d041c1d4542c0200c640c1081c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 294275854 1250 294274604 294274613
    0x10081c1b0c0303111908090f150301180b1908060c120c0a1215051306051507081b010b0a0b030421050c01022212170d060e040f020102010509031303 65
    0x12242c01320300c05000308181c500315510b80341c00310206940609961580c07030b0795290801440f6141408880e014064101499641d100306406490440e46d0505242444110f81c200c100010401c00e11b000307900903800c82c0f680d0708002255186505031003642040b51082d85660303c1e180e016015400c441a220003140c00028034280541c005090403a589007890401c001d000c2051030700380e07040c02110f90301c40070600d0401c1115140400c81d12410200140c8100700c1c10b42003101092003004208807582500d980040c114041000d0fc01c1100c02610400110a9066181981c004c0c080d00c00c1c01d4030203100f6580c446010070442c4c11a81201e014a912442d480d010900100410344000307070007118103060003024007542c081360308207000420031680c500304211040368140250100c5510743d5080700d0941c1c20042d40e04400078006194407640c6049148a060f2183d00800170310014161a030002c00140081c1c20500003001000c400380f20036203100b41c009014a80d285070050f07035a4000c001a051070b090031520b0420128 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 294277104 1250 294275854 294275867
    0x90604050c0f0f0d050a0b011e090b060427060e06010c0209040510150e0108010207080f030c040f0305010b01030506060a0c1e121110060302090103030810081c1b0c0303 74
    0x2103202410008600c1c0c2d4040003d84c1c0940e010b802521203030800541d51080007100518a800340440380c84861440041100c90443e041c0c6d00e0181c4110315544655883c404d039140d105840c001c200801402014032403150810300d0104a0500e02c038000b0b402d01a020440260f02507841c1e1007404181d44140041c1807580030486000405030082d640c2d030017014401c2107440c241d8052181c180741e030710705071020661900c4d030003102c40d40050b80803641513417050001c3e5000038400011540914044e040440e00c980390701002000c544030703c3d4000344040c140c1c40000000c00074113400c4280c4c0c0802c00d803402c00c415502c03201842030f107100300c60b101c0001880300e0288000040d00048422142981140b924003614040e5a031000a100d80c5500000840c0000543c032010f45420400d00310340602040041c00307014513560109581e4a410f0200609020904000484003038001c0c10000080180800721640e2030740d0501c03004600c1c2461202d1400050020900792195003880c6880c221403540030748903c540c217156441c1201c44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 294278354 1250 294277104 294277129
    0x90b070f02060d060306020a03090318080a0b070e2e170c0c0a0b101701020708030604090203010e070b04050406050a1a07020d0c06050d0c111c09080610030b090604050c 74
    0x32140d0319034011003c251b035440a040c00b4503c030740700050540413500f400740c242000701c0001c0c40714000041d0306002c03000000c01d08480003503202c1d40011690b110450181d94080600d0105a0420441c9107031460340c5030780e101191044a209400282081010403040b110340200d6112240103c070b900000c2000403442500030070907262094291407030040d003a81c0704000c1c0c4901365907084822000c18000c5c000c4407070300e5240790340c0513900c580210310340a250361752a1501d02008240620590703039140b90200390348085d000048490f2020040d80c0790b0300e440340312012841c0c102d8040e86024520341080482e980c02d02510140035903c000c41120074441c0600c54030456944032000498029145004800c00288004c41c2c00000c0d004980f20aa11117201290b000c04446404801000704a14000000340041e004941000000c465985503250240700322030507510a00c0703d0b0f00982152259104212100e2080111241901d108180320b0032261a0382410580d6074400741d40107071152304007000c015914a0070542d020341 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 294279604 1250 294278354 294278377
    0xa08070c0b2a03090a0b070201080603061005041107060c030501080c03010c050d15050a0b0a03050a0c1d04020f1210060306060518031501090e010b01030608030a0809030c0a030f090b070f0206 84
    0x4e041500c0d0041805080300d0343c4552403200000c540c1c039046680000c0c9265020f8002d4004224901d0410140c2e50445200c3c0b00b5240100ea881c0380b2412005003000c110b40009800c02d005002e100458800100201400d10900d0000e000b106862951403506002c1d98001e0781c4141e035101e0030080c030080424000c0611300c3d40c03d542c03d54095400607082d10f8006370b507402000030348541c64503100c00242c081c080d1f80c00206961015490804045900f903081041d0442c1c10051841070905040e49502050091003034a9178070f0851040481d200e504103100180407441850700002e0308190540c0d4250907001d42e0014003510300403400503c02490b0050400c00707022004000182141d0101b0070b45594610500740a8020744016501e440b103296100e03100340138511350342c402842c042041618120b00980c8074040c1e03000c04410040c41c2c0010501c0c2000402c140d40b104003044084c0c5040024602d00a800b40d24107642c030700c001c00d00046001458810036026034a40c0380c0c00c829415600317070541d401c20885500440c032495 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 294280854 1250 294279604 294279607
    0x61005190e0c16050a050111120c030414101d03041a0325080a0b09060108011205030d05070509030d03050105150c1f020417070302031c0c050a08070c0b2a03 69
    0x80400750782840702e0a00400c09171481e8402800e06900b901c522070f01134200300404202e021494a0040a03040d0b0000c51540c00640b00d86652811001c0011754104e0619640b00c1c124680c89000c4441d8450415060150780d0448000807188010780c0700c0c0070340e00c6201c008007519448400f00100320070045500800078510030159940030407140030030400034954000000da46004000f0340f40594400d18003d0300d0225154102841c14000007030589405010f01c51190300200c20b02420003070304109881869550301024400c1c0e240440000300207411034044548070b03100780452904820701078820f15060300c0000d441140c0c0807600c9448040e155000403144040c40c452100150250a82088501ca000c80302c00320159a5900c1e220f1000408640f2070440010703038010520800040e0303400501564603903081c45d4511030440d90980c00766031424840102601500601d4611400c02848100a108182c410006c043c1e031140c403101750303080c01e00405000c0c1d00d11510203000f100808048840071040bd558000449 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 294282104 1250 294280854 294280867
    0xd08060d0f030f0f030b0d02130617030304030219030e060310170106080d02010b010e090406320a05060616080906070807060b0319060207030e12061005190e0c 70
    0x4000180e46070020b500140064414030351055002c54112111402460144005002c1400003081c40d280460001e2149440030810030111100350040401407603e441d6000001240c5441341d42c6951081ba01100180100031896001040740d980c1030b10041c2d0550b41e100200756040041c0a10703a03002800703a800d4000b1903840000c0c031544400d0300b1030b012581c000c00840d02e140703407001503854122a4007031502036904080c4400441c3c0d0340003610300500d042c00c540700130781c986071410040020103903106690301588941c89000c00c0401d000100e02112071144504509a90340d180f100b108a55060380c000e940064200010010185c01040090f4903a000310540d52514050400245803640078035401c5501074004074002052082d00d01c0f50400494055020301443c00e101c400003c4034ac61070001c0103108550105801c02414814821180325280c040c1941660100700300e8102d640e02030803180860311401c1c01501054905105040300c8154001172011040700307003450108080306400030201c03640030005000a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 294283354 1250 294282104 294282113
    0x705031b031512010c020624131b090e01050a0f050105070c05100c02041d070302060f09040f06050907020d0206070318051203011e0302030d0309150f06090f0e0d08060d 74
    0x900080300c46000004c1780c06000c00043d0400d0b000400060b801510825a23000050212082901c42e080440d04e03041c01800803511040204192240512030f040024079507966503030000c1c0118259420000014460303a41e440401032072000c5401a011690a100410061940110082d26480e0f00c00c00d10510340b15100d5001c14064101d00c2ea04038002241c085410065040a1090115201034207801641b207521900903242d0b9140380c0d1000900541c4000341d80003030542100241d402e058002442845514500d15000c005400d0134020584202841404285002e00010710302d084001d490700504429038402809800a05062556001c80c496040103c2c00041040c441d141ca81d283d0280199102e50411a1419824102031044241c5000e90364091015075000149510002c003103184c00718030008545081d07802e0011000b82121004c0c140852940200201d800220581b1180e00c0100311520840e00500160745420080c4030142e0080c0940c44812846040314940c01100074200511200450b990f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 294284604 1250 294283354 294283369
    0x110f040b0306101401020a02030c010f0c1401050406060501030218120a050f011a10050304081305030f0c03100b01080115030b0d080a1808030a1101110c0606090705031b0315 76
    0x1d80703060004460109012413070491818124241080c030040c4680d40e0940c0c086035882c2080880e89040c0840d0142c0140014401e800b17441800f41d01010700764003000c7c0b0081c072501806054508441440c01e00741d002c00ca551080c400d540f009040e011410104100c150107000b80141c020003002100d010305005130010075001c100c0d9203001e11043c000051480000514103100343c10680396680300741e010780b1481d004168840b083e240c00c40e4004140580c2c50030203480014100c91030b907100540500440640c50030741d00001c2090301e9041c90550942d18000300705045041228004024039000c13400040040c0802c05400400d9440c505c441d05002545400900000744039054114044980b0200050744c1111282d1101880b026075401c00755102034142071107080b980307078040d6401450400c810340c419a443c40b00250440d4001d0b8220034040c0703544012800b40349444010460b0414080c03201c960108120b00d100c1c400f100e1052403040d021801460310308030740c911290300107451505400801d450000d0745913128032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 294285854 1250 294284604 294284611
    0x70e160e0118060e0a09050105031f0f090503120a05101403010e01091401060b0a050d200c01020a0e0d1e05010f05010b0403110405040803130212010509030a090b07110f040b0306 78
    0x320340c4e42280c9030f24010481c000743c65030408090507040000400041d24000344003245110120210308081620502c0d8500070010315810448890500c000d91040c01400700080982050030040d50a041c0d958096010585900352058000c0d100114020003504402459011103107a005002284000c40b800304035094655000c02685c1d0900e0740c1c5880c2c044040e091050340001c0140e0000a0306080d0201000b402ea130003400c20300200c05ea222100d041602d2000102c1c01c2500800280180d104c0308140701080c003e4101e410b8075400304d00c611003a809030b441c054040c1c2c941d1940c48110401d500f20040d0250555010300841280d0075074030342420780220200313400382c9406030140610181e10b56141d07081841c044100e1442490003203140c2802d0002044406040b2036215654480d903071080c07a03503031021660210002c2140c1000c0d518050600110b6a0088020b00b580c00c00c568803d003440ba111480e46000c1d11404000500e02200c03440103d800d07040030f03522009018801000000d81411840c042030074500110f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 294287104 1250 294285854 294285857
    0x509060615210705280212070f0203010c0305180106050a2702070f060b0108070801092c01050a0b061204110a03021c020127031e0f0302010b0102070e160e011806 71
    0x2040c0e028402440305c01004d0301c041200128040414000806526654038914400450b079000580701e0034041002c00543c0c4040c1c1c050b008212170300304800000c00030241501c1c00c3d080ca01190420700100c142c140140350a403800280180702c0c1e80d250200d50324008914400701031080202c03203141c9003a4140340c400352020a000d0000078807034030580d10f400b03022191641da806040c4a1010309201c125607004d202c0d0341c1528803105000403210208648050045002c0c1c004145241221203018000c400c190801c500403001c04005210070a0000f0811406028090244600c01d101000240c0420300c002090052154040e00c1400c1c560784035000705941d010171010208200348100300040444d640415042503404414100030780300f0034621044420b040075480054107070300700d23460000c1c5803070700743c09954640a03440b129102200e007130392501034048c0c0612031100780540200900095440040ba4056200b030741c09000b000703420314002c82c007a5101c51048244a041201450400740e007010000c9514004c0c0499 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 294288354 1250 294287104 294287107
    0x1e13032c03070b1e19030b010210110c1204050303030f060a150201020703020706030605030705010c050c0901322107051002011a040912081b0307050a030509060615210705 75
    0x220003010306030700d030000c1a07130108481007180001c1c030341e004049426440300a00d40802d41c00a01c0c00100d00c0c001e02e6840386010b051500d0210444204144000d02400c202c140c203503020384001121000b07840c0210710400b5099081080040c1d410600381c42100e91080c0300410880002c0d071120503031101040440348110141c1e40c00181c5006058042207024000c1c45607141c180581c50504011a450f031040381306240c140a4048180810400244820b6880c8500605480c0c02c5695403209074603845259601261740c840a03c1c40c0f01e4001d480360b90024048800500301d401e25495140800700c1609178a801d0499900130700002066603960014034030102000c0794000700f809160541c0da0b11010301060b0302180308928203007089002070350604a0300d1a90545007440c0c0c0982e910018545030031000c11404001940000040104954208014100f0320503907560030030041d0b0760380030b026540300825510700360b1044c09404150004448100140488001c00c41d40c014201000030000c2401901550540040f510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 294289604 1250 294288354 294288367
    0x51201020c03040b0315030d0e01121404060605091506040b0a0c0501140603011104080d050903120a0323130602160204020301080106080d0203030106080a050406060e1e13032c03070b 80
    0x4030780e0103050f0450007c4001d4043c0d003805840c080c0210110503829030512810205002c82070399250f01c070040c1e000c110503500300e540c40c10b480c000f0001c004500529200d601c2000100700c1d00300f6024940d868001000d0002e510301402d244940036503410400300f000801102410032070001e40207002d03818404406412030621030402030b00300b43c29501742004009002e1000d00c000c2040c0000020a008120030328202240c0d03e4801002003414540e03248040031101d000000c1e803c45243e0303d0703444181c1002c0d80300c10046206400140c19a1140c42c181c030140350b6030403003034140004104164010001020100d1081100388416408201640c2099000e82001d9640701070402c80920144488160805903201a51441d0b0422102400d5844084e240c40141ca42e0b8000040030000c0c142c0c0990013608202840700032074504032500020f80d002108040044089400c046002000c160030482003107581516808564103411501e0b480069000e1034542c5d1040686112001948007400700d50080c14881c0d10499441c0d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 294290854 1250 294289604 294289621
    0x1404060609020c100f060e070c05010c0804110f010e0d0b010906140108150a030c080f070501090b070803130b0f04050d0509010c0206030603011d0f01150f051201020c03040b03 77
    0x103015511a0880d80d00401041d02c0c01800803e500101c220300780720026602041101c0c9100400054100141c0f0401200500c8492038111250f101d5961007600284100803005a0854203510142c0e002045010010544003440c0703450312848030700541c10714180d0803261801002130f01080c4000401c3e00c00080880040c4908050381c01224041c142051380401c00b40400b9000030103090b0001c2c17851880c1840e0049094583e9182400b0707600540e044048051070700e0b207584940d601c4961310000c0c0c0a031449031a00000b03003540a000f41c1c03811500c164621500b01840f903215404c160b40001c0548001c4400590088002620410b40300c0c042c8649541c1105a40381c5450032601d81012048180d05100e4103110942c0b40ba80d11000c0200740c50790580302523899440301c0000c40e0150100750b0b440400c1c80103c0d12038810b845800111101c4401ca80b400078410f00d10909070100c5010611b000300d154503401c03458180118201481c0790708240380c9803400185484103030130743d09040d90003603000003628541c00002d1001c402c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 294292104 1250 294290854 294290861
    0x6061107090605060f0d060509040804050405100b03190e0304090c14040807410307061403011a040905090a0308062706010c1b030201171303140d140406 67
    0x4041c00801044040c0c00d107000a00c0078014001460b09044c0005507800421200340c00107030003070a003c0d000c0ca5a508017031604c07110755049400b800c1d0090b860b040020388504c04804c8107104071070715506a05d24540390310101c1d55040401000c042d08841d00c400c00011014000c00c001c10092241c1c540000d032120414a008010f10724807080c40c1c2c1415401c4c4000d101500b408100e51080712004810507036940b800000c907110940814240740c9607400040704610810100000c0641040400c40c1590581ba444500c15980c6400804110108a40c20301c0140810100040c400489084041845040035640e02800003501c03012102141640c200101c0c003020160840e55003a00418200c401c00300c0c140d40c0988002c0002000003507040949440400700d20b40b64000d003004031046030000ba0f02c2100d0301980c04180c0f00c490380340c40304074001204213114410112b40603180a000d80e8070f0a01c081850740b00b50714100c42540e00200400c103507140c108440c0a0810300b500c02c199841075080741c00c02107817a007410003000700d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 294293354 1250 294292104 294292109
    0x605010503031903051e0a0c020f0a0309091d0f160b1c0b0111030d0b10020c1c0302070906080a150e030f130e01060c110d1e05010b030106061107 64
    0x40d900a00400200031a01c1101d48099070091400017490b685815011040072078004800d00070301034543c02c2c0300d1405519041945000700c1a022110741c00b0202c00d815540307001343d0703402400140303d241003442418600d800000400032a01c40c800c40040503041440d0030051110350f03500a5500900d220f84850000c10403000007050607000081c1000c41c2070410000196007041c90441080d0fa60003050544da00500f403404103100408201c9880703034422031107840101040b282082c450140741d285440c01c248001503807000c0207000743c05414002c44420b400200c115450004500b54011084082401c003581d00c03a180003480000c0c020007014500e42480c0c80708031a07030705186812504021034600c01040020448141c40c5c0c180c80301d10f1b5200791682000006041c103401c1080c2e03582c092000000c59035844441703038444038050907440e8180c0054400b046010200c40600415004000c40b2404000c0601e407100422503000c1d1001162507034840780000c2c01c6a246400000115804560ba01460343c01080303518003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 294294604 1250 294293354 294293359
    0x90d020f03070c090b1909020711060c070e190c09240e0d02130c020303060a1202010e04020304060e0109121404230118060302030105100c0210030510030c0e0406050105 74
    0x1404159803664801c1c0f02060041d400802e4030f5664120341602c4644180e44144100340e032000850303441d0040f01011354082c54054909896004258006103024000c846403000000010b000451500004425580700109000340d040091000541c040c00c02d800b80301d4400b5401c0d40c44901190620410003d0080c003141c1c92441001c0702c1407014002d070381040410031280002c480c03110010139030b4400100200d0181340c005040c0c40c104000c0d5040a81c000000d18051001152604101a00e418009a9041801c1c1c0064000740d40c8108000407401e11f90b0007190058080c1c0400304000b0b1001c450b80e800d460581c00c00310381c101121400c4c411407039404001042c4460219028519013450900d050b030900440c414211114410300401c825168000c50040c004000c40003444404c043c3e4941005d00290030900c14540184800c800a850451041c1c40c0f82d250b06070b0003400c04245041030081103000708001000d138002c609000c000800862582000c8000030058402d5408891400b860100d041e6141a4001030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 294295854 1250 294294604 294294607
    0xc0f091e05040515130204090c051c0308160905120c010e1c02130204081f060f0303050d09170c0105041b030b040b07020c0d050a02040e210c0304030506090d020f03 72
    0x8002600450460166420034858035466181c10551080307000e545c4200a40c031a150500c004100640090003608413202282d4008038003008078841c00160a2003c0c000b40000e420764006004e0b407540c40c80d4001015518501800c0640e1900d000c102c01d8410882000183c3c1d0200401d82015039000b08000050030055405c1880720800614071602c1c4030718001d000703100d11803071001c1045401a540c1a28014042c00e0122a0000c20181c107407440719002010816440381043c00100301c10700c0300e4444808580c0e0680d0f0310707880c0192120342a802016181c0c0216202080603a600300d20001c80d038080d10084d01c1890000178142030914011056200c502c005064a68040c2c0c000c2012644803103503545d006401c001e0319480c40c0c1d2501422800d005901c42410750008401070040244040060003260551090301d040041c5100d03114015175a0385440000e9200500c01d01e50300c4588003080d00601800e013600b0084a042c0f61320380c1d45442c00c007001141c20b44600c2c0c0c00b448400041c0b0b03a04000c028801c00450003c1c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 294297104 1250 294295854 294295861
    0x1051506040308090f0a03030f020c15030f130803010902221421010501030b01050306100b0306010e0103181103060106030207110d11090a02130602011e090c0f091e05 73
    0x140342402144405445000081440140358540c000900d02031800104407001039138503442c020700181039504022005105003400350310242441014820580d035551607660075661225040d40700c440f03005080192514068143c04000380740c55000d180600401000561504a41c1d00881e424444050030f903c10100c009004000d205481c41c902c000b0000d0581c0c0a506800c2c600c521508900c40300c0b5116100d070340c44c2c000000b09000d030106c1c10505882007281901c042c1e80300c64030940805525402544814070041010820f1036016201213032404074181000304000040300303964210a1080202510b12256105024141e032405014680c007400b0282011424020151129101c812158000340c2c015507001c90200180141200599003166006181201514045032410081d400405200d07115a040c40800700300b0078010f0040300c03800700d8101c0c2c0004818021999004c041c0041c11019a01c241c080240801c000154201c0c0002030056000c011400d032908699029841180880c1502c400c0e2404060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 294298354 1250 294297104 294297109
    0x50408010b061e0a090b0a080610020d091701090b0a06060318170d06090c020c030d0903031b110a0b09090a0507080a0905071e0509060108190c05131205010515 70
    0xc0e5803900e00f040e1821500c8035030307074070040d41c0320a081d80154050500200c0e50102c6e0650100b8294400e4005881c000400e6500120507079440522000c00da000c2840200b09120041c080280071021003c25000864090f074242c8034010b400c00280c0b0440c50003612000c0906c5081d81500415161f14885016201307115038940300c5280007032414244282d112000600c1440345131094000c903000d81101c1004000b02c1501d010007940e81c0c4107142d000d901a001d064031b440d00301070081c40d8002c1226010344400d00340080001c841d001250030b52030201c44000e600110000c1544030081044c4c0035244a6080582d07400751039042114058005040719099428002046041cce41d01c50001600409200f01c08186030517580b41c034905004c0c040e00000980d6001141c00600c091045203000204c03802034030740d050184c071144011940404122407400b068607860b0700040c1b150306940d00c120101c800c145001e0b0b0174050a00981c0050414592007a20150b00070322074030045c03203828030035103401c600c61092810403214500701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 294299604 1250 294298354 294298387
    0xf0d1b05030703081c09020603090309041518090c03050105070216090b010c030e131107110306040305090618060f041503060807050f1c0b01170f03031302011e050408010b06 76
    0x301e007480388001c5d80003140c00190042000781c0e500601c3c2586034605800b100e039503074120150301440303036040464504148000d01540010760303500001303400c4c0b1401d1f9620400c01800310b4441c1100c07400301150000011030020301c10076026045a501810395045c12076883d980090641c4c1204200b2403500450703181c66131300081d400380c1407503150a0ac0c0c5092150039001038080725082d00c41112150900c904858000640001411250700c41e0b04164414107450090542e0364500300c2c1c00031301081081003000c00501c1c04030043d0070040c55140c41c854007459504081181504070354a10321140d08003080a200c400002d0089080c0e042240c9010881e031450b05205a548540c0b501ca201c0c0190f0350075041c0d021a443c0d402e003242445440580307194003000d2900d42042540c509105084241812803043e078508907010507902c1ca64100c4070002d505544411510f83c030303100050501241440310740e107100407101803903441810412681e601c805d0740381c0b8036000c4007500750f0310805402882078404102050000b250f0f030f907 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 294300854 1250 294299604 294299617
    0x4081212010e07210606030c08040c091113090507030b030c1503180109120806010801030b010902030a060e090610050d03080c0315031006060909060e150f0d1b0503070308 75
    0x6410342c903038682d214151111130714a1052150700720300958001e200841c80d08100121105a5401c00070b01260010486a0390810b650040804042d02000c004102e1a80c204110f641c00501803203180082618901c5264111a032100c820191a2010030502035003501c503003410024281e010b400038401c0030340042c00b603072511640120444000b00110b002901022100550505860020010609a800d040c9810115440c1010005110742c1c0000d10035441103903018100d0740d014005c6e4080c2d07402d10203081c0103504001d022000003640c6110019013400b0842d4068040c000c100c01030041c2d410091010329407a03205802c1240188401180fa03c0029488070300190f0007107020340c3c0359480791100d04001036440b44000807654148100304c2e00d8405c40040c3d610000480301a40c0340c0c0c034911a5514440000d031201403080054a00000340011480c4002d05038001d5541801090620011484e00c006240c100035000290ba9409000e843c002c00d800d401381c8403901900c0308600902031149960380e4001e0a201e0781 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 294302104 1250 294300854 294300869
    0x11d0903031807090c020f010c0f090902070305160b04020901060206090a060b04090f150507090312031a150c1e07270f0e0610060504090207140109080408121201 71
    0x2c10900e002090260310054020001c0c2030148a28441009581c0c07483ca0b90303480c0003540f0f041c3e1920846405180d071050070000c07540760103808600c0c016195000f500010020790901000300a0b100d01c9615000305900c11511800001100b4107080c0140609602d05800120640d8080e07414000d45e040b001401501d01c2e54090000701c1c0a00000c404100941503100e001000361101c2c00000c010800c4d03207551404d40040319032040049607070f40e40c02101d41002500c00035002025460250788191310030381280072240520b5150745084509500401d8a04004c0344580e80701080101b80341820032410300c01c034141070803c40700d81000d1000350786840f1b4403402d86202d40c40e0444607008410b1400407003c0300410300c0501e68501003102c60000e40300c06001e0030303080b031003840940507190002e5942031390902c0007020340c1c00303555410341464103000c0d4040080d070220505403080d82d002400300500000c01d02401c00305034450907045407141d00e4402c486140201401d401400c008007440038015104182c04600e044607002e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 294303354 1250 294302104 294302131
    0x1018060e1512010c020d0206100501050702060d1409010204090e0a0c0e101508040c08060712050601030e0304141c050c0d0213020a08040b06030d080f0402061c05011d090303 76
    0x407400261204105110080d015420003003011541d68000c111004903c82c0f6401ba00e9241c2e0b40d40e8000d80312100ca0b40101c4e03011400c280052005800d2010140c00c01400c030650008601024400c0709200500031120010169000a01401464102d0050b14001c012820092069110544ea100c00f00d0303480d03000e4441030f05000310000f4034840c910003035280103140300804031551046c02c220040070720504803000d03941100800700010b41c0901c001450f510403005d9a4940000400740d0303124101404000c0d0559041685818008a0880003400240b0081c0401d143c52400708141c0014881c20425650a170b000703c0982c0344c0c541001c0f80c4040350a24600204441000b204001840000c1d0440da41216200040d40301107aa00ea455070030580c2039000c0c40c050601c4054903038507281099500c203811510180024010b0700400c0c425103214030040d40042c4000c08490526061402d24550010b60322400b2034410b8448004000720050038000341450310440c50b07600030781d19003d40da1960f2840050803c0142112 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 294304604 1250 294303354 294303391
    0x151b05070f0e0a0b10051b07081e1501060504030b0901200a080c19210213170c100e010c0c140423190e061018060e 51
    0x24050080036204401668500ca07071074882c000341d5410210303800601c45241900b5442c1528240a508600c00c400d561183d2034440040c0080500c4020304607034a4071841168400700c1c05c0c01041c0143e86985400241c0c500107400c1c02d04040c1c0c034080c50170045007045c003031800c010310145a01a040300d080da500400e541c00d031610340c5124180184024401c2880810a511201d00e55207021001071040706841d594110040c0ca43d200010348921580326941100c1d100b00480b07c20644c014410301548640079840e1414100729443c160040c1d034040034501c0c210503410141400221511440b13200040348500003030441c40c03884008610f91031031207003441c0f0501080c40c3c0c0341d20079030f84121403061403640d11448041203255213511b21021032101f40382076031190381080c1901c0c4001f003014035421005513000800031071586425140c0600d90220300d04078411980ca07040c0d28160010200090740c000c1e02d04190300703c00c261800741c0f5199100e0750380349217008581c00d15404001e40d01e91456040d0304120b014003034110521 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 294305854 1250 294304604 294304613
    0x20a02010f090e0408040e1b09130204170c09010b04150813120305061c0510050619140a0b0a020c060a0509130518031303060203070324080106151b 65
    0x7002d5032003403000603103030380400c010825084043c0040303d405c03c0d0101e499441c0c0581032800d40185141c144032200b03060244c03003020310380300951510700c1940144c01440e00d07440300a51010000d200e80440010740c4150044545400d2580200c2e0051040b00710305410242003002b180046ca400c00c0c0d42c031080080000100b54001009914001c51640c800d441120b0044004000340140a0880311103125203007042c03000e541c81c050204191a5a0b900401800342883c028260f20f00501c4040c0850341c11040f1410045100920030710b507031000e4a400441507080d04165010004031072039030741204000c460140300040405400040101c4506012185242c50b44c40038241101e4501490181ca0350200043d00c44401d0f82c0c0690380424041c0484000714440311004501456807803050b00744803208210b40d068108040b801039130145801108502d0301150640540031080341008030411086060300c1c44071310400400030309200b000d00030240c150031840303407041c9600040c155401c0e40c060348e201d0f001624003880402c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 294307104 1250 294305854 294305867
    0x3070509042a180303020705120703021302030901050a1109150c0106060305090c030d02060112030e060a0f030b030c010f0507170f0a0e0a0e070c02030703020603090a06060509040201020a02010f 85
    0x90382c69401c9044450600500100011003581d0302030003142841464015046114401800f5260541c00030b0103690300d4482840002214480400c0d05402403003000f2005a48500c6542c04103c082c0e1005038a9043c5034a0540c2151409440d03071440600d00b845085420004c1c1d410359801800854401400c2c1c0070344001100782d88914003450b5181d5103080307008240d4980580c0054004c5000c04100c0b41c0001908007030654680c11140807001507440040104011083d10f689450340e68884d02e004070404001c0e0002c1102d03034211841030030100f540308210711400da40c9072150510981d002c5004009044950002a0007810303800900000c01c500002c2c40000d000d0180161961061f420b1130503903450064108040f0150042740c00721000850180551155151810040090743e42c0090f40e00c01940b80c550068699064500301241c060288071000405a6100005103100781ca0643c01f60601015071300e8428200d034141d0700000d204500d10030a02c80983d13030019140c101d5a60a00745141c074403811040c20303a0341 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 294308354 1250 294307104 294307121
    0x90705011205133203030601080408030c2a06060103090c0506071103100c0f050c03180f04050f1503150106030c05131d0f0f06010f03060306020d050114090c0307050904 74
    0x13000d4059084c820a20310540c442002000007034403014030041208801612844191001c0b4001442003001c240412000801150084000794065107003180380d00b100c10564159800b004181900803e1040e00e52900380001a03004009213020003e11102d0741c0c07144103048041c000c0e20300a81000c100380c000c0040e040901c1103440c2d801402c4039140b00130300031010082d042c000300701c10006240d1503e80165030f01072819130b420340d03510310f0155040c60002c0b0721210f1007107000c00c043ca03800079250a8042c17050700c862080500600f0010510030350303898014128941c034001c85500303c1c06984500402000c0b46500384003d030540300d0518004c215045a1101200e083c05a1300500300c0a00f460340d0300144c21201d04035042d5401c0711200ca0b010040d030742c409000006450864190401e10300e40310001d0310315031103031a0312500440a0b0900081d4183c40c1d440724401c0b40c000b9200c1c170130b00c07642d5000140805100c11a00030b2200804075990350b014a0000706000d0309000c090410fa0a001c00403403100201e588030341100c0172 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 294309604 1250 294308354 294308363
    0xe040b0c07030c17071703070f0f0923040203181204080a080304030c020613031502121f081006090608030a0212090a05100e010f020118030c0503090904120809070501120513 76
    0x224002465822a4029940b07403022032030241440d00c110303009490000042c800c07910f404bc80180342110304443c00e940b140305884420b200c680b1600c200d42d6944040e6014070b01c840300d521000b0303003181d1019182c080801c0e50824240020b000800080d00d001405c4140c1790341c48040363b5103d864924042c0c80042403404000c0d8091004104888540c906921610880c1d004103544130718000b07041140c10403841000c0004e960104002c3c0054044115506441c00e001c49440b02c04a0784e607510f1403258202021084c1d000010764413400e08110900480c0501c201400704400950f00d810100e07580a540c8070f5082400100c440300204805006549210384a0001c00c005031810741104502c40004100a807002625400f05480c0203880000b42d2052142c070350390000d00380e40c014401d102a2020740380c14500010440d4644000c1203071150603201c89403020300072403103045d0081ca04d00e21050060510f1000509064095000c8942000513a03481001015013468402c4005200d440340d003507104a0080d101400751 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 294310854 1250 294309604 294309623
    0xb04031401110f040302010f020a0818090c130e07020a020901030b220305370503010f06051e070f05150603120f0d0e0f070e040b0c07030c1707 63
    0x144a00c2010010041003000000c000e4000c0081c1d0012a500030300004481d14002031201780019400784880540042c0140103c0e0002619640d500045070b01c01c40c10002c0d2592618404402802d142400c2e9810800c1e1008079420301d41c50191340c0c550343c1348520941c40c07121322400110f082d0074003c2c03001c2d11240790060100301042d070b100e0030900d130f4521099520041f01c4000c140d1003e03c1d0031070040d000c1c0d9982ea05031742e080d14003280c59803114008840d500300d442400c02581e401004640700358400c0240011039031035058a80d850880000702c0b0344110707880f400078440200a04c0c880c01d154a01035500c088520b0b0011b13a1075522a042c0122800d10020004003075104483c4203e844044120100384150800c900b141e01401025904010a018140103017030030341704c02c1c021b0940b84c4106400a6407107101e290121000b001a0705070700781c5000000c1c0d010341c5c0166021024001800003440b8020351000fa40302030b040c41c10780a035030010040c1581f214090510105454284c02d4200a00111403c0b00d4100c800070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 294312104 1250 294310854 294310859
    0x702090c0c0f0c0a14150d0b060304140f0714130f020a1808030c0309062b0506042714030d110913060b0d0203090a06020d0509060f010b0417070b04 65
    0x40ea14800c0c01d50a0b44100c410180c00509030302d171314031042c0e600d0402900111104541c504401c10039002585500b0000f0345450807406161694406148558001e24001d4075007142404420300709910382c01042020f8200a400307000d0116a45403450304c00e5000d89210300da0075422a80180200f00c1d00c01c034100420300019481c40b4069101100c070782c455036074641d2103100541e03a55400d603880c45449046400b6400500c011031161425501801c0401034050f403c0c11000d401c6940401803202d0314181c01d00351a40c41d41488043c3c1020722621451103d08018940d82c1400604004003000781c1200c01407248011044035408003c0c21300c19a51020a50bc1003800808000c10079040360340c01440407140100b4944001500c4240c00b4003c403802c89000404842c90b1030341015407203029610080c4500b546d44141030a00000444601c01006034141d8035400080c1070400034026030502001a143d01d00764004200180f00a0140d0030840d0100c0d052092400501300f40000302c1802c03c0c6403035005a02120b00070400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 294313354 1250 294312104 294312133
    0x31e0a050402090a050712090f080f1806090108011503060503160612050c0403080a050403080406121401051c02030a0212010e0708010c1209060b04050426030c0702090c0c 75
    0x3940107502c00c03100760b2100d03a81c1c082c4d0358007110011901240080c82d00700028400403826400b2a0306030340102e02c8a02e82c919240c8404103103038807030040c2c500312560008038610007005c00604841c100300101c0703040745007014150008100e4401030240340d145054903036940303056038000e0780050003d00004d07041d00c0c2003419a0785152411b850303d2080b000420890010038040c22a0f910586103c0d880600ca290b0a003815605c41085c15080311000d1030600c0000c10000c004108124080c0c002024a0396a1120000d0b01096001c21307640409220041c2c8903080005001965524080d10f0581008a00700340c07881d5142d0001030b01c3c0800081c8042d400c10244404000101019005000303030007589000c640502d03554064980c04c9400f51040500090b207809a0b4201d41002030f001107801601030368000c105401c495001030304403142031303904881004078105140340c0400111113010050f011b041e451403e51410840500c001d118150000b841442c1450006424001080a42e04400c1043e000c135042820700000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 294314604 1250 294313354 294313361
    0x12060106090510020610030b1b1c0c110c011d06030c13060801140603040c05031c02010b01090e0a05060114070f02030114190e21040911030417031e0a 66
    0x1407035008022142000c0c803103d00024940c0c1c0104c0f01401d46222152540e21100d502507000340c13518040301024403c8440101d400c60180500111040c6040754030ac000c01403c00c00c40b80c0040c1c40c0b400348070510721700c810741d2a80814800b01442081c00c3c40030703250392040b10007411956000c103200e41c0010301000380511203080700090070400075540760502001e038480000b903503400024071500c80d4030740106100440a007007000140d5006441000701c4e0300405c0d00d0394006410700110503c4a0150380c003c210340007402e6824024000410780030b0800281b030074186a1014052240201031750641c1e51958040b540c280d2040410b14a10300c40300d010540c076000c103890002c2c941c1c03001c00c0059202c0d60801000c15240074000103842d02032412003004080441809002c1c07006084401d8100d40a4040d03449801d03c5181e0b1032550884440e121100240c5e00c03070428040300c08071800030508601540c1c0c05d008001c00510754410b910300c154540201d1035207940c0c90000801405807602d04840c4950710342020700c41c0700340e150741 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 294315854 1250 294314604 294314609
    0x30f050109020c0a1403090405040f03030c2a0812010e01080601050411220317040305010e011802280b0301060201180302030a1407062c0c1e1206010609 67
    0x24011640d8a5004200b41e003e0410340440c40c1e005440079000240c50800818030049646054a0420310304000182c200c0e0b60480c0d05880c5458945800001c26601d0f00c41c1c87c2101d445803d01c5000800d800150b030350362a82d2124820a61058047c0c11028400810b0a590b1600d0300c84902d520150f841d2484451546028072070381000d4458031001003014a4540141c48180c5400040113003003002940d400b280311078031414040000c0990790740100100e10a5040075000713081c043d4410769903906c0c502d0702d0b900315100300c082201d00b0b9142400d81c99414003582d00e140c01c2d0640442d640303510b240c000e244002c10640f00e02c000401d051013041001503070700c148101450407900160001c0118412959400c000fa641c00500103005030802c210140c5624040d16100e180240076500041c20040107540d4a821907441c1d0140b2583c00301001500140081180c0c134001d11140ca00f0003826050200d07801191001c1d103824012070702069501803030380c016101e01034411060522401210b42550b51010b0241c0001080e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 294317104 1250 294315854 294315881
    0xe150109080f03090f210115080c0a0303050a1710031419060c050408120304020405090a0b150409020d030c02240f030a180c0e06120c04050a020c03070303 68
    0x102030014a14002140300c03840616140061842e142000c001c01800c80d42ca0b200d030591019000c518201188418500c1122190320b41000103401100740d0560720a040841d0301048940d0b100d00340b12410740d111400c0b1030b8100c0e03506003442c9448100340d05c0262a01c4000440d6000000d0600c01081281e528003249842200e001300200540f050204181c162914030701045c0c2c566070400700c440e0b0000100503510042074104a454118106600e450080e404c3c04c900e0415a840c2c08030100500066291601c90380e44c01c92101d800800c0e50880315035801e12066030003001091f04905810380c201c5117440380c0c1c01c013003041070b0300400e41e401040440ca80640000e154540907802607003840c00001000d0700c02801004010038040035203062950343c54014401e40c1c40203281e000159254003c243c0c070544404510707000036228900c108410b500307008090f00e54102c01031507184500400310203201e0300702021454904039181550007240036552034490402030304ca820b03a0504542300019048090551641c0600b02e0703440403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 294318354 1250 294317104 294317117
    0x417030301151704021002010f060e1503060105031207050a0b0403030203191107080c120c07060f030507090e06030705030d020c0a050409170a0e0901030305031e0108071a040e1501 79
    0x10b410440703035041504204501d1101c403d0104003d4035001c070031103e14030502d20000c201070f401c43c1c04000c1954402c0c0e100c40d0030f4080050900242ca034034285540020300c41a0014800d56251000090359030038a0081c44c0c500081c0003654400b480818020110940c1d08541c0c12121410300385030041c000e40c003c80b07010f600d11221181c201c001500301d00075030034408044c00050741400941d48600d180c90b404903111540d18404c0392510703404102050f01800300e181001000d0403030b903440d0110103440b180003010b140040525100801c40201d400c00094000c0e5185810341241581d641004a85481720503001035070326201d001150221107034002001d42c00d0003010b68541004c0f0f640d41302404191910a40010b050300b0324159000c09014101d030140c401581603113419400c1d0f40003900450a140d10a8009a001620000401c523031004036a4620204c80002240e206c682e6150410183d2100050b0140b02c0c0c604030714070000c000021600381640e024000f007000c82902403d00c070f01c1e440101c80071a81c056022900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 294319604 1250 294318354 294318389
    0x1706030604080d0c170a0603120e1305091f0218030601051e01020a060c05040927020f0d08181207081b010530130c030b0603030417030301 61
    0x501141081c09154000456414984102c00074005410301c1002c140c104160359a40508a40340c10300014010706010324000307000ea0450814943c04442100260f00784001c03846503c4141d2144240314290300001e03580056aa205e03290140c0c10b05c40e4001001c491030032009803000d885a01603004003080480c04818804081e003080505850360003d105260780201d00c2009540f411502a98110203514140f0581e09140a40c1e030302c100c00c0f501500040c90000d2400700b4107100c4014984211000211030601c4249102c611301040400d1503000c6000a00130000b402140045840760003450072180e502545044d02c6121058281d0748030301031103084900c034000d4202262071060001c070f41031003030b50b180001030110512042c4503105a4100109a0390400c0700800c02880f10803410085e11280c01c11004058002500695000d450740201a020322000b0b20700d0724240001840c200b80c00c2c411280d10040f82146550394200081c02c40c002c66104010000350300095200600c1c0100046041c1c0b4a2400ca4410040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 294320854 1250 294319604 294319609
    0xb040c0810060e030c100c080301060c05060a0501140f01050405040e0604150e1e0c040606081005031209040902040b041b080702060105090c07050f0d020f010608030c03041716061706 80
    0x49040f10f03058140e003000c0c08000c114101003507200c241d905a824600074007201c9036141e003003d80c0260300c054001040b4650582c1004824042c0e903811a2114205200035414642c4400e498070160b81070743d114481e06640c1c01c8042c0d0145c002d07200103180017481044407000d002c0007607850703040441d0211040720038000340b03207140c0029105546a4400a5000380380c841910920700404441c009208a41445540206105e40c0d07500d019010203403410f40d0ba8030302981454a4040303080ea101d9000345100740c100d00d002c10480142082985c108000403240402c6405031800494000e00280e0360075508030342171500c2504100801c0b070845d1581803080c0c0d11449640d451100c1213855103000c0c01210b9000c4d400c500400c0202000c280070b0054517010300142e6096074440383c945460075000c900c10002581000f1050309000e102071007200010142c00c1d02451400c0740c0802416160700c01c50050381c2c0c141401d054100d0740c5210401c103071252015404800390b00c043d1122809094007080c081d201c015402804000356450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 294322104 1250 294320854 294320867
    0x3011109040e010203101205070506180f010c0305030a0b01050c03120106200c09040809042a090f06050a0c0605010b1e07030c03050c0c1e1503070e060703030b040c081006 75
    0x104030700300351700c80d46e141000c800e41c1955028040964041c4680070011400d40d59900052400114549840c0002d40000092080051002000c1c40c180f00500c000500802c0e0031004070f80d03100d941c128001969030310910042e02c0f0360050700703c0043d40d0301c004200c00b058481035102890607208070f41c4a2020241a00508154030098285105007980081d491120301d0305001122035041480355550608040341c80e0040380c200c580082c0954626581484005501c4046c4905201c0ca0006898494106030074652140c661903202e1040004000d400141e040000c0d22445000c9840c42c0c0c04032043c8081e5a44444203e8160003c82158903108490b10707020081744c1020048070500c581c1600ca149440706262019603098004520a00460050140040c029550b185400a03200c3c6c01c44400c1140f400144240041042424120210032500700240214640c10414220680d8011204250342e42034074a000c402508002240341c0c3c205083c26a0a035507103410070111441242015800382d07a09958420482d8017 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 294323354 1250 294322104 294322111
    0xf01050108031c0b0604031b03021003090209060907180b12070318030806040605040e010203041205130308030601032711031902040b06070f121e0504051e03011109040e010203 77
    0x8070020712a11601c0d00c3c100e0b008111101310090915040c60f60740e0307d803600300031903080da501c2880320050b00510440c5015170443d05005018641000070341c100d42d0104e03110380c2000d049188904804c100283c58244506480e44c243d15081101a4009a80b10302010041d006000c11208149003240041c041900c640b1550703900d09540303004540403c072152000d170f80007180908003a03049900c2d45004100c2c1d4495001d413182d001c4c00c180c00181d89151a013030980b001c40c240c550400400904003c00343d421040e1110081c203613500652220369070703140d410058004049410701c0304101d1080c01d00006c003034098903400d00f88003405800400601e164600400d5100c80c04614400340001ca0a40b051015040c01c0d4000f5540e08000f905d028034084007a00e0b1641000c0c3c0000045440c01c0e01c554580780910380c0003604066000c0d0311000c041504580303040c040c1646c01039000b95030089140303500f02d03040e05c6002200c00480380c00c060000c00405003101003010050340701e001c14a014074145030140341080e0b07052007121310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 294324604 1250 294323354 294323377
    0x215070810031112010e0304050406090209060a0f020f1c020607021c0c020d020d050105040c0e09061909060c2006060603010302041808030c09040501090b150a030e0304080f0105010803 81
    0x2207503810365948108610000f42e0403030304103807041e0344038207800702c02d21138425010031950007151110b03e0001004180d6000e50031011005005203d41031a5071910700680f0760909480c2003098032100030246c22803070501b010700301079121302c00e00d1100c003005d01c91940e04142010b4240d00750348182c0c0d14443c050b66a0b1021010f0028000c401c221104d18051094182e010301d940f006180701e00d294000c1d00090745100c50520140c640c1d941d1135083c00100700150280d003004000e180281d41007450001c0c4c03400c0c0c4812005210b540c8152030307620b45110031122980000345032035000c42c040140e0900c4d0080144040c0d4001c4a8034010205002c00b4942100d00141a070b1094400138101444c50b801c690a01000c2d00c1d540c20b94262035031b0b01070180c80000f042240690701c00c2806806c5070b6200d0250000308070030340e40c4c1a4410300c6d1503860140c02400341c5c0c03500d00390340c7e0360a0003079864280d0305d82002504400404c02c110800259000200e400300380a5004078620003061100b10081c0401d90301c66584545a1084e00c00959 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 294325854 1250 294324604 294324631
    0x50105150712080910050108070e0601091a0304080f0a0f0e0d0b2a0d091a0705120c0d0c050711090c030a0f020904050109020a08090d14250302150708 66
    0x858140c031580f00c1560005014099441e802001c00c49002074450a03044403d6907004240309100c070b00012441d656000c00c0074a4a01c0585241c161500003c007911045104c230124000001418004004100d4900c80c0504020b65522088100028090543e111466001504040351002c03589000301d0078240441d00001c030401c0c0c90700d900d04d5030040b100c04800c0720240140340c82d10300c054140040c2c1c058071000c034000202258810083c42c0030740d13a07900410b4002965046400c00d00c540954010140c5e05080008003100700d2a03100c1c407003000858000c2441400b2900c1c203088220310707020b80c450003400c04a845035840d0480c003102001000820390007100c14034051107003400080c030208019000041042244100180383c11030b010041000d0314001d07041720401c99000501c40c2c0c0e11941c44040c00394083d01200140c43c1500074000000e0810303402142580001c00c0106040c0310506804151265920403030051a03202c80c56450040d440781028030b400403505c5105030001d489a0300548646100710b0b045400038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 294327104 1250 294325854 294325883
    0x270f1a0105030a090204020304030903050d020111271009030b01080d0f080a0e07030b06010206070906020304140118060c0506010803070f0803070c0203071e140a03031110020d0501051507 82
    0x11240c070b410080c00c1210890b2140000d00c090b03100c070720055000d24081d90f0703000405421400c100e45003028045200c3d0840e031500030b40b00800c0d91103400351140c003011900c030f8108c18401e800e14424000341441c4140d522607180c64407a5000c581141548088910510f681d030035603030361079001c6603d03801c80c0342443d80400c00007100482130f02d20540303102c3d6208406d040d00041c881960f040705442c0ca09260400c032444200e190900c0003968040042070380c03202140c640010100d0410500940300d004922502594098000d03094456070f000b40c1a040514144950741254241d40d540000c1809040b2181642c7d5030003010300202d80b00c94048102c422a5800c900a1425110f803a520b40740d4a40c001005034042141070050400185d4007070021000402c160b07800c41e02485000c040369121500c0076400180242e1a400304075440f5200e000d800001c45ea0141021540c200070181003c0c20508088400440d03c0e20024032940c0000e825448907043c1c40098a1200c2e00880c1c21301e403054a4440c03902c000d0855841c1410f80d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 294328354 1250 294327104 294327107
    0x705060304020a030609120e03010515090c0408100507090b1e0d02040305011803080702010903020c0904060e061f06030b09040f210302030a1109130b040204270f1a01 73
    0x550300a0320140c032003070501e940e17612000d0072610f241604a0340b0b0b03900f24650038003003030b40800005001d04040b8000c10160600c1d1010684c0c45544245c824080d61200000070181500681620700400c03118066070b110040340c504c0031005010490f0188041030304644082040c08050099412a41d90309007a024654130030705010149401c1003200c88a115001c220100000304203000740c5155060080e1001142000c914000e40720080040034a011a8134000441002c01d60016405000107030070307110740000c6e48035810408060300f007070340d51505544540700a11158419100078034410321840345042045907103980c070880980e050600301070352100541001c0f6000c540b200820598043c400c42035200d46045041c180d4070b1200c8668103e0001c20b5003c000c105285195014a0b42000c903c216101c0c13500c18200c00007600c012210b40000b0031a03a90f820301c80801e403910750480d809860f403281d40000c5005011207040501041f20394a41c612070411201d00040c580364000c0c042280903210722034240e00c00c600d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 294329604 1250 294328354 294328357
    0x70b0406051e04050a140901080105090703030309140a0b0a110405060f0c15150307050609100f030e030d091a07120902150c0c1809060105040e03091e12030408070506 73
    0x48500d80070390b08010016040d036841d400034005101181318050000e081008008070f41c641640110610390410040001d0068003090300000d49030702d0308000552842d0b03414920400f21071005402c04134070907603c8101c28840380030042849890300d05810b1185110103101441a4092449180d80055090040b810007131a00360191401c0b0100804403070010507c410b40d4000c000054030142102030407007000c12034604003072007100060502960003a140401890100e01c0100c4440d0900d004c00c043c5180c000c200c20f00c80d03000111668401d0b0f00722900d48100d00c441c1d0b002848100f00c100d4a40001c0022165000c80480b0154481c0c880341e1203e8a951840b604150098581400d0803a8400134009000c5804001440a01003964401e001070000070b01200c24080555843c221313055840c150700c0c2c10001d40c1030000410034150f500684020032480e041006052450065840c015401603003020103030317178450090f0704002c04040c08a440c070340e0300b28040d011107840e80b00f01d024051042d0404682030005050000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 294330854 1250 294329604 294329647
    0xa0608070e06120114060a050103020301080c220203070f17060a0611071205010c020d1404051c02061803010b1c140705060a020f0705060313030806040e01090b09070b040605 76
    0x7012941000c103025807260031101c81d100c400300f075400220140700301420f007c02d02c10042c010a0a0461a65040186544c1d0307a6500307800307461050341254014084004005400117621490311400e5440e400d000c007000e880301d080600d280d80042c07240c2040b00314203c103000d0824041c4e28094251014281420000ca55200b60a21030070000e00c5100c5001400501c2ca140d02032069024600004242c04602002802c14000811070b80801c02040b030b5981c003002088080320200c40b0f0494111400304120f00c02484a5010314001a40c070040c0800c8c541c00782c480c084402d041d40f036011402040750041a10400a000c1d4a030b0390180040000e02d0054000036024921040540031080110340c086c03035542001170043c0e80442100760050b0000c40000390000d40030481c40c000741400302c602c5811072410080110754008014409070403c034040b8046000c40d1100e500654684080b02e000b40540f414900b45406006401e40b10390040c0e1040c01c50000f0702a07907900550301640c00560761245880302c50103402c0401d50911 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 294332104 1250 294330854 294330859
    0x109060f1a120c10090503071a03130204060b0a0309020a0602030a0e040b040e06070504090f0515060a030b060f070302060a02030618180123090a0302060a09170a02150a0608070e06 79
    0xd104510143e5205103107007003200c0d1136a0310141030343e08000c18907007401c0540c0d2089420001030084d101c1004d1043d0103681d070000254020080c5004e181c00040c000d000540d02600c1070020000324442150790580180702c8a40c020386500e212540c1e220004c90381c902c110f45844002030585100c0c01e4203841d054105000404005001003280c5004112150814074292104c00c00301e500024104401c1d0417501415160384080c19080103e481e00903410445840c0c1c103130440d803080e81d0000b2080186406580310000000004d00b03202d464000e1240d2003903142d4840c1000313601600c50000050021142402260f11038600509010354201400004d11044040a01244980701101800703071040c0301d0910680034420f800041e0100503203010f00d0000c04100e005480d450440e04003130b8003d40840e400040d034a81240031448000b4028246040424006000b6070804900340130018108910070360000c3d5892b04003125001d43d65a0392203208401d03081f80d22911030f0418680104e4010070840506401319680407201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 294333354 1250 294332104 294332113
    0x21050406030b0109150e1306090207050610030201050d0905100606020f25120201090e0f070f021501061404030c1706070504031502092115060d03090b070309170109060f1a12 76
    0x2020b40031f0781542c80d560030840f440e031740c007058100600004104094001d102501c0b10040c00703040d500020520702c101100c110f441c1c0e8a411501c01004030070410300080c02600d41d001c0001075101c8000a44a2404600c13051403445501880b030000c0c0201c1103c0c1c0c0d80d0702001c900c00708009282081e50ba0920ba0010b0701a41402a5030f6400907014103100030300341c400e1101184d011043e18044001901800e01620150f013154024480100484c102c0344010341511058108041d40d000050012a214812904020b1002c0c107040400210140c858003503184600149042c0d50255403051801c60707050080b0310014140801010f03003e070030f10349a5802000342d00740240c1018074a06808500300e00d910441845c0c0780c0203a101c404000c2000c0315014099030000811103512241207a55180140014090b014a0054100c005a003004043c001c104103401419500c0d0704400342c1022400c0c03103008242c0342d82c0c20b4402604102030744504a0003441440c1004914414580f403003c418800d00102050b541d140031042e104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 294334604 1250 294333354 294333379
    0x11a13020f030a0f110340060204030c0509060303120601090f0b0c070b03090a060e0a0506040b2202090f180313081005071b21050406030b0109150e 65
    0x750340000c40c0306418400c4003203400000c0c0305104080720841550480c0203002030042c04012440d24a142602e901a00c0c07590300e050510b5010200c102c5c040d400b40f00110100c0302800b03410461140c005d0000c580c003030046507074015644c200f0700c41965401c46010313905800c10403001400061071200242c2040701850042c2c02d0503224001c441c0b2a103599081000b45c00004200c0c4854114200202c401402d20040041c1c154144203071050b545502c10000101003640703c500c50203951100300210b20303110340c00c60110307900340c10b160030020342c0840261070100d40d00c00e2070f0440d07074001c81c40b0b00c03000781025501038500d484565806400188205016000c0b1034051100011301031148002c00182c017840d090840001d5449152426291070494265014a061400c1904210030380d600155401040c41168001440f0580d003464034940e4807402c004140841b4508190012050713500401034801e84d20b003a1001c00042e035511005503a442064454114054080d0204240c2548101004101d0000107810000940e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 294335854 1250 294334604 294334627
    0x1120302250e0c0408070902070204050a060b1c020d0504080301051002030333030703060b030106060908030f071b0e01030c06230a020a0206120f0c040305030702010507031b23011a1302 81
    0x31b8003680320080c00c54002c1080c00c10340c030f480c1c45036070b811114030b141c1080030524003a186004c500030101c020781c160078a0a091080c0715800d03011900e03000410f0508024515061034184030a0700280145c6004034848210b5841d400c0c00001240d00034182d501c940110800c840f4540e0a00500c229600506980c98201e10b01c007a850401560020314400c4d68040340c414041c500341401c48403160f00c284100170080008110080b4084112140d45281c03c80d0144d44021500300029600e040d44401404c903807a80000180042e0f06101145c10780b0b2241d404030000e9540c0d070000f186c07441e10000b088000406588540e500490454009115030038180c01503c50241c0b40b0b03000980240c01a082881c203550158081005201d0712081160380184c903250001e0905003941c45045c4c0e0380c02040c0c03000307050200004001c410704d80180d0402014811f1402d84c44408552450b00400b4100e900300d10000c041c41d081d400b410026410301840384040082c849058020707908800f040019008584003400340c0d0350801c403200240c4d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 294337104 1250 294335854 294335863
    0x212300f010801050c040317070303021e0423010512070e130e010617120a171608060307150e0a150c05070f030b010b0d0f0501120302250e0c0408 64
    0x2641242525400c5614002025003503030401040c80040740010001800010805400a8542c40700c104801c0c0d225041303403070150002c0c882e520100403ca0340340c281042c501100d400081060380c1941c211a0b84c0c0c4c1504440e801c8110b401e60304180cec0410300c1400a80395052a1160a952028180c9845c545141c00c0b000410070701141034094110740c0d51140c0711000d01803001d0050400809100202904e4045038100d496124002552411000040041d10448081c49940c00628011818110740e445081540070f0380d034800b00f0303003078218042114240003c44030319010503110210381405075440b1001085d03060413619001c0c0d034142c0a81c041d40c0035401195440040d411080c4203615500d4451109805061252a0883c1c40e44044c1c1d000c85051020300005003100f80c8a41101c103e9000c43d40ca42010407100b01c0a0241b00d14240455854040005400f0381501c031408003d43c000e070255824540d401031801c461582c0451a6103401c0e0300b0030420030109107200b01c0c45501c032441200960925484d81052400c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 294338354 1250 294337104 294337111
    0x20c0f0d17040b2701090314031312090305100204290d2003040f1e1a04020301200901031a1e01020f0a12080114010c021201060e180d021230 62
    0xa42e540e402c062041581101180c1c5520410a28250031490000d6041215544501008044bc855401c000341d419005005903000b0b154800c00741d413101101c0e0308100000f90418800c0f8444500c444504003d4050034541d6090681001190300c0e141c241030750b42003070240101400c0903880343d02500e6503514001034440a14051780c811700360b4141461090615a8603030b802e94014414180d4a2500080012040085c120f5070360405038802d2803070355403800041d0051800c400e50010780455130b07d0251040c105200140041e000c06d80742040803a801c02c03e4201e80a50080341d06800010f1084668640024503182d02405401441120910340c0718124881c00c20044481c2201c4606683c90141d4045822008079805082004846140d0b802e280000910780f40c112440a800b5034804c8080300c0a29800390894401342448c40b9101205042400c0b00317191081c0304410f00901401049140c5601c0d42c400705070081c8190700c400c803190900c015115025500c0d24000b040d210948910038442ca9040d601d940320070320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 294339604 1250 294338354 294338431
    0xc0306020703080106170a05070c020904060f0f0b090406021e0c010c02010513050d08060a0b0c0303090705030a08040e193801050a03050c090301020c0f0d17040b 71
    0xc0740c14052801501400301038115000b80103a001c5c000c0e20107403079042c4580e401002d600d07000c07134551a8070b001541c1d0f03a011054042c1d00688c1510420050107010b800c203466104024004228030052808020304861a03042c446501c91400c0020a02203091078024180003c14510204081f0202c001440e0941d800051036000b2030351101640d040c0b41c0d0f02031081540c41070702400500c00b8104240d0743c0544540d0841c200354103026a210204407181c40d1403000c0c40141c00c00f850501c0d510035680740da07a0742c2c2c1e41045403030240328031405401103041d040c00301e019400558070440442c1042c5c200038035102c02c14801484825280750b203814510714084a4040c5800b01b01c000d2001d2001c00f07801c05071826610302d0304003d100c289007802030b00c501e1503640032707003100c1141c40b81d4600001e40c0e4840040c03140c5035205011980368550f002044940e0914070104030710410000c60380c00c071a104058288160340f40d00c2c5e100000a0249403000008005ca8a80740c20642e1110303e03c19410940c140380c0e22203e20110a031541881d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 294340854 1250 294339604 294339607
    0x322091407030501090b0a0909030e030304290a0206061e030a060c12060f140d0c080c030708060708010501030b01050c0106062001050f130f2108060d0201090e070203070c030602 78
    0x2407969054480c0fa40504000c240901213203150101081e65083c06224842813142e8840c2d0070010305206903036280101200400b50303540d0300c5c0d4515042486018400c00215080980f11035a81070074110307012038036154041c0c2c0160078955102000c210b84200602d2100e18032880d14180b460150340c3c1403201c400150710400002840ea540301400a00c66840ea00d816002c540c548803040c0502c800c030310607010071030301e4a82550703d500f1582c0f800b1400c40c42c0f07056001030240503a8100840c00790301c041000580808140c0c2259000fa80e150840d9030360b03060594000c0c021550034001445154400c0e0004451a1010b0424615000c1d070700011500315251640441b0025040b20000d60440c6c0080c1290b042110850000307010034101240342e203a0445024110300042d84840c0418002c00c0402c15a0705a519003160000520304284682e100041800d0b03c5602c00041c19400012801c0c1f400380070201d00d04d501a940c00c0310103401e0079402c0c51000d402405883c1940700030710043d000a03c2d50030389039010310710450016 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 294342104 1250 294340854 294340861
    0xf070e010609060e09040b060a0801020708090405100f1214060925050105030a0e0c0607030e010305010504062402011806060302030c0102010b06032a0c06060909030a0203220914 78
    0x10502c0e65543c20920400815005030b102940c1c559074003c1e003140c1c008009800c1601c910000136020001584a031103294004220001445500e201800c2040c4013510107000554030540d28000303804c0c843c026030600c0d210704070707003480070304000c18121042500c00c62540c040c444e070000d0020324210045404036040d0340300c0081a89103c40000b90350200c40c900d24450014207080900103809400010710034003049a9034200b003145190200603962007400c024254540d544d4282c2001800c00c000380c607a8901182c00d0200014560620b442410100c4500601005054902007035550010401e204613004564895200e428403c1c1c0c006640d0401ca44507150000b400c41c50740c41414100041800381a0641e494001c20040503101e1908580d030003446900c0e180e01320394544c078050340410355207105c6c00800a40031448150443d40000c49602076801101d881c04650343c1c2c0082d040e500c0c4100035405005030424440f02c001d0003a032110b03089480f4022606500d41548514140d81126200d01c641c1001202e1041032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 294343354 1250 294342104 294342107
    0x10182901020c04060f061202040906080d1119060b04141008120301060c0311010e0a0c1e0305030f0a0905060a0c140304030203190305130e07090803030610110f070e0106 74
    0x300b955030800e6505000280c0760032900302d0320002e5485004140319000e0541c00d0f5180c0039504880150011800c104910781d00e1b10300c1141d42c0c1001100c6000410712011070100f90040004215526004c02c1d90386682c0c1280640c0d07400050300b003581115400540301d850a103011400c0040c9a417007490700e501c2c483d40d264500341c45a803814110078065100410100300501891f948403a1303c551f51905410642d42c80b00d0296030700c500600c051646280c0078081d00300305000f04080c40c00d000040740d1a00c12034151b0308015040d06800c004092000511543c0104001c001185000300940050102c508002054542d41c80c00710b046035004800000000c2c40ca510504204051852140303468800c0d100113508143c215408070340d235100564048070303801c40100b0170301c000c0600c04e0302221003d41e0640ca8103d180c41c1c0c1c4200901d051903051703a060703000c42c3d04500003062500000064a00c01c0d0001004900366402c002e6084d12800850072900c0303000c2c014000c2c00c0c406100300b007006034001c01c11481c42e4607241d890480c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 294344604 1250 294343354 294343363
    0x21605061902070b010303050f04031a0103020f06090307050f0406081209181005012102130302030613030804080705011b0f080c0c030a27030c030204050606031018290102 75
    0xc0100220710520640b804078101000d8181507d034541080d5a07120250070702d482c4036000f40e0b40000e00c6d00c0c049000c001007a24184610f85d049a1003035404441e010014400c00c0341c58081c82d220f090700f40e0322000e000c20140c6048181d4010414015000240e81900c4600503800c007000040e0400440070000341040d014103000c01d0a0030341e100e402118600c18201095104a00360040c403c081c104580540d14461240f9030344200360700c2145d4024119aa055014004a034006407803000380d1090144400190452415001d9041d026a041c0ea90b40e007569610380e01c007034407070f0400001968550758503500c00c200b4420035a040350301c2d44030b01d443e01030f41c1e407030405d800410080008191b4941e400c0140015018504008161140c8500508008460600714009181d01e080c01d6410040c28210142000043c00704518500f004c1c1ca0003614240441d80e0b4200500c0214070041d10b100039400d0202e42c0810107080000302154541040b0341d0089031100c2da007104803844010880b03402c41c040a1034103150815680410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 294345854 1250 294344604 294344641
    0x141204110a0602030d02030a020d051e09031c02180301090c091802130903020c1009060206061219050723032b030b060c010908090901060302090616030302160506 71
    0xa401d50821820020020b4490146400000d1016004004200c51421540540d01c0140400408116a152440600388001c1c040204040010840004500f042d10301004607840d11000038501500d0ba13400e1b044940c001e43c4210100c004985448401081980d4207005030f007201da0040100c00b80442c2025803c030300320703400d103010740409a00d6103180c000180c4500290012881c1f840b0800210f102c41c0e801d040c1d0030415440603e50344040025060444540c208581d082900c00c41d034201d500361380d0703a0710510141c00240070003035100e0741c03054070078101c00028088559a100c0c030880581d0b10050751500c80c81c684190214001d000545860005c3ca280d00301003280c1142d1524042c030802403100c0220f16191001c2441c0c000070101a00ca89000005445010807140c09417203400c001c00c2a00a141000204c0350005004036203d401620b00014280707100e40280c032a0314078001d100503d030a884502030711010b00c840100300c041c543c00b07001c0e04030f0710b075049161100c9031406403010702100d180107505000c8184820 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 294347104 1250 294345854 294345859
    0x1b1506120105040210030b0f040f020d1d120c070812120a1505040e01061d01030501051308030c0904110d050f07140f0a0e090a1505121c14120411 64
    0x108103c05a5103600d424800c0b440c10b401e0010b0348060303010100d400d0004208034542c006090800d25141c4c1c5001d58000c22000240f02400c000f644110400e081c103091100c02510040e500540c50b21003007003e084001c0c5a0240f441e0129090140c0d10210103050940702610301c01001030218405201c0210f600042d07074086c0090300208841d80d5480c3c80ca4124001900800340502c1d039a0182c25480c00b425071000c0050071000840305500081c0701c2507141102c0c82400211615402c2c100450041c03280c00d18800032055000c0741c82070955940c00c0104400c0e801414115602c5034440600c20001c041850050030b19603a5200041590b140240c14481851009045030742081030b404540540c06515000f0340c0c041c00b13228034125a82c0c0ca0014804c0768040740300001c981d400311350070082c0035804515038044030446101d40c1040c5640d035503031030402c80718a40c994400d0900c1d800048889140480d0030114510b60b00050900d0259034005c054003034881e400001202000301210f1052105104551180d01e440c0c1108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 294348354 1250 294347104 294347111
    0x6050a0308070611041809141005190513080a0201090f0f11030304080a060e12040f03110607021305060112110d0e1618090f0b0a0b091b1b15061201 65
    0x500196494a0782107000445a86d543c034000c26081004c50681e00d1f2040e1090004c5662240810801000078030060341c04050f0301105800c08880d851045c011144154a4100c0d035a180800c162240d541c00d601c04240d00c0d0440d580c038034034100081c0c01c2c0134444190341d002e40302c0164030040525001c40445600305245100741d02c1400b040100701400074104440302e60144002c6101c0c2c1941e0718903454111741f080342c10700b103c0f03011070f001c15004000113602044900841c02c44101210798414131400e849940c1020b908003400c000007103480001c542260380c11600624000000780301801c00309040b0f82610204421105002130f81c80f0052031f050164103842709201010701080d600b4812440380c02280e620070f03800300000004403000107080f142d00507510b9030b802040d07030742d0403031494680b420218900715810b80d00344d864a400302409003088010240700e40c400040c545c5403880881c2040400360883c0c1d60000c3d02001e1400c04c0d01500700c0a01c4039044642c000b05440783c82d030512900b0001e01040181103005142e24 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 294349604 1250 294348354 294348359
    0x9030e1011060a021b07080309030d03050723190809010b0603130611070602040b0a09090207020d1103030c371e02130c0e01090b040f030803090106050a030807061104 73
    0x20200c2d01e0b9801078180300006a07103d080154102c0c04100441c0045480d00522000140c00e40c1701000801c1d80c001c4c11025204045682d002c241e040f0b50b000c3d86d2080008003010750701a18201501c0200f1135422844500a052030b889032004844106142c3c91031000643c55800c1c829420b80900481c0c09090040311f01509514241502100c154a1a0b0000c4c00030341c1c48031200304c0d50a00c0101228151a0058002e65807a6190241180c2e1544140c40100001e24100d00014003610107100383d9201a03401400c01518850300d45562000319107804006600d4001041b0300c1c416460708005490012003001c0c02c4001d642e011105c0d0a41300c5c140310380c007098481d411001c1200064032541014480210483c0d500e04d44a1490000c0351005d841781160259151070903172140c000d623070840d0390241070b030701c2c243c0c1c0302001c1d0354441d442100c81d400f80744580b80303940549070300500001e900c10000d19400302c1b500700001407040c0d40700001140411290300c2500e10034400208001880f90030301640d129502200b000505d045d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 294350854 1250 294349604 294349637
    0x180901060302041a0901090f030302030c0615010c030e0a05040e0a020f040c02150915040b09070503121204061103040c1d010608013302010c0210110a1b0609030e10 72
    0x86003101444d28400700084101982e07010380c0d400000b60689136040c84106403a031401a40d1b0354400003d0151900c900c2c00082d040402d544000b81d584101a901d4004241c010b0b036081d01c4d02c45541c0480365021040700c2c2c011405844600c11550a031402200400e00d44210b0700502680300d442c0c8070600e000b107003002100d10099800085100c444070340004100880d640b40c3e900d4505040050241c0d242c0c0d2100381050109000d4030284980c000c100307180603160000d994208055882c0c9640c0300c02039003402d06000c2d10011007415100c250307105014020114011a4920340403000d03920803a4100e902c03488181041c801007a203110001000319560890603140d50511030003800c103a8051188101000c446803645405240b0304000f0310450112903400c843c007000100c406401f0b4140d5482d034030014810304803030202d0150b90380035000a60070702c0020b0520b1301c184004202c4880070b00044800c1040030703031503064000980303511552074581d010b5506e4007400044201080840e5403203985810030018503a51390040034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 294352104 1250 294350854 294350879
    0x90c0509152802070302060a090608060906010f141921050c0301050405090c04062405030118020f130801090b0603031c0b03010e01050907031b0e0c0d0207060218090106030204 77
    0x121a406201c29094100b24022441c1c140d860300000e401c000003103a8101029004400502034a0064407600d032036584030018004500f100f01c480900054481c803446030181e0081050f1328007445055200703494030307641c0800c07040501c1c0e4400d817400000e0284084485000030b2050418110355013080140041d05120f08034200601060240c3d500c641d90715808115503c000b004000002c00d005042403013895a01c00d00003003880b5800d03a500c01c01c41d10300101c0550162192080b20b0603241c2040466036514402c00c0004000d400c400c000f00c0c0c1e0350000700900c000c0941038002c0c2c0d0004002c014000701c0c0190707091400c5031a07160003400860103603005010003403009450421144544c0611540000e00d41d554900090140039108a2100d00354a000d0500c50400004179004068a0184030030a00d00920465243e004002c14400c04071120b140300007241c4240c50100003070561010056000d4204041c688030902207034405d103149005d4100d0315040d15100d003003010706940100f0280c202142400d2071b1081c440c040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 294353354 1250 294352104 294352147
    0x207080c09060f180601020607051c09020f06030a020c10141306060f0b190206070c11060d050a020307090e01260f0303090a060501150504061107090c050915 69
    0x1507240c1c1c1c00010900c0e162021030f83c9410074000c090003503a00000410790300b5070f142900c459005028040015201c039004500b180d0700568000c05084030240100740000c014112164104d1b03110040f5003120a55a940c0c81c0a507010748004000142d807020b0396a001803902e400340d4138850340703981814511802500310391000c5900045441d0500e00d02009c81c17404000411140c4c0104007080c00c0c41002103201d10040c0044c181024155586620041e0102c03000d2b40d40f140110cc0800c009907148141d1400100c0025184410341d030040d000b1400c6c040d103000520306485c4221040c032a07266012003000450350340161010002c00b010700c1039202a505004848100e24400010010020141ca0280e0101d50b070411104c02d110f900381094944905008042a4940d202048150b42c2d903400d11002003a044058640040c2e2145280c0300e142c82c06240c4101911000d12500d14291240108880022625142e010340c0140b082107917600c1e50381e010642d042052151946100245242042c4144e41460181c929600e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 294354604 1250 294353354 294353359
    0x204020c3910051e0c0a15090c030201051602030d030c020d080c0a0513050d12140406020a021017090708100e07050d0f0816120e010e0405062701080601060207080c 72
    0x103030766140035003440c5500050740c1d000c4c01c0e0b40c1c400034614411080c08190003d2061140d011b40300d00c03c07219409082683c0c46508082c22600d40890108019809000200300041020130f056a06000c960000390400c0e0004040c400070a4840000b107003201d030f0600603840921000d050401c1c850404188651181c000e1a6803107090080015a04a0542d020300b035505c01004028005180300e00c4902d0031070755034140714032808040303028001c00350001a403400958050700c205500900d0303004069000c06c0350784580f94142030203010048180d0520a28007441480c0720303280083c020900d0b20b1803c401c0c28035003504000702c4140d080ca40b15480e0f804000c01700d041c40131510101d078014034109560030481c0202c0255603006140240000c3e0795055010078200b400a41400b9008845075101030700e10a994549200c10610700084031440c045040349400c0d40070503082403019240786092403000010108509040318483c8054481100421805400f0040b1601500c01c1e44040c040040c03505e88000d50740c002c0c0e040041d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 294355854 1250 294354604 294354607
    0x906010302090603030c01050a0b03060705040e040f060e0a110108100602060417040f080105010f0e09100f0e030f0d050114010c030f03140a090606062303040204020c391005 76
    0x206031359400c000761140500c0c040000c012070308181c03c0c2c102c000c20f04002658001c0c0240000111024052003d40d4100c40314082112856603403036403902240980e5010807222a81c2d94801c41c841d0a03810025404400c0c8640e01d010f03280a040f41c005084c044008240740c0e6070111800e0240302d0305a0100301c498210354013054031261001941c4504d900740c000c03500910b170500c144a100003041201500000d040320214100402c3c402c1d103805071010101d50454207551664440d45410600c0541644500407000520300d000403400410800c40d82158410b0710310f10341e000d0b80801c400804035038600c41c3c58014000d292100c2d6100072400000390010341e2583e0043c00340004003e4102c644da01940080400082005400046160080504000f01a601d009680c03442c80c1550105600740200250205038400c1790417041d0703189002c0b007490b501c4e40c001007080313070070a8003480007107100d01d820000300d00d0145050b00190440c0c0341d0862845482c00611030310b000b512840300559400703501d03000304000806c3c040d440c046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 294357104 1250 294355854 294355861
    0x61a0a0902162006032811191107060c350d06080106060503010617010807120609170903190308220507081b01031505010507030c08040b0307080708090601030209 71
    0x120540d0860350454030010810103418a10194031032a1241c000c5000181880322030898221241c1f4054200ca800741007051128410b001e0004804c008568606000815034500d03515080c001107500c4440803135601044070f0f00300201500044074a44138400b81c1d55844103918211050ba0180312003d243c0c0d4100002d89500f220316680103903010b400010b009000c041d54500d4005c100358024499200041c040e007040b40c407040c444d0061241210b405000801d1184c0c24165500d030f0414100f10300301c0ea4260f0300d4a581c40014440c034001040e0300c0305803200a440b00d912009050802c100c0c030b00c0b036030300054280c80c045000076000030200d03070003007164101c04512540303000d000d6a07445540c04000c0c1242c8901440040c094400088603511018054035903d01820002c005400341c4070343c0750000001c0c5074048000c3c05154440d40160050714068501645403141548540c281e50340a9000004289800800c01c803046400c6252207070001c0651500603260f00c0c003064010380f100c0c2c0600000f4401d10040021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 294358354 1250 294357104 294357143
    0x3090602012414130606050d0e060402010c020906031608030702040606050a050d0504020a08010e0f1006060207030b100f0303020a0209060d02061206060f120f15010804030e0d061a0a090216 83
    0x200b01c400300e4075003001446c1d1605c41c0074109070061304814500504180b0030036681900860300310b008942c10307100d0000780017050342000142c0070010070294151161204000401e01c1daa800b04004003544006941c1d94509801400256030b6107030407083c02e002d4100401c0010f00e40c0701c421240202aa171000050645651000680640350341c0c2c40441d896082042d0701e140000003242822600703900070120781148045031050070076141c00f481103d0268004503000c0001c034840c42c4a1561045124070000141502da05101b20f6111a580003540160300c4480014214109410400c0d00314900b120b40780c5005090f5070010f040e520800f4181d0000c011480d022800b141ca400c0160742c03070f4868480b0029140c0c4140d51032600c00d40d6048400e0385815030f1510101d010481400100100c110040c0d6503807055944507101980d68003240071145401c80e0300120040003280e0710740b080c6282c208001d2094050b02d001d500c10003034040010740054224510400c0003c581403424441030510320f52003c150302d20700309000c0e603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 294359604 1250 294358354 294358369
    0xc03081b1b0312090606030a03080405070509040305070b101202041503061e050604060b0307050a02120703170f220f0c0e0f07020607050d0e03090d03090602012414 72
    0x180001056295100114140040301900711080f107008915000d54409074003d6454806a0340345406800c86000d150100c0e11400681e540035002c3c00403519000c0d46c03000031440410b400c8070140c0000c0d0011030480200a103650700a80c00c550440c0e02d01d81c41d01d05000700a14505000c0100078441c5584140e5035098540b4080c0c031900441c0c20080400c41c0400000060980707160007032604240710304d8840091494981480780c5401d480401080d2815603544880c150b4196125607a200203512503101c0708803d41e400700c801441668840d60303404040085c46c0040102019003d0302e0310545080349410070107446d0f211030b802d155404501c081440c1072074040c02d01005c0c0015040c00649242000c4901180080700c41d82164001c2c0b0704031405080713640d40c410080340c43d903000340e0320100014020850494540c150307410412080c050b030002c1c0d03803506d09240000742440b10080000c6012800d100b00c01c016103602840ba83d0041404400c5141040f603c5410b000410b0b1958000c03c240d0021001d420f00280c0c40e10745 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 294360854 1250 294359604 294359617
    0xd17091209130c0306080d0804110904021801090c110105160f03060b2a07030809040b010918050411010e0901090203070201060b0f030103020a0603111602122505010c03081b 76
    0x202d0030441c0e0280b141005029084a0140c0340740d501c240084803000902c64100306201d46c0d00240b9158000203800e0400284003405002a42d03c41654050000390b49060503d01c1e0081603003071000290a02d409a0191011032041c2c0300e600d13264580000c00000700d10b00080d1408048903894402510002d08074242c004120581011145070004030315100c1981900c1980c000041503842c008114903d1101c4d4640d660b0300c94000202440e070103024888090400c0c0d040600b07100814181940b406883c1d41c4200c3c01c8100c4024001170094968060006021068041d02c443c584c003032034010032800355400400c40102062084e408015030000c0000c00c800c0c802e600c500040c01c4025a40e9645140c240c40350075440c0c04c01c2c003060344202d0100da0001010b81c024030070300c8408101444c40e03900304001842e4600191159440c1642c0103900d0855a00342c41e50140f101000d0b000c0c680482c600b40210101c03810580303600300e40110b4144072440040c900401d8000510551200d8410030510f000d52151031070455034011703131 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 294362104 1250 294360854 294360889
    0x80702040c09080d090306060b04081b030c040203070309020f060a050f072108220309140a091e0f180b0907030807080301051f0f030c0c0f050d17091209 67
    0x406082c20180e405017140c401c0b24082d130000d105858030740140c90f2051040388104912903019440380c25401c09251681e161352180241510802140140403034141d0744101c0b861800296a628003000314a03104141c0000c1650588545041c01080c0c0006403040c480e08261504148002c2140020000440348030390641ca100c00a06a520098500123440040c0c1a103075180800030140c19a940110310544e5410955050307913400081d45c2c900380d034580580d503081202c26040810800023180302d003c1c50203100c0000c0b14840001043c0c64183c51040119102c541e102ca610604011840004027410f8a8050b11103801c400b0f54a43c580300c0d4103619241c41041d5000900003040410408203000005010b14101e4606941d0444e1138403c10300c0100085d581a00a0004100300c44945980706100e648890400141400c0c4403500c10300c0c0d5140e0440b00102e28404451035407000f0400c0c076a0f03541c4891445409020001d8560990030003d04c0b1a494541250a2400051000c80c003042299180325210b240b20041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 294363354 1250 294362104 294362113
    0x201050306240d09021216230405100602010c0e0904023001060f06020610031e020a03080c010b19211202010b030c060c0309040b010504030503040b0301031a04080702040c0908 77
    0x101100fa0300541a0890143d10881c0b80c0b0324562524400400c03801600b40d1002e81c40b054250400503080344a100703846a4079130950450740d030680d598450707108460240300a442c409403101c1c903155009080d03a004000d8502006181902102c0640790306441540042c1c0c102c40b140110011030172080300841c0f8940402803403a82c05030120010321410741c0f21401740c8008000c000015615000180c0c0c0e070305010360302c12140102603842000402c85141440d400340c000440700c4c2d11136030850380010b4000d030313181d80007614580000505000130070f00901c6031081d51034090328620700c5049103080c040c1d02c540c058030030805035a056102649041c5110000c2e8110f11354864500035810042503c028000c00c80307540c04501034032405200b91518500703141618400c10343c00005514240fa6141030001510907008414103004090001000148091001c1c0024000701d0786915100e43c51401c245c0e00c0ca848010909600104600610000c1060070341110f8501d60181d90215202541b6403044032424403581c85003015004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 294364604 1250 294363354 294363367
    0x10c050a0f02030d080402100f02010e070e0a0510060f030506040b0a140901140d02190e07050a080112080306190b030a0c031521080c030a0c021c020105030624 70
    0x1c100c9009200d00d00903011944114207030041603900c50350654029600110604208503014403518007403100400710f100214902c800e900d00d6918082c1140c024041c10524a0300f040066070036840740580c80060540ca051500b80f40000c0909141400c1e0503040815440e40c000035015200c0c2d800078118810050441078500c0d44d280c41884405010030300d180e209500c00d8000080c0d2010000c2801780c4130720000d15103504400d00b0313801c001d00080544265003000107004000034040031045c000c1407260f1400e4650942c0d50001e480001c02c9020160414001c0d001c2645040001c250030f2800c5d03d601c00d1080c2c882c00500070308105c807001500c801358069150010000100b060f80d01d05504012100a1592000c0c026000c28045040d12000f4070301900003001d072494041a441022140d045921a004460f0075182408036481141182c1c424040030300415040c912410071810106540c102c44401c00303803040f40e6080c2c10382c0020094800588510720403800c1c01e1170f1022020360244200311129105002940e40d80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 294365854 1250 294364604 294364613
    0x50c0d0309061b020f0f01020721030216061e0302090406090c18050d0b0c0c190b07030917130512071a040b090d232b0905040209010c050a 61
    0x501c0e9018842c00a64500c40c08100780c00040b19001c10554002c200c45503008044003449250540780d001c0c603045105018002030728030a0303500d10100300c08441e040c1074007110301c50801914040c0e80303242c501c06108418404216450344004900d0355501c2c00380e241089000400c3d4110080d000c1c201085a00c680b82400c00500d42d000c1d94840703040840329490350421040e0020075031a00785200d114233900880303c44041c0f0000744004850a80c08280c205e03d0a0901c181d40d08882e150485803458940701c001c03407244103400d200d042c0b49840c0c0d002c5d4061074240001921039a600e00010740c0c942a400e000800440e03e48130080c800c1e40401d0140401a0a4400d00100b07070b111196180300d984103081c0195038419070200c41c07103c0b0038111400e442040381101c1c500109901800300729032040030f0655000140402d082c200101d24444044000c082c0b20080403200001c80e0342d8050700700d100b100e2403001c0700346c0c8008a501d5500f0400240444000720f800507110300c40c440040e0b60061705c0e03040080150017829484000c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 294367104 1250 294365854 294365867
    0xc0111101a100908010f0b01020c040e010618060f0504020a2c060c030d050a020403051f02160f0b061c030507060603050d0f02010b010905010801090902030a050d021e011107080304050c0d03 83
    0x13038071450001c1c44914201c0c030030b8008444219a03440e0040e0802144040c0a042ca900410750440f4184000915903684164500c02000034400c84003202c3d859140c100281000c182404015040803202103181c12003c001c060082d00000d0a050142c408201c924411048015041e81420f403015010607510264400484c1d00c030f5110341907684c419031800020440c5810140309071001d6a5000300208490310110810250340c940000161107219020000c10003299202e00400781d05610070031130b4a41049031803030b0010844100a000d40c4c00f41d207483c3c036100840b2090b0550112101d8050400f20707554841c17418000050043d80c0c00141580c03258040c01e410882e0302000103107207000c065000300a125040c4c4011980c0000520400d0700142c0c5860044c0542c00090340826012440107088401036251651003604024401d402d000c00368001c0344004150141001c2100002c003040c4000300302d1b04c142d400c041000c030300800340c0123000e5920200001c0c0410000300801064a00300501050001d0510318004020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 294368354 1250 294367104 294367109
    0x6010c061521061107121407051506031011031512010603050a0209010b0307080612010b09010906050a080304030506041212050103420218060f03090c0111101a1009 72
    0x6013854504042100460740b01511803259009551000c42e03101c0d05821504295012801010800200701020010350104081c800d084070442800016103454002c05080c03d460091103111f1506003000d142961a44004880d07009a50b035040c503508400440c0070800c0041d104141d001c0755881e0038000300500400169103108a4030850b1810b40356030329101e841802c1c1c00705540031700203d61140f0101c0d9813803404200e0004540000c03800001e06c0300c01c0a002919130103003030b484aa0b5690341e5540521050070310506010141c918040114502491580d500e07981d03020080c0003918805402010510803032141a6030b001e4028140d03000e000e2035031213081405004080340841d0803034502400c0154507160302c04841c0c0800b513010440a600c0d2101401982c0041d60140308205d40b01e0f00700d41030103c0a83d440c4006070024200c0c12000075203e1929200c001e107402c4103d084a0b06020b81754821500d424400906c6266030101440042085004282c10444c025824000310341d02507030043d0394441250741b1a080d1404c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 294369604 1250 294368354 294368363
    0x402041b0207031101140a03060807050406030f110406080604061b0e030d0c051006060302040305070b030112030c0501150305060406050a15050402031816030b0c0306010c061521 78
    0x2411003054040d1402901041000981c008000c1003001c03c1064100c1141c100c010704000c03800b0603840101440c0c1c1d030300080081d80402d45d507a2043c030801600b0400301b8090310b4295030401c450390a5840d1040190010790000b01b503c079084800600c240c841c0c0d00900010482801100d5aa040520708800030703105003010661034035507951500105c0e504c03810303244a5031040500603022680b0303001070447d0081c21802e026191440740e000c50404d9400305100e254024038955400680b164214607002d401c0c000d1a41c0070f4182d18005100502002e603c0c5100081e140f64142400b41c03da0306903280c40c03805800c071503441991205036448008140800451040d1045124030702c200190794070200703880e00b00d40000840c1c0595845c01502840382d410142d000399002200d1625520f64590360207210780c82d00d41a000680b13015450f8010400c20481043c0c02142c000c0d505d410000d095240080000b45004c1d005180074102d10307141c4440e504050840c0c51810003a2403e2070802c540100b20418a1281c104d1070310040780c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 294370854 1250 294369604 294369611
    0x3121606090b0114090f01051201110a09080613030233010e01060e18070f0e04050106020a030216080303060f0f030d090810020c030304081312030c0c060807140f0f0c06040204 77
    0xe2600c2017005105090040840905174240310070300c02200741c0d8500881e269980e407201c0381c3c090494070014202c0b00d041960303050703100f60500701601e0401074050844440502c00051030030020780c0101d1540300b1304c0b110031a0902c0460700042070b041529055000f0600d000b81e204c002207902400f2401c0c5074141c829030b450399070f002c09140c02885500b005203070f140c9164001c401c011410040c4038400c84110450249800b0140048210000b001c48800ba44500050382c001402a42016014040c05c100c4030104000390304800c0c6810305440c1c49110050440b40b01c0e1422620b01c109540e5801c0508028540c0a811201d0501d840385000d05444c241d07014818a500c14180d03d0110403881d402150b42142c0803002450842e01d903950780007501c0d040b201643c08a10807101000c20008101c00d10000258025525400c8130801d0342051003621140d0740040c0d04000c0030700d040010b841d41221a43d070102303020200c43c07507403071030000c9980300035006144200540600000b442200c0c0117000800c5030195000301c9080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 294372104 1250 294370854 294370889
    0xa0515101203020d030e0a0c210602030f161d091b03100501230706111c02030f0f0402010c02010c110a03060f0e01050f040b0a140c0d060602070503121606090b01 71
    0x482c0d035080002d034000c8c00c1000170300003406045140340c030514904184242c00315040c21140e8a100c10390700103d690860400031542000f081e4612210ba880700c0d40941d09100380354044481f45540c0341101121624040c1810308040740d14014805450b4140c071124480032921b9007042c165030b01d8080d8a5202c1c1030300060b020148040009480b812160001400c0070181d480d10040382c5d1840040c003541106000b00301424441a80896075051040045141105d0016074910305800014901440900340c0c211807000c1c0710030000142d82100a0a10040e02400e041d180d500703217864200700e09040d040c9039503003040130f80700c001081002c1500f00b040d1484404205002480c4201e4103182210030032218202900c0421307003c00c0100309030f81011604520b8412001c1117000d102008020743d00402c1e0340300304a103440020701c9052010b41d4400c5a01401c0d9038406454054034210020b6aa03121201c0050b01c90080000c0c204076500510445aa13510382c400001d005100c020300301101c44440902c01d98100d0324030040803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 294373354 1250 294372104 294372131
    0x10e07080708070612061508070915080406051023211e1203010f140d020906010f0c0c090207030215040218041b030b10080a0515101203020d03 63
    0x74005440400700140360b06444c1807030445080800c1502618201e075640c0020414101a02621200750101d403603103100340c100300c0001004d001036684810101c40f0b02266065015603c11520b5800c541c01080104490b100d4502c800410103141d0300440e0b4405400080a01c0324203002d11400244a046408600b00303200c1d050303440b40d481d138074030384031400790300051402c520700c2070942d0040e010180700310304440481608110b218446c0d0f2003a0800d44c008151600c040021004400100722483e00c00da0310740c0801c48403680403400c000c00161500e0f0501440780d4031600c16610603041c403c40281c01c41c5043c002d407980c4048003c000c0d80320307420941c014041e10140c41c400503014001d19000315805408400c010226881042e0403c0c0082d000f1504a203c030308a001f46103000802c100b0107980038540d010450706280c070085484112942c040301140d004900e210300400c00200300c8407942c1c5a00d003904041d694920710002d11224803600070807403600d00103010304141940010140d008800c1078034101704000ca003801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 294374604 1250 294373354 294373363
    0x61806011202101403090703120c031211090a18200a03050403050c060a060f0807060905040b0a080d0201091703090307060c050c15100506040803030103170904020408010e0708 77
    0x1070061001c005107607003001414100d542c1110014a03151003000000044c48048041e0302c15a0642c0ca942d1082c03000344180041c900f480400703032103241490500d500f59607502400721001c0c0303500002490782d1800e10085003881c04044a041060041502c003400e5101c00440060486400b000b1540500d0306840580008003107505100d134040305000c05061003815581203000d060020011000c00005011481c02200f04100483c0110380c0c000c0c021031283c2c140759411001c00c130141d200b20f1780c81c1d002d8070003009055002591082683c1c42924042080048200480d040d091503a004a002d4030400ca174483c420344c1e0660002c9480b6128162280c1599800f03101d82d213035070000340c031004c0154008200c40f000103000c40d030143c3c5202c012410300e18108520004401d0410703140c0700b210654001d40908000d21401e0403403615010b42000c5480906250920000642e04e0205010040c036804c03017480224041d0f0001820b6894104c0020300a40d5226140c100b55400307401610f020f00e42510034000d0205d284c100105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 294375854 1250 294374604 294374609
    0x4030b0c0f0d090203101a01030e0303060a03060f11041d0106030b010f080a0e03030a060e13050c100e0613050306070c0b0a1518050702121305060901110a030206180601 74
    0x1d80840c109106545208000c0145070780881e4188501c044484002d443e0303001c0c005200c0c490380b5540806030703601000502134600511454103190403c004018403556400b1041090729045200080c075800c1e415030300c40086c05c5e4440b0b40030b84544d003c00c0003d100600d0702840a000c2c0382c010141580ba0366600019010340e50007882c0703140410282a000585140314051465100041c580d003c02c20380340502400781980e0066509109041d12500103004072851000c034035412501c01d581440742c404468803025101c4c0c0616500e18400e941c038101d100c00181c442e00c140c2070000d800421050b6140440440c1c8290400c1c2407060314080d01600c000605501c0c000c60005100c5a003000411410b90382d19101c1500411841800320184020305001040c00405d4400c42801e2000381400001e02f82000007000c3d01d080c08022101c5000c100400034280c4000303001d00d50f002111415140140c44286580060710308034011100a001881104c200344240359000861a004022541d80050282c40c48603042d0748901e801d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 294377104 1250 294375854 294375877
    0x1912060305030307050c030d0c020129060a03150e13030824060a0903050604060501030203010e0304080d0503070e06160209010b04030c050f04151508010e04031709010204090c020304030b0c 83
    0x600004c0d103444c0c09100180100400390080d645800304515840d01201c030400c10000050703540301201c01c0d00d1010403107044640541a40c851458203c240006062446080d280c40300701500c41082c401c14070015246c0c0000340070148016085031030302003c441c0c4520400d11046c0c000a09071800300e06000412004d000f40c240d00800040082c1a1030380a0083d40c0d48aa0b409008000f02d09100202107502441094000e41c0314680110721945540101803d42d600303402e40d01c00c030380c10422007001401800900794550030f001d428296200d6944000c1918100b03086c2014a1300a280003070031108204141582d240320fa842180c2200250b62031304e011010500a0740402825400000300900083c0340091022001440040022443d1014501c80001080f402d900090035912408100f01e602a00501c0d4a40940030282c0782144034a8151001844c4450103885806110128000b0401041c021740494020300040032062283d41c0e002d80d0001e50740d40c01403009841c0101c01c4000326040c42130203000c1715800d0342e40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 294378354 1250 294377104 294377107
    0x50c0405100c05070911030f07020607051801140d020715050c040e09101508010606030506060904050717011511010e1c0507150507020606010e091602010e03191206030503 75
    0x889415542282d000ca016a0360744280c101c0094114101e00451082100c1c0c0b5021039240e0400c000854030f203000203401003041d90000c8082000d01c41c0e000c001e4640d103000748000388000340316210068030b4151814038190304214001070650350400701a001000014454014403034a42848104102101c800b82d814100b1140204400c111451012201701d070044014015549101002a40e8400f150400524000e01c11031001013004140801e100c1c02d8001c00c00c030705040c071483c608000003401314824410384521032681d42c0701080c0c400b441010705100c0701d0406141c04d00c1c296154040c1140c0f442800101000141c800030900d1030540040c011502240001c10050048500102003d0a40d10300812101304010040c045840440c0c1c09100400300d0055108000409060070b1078000e0402030300500150500800c0108410b41d9198040406d80c4000703d8492260011100700040f4058104030004a60034440803401204504ac00702c0c016800c004507495008041040240380070681d2486d11001c4d016420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 294379604 1250 294378354 294378379
    0x3015291806010f030e01150f05010f02070608010302090411090f150607080a2304060801090507030e0604080f0d050a050105010f02070e060108040f061401030b012909040e061504050c0405 82
    0x42d801c0170b000340903440004150807003610051800a0225845980f000605082c20041541c02c0b941064106189101400c401c60524402419800040c030000340030b0460f100c001810300c038000b0440010103000500307000d03c5c0c0c00c100716031200c844030980d11960b0b00f0b0403d00158a0921340007080f60040c6522035895810400fa03600c080e500c000501220103110382207401d440c40b0a02e00070780107101600c0240c98801003541810000c5003100c04c014140024140b40c418607500c6100001000c66001c0d41c01040d080c2d4512080e11001c0e03503400b400407030784880c03070904041c07041e545071075003085c1d0682d5020781e02d406240a80f40c07001c9030340e41002e10810304020600004604994132940203254130074000c1c2180783c21000140e440320308883c01450b007240303003294440041c0100a0501102e90042100348491302108001c2601040c5800b4940725140c1341d1940002c200600b42c4031b540140caa2014807c05803522840c0c04c0011001303031011004081c1c444c601c1c00b00001c1c000380440c0d068400f91503000d04400302c03070744 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 294380854 1250 294379604 294379607
    0xa050a02100207080604081218101113080a0b070206100e0403051c0b100e01020705040b12010504030f020c04050103030903030f090e09073015291806010f 68
    0x1d0740c2010502180524031001c03450000400c0282d0195110745c66595850010450406501030040c21b80100c402c0403584241030003100054600035090001c900042103002c43c2021035007441042c01a80c50f488803008000303030044000c2002c8000d07038085c200310041c0ba555200f00302d842e850100c0b4104019600010140141655941100da000c0c2c403030300740715203010590f56491074000c203461030f050310f150340326480101e050821100445d414942418403000100040e80043d4555038503008980c0038a5441004a40a0b6504400034882180b41c4008000c00d04090030001c8c00c903004071068202502c26140728424600302032103140d04a0341c0580e0340240003811503908a604d281c00d03c140d601000012900480c86a54180d4198022182d010041541ca80380070582d550a00501c2c960100c1520b040304015200300048101c10806e40d071209088400c0c07600a4142d100804020340001d50343d40301c4140320701032028583c5c0c0602c5111022150241c91141d081c0c0d042401c0e04084030f986000540d03040c50603401070b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 294382104 1250 294380854 294380869
    0xe010e1605061201270207060f1d1209040609021206030601120b06040b06070c080606011101050f0a1104080319171b0d0b04150518012904260105090a050a02 69
    0x1600c0d04d14030704005e00d103d10304241c1e0480c0409644055a800c01029140707a6442814184402c82548000c400c002c40461030700c594856601007a0f14000013480c1d000c9941ea984082d0107455006005c5440f441140d4207082d041500f02c859074000d10030b40e800403400048101451181503448040040507955110a02010749803009a103600b1040a2080000043c640300c0404c0260915100403c0903181000004100c01d001c1c480f13031034042e4500030906c0f80d403048910106900103040f0344046001124625108801d00c074981c84003000340408201c1420b44810741b2200040c0340c41c141e848010640c00100c5007001c12805070b840e0f1070744c5640307501c01c58513060410019220003030a01e900020301c503c5100c0801c2c280c1d0700c41c1200804203550b13801c0c180803600c3d004e00d6054100a0090b903564081d030514440c00110b008900f2a008007903005c0c0302c0910500303076901c112800340c0306181c01c0805080740d42c1c41c8030500c28a1008401159400c0800143c04090002006074036140c00c00d004042041682c6c0902416 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 294383354 1250 294382104 294382139
    0x5030a050715030b090f0a05011e050d020d050f01050703060501092103051b06041211061504020403060e010b03012403170c0114041104090804051002010e010e1605061201 75
    0x703054450041004681c1d400040740d00c51b074210400c1c060103107003032115001110710503080440c0348804522402800070010394200280c450654100c1c0c01095280000340410b14100801011440b0f6900f120014581c10b400c024020100c03501d080c010140c54400655181e9070300e00582003001c44a6103401140450f141c643c0400720700904000d480d125091480207184810007170710914070782c051401e0008000c503894103101c0d1403810b0b140078103406181c00e040a03201c0c030000d0400308450289400f406083d680300d034100c50003994060f004014209481800a0291440781c4045109500e0309046045104e0700b4405001c50650170304c01480702c542180d49120401c00301c0518107503401d100388205440c8080900c294030001460700a4a1a0341c60180f84c001e0301d20040080c40343c0203504084010001a05510548064a00440385803001c42d03030070b4404900411508200703041039800c2c81001c00ca206004104030039144503800030f1000746501e4405214240c8a00303508120501c0710400100001d09090b0b440c17000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 294384604 1250 294383354 294383357
    0xc03040e070e10210606170109090f03080415050f0f09011b11070801111308031e2532030a03020c03070f03170609061e03010b0901080303010f05030a050715 69
    0x240c0d507140842c4041724200d070007a10101c1ca6159000c2d104003100620a401403005d89802d0100f2001da0752003500b1001116001424061218041006c011b040c40303580741d128248840c1040b80d1710340380d40308812641e426200c10000b641c000c40812030f0b4020600483c1010192102d0110700c41d101c13101c04450300a02a48d4244050003540d40c00311381c0505c01e0040c0315450401154007615160901145941d0341c000b60310200050744104041c1e41071844099070308182164021855807034181e01410703459407103c40d683d0780b032400f03241c0d90040040095010480740d00d01c4041d0b42c00321100d01601c00b070000d501c0075468840c5c03156105120030740c1128441e400800607102124242c90500d000d07940c0c1d07059015070500040f00440e00c00314586d20001e1540c2040b03640003c04031102c50f401c0c01c2640c00301c0c01045c03640c2824240103031401c4880e0038a072000d41006071316410103400214250b9440580c241c5a80007809111200d205046000a20385030000d518042c181d0410090040700b440e15000c640ea820007a0448030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 294385854 1250 294384604 294384647
    0x10030e060103020f0f27130b0f060a0b070302070e0703200a1110021e0a120b0f030a0b0405190503030708071403010b0d060e0c090409060b03030c03040e070e10 70
    0x4420740707600403413604106e007402c1008444261854620380c1d20400901c4051040c00002d1a2408078240d191403036089021a070940c9001c2d12000c020403569a555000040e10010000343e00e41050360028007242122181c1102c0840c82e128103e040b0299401c0d014620b4080f484182e046540c91101340080103000c0c4541800c90844041d070044508004100c03040301d52841e4003059880d003400405481c4a032042c04501c80510340940c016000d8441c541c4440c84110103aa0380d8a42d005039114000d401c1240000101203d40d000910f01c0c2c1808040d80468003114103015500307424030b03481e00701c544e5401f0090b4044051400c41e5103c1e4801c640c1024010522410892071951076210036400d440194060604c0b06c103030643d1000a520310a056640b980d0020202d241500c04000c0e40101c900203075922114211008205107600e400d14402414800240b01c3d41800002a04030f80c2420000c003c0044509800d10300d401036441d0030701520049250004244c000c0800c8181001080c890b42c28056020f50000902 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 294387104 1250 294385854 294385879
    0x50106030e10055a0a020a020109060e0a061104030b01050d03020715110f0708121303021c02120601080c04240303020102180a0f03030509010203161110030e060103020f 74
    0x200d61a100d0300b40000300b00802100510040105084001c0c91020004410200c20a0400c440138424001403c0041d01c9901086003080d180c0300390840103103030360000400d0001c000d4828420391615042c0300c041311224a400500114402c2c62010f440490b50000c1c0b040006a20300428810410102141102103008102c00401d807101649450030b41d048213944c40500d10b158044490340f40500483d014072131039201060801c0240c50000702006503111a21403251a4148021402410111504029072284080c00320700c112210a0417000203040c022031340811a00b007480c080603160fa1080c0901802904529103502090805030002281c1014440c15030750319038001c0d043c016141110b50001c500503500040e8950401c00700b510000301441c41202c4c055070040c507000110038007407241c0c1b00080a0200103c0c2e2070800340c3c002c2c0251181c0c481c11a1494070210070f149001c0440000307251566100d00c80c040515541c00f4840d12882e13075190000c030000c1c200759080d034080000c100300e0b1000300c941c08002200d51 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 294388354 1250 294387104 294387151
    0xd020403050106030b090c0906010f110f0d0e010507150902060720010e0f031005090c090106030204050307211103031c06030c060e010918060b070b0406050106030e1005 74
    0x280000d50007000001001411072418040c0020064904a210b07881115500b40351f5455812541e08140d0900303117075048100114050b40d40900001b981103041c01180540200a0300100300300807045920394501c01c0718088080151028019110084c0400c48038123a0b04d80e40440580c082040607000904650400006550b880c852030408250550648103503001001d455070002440410300004898502d0701200c4040801d980b03101c1c3c11404540d55482d0b8003c00c0440c04241f1042600c28005064042e4030740e191070001e0065803141c4182c50203845101c9001404403a5035844081403001d210000d00c220341d003510354400a080361000c2c56454042080980d400300c2643c80385011200282c030011070154a9410aa019206076901900034030400c1c910f48855aa0f000c540350003942c5440c3e003e40d29903a14071005000a0405400032207482100144260900039215500d910461140509014580c0c03a080224195441c013904941581c0c8000c1c60303540e850030f25400c02940700e809a11590001140287d9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 294389604 1250 294388354 294388357
    0x90606041e020d021b03130801060b0f03180703080316030216030c0212010c03200307050f0705070b120a0e0d1407060b0d120f030b10031a09010e010504060f0305060601050304080d02 80
    0xc4014446d40b0010b0501e5111401c0c03000d40f401403150f14000c0040600d06140e5000da80b20700c4484460624000000403510844070040f0201611207400b1230702c00e103441c0d2904284aa10940301100c0000e90030618500c2c40b41711f8002c0f42c080061403e40d404c400071850354141c0302180d482c40200d81c003541d103020b00301412000340b181c1d2002003003a43d00400c06540e00040b54001d05510000c90004500402c10080c85507049012107280e0440003032080e980e908113003456400e2650607007150120802c0041c07200c40d0740c00b5683c00305000e0600404104004141f41950660390001d115000b004980c400d800f00b0360105c54000500706090240d2000704507410364800040740c20707451110848402140b420b060180640c030031080d05041c81941020401c2e00d08070030019100e03c041700c2e02c410805840d80000e450f0f00721b554061682c1ea01e8040c02e1034103503503111061400105d40034043c0501070b030b00d009070006840300c207001c5c01800c0741d4101c00a05503549a040c0110760690000300240e6945004022000c46540c0c28030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 294390854 1250 294389604 294389647
    0x307120f020d060e0c07030c0c411305071b05010911060a09050907110a030c030206090304121202071703030603100501051c05010f090b090606041e020d02 68
    0x8000698818902c2ca03038070200d80540d0841802410703548200500403100c081200d840340d41500f003007407420030b00f458124140340040e00704081c440c2607031025044090002000c000040382c019001c40e000340342c0198014105031710142640d030014402b43c00341d010840990005402c007400c1c1c6000d0a427100c4040d00040c914050f90b004840c0c6a40d1600d1301800e0169415800c0c0410a08683ca10b14084861304014504801c1e40549441200345201141c1d40d240101c800408034601c1000b5a035020380c2c0e034140a041720844d40c20544c05801403100168524034048201c0f0152203a80841440007042501c41d070300800500d141c2c0f1810b501c0f0b03642d03002c43d00c42070070f003030b250300710301644008555901d4148145420040701c02110f0040304c0c2014014010703a075440303070074103a03c1e000344580103d20741160a010b0301402001c0220b04009180c901400240030b690110380e8420004901100c405403511414401140c21414280d1100ba481840110202c80150010045050301540c098107002d00190644da0080422 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 294392104 1250 294390854 294390881
    0x5090f150a050c03160f0302040f090203040b0108060c0711040b0901080313150c02010e030a02041107140a05030417030408100f0506030c03031c06150c0201121a06030712 75
    0xd400308244001c07240181a40146080711071402c1d401d010101041d98441007100c0010f00803000d442c006405e02c42e9064070700030120301111201a65841007002c0082d0300c00e88060b54621540000804c1c03140d4000352031805040803216803444c143d6903498088002c01083e10080d84941c0ba0a02c20701c0b1a80c4451003540645502c00155a0380c04241e0a4441c0c1c0c12a1940500715218a0b10088880d40b40c00c00d081101498080c00c141e51242c809a0000b4103208050100951107840e0160350640075035020043c2824070f10a84154003c00c0000050540c1d400c001c080003401507108200c02c0c4502e17582605031205c0343d0180c2040300d050a845a006500348081141c2420700d21380d40d41d0700c40d00e415a5070700440360824030030350250034000c0c00400480d84a00c00c0c4428900020101c0d02c90f4201a05654401c100410170a0795950054510490090484203029001c1e40069180c045801c00300c2140c1c41031174500900c03010728249081440041c0140ca0708003e00001c1804100a148200600e441c010740107200ca26 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 294393354 1250 294392104 294392143
    0x608030a020d02010603151e090309050307081f090f05010e010504021c0b041709151e16030804020f030618070b071502031308040f0501121406010305090f 68
    0x944100902d0a00b68003424011a818040100081401e0105659020f0a02040440c3d0000e10f140752422039440c002c0024400741c6804a41000d055000c068001950030407000e856490f5038864090f9a1440c408580603280c3d100600132005010b440d911641e02c4d030b446100800c030510017607200e50782140c41e04403552106035120f80806c03003149050b20541198403000b0b0204245034803207884500c0c01c00801440107182d040019140c1090b00000c1c0c040e039401a00c01403040e40807181001e990040381d04030b21031601d00d599074085024072600010086c0e0320080701403010003001000d162000c0792440005482681c0040c91405000f4245d1018064144681082985041310360038001c175a5103040700d1a44041030080041c0700038800250126062408203641401c00350f00d0f034950840340260030a1180f0000c190840000d030010b40400e0b10b005800442702c098a0321990800b0780c50301e0200380ea00701200c8810010300b01001408a60082c0c0c001500900b1901c1226880450107900518280403e000052203000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 294394604 1250 294393354 294393367
    0x1e050a1d01050904030507030f031503061b0806030a061a040e03031006020f1020030108070602010e07050105121302030d050702090a0c1e02250302040c090f090b0310060803 76
    0x4040c095074010700040d00c1d0701003240342503100100715000d03c1e0030003003c0046070700ea01e504092080d003064954a4040483c0030728148e60f03280c407000900400540120120344240d031107031040d000305401c900c100c0f0040c1c041d0001d00c0745075403088000c010800c1c483e0806e650002c08000300d03403654810700c1178404018008503a00d0a0668170740e9200042a88a5411544880c10000654a0200761107040750450100801c60300c2405084200b111614144042c2d001c00105c00081d1031803000032081c08881c41500200044a48940c1140e16030509018940c007150741000071459041c80c0740a450340c04064207000082c421101c0e070000381040c407030062130000120040b074000c0541c03410031441600312400040410118400c000050044030400c042c0c5445c4401002d1241c03061802032141400781803260080505c010b00782d0010802c03030906401b00703030b0056151803ca0000a800741032014280e941807036904150b24030702081e2601401c2012901ca0309402044801d0800340c0745809240098268007000d1501c41a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 294395854 1250 294394604 294394649
    0x1b0f040503160b1e070609030203041d0402091602010b031501060e04021201051c15060f090207050c120f032a12030c0a171f06020d0206011e050a 64
    0x9071a02e40001c20449681042612500340850300d088150300b5030040b034440c41c030506041c075000b150b0015140505004202c402c16a0100080c8142c0d0310700d50708511a0140d000401c282440d04a90007901710800f5800b1882043c2400900c00380320031584000b1940d10005030203e030914400050018191405034010f11007240c00801d1146402400e840444c2041c4640c840c48100c5103040c0300d4180108070100c41e5400381c4001c241d0f078201e5542c000c0804407013100c20580c200010091482010f10f088440f650118102401703000305d030380450b0418018a061844d2004006000c0c07256018110644030b20a000300c94603000703002078507542948d80450942401320700c0045102400c20049007031250041d01180540300c50340c03001c2ea50002d90101c1034545802c2040425200e0b4031114141e50741490701e00041002040200d000d2500031070101220726015507880000340d903191440f90501005d80c01910041c0408089017944c80030754240306c00c1030155150740c0c0c0f000c14012881d540049101a03640305040b0700070b0703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 294397104 1250 294395854 294395863
    0x80a1b05100819020702061204050a140d0e0f0303071103070906060809100c050304060b060403060237020a02010e030a0c0b04150e0913051f020a030501050f060306091b0f040503 78
    0x42800e42029450010f05d0f50018241d8401c402c2c600d41d0324000a0013003000d02c84208064001e081d800740034a42885032006c005541e60084481e680002418403c1031045418150301c003040c8840043c0c000e40c14032140b82c2d10701e8803418941170b0551700f61103800750004015241b03000d500014000c40e203c0201c2ea040c80c240d02820243c002010319241e90500d00840f0b0b00c00d6000045950140d0000400a0880d08031800114a480703150303c050075107800412040c410f001158909182076501045000d022150006d442c00440000210100580c116450000c0503500a003040200b021b07004040d900c0d205090341e41d0030035001c10f40d000070800c00c1010a05002521100d042c0b180c02c1d17407032801d02c0601c0d04c90460011381320400082c0160b07042882c0070912010011300704400725040f50040b01e111344100450030303001d0082d084501d00d50000f9003082c0c00080d15003800c0440d8109441c024000038a140c0d40c0038103100b02d01e48041c2a42c0034000c07a1580b00134400401c1e0010f040842c0503914507a036921b00d00401c05d03241 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 294398354 1250 294397104 294397141
    0x506070e090603150c030709050a030b24030705060d1b0c0302120301180903200102030703060f030b01064d060709050f010507020a031b0e01080a1b051008 68
    0x1394000c0c02d10700100c1e501880503682c019000491165295240c610440e00c40e031007984001c2e00314440e044040204203001d01101d203c0d00d4542c40451100e003c648202c5003007642000703e2078140d0410f900501141c10100c008041c1500300d0304010075083c008031000b040c18100b15200c0707c0054441c03c40c041c00c0650500000c40c1300101a42c5440c15541480c804608106000717103000030080c0d582480f003040600403103111b5500802940d003110450700014415010354011645900000c0c900080840c032244d203159500c2c250b98221001c01e040d6802c02c032042d03035400580749030360517480700c0140c14a140140b680c40d852003608507401480b40800c68922064290310020383c005805400020401c8070031984100b1890444030100d540300340071910040103036101d105e0000042c0d041a070201b408005c0c080c51240764020783c0304541c82e900760107980e010314000c20340c000c0c01100520f4000d5920500424040760300014403100d540c0380e0341c400390340d5640042c024244455006010500c44c10420400c402b50380e05000d803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 294399604 1250 294398354 294398359
    0x7020303041e1106070c0906050301020403150903110307080705010c03060e190609060e160903080a030906020405040e1005070f0f0c060b0405190b0102030403021302160506070e0906 80
    0x10350034680d480c0c14034044404a0b99401d401400001c000340301d0341616202d52a10050300c0680e0702d0340542000c0704a4441070280200407802c04a0000b0281014421901141d40112540b1202c3d191800640c005c0c041c02e01c4280c007008510340c0384515148060000300f1b4414070901c406580ca00c043d25105094032480c1c2541c909051034034800700a1303103030782503c9203900c182940c200b490f44142c10710800000f08683c1e085039002e2440d01d580401e030300c0000c488403030048c0c40c1d0300090002040030750b10446041ba03403400b004000e00000d1051001082c040d8006401140c031503000941040d44610101d41210780203520000c1c0d0358481d90b54803d403440c0520030550000325504d82151180360360000030b001c500300c0d02810010811028000824001c050b070000c50328100040042c010303414034443c0c185480c7d880d00d00d035449041c6462075006c0990300010445040301d43c05415055102c0010340c02c00c001b504900410303401843c0c0c2d8210305002803800d1001a11600541d1640c4515903180f4040c8003242c10003c11550 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 294400854 1250 294399604 294399607
    0x1f080109021306030b1801060c4815050a1d030303061c14070512070612180209010e090c0616060b0d050a05031b0105130209060f060c0312070203 64
    0x1c0100740c6150302c42050b01c03854100442c0400c40c00001c1400112a04a500c01d50710024001080c603940c041e02d407440042c00780381461989640303401f65104030300301e0184d811542c04c00d64032034451500190002d240c2507403050038283e44540d80c8805140004d0301c49442c03d0006040010b900000395080400911103a10401814a940c080f14020070fa0707900c4003034611341c8911441e04414265900503c001d645440c0e000f01c5141041032031103100360703a945150040c244122186000c1d52048580000c55400f1178070345586644080c84400c5034003008046400c4404100380f41985c2050240e154014050300905480150b0001c41c40c1c01e80303030603013031002182030180300e89010808444069030384043c021580340c00c51400904218400300107a13401c0c4c6140001022070141c00000070074001c0c04809008180c0c03040b900d030030400a03c46296401c0f140e04075006c42522400e4412900503060840d010381e80480060091140c100c070b15000038009402c503083c0031559500020b15950301d5200c401125401100900045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 294402104 1250 294400854 294400867
    0x305040f061e0509040f06080c010e010f0f05031b0a110d110705041104030c0b130e040302150405070801020c0102041401020c09130620031b03060123091f08010902 72
    0x5a02e095a07180404101001c201c520b1a9a076540c005020007084050811010399103210706074a4030f1421180502007051220a1062540641a0329000310310340e641d8038040404019007074600350001303056212900103c1d5201101d040d1410000d240704500d07511400c10540782e10706050b19200c1d00e0321a43c000c01810b82e0007501242030016120003951421500420300d00306038100c03480c840c000c030fa10107040c600301c9041c00201515207000902e9400615800c0b40012502c50000644000f01030344c000300107900000501c1a007a41425545400c40e01c2841602e14030340d500e40300d960030fa81020349500b595950001d000c00c05034254925102c9000420f002600c40741c510a000510300101c010b28001213a00e600300803004014082e40b0024540c620a20715190304002e03001401501e800480d005100c0d0741c0c4220143d90880c2c2400203892042805039100502009036225030342a4050b4003c000410700803d20010110f80d842c4280d003032580319400b0841c4040d610400d0018000503041c0c0c030035031840348108141d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 294403354 1250 294402104 294402137
    0x13020f0412050c06030c130f030c050405130606060528050a1d0402030106050903010b010908030906090103060e0a1b05030402060901031e0501090e010b0303121b04030f0305040f06 79
    0x640d801c840350318144865a4405041840c185142206055440341c000020410400480c50241220b200340341c900b0035031640c4641c0d0b803c0143c0301d14000a0a1b4200035941040280780a8100e15404040c1c3c90402040ca440ba070b0b41c1406464030f03034104c0804150b0206124850107184003448085124100c40740138580810040980703988a11105d00d4101314070554550405141e0303c0d07003410541d001030011541c030760b90740c54020025003188040318440c0d401c21410403075a600c00e03000c103026902c112003d103141501e040e0070030085a101c030f400c25042c03545070400028005040c0340d1031445826002404030300f42040140000c2c841c2001401042401414014000540c65950a45040074003c1c240001d0011f04680030800e012301607812918040e05100001c50044895001120203a403408002d010703019040041580302e0280784c07102201e84a03d8400500e090003000511204c0d8181c4140c12854192261038005103192243c005802041c00050204905211a14040010540c6140005485001400707 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 294404604 1250 294403354 294403357
    0x20d031e12111206090414030d02090a0e041101081e091509070602030a120204050409030309170a050f030606160b012103170c09030d020c040b010504030213050a0b0402030106020c13020f 82
    0x1064018409900006d00300801c81d06402c40202d590003c0307a40740c400b0491144082c0d8000100640940500340000607a50f0030300b0202401f540c0e101c28100220032228004543d2500003d0004243c41d8410030460091680c2c81c60040c060f400d0b01c8043d000031982c02040004800d009014208254042442086240e501009444601070280b03041820b0b02c100b8103101000e0f00840d0810740d402450190b03039034101901940440031132845030403400c061542101041d0454002d0030005404120208a91307040021110011a400700004000e00e043c048002c5500b40c1803408000200c40400c0b44130014085048c1c1e000310710a03510f40c0c0b00040095039140d654020300e8001d8841070300f4280910038010541d803003a140c0031b603014010f01030111000e05105450080d0b49081c1120300f640214605029840d00354406c0045a050740e0f0040c01045420301080318040042ca401400c2040b01a40c41c2a8104c00d55680c3c0010340c020070302d40c1e005040d0444950b040000320034817211845d4903141f0401c142170f204e0b40c0c00320 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 294405854 1250 294404604 294404611
    0x17060c0a0c02031e060702100b0a06030e01061e030b090106120b040204060305030a020d030e01152702191710120213050109050121050604020d031e121112 68
    0x1d048034200e02103202082c03a165540d10480d41d005010007414101040018031103100300000d40c220f42001008560f05411901107071415030708201922810b00115019070000000d44d40c03100e00011388a1b40e81c1180c4111684c43d041141d03254420400104103100d0349108031600f0001d940000c006440c0741101c0704800030907402c0002e011800000c001019551341e98041c00041d5041410b030780c0d58444040c0e0080d1610725845442d00480e123840750041010703905100316090640c058901c800a681030040d82000f180030280d0344070805050110740c1c1c403800300340c0c00038000d0b4000b18400c3c0f01e0840034101026003508281f48092103000d00980c200a02818603060560455031048a004442540b500111f000031181481040c02c55042c9000010400d089610403070407a002e00d8900700b07000343d0310303002070400e5020108054020f5000e039010401601e0a00001d0150f04d2283c240b412054100303d10410301c240b40300c0d10000200d00c01c3c6002d02c501002074055299014215115a0b240c51000d005101c40890041d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 294407104 1250 294405854 294405857
    0xc040302010e04021207020606030f0109050606061c020f070b060d11060a050c0a0f11060307090b0a0903021806010e1203190c1a1006080403082404021317060c0a 71
    0x3202d00c0e107944541e4110390401e40750061510311482c0071075010359a6001698040d0091240890f211085a41031080c082c00750b5000000d0405034985500700500c58008021803903000c50300f0151041c0501d041d04c010414148058030040c0c8400701820012880f41d001031400d03000e03210109491340060780c2007154082ca1032045500301e80391000c081c1c0482d2a0b001e000d031710700b002d803103208050811f2101035416401c0c0300d4441c034000c0b001c1d41700302028002180410740d40200460b80a0318184030b076a00c90b0340a4040310160b4500341121a60f80e40018401c025411940044400320b4018010f01e568081c0c41c0303107100c0b0010b43d128152455551416540da105490114940600c50365002d44da50b842192128851604002c011b09000c010a10540800c4d40980355100b051000042c00a401030041a800e80b10b039070551600103080e035a01c4803854070141160000420050160400d00107a5200d101410703a4a03114807401740781e54202103030900c1078101e0b580300c84016801807081045e03118000c0700701e520240e8207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 294408354 1250 294407104 294407117
    0x5030114130f020f070209010b09220b1003050a0c03230402060d050103051506030a0f060b0d2027010302011202130311090a1a060a020f030d060f0e0c04030201 70
    0xc01d4840c1005103401d0b00d1840d140c1d800054003500203403525002d401c040340221080281079030703198941481032081150f41d41d044483c140d40d4040142040c18045082401c1540100d8020202c40c0040e0001c80c14106900c00f09035a0b0f070601105407124450a072070050700d41004c22070040451501043d400c00410308c0010f09820100003030454540c0015580340010038281171005585900e842511240005054142c0000c90800107040d803500151403481c0b1500441890000d0240703444242c081e00001e541d0310b8021102c0b403010000581e100907103014ad240c10200028a1600b00300402c03020905100c150620124494451139507580b00200f0715044a03030901b0140c8641c0006890079000e80108111001c0490316a40c000007440b400d100a151130f5101216205665520000040300311134251a400c88a0800704035945100d08100d002070001651a00440311100c458140c0c0d140303503a0045241d8500162030340000c22604018000d404003902c0201c403943c030b951406180301ea00a00139440085c0c1003105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 294409604 1250 294408354 294408379
    0xd030206130c0b040f060f1404050d0501090219050307061815110316150e0a11030c06030405010c02070b19030b06040e0406050402091602030412020109081905070605030114 76
    0x1031601c007070b00800d51011400d46460380d0320040b400e9070a03e03104460100b00d5002400881034410740c6d00050a00f40790204a0509061000748100c01c0d400d400300303d44941da01e00000025907100080e905201d030328400410746140c20801854241801a07001d0700c1880b8401c4401c900e04000c0c06010000d0300c041c1c010746610b080c03200000316070f0030b00d1600214a003408009418000504810140f0341d40d20300a00752170704941703440c48100e000c0b192410308040e4503800a1010310001004081d8525800100408551030034070b40d00001541a0300a890489241e03548001c80725005406100350b100800750035011070b0800502000e00150414501c44043c101551003000c0591555204243c4010b001c000d00148118030f0180781c458001e200c1500c007688240c44140000d601d00f042120f02900e010160b034003550030a480d0050030440180704103400c90522400d2400450f24640820007802505002c0001420891444c14034a0505030301b40c0010701000420801800f0010070340180030001302d010b4640b0b01440c0d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 294410854 1250 294409604 294409613
    0x821250903081b0c10020a0c0605030106020a031215080c03070b0901090311130615080604150e040212030c03030a110301152706020c030c0301020306010f050310080111180d03020613 80
    0x1c0300072144552010301c41d440520f00e42c1c0c6c0040d415060601c600c1101c54120f4403040255040e000c01d11507100181c1c440d20040e0002842903042d004440d00829000c212a915051400c1c9a5039458110b400300c0d0340100440381c00c0d8a002c205072030007031024072609482c12040c0c0300001c03d41d0b4143e02002e025540f0311000100c603030301d403114584a200d900020810000b921040b1400304007541c406035400041610010800d50718242c450001c808403480303800d9040901c0c00c2c600c0c1c0301541380280141d0f8040741103400000b1705942031004183c050210800b5566a10303001165004841d0901c0117080300d5070090006012204480f1000c0c8281c64217414009042c41a0b5000d4900450f142108015894015840003500c190001498201038004405580c1e1180082c01490700704e00088509500240d205040003003014002d070015a0004c00700780070520020b884411060944031051640844901c002410901d60a1502012000003104864202414500c1d0310004c0d5944405000400b541756200154810030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 294412104 1250 294410854 294410863
    0x11b05030c01090803090c2e02100213030302060a0204030b0c0306030c030d0f0207050d0c1a07170703030506030604030c0201121d0d091703070821250903081b 70
    0x350710080081c0724424142c0307803100c52070700306840c88441c610403030760f040580d854004046e0160803480024007402d07010f0440100b5a00448850700c109500800703620320f21007032690005001e4540c000120248031441c0d450000e107080c900401d070b4244140b042c8401c0c80010454006241c003d1031101d4225203a454202c0040d04040711900d04a9041c420680c44414030342e0401c441c0d03040c0c0c1305907400b51802140d440040c02101d803200c15000700005042c45050140e40c58aa486194440c000d00665050040c2959143c56a1911000302e41400102042c4402015403600031b880e0311800542c0a802c15040c00c4e90b0260041c0342c040390081c14410900380d0301c1c002c906250b0011a00c1001c5400b4100d002e1110080c40fa208e50415200d0000999081400720741546003e11444d220a01e0400035464481992244220703500617215407900020b502e00170b00c0030000d061103098003071040c01103407144460030340701aa4003800002d410b80e418401005400c2000c03d88940549001c0450241003c444aa0300900329040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 294413354 1250 294412104 294412117
    0x40504020c150108010b09010312051309051617400b060a030215071a0a020a09050301050712200417010e0c0f0d03030e1e011505011b0503 61
    0x858804508041c0500d4001140c580000202c903402546980f10303440e6509171400b0040b100e410040000041001070303448103400d00400c5031031401609080e0b09113056070b03600159610000f1380c2c0e51260140701034a03001c031190070071040280c1410603550b10400d42210b11000020440100c00d150480010108180d44901711900070400c510416480748018014a030b12099020544000100b800060001e00b8205040c50030740303800800030114440040c0d0703071400640c050401110001c0b42c8039000010f08600c080614000c00c1000405601d400b8066801014001c05900c80c6110380e0500d030601c4545500190b01403488801c1e180d021605800d12010009189025103c40da040710700001c0028401c4011620582c0001190000303100e803802c5003000c00ea5544011004a0f40300c8609102183e0918010341244d07035143c801d080100750810b4804003281001c503030242c644052091841d80e00c103421400e204e0302e80c0106641e6000900c10b418800002c12010004071459070b140a10210b490a01c10100f041d01d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 294414604 1250 294413354 294413359
    0xa0606080d09060f0c06060f08060a0504020f060c030f03040b04110a060801060e040905031918080c130e01050c130618030204020915030c0414040209150d0e070e0106020601080304061704080405 85
    0x9080d40e623484042c0b01c1c40a40c81810014011000491100e001c1806aa0300458000741100c0300f00070000f08100d4203900c0040402c0301b03488104a0890800d0a41c405144103c0c091601c40001c4d141504003661000840c002007449400c51210a002454124003c1c5040d03c009180101903c1d01da000030400404841a01030302d04e12011940032003450408a803030413020015610042c1200713400d1120784050056014001071a080183d2450460401c2c1030103500d80b0b04800804112404540c1c007150031a18252801080300000084500700c442038202c040300205150b11301500110701c0b00702501c0a014031400f0003440755400140c0d20500f03591320040008007407a00408a5628207180500000700d070700c10b104015428505802094131807800e4030070f460103120040c10306060144d1b144204440c1c0d1340070306c0c44044055a51f003252030f05000708001120142c02500701c60700043d414880003070700d40030b030583c4510255841000148402031340301d200e40b41c85c4420210f10091584803803412151034040e40d0440c94 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 294415854 1250 294414604 294414611
    0x315150e031e160602030403080f0f03070e01030c02070806040b04170a080a0f02070f0f0c081b0301060f1214070e070e01030b04060605090609061207020a0606080d09060f0c06 77
    0x1c8801000c00821500e090b525000c03203c0b000149500c0c01801d1506100b42030240e0824001000405c003d040240f8000d60340c889040c0c502010180c014040d50001d40388440003c1c06c0742584a007552705445403014128441c0000d00c41c030351505003541d585150007000148a414420040717000c11207050450302c0c9540010245688600c0c1d80540142007100840f1071041160500156800d08c0040340308483c103054001c4074054030f0003481d4450a41c4070301860300071158840b00b11000280c3c00f80034482d92400c14088a54001816808400c15023940c11980102181c0e02040304100080801880c1c040e103580d9000d00c4501c41c100200d56400e00305119540b000c0b500c160302404115030543e1240d1196a884003d0300c040191054903024001180c1090041d000841e004100f04052881c040300600600b070030041407545020070340100f81c0036814080d9000c002690007913800c03804001541c000d0402801e8054004c4c030b001c100e08071005080c120f0522039801442030a2641e010307228410b0500f861010307001901030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 294417104 1250 294415854 294415873
    0x1209060207030c17211902030907050a08010605030c0d0303020c060c0705010f050903090114070609080324030c09060f0306010305030408010b040b06040b091c210315150e03 76
    0x40c0020441000407540442d4496500200d020040103640032401c842c0121140c1041555045d15028406070040c0a034042604050360202e000e4001144101d0010024250b03103881c040c188081c5160700d410010305641841401d201984000440303003102d00c0300725040c003002e034600d040541c000d00c11400356038668051001041140a03030313a0001d14605100c1c10080103404050400002151020340b10208660020050700d1040e40c45605007900301240c05000c5482c00119541ea034044411440c2c1c22641d0304004010000030b900d52845868502c24054035841e110024480020f40354014654910b12403c03440700401c0c2c9607294000303140c0012030003908507020340d6140d042c92075498005208040041d800c0071200724050400e4054243c85800141805040a0401d590707140150460a0b82c540c03c641003007a034540740603c03915482c1045025581c03900c04221459000ca010340f0101403060700741410a804507204e0011340c541501240c0c0c04103410451410311180c2151281d80070100346038035100740b1005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 294418354 1250 294417104 294417107
    0x2160b010807060806010203070c051525050705030a1e061107060516170a020304031e030605040f05060f10020f151806010302060712090b0406080601180f06120906020703 75
    0x2d4200b070352229110a0140d43d1070400480c1da902c100600207010031031510041041341007000319405d400400c03041150030500c0980d08000b420200003042d0b10900c0e500110700e03040c400e0910240c000381409030003411034032545880310310300101c092405600b904004000c0c801400003a42c4801500d07401031131080d40d00c0700f540c02e0040141006850500e4001cac0c8030b01d502e40000d802001c2c84a203001c5901c2240e46542da0300c0c00404000e400040082d0305103c11031140c02e1001c02e0100607201c19904c10745001a01c2810b1030107100c12204440c060300101c81c501010f210203903071380b280c4036040394104850302044e090304504220306040b03c0074140a80c4c1d12034603c1c0340d1150303081c86040a100fa00000c01c500203400102c3e150f02c1d55524288070181d0005c000b007007191701140359203030250801c40141c01d020703078850ba840000750259070140d0f10803000501c1c80c80c140002503a200403000858084503500070012810805e54582c0050740b445000c05205130406110312214464011007030b5150010801c640344d40e0103040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 294419604 1250 294418354 294418363
    0x1d0c04030212010b0f03010c1d13060b070b0f1015031401170f0c0d03080403020c03150a200a0f03090c0306052d16050702040606020714150a0302160b0108 68
    0x890a01c0b44190f444c0c800f45e5414141b181504003107050751288000b00420f00c611008455800c03105030441302d42c00540d407001081c0c0c010040181304d80d404066580c4114100040d00e006c5c00341401061021903814043c14070340800690041d10300b0604240d403c600e00c00c8094004044610041110f11140e500001d480aa40b80705200900f000d0810780310481c2d240810580c80d91401304a4a5102040c0f10701c0c980842e00c5544940d501a10900494012581380d20000b45460070001c90501c03001450010048115014020680581560060600004036000c0851654020301c2e14400c20045202e4241020034400d4004005150304281d0300c0840b01d4032401d0076400384c041207481052003240041c840b41020102103607446c009000d50003041c0c2603120801c001c251002e0a180e00002c0190601c00040560764a1207000014056500100009032600341d42d007112440b110000d0b80b05132480449a0780d00e514400448a020b40d8503e00140d40380310034800d280c1144030002000d4001c00c0d40b0400852103000005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 294420854 1250 294419604 294419621
    0xa0c1211010e010209060301090908040b1606060509090a022b0c17070614090f090a0518030a051b01090f030e0102070909020627030a03020a0c060305011d0c0403021201 74
    0xb84501100c00c1c000b1420303403107800704c202e4100d602000100700085483d800b0440903485088031074a495545d10340c0801580104107548156000e0f481c4900420201e40b0481e0001d1109440c5600940b511031000d9403581014030002e4001c841d43e40940110b00000c0c201c0e403101d00c02351600922650050f0030210b841e0449030188010114040544060801000410b070080720040d9440d002c001d000e40c4402c1c4100d4000c20151170300103d400ca0410f40c60f5403000e440a105e07600c4e594001419190030405400e40c1500304c510720185803c2088071920a40c2d11a046490036900100c1841c1c1000e826440c0310300410500340090401d280c80009182010ba1010f01041e504509030300301c070310741da869800c0305003100c21512000b907002c5410416030407030f140440e501c880d00340e05680c40e1150304215130340400d040c410114000c600580004e841c404c03c0103407886542019010b11700d001c000a40c181482c003ea40007848100e0004410404001080e080703070396080b10059a0f0103804107816040008105000e8101c28 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 294422104 1250 294420854 294420887
    0x1b080301090e0705060418060b0d0f0609021c05220302060f01050a0609140d06022d3108010207150f0c27030b0c03040506070509150a0c12 61
    0xc01c040d58038030005001d8051300c000408031440c0c60b02d00110f400c2148021500d010f0001d0701c1e0440004c50300011005801001c42c003034400b040c80c0d880300000c0000c903500c5400040c000c0e4818005592001c00f6400e0313281c50a19070b607030f0002d03ca403600f000340c540c50420051800f80742c044a2003640201035008c02c40900a02401c0360904041c0d0b201c030200103031041d2074043c201c0000c062030010400c4d083ea2031401c050b4a00094000030301c8030004d848004c241d900a601c604108110714111074248003554241c0c3c0c131020745550580e420b0070340c0c10490410440c103035110701001084000b441c0e001d0340118051000280018802103507078450518004140c04000c3e9080351301c1c1445c00b03068108060041c004c00c00b240c1020790300ca28000200400d4440a1011020006400e0349000c10104c005002d481304203000c2c0c28400e0355503840e807800b480c1c050310b090002080c0e0b108100e001d00212080d5221541e0f200c5a004c41c05403425100e0301109801c40307840c01030f10000342c0b90000310300ba4a000b00381c100e0502103101c042c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 294423354 1250 294422104 294422111
    0xf02120708010e0408180a06031a030615040207020102031c1401050319141609060306051305060c070f0b040c03051903050418091a0f1003050d0f1b08030109 69
    0x6100040d50018401d1088100c100701e01c00001300010031070002000d0f601210342c0c841444481010200700300490942003000881c2c2c0d00c0c400003403624540300401d107000d0821002801c01e4608690854507049043c0440c5004513000304880c1c086a00034400e44d24180b01e250f100c4420b0030798513a03012020381421050301c1c0d10b03880a0030000c241c2d810301141452411902c11480520043c1a0343e65125000000c03035114658000c4004440901d42c001c0540300040200b0500421042d003141003543c1151409080c19a0040c100c42c070f0000043c6020800c0b55002003000c00a5031a40000e00f000027100c5517566001307003150b060200b00403c124019843c1c8050328010002c96200800e0307100c070941c103c0e01c40d1034043c01044090004002d081c1000c40d000c02c1140b91003001144d0344130a99111014035035541d0b0b980803c41458000c01410500e030314031080d44080c2084151200c107180d601ca00341c5900621131040c007044250350307603c101180110484804090443c401c03250030f46080c00c041425420a0107800c0700e9905 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 294424460 1106 294423354 294423361
    0xa0f03060509120705071208070605010308070308060103111b0c04090b1603060308090d02010e03030d0e1504020108280f09020112060f05041805010f0212 68
    0x114100200341c50508410341e07810081052481c411a071814041c6101240c0c0010303582013103403414000c49211031b03070031700b4101c1c124031131403030301410301c508240c00082000825001041c00600a6aa451091312040011010384240304856070441809100e01d054550010390481d4500c28410100c03805040c040d004038007540c2c4558025a1218448002c00802010008031030951a410b440d0400c103440c2903035140e11050007a410040d005004a1001d601164080c4d41800c2d901e0b04000c048907108d40040741e16001400c0c0ca80d040b140c2c00d0107200302d822007402d60000c1181c01107174140c40f01e0308556031750100009100031203156007c10300c0c0f1392581304502d844980301e4610815075401021aa04051380000760220142d190303600402440c10713404101446e41032120340309844040b01d020030520020411404c06090051028015520304203c0080300c000d1940206442900001c0700c260b05d54 = true := by decide +kernel

theorem cover : BRFrame.Cov 294244604 294424460 := by
  have h0 := BRFrame.cov_init 294244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 294244604 ≤ n) (h2 : n < 294424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
