-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4138
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:40:50.446796+00:00
-- url     : https://prove2.me/submissions/fa09b9ee-75bf-41d3-b1c5-4ae71db930eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 744064748 ≤ n < 744244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 744065998 1250 744064748 744064771
    0x9011208180f100206190905030d0c0e1002100e01020a0215130b1015020d090506090d050715030605030d090e0403020304082b080c03162007240c0b 65
    0x6507a42d00103030031040884203140240c0c0021082000c84084500380e0000050785807420003088800f82c60701a505d010340d41c0d103103528503642c0b0206a040c60250311302015601004100c00902035032408025100e14050404c000094100f481720044a03c0c10300a407415a88a58020b00c42d41c05803150380000340001900c030740c41c454016a034220205948030f844600c03a030781d100d010b9203415150051910141d80406602811500724102108051f940480c400d0100d03202110b005464500c108001034505950038401041c0d0320031000002241100d1048910400407640c600b00000c6036a03c082c0f5885140a81030301e000070746240411b000304d0354455000d41d0800d0207403049a041c0754403000c030540361010310b011001a000f5804014900b690b4192001c01c3c50f428186030001c15800c00741f5482c006030201600d460403e204030b440908260384a20030314034008844a458280b11442c441d0469121061405194042c0e0405403521440d0f203643c83d2154a125040e90707031814a09240e44410202c040054054295076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 744067248 1250 744065998 744066019
    0x71b05010905010c111b060d1503060c140c06070f1223010918020f060705030f180d050303061c0203030a080a0e16120203070e0103110901120818 64
    0x18001d22505408074441e4000140107042044003405400400c00b03002c20992014072109542d0100d0790400c181074200b0340d461601d4032030300091036024088c0740b8240c1040301c9040b000002807040b1078206c110b246000b92107210b0340c00b104c0e410003505e9103d0140d10314020341c0402c1c04142041d201c0c0300c0403918210949007110601201c42d04000c00c0c0e0b400000c100241505150700d050400e05220040783c0149030000c0100092400d4401080d407985914002038170034103801000e1440358403810112040790340e108080c2c07651055400003401d8582c000222596141011036590765550525244400c113040c2c10500039070840e500c2104005860009424801e0410818400000181c50420241c2641c1e1515140c00c99039242c0f5a20310740c204ca0206403062100d0707000040400310065010f0210342903518404242e801c201c1c0f83d0000c41d241100c103034042480c844901c4000002d1103819032601c80000300440300043d550740c1e500c2d081d1001c200080c5010b0b1045408100c0b0507070003040700c0040e6610480240031280d80c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 744068498 1250 744067248 744067253
    0xb03060f0c0c030f0d0b0609031f39020307150519020301170607030b060a05070c0b0705031306090f0e191e050603060403050703050c0c040f1b080c03071b 68
    0x1180c0110a07031404c076036404113801c58904001d01070342c8910b07007090312414144840c000000ea0b5070345222002c04520039428046454026054000624035158000c0320403007460226441003400101480c07521015107800d220409541c4080120784030345030881c44104600c00403180e40c1c070041c4805002020713030078034044103000d18030003c0c0007550082084019400d218040c09010500700500103048604043c0b4108012603241d40342c0d0141d8000f07205030b1400d6074491403d4604040c0c280a65040100014008070380c80003000400801407095080031111010210f90b116015217180c07515000f001c0441141640070320460403d0340b8969407000c0900914401d66842104c0f0200700c401302d0107030451910301c442c2000d103d5112401920380106094009181c0c61400f503d005140e4000d05100408100000485e0400c09008002c1402201001001017221800c41e0352081c00804140c5c0002250801d0885801c0c0038a019100f0345100f031203010002803550b40d950404a4051040e46156048444a840c01101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 744069748 1250 744068498 744068503
    0x70c0506180a090f0e060601120b13050f16050307021926031605090f040c2607080105040504020d03120908220803250c03020d05010b0a05040b03060f0c0c 68
    0x800c034664001840c1344039000003606071541d1303452800d80d41d4014030512945991080541080c45400480003404002c0c140000e51294203804405810078140340c103211868102c2c41019024100055038000740d50914103064815000445050380941c000d4603070b01381d2014210640114551143e81e0240c0120800010109081218940260f00000210400103940c01c440f121211407415070908504104010000411001090030094041c50704d4540b4140c060b401408010380ea00005544450714095118a244050504803040000500d50400002761800c0a01c240390090703401514651542200380c0301903442c5501000ca01400c203aa5030440e00100f61a8006050311880c2c10960004840b4404a00802c0102c0c0d500f2400e02908100482000400800f0200c041c0707210303001195501104a040c040410704040d0f01c007035000319010409204002044d8071070701e00c030f2000b201e05125a1380c507123007400100e4100d004000c4d0194880740100e821040060785944d84000005071491525024100450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 744070998 1250 744069748 744069769
    0x501120e030a030c02100e19240b0118120b041b0b090a0504020f120a18031e0801180e0703080a0c110105130b1b071d01080102070c050618 61
    0x24002651001500c0e03107642d050044903040c06c0712503018040054226030098460054540d40b105840035204940200071140c00180034100c2d2440c081000417000346141c2c0d02402c0020206400038481d40584442003034100c45150a958080704c1e0008103902ca941c46104410010340700303840c030380c0ea144144c501001074001000040c04c0356824540e1200c086000303101740110300d03030400e07841640148000701000010f2411b039413400c00c4014580d20790b0b4480540c10303401001c03003000b0b050051a21688030300a050300420300d2a141c0e003c20201c0c402074400000201c451500c00e00424000101440700f00105100c5500324a0105020100342c90140b81c0d295a04c03030039640710b01c0e010000b040c0b00140302810303c941001c8800001a080c204145002c980c040c40040103002c9010741c103603090003c202ea01d040951401d181d0741d044104403c4444940e12840400c4250003003101c030103050542d20b800400e03605418025200500c1e8403202c50b040807424001008859000f8180e0008104a2220f2018095444244a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 744072248 1250 744070998 744071017
    0x30804210219050406080106081207030509100519030506060d09050c101e11070b0c010906061412031801080c120a051506070203060403080c0c030409050901050f0403090501120e03 79
    0x7910110f00d414280400e40302035a000c2d04859241c10020420f0350408a03411b1401d000c013a03025036072445145001d41c0d0398000c00710303041e8000c2d4190204800c000d8100c0000c00030024009029104111440380441c00d40e502100c010f50856414080300c1d0703460507150400d504c0ba603ca01c05031200fa820301d801184140b483d40c0900c0d0700240c40d540e84c000501610030b1140410301c02078075041e5040a24400070558a08c1a40b0810124080014101104981c203501c0003190940c0000107014441e9505035020391360b00d101c3c900c80c1c46a45c0707510204480d00c6000040325841d0944101d038000b80444d020056031401c000500b2664442c1e010003c48014400280c8418801d24800e1400165410300c44030745050701c0307180c50800780280000c0241c0d00151350300280203a40a6814a049004ca0740c41c450a00120301603030050080038800803401140d00d0040b0f811107803282c0c2504000b00020b41c2d0f12010071180e0031007600c1c00b50101e441003205000c9944204007021b140390380082c0c04142000d10517a068038660182c0c110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 744073498 1250 744072248 744072289
    0x40612050d0305070f02060f04170d0b090108010204030309152328081f091103040203150118050912041202010f03022b09080a05030a150308042102 65
    0x186007800d0780620a081d045040c1d850043e010380400c0c071001e55a510082c0101090500c2d03000007408012480d45e4000a0942caa09000d480b03410700c0703c1c90b001905030300b0f0b08203205080107400031840b408144203540c100da030103503100400035280c820f10b1035404054200c074100300148145ca509142d03806489468514181e0342c42142d44450b009503100c101c800c2d614541451840d01c00c601c008281d840003456810420f000d030002005040c020b00039514208a50103402198208107d80400441d0740026501c254000c1d01030301c441c1103140421400d0810709003d25205160300541d0340b1600c5590307500c100d51140d90401114888084485894401c3c0c001d0b5024040b864144884403007103507030100c01c401071030344541829400c06207141c0d103640d001a205211030300d8401402194060702d000a8000f4540d43e500a5220b44c6d84030084000106903a00803a41444103900b0409040d03007940d1843c1c009811aa004070800d4240ba00742062a90002c00b8030802d9120b1034031241d001c101680c0d4201030a0840c0102110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 744074748 1250 744073498 744073513
    0xa0302040e0c280b0f0d0c09082a040203040f12020a06090605091005070e0f0303090d1101180602030f1b0709050718150e0a0803040602030409060e04150b04061205 72
    0x201628043c02c640c100c0318120311306000548a4038001816a100c03080301645c00304010300e82c10030480740100c050744001100d20404d400c2c840380b8100f031201c44020601d071641c1c5811210102051206074402aa40201014545080c0e400860b4004100302d49218036231040e24039002054a60070140c8800d04402c1c0d800e1507844042c00b44426040013140c030100603c1340207000603d00341d0710180c00034900e06546809480b112441c4806694107008a540e0f00400504603101500070342443c05402400c0e00f08a404921440400040400c002003508100d480039801149031650f1010303034180c05d41010680701c00d03010340904120844e02e401d0007518040c090b40c600009252906500040185003a002504960014840280f00701c00f00340c0d401070884502d42c102045516003940200308000c440e54040710b5203010100e404240580d0110041080300c1d0341503818060760f40c41d684031a82c0c01c0d00030f41d40145070380c0790140d400c0c41114064115000300400244005003a5940c0d401c034103202d0800c910100d500390032429 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 744075998 1250 744074748 744074809
    0x5030d021306080f1306050601051204080d050106021501031e0f03030f0b12070b0a020f0d08061503070512060f0411070b18030403032a0506240a0302040e0c 69
    0xc007001c0e40402c2c00000a103445c01d00700181e000c2e03140c2401020b0000c54507000020100e03401181168040a02052800740614141c104086250070000a2001ca641050300003d01e642c03000901e0b420000010300102c106904c0c0d03a48040480307284004003210710b10209401c00120310f040301c074909007601a890104018190059000440314010350f11403094803000c04ae00c4940000086040030f030b86082c040306079a401c1d140c00591600b04241c3c50004030740300e030b1240294826805000325000d58016503000a54420050311070585010846092000540500c00c540c6d00c017004840454100c0c02c09807038001c0c084480d03400303c2c042d03681706900380d20020740c0061040e0400440b003803880e5011503019209101c101258604507107900c0b8620003c1c0030440f49004072085007904010801c0301d4406103e800408114a1030020b840e40c1044419003142440a01080a41a550200070340c0b00c20000380030302d100c1411542000000c0c034000082003014070642201d194a9103800c0511003010800125144141c803a05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 744077248 1250 744075998 744076007
    0x1e06150a0b040506032716081b0906120607020f0708120702190906060306030618050d1202070c06020303100605070201080f090102090a1421060103030c05030d021306 73
    0x12206009000140041041404840944090302d204030303112551781d2103240c1e003850b841a1a00c11112540b018109200b031600d40054070241035400000c8038101b15503985415500c80c80f0502c505051281c65084056062600b00e40c03a03540310400611000382c1036180792031a45000000c5900c900581c2c000e4211641c02d0204200310b600404222004001001654020300403a0048906c003c1c0182c510440b030014501c02030003894050030301d107401004815500c00009015160500c0282d41c0c0c24541243c0d103074034105d55208038680d80d4103c0010800b5140c00981214911040e858002401d0b90a001200010300d001e0701d408000c0c4070a50046840342020310313014040e081c00b0f51141e01884002c21070030005036004408a41d00040f15040c1c03003078035510742510601a1045480d141ea014003400804200780691280900002506441080c0540d00c1000d280b1095400c00c20b005400da40402d00400000348a2951024621700c41c2040c0c9080c8601e50a0b070300140c2e00f000e0152050101980c40c01c4c00200d510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 744078498 1250 744077248 744077281
    0x1050a0b0d14040b07031113090b060d0f150909120e040f180b0c041a09010e1201061a040305030d02210405060106021b010509010f050f07060603051501080d0302030601021e06 77
    0x140e601e1440c3c49800c41c2300d6100c040c1244507502000340c5460740f2070404d0391500181e66074030180c980280103658040328003000806c040c5a0541028083d0340020595150324803810400d60f0b404030303240550b240d0240003a41d0907460a03814592043d15460601c0c444080381c064460098185181442a603d40749015421400010048408800180010065114907070341c404407500700902c0c0d06a0303400c10140121440800300e44800e070032841c00000c01003182c0c0154003440407500204600126080c0c417409500281c8500d02c8068003aa2041c0640012900d8550042042132031400c00c4c0c000368180c1c400c000011000c01c80d005d80d0316410600042000035014803000c045804548035104a82d0b4208001070030601600090078100020903000055240c001d004a804040c15016201c0d00c2e03400381c9c036102014003100d00084401d8001c440629a005107045c0400c2d0594403010b003c1d15508442d84c0b130403402504024030b4181148079200f5104044080842181c002c0346508015214910b00002c03400c098810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 744079748 1250 744078498 744078521
    0x209060904050307110d0c180b0301022704021b0a03080a0204051804060906020412061b050f0f0f0703120b0f010e04020c0709021801080c0301050a0b0d14040b0703 72
    0x39a80d08100c0000d00100072035520981c021403803c0d0540c40600425001031640b00004c089455454010038003201d25403484a030b190540906200e003241907400d05080c2d0040b0300c05420413248030a06504911500300800310140c0000c0c00050a1040c9511a88003540da90f10350300705250042c0d1a444103050340034180030303400001c2c0c0d0000d614161610020071700d040004055a6440614607020bd4100300c40b40c3c00c500f041c01e0b00100300b55102e90315200e00d001842e002d45800c5031541d20b4252040391181426040c03500d4400d4a445160502c401d410916191350b00c950406012014100120000f40c7c1c61240a000120302079038030030704007c1820404c0c00c200c078001400311707101e04c0088426071810f0703031b1045240080900603a8090b807150b1b10701c50081c0c42e10f021038002c50b51450000c10351030980340c0c2801c0600b42040c006da82e402c1d0306885d07000c0e00c1c0f45103200030f0051940040840c3d0044c8441c4a4220003459800e9882800040d2400c08609030140c0e6003044c0e0f011a1031143e03000c20320074160740c540541c420704803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 744080998 1250 744079748 744079759
    0x6030903081b030601050904090b24120c010309020a1701020912010e0d111e030307080f0108210c0d0e040b0f0f040c0c020316030b0106080402030a1401060b04080a020906 75
    0x41d0303034a030040b1600005120a0400800149425160300d0b2600805c0c26203501c24044078141c10702c00b10883e41400342c0f81c00c0702003880da282c4070100d50b0301d40002ca803031403e9180005032500c2c0c12035a00440151035090740c00d0b81c01020300c40000550340c203025468041040080001a01da032500740400a0003200c80c174124007560304000f6030944055002c901070381e450800d0b00300291454a5124400e08012514100b50000d02e05258000d950f0300020004600c2145a652014621741c0e80b10210400001e0a0203010a694051408604070000a038144084603403a511014200b4460300358007031030b24084286080001e200c0c0a10818241094010340b00b50450481701071040110010206101c45c1d41c5030700552290b0380703c40125010038040c1d1080c0d4140ea402805035062101032503210a190070349440111001c1d90742c50000107000b403051034054002d0b03038020094200c000c00c0b519201d5000c119140c0d004225540c8103000110ba00c0b0080090005000325030241550728a54010410724640003041107000382c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 744082248 1250 744080998 744081031
    0x51303053c0a090b07110d0311070332061614030a020c010e0c010e0411040b1207020705182701051003030212031005060f070204050f01140a08340603090308 69
    0x5001b9103a03001c45204281d03038504d46208076007811200403120344141d840c07a001c0c0c074801009208280001401c00000340752101201f80244904005480c1c88000426154001c80b000c00c000c5150358a51a03226940c0f8640300102003020042800c0315407080d65403480d00c03503001031031064030706080c000c410030422400040c0103905a0040040c140c00350f0000e0b418811070351001c1040c02811600c056802812080142584681c000200c0c00b41d8480141e070648094469002c0009141c07400c08407480411101c038070300e8841a25030400340c001406000050721000c00d0f0344014044040424070902d8814603108a41e00d5142c0d02c0d42c07c010782408050381c1c1e00440140700300100071245d0211881034046800958520707640d0440002180d0240c05000e1000750b1050808080c00102c00c00080414180d0b2800f4895000c50028031040106003101403190100542011a04400c040b64010110b08103100881e0307600103422440c01d0b40810302c4081d400190100fa40e07a00000705140d400050b0b1a403040b036120030034268 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 744083498 1250 744082248 744082253
    0x60c050f0708101107082a0a020f010e0409061b0f05040e01060f050408060f06100201051314010b1507030311030112170421020103051303053c0a090b07 67
    0x1144006081d80e4405511503441c003d080c944c0c030742110500c0d0742102c1500e444c0d0f0b102c540034910000c600c008084185000140040c0f1a034000300e4440702541d03006180000b000101d03401502c0240680000d264482c1d0350b13104130400300e01c49026007031507800040900c09581e01a502c0c00350540040400c0101002018001804403e40344d141081c1542d04600345143d4000082d41c1c21200307031040b5002442c0358010182448035442c5c00e002a84c0c080c207001c8032100b01168000604a0881d4001c8076000c518000004c0c0e418080b43c0b032080060702e000e400030004204904803001080c41c55001d4804d0000c1c0280000c0c114040c15407500c901040344001000340b070300e55403410070280c0d0003c20b100f002400004840a10501d0081120701320b078010311901528428105200300b070030070040d00004061f0302290801c0c0025104030044851450b0642d4952901d604003000c9122103003541c5100d1510000c02c80022141e503007005042031100061a0103500344503942c00c00c0f182d00806034081a4040154210140101d200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 744084748 1250 744083498 744083503
    0x21c111017060609032503051e0c041a0618100c080409050a061a0903070803092b020325060207032406090e030403020f060708030c0d020c07060c050f0708 68
    0x4002c4030840d030090321494031800080c10070107042029003181c20104c81c4503a2140102c3d400b2000c807405201640e0780503880d1500e0307009203600e104000314a82c002d00990044d624080c0d103d0101400c00401d0b984020f00b0420204100390311155030400c49914140c0f05840924004c40c1da61894110f918101c0841c40c100e640380741250140e406441c02a0385c407800044c2c007026141d8086801002c0002d5030002445034150403080c1c950086050501a018100011403544c000000b2a00000000383c21000003408840c24a5a0301481c403440740200300c3c1c000b22a03000f5030703420800d501c000741704029440007500320078282c0882c03660584d10010540d001101b040010030104607502a0894984000020100d0b9115100005200d980c01c05d903413087c43c001000d07902400c00070152040d03901c20344035900708410b510100086405208001000180e0801c0015588002e120140905015103000035007800d141d2030783d1500300107070380d000b12001405052103102846810400f4071003102012024044039424269040e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 744085998 1250 744084748 744084751
    0xd1706030102191d04060b030403110106060e1e04090605250c020907180f06020709050114061303080d0f060603140f06010509030f010b010f0512070309021c111017 72
    0x428001090604c40c0c406150040020f03039004010800c010181d07c5030751855042e041030302c00703800050055118004081c014032a04080e15599180e0a91280c0b8000400101e405c00c2104241e4050034103610901c10384035070040680300391141001003485e190020000c400c2580c92414034601c08118841c091829801c841824401e03074040d41c040d80a9540d250094940d1542c50300e005000c1c8903415000a000580e00c401c039029190386909550000c0c0d5182440e0043d204280150f5412003040e000f01c25a03860400001c200c902100c82d0004112a900c0d200c43c80141c10041d001114191112140503c900f804d02c40e103405008141000c000020030043e0b00e00302001d00a02c154041d141c1017010481c641c0c0241c003035030b091420040407500881c0c0e4402070240600044071120340400c0c0702511104005020b103007a00c0c001c8041c18002c0d80942d5507084110040c1000c10030503a00585000720808203490641500340c82c0c180610411640b9500786014029000342110302c140400095000008052003140c2405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 744087248 1250 744085998 744086047
    0x6040b011404120c15020d09080f030306040f1512022409120106090f0e0c06120a15091a01020706050c0a080c1e07080d09270e0d1706030102 62
    0x2d1501c8040b841c140341141c13205d13003001ca25120343d4240c130303003860341d00060481c41e40b90680d60305070a65644501455803031200611545160b001800003a606041c9644251440001d00d613000c200351002d44c602420781e2045400400f2021100a001000c0d800e00d00c0b0500040030f18580d0300c0003a2079410315a0780041c040c001e0007a01c1000058140c252010b425004030f8040d00340e640b420841c1c82c010251b04070045c100700040c188140200310180303805160810544103500d110f94211610396079000b401c14000c2429000c03440784d020800c1c901203020092031140814945001e040342c924002e0350000645086c1d01c0350301510401900b00960881c460020504802e25540200c0664031405510a00f5041c8110304880350818401e45080141c00b5800182c2102210f20703580669044100e96007003202c44d00d1142c013440d000001e5540141b040102c06500d01040f84599540008051070840b031850b0814200080200c000b80c1071840720a10170000704496900302404800841c6841c10314504bd100c10015a040c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 744088498 1250 744087248 744087269
    0x110606090402010c1727030c0325080601060503090c030105061c080f0d0b130b0108060f0607150b010908030c15071202030405011e0209010207050f0a03050f0606040b011404 76
    0x800c407440f81901c0d40714001e03003420381c3c4503540500203000c0c8140142d04011040305c031b10341e0703041941400710343c41001d508050b0260084003501001c24240b100c1c1c0c181e1402d040c003074140c4001007000003800382070b0207400c40b9078681d56030703041088204d8503145c00680054441d0f4034080a20040356a651070040103210820707220051a200390070040c0f42c80c0178401081400c00d000050b13a002c2500603a2190100300c0003221000000303100311500c1c4088901c010801c1d4007244200c00420240d15111090040c1c41d00c1c0148041d16010550b6a6089003407a401c850349045604c03001040d14035a001070500c40641502401907041c41d4440b26020b036142c500302201c2c1c80f010110404100400d2080702000c1061800c41000e56507802c0c03524001c0d00800103c0106c045c2004460a419480d040724000c4a1984405074020680f05050400304a41c803011106503c0d80a01d9640c0c0c000b0004406000f00d48061100c940500440e260640a20040d00c03003d10500d410444590102c42c0000395160a07142a036114000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 744089748 1250 744088498 744088517
    0x50f0115090b180306090a1e06240905090c0a0b0c0705060f0c1905060a050702100f140604060605120603100908130f0f0b070503040e0903040611060609040201 70
    0x10940c0c0041081d08250541c00000400403c28030031240c0003124070382c050b0b01300c42903603885901c11350316808401c10080c02d110514418180c480ca45010891502d401120f00085800d1400130600d15405030355107401448406c007004000c40c90440c03003a154401c0c103180c081c110054800c000101303140380c103014604644e81d0120f881d800d0701208004075006060054452035540c038900701010650342280d4000744503413003900030008003e01a1948110303c0c0d64440000c0c80651985000038001e09801842902144a0703001807981444640c0507080340302c401300200241202c0e4584600511040c000c1580e40941c0c103016081203c141d201c02298a06052820050590380b90341e00003d0610b41004503880c40c4c28284541c81d030a1061a000030301c4820760100a21844d965295482c000002c158443d40026168011040103a004040c0040006078030940560f450b250319200c003a2040032007560f642c200c42e0b002203130901c81c940d0808d030495035854000008050518200e00042c1c01d100c00204001d040102640 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 744090998 1250 744089748 744089789
    0x3080a0c0806130203101e080f0d05040501033309060e13030c0c03080f1801091a0d020d0f061503090c0510020307060f021306080f011419030302011d01050f01 70
    0x4081b1001d0a401c009003442005001c400120f1010180101c5025000d9074142440003200001c0c441420340d070b651295410113183c04019001050080d240d20385410070302a000e00380400c5859400603003000300c061940240d05154140c81100e9580c1c10a0701e0039000c44042c85000605103005011306641032600d41c4021000780780c0f0920403021795000910421b0089550440d486080d00608100510180410302d581a040011030f500e41e40d0b485021b1010340008540c0500000c2c240050501d80c0071580c0152801c00d040303640004550351407482402e1680d84117002d008000812610720500d541500e41400404126101c1c400e04c08254030030703140719442d1084102c07916402401134850864001608100c0b140d1400700c3d80000c1e40c001d1620b401901040c11020440c64000d4034818003d08032002c40082981c240002c4c0100401159603213907001c0c4954102241d107524000b0300d50040c5100b94000700e0101482a0100341c4048100c3e07900e0001e0341000b00b0021000420010103044600d25600d80402001c0007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 744092248 1250 744090998 744091021
    0x402042a092904121a0a0203070807180308030901090215040e011a030f060414070206160309030503060d050102120c090a0b0406050711210c180c070f031b03080a0c0806130203 77
    0x24042c5c1c14100c0310001c0181e0840b5940c05184101001d884140044d550f41208842020081c9140c3e8940c5c1440c05c1e06002181c0700201456200214038000160140c1c1e5800151845840050343c008a550014050011548001590f0300415001d10600c668030f00080201003a808024250914020041c000508940c1e9507000000686c551110b1b01940342001e040081d1030701000c654007903040c41c160f004d9058882c4a40b142c0040780350140e840c07505580b140c0c0c0810250312108201a900740d9000c0c00708410090302112042e0080101220056550400005010851040758480341040c0c034180030030840e80350080c0840c0c040f168880c18101d4064040c100162034507030700d10359410815840154009017550000703110010040219001e20b01e50f80500c0c80e0180d407682c05c84030504021070510041000505041080c03021500c80d0402d41410042904002c00307444e601c203c10f400044264060100c640d403940700381c1d0360112017458243c0032442c020b40881c3c10548030b08003005903103038008000344020588 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 744093498 1250 744092248 744092273
    0x1603020c0d0e04021b101407091e080708070609080a0809011b060606030b01080906060f0909071e0302120a0507060e1302070305070b090a0201080402042a09290412 72
    0x210074100c0d046940c00645950b0b45113440c0b0546d100c42c0f4000502c005c0107074102c50b40e803181c0c0d103507511200498100203030500d031840c0c40e80541d08101008003011803100000e2081d80061300300403006041143c940100106260400d500101c03803038008601800100d141903003140d202c00e00030f00304070807010303e0740f40c44104001e00c801000d0308462610302e000c01d4441d032540241410441c01d030307603003625078641490b01c80d01c50340151516030b409206072002c68000c1c107090815603803208441080c0c401080d0786884601084501d2128039001545102041c0b04500d45980c000d443d0200c050000c100f18002c40c0d89850390340c102c0d03010b0081400500016040590344802c5c0152840e00c400c0c4c000e54443d50940f40142041c2c01020045802d5800328002503100e407800554140c500390141c1d16103625490740e4080c40000c0c034a00100000030400107480b51500c1c801318000b502c3c0c401c541d0381c90000303591803c0c080c11403441103048590000c091903000083e1043d1410160b170709032920120f51008411280c58002c521014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 744094748 1250 744093498 744093517
    0x3060d030f20061605091c0201050f04030b180d120f02090406031a01050d03020d0309140a150608120d1817040311060406020a060b0a0b070501051603020c0d0e0402 72
    0x8010b46051101e0120f680ba002d40c0102c484040c0301010a10140c400e17025901810380c101c0501c0041e0520780c0000074000c080c19006040040c9401c0d0450b00300c01d4583e104d40c0054034031445100a01000000a80038030240e111200081c10444030742110003020000007030301d039007803c40d10750420401007000e5030304036155108000c00401400b81c2e01c2c917040d0b19801000250708140f02c069000080c40d810280c80190b84154140e020307180c90f110740f900a8006048100054917078609c2c8d080046e1206408000f40c1c81e507940114032121180ca554240c640568083d60000d012603000462800c0042c331210042d9141c03104512000f00e0142000d003141445640c140d40b0141c80e40050720703a0364801084000041042c0d074021000e0b500403490440900c0070911880c0700702c40059209549150204882d035020f0210b4200003403c010400b9a5a00042c4094101c000146d40b0f50355940705110b004271180203115000d10050400b91f0030700620300300031612003181c0210f880501541c0c11040300381e80c0e00c50b4115802e001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 744095998 1250 744094748 744094787
    0xe12190e01110f060f0115080a090f0f0303020304060e010c020d050f0d112503050f0d0e0d020c0f100e01081008160824010b0c0102041d071403060d030f 67
    0x2c3c2d070030f042e081e84c1d05815a0485043ca401038004588101019000704100f451500c40155540751200c1803001401541d42c241e8818510383c501c800050410341160440031b0103903801588034245410a8800c5a20b0000c082d08240c0c90180c11410701900402e5241350000503042007921b03281d100d02d10500300d1080103d5008500e140090105050b02d81001030030b21100e80341c82e4920000590208000b41001c03484001e400701c0d60600c910380c4100c1880e001001b00400c491000315429024a80e82440c2c00d607110700c030300b01507009581503007102e00740450608541700c42211018584481c810010b8244a250342005042140e1800010306074000c00700028014448101103920034015540300762540c00300c83c000d8552034049c5908040d4070746803c10002c80310740030071000030000ea447c00348170801e41c4d40b01407449100303035400780000101c0c4e5008500b4804c0303080484982d0309851400002c000c003400c0140842c210101c1050082c4003564944404614000f503040c00c01c000549542e4200356855200300b035001c000038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 744097248 1250 744095998 744096013
    0xc02041e1d0c040c0302281202040e0114010507050a03020309041505090f1305241e0c180901031407060503010311040f14091b01020f0c0405070509060d0e12190e0111 73
    0x1000c1140401c0101c0701c0355488d400105071003044407040c0e01c103902c2070405400d4800014007004007080b0b1429040786050500d940380c5079003581c0721410160013210a90244c0c00200c5c8850103820039004000709411040c0e888119a410300d400180540009054090103056584c00a445003454440745d00c1c0d01c0b500f01c1c4c12940b410341c5020325108010401c249410b40b100c18100829030b240490000c3c00e0035810320074512000c0b030741d4102d203511084d0080c00354101000465441c0d01a161a0015020702075801020f6950200d0a1901540d1030028140e0081702002020001003000ca158442d4000d03400c10b0032031300410003178490342290002d0440c041032202d031001c80d0401d010842d840058030707400c0d1808140c00900d0001c002001a41c90b0148511480226044480748008601c0c1540c41268094403e013061420a0700d000701150443d00105401d042885c0e036141040c00900c0f00300301d95000700102840d1580b1385000a1180740210b0414244e072018400300c0a1061801d03802040080c0342e101c442c3c41220141e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 744098498 1250 744097248 744097297
    0x203180708070501120e1f060b040602030c0708031c0f0b10031506030e2d03070302070e090c1c050f120a140306011e0c02041e1d0c040c0302 62
    0x3640100d108040c003140c501c5060f514000c945d401082d29846000e0050444841c00e000001d9400000c000104101c1c0ea5881000c14909400d1001d80003403c6c481c1e004640301c0380c284000a1500da81504501c980f5401800391002484001d500b401140c103468102141410035415048080d10319141d8103a840311081040c0c0740d0240c0e1541c003080e2000d0081902c10000b5603103903426412180090040e42c00c58100321205405524034202c1c0401c0b402d41c11000c001e0b141c3c52540b82c2403e642040c0b40c04c40041e046001f00304420040310140e6a085031321000a030603082441d06c005820b100c1500d030080b040301360b080e0401c024880280705103401000d2041c21748400240c15a0380460690026000101240c000d1000f001c000140c1d4007920f1081506844416003a000c42888a8030011f404032080c04000040b10b9400040c0c40d203006400520882000000c0500c1005a03d48159109106000c0d00c1c0c15000c8000c180c030000019140b507800710140d400248624078004110007911528182e0914040066030903000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 744099748 1250 744098498 744098503
    0x121c02160b03071704210203090423070305070c140f150109140103020f0108060a03080f0304060c1814010311070804030c150206041b08010509010f05150a03060203180708 75
    0x2040f6126030300c8a500e03484c600054021824291000f42c0780594401070700c41040c10030f4102014015190040302c1c00c0c00010000034080e0344c0c0103c100109e400c46101001d1884031030034940d64101c003050900b4801460001c070f00400c0b280070050302400036110900b4140c0c412209000704090f80900c5019101103020700044080714620a01c1201d01007403500180d425940304c0300d90094103032603000b8a02d044c440100e100465951001038203541c6d220804080010005030203000801d4044c268030043c684070b14003800c08504a941080c01881402010b21454540400c02c85d8a41e059508500c44460141780d104012402082e0f44030f018074503588001038001c20301040a028008403882503810003851070300c403214070541c00c4103955501c0c00340c2d0041c0041400519400b1025130010310304040442c0c00d5656800e804d007074400c11369001d001c3e655121050b4540140700c2c040c0036031089685030f40010b103058010115402c082148000b03040d00b91302201180c01c5154032411a2003003401c000071154000d8507001c100741c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 744100998 1250 744099748 744099751
    0x60834020105040510181b0b030f0405060a0504050a02012703050c10023702060313061407201c050a0905010318060509100203070903030806121c02160b03 68
    0xc41c180311740d09030110400e5841c0106009401d60f58180c020581c40703943c1c0c180300500107a0040300302c3d182d200300105d406040d10020314400c580c100511a014102402c1c0a410014080c1031007081714105400c11010803c0061618a002e5080c030307056800d108247e07441002000c03280501c050341c0c1c0821000209000000419007900c0b081102c1d40300310001c0c0c1c620260b9907501420843c038543c0703c1181031aa40e11400352800680c4101c69543e07001d40743d403581e000030001d61040302c2005100c06030601c18002c1c06000c2c810440451441d501420071400d140303402400440c0d44070603d041030340800464920518061104403081400d096000340c0707540c01e002014040c2d404c0080c400000401036040007074158824003c0720044416011081c0311081607841d4400580b80040500c10a4480c4c1c61084902070403a1000f94415000c43c2d44004101e030951800800b21031000e02031078411200c031001220700c1ca201240002c000c5008001a406010200380d0580c285505103a81001d400103c40000895255900045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 744102248 1250 744100998 744101003
    0xc0301061d04080a0207030203070608180a0534060c05101509230f09010b03010e151e0903030615190e06040f180b01050406083402010504 61
    0x344000c40d00e96038a104501c1c9120095088505000c0224011500d00300c01400105160b01c10388580c20f0b1242c010902c1d10481d40d100c0400501032108200304032600c1074903510401d54035800390644039103a4079660303610b502983d60004000900d0030801d0a00c030303182510506060700e0b10400e10420383d8408000d04402c3e4490780c261003900031040646a40310280c400c0c0800703a011101660325007400c1000d002d0040c030b00325102100c5250700101007540440c045420301d1003036402c195003000d81e14141c100d950075192090032080c000c3c1c0c146201a0031000011522026416402c0c208007444c0d903508000c0504c4002e04503490180703208607801e1000100021004520996065940500313151410b131a41d955840380070600304000d607000c0c590a50041c4100d050000b0408020005800c180d2240c80c5610005d041d50700c0004444255a50401e82c421380340036114800c0400d007000e0b42010314200b0050040307140101440081c81096081c0a0154111a900509012620803518101840d910040c2c001d00c000d0b1801d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 744103498 1250 744102248 744102251
    0xd050a0606060903050723030109060b0312070308190915020301062615220515060c12160b1519080d0503060a0e07090311090f150409060c020c0301 65
    0x10074403e01403e0300808495000b401814a42d00e0000220444103440b542c50380e02c4500ca8214607401c0c0c1d030074043d13021440d020360400130fa05203860b01014a070002c10384850054013000e02046020039081418290301028050080b544c0350982c0303090310300904109030010020242002005141003403680070f54141e8125403124902c412000241c1755560f429a00c0038040c0b0800300000404c1c0c03954000c030452408101034550078030b030518443c0c0407105c01010540c50b07120540d18800c10000e807182a40c0f800030440c050b00e030f062070301e140f00303426a8460442e1000d0b5603070401d0000300f81c800c00c40b2036a0300c03200d85900301d505c0301d900d800d000c4600c1340100800c06d08280b080585c2504900c1050001c1c140c0421034206c00010800b8079542c4000b59569000109910750120010b07400154415a0211075441054541d0311000041d0849c5001122140c003008000c4c00741c0100340800242040d02c5100f00c0d0891441802c0c2c400b4501c0703c07030004015084511001300314070308040c0d4030007016030000b9603200c410804400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 744104748 1250 744103498 744103511
    0x40b040b0c030105090a09050703051c1407030912051f060603050702060c030a0c050f040807081605030d03240806060f040e06070c0c0e010f0f05060a09060e0307050d050a06 76
    0x490281d035020a001d4950b12090070401b04980350803503404012528840e6040e25002940c83c0c03215410442e100c8283d011181001e0146464a9400540043c900724041c5041d800e1500d83e40380180011071901411451030740e820100303024070070104140380310120404890750120504403d00d00183c4a14071484000c24184000b0840c61070010030014032461044120a00b10f03030300c80701d049002d0140d015190081c44020040022000d201c1c00042024201103402000b1a5181800640c90001050041000702c01c2e40390b02400990340100f445000f80519240c08101c02d010800c00e40e9602e040f5109d002004109070b180091920740100c0d0f11446401d003101c0390b04540d09040144800c2da85400b56014154100e10002607155000e0f0385030040c070600825a80c1c0b406511005c80300105402a005258880410360080041e500e81f04d40c03007400341c6810340e10300d42440f189190161095a0750300940d0244a001c0340004520b0714108032238001058020100d21400380141403d07504c0d040201e009450160500a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 744105998 1250 744104748 744104761
    0x110d0c0f1106190213050301110c1e070b09040615090906060c111c0b01120b0a021c052d040c0506070305040e13061112090c010c1b030506040b040b 65
    0x1000c0f8802c1c4581c0300c8101d1a151000346a2000b94411604081c02e400340b8103000c01c0c075880c248a07106c0d02d840141c0215030f45040f042d58040c5400ca455030540d42d10700c46410411030400c808122407040f242042900703500c0b100c3c48400200075140e0750704050800b0f000601c2d0040c1e2594420424811280c43d0401000025180e150480302c01407042c43c06407804405d8000d01403039040c000d521803142d02e6204080c1c07045049c1035841c29200745007a48040b01001d24100940705014514000e00c3d042451514214906811a6202410000d40d03884a803000c5903a880040d0402e9103049102c6091081115040080c01038071012000c0f02d50b007540e007514026022000891035050030b400b16a610750b01601c1d018209850a40050342c0484020700e061001c0100300c2e007920002c4c409001d442e244148800e40c486d298001c200c3c4000e4007940007041ca103030640c031a480600f8a40d805c108007800898020260185048040c07804403107000240d031008040d4841c1404200c140281c40c00a14002d500c10304c01d1007101c1c0c8034003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 744107248 1250 744105998 744106003
    0xa05030f1e2419050610081b0408071a0304110d030c020301020d0c030b060406080103020904060b060f071101030603030e06090d2013050903030f041118060f0301090c0504110d0c0f11 80
    0xc0301c0c0d05d40c00c0381e100c807244400280100000d1768400a4484920319a04540d1594196a0842c0e4004102d55102c3e140c14014141d10314054032256152944460441c81d250725100500c54019a4090103141c0f401031040500d44607044071081c90b50058020740d6074408844a1030014030b01c0d882003500092506149060b5841c21350308903400c8660319501c0c02c500c3d07402d540070031241e0a00a0001c5425035990f038541c5100c1c0c3c4400010f004100c4140818640314841070814880340450240e9081c1054540304040c000070fa044140d0a07204102030f0f5100f0703140c01092001c0b5208071001a805817018020040108092054075001c80d1850019a81d007440f5600c08240c49065503c1981ca03024541c009000103000800348014803036005009072014114030341000c02080307081111504c0c545070035000004001881c10894500c0280d482e00360020040020142c03102c0110b40f0a40c02560b2090f078540640300351f40b007115006d81b18000c100c0881002104181d100190400e604007a03800302140c030100d0f115a1183c0301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 744108498 1250 744107248 744107251
    0x90304090c0908060a0e0f0109050a0b0a02090907200715020c2209021318020103150506070b09010b0a08030901030f020307020d121b0903020a05030f1e241905 70
    0x4260003000c0b90340301c4010388005041c048407041d0503842000d1107da2541403d00404030058000c0000e001c5e48510790605c140c680302c00500610501e4010495440103494503542e40c1d034020703414a0911f1003003240140d1403100c00340c0c202e050000c078844d50601140c00c13074080d0410100b100841e002c4401820700c0b1800e00540c00800700d908164189039055401c81031419810499020744000c2c2480c0d002d61826000504554608900d142101c502040179030855815124144001c1d038426007e0307804d1440d241c00607a86106084000740380c40c940d40701084424109400c412410140207160010103a102c120172550390300102031044c0003a0601100183d00503282c0f003240e0080241d0b80c0a4042d009034004184d601e00d42c01140c004c40c0c0c0766259040c280c8062000e400d00c17200c02669035240d8540d8610300410650074900c4c1c10480c0300c0c3d003085100314820000004d04040f450443e2010304000401c08900038244860700ca5095500070551860010745207407054154407541c042c071a006000c0704500c003540c045660 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 744109748 1250 744108498 744108509
    0xf020c0c030d0c030e031204090e0601080c03100b060405060301030503030a150e0403050903070b0d02091504141c0b070c140d23090a031110050319050a0f05090304090c09 75
    0x100f055410003003803240782210031006000d011140d5a007454050442594019403001000b19170b90702060b0200c42c005d100030b60040074008010725905181c000080d46404068500d00d20503584e43c013000389242c4402050750300030103008064586a42c3d407406c10a84036402107400c42c0e41c0c18030b0444001c4d04481822404000c1d1050003500c0c0309183d6440c0e50996841c0c1c00302100d50350621600720000703000728109005101c42c2d58180e2015899201d41000c0c080440d1540311441c0c8808000d020511440140510401c03013000c003110f100809417100d00e0111406100080081e01003003c6100700710006030046403c0c2800340c4603440141170140081d51a5460706540312046001070030301c801c00c8041502001580d030404840c100e500e4a03080c441c0002800c58030491380700300d034000071800c407802071860208181948402d4a051a034034629160302c44112074103007603140070500d6640301c010403140a280c4e40400204011800c00700a14200380f03003115030343c5e0003170700c41c4d8a000c6085c81c58010341a0700c140d030036804076070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 744110998 1250 744109748 744109757
    0x23190e1308040312020309032d0f190201110f0714090405060c1b010e0607020f0d090504180f0c0512150f0402031c080f101d0c0405040f020c0c030d 65
    0x70304542d1800c108441c11398010702180320034040305120703550a2110640798202030540c01c240001c012854440503903507140e201e42075041420b00d26100b040c04903140120100b560495407a44200d40b0050b50580308410880119229240740c900d4100c200003201401c0c2c41e8040b4494030134083d0842003151001085030020142c1d0408004564a000c3e190054000c0c0421201e50a1a8064140c82142151002c0d005901254010f000b0700c0301a64040c426028580c1d1514042d00d080e1020450152004171684503913030099554000a00d0701c64525416000c0d4103030300c040c0454202070b15041c4901c44850f1401400d01c5544040c0888112607030001e00340e816190404410001f0356100c1581440c03143c001403050307030140502c0c8103d40308140c41803810300e003800c0d4a0300ca134200c03400c21181c40d80b42c0c0000200740c1110b044010a0612010700e418450f890202c1d130030300d05d00c046961002802c48a40c01503902c0590040e0800100c0d0305508040d07000b4207042405c040440c1ca04904400805a40b42c04490001010a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 744112248 1250 744110998 744111007
    0xf060501050d09060e1f050a050f1501090e0c0307180501021908090402030f040303050703094107180515060c0a0b10081c020723190e1308 61
    0xd001d03003060301400d0054800183d040501c3c60258245860030b200003103624a03246c40703502d901c00c25104158000700c80c40010841807800c0c409010070a080a0822098001d024080c6003042e031040705000c015014410200c009400d01c00078100c1c89420540f21171021420b02c0038100790011180c18018226070781640205a07400c1c0000d01c00c81c0e1464152410b1707540f0705040005050300e031120300040d0300900d4001020b010503d0300f03060040803103c0141c5540304140c105402d06010402420121006001e950580641c0000c4802c00e50350030707122744502c01005131349421005c40d103900114603282150a1402c4600030500850350b401c0071220200d4030b42526180802140a482c2418000b501c80c0511074002c403407100c0020385440e061082e00311000d662800c40b40a01340546001403100200c051001c0355803120a042e21035010351540b95034014040c0022400c4440d1040a0644071100d402c3d41c80500310103a1544080075139054022540a03441060b803030000401c10a00c1e03d4a1640003103a0061485410b2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 744113498 1250 744112248 744112267
    0x81c0206010605161b0e0c0702061c0f05010e16090b0301090207050a1e020a0605071a0a09020a03050d140a050702060304021503090a120c051c050f0d0b01030f06050105 74
    0x2600700c244c02168800d2144414400500d07181c0b1440d8541c64500000300da00d034600541042054801440781c0c4403500309001203c01a201d0005603441d40000488040d441050101079400a009004410713950ba400d1000016540c0401d84001d8000c1d00c0708580a00910002c1d5400d64000380d40b03105036071460400f0001000908882e5000e404c4951081081e00c000800503102c2a0b1004c00c0c503080c007919400011a010110314100c1c008000402840c10b0050030014035071201c0c4080030722200c101140084c2c6d500061a80340185d40800c00322540203104041c03558070781c201980c0e43c0001e420700c100130654004000d03030004481e4007581c800720056540d162034151075509100f200d40000e030040b0303001f10100d1070001500103d580518401d5010900810107205181040c4001e0b500c07a1043d2018010510800004500301080b05004401e0381d4176524001c125030507046800e440707154211040000042900084040d0348e4102c40d120040c241c0e02841542c0d00e103000e58049410902c116400714104222a019 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 744114748 1250 744113498 744113507
    0x2706041a0306120303090c1804022101020d180507050102010603051002070309170c150313020f12060c03010303180b12060d0c06050c0601290c0c040c0801081c02060106 74
    0x81c000806808012800002d10f040ba14580091b00c1d0408580c0180c1070f244054205419a02020b00b00700d400b80d44642030940200f11a840c6094401900c3c0350103014500d851310003501212030b07000300351504001010842100d06c42400036590211034134001d4540005403507105000e800c00f603c1d080000f401c3c40c4d01450903d14020f500c2650b00320700380400400c000400304034a0124004500310700c0090901851031000b0001074400e41c1d1004070350900244107021054640c02c000c482501d80c10f5035060307806809803000075101a00071805400610600d420001141c0c40c403800342d4100d91183e190303c6004200c1c0d803071a0307208003542d01070304449140238007900da100034280c002550440405440c0c00c845180541350000044001e03080701c4041440001c42c0303444480308004080c01050560301031496689854006420790468584221401c000070503040386100c0305112001c039036480100100700c500d2550f08050086c1009124190003030080312810180958004000041000180d0252525a083c0a8280c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 744115998 1250 744114748 744114751
    0x60a140c0c0a1d0105190e01121221020f0d050c090909030301030807030815120313080106180b36070c030822080f040e0709030c0b030705070501022706041a03 70
    0x9401b4072240d4800140b2034103841c8028064001048000aa41ca0304c0c140b03500303203154242a540c100000300700009240d00207010000071040c085000540c0e46d450750740480100e805208201801ca40c6080240203208a038040181484038007901d00c01072a03601e1044468a9010921010b00003010400030600028030450485500c40c112440b0954068070400101c0c202c0800c5020300e030303c564000074096461420b0b0403800c0e4020320010009000d02c03810504820003001d8510b04460110f80c840081004c26620340100d1f152408558940c15612100c0c0030105a840c4900100c142c50000d00c200410b2078180315a492104240e01621400040d4648526010000c10091601104a01c04d0004400052032410041010110407038034203403164140355050240310700103072102042c014102c100300300040b801800e10088900e500030b0507071241d45102d015561480382c0c0f5801400e551000424803808034204100c0320459502e15007400f100880d03581030081900c1036009091500d07810000da00c035200c0c8104c1c01103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 744117248 1250 744115998 744116029
    0x8030a050906160f11041e0221040302011509020702010e120f0f060411010e090c0d090f030c12030e0a0b1815180714060a140c0c0a1d0105 61
    0x1a183c480340710020f09049004040440b000400c60100c801403003000501c04242d81c504850811070070644000c216810104001c0448089070080384a82042d05910007035281c1c00c50780036000071a8946032030028000c0080601c4510380ca81000000301300340c03525109880c00c10b039041c1c49900c900da1010f003c00c29010940100d40308980b086a0001c0d004032700a0040d0f24007007010f04028a11818540741c03030601c03502d2250600f4100654030f01d00580c0c940c0d58149960300b0034900d02040e80e4030141108842c014086254001d00b50f009400c0e900001c059010b00c0824549002d0069081c2004901000301c041d02c4442030611455444400d11002180404003010b030041d5008852440112446080a00700281058554903129030b58040002004441e07410001440208003d000410b090552000040c44140c2034140910808102e08a886008070304111100b996800540d031545915400035580c0c1580d140f059026228803403001601c0120007200d00300c202a0754612681580c205028400c10201c0310000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 744118498 1250 744117248 744117259
    0x3061d150c0406030b190f14030102030609040f0f0c17060708060f060f120c0a020d0c08070b0606130b0306030106140d0f2a03031403042a030503040906061808030a0509 74
    0x28121680554080c40000c0035680c0c1c582041a203010a0308040e0f18403010303123601a074010803c1142c103540c0c050740258840d62104280c07101c41e0050406038032101600358001d0242c401400003241002002c1b00491601c101d48003242c100365140f030300403200940c054451302c0e00400210440900c51501e10302504c102d00712112400e083c00c802002104804000341c0d2081034031600007429643e1980c0c140300c0c040f0300b08a1824180301c410804d95130000d042c82000000b5181011007030101705169038071001c4841214003020401841901c403c00c0c0c1c1d906510a44d40e0605c25881c1040c00a15444006207840c070010000380301907900e02c0c0503210340303c25011118045070f400c2000944002e5541d41c0f01041900801c0d203025200e186400c1d80fa001c0c183c401100070118201006204010000e600e4240c0c0d192403130010f03685400c6480cac3c2c08604400e6400b02c0d4100800b98040482c0108840b0b241f580204100d510503075482c1c41080c88a1800000098580224000c40e0010800101c0003030050f03008048580b4050007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 744119748 1250 744118498 744118519
    0x911090a0b060d0e07060206040b040b100503060403090f06180b0a0903020612040b06011d010f0e030a0501090c0e071e12060909151505040905010603061d150c0406030b 74
    0x15181e0b8070140240f01c003941d4484000c03001c08810000b40c006881240020f1900341015140c0c45014003004000400580009000490626164485500600010701102d03030314209031401030140328881c001e0160480e160743d00042d05501c1902c01d00c5070003c1102a80011710304004049082d40e1105443d0001d00004c54400030068481400810000c000f40580d030801e0300701072030100351700040035002034100444040040c4c40d40703880401c50343c0401c1c4242421a4900070249083e0b40809400c0131140d4103000c3d880346002440019002544018400c0c0d82c4000e9035901e40d00540c0310420700380c40c180002030160a8050b0a024091a903031107a04203030415170306208526903254141c40183d041b1000c51510307410300d242008081c51402d441c3d070b030001d0b501340034200c84403003514a00c0100780b02d26489070f074840e5048401e000d001c2d40400055500450244110044c04418440c25192000281d00e01d21550a04030301c04410558294010300884952030302d403900c1c0500840107000604400e5500c01844203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 744120998 1250 744119748 744119771
    0x12120405010612050f010e0a110103021305042c010c0e0d080706020706060e06040b061804090f06091506030f0b0a1b020106180b060a0c0c0306050a1e0911090a 70
    0x160510f081512400084c00e45800440056007034580041c9641d450f0ba00007030b028000582c19200c01c001070a002c2c600180c49201c18200718515400c1a400036401501d4600070703400c0601300d00d222030040e0000b0424400e404903544201800c07982c8a01400340003642f1001c031440f0600d44600711000d41401090998142902a141d460499014620403140a6503581c1c01b00440c0306100e03404c0b54403d500300c1d810402c4c0d02110010600c288201d40c908503810b020a140c00c03285a80300da004c446007640003520400100040c1c60410020929201c0c15a0100040c010401032000036002d8001640d51204954808080030745e50050031010141c00010050384404450a1381c0b0b01c01046091200c07660303800810b40c20314240c4230f0003000282d0004404154180500c80d86030b0748070481210b541d0082494109207422260030024000c01c142e8000601141c02c0006020b0346c01a0303900424000200618803002014036081848121001c240300141181140d8080200c0d40c074002c5443c6603c99001080880c00f0710190 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 744122248 1250 744120998 744121019
    0x4050402061c0b040b010e0d110121200f0409090f0b0f0f16020303010b0a0504080d051201120302190201050904090f0b0c16062d0f0e121204050106 65
    0x80e4440190b0660b5248001d50b40d24050050701c0015200f030801c1e284500c843c00101d00020144035010f410100307020309203055079114040c40515070075990001195007003d500540b01030240003441089941140386030740107441d0f044040fa451136a1500020303280500d0a04400c014140404050300d2040c07240c02d940d000710725070142480c4900c524820800c40c91800b2060100e02907405007010300800c100f00041701170590000212419180030070b01e09502d5000ca03400c1182d60b8032694000c2d02090140c1152004c0c03068012025011303450a500c1c060f0f43c240e0700c4040361011503000600107070041e4002d04901c2c145038000c044014982c0c4c010305d881440c01049174046000e0390628013044859221000c040001e0000281e0345940204030f0f17070000b40c6403445140b09801010210302c4050000d554a080401000d20000f461266401401c5140e035130418a6030000390048c21703c080c441c15841c0c10014220750094010030609410800a01701c5400c00000c46400c000c011002802116550f603180e902180160780ba = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 744123498 1250 744122248 744122287
    0x70b1e01150c0206130e0f010905090d1809021b06061504030f020d050d0203041a09030718020403050105070c0210090602032203080712090e0c040b45030a020904020405040206 77
    0x4005c0f6005d460514202c00003076007d05a1082254501e44810700140c407102140482403240c3d0b615007804c03a000c4140e0000303080e1040380e106030314141c400540f0359800144031480c1c181021520701503803c6030f59680188002002c0912801c521300f10100010b000150040070030390003c03800509281154162030341d541c2d01d00100360221501591012030100004d11100000c54589003000000ca428007042d00007080c1e40382c041c4e015503c0069400242007007007c0441d4191001150030070000c2c040360520f1603000d894020490350036401a101c54200154050081039442c1c2158540d038000e6103010740c0480140341802c030b0312045182c03480003c040000843c0446014151040c06451036401d000105400503060070010340c80302c90010218410072010703424100a031821200482100ca42c0c40480f5401c01c1c82c03c2007003042c0380c1210300a2083c648512a072034482d1281c0560082d112040c0c042c3c0f606c0c02c1554523002030900950000c0c104001800504081d0402c03a0002c0c400b6160605001a007110151a00c05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 744124748 1250 744123498 744123509
    0x3070b01170307060603030e0a0902160f05030d0204030303060f050303030f0115110f0c090906090601030b040c0e070915020705030304030602091504060e18010302030309010804020114070b1e01150c020613 90
    0x28400343d10340651070180c8494000302b400e1242185003000c82040d0440c0803c00079800f8162020381d045130018003000748100c03040c2c000074142c1155103a03140d25010b0001c00311030103103050070301480101041c2c5040c000111790042c6140d05080030280e10300031441cac0019079049456810030030480510882d282040142030100c0c0107560292000c1030000050156100008102040c1580241c091082c4420040b0340300741520342000c064241640c543c01e01e1003035031180741c4c080c29405061000f0071110300e50011400f410307207404c05003d0122140e40c110483c0d03204524060341e685a00104420000a00c555006050301ba5010301840d00c9000310894011058100307912400c00702c0c00002110100b890540300810644080103003025031541143c0102e55a1b000c0c0307031903032814080f07040041000c2d0384c001c0780b03a00c41094244003035982c0c5540a02d00034140d900c007603034020a0b001405103a0640441c1c20303608075050740d804403c00045040d40d000100d0b80002070706026600a41c0810281c4542c0c8602c0840001500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 744125998 1250 744124748 744124757
    0xd0606080f070e010503040b040804030f051e010203090c24040602070602010e2113030821010806090c0607030909090606080c01030b0105040b07111008060a060203070b0117030706060303 82
    0x9860314480e490030100034107007420401083c81200c850b85e08072095a810581115449501350348924140e03060f84540d4001805064051811900308080003071050400314640300644c82612040c00000d00383d001c25545a142d44e0480c5c0311101d441e051040f0070030440708429254190001c203040065641343c1c02a0020740040e0400f250500581c0d409005000f8600180b1008080a045000201c00c038403094842c4151514030004e40651182900c020420146070080c62050380c4076000d4001024110100318081c0081001000010307002402150300d5120b12401e1000e030010344038010400000d640034000460038020307400d0303021a50648500c580e4240501c503200000780301c0c0c20f02030500e1411a0611031241094100340348484940d0340f1070160303070031a81d070821090340380c0c0407074030380100c410300100030058010701344609643e840c40e805031040c3d010b01015100030b90920b072100d03004c1740c0341e21032001c015144005480042201c1503401c8000304008104c60107590410100b07603904400da404503030084d07000a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 744127248 1250 744125998 744126001
    0xb010219030e03060f0118020a11070e270303060607022707120b0a031e02090c09100807050a122a0206060625021c0b0703050a140a110d060608 63
    0x9040030031045802081e10302480d245c40d03140c41ca10100012410200c2d003d519000704071034500c94007034140c80000b590010203031264035488109040300804219604425041d10603c2400e407086101d071803170603600300b0380040c5240d40d4540c01841701541c03144008a8000c40c1c000101d00d0080036900c0303864140601545908007604103104028001c42e0404501e40c0c000b441c1000c1d5845550f14140d0b0038044a60101c0e11040034181020200d800c40344c0001e0207504011903400700441d08558000901e9100c030308540000200000c100700307d40300300c0100c500380b0100d0801c10007007400500411a030100c47c0d041540209042083c40c0140d04441d000c98060714110459021106006406001e0940d0041c000c5d0341e620704040401011000518510610920020940100d0410b40d21006c2103044003070402540d01c01d05e4070803490031f0580200e00312060400a8945070104d241101c19000780544103000c0c150080e002d07280c1c04500001814010300203040320004000c681900c1e82c00340901002000c4584911615 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 744128498 1250 744127248 744127277
    0xf030c090b1206150102010e12131208070312020403080408030703091e0902031801061503051e04110a18020a020606030a080304080c1015050f040b0f040b01021903 72
    0x29101503407655441059410340301c40b46400000f480302c0d402899100c0c000c600070008401070b8010700315100a4000c602850003103110343c0c44200300a1a2040210612121803650ba0302d10700e55008290304000c3c07220b42c0c100a0a8080b80c03081440c0c2c0720905906800600e8280e0300e41d140c034240d50207a48902090303000411850706054011000c08001d111030b582090140301b16540c41d100c179407968003420444c07941c044041900c02e03e00525504102d1b50b0700000304401900c0d800b5100342105580c1440c0006030400300054500071489007000e6401c8080b6004200c41e8a980d5184044e04051002c0ad41d001210200000346100c0e241160758001c005910300181e1364a03041c4c4000342001e0004040d140254014084880000c0c060f0307003260f0f48250000c10701500c600c02e040c00c00c0c7c10302d180003c0c4203120a04103501e1004443c8110a22011038600b111181900b40d00e45041c0029140c0d0701c0100d6601202501851085080030b800c00450110140305603041e5101008c1d0713481d00120000c0040e03000a03940c0e1811100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 744129748 1250 744128498 744128501
    0x40c0f090c030b030109390f170d0806040c030f0908090a120807080a09120c060e0f031e03120103051006050910050f0d051522080d11040f030c09 64
    0x194260294005c0c000ca418546800031401f9098040104002c0c801411085c0c02d0500b084071001d144920024a40459840c980540f0701c0000d401602440703652024600004c5400282d420355403601511074010664030f00c3d04000040c00510940b00615407034181d00240051a4032515203c20b02c43e0030700a85a8180d0000c0c0004000c058200c100c40b8001024010041004002901c0780c85601000741c56407405040301c1255041e906034040d40c201802c0d07400000800c1000d07003c60301070303c00036515003101c000c06808112010300c1129140d40c040e04a0300480c002c0d014089242d403907042800381164540351703000469810412090340203031040d4002d40811400d089007400f8050007440c00301d541e15164100820580c1050209101c4e40388580d24030b100a00d42900c80701811a000e40d0494242e4504940759100d0550241003124140701106200c0c49032658080c40010803c00607400c908018108103040782050018045101e036480d100c0403c1c4070000704004100740303200185108007030421480b071a01d05c0c00300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 744130998 1250 744129748 744129761
    0x2010c180f0e06032404121713050c060f221a07170c0a0c05030d090308030a060b0c0d021203010315020a0311041d0105042003040c0f090c03 62
    0xd4041003180003005601e44614040c0255500c851030500703141c40c0c04000926001100c2d01404055501158892040b58a150000c0c401e40c0201c01511800c140300804032010840d050280d00e2a14200011400707049100103002903003032044045801c0d07100c034040080c4044d0011000d003080b9440004251249101c00340d089691440000b450009403824400d0003c07412010141c420101803010484405001c40280b0b04100d545524859a5a41d10410640c40d110480c041090751a803041c0c07040000d29007400103008001c1103c9580d22411705040d030350740000980c8043c00d0003000d04d450b4440401c159880301c0007000000c2d01900104900800c500707000e810005111682000541e0074401000415220b0f50040e0800c0c061100041c1c2c1c80d121107000781e0040801c41007004d100f590105020609185a942c04c44a280c17100b480350a46030303039402c01c110540b44c045c186550030f40300c40310145811215420146810500c196800d0301f14544036170304010241b010390300c03d4401e00e45661380320422603010310415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 744132248 1250 744130998 744131027
    0x8130b0c0a031b0c080a0e09041109151e0d05030a0207181806020901020a0c030b090c04050c0405010f300b06130e0a0207020405190b100f0f0507060c02010c 69
    0xa10f905007035000081c101d254002005070907818009160307200c640c803480401e6001c00e0010308490345418941040c580b0b55504003d43d50107441c0303150100c1c0141c0982e56011102e8079004049515a0701410406032111903c40362b5143c10415213008440010340c02e0000e030000603225401004014901015108151540d034211144185017030310341600308820003503204009800c020f000da581c05c11329004070f1402400a5024220081207100071040240c4c00106030300400818040b540d04559860410044540607580c0035031a4108000400155005d1003c1d01c03540d600c603092000f144150810840c0e84001d0b100f1103c0840b50350381030a0030f0010540d00c950908058190781d01424420541240340480381140500e00c440030764000010b034000ba1540407560400d50241c0240228103001d15900080414441244505400c10600714000e003071200c00320034a80c83c16640e5900b4403e010701c1c140c80103400444e021013080010000f11001c1022070040b2101c100d04c41d800080c42d502110070042804041ca10302 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 744133498 1250 744132248 744132281
    0x70b0603011d1519021305150a0804020d03170a05010305060c070b15040f0c02010b0f0603060919151409010e240d050a1a010e041208130b0c0a03 64
    0x1110007000300000c00d500a80155070403004181c440b44540702d031214013009010b02840c00002d403001c1010aa02d10071084030021b0f1303403450034481d41c9034140d9524014620803500207400341000501600e440805c1601240c0a81482e10621070752981803199030707408884140580307032108010410003100300102c03944010055603181c100141540c9a0003030742c20141141c1e039000c048009180340c0d41c2e0b0710b80c000d49c0e10b4414998100100352032517101038080d1200485542c41040c0782c00d000381460a108084a01c1590b00406420b06a0758040e0000c10105203224045105580c3c0d550190781500600e41920150250b206980b514181000c204202c01e60140c0001e0040c112071020f102c03043c6400d911201c4039040110020f000c0c80e00c500007048400d103814130003074443d208014003a0b040c4108100d005001c03607032800450b138603a030700e401d8070103419403058400611216603040b00c040d030b15120300e942c207400000210f243c07817203d2041d0f00c605203924000d0b21100014140001c02c80b41191300743c8203004400d91035400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 744134748 1250 744133498 744133541
    0x1050405010c061d1e06010e01080a030c030c081b060a0b01050301050409050a15060611010b0109050108071106040b180a1e15020301060302030103030905190501111002070b060301 79
    0x38088000300b00001d041030780381d0701d05050060007410107100001a000895400801c5040c211141d80310b0484494050301503000003068902071000194140c4072100700414014109642c00c4aa8142d02c2c1820307410405008140c1e4001000c20000b000402210b010038004181c04502030b90600d01d0113017421002c0c0380780c0300c0c0080250b6045810380f81151011200021150841e0500c0360508055050040c103241c284260414110b0445d4481c6060316816540c5106010441100600700c0e858039038014045280884200110742c0324029050f030bc04920710341081c0d000c1e6a8000503140150564084902500341e10403c10384290180300b11554a03c580014102414144c4500369040c01540300308008418011040c01408016120440c00c0d10f00110115a40c3d0781d100300c020000d40081c007003200090b0207000001400d140103030500042807201c0040c0f0b62010718000c010344489000949800300c03400f0384281685840164070141c441c0d14010000003540f45003400401d82107400303800802c4061203100c031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 744135998 1250 744134748 744134759
    0x3031d0a0b0307170a0501090513240605182d2703070501060f0e0c0d0e16030303091704030f060207051603030c030201051501050915070c03031d010504 67
    0xa15081103880c0c040c4400d60300e0f103c0c80800c0b01c0800189080030121950708050003e010003e902c400d040341c10180302003080740c41d4065200c44540d10300002409030400111035400340351219480e03240e142c101420008178155030b000070030305100704440c80c68004100e200400c0389243e1198408240c0c1c240400c10b828001455124a1042c401c014044c00c41c0701400c84c0c0c40e0380300180301c1208445908107003011a91904001c0c9130940c040c10a9009940c240da800080005109040d4070016010301c02c01001c99013403c090242141c01003150041c20380035440b030510100149448580c035000514040d0350045100b1071581070540c2d041040800c03502944104006c100040f1310703461607040e40140e0240c80503030358000a003007051410340c04803c1030380e06401d4581c0000800d40c204851840e1076200750000d0215940b2212004502c11902e4829800b00704104400100e61800c140f440c902e9508525605003000c6468542041640e01600110041081840c551a02102c0442e40021146091a01d01e24060805 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 744137248 1250 744135998 744136009
    0x80a031a0102030f030a18050a060b030d0e040b19090f0b060a090303180b0d09030206070206090c240a052119050c070512090f0f061b0304080f0703031d 67
    0x10050a0214080400030865011140c7c10449900140320081131010800782440307a201d100c941d00444400d45400400340c42070031302141c080c1d003000c0f490302c40010030444101880084e240c120f0125501031400e0900b0070301140844007000c0a009811000550910044400c40440300b03c00300c021321074001485490411540101e941041d25454906415a042d0711903052580d00040c0c1c210807018000480c5021040400707a2150910b5030003942222440c0e1607400007a0388078501a00c40300915045071900100c9806c0604d40c1c80c1864020054060300c0180d6042d014681e60401041c01c4001400010804240408500210000d610015611400d0b081030f000c44040510850300b40101140c4440004280b46d800200340c07510b268101c030944015520b9625001d45075407000310f2551040b0000e144140c981e06004420750005c00300641811f207880ca030b50b14039490000d885484441d45100c10000820007403005d019290000c080c240080c5506411881e02908645482c0060404486002c20305403e40d984c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 744138498 1250 744137248 744137257
    0x1030b0d021e06040b1c05010902091509150705061806150405040303020d05040b06150403020d0b0c0c07030b0603070e070c1101120c0806090108010203040206300103080a031a010203 80
    0x14a40828031040004011070340074021948401d80c5c9600202d00381c61751110701015204524480b40041060781e0b01c40c4801c5049010742040c0300e401ca845494070110010f0f0321001441c0c0d9030001006d45814080c210090001c41c1d11071a000c80e400e4010b101800002060a000c0c14003080d4100042c10140c585254040410300314095402e1043e62580007080506000341d0455400a42c0048107000070f207414101090011000d449a600408020344040050381c204c100f507500382c9070b00074105090b18441d5115545128005808007000305000c1000c626102d404100030001540702c1d2803400c200d884c2c50740070141409120b42c01010f10300205401c0040b400c0d032041c907402c40c156001160b551680c58504c012582181002e07420445940743c9140a4103070b0350000c010350300c11002129140c5491383c8030403507503090740802e980094000105000f0141641c07001c04004140310320fa1000414034407101402c28003c1c1c10281d000352001d10000540001d2140d050155560302d06403e407840000d068841e0000751303244213 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 744139748 1250 744138498 744138529
    0x61d0717070825030e0d02010e121804140f13030e10020709050901091b031101140c1c02060f0103021f030f1d0f010c1403061c06060501030b0d02 64
    0x308005208101c030507503409110190b5200c0c0140d0f42c2d02d8408050020400a5044a07003031040c50140120181b0500803039001c101007170701804010314183d00040198110010f01156042c508011458546451060701503c100e04092034480c2e051030702d11403005080c00382811001740400e40c41c4902080d00021260f0300c500090f40c00014160003108100e060110540145402c00d0400c0b080c0300e41d13410150803900403240a00480102d003403440512a00000c2e891000070103954414004450340d60046001c40101064070300c90740c0c034205040d102c690512039403940030030080d01910b1103240301540c100007141d0320030407040c9488015411500014603119401031140b1540b5441000b41c400180310b9007200b0b40b942ca02010601080b826001c426a561060400c40b11580c486c003c080031180c98140903008070440340b500c0da0501d5060804045016a0004050307a802c00302a0003a140d40001c1070f4018020b1034042d0720001510b03418500010192008080d44501c02c2141c28081ea0140e6200d904040310000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 744140998 1250 744139748 744139757
    0x80114100f081203070509030a060e1005100e0907090e0d2a021504031410140c180103020f031f0503030405060d0504061e05100906080c0d0303020d061d071707 70
    0x140e910800320340c80e00ca203121fa55014041c1c0500f02c82000a5904038a00e04401c15017600d052600d503040b0311048610440c2c41d00d84401030010f0420200f54481910b07070308120b004095502503615115040169080b00202105541c80b02a500c10603541c00b129000d07901184003581c3c0445c40422600042c0803284901c041e104400400d0340f0340302d5203201011200110361048030102d0208070900e00d183c65a0b038800c8400b9186044c0090301010705004441c9138030804a400d005410800c00c6240e0a150f0049c1c101c5072418154204064071604c1035132400746102d01204039100000a49401c80c40c0d001d040540e0149001e5403051105000076540c40c0241c451711241c08000040b243d0b95824040b0140880c111a244001030312407101100d40504e4001b00c0c815a12450036212803540d078240c2c0412a0441d1140142c40e801c001030040191030403005086081d4080c2c903025040491010035030301214000e900c02032842088901c1d910182c850301041c12762200341410f0000c210a00a42011404c0c04018105002c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 744142248 1250 744140998 744141001
    0x430230712090815150409020a06050c0109210e0102010e03040324020a080709050915060c2107020a0e070c0807031403040825020a140406080114100f081203 69
    0x42c1c0308028550081684008070744a10340c41c0100310650301070555202420103503a5000986909040c0281119254013800201440c4c2c40c2070b0f000c83c0c031500007642c441e134155214801c06000c24044038488080700701c031041110703806007409000f03010a003100c2513250540e4103211302801701800101c00d0b1012660800d040400c0c001e0012241d01c2140345a8001000715440452035001c01030740400a40e1280ca813035100d548145403030f0700c00c004103840d080f226606080003418038000c503804c102003e015480c00c00d4040740d8101000c003507542200900882000300c045000b00c0c2c41010b51a0210710100140310701c2d8042d155500340000010140454114082c20521000a4440405200b0b400300d81c081d4504880c2c060300c07030405240806443d070101c0121500980382c8a00d4544035111008020180781d40240b09406041c60100c0302c0c1d00d45100700180c40e621981e1484001000c020030b0040c1c0208820004030005145491400c07d450220550441f082a808240702440f000b14001f60b440000584010300945a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 744143498 1250 744142248 744142283
    0xe0d0809012102030717090f031b030c0706020607030c05131712030705040e010e09100c14030406060603060602190618080705060a050c2104302307 65
    0xb5901c150180401c2c07030b840007042000c2540e00000c2001c2c82010950291219210b03000c0f00390341d0304c043d400c10741e0301900100010742c0d080e144000c08400c0d079003101d025a424810301c40321903410040e50ba4051400b580140c0200185551304d4840e18440b001e00d8140141017440038030103100c04a10601070910702c1d2024600286403044108070f1840b400e1854622540c0da8070702400000c2043e00305205c0c25080d10845000890082c0349a007041d441400c00600405401300c040101c0c1014000c40e00040c0c05024020148108050b440d80003184180d01441020501c1c91601c0f500800319483c9620000445d00603540c690300c0e1074240b4140854050700180049440188410092107101003000000e00c000000115002044008100c031480764541c1f4100b00314990300c62908001d50711500754087c480c80300b0b003101580d9030784454000c240c20a00501c0f280c110f01d48000c014006010000d0000651030504800070b40c181070348803d51804d12545200c160040d10741c4c3d110b4052060045e09001003d048114100c800c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 744144748 1250 744143498 744143537
    0xf03080a020f25050405090a060506120304061d0d1e06022b060605160204110906070813081c3905060a06031110020a12030c0e0d080901 60
    0x10b90002c001e81d0b0f441601c0c4a603025201e20290420303411220b00603400034052600744203080c811034901000d042da4000d0740d520940141402001e4607840220900c00d01c00e426010400750004d0300c02900c030142d101007045078681407050085080d503c1100b0010340d400002e098992100242400d404801000c806989400c0000e03024524410b5000300ca02e421a580302543c0720050500320440304001c1000035201c03042142c00b849484095007a035138036040c10b023005003440c0c1e00c030200070102e0039011428040020001091030b07105031025030f00385d8404506c0f8245280c5410300200108040c5004251030280001420f640321440501d0005115103461414250b00b050381340b2140c000c0d25000c4115030141c502c0f211030142c41090300306a68910485002684d04080b40c07044206403600204e548807514900800c00040504884030001180148070301345c0002003c45a485425400b1920045000700d4042c10042917241701035080c40c070401c203190040e03000c92924811035151103400c3c0307000150089418096038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 744145998 1250 744144748 744144763
    0x30321020408010c0e1002060f0c22030305070b0f0405060606091c06060906140607080307091206050f090d0804030e0a03020a08030c071d06010c0f141011040f03080a02 74
    0x10314a5084c02c1010042c140e00810f680501481250788078059004500308a90310a0100e03035a102059500d4049901c07510b008000e0070845803001c030449c15441c0c0014500e02585400d503c22000b20341c01151403070810900007032469002c92002d40a032610714164030741e03d070303140707000341200380240f000203805000343e129144401204001c051808042c001c10b443c141000344504d105011540b80b80041c081103403100c04540303080c00b06009001a082504c191180901980003802031400d01100310f100140f990542001100c80300e0090400143d03626042c071584c0c203039450086c01c0200359000001c0c03a00b003040d0420040c640142e0140350458000802c0ba0100e4000c0359140c0000c0e510a00c46800080d500c100000200303c103102e078101703480e0303d640e403018a2810704200e1030050304600780010008045510406001c1241c0b4001c2090000050351604e03a82c0c000102c2c02c922039501d8015500c003141d20401d40c0502d205104194603010310b041d02d401c41c02002201540002041e043c000101c041e07949100b000b400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 744147248 1250 744145998 744146009
    0x2c0d020607030806011d0f27010303020f0705060f190509060c060405010b060a0507060c02070b0d14061c14030d06060c1b030308010e0703110409140c040303210204 72
    0x160799a9810b0801030424041114114000350f03a003401c0c819a142e0440c0b42c041880c030094451800c3c41074100410a440101d0802c6800038107074a0041e010041e110360b65180294000c3e0040d18084900d401958201f200a80155000380303820010032404051070b80480d0f0421a0070003c414108908850403075840c441c0449a962001011640a030036000c04248503001c3e42c03056008001d40748105082c420140686a2040b000c20b0043c420100403030016007014103000d98070306c15940d041d509c4195405064001c4d41e02140b02c0d659440c00cc0c1c85950325400d20b1034000204980714a2140c18a9100b00c4030018040b1000303190102c00c00d0400782e001810402c8c3d43c078402d07040506020403521000c0060801081780c1080e1030034030410f038101090441007810b480c15a5015031f915007a43e82401511041c100740038000008040c1d54401d0f08042c0d81315070380500060022130401144c00b99420001c2c0c000d40601505000d00c44104205c01c000003134200301b04880c0c445141c52000d900c5159818114028041d50b4440c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 744148498 1250 744147248 744147259
    0x50306040b03010f0f0f050a060503031c0b0a1203030b09010f0b0a03060f0e04150b09060409082106030c0f2b0605010801050412050a0c260c16062c0d02 67
    0x48038881845900b09008420786c4010421003941c1c0c207504a0161529031003200d1305608200300e01845007404800c0d00d00041000c42010920940e0780c80450300c00314240c2d01000007082055190403c16a06005004100400700d40382c111550400c4000300200030310344160404180009056a94180260803070402080360400d0064141c1d940c542c41817000700220703000c0312180c000405506084140e0f118400d80c034070016060007400e07941d07503080c000100144e0909440c0c00c98244210300c032550a1841c4400039224404200d00d007070404209052800644601e49440f82c0280194408151590002c032403550600700004050101410720501d210b404443c0c020b0615410100041030b80101500154043c5100340f10360010561a080708079102c3c064240440006042251030380045504101c2d080160034034400c2c2016000039000761400540d0140b400700940703400c1410000011381016084400902803400e0144403010524081f030b03040c0310030040745c051400f24802014040d48a0300981a0102c3d4003410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 744149748 1250 744148498 744148511
    0x30c0901061d130903031518020a090b0c070e090a1a0c1b0616090302030309011211041214030c0706210c0305040c0f0506120c070605181507050306040b03010f 70
    0x45036005081e540c4ca09601080c1000034240b11400c4482c2134408440d442151446048421100c2501075401510446c08001f280000411807980c0007000304081036528004098840c03a183c2030241040c4010690f01c8503422403400750740171400690b40b255180821004500302075840c80d001d95a98000c04607410440741c4200d40c00c566404000034414081c1884620710400c035400c4003c100c03201d0b8950700000707401d50814440307002154003608895480888801001c00c2e80075900e039901c280b5400c103034404841c18034180d600b101400408840680c10444040c040c5240008001300b0704e640c0c1c802e601c0307800204800f01c02d00108001f0185110401e40202000a0003051030240f0014040c14041d00e007942c03004404500060204040f0450000301e403005032981e81007030307a180025209400010311f403800c1c068007000b4001c00114030703209861080145a261040304e008a42031185810540007405900d280944240060a5007100980e680441c0844020586e070348110042800761080701c240e08113080c104003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 744150998 1250 744149748 744149779
    0xd0e060915040b0d110a0e0409030c023f07030b1506131e24030204030506102d0512010e011a0f03030403020d030522090504020906030c0901061d 64
    0x7004018810f4480c40500045e82d0172800b1a219100740720304240443c0700107400080c03604180d00300c3c50103d406030502c09a4010250040f51401c15001305c030008900070180007459641e005940080d00040e0f985559908020000146554155600016084032440b078001106056a46005240c01401610660300c40b0240c41084400e07a10601815500c0040001034a021034840c0280c3c0003114050311540e07050702d40c1070030103029440c89d00f0311040400d9002c10000c00814810004680201e04498501c40000d2505240000d4001d120300400014000c5070103e0b1070b0030344641c03400d0040d200100d680700841d40c64038003d18014007090302d0085907542004550740d00c0a00b04903210360003a9007941c038050314032401c00c01c26480380700700d000081d403100d514803102001c07900c19006420a103080343c00540340d6468020501c1351224281c1e0180056030f84505c204011402c0c03906000c6d070001c80c00c0d4001e02000b04044001000c42c0414018201003105038084c2c0b402d5a0801e412000902402a0054085418a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 744152248 1250 744150998 744151019
    0x50f031303020a0b12010614090303070c0e1b030f062704051606140a0c0c080c1518090709050d030507061d030708130e0f04140d0e06091504 62
    0x2071205a1003981c001d600007801c0c400c00c1040380c511003150664141e580e8289170b0f00344c43c0c1002c179004040301c1c1030040c44034546589041005241560140342801c1400c0c3c074000c2c100100080c01041c0100d141301020102621300c0c418415280c100d078141c00000900e80d04c00340801c00309111140303520346490144101c080c85400351103c07180074501490030b40d401d003d8900396984038608688155000292902052500d911040014003d0f060441c030f40325000a002d52201540f0348840c0e04540390380e4000c48460b60b41480d2000c82421000c100010381810080c0d0b86102c100001d5500d081356009081002c00680c03d24482d10001000d440c000304000d8824000c0c4c24004c2580c2c001100484d882450a00200e40380240e182c1c0194241d480d000c0154a08803442d580d40c6040d821064103a01440003681000c81d00102c02582580f10f800d99484040f414a4541042c90040804100e1121030750444140301c0340203644680300403240e42c1e040d5041d81c2e86400c281c01007500210484100c49048001007808600200355 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 744153498 1250 744152248 744152287
    0xf0406090c0207050306090c01210c050309072102010503040609080c0102041403030c0622060c05030601120501141212070302060601080114012f16061d060d09050f03 73
    0x307508941c1115210000c5c195030b400700b0303587c80d162175124000d08025984070381c54825007090030030901000e141092384a00e042d210558200c8020901c0030080004c4003030104558030003040b40c440c3c501c5a008098140095000c04550040d04018000000400384020303034204280745544908060381d60350306246118000c4d00140941c01c0b40480318100c0403e680740000580b8441400305002d015a92035400c0c01c9201c10032201088101c0200007289540800ca1511034841c7d0006241c49181e92480d040e00010701030207203211004800b92400005000c0300707081d540840d405c1030041d1512204148003500c41e6180c1640d2030190706d0040e40004030001007690201d40702d401603500ba00d64411030390721280740c0c055004a0802c0701c1e002030000c0b00700d020030340707480040b00040040c0d90150010038010f4412541c1040301e9840c94207011441e54000b000001d07441029021400d400d89421125011001d0016050340724031003064900030b4889101c28180300c0305010680200100701d0480e075846c8054103039036512004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 744154748 1250 744153498 744153521
    0x120306011d0a060e0d060c0801140d15050601020a1403070c050307030f060203071e090e0108151f05060a03050402030d0e090f100f0f03141603030e0f040609 69
    0x10540c028504000324429540d55441004185482c0181040c1c421540081240c3d103c0c0d92001c6146060b5003c1340c1148280c100c036460b6030361465615814512801c41c1c410007414a40e000d146281e1508012581000d500340102d21041030109164a50f940102d2070b194440f40082c00204c40710194003201a4001300a100c072500c81d8444c02c2055603140300b0107407117140921024115a041040110000c0c20f1580150b50004036030401c2521081115004034000e000004448040b403001c890601013080ca41d1019401841c0034002070501d90f0b882040c0036480c01024119a10440340311440030756281803420034102816000c0d0103280c4032082150000d000e050141c506031301901590040d80c541511075151a0300d94140904002940d44443c602105140c000030604002c485540c1400f04285641a1112000348014100042c0540c1541041c0a4031085108030211640c00320480c050404600708049084030740604041c416909003d0100d0021520340b042380f079015141c03880210b1044026482020781e80c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 744155998 1250 744154748 744154757
    0x60206150a050307030f080d050a020918011208030c0f0c0715050a14031803180319050a1b050301060927031e090b1201080613080706020a05070512030601 68
    0x14404051000700791081c028207403d5008101c00348081580202c8032003000707114034103040c81d00b0805040d120894409a034001521500007544109929040400b661945007800155001e540f41c51b420640009206900510540c40880040c2c402001d104c03d0301c9900c2014405540e8540070711012580b102c58502072506140307108103500540611810603a084108103032685207854114200c010510f8100518454400b03035480c03a41c0e104841b050010b42100441e040d90407455044501c205820801882007101c02074107a807181d200407031400a21100c4143c0c01803d00d9840300e13074202c400030012075190840d42d015801d0200010340b400b0507034000403040d00501018032004420032400e0b2500e59010341d000e0300040e10341c2c14880901640c1c105607403105c205424500d600b01d03611844581e05400082d040c0304c018030f40000400071030b8810b21501c3e912140400d403508000689554445580c00398040141c400e44c0c0c0413071820600c4d4011003c0300c113920b0f00082140e0f074004448000d06020303401180c8060015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 744157248 1250 744155998 744156031
    0x20d1203060e1003030504050904260414030f0c0906031c021f0b2b0c0e0f06180a051816080f0a0c03110609130c1d0d0624060206 57
    0x10600003c00000e0325030654855103445d00c0c09042205101f8080c2065524080402c0101009007240401c0300900c601c005103a52101d180c80c11070f40482c103070b00000c02d000c0d8110413498140180080b64082d0048000c03a0060f20715102c100100e407406c40041158003406410402d00f0301e081e03400042c45500105115aa0860744206444d0f02003500c0c8040012034010580c00c3d600640601415040c0ca21941000c40c2204420305645464040b0040340c0d1120b914861220144820364000d051b00b20341c003800503520740a0102c4c0300588280d65030402440c1e46001d565410100d140e6500005440100003100000c0712000b000c080402c603400300440c4101c0c52188120f4603030054140d00803420910712a00814080003da10f5030301c5050345405d0307501c455076000750100a030003595a10f03040100640760075894000303026098800050207800300d40c03040002200d005045c00c1d44c181d443c00361014005510803001303e10850f80e1000340c40088000744040710364508803680421003650018503180708221014019201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 744158498 1250 744157248 744157261
    0x603060a0209090f09012415020705010203030109020f041a0d0605030606010c06050a020d0c09080106050102070b040312090e0c0d05060604060807141621031103060d020d1203060e 79
    0x201d00c511048643c10140304800074034042d80514034180e12140303550000c5030008401c02554049010110f031105003020446090003400200303801c0004106a0b0f000070f149503414800040c0d81d9000510400c84420b4000518000804289007aa001480b01d43c000c030100b801d140b0a039003081c4d0481c80c1c92103c0603103400b000090a160014150b0700580301a15411b10121075903d0313030809400020b04980038940c0810000411940070702c5210007000ca80c1d036680a207681891803d6007951001e900450440d4001d501c00c0c001291b40c0030403141200c0d803142c103070251400d22010542c1d405d0b00c554401811040c0381410400100c1c00c0c0c100601214100c6901000305035500020403142d40124064903000480708400241403c2c003c240c2207130625010b07804241050b9100d00440810400140210395800d44041000c41000541c0344403003681d10079040038003005070070f41c00b980c41500004003010b11070750002d154030707046d92107801814480c142c208110252591405001601524141c07003086201301004000442 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 744159748 1250 744158498 744158501
    0x111b0d1b0e01090b150a0324080a0b25050d0b151c020412081303080325110a0210170c0703080108190b040218040506011403010c0503130c05180603060a 67
    0x24805c3d003040b400b6040070304c070000480043c405104488103045a4910b4000c00c1041c1e5a0018004c10040303000740720b86143d5142c00d61000c503003d0590a0001c1c1181001c405062900c020714007409110314000381c803507030440003c0004d0840a0102500a8029241561f41c020104020181c0300c4080c0ca56949400750303000301a0480c031a52107481340d0044080001d2000581000c010426064603031007070f490070750316a1a540b08552084d90410390207602865405240184420601d0402c0b0060500c4c0421181415002e0b44806803030300000e200e01102d20b0700c1380071180078416100c11644d01d10940300300e520b410312500c102c6900895007540400c050400000e40410b000410102c8114a0038403404044016076900c01060b0740517004036800724004101801030000c104c0954440d9005070010226540340c0401c462880c10410071450203a4102a48110103a0f00081200c0e00f12041200c107440041c0306040404004000e44c11965000b10078402c000314200a09807000e0181e035048064034600c1d21500704010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 744160998 1250 744159748 744159769
    0x50f25022107170102190305060301050f01050d0b04081905040e13020a03110402070f0302100b0901050a06200312010e1e010e090a0b16111b0d1b0e01090b 68
    0x1a040c0c2c480001030250f0f540c000b80400420007120000f50500d9034100205101448080c0000300080e0f4034001c00c021031600340603060300460745102c5068294100008503849610141010300007003003000100f0108045401200c84c0600215000076680d03491940050003a8410306c205400e4616a6020074041c5000c544070712003065005001400c00303441c50f5107c484200c0302482080d8400d5081c8440c030042451501c08045552295000d0204900c044100b0811612840c5e100750040070381a0050001c2c0c2c0b20b954901059800604005030b014401c0041c5032483d005000500f0100d000c003180e0301842c0410078070618103031400400041081e681e00040400c541c02c1600e41c0584009070b401c010030002d030b00d90060340e401000603010344050f40c0840d180c482e040d00003510b840490038915900040c840394070140050024003001d01030034566a4091340a00e0401004040070b1145080024040410158009140000c82d14080c003416046c1d98625070201c46500740314041d9018100074904680d45803410412 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 744162248 1250 744160998 744161059
    0x1403130f3009090e031611030a150507030c02120c0c0607080a091e060c0515010f08010e01050603030301091104170d09060201090209240d1101020d0f0807050f2502 72
    0x3941000c901c8000381c1b480c80c40091003a1440740c2205081901624140320032040c40f4014040c2a1150b040e200403038080340d000070511000c0500e0460b10030242c03540401c4001c0000b000620b166210304400c601383e03060001608100d5800307030000a8210401c03a00e00b02800f00b5030320ba5103a040301540e5035840030302d56a40d9020408002100601c061290718000c45450240c0c41c040d000b203a120b950240300c1c00074400b100b03821001e0010410142000341d44c070f0900815414881e0f4100911040c1400000300e5624041030003250440d640714103000c5400c115480c290380040c070501d05481021440c0301c05040e00d03440e18903074110004000200c041005401405a03194003540a0035500300741d03465245842da8041c01e01040500390880c40c8000740299a004803491916003d88030a5010b06001c000280c03134441e4208403602841443c003030480e8440d8210384040d0344500242041caa41d00b803030110404803407027841500100e18441148108203940402d400c81230842c42038800c031801851a49403105440c101d100d14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 744163498 1250 744162248 744162253
    0x9130e061806010e070503281b390503070c06180303020604061a0307180b01080108060115050d0606030c02100510140d0803161403130f3009090e 64
    0x700f00c0040c414802181e120034010000106232a1140e9484c130300c214078001f0320385184d4807194100f05800076440542c0e8080c00500b840415074800d00c03400280081c0d04420501c2136010488809445001e4580c2400501e5012007074960b07561040c90206004200d0f405400e0001da000c003d10702801c1c241e1000d8500f1380350584c00401030782c2c3e10f980e92000078258070311400c1c0710125a400f60708a2600d0401c52500a01350401c0802c5c0614035452011085855418815040101c1030f0010019002d001c50040c1c15034204000da08211391403042c05442e1031244400c00d1034014070b459000503106038035038030413221048140d09450f000c50400c15800c0c255501501e4584200000706810010282a003200d2120624068144002420b16458041160f002200d0148603282c4151203104019441440e030250071160441060640c10100c211110755503490400800c7c42c2d0321000c00c5014002d0456140b80410304000744088948240700400000901c104e82c4480841d0b404440400d09281c80c1c0240346914004400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 744164748 1250 744163498 744163501
    0x140d090e0a051f06021b030102090f0105030408070f061d06040201020c0d0302120a0905100203070b010302040207060b030d0e010e0603060d030f110312040212061b09130e061806010e 80
    0x91000b010060104404440f004240a107803007003c9654400804164014002c90745003a82c1001e003015041c007500d4441d91040040320390303ea42c2c0c500d101c0042d45082c07030425200d5070742c0c0c03801150b04d10804030090192211a8450800c100641d08080d00341040160300408050301c040f44250344003010b840007405038015001d8241c0c141810420706c40b1041c001e00c1110820b1a0b084480c240c1584803d500b000000c0a14a06104604115041c0c109000c1300344025480d011241d1502058904107003c028440c0c2e40008040301400006d0f000208140002402d40f0a08014204041c0ca0000000196404100c0380c0c0068041c17413400c00b09a92090101070464143c10f50300f690100c490340d4a001c80201804851840c0811890082002e46042030000c0300302c20040c102401040303007030700c1e180303c2e800d1255000d8404c000030041a9048880074ae003000d40c0e40c1d41c560341c4000010f0480c030300c0100004031051501114544822000440c2c038002ca1203151641c00f10500b403000c29071914401d000e8014030248510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 744165998 1250 744164748 744164761
    0x806041a0601030216060c0f0807080a181b0302040605040b0f0f01170f0105240901120209060a05130b070c06080a0b090c03090d030605031906090203060103140d090e 73
    0x1903510761051051500502e0b054402c841a20140f610b0b40c000e4550039502c190340302c111a00f00601090407002414000d00e180342c60980107090740300040c094100c2030384440d03c01c3c0c0290040600c0003007040c1e11004980d00f480d80742044040100562005912036410710100183c10304043c42803098a441c09848038818140d000f050001243c0568422410031071044e00d4010100c840b240b001d409402001c603003c0240d4982010041d018000741445140030394404a844600802e0000302c4040c4042820044120780d50b9442c040f000740a400310654210b81d0000300780034260344c044010012030b00080401c0e51411b482d2100341d0034500138900000c0c5984403000052001601030445d46500030085980450039070101d5010403020030080d103010700c910101005101261409001403100360701c05290400c02c42c2d2a040c000f83e983e0b0540d40d5104024402900b402c030a0261a030819144682c0107003c40d0300301e503942e1407da00d0303403041c0059240311805918a42c2002511881641003110340e81d03400c034110385e20b450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 744167248 1250 744165998 744166043
    0x70e01080903070c15020c04050c161a011508010b0f040b1b01110307020c24070510050702030306100f2001181118010f031b0b0f13080604 61
    0xd80109454031080c406800000c40707061011307004e440c038800046a00c822088019103000c03044998544118101820000c2000856080d0307144104480c2201c084176181d030030f03d1111702c25080140214000158008201c0c00c3c006000711245800c241e80300040c0740c1c1d032404001c010780a12080304c80041c0e400c0100304101d01d0b0305030252100c0b409a0184807169004480410b0858230b8003181101c800c6000310070000c0c0d4075010b0041c41d080107070680f6080e01507140e0382c5580f40c1c5103c211107120440b120202c1c404003808002c0010500708030f80d686041209007020180a5541d41041f10880d2040d2101000f11075110711a03180640300a0791350725104452140745c4111101551a8000c10400750368a070414000c8410010091803194065a51264916080030612100da0380c0c2111b0003154040410040040034900d44040048a4102d6150100e80e10808166035072a0300d10b81c07080c0d403c50404580d42c40d2268600c1d00614140480b80484c02ca01551a0b5941d5115075080302c001e850302c080450181c241a81c030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 744168498 1250 744167248 744167251
    0x90c09010305120f2203110105090a0e1e04050703110d03050924030a0504060b04150306020f0408061f061706130b1804110a030f030e0102070b0a030e0601090203070e0108 75
    0x1c80c0c3c081e4200810b21400c0112017042592450400c8213004003001448031541007901000d01c04e20b0818039102c404008505884020b108e0081e80310000360004030b0401403000384c00c4840000a800306102d0130103050066840c1d40d580410349900450b0302c402d002c940360050a4880c40d56040d21002d04114110007000014040d10b01003441c552030380301c240c45032440d01c000194824184081c00080a06150405504035035010a0305030040c5e2400e85005015507903d11504d0449500c4000543e45910400e200c0b00b050041c1c0d030156410b4420310051042440b042041e1400d0010f01c1c2c89001c401030355554041b510030411200045001c90003001080c100d0424009683c40e1344001d8802140c40041900881c40c401e600441644440403020140000c000740c0024000b4410f8044a64041150440d203400d4045500290020f048c003452400c1d01103d41d0080c0010002041c604e02c4064540e5800351000c1c0250581300c5121015008000010444400134420349028000c56610140d105560000640f200c420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 744169748 1250 744168498 744168517
    0x40506040f0f0f030201021b12090409021201020c0a050c0301020306090601121514030f0d080708040609060615080601110715030605090c0c06010905040201080411060c1203090c0901030512 83
    0xd003042c1e04004640e111040c0380c1e40b248a54001650b601259404244426004035442419040010b03801b03c580500810b443e081c507811600000c44040ca440002e00d00703c0310010399222540081201402c41c0030100c2c20910440c06102039524a90f10390080600302e02c02180c502c2c0e80b01d08c81c0e40100341554414441180e80c0720a40e8400a50050307251f0681c0da03c101c0c80e500840030104000594052800c0500c01c40c3d40e001d84800c0204190070040c80040d11a0900401d20000c0103401000074040c4130150304405200f07500000d040199079110184046c07451508400c0d000481c0284000c01c455511038a0170300c00c40c0c500780700500100380c100317000320181c17492100b5000100b645440f0085026954424024066041d86200c0c035130356802c00ea0f805040000591128407882e282004210241c1d0700551031a0340660301ca100011000341d0340d40001c42c640608100391001d882070260240d088190070004500900d140b10481f4003104c0900c04011401d4002d0000030910303003142d5000c4a0074240301c00a8030301d600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 744170998 1250 744169748 744169763
    0x70201050d06030c080706050c0c0103090302070e040302060103111e010302130e0907060201061707150909141005040b06090f031e011a0a060c1103010f1a0a0806040506040f 76
    0x1e141451500645885400c15500e0600200303040005680400028004140500301079080ca80c244154946600991900c28140354230740e03288004040c401d000c00b00141c2040c01c4042a9410f203070800075500c01c0e00f40401c031899121200881c02e03d00d0214a8051400356030340900e0800b01d40900110081c0d040520602d00000a20102040708262580b9041c0b00700f08101c010068946014002400d596041c0d0200322341c1400361040c060b4486020807014251101c1103070786609505040c60458518013180c1c48a0861454181c084880390014034186024254460300b20120903103a8082000b01ca2101d005030354014410003050085080120112141d603e0050a844494940c0e2040c109200d0031405203181c581d5440451001059000c1e00b06c114691007a1a8084401d0403c100500510074000000c0c02454200f0002e1203259000d4000711061106000c0031300250307110f907850414041100d101a841550300c404041303481c0e02c001485d0342c42150000020805501c5540fa4101a4981c0c0c00c2d040c6c03190f8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 744172248 1250 744170998 744171007
    0x1608100503100f1b080628061107170a0201020d051611040b090702100608190318050406060e130203070c0b0907050607080d0b0306091b01181205190b04060207020105 73
    0xe42e00f43e40d403404c0080160f01c81c0e00d134a240007810080c0b6031016078400c2440c1507180700380300010300303284103001c007501d03130b42e080c002c03c0700c52443c9416140c200182d100314240e090b4040c007541e00000105041100d24401e808981030011440002c1d1018003030032290b1641300d901200c984020620000c0c1590401601600000e446028140400c210000495484025a2100c0c3e202044040d81d445800300804010016140403044002055804c2080c4440901004002d0100d20026001042014010600100701700401a0f072800040c0c200381520030003c1c840c0c0001989e001130349045000300d91042c50360b0742d00d402c9805619514441402d00152090202d441030b0302012580d52250001032a000e8007440b48240c40b140c84002c110191411a40520b0094001c2400c0c8225481d0011340c440c00c410030061031244031651000100c5044c80c1d82038000c00152001c510000741d920308942d0a12110780a0810b0303498040c0d056081e507050b50100c010041c4940d0b0150005004035205501034500d0920501d0701d01d142 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 744173498 1250 744172248 744172271
    0x9020306132006160c061704020604060c03110601030b0601180e0429010306020d06050103140a270b09060705041503020a030609020c16050409020901170c091608100503100f 76
    0x141d103004c01c0c044400c2c01a00380f003072241c50b070000703000f4083d0070404003851014501603022030072900845c41000140039103010719104243c0070380c0c42d850520030300d0710403180b031503a490810741c030342e0001541c0341400714919811480c0211550741c1c42d4010364000034480340c8283c540c0d83d1130b440308a18014019500d040d100c00e0760482420030501d0f440c02075005810168031104040c0414040343c440d6480b2074149454090712000c2e5110790200f199010700104d90001e8100c40f41d403401c400c0225040503a80030108020386400c100310000c01780c1c0c1c0c05500c0032403c903030643d42c419105480318801c500500c0e081000c8540f12604c407500c02c6c0c0003804044580d01d008201c5944c2ca4a03460243d8100c000b004800382c00410b94020040d001080d0440104412107040c44003a40c6900410f202c440c06015490300d0001c030142c401c5060301c082014080c5800c002d07180e60070710304c3c0480240001c2e80e02c007c1c40000190300c41011988042e00d1a010100340c0340c00070047c1c2501c00c49840080000d206500300880b401d0b40302c07030b080451b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 744174748 1250 744173498 744173527
    0xc01110a030e0c06120f10080d081618032a0612050c0307091a1e030a061212030c03061505090306180d14130909020306132006 56
    0x4030052551004240c0081460445081032100f10100707005113401d01c510105107180100c41c82e08144011241c5600f0307219900f82e0900b03072a05411804c84c13481904501c04a003984841120311030032030301e0841c41181c0c2195008607040720b10080072107000c03002c890017400882c0440c1402803840303c08c103c0203125005420780c07032078000e07141c6c3e0300400118030210001707190f25500d8007900740e008040a11540c510b1600b581c02809441c442d01845c4110000c0c60b0310142d0240520301100c2000141c05108690b825940d521920241c1c400c030395030402241000c6002544c443d00789aa504960340c004601041d09200d070004800800d08142404205921100300040020200701c0c494910b108542e40d0b41d555000500c140f51801801600340010301e000c0b4035001d0030080c07009c07990315001c50b49440c040341148034041390404503000d00302e8102c90030004150005298040e81c1e0201c10400d100360140c40055aa5041c82c5290391b048035006000c90140c200d190740d09001c4400f980c1540d103401090642402051542d401e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 744175998 1250 744174748 744174757
    0x103120e0a0611010c0212180f1804140609030306131e02180105130e131509060509010c090303142701030b0a0312030506010909020d050708060303040303080c0c0111 73
    0x201203050310741c441c030702c4110a00511450040e640010000b002c40c034047c20f8154400c0e0165030003081d0045405543c95a508810281d19020050441c029803001800c000c50011040d42c0498a200c01c100c101810340c203000c02c400c1d21680556014604682c0c64205020f0060312051080b0401640c41c02c0a1003541c1174015560410303c0038420060302d40c50401749258000c01048000750501800788000581060f40d081150309a03909072807045074030389031040d000058a20b450b100800c3c1d0424900b03400d081d4141984141c01071f602411040c490b80d200e040c0001d0032101400107110004000140c103101003809406440d2210043c1750041d4a0909000e0b00030700700301c0d10480003607a4014042d90350741080da132500400114000c00c55043c2041c41c03031507031807220f6080109021010316455400082c820381c02044c08000914014600f556507451110130f0000400040b582c50f0089220304012900c1410000155810b0381e41c151510300300c03505c41da154040580c101e06105041503484001400b4882030000290 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 744177248 1250 744175998 744176009
    0x130609050a090b011a0706020f0906030c0d0507050909271203100510050403060b010513030516091509020c030c250602010c050313060906110d0518060103120e0a 71
    0x2882d02c8149000c0d20358a5040c0e01052030243d4039080520071941c10700480f62843d5004000503512580c140c0c51200354050695640da1040001c0200a07200520300d00034102408207031401c0105544184050324035000382094660008a0741c4c0004d500c69010b01ca03420800742c0e01450251144080f02443d500d0031142603d400c11044c0044107108041842102090240000f00c0d08dc0210844460300240310303000da84809049039031641c003010110790140c030450344071400300300000310110b03103d06246a4840000c4009400424080e200040c0d50300700780f00740f034103c00d201416080114034051104001e5085680341d90b1181c0420000b81900020400000001c0c48140310048078991165410641c00c1c03003d9800b04041da4100a40c80300e0080d8007a08a81c0d004840c00d5042c80c002480703040010041006c04002000f4903c1e00b000080e220ba60345010300f030000c0300c520080c0300e0780d510080340da800d070212881440100d601c428014030024018103007201c0c409006251000031003101c080080c80070855a80301c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 744178498 1250 744177248 744177251
    0x160b27060a180e010632030c040e0a060f0504020702060409020c070501020706030203160c030c0203060406020319090c030618080a050a080c0a0207031101020f030c0303071b05070302130609050a 85
    0xb103262100114500c2c600800c041806601598035100014180c860140e101608901040d0781c5810700741050801044400b803032100154032454401320031100c1c0d62003401501008034107030000611103d8280114000e4800090650078040d20301010f010103500b0046049a0140c014000450310b02d5580c40905040d40c1460010040c261814001a05106007030304a80708150040007000b031007401c00103107060704031101d00d0902d41a02850504640c40c070300702c3c8002035040c05694144024403003960040d500610502c4000c81643c0824000441101c442a17801072a4a152070310406c08600d031507005000b60307083c5620144184103503507110394040c0d12011203d000b00b9001b18011b002d9990044c009a44410000c0480d07250a550b2203001e9036409040c400104040e80c040c003809001d9109100756000c50580104490301c4105d81c030303e0309850f6001290340000098a4138450040010440302c0340e45916007290180603400d055401348455036442c0a02c24004a859582c0007034142c40c40d204d400d2003507440303440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 744179748 1250 744178498 744178517
    0xb150d0201142701180b031909080309060a0e07060206040b0c070f06060e0604020309100e100e070e0603010c050d050702010b0603070f0e1002030909091914160b27060a 74
    0x5440141100d101c001a02c00202003441b100580808030303a00710005081704092403800060010117070010f00c200410301031020090250700000042d92034007030750b17481d5800c0c042403031b426000070350701c030084e00c121001030380920040b40110301002529608001200141882d00d0010b072280800824000d5049903015940c800401508410200710f68000c0400c40c1d09503d1070900b048050350312111080024031080d0b940c1007481c1c1c1c404080040010700b440326a0180300c84c2c0c185689681d29101c4603c0750020440068000800619041c0705d249180e9005d80c54075800c000c2c10720780050041c40000c100805542d6964a08042652080c010714800e00c0141c0d50100d4000048000403c0700d59014500b502900102e1085207a464004c07007503801345407040e501c40c20260b40e00b01403103203406012001e0940c92200d00403008280600309860034000c21100e411101100f111895094502d020340c0f0420040113000d2000d030340c0d102d10104006405010340d0030031143c035000c05400190706512245804011400108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 744180998 1250 744179748 744179827
    0xa0b0106120902060d180c09271a090f0a0605060316030201090501050d090206031501140c1902061902011e0605060307030e0316050a0b150d020114 65
    0x58070601a07252414103204911895002c02c40d280035095104603010307215502c02c00c1c2d400c40e201c2035502040c0c1001c0b1400c0099500c5c401d0784028103c03021010000c180401c0110707000440d10a1f81c0080941c040000d61504022140500040303d020300074080c1130264810543c00c2020402400381c40900900000449040100406d4030f40f0780c0701c1c00c030003814454545082015030303080510802101c8003802d0059451200c2c48c0f000d0700507c0000c8009500c94008018045c901d00c1c03044100a016000303807a6035022180c0c5060000140c040d85521512540c01100c41756400e48044007a03043c56423006c2c0035542400c180762160986090300a82c1100141e40da030324044043d881c030461411121100d00410000f0a0800c000b1810a01c0b0040c0328806050b20f4800c00a162503080040f501145044000d28501c0001850540d0b11500701c2082a64005007120100d15545842c440c2c1c0c484481000703044003a07290040d0b0040d1400c40c41075000c0310081c4018410140d0740103240710080201e1610f20843c02001c0b603042c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 744182248 1250 744180998 744181007
    0xf011104050f100c060209041d01020d1107050705270f060306100e0a050c0906040b070b011d070c050f0a050705091503061302041814010e0d022d0a0b0106 68
    0x2001610452485001d582051380180c6250400c0f83c1100015a994207210042405400030328526180307494100f002411300c207010760203080e00e00051780c4140050314080750311950a00485d000500241c20001c000c00c007071b04d800411421442c107a282502c1c00c0e085071480c51500c2e038804482080500703000b80200728803031034280a019070220000c061120000d00b441244600040c000b011000210380c1c4601040d0040703200c8040e1140610000c0000b556540c41c0c550440003900410800c44150400a00210707080c4800700c0055110000c000d1b9421155550001c110b49038010740382c0946443c060030b500900f1f040001d01035506501c2c001c0c4000d0003010b00d4801400b00075100107000380901c0390550042c091f95500824190342098001070070f400320004a0001030000c201c0c64854030562007840c60000100000a48882e800183d404020072601c220404416120807004000c03c0c0147c22032178008080c040c10049900f20b059400c0a1480d003c071041d0207207403a007294100d0603550790301004010400c05034030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 744183498 1250 744182248 744182269
    0x506191416060516020d0806121204151e0e0112020d1a0402040e0f0c0418061509140409060f06031110030c0206040308091f0b0109060c020d080703020f01110405 71
    0x39100714003d07400208002d40340c0300100c0f500c030101b01f5603c0100320255504904c1c0841402e03814196884243d04482521581e070152294000e2030b040c1c00a0308422601414501080c1c13100840002c4950f14040c0d812541d07680d004550034140070440c95040d54100180c800f8000200c0301c414001503c80010145000c2200b0f41d942051080b80100004c0c08a000780000d0b41ba002004144058415140c02030388034003c0c001c6801480d0078a00e0f03010030041e0703000b581e00001c0450b9074600160780200070f009811298512280201d070740d0f4006143c0d4143c1c050400381c0c003c00b0321a000b1900001c0d251541003850058815592068070109080741003521545402c103100000000e8a040421086884c0000030351940b00051010701480b030b4100001e4840542401078000e0319480d04040d4900c1c1c6032540f030080051850403565400503680010104444e8080d0300c0881800307800800b000d07201001070b614000d65a002ca0030450860184141c0c147c004a000d000c2d0134442619507514a80b9181400e05100d0664032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 744184748 1250 744183498 744183511
    0x305030712060b0406080c160b1005040c2f010905070504060b0406021c050d09150e1518010b030a0807020f0108060f0f12031b150105061914160605 65
    0x342020800212848904980031031718542440c03115961024440071950040748402010031080310801c9003005450080380d0f1148000c2d480d08511291070741c080c0000c50740003039070301808100d0888882c100000581c80000e00c40380f65400c1200c225010411403800c0d5440f03110105c42c540e20a0a041c0000c4c40e1a00811010300950111107060614100c402903a40c40350100c141d80a0701c0d25081510001d02c10022142d0b244403481c03060029a5042c078203c0d103a40c8582c500091428a05012101c40910101300c1701e54551030f42813040082e0311400110049141c440155086965036007510604c2a14144460503100740074210041d2034803000c2c01804001003214400d1410440d10208000507941c0e090180080040705582000700042100d01140080101da81d00c00700741e1202140e442103091110079803546890100040c0c540280602c400024203180038000c00d98400313000e01443e000703003943d0145c6041202042c50070119600000d0796a14195100903500188442205900310034040c05014440c0c1041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 744185998 1250 744184748 744184751
    0x60f050f01080c09060d0207081b0705152107020303070e032107020f040513110904020904080706060b04060c2a120510051510020304030312021c090305030712 70
    0x110340000003010b00000030030910598101140004054aa240a0340c01c4100c2440e811503a941c450b050000305074005c800c1520210352400c0c0000c01d0141c0c041880b400b00c0f04068010443c60746c0084842d0502d030040744008107034090b00140c0031300101240d40494081e03809500610780da130803c9440100000407040609010764022460710031350007400b948510401018090680d02c615540c800500d050340d0000107036500c9410001800b02d100300700240c190140d881050030740285000701d014801c100c2421036004c1d500488603c005808503410400800d00c05100301d00000d040c1d5100c01c0d0050180d00203404c100001998400d00004000160701c545a03941580c00b5883d040f0b400e107901024189410303001300e01c0695242003107041046401c00101c0340da80c507075100c01c0c0300d24034013040c40036400d003518890548203804d40564510310900100480d4242c90701a503410540312030041c0b800c07010390b01068080d002006071400309068050107101d8040c5192099035829520b0400d0350000380500803d82e180701c00326 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 744187248 1250 744185998 744186019
    0x9031202030c120f07051605010e0301090b130201090f1d0708060d02061b011103042616020a150906080c21090a0b15130b0303031b040b0a03060f05 65
    0x304005110315468040d442c071a07654070313100351403044540990340004081c5e106804042c200d81501d00e03003000c01d4074000e0366848450b41c040410982641d4110001910066060011410341d111600e492082c403801810700d0070104e80d494a580b10440e0b80b5038051007641d0b1245100e880040d40412403070b5041810307490714140f20b08102e00058407100c0c00c0074000344960f8001880f034450103800200045d0030078106008114882c004000820075510880b01103034181460165101840420405003280300f1000d00d445e82400031480c04181208000c2000b40d80c0404c1c1140001f0740d50b8503020381c980170b141846d52032847c214503091014000030405000c00c0c90007141880348140d000e070741c4035100c0c0d800041c04990700440d031243c2000a01b094170b418005407400e40d1988c2040540f03140308038a005107400a40d80929800d01c1134a5900494103030442655040e0401c20100381000c0709070308000d5644016080c03451805540d0300241005901c003180000200340c50380410003042104503a2807004002c25160259035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 744188498 1250 744187248 744187267
    0x303020c0c0105072307091a0f010207030c030605090a0b010308070308060306071202070c150903050d03110d05070e060a0e0102210a120902060a050712110601181b0903120203 77
    0xba545c0d104078a106490300e2041003000d0030003081810010045102c0c2005244a0164180c10031050042100e006500c14000c0240303a5200180a8080725082503001d20142d09550341c810240c10003814801d80c920454441d080403030a04d515440c02540300d81d040603078034003542c5005003014000501c07280c13007a000001044809074001c4003000b070050400313400690350480d9180050255a00d50440c8411102c2c0310303021444590480000c0c0700362801103040303441204e001413040781921005580303441160700520280340300c441c1c69008590071540e075051080c40c2040007400301c0c903590000903c07000022110310701d5031071a58061265407140d683c2032540d0300c40d000000f0030030a92449201c00040401803068031024a01003540d03c001310340d60780102855502d207000780d8010802e4002000980c1d00b4440c5203101c0c920740f4010b240081c075440310300d8060703e066031070003509030840403041104a40007910b5000300b5111070714440b014105860144c88041c81c09085041804450690143c11011340d8401c1100050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 744189748 1250 744188498 744188513
    0x2030c04060e04050106050d0b06070f05060108100510060f050903010507050310080a08070f17040305030d06080303040c0e0703020706020d050108190b0a0b010e130b01020d0c031215080a0303020c0c010507 90
    0x300251a030302c000c903a4441e05002b10f481c230b21506c0006015403109514060403c4408200d260403505103904840c01e0340d4100090400316001511090fa41944070b00080003224042e506c001007140d00703401c1c07160800d06000082400d54204803013040c006903002040200c00840f010080b00035001e850300401d01c0310420b59501102e882803080140c4a2404030101034200440c108a024503607003c0c440300c80c0c0f903a5403860010b03540d0700070510f003640f01401c02030041180f500000a82e88615040b42c99003800e03a02c1c0405590615002800c01410107408001c484042481030008100002280b4400611903252021440c1400c000c05601c04c07007024003003000c0b00400c000003080c0350886a140c4002856500160059900c0720318a8441500072964000d5260245030b1640301c038004400c2a025900c200c80c00b51001c82c0c445842c81c8004000c40c0640e40725801c0308070306910010f460302100d1a90001540c03103492003032401e1441030044002075000160305081500c2840341207007504c0c080c00c0680c100025591b40300b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 744190998 1250 744189748 744189757
    0xb100302181908070b0d1a06030708070504050d0c1410050f032a070b06062d040f080304031509020604050d020f12160f0e070809010605030102030c04060e0405010605 73
    0x521500309019041001c190b0082c4100080c0300d0322003210081c960b1001608501c0d0000b010070b428091605090840340007600a03114101c080080c035043c0340d540c408c0801d6511a0003c0d10140800100740004a00d40d1203407400040707614016500d20048501d0007026103511000c0111270703805041f05035140c41c11250081c081d1070342c014440c4035558407592605048004d0140d2003400c10b0440300d10301a20540540745200400030a4050140030b14141e4420050200520529106d21256454048401c020300d0681c00182c0071100c0358848140360030b680d101400780036500e83c0c22805840c1c00000f0200b00b0416407503034a1801c1800c0d1042032081001c10307000503999000303e12410b8003030b0440c80055011940c560552003d002c200401c0c00000c400031441d0a941d5000c0408198920100e4002c0403c0c040500004401166000c6c1241d080d2580d810204588641016020724510341d01c807400400c05681c280055440b60000b4580580c5680c0351160040111440654150285190600502840fa0303c4003c44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 744192248 1250 744190998 744191047
    0x408030702010f0c02100528050a0c06060308030108150117151e10060f031a0f061204060b040b0d05070b030711060109020903060f1608180f010b100302 67
    0x20b06054010f00c809540e4551481c4d402036001581400403003000b60000d01170070400301319076600743d0030945a013986d421207003241c0310150100ea01840840c100c0c0e40b1422110180b14407880000c501c0c1c6943e6070b11021190000c0c2c22400d5150010840000f4840c41041100c0c01060f4072001200c12041458281e43c44d1070a0f20340d052a204020700009541c0710b0003203506803c4040b84090148140f07011000004400d00314056000064140310100200320b00c607020b84504403803448009403008403028100310802091071000c3e50401c409000d800e91b0b65190b080c00b41d1290307009150220b00103003433074108800c95441070840340c45100380e81005400f14000040c0b940545502c0210960b494960707140c01d41780c500d140c008106062160b2030020507104056009050301003415002c0b0343c0d05440d1a500104042e1301126851064a00d02d440c036003a00307110b0780680ea04a1482a042042e0803001c075445402d03d02a942001020ba44404898220f03081920a100000c5002e00c3e0850030700004201ea824000c01e01d9818 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 744193498 1250 744192248 744192257
    0x3080603070e0402062a010902040c02010209130209040e0f2407020303150103061206060819080d050c0d0c020a110108071d03120309240411011209020a1712040803070201 75
    0x1491940388441a60709113803812050b0306d00364004508241c6020b0a00d4910880c060341c1000304220440d8014020380d1001140201801064800e1001030300084d0060806a607102d510765407048040f50b0180501440d031034a210282c42c50304d54007420b08031a04500c1551140b821403460411080d180d0100503690040003e0205030101e0315000700480c043e0055030031480441560500300c904103e0a60b000c003044a524105850015507080c020440311b00d00b1100c050010b860401c80d110304074809500040c4d004e003403840d100d814246400e48590468038ac0c0030400703000da07114030080000c1c020400d00503480d4641c01d20f090002c03032404000c01087c0900148440c8214420600e40c002e650741c00344030203c40301000782c141684070315116040c10341c1d40d02802800040d44c41541c0301d0b01c40891f81c074080720b442590402074415201000b0401152514199000d081c0201d07580d03500300005030f42d0010110b004043e1302050054410140e54071505005450250041421080000f0003d0b08408000d41e50300d1602400e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 744194748 1250 744193498 744193507
    0x9160b09090402030705062208241003060906090501200412050f24130b13020607022e08011202240d090c050603040b01090b0f1c03080603070e040206 66
    0x31038500760003601b0155000102040d28003841300706000011740b0071424010045203075a01e011203600d8030f9541c107480072003030700c000c4458900e0f0745400d04041e0082c1c1c0d207080d03844103190b403a16103d08481c21010201c0c1d000b5250b4584c0030620909001d030300420711743c10708640e160100b0801e1084140c42139200e07414441b2000204802400000c2c0100300000e050b542c166600c4000c0d00d000e603010701444040048491801070049081350000460940703220b0780c0040c400c140c0d03460f1003103601d04422140c0012a0321003002c0004030300503102c1040300c190311070240d41205910b02290080c4154140001c0c0c560382041480401044010070b407004542c9003903015507040164100c024030111090140e95184803246800190400a140e40ba5101481c110b015120841c0c1990300c038000c1200703a1100380c0e030140c1004d40c1d040041c40f02403500c1d8020101e10340018800c0c1014404a03000c00c42000c180e1908a03841141400460180b603082950a0303840710003140585051402c20604c068191006000a80642c0c000b06 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 744195998 1250 744194748 744194753
    0x1d01120c090b13031209120602031302190303081503030f030a3c020c0607210c05091801180e10060311030d030204150c080d0203040b09160b090904 65
    0x4141c000541400d41c041d59507042c884244020850682c8412035109585484414190f841002c002e402e445202d2806041220306032030b41000394202402020714016840403c80044e038811061022001c044000c09000d0f500e10304001c1c1200034010f0003882480038450442c84580d80c080101d40d142600314903030644035150107041a0081664001c50320001d40011071180038810354103800c0c0c10380c03410001d0410042100b2240d010070380c011492205501e41c400c0f008103e116018a90351241d0717038040e03146814212108050b41060701c0d041d445410200d1400128902a03090102004584140422002ea00c0354584015a50220b0800500103c0b00d40d540104010003d814021030403c42c98800c006e010705502c0b8100a840300302081d1946109114480000c12030b28024000c1e1001c859401000c040084079011054641c0c40c241041262200300030850a5042c1c1e0451000e540258000c2a45114514020130a01e00d481030401c4890948008000204041900007080341c00c0800180ca20203040d4880d071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 744197248 1250 744195998 744196007
    0x608030c0a0b0a06090e0a060f02160f022d030106080c06030c0a05160b1e040321020c01050c071a0c0406030e10061502010b010c050d030c0210060801020405011d01120c 74
    0x30742002d882c4900382908100106c10004e002250140900810003208198904007422407080c002407041c0310030340005400104001405032422103002500180301c60500c0302400b2100900e040500d00e26032842d403c00c181d01d0609101c0c402c00341000300c00030f20010300c03418005052400018420300c90b0319000103000f80301c50b202d0015035002600c05442d2100c0c8514a04d88000c1041048884a4000c1d01156070728031400c15980d1011700490f01a03c40006840034400d1a1586110b5150311804040d0200007219050800f40300311886800d12040780354039103101c0c4c540354002801c9145982da804048109004455004a041700c088a466040010b249949800c4c00c50a105007000c248800c10b02c1d0620014069058500c43c40c20340445500810440e1b0550006641b4038a10360001f901c80e0740b104240035915802075100614038003403401120030220040162000341c80c200c1e0810401c1c1d9402060800181d40c20203407074481c410010b98202040448580000d044601c2d00c01003880d030989803644500d603030303014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 744198498 1250 744197248 744197261
    0xf150b21070212071214090a0611011116020117040b0c0a030603061a1314010b0a020708061003030305160503071d04061d060d2102011d0609010608030c0a0b0a 70
    0x140b4152900d584140c14101140b0101d20941750208482ca60b5101050f01d80780d007100c2da2071f032000704442405428001708591210385810032400640d03070760102524001c100310241044001003260303000112514400104503540650407454808818010b200014103611502d40d8801c0001501325200c4815035011009882180e1019046a00d41100e180304400380354114550030806860710901e200c0e80c414a902101c0743d610000001e6032040006110b0b40c1e420100800300d100e20340c0b0481d1100f58642101504100d8180c42c0710425107031400040082607054000d2552001c107207294440d0182507408040d20600c0000e00040801400d01c4174170110324011401400c1c0c528000d4810000140c50785844514240c03d20b860740d40c0342c410400062072600e071043c3e690320683d900902c40c0413901840d802a00c82170300410401001d5540310390b00c01284070041d0807807601c0322025100820701d5041004c0601e0841d000c603041030300c0b2034204000e0308103800000107010500540c083c0c04503210780e0310f002411000b07006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 744199748 1250 744198498 744198523
    0x111060f040f24060f05010f0302030627010e0f04031407020a0f060e040e0f150c070b151c02150a05190f0228080a0201020705010f150b210702 63
    0x7403104603e4000c8628081104110356030100802c009500c48100c09905503441c440d150000740115405034109109070065600f144000e0b01c021090200c1c000d4511501724103039000800154128010031100c05000c0c6825000b007040303841401c440c141501c005001d0141d03048003280b2410002608821501d81031500001000d996114416140d203c0b4002400c1020341080c991046041c405e1000e600074021405031908450707030004000003003121403550b100700d1004048000c3c18200b88140404909504500392191909003241080c090051040090f40070600c1c04031791704c0c400b200b2000300060300d03100d075500c01d4018404282925583c0140003101c203803050110054928400e013003503103449900842400720444042d003d45000e0380603006020311001c040124548101000d203048000318480c0c0005040d5651184000762602109864039401d45c1c40400010400703540d504501d013550700312810100068050b4a0b60a49001c07030722a1444105150b4211540318982c00c80042071006000700540310b603042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 744200998 1250 744199748 744199763
    0x71b020d0201210e07060201020c100e03040e040f06141e0a0902030f150c191214180601080307030503062803030c1502030405190302010b0604120c050111060f040f 72
    0x40b03808520084c0c415008241803e10541201040744c1c1d0040c000e40344002244002014030b8242c8040200240c18600d0b000c0c01b15002c100310200301c0c0c00015100d54822401801c520744156841d1030000d00f112098148018042071304010302255000ca4041c4003504044014005425110303d01002c00500708210000e40c5882200390081c5480800302d400f0b800e2484241c180c00041d50b401881e450f09101d0001c040c10305100000880303604038040c5020703042c2e40d5520000001c03100245851041000c000b030310494121038000c076804203d404100220b60161850302c001c0c50a0048a64002d402c81c00050842c520402c0c4444a10004034031a20404481c07007144504681c845940e8203014104034101801920002d624840306d88030040c880c0200c9010b19030000041080c1c0395001d00c4008003000c1104101d003195241c108690903a41d444015001500e04d00700c1a044400403480c140203500d29552000781442003442030201015404540f25600c0820b011403c00c00303035070350701d00b40e03c0100c0c4400b0010440c3c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 744202248 1250 744200998 744201047
    0x1d0415090e100f0501121704260d0306050f01121107030c03030f0903270b18030714060f0f0c0316020f031c0f0c0812040308071b020d0201 61
    0x1c0d0000180650282a07035101081041990304002007a5a000d01402c070300011803101140000b0541c0301c00c0128505109261801d280d103030a00b00c04c4c59400d80144001c0003800007000310021600b44502030600c1040d0501300815403401c40454000c80030400440d05015007100034003081502038000b011b81d401d150190558070000c1d8540a0615034542d81c090300000d01d0406803501a45003403040360a95900740e160742480074050f8042940c19003a41034220ba1061002c5800942c001414001d40305010700c801c030040c502c421420505240c4181d40d4000c1100103e400e100c0c0d50315440b00700440348040c0c0c016920954038031040c01061094821005200c0c554840011850480700307075920000fa00503c00c030b03480132004424008040d900d44498844c001c00115981207599442d0040c048a80b002041e07003031580329059240c8880c6c074160405411503d031100d610040204259114000710382c0310038103003029000e090b4011041c0c14030004601340240951a04c03107000055a00a4280e41a080c2c914040803404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 744203498 1250 744202248 744202271
    0x5040b0d090b1006020c060a020a06060b03240d020415122102150a0c1704060603031719330503010b0f03060a0510030f050c09071d041509 61
    0x8100701e01c0191210114180443c1d01803844103e500e00321100342c0d005010400c452001c0114541c0842c600e40e01707502c80c070302c1031a00040803030142d40c3c0201f0941c081d503a1a40703800c00300a6540c0790009502c04d0300b110f4181105051390385502c02e06c030102c3c0d01501d000810854982d08030b40460080c0d0080d44000408000702010407a1400341c0348020340b0140040110000d13010010307640c83c603c80185480d003c16500000391030b0300c80d5520241c1108060300c1c04ea81006030728024201d040b002541c0548010707480e400d0502c241500800081d4020044400350030080c94618450904081e4500590380400c2c3c4900c0d11400c00122a01399076101110440058010001001d4655030781002d480ba0070f02a50030030140e9100d82c0341a405c4001606030240282000382c0c1c5800c1040700130a00180b00704c5102a1411010010614000e1807011480c0700c0c90081810310300c01c80400180c0e01c0f005005d04100461030048444510b0100c0c0d07020100e5005580c081515082c0900316402d001042e08105402c0f0b1500c40310600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 744204748 1250 744203498 744203501
    0x1002250203010e1f1505210102041a0c0706170712060e0903120106020718180f050307030801140d080a021f0c030b1e0105030c0c010623101b020105040b0d 68
    0x184114a55400c0041d419150f40d85000420944940303a8855081d1508a0710034599a442c1004c07d03144900045c0b51548840c04203641c402c00207034071106650701140f0450900b07401c10025000d00304605003c40c031144101044002204010440004c100368a254484800415001000a028400c01d48402c51900e4040681d44e034200c4800841c3c452095000011520f001250880c15034000c0c0758980d0300194020714240140000c2907035046e80c1d07240000e070180440c54428a800300f8511843c041e5544a0850038000d003c0b54061304201c4a03c004038042440c1c0d6910a4a0343c286182c2c000c8846441d0448018183d0802c200403486406905015415941c034000d141e0140502e07040c543c41c10000295401e05000016510140002a28185101c1061158050340103558420701800d0b11f82d1400310b000034403602355442644400700200320320602c4080d012100c420002c00020940d00920b68410034980113142c40c0c480040c42b00040d070101800d00940e4422801c8502800941e403045950b0865194a2030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 744205998 1250 744204748 744204793
    0x3010e25080d17070e012a06061d07030b03030a110f06010b04180605030307081c090f02210a110f06071401110c0c1017040f0201021002250203010e 65
    0xf1104203001e000034071190042050101c0088107175101c03025010886103080958405040c200101c581840c600d900146080c081c410203450091400c00384000018000000440c2c060884401c0c03500f40b0200030495240001a01c101109030f1801380d90f04201c01d03c1113170401d01c8950780e00b41c05003c0c1400105c0c1f8402c1e00c1c002003040703440c950400d01e40101005443c1c4210f550742e0040562507002044040302103000d0b600541250b541c504100300200e450f40c41980e088a0106800311845a004800e107400c3d0301d440e4110124084225551700c1414a06900580c1c0341c8903812001001c031481c4c1e504203012070f1200602030b44d00c4840a840d0315541c2c200c0d0708054a4192a1a603880055030a10002020360080507003a038041c003031080f004000e0140903070200081e01081010b00020800c0302890340040003460800c00380a1b60050307010301c0030900b4600009041120b009070300c2a5039801040309040b880c04007601d00219414440c4a404140f000d440020701410728100340d1882441200313200c6421907050310810 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 744207248 1250 744205998 744206027
    0x4030221060603070311060d1d0d141204060e210705070506070201050d1a040606030c0e0111030703110a050d1707080403050409200a180503010e25080d 67
    0x140d9442c1e880408055aa0b1410b020050070003820110009050800b08050104400390440110314207081c40c84064450310000703072600c0e2a070f120340001d00740745400100600101d5038000140b4907040c0f4010103070149e003070050300007408c6523520f20310410511011300566904c0c4442e8146103403503492104006030f00fa0000f0380e0644003409000400262032a0003002c80e42080c0d030684510341801071181c0f4242c014100004120400f41500c02c0404899403180b0811015000a803070000b80400d503c0c0000302614194180c40303041c4000b202030819642c4001040e50140359141c509000060a000341361801c0c540c00e880000d02a10030030b143c1071003c68110a607610724821482503c0d9950b81e070480100c407825403e5401401080b0704100034031801407107822420142d0109210386140d070000b44d000c254182e02602403080040c0184680e5a100780032400401c0040c40c01710002c5c031101c3c03014040d16440e5142c8041c1402c2d107016070000e4a9000c54410102c90007004084e01340c4568002001000c0c0104d402c90845 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 744208498 1250 744207248 744207253
    0x40f060f1404172b0c0c030c0b0a0f02010c0207210206031e160503011203051b01050a0b03070506040b031b0406020705040b040c08041104060e011206060501110c1504030221 76
    0x401602400b880e078145210030075402c071140b00c0301d0130304002d44620341c20050a43e4111000540880854000081040144680b110051356241d0b02c1c0002412441031000302030859040c81c0f10380c80039075400540401074607107506030034422511a0302d809400c07458a04000350800d2000c810400700315920403441c1c11038071a021441080c0d5071040001c4c1700c070840740542c010106d001400103201482c0d1060000c1c544905ca4244140707808074122001d40c50440810040d04a691108208007401009008800c0e11410a900070980c241c202800209540550700401101000205c00510313580b800220440c00d03d4545403440341d8a644038074009403100010300a0a01640c105000845181028810100003070082e94032070b4459140d561750b080c3e810440900070740c0d100303484503400706081828001c45402040700c0d001c40090ba00807850100c0c26543c0d0340c0d214905002e190203a035028003c01040e4525554801c42c1c82c6550918414403e03006070203a82c101940000031400c10841000116101d01c0d401400c5004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 744209748 1250 744208498 744208513
    0xe190f140108120304080306061b06090f07060c1403130305070e06090903070b060f270702060c0f0c01090c080a060509010c020c0607020406091113080102040f060f140417 75
    0x80e9203450a143c040094502000001d0102d01c4d040003641e0007000040406140002d652030700081c3c04034590541002d60000070510407103030000c0015542e42c280480c00703408503600e440340c098016031a881001c0d20504c100359140a030034805004844803074540c01d0b40f0000103a104d0620564070304a41c000c1c040f2003695100481c0c41d03460a00300c901d10489185004502e4880e19981d401d08407070014080340d42243c410000401c0d243d507400d83e40060101045c00a00342503440c1810780d60b08003005400300c019908014180300d030810101d411903122541074440c882d6116064032105005145549010b1301301715603003201051540c404682181c881d800f0301c209010b503454004a040c200d40c1d10b503503c280568028000e0881508180000e00341407400103000142403580d6460100a844401403079640401000900c0031140040c13a000101401c038030f00086041c10300344880603003413030000c3c0114014800d0342e0409081d40e510031211410041413856299807942d0303540e400040501980022000140204c6e00e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 744210998 1250 744209748 744209759
    0x2205031f111303060e121c061203020304030212030f0301030b01091a0a060f030b0d03020601030201020613020d031407060c020c01030f020c0a02041806111801020a020102070e190f1401 81
    0x2002d8404501081c40100181071842d03070380000401e0310070a400014040c9210390034240320b041c07020700740c0150142c840d00d4206040142860031140c40d0b030400354000648843ca440440d074000155400d50b40c0c1940e22030000e10183e00d0091941c020702141034000303c0000b002008210140480034100d41301400c5c244a40300d401070185015142c01c201c1142c1000350b43c0d40c1008024802c4000165040945c01c00142052001006c1280340c1900e45060700540c1c4100c004004551707040082c03030f03031007210001c0c884400c3d040d50780007500098143c0c6016080100382100c88031a001c8440c220f403030565108130304001c1e44514240c040d444050f90720410b0b0200c1d141004950700d018560003180c3d001d00710007010300f6207115507508100007000090b1495410040c4c407070078032002680501c1030032604484c800b43c0a4032404c1402c0c10000c03004861000d82d0454014011040043c0d80005010082c2d80703208206d01f01603a2005040712060f00481d00c1d03007840354204095101018095800308041042c401000e6842d6a00c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 744212248 1250 744210998 744211031
    0x20102071a040b070f030e25060516080703032a0809070b03130507080706031a040903021b011e080108060903040e04030e041103190f0b062205031f 65
    0xb290302070001c2100e18005440d02d48956504103c441140c10b0000e2101488441d00d80b8000079402809804101036000040d2942d805032104000d007000e1a00610780b45803201e0380074481210440041403e01c0210382642058040d03084007001030300a414200d01c5a032400e902010158403001c60b14046800d00d404078100b03510215045d000d4550307401259280d07031110f030b490010400e140c400c242d50600a01c04e001c1207458090161100400080e500820b0425070a2100c21070302c4441c505030792142d8544500140080d402181c000c40c8120030000fa444124440801641d014020300712107510401032001100f04140c020700b0305c41c141e9000c40111103050307840407000c554920070307030081d01c41c0c03040d41000042c006407213114030148040b0003070004103094940d0b41544c082c503001075071000800440c0d0403103216081107611074981c4620078400240845201e41c00070030141d120341c0070403203903244041c00700c0ca0000e6140c140320b00c02800060200e584216054a000e10503500c880c1105108508154088042c20080b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 744213498 1250 744212248 744212251
    0x70b060405090a260703110d0c0b0a05060d061104032a0302060304060f05010b0702041518020f040f060816020a0308180c030a03030221041a13060903020102071a 71
    0x10780004100c5072035140c4419031394841d52079042c1c040400000c0318210f402401d41c06000c507140720307031940344c900c017903d01d00d19080030101c0d18980301b0001c00c0e0194401040a014189401800050000038180c4586000c40d00c070203016100545480d00b01140540c41c1e240d0780005100b200e0003001c804116a98031690340d05205000c0d01d400209038000c40c1d05002601d00b42e001103801500c140c00015010800140ba00c09860003640b10148a02002c140141507041a00402d039015180000e803030405030a0040c0c030071011034441e0a41d0f0341680d0102d07490000c66005011200600844203118035141c0d0303251401404090100c990211001d0180700d01c4d101c031070000402e60340680d40f40d00c60307013090b50741c6002400e0000444042a1000d11503540300540d552014000038902038029600036980358139640005101d41d118408521041481e20200f10100d601c00c55808010221180c070000c8a859030402000004c84941c0040c000c40d103071038551410541c0541c02895202c1c070903040b100390080d01248003261b0240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 744214748 1250 744213498 744213511
    0x5090306070e0319030f09090e060a0e010e010218010324090908160c030314040501020a1202010207051515040c0f080603190605090114041e030512090102070b060405 73
    0x1050303001ca80500e0190741540050358026089038103024090401249030b03074200c03d0941c0800c05201c86210039641c01011540507000450051100c596003a10325599a00004e00344a1800c1d42d490482420203020b40002800b6884000259150140a411510807080010440380445d2419568824401480411045031402031312a101080c0c50030706558060090114105e4140000704421078034030190519800416002d003418101041c25460701600221181c4d070555000c4a007800104106c0ea4001102070035590f1211154445201001042e0b01a020301a001802400760203041c68810160303450123449280c100c42d0b0a881285040240011074a0f405080400200100754010b0010300078103650f904410080c0071a1001001800a4900009606001c40d40c80d0384271424000354a40074003901c010402041d40001450600b95100038500d078680700321b003a1041a0803204d0042c10300a0098407101104d05c00b52904510307100d0b500500035882072004079120910500030030070f1420141f181d0b600c00c07030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 744215998 1250 744214748 744214753
    0x40b04420902030a060504030c0206040303080405010b01180b0d0e010c0f030f18060e070308040b280203090d03090f09090b0703092004091a180606090c09061902031801050903 77
    0x20382d07107446010340f06c018070903401e0065407160800103848443c020801103010703588001c0389081604d000b60964840d82502410050422a80c5d2a00d42c181c0c6c283d10201c90224403443c1d07130341603407100a00151504414420f80c07540307408100c40a03990044205071018000341d504003c0246120030040440780b01c05050124084c006481c100000d20683c0400440d071921812103902c00d03925615240316030b000c0e03000b07008500c0340864003d500c1900030414840710100550a0b40309101e841c07a0096481c09070011041c07044d030b40f900305074040c1070007000c4160281680201d043c0e1a207840794840b1010388100c1c00c0c100c40c502050800500b8441c40f901c512040513501000408111800305107580d8240700c1c4d001566407042c0c2d18010038000401a142025a001070319048074040c0c40c04502010161012550194030303500800f00304002ca80c2c441608503440040449641c2d200d05081000c621035000d002c00c0e228480d0806444030444607000409000880e5040038821691145040112244d0051b00455501903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 744217248 1250 744215998 744216013
    0x313050901090e0c210f012f0a0c02061209060105090106030b090727261f0c0c080a08160509060706020f070c090b04050106030207030206040b0442090203 68
    0x14503001c100320210461000e5100314030450f20b0f2078181072000203880141980c0d076550580c0c145100d100103d02c82d21032300e00042d2401221403081ca02e207910410311201d00b01302c0c2640b185011542d0344d00a07503100c0110314040058518044400d607a0760a020b0040718420b016800001403035510034040c003400030307401429601244d102e01c1000c1e45c0148a58031385400198071a203240807603d450203007940051031404180828a81d1903e200d40c03c008035008010090740000495051504a0440e860117590300b503140010107080c1d061040f2140c00c50307400008c2c070150002485100300b550103903199000e0448101c2a1040d4450307000c042e607880c4a00c40400307400140502c004008180564040c00e09801c0c0c0620fa03c1c5008413a40d5004114030080e04941c800d5595000004d400782468032a0701d014103800d00f011031800c0e4503600d010b503541724010002043d074418180001d08001c084851101d0007881103807032140001200070f010303001c111015203c0e50400c244842d03001c0d440e1178074001e801000340c002c0c0c042c1c03010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 744218498 1250 744217248 744217273
    0x1a0f0106031d1b04061502011b08070207062304080f010506032d1006030804061101020406140310180605030f191211030a0e090a05010b03270313050901090e 69
    0x5501c04049004d5000c1e0f96510300003010501c5090040510415034000a042000200f44030740031017210070b010080229202c10824419000036644007a50714a040050708509440b800c5e8130034424070700740c804000c0700102d400100e5030f0000810300400d2820344002d21180e61513a0a16640f065031421401c059002c4004900c0c0b55602002c4c44116500711005441412032103221001c00e44456510848005100181c10820f66900c1102f11400903da1402940380a1800c14001d00e50341c080c0954000fa400d000011414015040301c0807802000c0c0180801814149048500014102482100e001e4050841d207804405008901c0002240d407002000749081c00d981c8640d11020b148403018405d0283c0014012040a000c10151142c03000325510b0140c0301c0c10100901c0706d4444068840384c6120300300b10040c0038a03240b01d020741c0d41c07000c0e084507034401004804404040f07010030031000124074000024140d5213040174841d400c0a942c03003075a910200d40d07680ca010b64200c03450131520707800079040842968903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 744219748 1250 744218498 744218533
    0x309030a06140f31020a060c0201020609150402040c121a030709091e0c03051207140c0d030e1302040e060f0105070f020d08070203101d0c090604091a0f0106031d 71
    0x1002400704014040e400c1056006c56003040c01d42d04254080740408400200b150703810042d20340c2c800105406882099000714516010040c080c100910603070b1a010b0002000b0310034031011401031920881030000c689806101c0c000e01280c00c582500a000d400804542a10b1900554590f19400310b90143c03140001e141d00000180110000c807400c03141082c000002ca41d04018580350380e1181080c0554840d464a4016059406c80c0c100322019040300d248100300f59640d8400701005a01414104042c100201c00150441511218541d450b440404c0101d6990440030f0304a1140406991302014a80c80e180199114000d41a008000340c011502020050034032108134403038035101e00841820710303540344d00090400010302103c001e429030320f80e0307800c070510400c0351085480d00703074407020700070304d07120400403414180c0000c04c041c0c00380c1c0d140c1100501308103807038114000d034001d900c04003807003410b01780d268810550b004c0c440c9100090921583d4000c1d8116540010b1a080480c0005e21002120b06480c41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 744220998 1250 744219748 744219811
    0x61e030f02040908040302151207140a030c02160314010b042c010b090c03071409240c12040f050f100c03020f06070201060e0c07080901050c0309030a06140f 69
    0x207404c150f0600c0000b005803111030f140344400c814402d81300d4850340c071412542c00051009004604022400e1660745513041600d0454041c82d001d850081540c0001c0c00c400e910f40212101c0303500d00b01600010002c2400103008201c41c1c20304090000b031080300f48600400003640c00c8113640c40303425059025040c0b030103030b03042c08458003291a51300041a0074800d0800905050003c48040c00c0b60b2900100700550b40d075201152484541102032224188044907001c100b40c1c039520001c9009400c881d41801800c0380f9150280d0b40c210800780304070b940250600602d04d21036009172040c0d001c5070b0040b4802103801d142c44374051400c01e00c0540500c0045004c0c480881d40452404811380540c081c0c0e1100e2910500d09001951155045030000309006140080c3c41c41c410000a020f101500c2040c0407100003c0c9101d000c03600b20140c2480c10545850030070007800d085105010445a1500c40d1b1840e210401109400148019648500f040c203165200d0b003801d00303025802c40b080760444007000317040789101e40f8103480c90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 744222248 1250 744220998 744221003
    0x9020a020c130f09140633030a0f03090f09020a02120d180b060112141807090501060f081303020d050a050417010902040c0f0801060e010302120703061e030f020409 72
    0x200303e40c0c0d02501203800f20707022100180c0f01100076400c0411403030420442c2d00c3d0000c15a0810050310a031003148641402d801c5004080455405c4243c0b440c0c5075130820140305204d0f00300c1d5a141d4a0705091802038601040351240ca072038601100c0002800310428800c0e2034240700190068819000c070324a400e400d660100c1204900d16a45000c0b11104c03101803555801c102d8806c400c030007000e04046001400c00d02692022012003814190380003e08449025210741218080d5403a4000c1d01004030414207041a58000034100c61500c800054050303402040040c440c1d065488503001038881c12041c0c00201542c10000d405a800118080038480c818001403c980360355142c958103054480700d8054208810405642c05603466150b0b8105614052041d00743d07409844c14482c20418500c034019090080511440b41804000103400c00241d0103a0100c0e1051030900e0b81f00c05580c505a80c0c040d00601081c01211080010b41c206008941100340440050700d421500c8410100119800c100c0500382c40c030003c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 744223498 1250 744222248 744222251
    0xd080406060902210112030e090405070503060c090f06070503120606040801020a02010605040c050c150c1201080604050f210304060b0d0506250e1c050613050709020a020c13 76
    0x50307402c200e101500c0e0f0f070842e403e40c083d41e4216412071015210b5041e00508030800c00250104000303500f01c5124594600141c43c0300c0b8040ea2241046424018158883e0360140a0881008000c6e1141d030003d240c80581260070036130098600d402d001880c0a80240184190b00030808050b40d80c2c4c2401e4842d40c40b40009012601d440d4079000e01c5070aa0304a45c01c406c000d41c0d152042401546880d000d464401c200038504181401495000c580d51640c00b01108202581c10b040801c5550f8040c0341190340c200304130350100005581d0b910b41c4540e100c90858056801d4020f68411100700c4401262119000b105500329010390605d400c1d0072441a4000ba10454905588003007000460f11401040d510042c082c0c0b0140102d450700703802c041581e4040f106c81281e0f55080030b0300e0098203604600c0c00505020250b07042c8141c07081c10550100f40c0307000080050300611070482003120100424028031405071080e01a5000310341c0e1040e854003680034400c0c542c00580c000e206007441d40e040c250391180100c203403c4c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 744224748 1250 744223498 744223511
    0x90604020c1f0e01050108030f07030c03050d1406120d200c03070f1502030c03181809010c11010204050a0e0c120106030506010e09040b0703110d050108030904060e090d080406 77
    0x40c0c00d5070305809101d11002d54035860744034410402072141a004020841c0075624281ca0089904500c0c854908000c0922401060090074548600156101c40400040c00c002500c5188100305003d0003c60b8017510454501c801e103000220702080b40707015104592030714510303200c004c2c01c1c0028441c1725201000742d512403040600f11543c1c0402600c0024085420f80c1c6030110b00b0450301c2901e0124220980c1300b5503104000102d5180303800402c58980301c0b8015401500c40d925080082e620072030981280d20494829024003071102c0c4190701601000303040d51504000e00440c07048c41c80c02e030f00940c41295480118a00c5c100800321400c0c0407035511000f110042490441c00f031100c000d0440d02a040b1500203075940d41084a82e58010060500e00b48048400d02d031180340c955240e89490f45e0090000b002c0540b00c10f00c0c61507005a00701942c0c60215081c40a00035503850301c0d07145640b500000d40052040c3d040503000034450202244160103460740c44043c00301800a403c0c00c0d180700c1d10240c800c071905540e03240d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 744225998 1250 744224748 744224773
    0x213090e0a170c0601050108070f030b061c15050109050303030a0902011404090605010909140a1127130905070b0304020a05090103030c050f0c010c060e120f0d0515090604020c 77
    0x8840090b019891040030340b00d12141d5909880d0020580069040c020040c090160f0f40741c04c06040c1102c800c1501e008190301098101244650180411040d8107810111150450720300a40120039090b29030001d0240c120340d18001140c0351002c5120310758054008001052458002d5003003003c5041c0181498031480104166001c00d5a0250303000300c007040da8521092120b981d00a1b007800041c24810010700c014040c0e09800043c10314058002d001c010b540702e03501440c0700d00601c25110208149045070b02c842c002c00d98220b040702c410410076803085e00c45800700508030a0300d2103a040500c0d0403070000c0000c9410100ca12049038005401682d0000702034400250030741e25000700301c0c080d601c00d41da401e400d01894544240b4142d90b40720320740c00d6504034285012003640c0c41010055600d800601c0421030045d40100c01c0e04206882c440341703203100f10024904079540c0d8420010070102d86441c1040009544101088060809800807039a0040c0400e000c5081b61030240c0140065071300810a8030741603038509 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 744227248 1250 744225998 744226013
    0xb0a081005220c08190e1c0f080a0c08070f09030b0103080d0506030a021e011404090c09140906010305090f0616030b0f0303070b04080408010e15010503010213090e0a 73
    0x10440e02c01e001e80700e015640000042d0103101c05250460801d0354007801c059a030204494400004c08682664507641d01c20041030412034140b81660805120001015202e002042c0034020180c00b40401d4003200481d048020034803c20340440a10f50320714106440e00b00d8200c450504000d026020860302450200116840250041c001c43c403407084659201c0350031050f8001c3d9074005201c140300e07410041c04e09015844080c2042c480070000001080c64010720001030b1418400310102000010000c540810080e00d6503201c2c1a800d00b0549501000983d28852800c1900800360280d4100c4d5549000c20030f10750107a04503a0f0405402c505807111b6240289040d46040030440340040082c1c048004240a290544101003001c002925a001030f0382d40d038004240d80f4804d0300c00092070503015000060500c0403100c03e44001d0540e18001340002418650f2940d03480724140e040f8000c0f40c5c80a00001003910b414802c48007044045465140b035145410342200c01050800c20421180c0114035418000820f403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 744228498 1250 744227248 744227269
    0x40f03030503062b0b01061803060509030c01020409090318061d010e031f0617060103021504150503160e09040609080d110301090510060c08160b0109020a080906010b0a081005 77
    0x41900420130f50889041c003c04078101a031020040c42001035403841b850900742e89800c103982d00300d40003140c20344803060242e01d144201d42801d40c01c0e500c049004150358074a50450003c1e240269525680d41c0000c101c8805808520310414001caa50401c025034a11000c90545100c2d001c141030545000401602007410281039502008154102c01b81c0d00040480d54441c00340500b1100380000c14000e880c810060341c8020601000c0d10508600302548031103411501101e002d015210701031244000d20368800381080d081500e0b400e0061288059110a10f441546514410f00c0000c151010036191a01c0b024010808404151960213040017080f128a43c2c0b400f1300510701c803035680c4940c3c1d298548031030a000c442018018080c00385003200100140c991098000c404207030001c819603920550307100650348040e55224020139518082000060000d0980e01611038801c20352141c2c161940c0e801c940586038102406a0b51000394140a074070031451003400690f80c400c5801e4034081e0760985070000521668030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 744229748 1250 744228498 744228559
    0xc07090b13050c040b0d390e0d02041508010b060a09060c051002220b0922090203010627050c160606050901081c0309152a180803040f0303050306 64
    0xc503440102d1650110a03024240000b604c20881c0a000084100301d80050a000700c7e00c2c200222180900720310740c0d0b00c14201c44050b034000c00400a403100c4407480e980b1060148240301c410751030088480d001e420b0802c1207c0d20304130640e980307410260818000380c6801d101510181d031140705d00c0341d104000c03003010b2004200c02440003c03040c10308800150700d01d2000f5225089400714040c1400241f01580b20740e80c002103080042c0e540c0480c0c0082060030380008184003400a5415820080c0c0010803810f85100d9a01e82a035080b003c0d410684804800000d982c015108104250320400c41d621a0f05035440c0303200b10041c410b60380451150f607584001400000b0a17000400140c114610b048621030075038812861200032410144919a010380b01c0f40c0320103100d1048044c800b41c40c0e800448480d1000c0401751024072003042ca196022035203600c0289110201f1341d0300c2c0c020b5021000080f4000c0000010b580448100128000340e1320b0640d50102e40580002c0d010326040696000418944050127907012803000303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 744230998 1250 744229748 744229751
    0x1503020c24061c0b0c0a020a0503030a060306050f0613020c101104290423060a0309020301050106171302041404030f030b060901270f0b0c07090b13050c040b0d 70
    0x1c0100c00c00c5554400503007100c00100e182c1c110f030300004111506a5500150701c104e4a522819848416402c0c9103083c40b000305107003c0002040740c80fa100e0362080c8160790207000d0400c266541d50702100390103841501d180b80d00250301d0601400000864004100900166007611403810030f10240c0c1c0d003a9480a00740c98050400820103002c010486501c40b88010f983e000c001d00c040100c40e042190074441c1b40134014441c03201d840c1e0460b40718150541510303110740c00741c022a07540580c1400200204402c8400300e1180d401e0000002e44180f10781141c01c03420340c00c940c4804250700c40d01c01d51070f41c10066901c12600940c0f00d85c0d070701e47e64410344801c1920550103a10303082800d0b0b00b911801030448145803509880f400d070521241c84503980c4940000d10781343c0e43c4448000d4808102c0000c203442c2ca02a0b000d2000e0780c810f01c00110f072030b0760583c001d0700302e0b018450100e9024a88480007a400e555690202035000700c82ea544900445209401aa801801c00707c2c50501d002e898001c64009548040651b4140a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 744232248 1250 744230998 744231001
    0x303040609030b07020309100f051308060403030b060a0f051602100c0312090c0e07020c060a02070305070933051c05061609140a1d0603070b041503020c24 68
    0x40240484180e01502910146d40340102d0500000e4000032407010010400008007409a00c0601800403203500c0070710500300011042c0c2e030ba09580d6954104607000c030006030600240b45694205442510f0b00f6610681f070300340380c2c045500400c58564008107108031901c81030703d4800c00542c8402103859a00d0362660350700111451282006090203410300711032142c4514044e41240401c50315000720060718480134181015456a2004916040c03400c0905070b8004000104800540d0b0001415822a8030540913281c101d039480411008581e041851031700400505100290000c540e0043c60703506c56400f1180c04210385e1100c0219100340b40f103080b52480d046509001c032040c031008009242d400162180c41402c0d034503400e03100400e0f0310a00c1c4610420815a021080010341e00e80d04003002500203040101800d14010f84da0030400030701070300c1d600c1c064025004041460f0400c581200e05603460343c0d1000f42c40e6015484210300030750002c44d60781114081c0708c004290902c2c0910b03c034031380070b14801c00b40e1115 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 744233498 1250 744232248 744232253
    0x110d090c05011b11040902040b09010e2d06041806020d091e12030b031f1b110309011202090904140601090c1704081303050607020c01030b012c030304060903 69
    0x2102d82e010581405800f02e502c0c04000206502244c16081c4410341e4080303a10b406030720124014000303040195502001d040c0002c0b0b900c0116040182c4154582c07024040b00340200d142565060300c086610019208a1000040780d0b801c00c3e400080580c003690400400d50303401074440500b03e0304500f094a10756a00c450317100c002d0060b5881c2d80e100340704800200340b0389142e4581d2030b400d90540306100d100505449450b020010381c0c042c44006040c1002250403111140300c17590b050002d02007525058880c01045c02c9802d28184a01368000c0c03030704071590086203020f14040040d203d8008003110702d60555002c001040090700c03034020050085110301105920031090700809030400034141c00c80e500700c2c1d00c1c10100c2280c140d4403461101039000058025030031a2201c2c10100901e2140c50a0040003a0082030000b04114000600300c0c4110081d509440c40c0201c428011030503540d040e0302d411300180b11020500351249007029040f10340c0c40900e884c40401030f082404282190800d42c07040c0046902c15504009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 744234748 1250 744233498 744233507
    0x819180501110309040b0411043b0a0225030203091302031302061612050c01060617010e070309151e050618070e2d010f020709110d090c0501 62
    0xa86400d0070b1041241840300c0020707540740100c0d5101032103192904030484407916a5840b00b080c0d503100d114010341c2d85458440d124030241c4d0f034a41c01501e9100410700400e8040c2107108404031145c10390070030074a540381d841c8004040c1d0010070545043c5202c00400d0002018072fa10501c3c89588240c010b07540b628240010484181000c081c1c0c400e069004200304459817440501004c82960304545943c0c0300e212050402c048003070340d818020240044003100300074598000c0040d1002107001802030240d1a150f5908682c800e6555058a038120610300041c024a15a4000c3c035034003070428580050008800c0c1c80e8000c6521110319240701d682d0780c0300103085486080c0100b00c42e115060450601032420b0100100b0b800c6036074140010114402d050100b90041d10910010f450440010700b4243c180600307a00a1401d1000e00c001034980031100403104000b9405030782c10441c20512900030304070046c50480140043c020790360fa030450f1804100a614030b1950144509e80f20300b070046c504104040d00700f400140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 744235998 1250 744234748 744234797
    0x8011409010639020111011a01050703140f041701020408030f2d0c0730020607060e0304090b031b09090a050102040906142d010c12020c010f030b03070e040819 70
    0x850f964105141c16101234616000b1007003040c401e203450303a60362041e8101110030b40501070354405c80510002d080c3c50041044c2c8003800c143d803032082c0901c0c06900030130034a500300d02c103074814203042d5017042c00300c025204450005448020445801c0f02e02c03444600000c407500042d21400e22900040c0828090780801d000c02500300505405020000e200d10040d81d80e640e01500d050b0034880205103500354908540f03840d010344400e20f41c4590103000c1b810124200944070b400c240505e90109241102001d0280f4001a01880182c500c443c201c42d111600d030203105440e03000030103016440c40380c8424071001a800348014401440c140c3c00c0001d07940d01b0301c40705045031341100d40c041e881074514494046441106040740314880352401540307000c42d00914010395404420683c080e005694106040003500e4011401e000344110998500001001d050419002c0718140090b05400d640b00c06020b024014a8244254003d80950840360601460001c05980c034214001d40380002030180381c2d01e004901c564032415 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 744237248 1250 744235998 744236027
    0xf040c030e19030504090c110d09031a0408030415060b1c050c0c12130923071b150f15030c09020315010503150303030903070201080114090106390201 66
    0x198070320003c0e2001003007401640170308074691f03a50b100031100103402a03241c50b100f221004295641841e90300f8018080ca4070300d101c15901c241c4101ca070058005800000030348910b5000c4a20b038190f44880c2c44914002c10183e880c0c484107641d0311004102c02000c0c0300a8110b40b11070068081046a0f0844084103840d00980034215016003803001c0841a00049118000114407880960716030148000c40d0300d21042030361140300303028503012991950001810380604800401300301119070b40c0301c130102101c491205d8002502c42d1000c201c0402c2c0020341c0c0c1124480b148050a0000c200748460f0400d80301140c0940c1c0720001904c1c034810b001c1042003491002c0500501d00e400702103040d490441070090340c0b174040c44010b9041160000c0083c1100c030742440c040d444160301404880c0c8a01d07198021035603ea10148003603010446840c0006030301034100120a4090134040e00c0c0300403e07441c0003015950b03404851031142000700508000a0340ba4003038010f091181c8071024036074032125003500000d40003d0300c8030b800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 744238498 1250 744237248 744237283
    0x231906050a0503040c05131b090b09040b1801141804030206040210120606180512100b0a080307060b011103120f13060204150908070f0308090f040c030e 67
    0x208401504501592192401401d04550725580c0b4a42072a40349105d030003090b4008141c5820640d0100140c0c0140403030959060171000c42041e420b001e4950036114400c46001080c10070400241e420b141d0400320410b00081c05480c0402d644400e41d000b482d40c03d07008419195000c0c2582665850072080c6011070341040c400c0f000d180d0406840080d281c00340108041d005000c80805111611b01c10261820301c45440c4a041150300d4a0f8040105502c0e070000800070080c14082c1c0c0410725141c44a0406052810b03c0b00801d1010f894000308400b8100000040d80e00452000380014903c9092000748071083c491080003c0c070380403400001d0002c10450365030201c20350092020b00c1c0f591003c00c04440d0000b5600003d0f01c01c0b07907100388004418058440c402005140003090002e08030318512881c48070180e490715000103640c0c5808030b03e80e40340d41d03a02c0351286840304d41d08108045031b007601c001e01003a000a81403d40e02c0406d1000b00b0300b0b90b45045081c17000a48d407000c4140c500c030302c240404c00d03100107140703607 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 744239748 1250 744238498 744238549
    0xf091f030506090c160f0b0f070905010e06030f0912041404181109040203011d060907060507030906030209040906020c060403141c0b060c0706120606230a020723 71
    0x50154081c80c05050030165007110701d03001b0b02c01400312001031554050151645890074414901000310305071480d20105a80750f102084960081c4900c1e07010784030240000741103903500c0790200c0c0e07502c8c00a00407000c10300880d05e0484911a40100a1001c1d0921909041c500c01c2404140b00c00c9511154030800380411100361000056880c442c100c00168003100c500d501a1580e00000b0700401862800c1d50220400000d00e001001c070205034181302e040c1d61800d440e401680e4540070381d00740c0305000b00100018080d18040c0255400f0381d014002c80315001d04000354103905a0b503281d00703d07880065480a035901c414204400c00d0b82c08210100549401003030305040450380d0f0242e00c0d240d10403082c1040d500f502c0c0c03411f201d1544c1701e200c02c0d182ca5480400882d81c14613500c00010704900010401d4410081c209500070a501d13002c1c03000c040c0c860700c1d1141c104031654500b11010920350800340d440401c43c020792a00080408219984401d2a01514989100303c40088104034035104ac802400900464010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 744240998 1250 744239748 744239761
    0x206090d030501030c090f0b0a080a030323130c12080c0105090c0907210603060203070f020a0f0212150109150f050a03020f030f0105070e010e0f0d06020f091f03050609 74
    0x80c01720b0446014201c0481e10b0380c240c0701e0000c00340091030021a04032040480c0003138016400210061b00354025201042140c0035130011407450101000408041600740000c1010303042050070342c941301405036040d038086076110107000b0004d840b101c1702615500350106609100c20030a00c2080d030451f81c010b0081041c1c2042c0c1c03003c10900e0340018628401c1c081907810190740c2045e40081d00c1c3d544c801c07040301044803540340d14061000b90019241d282c00640310012800d00140000f910704921900030b02c5e003c0c61f9510b84d03400c00c003040e1116045010240500380107141c1c5625010a1540a00613801000ca515110307640740d29a0190541c2c864481d00811800400403038880706020b105a0b5019200800400784050100e45049034044080c0615032801d81000038403a0301547d40e1100c0c40003661101310042441040011821010341069400302940c0041c50000c2d10b01c0d801440356030078507940c29040c801040e0000d024400071050155000100c0c9210300ca5140d490311a2903400442115665200e00b08007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 744242248 1250 744240998 744241013
    0x1306091a1e040b191401080c0603041a04110613080f031c270b0f060a05090f0601091703030a5004060b040e03030603030a050d060e04030206090d03050103 68
    0x180c009490b81c0e0143c004a0510303071090601018010021005102d0000d036249115080d1009226140079401280c056440790b1502c0c03c02c4a024603040b00e600c22075008644021003140c0406042207440f00641c00021050b41c6400d0050007805515000f00c0d40890b280c0b1040c00e0030891034164224560308208a03046582c513100302100b0900b20440c40015484040301d1030b007840d202e40042c0700d2003d0b180d042d00e100c04202015031003d01c5860708607140f680e0307504c0720020300c0800d001c0ca001d0a0792142d960800102000b008a41ca0b65002c0070524040140303e030703035000c204444040d114009409820006c10000c002203d401450074040720040b0002032101d1010850141c08205401451001d007a0710710210343d17140c15a092200807456058022541c185072030310308004d007050310742a030080d82400b4601400803004810781c1d201d072101030081d505d065100e030740c01c46180d8410700d0891110f0f40e40c0c00001c52580018200c1c24441c900c2a001400a07081c5541c030a46041a00e8038150105030a0500610005010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 744243498 1250 744242248 744242251
    0x30c140a0806030316050319093008130305010b190506030a140a0515010903170721030e1e0c10022a12120702091306091a1e 55
    0xc07407070501c0041e222240041c0c2140701d07902e500c003500c088610182090040201c01001d00003440e40c88050b05c84600602900d040c078592040c101ca0b45418440d0ba10320b00046401d2800e003d0b01503041c035484a01c90b40d03ca014640080c1c900728961031a280742031040007802d104040c1d294008645100d40c85913903051061a10880c4d01a042c01944044081883d00c1560b41010400348c101d1025070b01d144c82c0000d102030041608507888003101c484c4140300b1141c1e50060403104c05030782e00501c1070b4035a403502c00c3c1087c0c9940d01c4464203d4840d9402041d004041e44083e03084280c1e1895550086000c10024403e203180c1924403082c074184a411000f00d61000c1030003c0c070030503075600588018000c10b00b441d0050b4102594030000c501c8410148a21103014044100c043f0501d00c404c59400441c204140702190b601d10380d100e08004000000c00508015140000306a640007020b1b41c3c40301242c0203203507500d41c1035803217241c0c00311000d030310b082881031124440301c52581e409012401030750050044141c120228010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 744244604 1106 744243498 744243517
    0x2a050d0905010c110405060f04150609170c09130f030e0a090e100e2518050402100c03020f030a02150105060f1b010618050601030c14 59
    0x5540307000034007900a030f04410f0700d10100c4c01303000040c00b001d040154490103d00b8840c034680d496010340c1090f5500100403031801c81c0b500c0c1c00500002c865401031150600c0011907180001000030f0644810541205e202c030316611007603010041d0104902c40908078034000c007094410f05400110702c0489030020b5480c00141da076a4024442241c035011807024098000000c84550782c010b0780c03c404950800701058528514040030070b2000c43c211801c03204c08400e1001c90800843c50005220b8884404024040c051450f05038000782401c004103110509000c03201d1150002d0501c208904ca1034004088202c80d40c601003c10065582c248160b02c40303d81c0c0700344c00b00101c0d242c00c200c01944d081e09020f281c03242c102102c40c0300b40b50340d055118080007410765032107000090480489000c204059401071000a0504141c03000605650a0401c04820701000305079051110850500701d510201 = true := by decide +kernel

theorem cover : BRFrame.Cov 744064748 744244604 := by
  have h0 := BRFrame.cov_init 744064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 744064748 ≤ n) (h2 : n < 744244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
