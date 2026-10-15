-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4232
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:57:28.932028+00:00
-- url     : https://prove2.me/submissions/7ef936e7-e9b8-4c94-824a-a3f7985c9af9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 760971223 ≤ n < 761151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 760972473 1250 760971223 760971227
    0xa0206070212191505010e04060518030c0d090806070903080a020f01022113032106051c02090702030703021e0f01060b0d14040c1203021c08010f12030e060a 69
    0x3111811140c0240d5601d000c0180080750303c030102480c102c1d419840100c0b400c007485158030506040f44c5030036007940e002c2d9580e0380e5288020b040c010504040c1d94003080d031407683c5000c200b029006c144a14401020004124071000e800450f0741d50207010309031311250401400f282d018002408584d40480b100c2e44071440240164100007620300300104540c800b09440c20703c03111031701404920b10010031007001540c99046002002c207008040142c0440d03146491048508030941c6229094001c55500094044e2110002000300b000130340b8141000b444940140254582480c0f641d4000d031250008520f0105039560103502e60040d5a421141c104582c00b03800c2240b48140300d8114401c0c14a0000c22802da2540058a21500f202c2c10340800d05140c540750700403001611242e14012078000a1880c5110300d0400b508241b50400b03036044045000e10508150303a064030341c10300809a00a074650540d190304010700300202200d0f0ba0700042c800b1000700911008642c00403070142c00d18105952a5a0301d401030701c81 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 760973723 1250 760972473 760972489
    0x1a0307051009030b07050a0906080615130909141c020d050706060e0f010807090606120506041409150f1303030c090b040b0c010c0203040815040c09020a050702040c030e0a02060702 79
    0xc050013406607041001003580e4810004d0044000c00e031a41010a91104800c813035680c0c040300e00c9504080c0d0700040070407100c1040d0281c5922011100038220b4180c54103d40340580380040303011980c1450032100317500609414010492000c0c041c00c1704903c5400d1444001f95034000504420007801000180740c07050200c40d0300a0009007030800058103907410034440c41c020380c0c4024031518015014110010410000e40d00400007190881e66804000d4552140707003000600020f0305040d4003550f11070b07110404003180d600141c070510054025145004150305151b0b02d101005041540390066003003003042a0300640c0300804041d03010f250004101480100070317100d92a1980000309075810104000079002036400061888400c5a0003c0c0f004040d904000e0f03a40303006500602005800c03e100d100c2c00c540406000950141c001e02d1701400541c0d039502c2c400e0480c1c1c03101c07281100040c000034000c010740c100350207607504a4440d8030341001030034248080ca644880100f2002441004006060019540d4900b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 760974973 1250 760973723 760973729
    0x303030207081b1f06080c1504050a080307030e030607080f060d0206030c070309080f071e1203050c15090309040b1302130e010906030b0105060d090506041101031a0307051009 77
    0x1403062a0300e01c400700f2103949860040c10924014001d140390311800c1e241d80101c00444000400909445a81e03a04000c540b415159804a0f0118107000014041d03841f005a10020310040c07024640c1e60210742030080c82c0c840e03040c624a020781d00c43d4041c802c0c81503000707100d2a40052211005411078070b074480000d01700e6910740c001030f500140100910010707000c1c06004003d02846915202c503030b00d0781c410341283c50b0014150000d48680141404000c102e106100030782003040f00c01e1076554000d4403101e01c030800440602055000410114501c0c520710004c11405001d003010582c40c50b001d240401213155a031061600050180f03859003c05101501c51461101e1480307011001591102250468680d01071540d00c00c112003044480000227600004d0f2280c4d8013520b4200908a080381e003001c0078009140d001120260085079100841c00106601b0b004880c00380380b2660f20b100e010612140010240c9100e01f0629480024800d011111780d80d0002d65441252001e40e0f100440681460040c0c96204640d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 760976223 1250 760974973 760974997
    0x31205070806040b01020703020f0f0a15031b0e100e010504031a0402040501050105160b0c0f0d0f0b030d05091306080609030301150e0f01140f040801020c150709030303020708 77
    0x80140505550011030442c42218240c6080041c80c881000480e61101c070352001035000345403004030035518140151008000030010304030303480c0c50b940c40d2180c0b40e04000c442001c00c0000c6e80c4514400c120007040c040e03107180901a00c0d18a520240107070000f80e2034141000300c0c0b418030050380611252a40901c00b030b00c0055400040b0700d0291207000786148040c541c2140c04a101d2440c040000c07074158050703c11341e060410354161400c1841c0c01c0c0c0d41c9440340e00c10044e044240d40362090040100c4061030170010400ca84409001003614042c011202e825611200c2c4038502c40e8014009a4118075400f05c280c03480400300300d03912000060f1542c048d03c01041683c11100903806981b040255410000004504850640c43c44403803c0040720021640c40000c203051075400440b00301d02201a41c0b1580801035200c0341012002c0c90126400741442c082d50060740301081d039940114103003800c00e00902c0300014401c602c010304260361920035001400000e0324003004007403503404600315080c01000029140380784903074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 760977473 1250 760976223 760976231
    0x6161e020f0609010204030c03080a03090f0515090c01021b0f040921170112030e060a0903050c0a031e050a02030601090605040e0d020714042004060f050906160312 72
    0x1058000303440302001038200000344220804245000301c1403084500b2650880c01d144031850959949410582c0b11000b51f500300354480001c0b0012035044603450ba040d030f00c81c000928a880c01c0003401028660024036802c0e540e00501900b02d0166004100340000500500403413070b1782295000040c05509000c20f0311600f04d45091001c404221407420036562001c0e041d0600000707012210011113101c4080304603058400380f12401000b50200c00e491104115210341415602c801180004c0366082d04615445000550140820414081c052004d07190018054542100040c10368540085c200202c0c9400b0b540391310100703e21010b0101c1888403c00060380101903a025582d10701f080000b800e104c1c01054480d42c5000400b01195200240316503450705143c0107400028a00400d007079110b02400c00031a0043d0715a5520203071540054150390515452544007070310355080c400002c1c558000e044c1c002041c000100080042030380d4140070b8619101c19001140b0044000385001c0701e260506011290100d418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 760978723 1250 760977473 760977527
    0x9031709211510030804090203060d14010203060a051206070c020d05070602010c0e010e0108040b1b07050304031101020a110603180d030b0f010912060f020708040b0c16080616 77
    0xc80d402c650a071051000480780d45a0075034218042e41180700050010700b003003004201c0b0001d03c0d000345030302c110f00611030710307590b0041d031100d801000302c40c0105d00d2240d60010400c01c2da0301d018031192000c0d25094440e0100100d01560850f034800d000341912045c4a80d010b41a0115903514070440386180e80030056454013566108042e01070690301080001003400f0b5065a5103a5116200b203d0000c1c0d0140c0d01ca000a841e140c5a101c0c2c25800904503804541b0448142540440508000c081c002e12907001540d0303c601e142003444c40f104204a2141c1190400c0d1052400310300141448214403100b10341d00307541e03a1116241044040d0241e9140c00c054042c0c0c4102c0c4a6850701031313105404c5a90305480b000c42d04102040110780c0c0d05854091050a11411700362403000c65100e1384a54500400c440f0014540415a2140c86040c0c0040d4815020315100103040030f01d860003801071311488120010142100f5042031841c0b526040000c0c0b1100342a2000280e4400c030301d2107002600e01c0c0100c101c0e800e04055031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 760979973 1250 760978723 760978789
    0x51516170a030c0f1e03200309010b040510090e19060b0307080f0d05300106110d050703030f0b041506080f0112080703020309040f060e0709031709 65
    0x601501c400b103894035944010f524001c2d20910040c1c9055511031a01850000031440805566007460041580e42ca4040700101000842075068004101c0707203039204d140ca0040c80703082d180e0380b801c0030780114200414410b1800544054605695200d44041504074802128514000d141100c1c0000203103910004410b001c13050784151030004044d0181c1c2c42680e1a031030b002c0e5440412240f034210541c80260040307600c920801c0070b0004a04060400c8641c1a803005880501c10106503d41d42c00c910303800700410005402c8103e02c2c139401030f18401780ca03160495140150a0340a0000081c3c02d0507129400c40380425181da001041d00d40740100b0800c25490107a64114a10000d030003a00c01003008540402c1c9a000a07208060407150741c030348041085d1100f503595a17020342120344120194482408129116600c6004006104044040000b2030920306010080380e8000640705800380900580188080381484600060202008605c159100046e801080d0841c90314054a0b4003851a0141c0c032040c0c030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 760981223 1250 760979973 760979977
    0x6020d060b030105280510020c0d0303050906070e010804081b0a06020a0f08040b01050f060f030f15060c0706051317060604050717040f08040e15040e030405151617 72
    0xa24160388180204034545c007103441500008600a45031a07039508100241c1c0340828020642d0f002510503100001e0460003c1085408041021000700b0f407200108604164204445907104c4c015181030141c091070a00080c0030075a01030000b030603285000076000460f02d81140792481201c0c0d4201110610f10650800500941110200f98005440040048052403103021794030f0049820500001c1580d00c2e060400840e0001c500c00d26030403031000c0c0001100224a130028504c1904030240001c80361512040403120650310642581c86810184602d04521000140396020f5031803d080281c3c8e07403c0b03280301041d0342c101d0980c4000c041c110244000b5125600204e0414042c038000d850502041e00e44034010b0304d0305440107620091350a0841d00260100b108012030108090254ce072032803803c0c0d10703a500601301c501c0c2182d54180314021001400001d04080c441c4000e0000d900020b582000d08050000700040e03070300500030046c0100800c06002d50410010805c030b903998400150000d080c510140d400c56a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 760982473 1250 760981223 760981229
    0x503460c0801060c020a0b16020d0c05011b08031303020c031009140111160305040e09301602030705061b010b0312030c030907170f06011a090d06020d060b0301 70
    0x40d0241c80001096406549207040c02070380200031040d8142000090100e51b0040e0090040300220001004096100c12840480d19801003510303075855410900090700000080b0440c4400d00421400c2d01c000c2221001600d03000b1000943c100d074581c10344d0504910780004044040e9050060b004e402181c64015446905001e210f02e508042c0000c00710000740c00c0b10030703a0351551050001084170200b81901000c1d23010308a40300c0d007403141c107264580c000200e00683c11101d880440c0e01903100108504010300c0c112030030611000207507507080340140100003503003e41c075000d0580703601c140c421408554040c0b100303c0242c0790141005480b5004000241002520807504040c00d501e4140c08034107909000c40c18002e240161591a032854441886890181e40018001503550003402804038054908611410b00c1c00240d2000f0640c081010891905041d010307071021802140854940000303240240981d030401c00700b11101c0703020b22140d05010000c0d106001411801c0d501c3d001380461000c901c2d00142d416 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 760983723 1250 760982473 760982477
    0xc090a20042d0f03030c15060b0c06060d1212021207020303180303160c1a010303050c070f050a0909140a050133050f0f030105040f0209070503460c 65
    0x2c078440c82800004011070601079603070381c2c0034243c80501c08070780030f054000b82c01841090170500aa5400c030b02031080351200e401040404000141081c1120010090070742c010104449282c4801d03a036541c2c0710041c4000d0f10507081807110040e03011604c806684c0c15038070643d00840c24010203150110009451780d00890b9421500c541552a030f950707032100002030301e11540d41005011088160701c0400c0c0d88000511604544178038603001c0608807441c00300101030003540301e0741b18541c0b140341b425420343c00c05100e6008035003803100424081049944a1800c4400c1711103500c00023078605210b0404040c0a4142c14102240d407088000c030000304001540062040b100f4a030b0301b6810b28603424540307014884c000e124a00003a00d40032052040386090820803640d0380005248102510b00c04000ca420360b082201c007615031000c011546010350500d0000558000740d1460310928614010270f064110b1250140040c404201040d400020340010ba071100103996620020007242c10030340340c94100544080c1d580f800c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 760984973 1250 760983723 760983779
    0x5060f0f070807120f0c17010b1e03090c0d030e03100b2d1e0406150c0b04060908120a0b060c1e0c0628020c090a2004 52
    0x46034000603031055005a00d150b44886581e10b540c0400c8806140a41009080d0380e5581420400c40c44070b8452054912034a40701c0301c1c111800002c0b00304600405078040380c00fa1800308a000c0701d4104442c0042030440c01e00100c43c2d04d036212815091316041400064580020070310b40fa5405140e0855408075080504800300c071800103030181c54205403800164050f8121050b03041201c4503580c10348440c00c81a0700d0f6407034044681010f1002a02050384038105108910b000000c8061a041c076005807809401744520080d50101e54400c0100500900400541040300a0011504000e80c58000301c220941040d1010b0f201d6142801188610324140c1325031226078640604880581449030580c0c3c28110008090000043d60b0613504800c449a4440841d041c014903420074169900e01018004103c0541c0c0c0007402a40030300030600c003004500070399105640c0588600707aa0740c0d4655488540c85600307140007050741d05000d4886400c2d00d02c551000c054400e8041404111038051500c1c0d07400080440d81410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 760986223 1250 760984973 760984981
    0x60513150c050c010c030c1401151223060103021e06040b0a03051312030f060b0f04050118290d09051b01050f03011a0f070605040b150f040b1c05060f 66
    0x1d1756080310610000c010070110a0040e01085410360003641a000c0340b400401c1c801c0210800e40184842034200ba000041150900c46c00d01102404002030302c03940c140496040703481c00034011380d0740005100003482040c4906a00c1c41000d8150180545654043c11458485455201c51041500308008020000e031070f00e070000c0c401600b0140c3e003291041e008142107000313401030907086001e456508000300c03056480c0d060004001d031501004040050480c100ca545a50518000400d0b1016a15004100000001e014010000b12405e0b5038011800e1030400181c07454201d00032200c6000f00700b070040c000351402418030300303025010a0000c00418042d1500341510140e00040d02c050080c204d100340740c02c105100502c0500b082d080e002c60240f40446e034450a00d10003102c2c0b1111b552000008039151500c92090004000001c0d0b04076030060030003c3e95107204411000411000e030300103502c1f244a5500d40106500a80341c800801026821000b210b4540000500384141d8079041030b00d040ca41e4040d124001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 760987473 1250 760986223 760986227
    0x907051503060904080c070e1006140a0504050f12010f05100906030506150a050306280219120b0406081b01020102090603010909021507060e0c030f0304060513150c050c01 75
    0x5070b10685004040003081c1d100d175141d40a240d04842451401ca11503010007140c0741c5940c0070058421505481d0500a2130309148005040d610140e03190144110148403144000e07070001e007903409450080d074000021682400010740b02c90540b607004002d652801c000a0403c40468108500c41d003003048000d200d00750b55a40780c4c0201c507414403014103c0d8018402090560b041200b8100e500c0da0001c1c201141d0f69203400000c0c0c01c011050ba80718803034040106c96a11045613100c800c400c42e0414030070444c1050320b60b00d030f9402c0d07400401640f0000c1002e80c404403002e0328400c0d4841d242034030300074000300200c035280c13a03425648040d0300c1c0001c2e00e2f0800381c60009002e5031050007103920024020f0718090460740ba210486019050404c8201c0c0d0045042150325141003d4002810300310780034080101f4000c50325540da0b1300700100c00d9405802030300003210070010580000101c400f284d04614003540e5910100c000750100c05210b0f003010317000c010451041c83c406a40458040308050044003a02d080c1c491940c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 760988723 1250 760987473 760987477
    0x80109030e100f35150301060b030703050720010f0609050103020d170c150a05160207150201110c0f10020705071a390105040c210b09070515 62
    0xc4400202e40b00000c15025224101d000451301c1600c6210b5604100d00000741c0380c0507510440085a80c1d00c01c000c0007030051403102e928280c508160002c1110a00f40408441248401032025041c15200c00209440a10884411414420201d05203686013408074415010305600b00021f078042e0304082020410344030714402c2504030ba5000300800c1610140d82d854881103149114107c00e2880144115189108140441c403901040e92482840c10b10b0805002021240064140490355199280081c40c003034001400c10152442c4452101d001c0c1c0c540c0030104d000d404038034200c504a290204180b854405e00288000001c5014410740742d41d034600624030303030890051042c01380150744800420081d24250b218100903640082c640380e854600242c001d00708010ba04c46240c2404c41c01c8103440038145101803102d203802095030303009000c0b0b030800d0745401031078020034060b1456810300c0c50401c404102050181c09103c1e91300c07140c203880d9881d0500d84651540c0c15841142d001c1d50403100c03821b5071180c002c02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 760989973 1250 760988723 760988749
    0x603030904230406060905010e04020f211507020705031f0507030b0d0f0c1a030f070e0312090901050409470402030d170c0702041401080109030e 64
    0x1142408198020000a00340321000364800c0c1c41180705039440c90210102c40c41c0314601820012602c10329207520301c4d08889050b40300061801850051000680e58054100700c071104c1240c0303142c400040032001c41da61201e001310307881d0703a4480d180c905452507540782d40c0d451092100d50251058507541e20305250301e82d0000301c4200c101c1c0c04a9414031409400b1030b845150040c20602d4001402e01182c00454220485c501040e0f90000401800c5001c1200e141e142c10050801c2d02d0301c0d042040da04042d003064902020b024000000d507030000240d295071152440101c038040c01003c8030203641e00140720740600d5018210b8075014100341c00000c02c1c2ca06040c060001c015900000d0b1140d15158859003a040401e40c00c5802840148440d02e1101080c0246a07070304440411510501e040c18248105440c101c2000701c2c0317405101803a849248d000c015181340d182c0c01400254143ea0351440c03440018010400c4260780d18407000c024001243c10b040550122407060f109803500341d0785100e030380208403400d00c80322 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 760991223 1250 760989973 760989979
    0xf02180714031b1b10060b070602030408090d08120105010509012708100e07050409080a0807030902130c0e090411060702030f030301142103030103030c030507050715110606 76
    0x71854003814500403005540c4024069211043d030007002c0c1c2d024003540d10140260b01c8011130441c451003034a00900c103030190b00b440100e04014451801c1c0310b5940038064044090102d80e4044005414401d00300101d40d0203000c02000314404030f040c0d191100d03664000b00c6c2c40d030b1800007590001080c9540202e003100c48a81050311885003401e403011042100b0800d101d0804034803c110380000070041d208001000102a03107940206048040c00380b4945080d0702c1e0390103184150308049004010545880803038003c5103003450300c0769180e035403007200340c0191805840003500841d001c91642040280d0340e1000c3c03460f1516070f1f40c0f0720107002c40c50700700101228282d8010b4490106c00d52810218503102000b8210740d84003070203444070b5080c00b042c40c5003160000d83c041600d900050070060514a04280f40c180524101d0301e0a41d00ea11409038040d913a4001400000c080c410500804424135009800792600a640036089880c060745958840c0b03904281452180c0100386082e40d150700500021410600c121005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 760992473 1250 760991223 760991237
    0x50304121d0f1c080301061202131a160b15040b300f01020c070f080a0b0703020408030318060a0209010c0f020d0b0106020607090e06030a17040801090f021807 70
    0x801c040140c0107070760311280396201c9481d04070001c03203114407002c00c02004c4c000d60200d6240d601d400d0020b03110840c0c0500340340103d031040040355030008800582c101070f81c1b40c5400d8140c20b010410f030585d1013403140c00300381c00704000194458010041444503aa201e01c0f41c800c1d2101d440c2c0e8043c0c0a0000340c403a150700b8641d1200b0481000c05100d00c0c504002c140401c2100c107943c0c84a100c0032010303410315021a15058641e500001d00e0110030408200b58401000000501c1024070b2130003409079215880c0800c010400c90716200452900c0748a0340544002d0310a090540361399050a00d9840380c0c01d0350704c41c243d014500039140003d0713082e4550b10a64400840c10b0319040c45801c19030756080781c0004504012030b809103001a051000c220154811400381440d50014403982c2000c0601802580302c80d031001928001020401040d42c90100d8500300f001c1d030002d401170700848404020841c0d4003c45c2c102d10445c4d86829010b5043c041402c0c07444000c14000c0d210403c0061803079502409001c8202da03807401140344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 760993723 1250 760992473 760992527
    0x5130905070b030621071706101d0c0f090a06050306010806010503010b12040512070f11030d090e06030a1202010c031b050412050102091903060e0d080115020a06050705030412 77
    0x240c3c084030725214178003d0711800e40d11050700c031321805011001210310798848010080041350451100014200a136403150fa0501900c000340200035004206c89403070800891402c024100c070106030f40d110b0304000c0c00700b94100e4451500a000741c0003104c4080c005080000460326950003541224140c41900400c10304d00030004024144d84003001d041104c0a1082c2c1e0f001e0340d03425882901812505204e41c51031140310b0014242844142085040c80d0303c0390708980810b201c0319400c03509881c100c0e81c420b1841d160301d07030350310300000d040c540046400390084080225015040390306501c43c046400003070b102045490040c0340c0200d441c0070220201c00c0420b1007008140311820340c8000380802284144005450880118082100d0025400080703459600103030052082000c5030003100d00ca26071000040400c441e280000405e404030600c14072840c0050f0484014040d48288943c2d0030040e0030900901060505100060555100f00e80999006145000396074805205000c0c80d10510318000162922030b103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 760994973 1250 760993723 760993759
    0x1504021c020a030c080c1201140f04051606020d02070602070b0f0f07060204030521070201020606060c07320a0308030601082502010b040b0406080703080f0405130905070b0306 77
    0x1221400690340002c0d544070010009038000c510001404055010b080e28890f13502c103200c3c10804003002c06d94a64103102c07805044501d403d80199104400300042c110b59142c0c1d0426608002d4901c0d07415894031105000840c2154001640e0741200d03120340d0131150720554a8034100d0b02c8941c0e5004000440d0420804e84039100c9440b000340500c984201046441d1a445640d040d0032a4042d1340102c42d65080400b482c01048a07600c0050340c50b02d001c11002d4070f094840d60000b9202c1c540100040d229243c085000c509442040080c603000e0285000c81c007490301e0142403220343c0141750034114004054917401700c1e0207500b400b50319181205d500240050a40c2c494400544048400400d40f007100d075001400c40040601074442551141100c4e000010000110014041964144030225000d42d05243c02009504400650003007280c1c1c02c140c605466a000034071030250340c82154005070748820070226017408803141e82c2c840b00d0b4079032090302220b8203036586480c01900c6010403120954410f8101c280d1104083c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 760996223 1250 760994973 760995019
    0x6010e0618011518060816080103050a06050c0904062d081f2a08010e060d03030203190c02030c101107061a220501120809060711100302030702150402 66
    0x2c001414008003244c01800c24640110656104074005074590342407101110120718081c0440f01c03180b410100310340c1152100c0d42e031018140350080456070b035100001d01e0041040c4c1550000c28000704140b00351543c3d010740d42c0010700101075060a08030305942400c0a031482508140440c0c554401424501081445c0d00e07074100a0038039041031140c1c94460141d04d4014511448040303e0300055800c0c1628411680100f580d501600003c01400075401840001c3d510341114136071840d07041c030b0301580d00d56034055504003980b00100312041e4541400c9001c0815a008000780c40c51088207030455001004201058003911000181c070100004104005404100d458102c01090f00103e0082e552061481020518031880403003100310b0700c1c161003071001802c8568094079004004000c00388200c100f041d110f07000a0f228420300c4510400001400c2004c0100848030313207801000040864240c03640c0950050040c2d4011617460005020304a5114640080344d203403140915000343c02c2e5000d0300707c0c071940da0b1707109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 760997473 1250 760996223 760996259
    0xa050a12090f09140702120f1605060a1b03020a140903150a050a0b030120091201021204111e0103020a17010b04032609040207020f0301020c06010e061801 68
    0x100810001103410b19502420301d00030250b0300030002d074401c4510451104500060191400c54200d00003000240f040d91059885901810098a0391180020459590500600c800a0490041e44200803400301c0e00e92200c2500c4d0000c0a40801c0b0780d600400803001c0384550080003001c81d084450101d400f048400c064136154202504880c3c00c1c0700756110b001100341d42181c4c1c4100031900e48003003100c0740103079004100e4ae0350360030b80080c401c4038a8074803402034082d07452100225007100412038481559420410b03412854041008540c4c41c28070290042c00c2c1a0101c500340c403d1b111a80e14500f007400c160224081488c00001519020b0034940011406940601d07035102c20002c907001400c0118034000300c26402030054800b01c680c1c1d1445c510300003441c42d9511001e0882c40d000c1001310800e810403181100c9411000b01e40042c2d448649100081c18807418910071078142d032010451500100000442505850204002811030380d038500070080303505820b0798142910746c00c10004210340c84030000f6407046 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 760998723 1250 760997473 760997477
    0x1103340c020f0405090f07120c090908070b0c090a050d020907110f1905060c090607061808030f04060e120d0f0608030a0f0f0203160f0c030204020c0a140a050a12 71
    0x2100760610000b4095540a0340c5c1002d854100071480700c6443c00030480c44000f03100c2001007900c400000e85611309184102c4c03007442c1105032205030b40020007820030222070103650301070350680d414103040800c3d01e01c0750407919003a4020b01404101090501d401850f6480b4140d004200d1219503880c603108449003d489002d01c2d07141e02c6025001015894140400301c0d146561014011840c4110304000f0710f01034000c0c090032a410400c2001b0140c1e034441c1002c84890700e4100e080411401040f00c60306000391681080500b103c6008820300071054041003241d80201d015035001e100e442d5003101c03150384400007611440740c3d0310410003026907100c1103508400398400740c60500040305030b5181034050965022a000c00000b516031161a090a608541290096400c510081d0f0800c94603d09d00450703910703107603c003626011012003507104100360408000c0195902400541d00c44424103600d0350b845680880c200c60110381c648040d00540e20000d104400c064004004101c11105501ca0150a400e48119001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 760999973 1250 760998723 760998739
    0xf03021c08300702120a050705070e0601030c0801060203041e090203151c020a0303141e0a09060c1e020a1203181205100203130203011103340c02 64
    0x490420800760058000050102104410080e80251200c1e00b440d5550a4012048184044281e00103506440c10f41d215602513034400e56188140d400d8015100300800b07601c204580841c81548620055004010a80301030040b200f0644080d40c1e80c0409028078401039000b40002c00030641c0c000b945010501d201c00c0700314102d0341c560800070280d0340100c1c0c0324a440301204040a005041100000c81c0e181d8480f40200b40c180043c0d4000342c0c110741c0d02e20014080000c03560b986c501c0800444200e402003003c1c0c41c0c6541d08014071070743c1c55140c0e0700030364580404582100e40006055000e6003006810359409030784c2c00c01c41c2818100001c2c0e0f000342000242c0c0c200b05241408180b02039000c1c007072a10719000e612107c0c1840c0f00844a011070640d260010400d03800e1900e6640d00180300044c00352140c1c04a01c034003580b0386d42e0744100e51310002250440654590300707040d100503041001400944c021400d0744060410422610500314001d055110281d00d008062030030804081d1090b00c8000701c0b180300900f408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 761001223 1250 760999973 761000029
    0x1b060304030221160f0c08070b0904050c040e280b0102120c0307020d031817190501180605190e071502010f0207080a030c0f0c02010e03120a080f0108070f0302 70
    0x284103114030300c003110000b0141203610107201b8404d00440c0103180d0305008142040c10200392240c00d02a208402d8007890301c40012a6103003204105440140440b018941c03950310b010030314040d20519000301c5c40140c2103041c1420000c00e4890003040e50308a01a0001d040c2c1412113004860340f03a0004121244900060121000503510600004c00190003a80c5215100c035400743d045451008590000c040007000b901c3d000100f2070003284a4910300c5c84520f40d038000200e141001030140c041001c091076450501c408000420140d50300403030081605650005005110714095001c60b942c06015041c03640c80008100898070140c68945180c44461001040e1342c440c10300800181d81101c40110f41041001c50390fa803420354103100b041c0c036842107460118031003680403030090800c1d4120040a03042100701ca0901803583c5017002903650011300501581d030b07903122805005181e4041500d10214041444000052010b0001800001e0b540a00c0c18004c4c1c02d0701d141c0c20400f020326104040c40511024000f00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 761002473 1250 761001223 761001247
    0x30403050f070810020a14070606180903080f04031704060e102406050d0f180b0f100b031513140105180c0a0c0203030712021b060304030221 62
    0x2408111040000c00300740f410303c0740716800c1c80b84910041c20400d10500694200319800b6851550b05040840410703913400f01420420003810040d0015044007403210007085195440d90310001f80940603580d410303816251800112031054080d140900018289580c43c0c45034040b840000e40c000c1d226036400a240c000d07420481c3d081c440d03280300d03405c140340e0f40f012350341d001400f800b5070100c0304002d4071400b4101c242130500250141c040d0341c50024100d5a5004411008078840c0e10400e564032240003442000c1401e49080c1040c59000c80e00c012401f070380b55000c1030170b5020f07810098058600004805003161340e801445a4205900040140e08c01900c1e8128001001c00c0c0c403e0350500c10321201e0350003c541c18034081c04108890400140b51203c02a400c11030100c00010540310b18090300d26142c05c1c0ca00c918000246140521070015106000c40100c010486030002541145240140c10200c07107240c408081110074042203c0180141e00900c182400c203400e800901c0030740e542050000c174202020540380d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 761003723 1250 761002473 761002483
    0x18021c110301030209010b032a070206040e041b1a18130507080903070f060b2107050103051305060a0c1107090204080705040b030d080604200d11160f0503040305 71
    0xc05540e01600000510550520391a070f240900600c00d140f500d1400c000321454070140c40c01c1d24000c100812002024054041a012100f2a6400914140d11503031074841c4013075000000d0368101d81d002e071802c806a103884454040d010865104e00c814000c0f200d03081540000d03913400210417500074060361401030034030794440b030740c08540ca4000400000c0500d444c10b0007604a0902a0507140c4070b9206202000015617400c00c035072200780d80000049900c00345000803c4868140003c44149485001c00309191140005503000488100340d80074409910b1701c101800001c0780721440585190085400154400195001102c0a860b9442d08011103251035014509042681e00071440c141d80016040042040800080c0082c041c04c8400304503601468000903a640c00707810f101014030110708001036081d9919070040c81d030080c1000d0110418650202500d0980d44284600000d092910881c46c89510350304099921030342011010419070019905c0d0034034401a40c02080b507092104000100000d402400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 761004973 1250 761003723 761003741
    0x818031006091b0305090304090e01110304050d02060c030609041202120316031a0d1209030f030c03020d0e03100216050106030f0515070917030c0109080d060e0118021c 74
    0x200c00903601005500c514030b840820f094400030541800d080c0007802001004030780c21101c000c01e0000c1e1140c11020b005000d0300b41c201004842c0303c004005c000900902141441400c0e00035802c6c0e4081f69142e881300600c0d40400e98004c1e0304441214000b0f800144011656891f2a01e5801200e00c912100200484103034070840e501038450074940c004600c8503402d400383c17601198040756010364102101000c504100d9108101804070010441100c0d40c5d10f01a05444000d1500700043c11142c502c6420054210b0b03440740b100324010320a001e1103841051003618101900300d4010003070810950540322400c007a4108168001d02e5040c0c000040c000640248603000055100c0e40c114003695100c0d081c03d80c10444000344131240b2401c15010804116400f02c410303001c0e51110380480d41004018000c003417950240b414854500d41c0f030305c450081804400700280c16074003c019014003444c1d48881040941d00c0b020711540448410300400f401103095550042e040c035042c105400c50713122052070101c2c810ba44110b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 761006223 1250 761004973 761004989
    0x1140d060903030e07050d0f020f1225120302070302090a15080a020a081b042307030605040b030a030e040c0327060b090f04020112020c0709021c090818031006 70
    0x1580903132041c2c018001c00005040880303450001103015111080c19900051000344900e14240408a4550b00c8914440902050404542d05201c440c0f844864100103d1074520807a21403060004500805149941d1000d9250380a0040580727194248210444090140e240e0162245c0018103004580300a800c000e003c204024070034100300740140004c0b020a5048800280c1083e03031061200942d01c040c0c001114020703140015440301560341c20360340c52070940092812116420a104485601d50807140c00d49004680810000076204101566080444c00050101d2010000d602e4180b405600c0840801c82c0340c00c0202c6e805506000c0081c0707400c0c01c405404c4045c44002c0c0a8070911100b0f201d43c4140b03900588401c0d00d5400e214064150400c40100024100215100070160b8400c00c0c1c0c05546024202c441128085c03500c403410040690847ca507441c0544200301d0000300079400d54040c02c0b00a0f43c00071000c91400c40c61184100360a5880011581c15106584c0d03001c0072050684964001402c40c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 761007473 1250 761006223 761006231
    0x30e15090406210809150304030804051203060a0303030b0d1b030302010c05180f01120513050f0a080a080406181a060406060503011701091a0f0106030606050301140d06090303 77
    0x4400c00c0100d46950300181003040740800b20100f00440c40d07442d85406500628400e844100c001c000034080c00001041e80d400040c088180000c05400041c1c031030081f4825000e803412070b81c91022041e040d0004648495004d00404000c00109029504c00103401d60050410000da6546449500190f101040007a0740c00114180170004d141d42880b0340c0e4241629454085c0c60320710a840d40301104601c80e90580d10801180082540341da0080881c162121480d001c00e008030320f0f11004880701141404401d0312180260400000c2030f0308007244942015910186540c103203182510215076a5900038000c0f565a03941e450100e8003490500c1c002541c041c859840403080f604010614811001d01504560146003000300a00c00d8640040c1501e066a074140180305068018800d898003600c240c2d50040c02049240710160f03112012040c80c24400c000c81c0d10044a281d9030b032a0102d0481c0c2083c80707048009001840144652a08a004034401e804010112001405039440e15412a5181902100401d590b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 761008723 1250 761007473 761007487
    0x250b0403211803330501080d050f0a0c14030f0a0e0414010302010305060d060227090714070201091707051c11040504020d0b0703020a1706010f0804030e15 68
    0x90510070081d415580c0c50110740c5440c1000030140151101d0000815108000d9002d0128262411320242c8500716000d0407544e034094064400c00419007030044034070782d02a440c155045a402801200e5a608000d0311082c80c0414805044030710403401c00044491810340d80c090080a00100040c240d2103007020345060713443d00c050034054540410254581d020b142060601d26504119218441c1100e0b020f00b00855541d4900740010025403062038003d000500c08260f000c402d501c0701142e420343c654030a0751381800d8588201008070b06c2600315442c00001d0090744411100740340f10f0000d0502c251040c10f0102ca01a1281c606e101d5920036008c0034030803079010b40000c000514102c6101000440050b010a910f6841d58507640c002c2e2542c00700c15401161124045021902c47c6d1880c1c84c2d125400c50864980d074106480300401a6002190403400035034903540d001d0046208142c880d0041030161101410f035030031018240da40705030062060701031103504001510162901c602c00b01c00c01071501c0c960307581e81003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 761009973 1250 761008723 761008763
    0x31409011a0d03120c140a0305040605130b2d01080607090e1b0c07090203043912060b04390e060c030c07060804110909250b0403 57
    0x5426205200b100001210030103e07420800c8500091070350040407640d41c220807030a6501c01e0000080320f5075248001808181c440d455030106005510551044c02680c98080010412964220014141c0040304000c20112203000700300e481d0a4905070415190404e4142c80c400703495200b46c0c0702d011071780c0200381000300e12540b04107140d01070034827010f000c041420041c00d128240c4c06c0401c140c0c20316000c009000040030104018031001490b4002c02907540b45098030b8402c00c0300001d6800d01c02d900d210520302c1c2c08147c1e140685071500b040920840d0240300c1c981074100100e11030205060301c103681d90f000090040d896500443c54007500e407640c140c0703920a01010364822500040d05070790806c401282d0f10580c85600c0fa280d48868181180c0564441c00c4010303103036003548220b148615480c0710300540001d450740c10106082c40347c0d00035181070800544280c140403042c1012a00340c1c0e50303604401401e400c4400f00c852214524940c42c501d650806031a4941074000f548550000e45400541a000c000701c41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 761011223 1250 761009973 761010011
    0x1d060d09020108070c0503180a0e07090509090705030c06090d0203070f063c0519081b120406240e0906070f080a23041b1d0105090703140901 62
    0x50080d05d414803004125131030325030b00c1e801503010100a5400010701701e00b2541c0e0713a04d1054040c050b46070301c5100034182001d01800719a81881900d006003078040000b4504c58001c1244401c440d00a80034001403803d410400c40d59901120406900443c8001e0400140e05c0401c42c1d032019041c58800079a900d400e14001421480d240030700d4030748801c40d640009900f030960714000003841e12984540c580b4407417603d1080d9400d0240c5c0420602c000c0c80036002e42026a40b140c80240268280c00c2900080308001641c07540038403c41036905080201c5a0220b40007481d20f51045901c80c400005440104582e001000c078a146281c2c01140c5118840c802d001d81e240060151070341000040c1424403800030780210103000808020720202040340d80d050309014030300c0c2c04a180c4a5001581c1c1850b00c1900e01403400c42e601d5004010443c2d14001c044c800820791400c004c09815204142608800740e9a2a0104103d28103600500d940c04141d210f41c8158866084e41c0e02e01030280c050000041440303c80000c07200713160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 761012473 1250 761011223 761011231
    0x3110a021029060c0109020303070f110a03050303130c0b130e0a061206090f120203031008030412060b0303040e04080c0d020c01171b0307091d04080a1d060d09020108 73
    0x440782c003021030b040e5045150149003003150543d9200d0701d41c0040c91005004103002c52005c1d425000004400c004c0040c10b40d0100e0b821441494111004004d403c01e000346240b80c5d020081c115881003011481c00b080c031024040d4074501c03400c00c17103106940304d810300d1030a40c000300c0e000454203082040c140101403e08210f1a4084840c1102b0090a4a003d124400301c51504001401d030665a942c22030600465844242045420107004107101106980c0203569900449803c8195104440c0100d0406004412a0b044450040300f4411139402910b0321801000d24581499161004110000c0e00703500c446200c40c4294010403030141c645105001841c101a0007082c02c200710b401c840c4407400f4607a0403d00990340c5509050018200d50395a558518014460b1030305005400ac000c02040700540c2c0c0b116103401610140403404000880c580d0042807520070030745004114050a110711140c0a01c21480510240c01907103100d5132100c4850081119640b00b400c4c000300d0545c64202034019560001c1e0082c3e00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 761013723 1250 761012473 761012501
    0x30c0c0609092d0c090306160e010e060409050703020306030d08090604110f030f011d19030819020403051b0f150f0d14091c02030f0a03110a0210 64
    0x64515200c0c0060015240102908455044040410f00504001c8841e0041051a90341c00c1107905202003c240c00d50003e5000e10301c00d20035040068402c1a072002d03440514860340e16010a08a440d000540d070041d040601d4a4001c002880000f507815054060a07000f074038140c0300103a6034100350060505000510119505118074502805000000041c4003035100744c000d003240301c101c9180e500080c0170b80c40440000e40d140c803e500500d0303100c94042d80026255446844012800b1000303180c910b44400c2e07c10ba01400503c200035469012a00034403d02c0d03481340e0600403203400008200c100c0f504a800c65042601c40780d21aa0306111004202020324428803411907507590740c0b000140c00568078141101c2440b0700c01030041124041003400030162183c3c0301d15135009004046081000e01c612802c102d407407840507c2025000380741800201368003044018182d0103107240c01c403660f58140d4140e00101040007010794030162403668809401c040c00c1d074582113174082c2c110901280c1c10702003510500442080c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 761014973 1250 761013723 761013727
    0x902010f18090504020f0301021201090b0a0506040911040f120605071704030c03051905130902070209070c0f020a06020f0c04020a120b18040f060e01090b040f110a0602030c0c06 78
    0xd80000c10801080701e404140204141d603685c400300e40400c006000254140d1300106018161840e00900281a5001c80c01d00b042004010341c20403401c105284601d40d00b02104000a11580601f504041480403034084414034069440f49030b084000e00d698010100850300111a01c10040d040c0903858100b0700c18609107002408491908441050181c030040601c5a0b1660710010180074405070350a96001c07807501000c020307106801801d075030302c05004d001d410841e8103408114211188227446c841074000d0003c00c903507500c1202c06e030784948104409848900000314041e0040c1c1d0f90403491030140c03000354003409a0268001045d0b00d481501c404c42481680103000c070702e60300e0fa4489020042505804c4020600f00001c001098082070000c00c91800d104c0501d080005001d440007083c41841e200364020031104151400e114200c466030743d07000340940748031300c0070a0205000041019000340266942040e0080040008020b6100b40d03102c040503070404149902e0042e0180007120341c09800751040c87c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 761016223 1250 761014973 761014997
    0xa09060f030b210a1b05010915020c060d0609090602120601020106081903050f041706072604080d090b07031a030d050c1e1507110a06110903100902010f 67
    0xa1500808201001103011280a0f9050000c80400420701d44076004944002e554031004a4000c0090740c5000d02408a0241071002490941d102208601d0200035400b0b001030305400c0e0304000e042c3e4442c20302071000301d85035900401d16042c244a64069030b0b200302030069940d09001101074111900070a0181076903d030040c1040f039140041880e6800c00503141054281062910342950140107503400f03070a0000f408100031480c0f0788107402401042c00031204882842d51031350b000b21040100e041d103240940c0c45210300c0208600d81602d0043d00b081c40360031058104081c0701c15a000712000b4201c192100f14166051105a035014840c004400944c284a100d803002140d0110b03558800b00e0440d44100800020340e8150504203105004112408140c04507070840d641c2086a44d6054030f040c180c05482c032143c003007809503005072030325804003641e0000741c4030501e641d8540c1e00080103610486070680408003c110b2903554240403001442109400014000410780001042081052220400d0042101c0e542c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 761017473 1250 761016223 761016229
    0x121608040602090414090c01080c1e0d020c0d17090c010e130608060403020106082b030c0e0a091b0c0302061602070b1801021c0c020f040e030a09060f030b 68
    0x42980150070980250756811810040740042c0084208501da000d0748105000d40c0c1d010114109198000036030300c003042c41d01c800c82c01d08080c2c0706000082020396025250300c40300002c0d100140140403001c60005040161941d602070900034407030030000014800e0400c809a40c60710b030303a40300e401540d0317031000b810089002000a8846051500d41d14414000c208039040e009445800100141044c0403e607855418181380281c00b030001406402c60034041e42c003000c0c824482d84c8100d4404038040700c41c40c80c0210303034004080e401032034003004500400c00b1302520003140703460700d0003000c0061495050010740a030a501082074146034800d124400c1180a00d04100400d600058543e00420000a100c01384924a0010ba1401e040350344041140309020541c8540c18006803d40207448900782c080e2920049a909051071040000d003a083c041a800520070015081c000043d610000d000341c40015484004241146903400c01000f200000c0e288000501000d80c0c881032047d5440c03800c0c1014000c0c0d402c41400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 761018723 1250 761017473 761017487
    0xc070b040807091d0a0f06060602120910030605061803070e04023a0819090303021c0c05030f2d030c180a0305060727050409140f031216 60
    0x4202086441300000020b01c0003110581441000c1e110807105040c42c00d28207000c3c0400c9814003940d0140c5820070000c0d0050000c552640e1a10b42e594901c1e180c04a00401c11600c0d1448440320300406a0324480450319407140ea0007420031a584c0840040741a00c40c408142c0b41074007682108903400c04800500c0010707102c0c40a90a802d250341040b00c4400d40072260080b0b20003501035642c0b4842000d8007440400e21503044014a41e00715802c45e441148540d1a50a5900d503900d44802801a8050026180c07642412621f00c1042c2c00303207141400314080f85448540c0340d034118486284140c1e100081030300400710340c10003800d0a12048105090200c0c0342042400a13800010110341c106131380042c401042101c183c00c00e01c00075030000c0c0010541c41e140e080c22a500c4500700c1790315010038481010b100c103110760000d00c8040c4000d0000d4142c0c456050a0501c0060300b030340e0700210303040a07222254010301d01e400e110b0002d9070502c000045444401e641c2400605010141a4484d89140002e441c030304c141d0300c021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 761019973 1250 761018723 761018729
    0x6140a23010b091c03030b0a1d0c03090c0603010b040617070c1e0803100504061e0311120304180c030209090f04081c390c05030708030a020c070b040807 67
    0x42c5151607102050125101e00000518188511281c2c54001c04164059100014010703060720000d10180c1c5803e9294440859400320710070810040c1d0025000910034002198000e1801c03040c1d5058000390b00100d01103800a81056154030800b1805001c0d6903030060b802a41280c480a4255003410f0048000c1c04444080308098241060b041c00d1244452107200c80081142e4007808042d52441c04246000124001e8040c42d481907003030400014003424054000d0b00450074100420502070701e10740d01c07101940300110f48030742c00040905101d0200e020900251000700400c04003051004981891042210020000201414410703c81c106240e154442140d0b401681c24010a2240d140e03820300445e1401040100d059001e020003980408144503041b100c3e410000012008085103c2450350b5010f1841200c03043c0c45200c0c034500411010700c0394401d080c8035030180080d83d1410860303441d5155039910480f00a6a82ca070002001495894104603000003010107007082402c103824007018581700c80c3c03144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 761021223 1250 761019973 761019989
    0x906011d151507020907031e0f060e072304030b07050c01150f0e0117030724051005030c2b0201020c0d0303060e13050c0105031306140a2301 62
    0x240c0010844428011901421040100a07056204070105951400c0d8000141240a99010400b0074030044c02401400085404600001c0c0038001d0600400c1c018038500841010141d1a8100062128041081c0070300a001980d104490b2078030800d1140c038940100b80810007885020841017010882c80e041c400c1c0c1001322440c003e0355032038140d080580500440a00c0b80c0308a4400340d80001c480403190700d8141140c00340d04901c02140e91b21049081c042101e42030f00080d0b900100010b00c0026040e01c898150310743c0c003a60500c10b02c805c00401c0001c03513800b1245001d01468070340c001e01c41490108001442c3d800201e1700d4011102608030080c0c0c0680c030032815902d1144000603e030046a000380300113045a4170280420113a0351503400c000300070300b000d48528184c0c0040140170501042c015450300c0140e43d0003100130400081c5c034400443e0030340e000400345c501c0c1060000d448400901a030141070001d000681c00a840342c01d141540d581103499004c01008114041180e55100254a03000d8904540d030203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 761022473 1250 761021223 761021279
    0x1a0105130207030e030706020d020c0105030c0d022203061a0906010c02010e01020a150b10020f03070b0a1b08070f090e042a08010c0210050105180907050a0306090b090601 75
    0x3520301940e84c114444082603040c085c03030b8408203502e035001030f040c070008029508032506614803900554451009a0340b0105c054010049582c4a5080f0b40041c03501c051003103401da6850221f5040c07101391a640340c00494a00344c0b21780c440e010402c0e40401e030901c03809080b0b902c10b900b400d240e07001030001c0154007002030500a04031540f80305a8001d020b54405260001c1d4480410081c0601c0500103050002c03880c0e00c26141e1154094030305100080440034081e00b803005610f4000c02c0d07100c2c00c4000038001d003a007280c940c50355551030803a58250840c2c00d488001d170300c4031003241c02d149401401d003015500ba03000c100441c8400410034401aa0140303500141c1040d400c2d00b280904018402496052400b4034401121819000030300c4081540300c41c62002a0344c0c260b0b4050102c842200b0700b610403c0c031455070700a61040d214030080000300401a0000d4104c0b00b11100381e66268007040c641c56680c2d0041d10055a030b01081c2c018801c1d8010301c00c1e400039141c00a481c8941c1070007240c003002d5050002c0040d40002d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 761023723 1250 761022473 761022487
    0x210305014e02040c0c050703081303020a0303050319020f0406110c030601030b04210f0807091701141608011206020403020a0b040602010f1505040b0303251a01051302 73
    0x98014640c03070000440d010358140701d080422000c060214084201e024625140e52a02054403030341c03411080b5907015018004462440c0c0303d10b0b5807a0000004841001e207942400401666020400c3e40118860344038251230745803d8000300c4480360307031480ca00521801004184001201c1c0801c950543d440e40c00d001d40300c0861b09064514100009201380e40501c039000001c014030060700d0700d0b180716a120b034087e08a0b00c10070711009074404030562040c00202d40b06440080316540900b1116900181c40c0c94a0021360f0758802c1144501c440300c0214100a9640d0700201e9034500055080380c4e8002c000049008a080900700c0c018003c1c001441006190200f10f410b0008110701e81d01120025500100840460380d15500c80280c030350710901c950400341d80780400300300450400340a000c91041040d01090007075031402040c07001908040c4c0490b64107020030009448000b40c2c10145041c59900d2014841a0f42c0b0249400c50409020b01e01061003862102c0041060b95110035617a014418800400340c1c84182c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 761024973 1250 761023723 761023799
    0x40606082a15071b051005192706030f0e0a05070902090d2112180209060d05120301030210180b09120331050306040204020f090d21030501 61
    0x500c0e000200b42c541040310700c100031030b0254030400c10359030b046810601740c001b8140b040da001d200700100c5078400400029000d00050080804504421003c03160146805041c0103c0302c10203102e41004020a81d910384c0c00000c00407a104000c200031207403004140550141e114a961242c1038420022402e800041c0e1400c280c95152584460316402100d0303002c0195814500c00b04ad0743c46590240002d01c0184130a40c403040070f4021500028960201404003102c5074007440418a4000c001581001244840300006a4104035404613850040c011680340d50440c8100040b04181000d18020040e601302d46540c06405000081c08480505901503031310910722000c41c00b021100940b8011500001c00d0400001c2d40d4003454242600540d03480d1042000b020b4460038601186000302c1c3d4269000400190050030305500074100c4a01e1780c112642001c0c00c1e400011100c6140940850f01490204a41b0400409001c003003c3c000515003402e011660404005450358640c0b031260342c1107a03540c080c006400c55 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 761026223 1250 761024973 761024977
    0x3170907050d050307031202070b0a0f150603200f03181608010c120e070b3103050d0e011b11040609090b060607050a1217040606082a15 60
    0xa002d80800e4145409080160f1079400082c0c0c10350102e13803211400b40d10000117108442d9465404101d41c0140e45415180c000100420f420451801e540c4038440048421499680401001c4a54012900c428118401505081494005400d060303050201e813001000e0241540e038040a0b20700800d1034128991201441d11501d04c41000603100c0c041c1021411340b074190800e61062503103880345031b00748a0f06030740da40890309541071280003508009c0d03052003080f01e01001080d40140e10301c25051030350780c804080c2100f0034850703900301c460b0083c580e401c008000b001c2c0160700c041c0b0031a0824003215404500060000c3e00010300c00016100009040820841c0407410304841c4a03014108000d0a41ca8070300c1c10300104030707011041c1c9450206000003251890444201d41a2961200141080101c83e5075094480b181d006d41900038010346a001c40c49045000d8200351049018040100b00a0328041d115420816002e40c44800444000629480e2510300095482807400640ea201c4030040d061110500c28 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 761027473 1250 761026223 761026229
    0xb03030a110c0d03030b03011b0509060904060b12041514040206210f0105011107050f04021303080309060411010c0b0c032a09010906050a140702010507061b0207050303040303170907 80
    0x114001000ca09045d030591110000308804e900802c0f19014903030010407410a030440c2c86002607000c00207600c0908207600039180b1550050000701c0da4036107609c0f0810050b042002001c1903c83d0002c2000240250401004252050b501c010055060261000407003800000e00281c060000002c03002a4107441c00d000c20407510508000414074204842c917074500c103000b885040c0c00100e00c2c86400b84042d10104558048039030050111b20442c02c0c1800703101c065003104800e50351203c1d009600002184002d8000d51086a540c0064403291410386802058403a194580380d04001060015a0000328400d8087c3e8101501c0c48200d52607540e400a42e50b08540d100c09100d112014020126681000318006400506d0098a503a06000e03119001224180078851101000406c00e5070702080c140840707001000c0d014010b2600c030303240002940f60f00e0152940328880d1142d5820000341041d140d9030500802000c1d00e4220051464a451610300070003161201c104a54060781820106140b034104000b40c0f001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 761028723 1250 761027473 761027479
    0x609030e09040f0c0f0b040e180f0d031104081b030f150f0a0b03060714040b0319060609050325080a080c0705040501051507020a1a1c0b03030a110c 65
    0x54a07041c03038075080b0300c81c06503401c0350911303110304002c0f6014104e548150241d424010019051915151020881c0180901360491103130084030300e051101004d01200c00e0040c90b10005040e24a00348030010101c0e40010002c4020310030600c000c4c40030780703c0499511600081c10b55040180039410001900701110358060b50903922a2a0f81e90500d0503d01000c90301c82d928282c1250707600d81d03c042c5140107035805404400c0d07250700064002180782d401540103c804412a000d12410316444480141032a8015181002946d0381c0b08440c40e031a014901a8101030505490004c1000d450310010980d282e107240040490030600d4040b148100c01c07510440c0004021007400c80302c0410039401c0284035680106ea03c810203004110003c25a410079004040c103c40c40600b280004137040c603440195500403110481c0c0c0940c600400107220024101000b0031000036107200c0c0d80c0c502d240007007941281c01c0f5800c0c04010605180036804583e1b03000c001c0d80ca0312619402c00707044090701c000b003040c10701490400340d41d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 761029973 1250 761028723 761028739
    0x100c1103010e0d1409010c1401060320121605040e0a08030a0209090a050708310c150212090607150c08180f070b091504122306040609030e 61
    0x1080040000d46501c0c1008607255070903041c052903d604d41c5446000883c2d07010034110303038080000400111042656401c11400000e20716280d5462080c00c620161a401c007407003580340d42000e03d02e0111200d55a891262000300101101d091070380020441511505120360703134603204204110428008100a6680a4000740d6a41303071030000c1000075000603402d0b50003003102a00040e408032a5100d07203402143c2c035840b1030030241c0d90007121040b003114040c44c01c145441003800d0301842c001d81c1c40030800054800c0340101e000508001c0701042c0300b45524040c10440d07000028001e04544148219014488140c403a2541e502103400c0000c01030440d00d130100304c06850040c104100550254440d4014032607110210341c0342003150f24160740c2c5c03c2c1034041041c00303810100082118900b840014032a01d50007600744504081d50021000d542e400c69400316030064440294441044800a1880e03405245900b6801c03001c2c1c0c0c86012259540070051009012a036640030100900d0b008400203c3e030150001d045131 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 761031223 1250 761029973 761029991
    0xe030313080105150915040903110a05060105010210020906071509050328050a27080a06090c090507050a03090503070c120201021203092e020c0312090309100c110301 73
    0x1c0d00030141140c2c0d05151421600321050303603140c0750400c540a0321030804441607180380398042000900c041d038000c80c1842944422501042814007902002074001c44c0903000c150301d000d00290a00c046403041150f403d104200707800c0d81d540c403001a144070a822114441c0c0303108941601e40c1c010803801a01504510003c03803407106018444101903107031410000c040703250100c0c0c2801600c080c06074038004004510380780465041c41c1c2c42c8050010598500c0e04140ca60b99540310509030502d0030b49101555516100e03100e01c07091015a1407540000e102900c410405e03450100c400610500440700c0c0c40040580f40e505101c14881c0800640b00c0407600004121050741e610410f40d070403030f0b6060901700c2c090300402c0e44e0564448603400580344154032010150410b00c2c0b2a1121621070301030080b407100c501c000b40c4440c140b0725000b440908400c40c20400116a205a110440c0f1401da400a00d02d104a074000c1002000c2525000c4085030341a40b10309200364007040d80d2030007101d280184084550150300c0c2c0000c203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 761032473 1250 761031223 761031239
    0x150501080a050c060306150c0c0405070302090f0a240302040b1b10050705030a1107060e07061701060c0b0a23220506010b0919030507050901081506010e030313 70
    0x80e01858402c90486180705140b2040c040e00740800c03250580d008413590030b0140c1400b4208010120310b000042925905a05240058210b1703c080d00c02c100000e0340400e1100305030820440e041c0104100700d510100703051901d40380c1c40d16241c1c141c10700c02501040d03ca1920b100340c000d40548001d0003202c05240c5c0c44003c500c100c40c1d150040100740b403d03944260b90304040751144c1c42c8105405840b045d5107482c0746603290178014001d0030710300104144408082001e800031a00c2c0340b00740d94132182e61102900724580b50541c0107050716000d0001d48001d1a00300010851190400100c100b0030780d00c00341490303e41d902c2050303241c002c00820307210b0090490f1010380c0050441c409040780340302c0c41c000784458104040c02190201a020707540c1006006500c40c400501c80662010301038030305c498009046603420039072032082010395489580b0840305603101203800d0100d80b03440d41e109400f50000c080281001070a0350240e43c0c83d5400602894180003e60354840c0140e1024030841d120000c5846185c00e042e0750350742d14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 761033723 1250 761032473 761032483
    0x130507121203061706160e15120f130618020607060c080c0705031606061a0705070b030702251d150d0302030a08060402190f080c0307020a030c15050108 67
    0x4000ba14000e004281c0c142400f44000540750018000e180603643c0441d400042000001244184044041750158503910f107101c84980744402040340361120705240071159005d030042c0074110340189042c204501c06420003d581c568a80140c4d011445041c2c003841011903545006000c2d400c414002a6001440180d42000e04000b031541e54422003550360740b14000d00d600501c80c008183d0741040080d0510781101311460079940b80a00e0002030401c1d0390710340c441c40b00c240c05140c0440c0d540b404910303103017485014811040100543c0b4030241c51440c00c90b60003500d51446600c4c0305c400100d400380d6015030302c0e01d800401c000340c40c0c1500f4842c10785402581e5005c8000c02201c030700200c9801002501c6440c03c044140c0103e03668950020360401d40c200c8801e4403030142c0100503075003243c0e007031001c01d91600100000f5141c0d880341d43c81310700300c9034904000203240f088001c1922003c0481002803215056000800030b50a80d0940340c882c9071380b12145401600700d8001710480401d2410a0b00200d412034000c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 761034973 1250 761033723 761033753
    0x50112050f0601050d080c030c0105011d06010309030e120708060c0d0e03070c060f020c0d0308160e0616170301080706020f01090b0106080408070b0405031b010203010e13050712 78
    0x8a885860081041030b503200000d000d2180c205100728099000580c01901034000c3d00f003402e09072420810341070001421507600340d00c040340d81100d02c41c00c9949220b200310000d40003402031030309104508203a10064400c0a5080f0364500460175103c1c0351078941c0007441410003a141c294207440441c2003106071040603030418540003d0701e52400140b12141180001110703000380c3d100545c0d1441c940750090603078512040300b03d10400c0d40a200120040e0750f461981c1e00ca2124425140c0d881d4500b4091001203412a205001c581440040300410703441360780e9401547da40d00710000125001c22041c2c90304000c03603c0b14003112000c922002c80003040c0b60300d01003000e0041e1a540ea0890b50010b160f100315a003603588406019100e21110001409400d1140c0640c42d8880c0c001c90506142c06019030751036000c024112010b6070150808a0005a0103447c60f103601b000001701c40c02541954106040100d104801400280c007401844a00c80100881400168010540008100100d460754100f16840c1000300e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 761036223 1250 761034973 761034983
    0x90b040b150a1805040302120a0f080c0a090b030a0207021302030604230103020f0d020303070c060305060103092a080f0703030e06180d02040204091d071a0a0509040f050112 76
    0x75169a41c100a012082155090600103424a032402d1140c0014440908243e045019000c0c030701608442d248000c2410310301c150745038090381c0008800117102c00006490148044d50801004521315440310a45090784c0031800c0041c0d0ba0340b40c5140003402441504030094020788800c11221400041c2da007c4d621540c3e0988060140c41d0304c1d038a50409110301266101d800703a01e400c00610250038103801d02526800c028141c888250041d4000924607040a00115071600e0f6106060208a0b818021240c01c0b140a09040c406a066a540c1090907000300c1d6030141203000700103500000440e0100984010070701002961b002007014040e05840d0f91003401305a01080e0080003028003402d025080f944c4980c501c000703503941c0070703416000c1080b200305000e07080e64095024030000c200d150440c400c1d060040c0c1c141160440382d40000c1c120508090781640100e01c040d2100003d1160b00716850101d03010148a071402030347d01d0254100080c02009413610300d1801601c2c1ca000815040071417088103100b28011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 761037473 1250 761036223 761036251
    0xa08100c0e0406060c020310090b161709011508071a0c1606021501050a03080403060525020d080606040b0f03181606230f0c07030b100501091d010b070303090b040b 72
    0x84c0f0100e05031044034000922032b0103000d002899503004096811070700c1085182289442c40200aa810561000e0320303030944c0c2e0b954800e4500c0b254111203004500802c4801c0240c440145041802013030581e04010407a0410000110b03041001c000b804100302084450001e02c462544400d4000d556050101030a114010384100204140c6000403d2000312540046583e1529003142e6405000e03007405802a084e0750414030304a0001a141c4401801200080c3d004240800d81d081e402050860050f12a5000301000c00090020a41540031034100f01c1c05282081d5582e11000780c031000485d02440040326500601c2c00d210140c1c911800c464045031020740d503082600d610741c9804034043e0f914100850400301c1c10801c2405007031610010b02000e15a075030540c1d103055980d4985148105080300e1400000e402c000007170003d9070b0070510f800702400401905210b402c0c0c00e075201544c0342c101801045181c500114000d01007601c240c000d07500c082e9000007041c2d81410240b42c05000705a06540780288400780d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 761038723 1250 761037473 761037493
    0x110d23060f0907080c0103020c161410140a140712090e07050a090e0c0d0203010f17030403050a230f0606010f020a030905150c0d0c110a08100c0e0406060c0203 70
    0x14400c0030340e00180080e00b179140c11000194001c0d44144101d1040d4051100c80b0719590407612803030802007c1103840804c003210000100404240c468402a05000004441e05103400c403c1055403213a8001d800d0074132400700000004203050180c070074001e000f106000d5120160741c0c0e006083e03c086548480d40440726450b4824252444e01400426400007181c085007005000c10781030016401c10340d80c908461034000c0085051007640c4c0b098000000f207404003842000440480004038040320050b9020318202400e641d2078035103071200748602900f07000c66a05a8148081e171111401c1c0280c10760000c46030700d029410100c5403201400c64105002c1003100240a079418004124104c056925030346542c810307814074041100000100f44080307001c070002d02c54041c031994100880c030017424040c0c5502c0700c526403038981401e084800303915050081c1501c0700304003c0c06100080410400c00002c00102d94200a9113007100c0d113003880601e1aa2203414124000782c2c150300319484040c650f00940c01e0f50030f0000d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 761039973 1250 761038723 761038741
    0x70e0c07082b020d0e100b1c17040e040c060206161b0f230109020d0206180a1706090d0206040f0f02040617100603110d23060f 56
    0x18000c0040c00310328080000311082c071509080704140781c18510202d4100803404651a0407038000c4074008561994602e02040c0e03a0b0010448080b40c441661810301400d0284004104e1400546060b00d041c004240f048208004110031743c80a005944c1240d251100d9850111a1b1400003d0f1019034003141c0303208005c41c42601c0811304038481d2178410390031030351180800c41c102c0c5c005642002c0c2c02e202c41c0016001000041002c008200e0a5000710f074a0f54489139501c4102000d40c20165020407540c2c9016103850058640d00316140132150100c0d035070740c0c4401601c4003031070503641078100d0607a010f00b4a45010070b0500d54104614908014001221155600c03d1099a0380e00b0141c1c8084000d40e2140f0000f60000c0e24000045580502c02d403130303c00061603207034017090a941407034101c0c0761062151000142d5200c000c0141402140d080c0c1d03400c3c0b10390385c5152a00c10400c40d04010f042d0180070703080d40050902101c05ca0036070030031a81c40146094252600c1803552185010744402040111038004904100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 761041223 1250 761039973 761039977
    0xf041509030207050d050c06030903041509080a11060c0f06071b0209130309270b0306040b010509090109050609010e010617061906090e0705040b040606090911040308030702070e0c 79
    0x10741d0580090003050b00303140c00c00c8042488400101d805104101001c3d22070340768079000d1401b400a03000115110346c246008076020028400074081044660ba2003000441c0f00054031070b8550750800d054081e8580031001143c42ca2068140014042c4a14001c5000c0c0401c00035030184104c0441d0385491440c001200c1c1805a500c02d583c000e540140014081070f0191401e40d00082414030a09141c420b441d80c071200c00b00c551b48406070348005d6400d01c5402c24404021801000c0b40071408a0103482d0603e016075031060129818016030b4040c5065000061103280309500100e00190400225903c2d45011000e80c0d010f1322014810400075400c0a42c002180d900c00c41c204180c1403030a80280001c3c2d030700e0040900c0b083c04c2078850307020074640707a00c80050020040d110b4001ea05480c90090082542080240001c3c0c0702002490350181d850087c0400125a026412106480303641c900480d442007840500d001ca401950006095000d0010a003c0120340010f1240300700c8076110340040c3d884e034840501071454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 761042473 1250 761041223 761041241
    0x4060c09030b01140303070b1510090b0a080a110c011a04050403210906050415050f060303070305070501020408030310150203090607030c1b08010f0f1a060304080409050f0415 77
    0xb20754a00103006251100f50000400c0b07501404880c140030094aa006c2480010384d03c080b07001e45170a1307061032941420344502c410000f0034201954424900b0807a0300311341c4603124002d4100002400812500d101c20b402040c000303021046070070740f039042d001500c42c020f2641d0102d1a41c003e26880c0110a00d0510b070044502c40c0d50182c41c1c09900840304400d8041c0e441070a01000b020a564141001c0014440d10405001394001c00600201202520a00b401c840c0302608001024498004001d05a54000219103807d0340c940741c0a40c403040223140c090b02a000c0c641021241d80404410480f81a1400c0700040488134501c91042c0030043e9008241d860b8820004904d820080411659000c240200f54003150329105085980b10b00c2607540d03040c140b4501c02c4d0040038099465101440c0c600d10b0501440281d40d02d03880d03040005203252204054122800d41d903050041a010001800740111501038400a20864605100c3e81c5800c561400030350380c04880480d00e983c60a040300f003150409103e00241 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 761043723 1250 761042473 761042483
    0x8071706010b0307030605131b18150909022d03010f032d080903010e0c09060409080c0a03020c1c031727070f0b070b010603050705041d04060c0903 65
    0x80c0d00b451692407055100411400070715454100003c2c0d01c5c0c13030345a900401304520410001d00011030a1480340200745480c984400c0280b90b070000e5100305103450040c011101c040c03c402500700c4550800b6250012a5444084610f201049227000f00c1d10800300d60082030000c00389021100304641d107411050000f8000e8507e83d60340140c0a01c005203290012003008004188032840c0540548904481c0d071111a404960710400801c5480c510b06090042010441015000d82005042030000c12850f01c00141501e204079181d070010f6051007185030480d10749801e082d06130b03a041800f50801a561300641d00ca4203010b015a64030180060900c0991075111580c113a07242c14900e114040c00301c0070441c0c0034180c01d4004080c164804804d4000c01c92154443e18158040c04406140403803d92004c0340c0755101c41c02011041081d44005102e0201c8103064600d0743c14005510386608400b2560f5014581107512251840c00a0300c81e00140d101009204510910080c00503407215203080390442214070000304 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 761044973 1250 761043723 761043733
    0xf030d09090c030f05090a021c1e06091e0b01150c02010c02010306080a0b040c05010305250c0821060604050d0b040203032b11130306052509080717 65
    0x154000a401010326030565190102d090b900c2c0d001344da021100c0541d407215441d48441c0c1424214182095498592140220740200300c2c0e52a44465100c0881e1600789207940148030f02c0c0000300116a0300401403c0d400540510556610b2000883c0c07610180000f5140144007000009010101c0c03e01030114210780d07038510b40c079551184d0064a003180c01050480c18152600f4021999810030090b1610440c0116a2001c031402c0508004d810002c2c19008141094104420445050550100610802e40508000000c3d11a015040b40d00c94400d00c0b00034491800000c08880d640410980d0f02010302d49000303103040607140d4600b048075034800c0340b090759006150203000c2c0c008506011095633009002909681c546200030b801000707640030191840d00025010880240b03603a101d84104400036410705086440c22b0380c107010584044602d84002080142c54100043e001c0418107040b0524003900840751000f100b0002011b41034086c1401442d05900ca910300002e1381c3c114202100101880300d03c080c10f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 761046223 1250 761044973 761044979
    0x3020606062703070e0a0902010e060906040632030a050a0c090b0d150308070c0603090809040b220f0b010804020607080c120a02060f01120b181006080a020f030d09 72
    0x3802c800140c49120ba0502550301d00240a45081c410140300d090383ca6400500303084184009080900482c03a07060081c00d00b40030054480d140c02040b81c041c2c03a414140307422032184410440401181c000c42900c038080c90b000c10901069402d001070360107840c46d250180030554a066081c021220520300e04000110100d02c100480c2198400501e2200d5140748040303040340803480c40500403003540c0d00403280c900d4000b072a101440141d1003c00c01820141c94148103084207a140e0034414041c038001b4902c6241c0c3e51030030481c260b89518510006420751500c4280d00854603111500800309000d003009000d0a00d40b0522040d88500c041500c01d540c020714260030304030035850707041e015040003048511500c2003441050058510070040c14481000c0d900918003482c040440b1903500c81c1c10f90181c07880162010003000001c54103803107940d20540310240001900203052146141c0a081c0b500303405200c0c40c03c40d01141d101804038040640c68003e4420380803040322903090540c0e42510400400c00560703d94418 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 761047473 1250 761046223 761046277
    0x907090c03021b240601230c0601080607080c18030d181d0a0f09021c0c061b020d15020706020c0105090c0109090b0f0a0e06030106050a2306130b070302060606 70
    0x2264006806150004401e5106100d0380100c28503003207070000011700408c40041c0c10004108540c0034203440406404a8209218068404140079000c0c410036400442c49056403840e100903803801950080c200c580c130322080d580142550720240032800320008021404a00454900a134110321205403254900568411413140001c050410600c0d03640c0341c851007881c0c05a07840c544400650403a054095a0002507480d205605c01459030110f001c0c80b81e2010008c80380303059a03080081240d010342d160030782d032120341c5040c2181c0311040102c00c0005102048050a020b0726078068403000c945200208003a0701d58003d600c1da50162a40190b001805000b4240b1045455801c24109101c019064440c5128083c00003007115440e60410b20100d2100020800c071840d0901400c1c00504c801d850340041c4604001d200d80700304600c01202031891403603c402074000d8692408694405030b800751103d0515440c1c400046d190341c40000282c0040c425980400d01c113181000441d0b242c61012b20701c44161822084034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 761048723 1250 761047473 761047543
    0x7060503060d06061e080c010e0409031205131a010f050d060b03060f06010f0e1e032407090603180f030c300201140f0907090c03021b 59
    0x180c0d503040302e591009400000c0003402904054085d140000b1092010281d43d500003c100342c0c04142d8540c058082440c2a03601710201505040040d200032916400906042c1e0320300000d50840035006240c0300810000700844003e05e500740b40b080301100c00142036040000d0582e8028011a24083d0b0203107c100001d1601900002c00d41c0d11424000c2070450441000a082000840b078188607209d400e810400d844d0381c020000500c1d8661400c08494038440440131074407805c194040c991498000481c030011640e403c1120001da07400300b09410750040708140740fa524840c01980d007507001c908030200209250307003e8095000400003152005505440d15114074104554000c5c042d010f01c843e01e440e54020035001e48100300b000c0600a01c1c1000000c5015540e41906142c414400459141810101284001c07040ca20b4112010006101c0640c0350012054281141c40d84280d01d600d2900440361030722901074020744440010030761081110040c6405241c0c403444135140704c01c20310a0350200ea02c0c0507010700c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 761049973 1250 761048723 761048731
    0xe0f2119030b030a06020a08010512060912250501091403040b0901050f040506031509181005100e0108010b031006060e010c0305190206060f0a0f03080a02030d0507030f0f06060207060503 82
    0x1104c11162082d1180b00803a1310070f1540344001000d000060041c0e0401da19031200f40302078000100114509009601c0c0c40c0c40800001d0125142c0000300707510b010403100e03910b81c01001013200344030784e42c14580b41c050700030003900108a030380e0030a80d0b6006c503000001200380c0b800c0b1039020080078600300c2c4580045071f10354011b41400169020074071002c640e81d2940405103100700401c0b200400320301c0d02441081041000100b1010760286125840e10304540701181281658000050101d46500e46a80c9a030607001e03150440e41200308800c0c0000350904054100404819056081d03031144802916680c0c1030300c805001e50000301d040400c04803000c1d440364010061503806868400e0402d20b90100085504144158a100603030004043c0412843d208200a00e03050084030646d0311a45002c40000c0d0f414801c0c840a4045c1c0400716a0b000d0b140d00900407134030490400f0508000e01d00d030640002d17000300381e52550307074000714500580001210b8180c4035140030b80701c85400a102c1a480d1401c01c03078003944014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 761051223 1250 761049973 761049979
    0x602030a0f051b0309090f190504231c0f05040e090a150605030613050c010503040302010e06131416150306050301020304080403030822150e0f2119030b 67
    0x4002c0f2948820f08410b11070181c0c4020281d9076641c00401080268807000d009005000102000d0190001d5980c43e0b15020407102580410980d41d507040c10700c9010b010b00c10308904002e50060710115400040750000611402100c1340349180d41040085407512150200d0501040040106001d002546109a54001c0170101210b214484554618104038182d20b01c40c10200d449440500640ca803c1c400182e229100400080c1c03180600e440c0c480e034034107002800d18144130b800800314050510070b400c4415801c0c480703001c031455400c0c0089c0210064111802c185c82c400c0d020b548000c1100800f08841400440d41c256843e00b0b20304100142b0194070a9013549814103a540b200040d450b10300380003841c80740e070088142646607481c504000e46104001006816880e0f400e21010082040c4814403000c400c1e0030080b03010fa07103082c40340680002d1030b009081d47d800d8440c489a4803500080000e050300d116003145101f903400b024a4800741c01d80d00a480800700c0c4c0c04041d90200c4c513428400d034401c030a899401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 761052473 1250 761051223 761051227
    0x100506030c071e0c060f05091e033301090c0801030b190618150812070c080115090c03020405030a0b070507201005090915120106120b100602030a0f05 66
    0x3103850742c0f1140100c1c82045614191441c010440c60390041644900040c4c5410624039001e800e070300158409503940709010b444941032844036650b4804101082c80702c0c402041c500618090003055191940c1c4003128407802c819042c1c0081005c21540c0558240011107171030300303000743e400c40d03681c01042071009005102240f403111694032070444038020740c1e00030660107588103021800e001c4108242c2c1d5440c00312416080420314100f10352400080c60110064550400d192035640320b107894588501d041e8422045503003040d5904800403848880c6108840ca080010802c4440300103050701640964803030154560058511320010031032540407079510041a01d4264a01083c5517513060035441d1100354001c1c84074884c981303000c00d81868464520341d1070450401c60705000746100081c41e0000c1c0280000c010800d080c4000883da1645003440740101e032444020f00081ea00c0c0e6000d0a0307100e2803400b0079a101d10000300810031011b80c07034017840261415540034618200c2d01005c240c07150791400010070200a01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 761053723 1250 761052473 761052503
    0x20112050c19090305010b090606190309021807030c0336020901151214010b070c0509090c1903080708030c0d06060f0f0801050f0f190902030906100506030c07 70
    0x1d00400180950150320f0b05080325003035041c40340c01c6908010105004078140d500703101c42c030f41e40d070404d883d1018000491000070f0000142c080303003c1c1086817002034100300c0709842c05005d100d40c0e00d001849051966010071101b1884401281941c0c11102d41c1e25000700f039500c0012803600c0241c280641501030f040e400c00b0081840d8040b44d09000240e0000e0706015144c4000e68817143d102074070030b590103403c2a081c09019050301c0c4486080c0c406200b80350f80b10000007028410090062403400c01004020007101041c54a070b81445d86600440c0106842411284000b103901081100c214040e43d4220000070704000d90396440b0728407075001400750342500703030700340301d0035511215601640c00600010303594110707000d5030507a014180d010f02c20b40f4074080c0300030203005201a4469201c188006d050484011400702036900100300241c0c5007600c081000c40704810081120052500114050340c4007404503200380e69008407444903e042c0c0d0145980c0098200081008191703614050000070340034045140d03800034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 761054973 1250 761053723 761053747
    0x13050f03030103150507021f09020103060b041203020615181e0a0203090706021f020304020d0f0503090907030c08070e0103111b0d020303131502040506030a09060c020c0105190311070627020112050c 87
    0x4184e001c0e00d0410350c00ea4100ac105941844419080b00f0700c9600c00080446d400c0c00203840b00001ca54021090210800042d1170101c40f00701c2229010119105160a06001e141000658000c9944d141e4030f104100c03000035074501c00511012035101da098030f44517404d5015070b09006944060303c188c0e80084820b910b0408109440040e80f0340503c208000d6607980355030070a02a00e80340c003c28400070b0504e80390b0b038154a2500704190a60140c40d41c501002402c1007100160000c08035000d0b60000610003141d00b501500d003009181541e488148105c54076401154800c0f0fa69100854a056905101c001e039140010f000b0310040c400051600805403c3c50b89410200c0c1603034004490800000391118440c4c020b01c0100e1150785902808c500c060f00c412280c450010700310381300d054003084130703024002c240c049030600c290b108100c00c40b0103050319555485103007401400790440e0f928070b040d0300c0314031104248a501c404024455241e810703112030301c4003050060503100801008040c42c10003101080b011083c58 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 761056223 1250 761054973 761054977
    0x60302120606150405030a022b050f07090501061713020d0b0a0b04020306012106050910060906020105010e070f090b040605130f0305030313050f03030103150507021f09020103060b 79
    0x18220001c00091504a08124050500c454048000758040005000c991000315602e00b4080d01070319003800801002040f1246045e841e0914081c55440034880c03c2084004100c0356220141842122416901c540c800800c450081c403805001c144260104401650251a040d80c03000b820600b80e0101d83c01a008902041209501201c04c1c0d51580100540f8081c0751186a104d441c06903411421844c0040011341020440071041c6069040c0381415440300c00307a900000701900014011580b41d0812030401104d1000c1c5014540c0840d000d080c000c80d80701c6c414400c4504a900c994a10300342526022400e450310004405902c041000d140c0e4007003003032010400280000d050f9551103a60390303901c6c40c2e20040d0041840d042586141e5a40b001000480e4000007a250028925550007681c100b80345400c030f14107040c41d0080603a601002c0000014000702100000c101800e1001c144665510114108c1c0c075501c1540c030004207006014842d0105c02000e82c810100644181800902d490b2030b419844942e07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 761057473 1250 761056223 761056249
    0x702010f2706020f0c09060d1e03030209030f010203040f080c0142030c0501031112070c12030c080c1c0501080d0e0102030406050301050907140705060103030e0a0503120d060302 78
    0x10318075201002115810486a902407180101030903c0c90311801c00500780f142c000d001580714010800c000000c4c0003a41e006845052001c800c2801540590328020340690070201c101d82c483e016a81500c41501018000c680c0f040b0390026054205103911750320824150410282c0c100e1965030703030003041101541c0c18035110b0f5541e004194040b041e0349200f40400d4030051440c2c24032040c1c0d12400100002082e20b405402507800c24240400e400ca00701400054a0103031030441e080c81c011a40034021815001080d07078079140e000301d64036192040c0a000a5094030100c2c0320010000b06100006550501c40700f002d04207810342e628800d140c29050400e52000d490080c1c2014516800801011031159007180e510b0440303603820300166007424075014000c0d2990005111341070040720a82c000a13000d6200e10002e1510000c0b18614540b00c444504201c0d50b40e040c01d00003200450079684058509241030411076040310f10060040a42c5490010f4200060b00105000108103481e90f20120044c1c2d5034000034004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 761058723 1250 761057473 761057537
    0x507230319050406060302120d0e0607080909010e190c0f080601020c03010c090503070f0e01030f0503091e03010c11030a11010b060c060a14041707030221070204110f0702010f 77
    0x175415801005007080e81214070800b107601036240c51012540140740d880d1192070481c5c02e00e403a213a00d030038080a10310515074116480000c0200105403800c40c401c216020764a0403034a040940340d441d0024044801c40402c001c04034081444402c540f5105005003640008180b040d11a015608070101e825102c003810540d0100b407240d0f0003031005013030820451009203408030343c03460420f18080e041b03240700c00b040c000603207035411001e69141841802c000700c4000c20006004071a0301d5114408114900d103081440a1095080036942c2807014070984451000a0104006d1403408041d4503003604c2c0800028103e085030754a580c0d8413400c0d90751350005051661340d01c2c0050310072071800964150072519100009038059040105000c0400d0171120750340c1030b003003400780c2a9580e02030a04050789092140b19a880b002d1101307034550701d15038681d00041c00905100381c9050101404c9040064035a024009400d0b8040c00e0510040000d0340c401c000c440341504150404246149120010009140910b660210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 761059973 1250 761058723 761058731
    0x40603051204051807080c0c01020724140609010909060b0405040602030711060f071d0a06030209010912212303070e2418030f060103060507230319050406 68
    0x703c81d040030410358007050100507001c4498981100017400540f005050012502030208010312a80002d6049880158204d800d200000b1440140d444c00640b00100d0a0051800d0038840f00940e1400100c1c0d80c00344000078058a02daa00b0402d0b03180007082607a0045c0d50300ca84030700105600740c44600c2890b00560284102607568501041c0240003044100144503095200d14100002c6881018016801440c2e83c44c1c0002200103d00c010040317490b040301c049a01000d45000001e182c0d4140c0c1c01010301030401c4e00d41040c1d5a0796000710004540103000041c000c940c013103140b008421036942c0800001340050928a0040c03050000c2071040070004410005200c13030000034400b441e034029120080050b01180ca006124101d400c0c213841c680302015445030100004621150100d040002d84148a01c0240c210341000c80601c000d0380c3d071000d0038882a145280303402d0100c0d0300c1c40e102c3c4401d00c4445c2c030741c5183c10921508110408655031300c010400541b00381004100400382c4442d010355030185005400c081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 761061223 1250 761059973 761059979
    0x2001090b1c05060a08070311120d0806031204050f040b0625050c0a05011b0203071e03061d030a0e01020307140a05010b01022a0f0d0c0905010f0b18040603051204 71
    0x40101c4002500443c821303000f03240204144070001401006495200030101d0000c1440c84c0814141210303400300007c0d07400707554952441c140d80910312610816041b812110103030032849110f1074a10550040d40e0304115001e0600c9842d0906070450500114081c000c20f207003640f0050810800307403070909078111200f89410240c0502008002c089491070003180d0071b118581ca0400064241204c040d40e401c40d03c141c5100660555500340080c10041044d810916244500580c003484592100d0200b181c200340380000d409c1c409070b890b040740b00c01d02440d036005502d031260442c0182c50701140020b009045200411141c1d00080701c1c1005001c5c03840f4404000c10011289180007800c5d1201c11407154115071102820902c0d04c1c030041102402000f140030040501074074070010a080303240c54280981c001183e180c40380d0800003500008400c80345103000c104190390720340d024040d0000240c41000c038000c40a105424048080c0741560030200001440019641e6480d84d8075400c001001c40403180d61103003c03c0c20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 761062473 1250 761061223 761061277
    0x150e130b0906100f0608071b050709021b0105040804050607050c03100204031a060f040b15031e010f0503060115020102070f0606050f0105040807090c021f0615020105042001090b 78
    0x7010152420f003512013029800c4c10001880244004c12200401c0482c1c0c504e07074400b05108481d0900340d5040416030b074445440305c075080c019500400d03c0402038581c04080d40400c1c0c0e4180308060040d030788009600e1070240360104002450b0030020080e2514000c4901300d1055640030000c4002e544102ea901607159865410a071343c040040e40305034500d07060804108501c0369241d410030442824226000a4603161520200726980e0140742c150980c280000107109000c481012000c0000550202d0300402e0b03a01c41101110740d8150703110342c9801d0b902500045c00400c2c004c0041e015210300500c0018140302207038581104034244104180da42555804003803010b802d01a4040c01140004e080092509203400003580d40d500b002d100350044580d940c07150072940c81c03081c02070409500d00213000794032100d01903d2520003020301e03106d0340b25480d00c8070361a800018010301846c0e100f03c0c3c02014500203404181c8083e0350280115181c50b04110301090301041100f075600141a00b01204000e128064083d075001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 761063723 1250 761062473 761062501
    0xd17090309090c041502060f070f0207260a06020c061305030703030b1203070b0f0a09051207061103091c17151f020c03100e060103151e0c12150e130b0906 68
    0x44010001d200ad2050b0002d03800146c07400840d107072044a0b03140c500112051140744a528004000b10307010700e0900e0001d00c51107070041d01c07200d648d0310195201c0c1e442d10075407900c1011450340010000d80061040a000c24000c3c4c0c0480b03440705014000596400b616000ba0f4210740c4804000c0300c40036400d1080c8040011008030860340501d54800c104403041407500da40d40d0b5209848002c2c1c501c0400091035504200303142e003013043c210401120b95030712402c1a141c2079032140100c1c90503030039050307405800080052240510041c42100403070b4100d641d856805280c641050046081a001029440f080e5170f10891121a404980419405418110074401c00c060400f6424001001020304041030786001103030225800b81141d074408092210420b983c014000603006040c4964a5104c0c0c615212103031100c241c000d203080080903550341e120504c26045e03547c00c48210b0300c4100390702d1071080c3c01400103006032036078260001c00342641d80b11a60b003d6900c440c1c1d508000c4410581c260060410700403403c1e400e181d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 761064973 1250 761063723 761063731
    0x4060212011d0a0b18092506030f0203040201050702041d0d0f090b070308070809100906062c01170a05190c090207201305090d17090309090c041502060f 67
    0x20244a8000c2040c00034410200404e4540c02d1800c890300440e000400c1040b18618814000c41e001f40d04002c0042d035080303610003512801c808039003040c1000402003410b100326441241e050b12614280303000c0c0c1e000d210050603200142c40c4000c04114403000044002c010344003001040c4d6031415034a240b001d60092942c3c04036070014480c0b00c002d02003000040d030851440d42d404071141c078040d162555030480741454522040180880107190482010501519410900603078102210756003055400c1070b5000030300030b1a1601260780084140c014011035000c42500c85504001404031151880e454480d5800d0003412800354090507204181503041065044001f4010480c40c80110b0801881c1c1d1509100b0020440007000e40380462504001642e40d40419100c03041ca40500400a038504011a20f9580c141203c4440c04240044130f030a241d0800480c119115003841405141000c171043c0c24007424070000b601d010014039060201084088030019140340c0c1c1800ba50003040c00d820300d010000f040c03c5000d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 761066223 1250 761064973 761064991
    0x1e080c0f060c12091203090d030506030a03200c090901051503120a0320120109050606181003060b0a1d0a03050a030f0210020c100b010f09030b04060212011d 69
    0x25040040d079041410554400d000c00702c3d005449030352220205400c054602604024440000c03003401084540014103072541d1100d502c0410403616480d0805a6a2036481001400116041e1401c0801007400201194080f900c4085480e40320480000951811085440041c41c0e950b803000c00203101601134042d43c4103003064020340401c0c0540c0d85c1e046054071503040d00c8403e05499421000964444401c040d162040341c102e65074640000b1010105940002c1c1303c0e03021f4250601012907442d15102045404021404216803880c1c00540b003880942040510920181691070320b0018002c852a802010100b000b562150883e103400c003024069440300b00d148601800c3c407004148005075000a4040f101c50305410400340c440e00240c0d00b01d203070000d00f100c003401c500d00208901e22440d10024840340c0014030454103000347c203a0a00111820b5446c000100001101440b04201240241e0341068009014880241c03410313285a05001003020700b82d11400040001c2e80360280c141c4648818141c1000c101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 761067473 1250 761066223 761066233
    0x110c0c0105030103150b030a060c0c050606030c030a061104090204121a0408030c030612011d070e0403230d020f09041b0207051009120b090f1906091e080c0f 69
    0x141c5560420703403a0740d0320400c01680c1e65019086c00783d40400c0301090840d8007040c00d111110000c00300400c0301480c032004842a100b29004550745150101c0d0160f104800500205010125611100090428411b462000403010000130070124610700040020f0103814410046107600c500c2c00400c41d907200260265200c036101c042c0000229107004407a0002298100e10ba100e072501000260500b58410b400302041d860811594181000c0ca8003210003108294251280c69544c1e900c2d484030700c901250003e0024a110710018180b441c920032001c00ca1321840a40c0f41401a803400a601701c1e0302c1081e000081d1480440c008071304d40703864040d00907500c001407022031466a03400c4001c1d59541043c003e042c0319038248100b00c1c1c40d0a2003660300c84014072000d02d001800711242d003841100d04005a4015103079001e020001e4100c000c0005910242d03036010102956014110740398080141030b010021039034181d51071b600c1c5142803451210301c014a4083c4222590364408030032050b14020405420010030741003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 761068723 1250 761067473 761067479
    0x91403030c0f031521010e0a1a070909060311040c0f140a0e150403021f020c062107180f050a0509040503040302060a0323040b04060c0203040504110c0c01050301 71
    0x401c00645828000c01c4008a440340c440b124010040100301a0310b94000340000681040300c01046070300c0019195003002008000c04000302e440d02c5113840c0c040900301d031881d03998250304070800c00303542a8005070b5441c10040c0d040d1101d04c4041503418a500540e0300400c80f1b11038441034074091164080d06401800c22084039009100064109003208002c4090b860002c070345802d42e540224041c00d59640000c201101a09803110b005101d900240002d07030261107140d020707403010604440c1c5d00306240c1c9240c00402c0b0f01c080c0802003005661101d07100c60394103c0030201c3c5070600100c0c5080c80d40252003e440b00c0e264040240c090500c0500a60b000b004c210101c99810440d07515420509d4055802c15a14031f01c1e5540c0b181001c80c518803c1c3c0d8002500003900144000a00b580360380420104030391204001d80e146c00d42c0c3e082c8a00d4041c1a507014100120322404100014240c3d846402c180150740142c0f410956500001011140010f00724032040c0000680101a040c0600445100d04000d003045411541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 761069973 1250 761068723 761068741
    0x1c14060601050301230609060409060f060302030603100207030c141c080c0d0e12030112110306070e010f03090c0602030406080f010e061011030310150e0f04150e040609140303 77
    0x105c121030003810b001088a0612151500401c07600c02138405003080fa41c46503603c4142e00140614800e5141c00051070ba408503040d0700c24000c036401a01d00400410703240400c0d41c0420001c0d84070b410100c06100d0800c0648001401003244100c0032440c000c00742401c0300443d00e040c1c4030a018142c2000c2081140f0b020011442100d4050f1040386101030b000083d40404c01407240d1400032106c4117080692804030000507011041250200d03c5c0d84130b100098542c015120a040c2e4440307041e245200451034181300000294450700c0103241e00152864040f82c00405901c8040284c085500402c0050300001401c1c00304581010b00d80b0340241e180c1d00c58403040c0d85031841144031164083c1029110fa5803035030170b44111900c0360300850030440c008401c1d00c0d502e0a20004984c0c40d140a80f0458003141c0015000320942c0e8069641e50302010000307081c0340300141d041d404000060061601d82d11914014840c0410b1050320150381c203110750710444000500e00c1050424000d0b01c041d41c10000f116500400070000f00034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 761071223 1250 761069973 761069999
    0xc0b071a0c030a0902010216090c0f1e03020d15151b170a140c01020712020a05150c1201080a0218010b070b07110f0c010f020a0c050904021c14060601050301 69
    0x103c11401c00241c41c10319200403414004000c82e1600b0300c00c400c44003c56042e10750380c07101c0014405500c032801c401d1903441c0103031161645030344801c1c00042d8000c13040c203945020380c0080429204100c0c0c00142c0035946020034802100d80e401011140c842e008a010002c0d81024102c1140d06460568202c00c01c1ca0342d035501800302c141004610402c01c04200200a540190341c41e2001c040880d00f86c980711780751044124003c0d00f200d6415901c11038100032840b000c074004520001070540020150803007180720b040c08071150101400b0300300101000c0003003000c2c14941505040c003801d0008040c0c0a81616801006a0850203130700c034650030150ad000411041c1103440442c1c0180e680014210340030354a6902c00e480701d10003c035107420f060050040b004206240072540814520090b01c2c0d8840c2000900001c2366149480c4000900e88402c400c820f12891800c00d0308283d01c50b10080c01c015034400b40500007081040180800c0700c1e401300c8008040a03e00b0103110580d40040d0030710f071090456240024a1001c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 761072473 1250 761071223 761071231
    0x12240312070203010b0d12090e07080f042406050f0f061b0703170706061a180f06070b0a0507050a0f121116050c060405011403090304030c0b071a0c03 66
    0x86100180701011501c081d088908000d07001401c2c8075501102d41000e90011000c00040400203000e103001040394280d10101d98003c042d10390300c4207200d81e1611100c080c20300f009007080e10052115010406080850f100c80c1c6628030300346074041595881d03c414424801400c902481c483d00c5c0c801040309007a21900250340c0c05901e41d603a0060078010342e0240f00d090030841e400c040c0c0009601d8402e0710301200e004004042d200c4c0720f030304104000c655400c240f081e1003c51501224254070b040140421325000c1e0300342840030400041100d40ca0050f00000220b0b10340c0000e20448243c3c5419041068150080c407501e60300610340c6c184103252070f0281500812004e088000c80d814400217503d09010a040c0b40d1104011400e00b005080c2d6441080c010300c4001d12043d10120b0b190b00c2101150042ca0070300000382c070304990040e101c010322420b100003418a5500f009010030040c1c40103200020100740503511140042003850310f010b40e6104a41850340e0003501c1e114900c0c01081c085400c1c0410101c10070112540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 761073723 1250 761072473 761072503
    0x100609021602090a14071d03010e120f0c030a020d02070609141e0936060414160308040906060e0d060216083c0a030b0109050402122403 60
    0x10744d45041e040c2009208100d20748000b0000b500401082941102e1407070a00f0b4040513088118003600b00400d4240d46c03900c04002d0395500425680d0902d11040805828030603480100c0d14101080214814a15000a40341e800164419000c40c8038480d014005000a000c203443c26041c064182686100130258040c1128002d11400c050600d003048010b111884030080207000948504000e42d543c405175603840304402582800f00c980b8504034840140c03188041030010083d20080c0c2c2d0fa44c43d5240001c41c20343c1502c20501481003020111b826540820300554030501d0342d00e480c0c60a145901c1d0481c2c04d02d400000070f0058218008038507644460030b01d180c1e140d22407000740ea1078a038403420440f5210f02640003403080602041e06a456011111180c80d000e200d40c0030080b0601001d064945078000884002c1e440d1074007084035151051080d00000400c98041c1004000c15603208042002ca034000a4040805002e08081c440d640001c0440841e01d0040054410107100066001030b403181a04406002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 761074973 1250 761073723 761073739
    0xc15090e060a05030d0c0219030c05040207030509090c03070305151c080412150b06040e0a020d23041b05060904020706060e180705011407030e0d080408100609021602 73
    0x600d40d141c00c102c0c03020307140103816100b107801c1040003e4290140c40c40200c0c42855100d00c401c600c2109a400c0008482e0091002400c01d403070726040c00001c0d07110324170a5080280822007041b0701d03120001001e0140c0000100030390390349000e0034024212240030301048071015080d410344e5515035a031001820319042c1880d04d1010880c1c0703490000c04500ca66841192a001d54039100740034403c0d240311107004000da2a00a010400740361040040030311850107220005020710006c1150260701b640034001901c020344002680403802500300c101d10ba00703d001204071200c0c0c442004200302d8100c201404a491020316100003d0914000a80a000b41202d075801745a020440c6c0040c85003a0b0068001043c80540e29002402c11070307070809822011010180e0b0758402d81c1d40008065100740d00401c1d103482c0807172006091180599080f07442000e0a22420b40c003a442c5105a00440d403154003e100800c100001002401c8106002e0000d640340b680c080c005082c41407258102000498489500099048038584 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 761076223 1250 761074973 761074981
    0x11040e01230d320a020112090203030f130305071202030c04060602070b2b0c080f0f0105090702010b090703051005191a0d020c0a0b0606090d020103020c03090d050106030c15090e 78
    0xf0303501000d00d004041d05004214040e09100080f0b110001503000380d0316441d4001d01c10b001c81050300c4100340000c0d00345e442080041011a02d0030301602c03801c2d510300d0608451655035210540f6010300741e00450441001c0e80760200c01c42c60300700840307070500005039010300c03e42c0c0c64101d002c0d4595100b4070591100740c50002e440d00c41007030381e03a50800c150304000070b00c554600031121803c0300070f001a0b081302d80071800c1c01c3c02103012407c9680f542032141c0e0b0140c2071204039a0030320b018400300c1600901000159901d84006001a94980144a01c2100c1d103541c0020b50745401c0d040d255446805034001c0b0b01130f030801034590501d03081035807082c801d8500c2501e11407115031a01d898039a00b80300780941510814400714144c010100c0102d840d030306090003560710030241d494980c204a02c0d44281ca040607030050994198170015402600a084402d58540603281800c0c3d41202040c2d1040c11070004903026507503000c083c0b040150f0358030604090300800305001c2d031103501610007601103e414007a0b007440d401d40d48001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 761077473 1250 761076223 761076263
    0x60309030403020301050c0a02070e0c182b050c04020412120c0209100f0614090108100b07050a05060a0506030a11062809051507060f11040e01230d 65
    0x2a0000d40d406130081103285044226070425404c03041c0d01d5801070052010000b480307280d00910b02d0250b000c1080784c0745403910503444407c102560344601030308240048010240e00b802800321081c100c03810031001061001c1440e00604040340483d40030300c1984144001d00040d1259402004200d5200d5904010003804013400d035140100c03010003c3d4071090071410490f1048150703070700c10102d544283c2c0c50110a922950107607414682e0755141200042c050003107082541c845c812054201c11180e00c0b540740e8584820b401041688240c80540780e6910100c000c00401108000d42507109440010420040c01d081c03000035196004580c001d89508083c4060501035580c6904035020200140076107022009010700c602d601c0880c50503000c01203244e2010001c0d5501f0944180f128140c10750303078082e2400310b1903961035009240e040c8115841a5680c8610820700382a0780042014010351501d00340d1640c94191402031a03400850007a0007083e851034001502d44941d01c0a40c502c41c0c0c0484580742e190485000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 761078723 1250 761077473 761077477
    0xf071715040911030106030f150b011e0908011b080a0501060e190e1510110d05180a0306020c1902030726100605010e010311030106050c031201060306140405130206030903 75
    0x90f6901d5464034100001f0807081c000c1510189104031404001c11505001450440f08800f211a010030b41d018004d1040404c4200c4030044614039041643c110f81d2140340301d500b140c548403c65980042900d14000c40d13a900160380641c801c00100c01800150704010b4010310079102c4007061400303101e080c42600040101c00b10b081c80270305030081440c8807501c0e103070340a4a00301601c07490003409000b07a04101000c562040d003543e1a141704800041c10911401c0c5800c48007540440e000c00329806004003450200d5075a044200015400b50314056268840d440d5000d04090401145007001e40b02c01241d000103031804141801250380211881c041480c0340b000c6180003100344c5140c22510300669441204504640d408401034800a0761000104400140150121403074095034041960781400104440c62040340142401040e08003524105800d0007035003000e0f010b080c2c10040c00f280d10341c6014401c540d041241c9080007071048506021900b4016400031012440c0c10f00640036400020000e0541e402c2001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 761079973 1250 761078723 761078753
    0x4080a11060708031e2d0907030206130e10030f03050a05070816060f020f0d05060613080606030c1c12050c0a030305010302120f070e0403170f0717150409 68
    0x114055483c5440108800d00c260340107400e140c1c01031441301040c40f09010000c00c4401104030090051b640c08507503440c0035040e4008240100b107226400c000303c01600d900d00076050007641642c4c0d0910341400c0000000741008002c05115500300f0001c0108045281992404000c1d80c1500340a61f440300e840c40c0450b40d511880310060410500003540c80c4511140c507040810081c003407030301005191b5010390b100d0282d1291041101d442042030064000840c0030340e00007034114000601c1c07285008840c5130704000d0a50968030000380ca4200504000d001e080501902207101703011034109400c80315042d4004040076480c480a1300c4810000100b400c244c0c040c404484110400c2011100e5540301071074028003400007404202d0040c05008403184681c80001010800c09000f900a04411800c1403101f841b030043c01070081d003c201210020a606000b0000b10500804403000360700920729101c1c00c00360281040364111045544100304200e1003074880d81e5515821081180d020401e0f120ba42881c42c22120401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 761081223 1250 761079973 761079983
    0xc0e09090a2114030915010603060609140301021b0f01062112030605040204090b041113120303020d14013204090c0e070e0a0801020a0e0108060102010f0e0c011404080a110607 77
    0x85c0468024006180213812040040c0c2d4201d80c1c0c6c82d040224103881c0d2a11a41c07001c40c00b010300601000074040c08810450901600040c109603c200d8890f40c4000081c0000041d038001198a0422100a01808000e030103111200290310010380d84001d250b5801400141082d040d41c500b1814480c4650000e40040400402c1075480d00c2d11083c0007001805c1803039400c1d10807854040c1c4021101d05a100b0750f101c03031800440d029201c034582110142d819107000c00c22010180d0070401d4000c0c2d0151441808661685200c040b86958140243c98248140540540c504404512a6030046240d40000c40b1003200f800d99002c1100c03821032510f6003640f070442e001501010728010030880040d038050001e00400800b01c410700206a900e504407402c0b0f206000703034100015040114880f079940207102081d00400b040c4000640c41400200020485010080301e8019400209032506c1e65070b4410ba100700e03418103401d081442c09103000200e42c1c2e40c01d0800d0008107844106100c0c100c241d900c1c1c1d4180c4022903000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 761082473 1250 761081223 761081227
    0x20612091f15140d0f080d02040305010b010e040b100e0a030f26120a1a12060109052d0a02190201050901061212030b0a090c0e09090a2114 61
    0x7562400034140d50950307415400c2da02800060440c09024081c440e42c007024208842c01100d6844000600319020410307114180e082003040c62545a5100a0006501800002030350b904400e00040110380740c0c0800c0381c0b050b8144044210300e5500c020074800e030503049091114008420b03001080f46829158170284c0300c0600d6200a00620100501441210302c00c041c50340e400c0120704401c840a809008a010070001c8120009003509146070f1184503000290100c1c04800da443c0c5000035070420000c0b01c5070b41c15412850040100294601a0f15003142c0e2040002c0c900020107502c20b8001c1e80700103071500b403201500000c14031003580d545c112114038246100e44419014190000303406031200341c0d950040382d8a0200c000490aa03401ca1003e07580c1d07803060500701c00c19040402200079020b1031540d240c0c04000b00c0000110312130b103032040c0807081c0116110b5261380c0743c0c0c890400800e040020700f030103081e03040000c403c0c000074038100305228040581000700f0071964038440125070101e03031010a107900e02d0700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 761083723 1250 761082473 761082523
    0xa1109040906180b0f010e01060f0513030c12030206010f08030d05191401060e060721120203070215060303120c160f03080115030e2113030f0c090902061209 69
    0x40f4080345128045c03080000c070b5a030f40d807a002d00b00b1050091080000041c0d0300b80d01004a01d10030001440040e200740c030f40101c0b854481e181c440301c5004036800b0310a9039104d642d07850105601032015030700400100d119464507515150106489225804001c080641c1e20070010320200e520700075194982040800402270480c114103400c0a049081c002c020204d1525400c00d0141d14042084840c050790200c0c04900d05115139888025540b0151024014004030110b41b6a0b500442e1000e980302d02150b60081c143c41145040619400c6400303002c0501a801c10032442401140304001e103600801128003941d5229950200c010040080040003040050410080c03000d240d07014444505940e2001440c4029000b00c8200b0340032109901c1c0070301c0d0190411807404800010441e009407460700c00101007882c041c2c64918551045c00309810465020580c02e403c0c40a0200d0100c0100103060041c0381000103040c01d4000440c14015030420204400c140030004200c10001c0c005240b602c05c8403804021541c03d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 761084973 1250 761083723 761083733
    0x4030602030c03040b01090e07140315070e1c0f0807021c0309091415060d09051f061a0927091b0d11060a031b020f060a110904090618 59
    0x1c82513406035180c0b40800008600c2c07072028854a0328880301d46005007009864010100c1503031540200c116410b000b0901421125281c00c03000910917269aa500181c481c620801c00c0008150000c180c65041c01000c11500020300e4003940213001c0e90441005903c0702c106200207200383d003180407001011451401040201038205500ea4261416610240b007103290b20040034904500480f00403a42001505084041c1c1c10503070000c202d503038543e12000c1120549500c886142103807001c0781030392400c14003c200c4512822441082c000e4807001d0403034140c421060000c0036460044002c01841002c00d41c2f07101c1515030442005001071001c00c017281884e0301e0301061880d150514140c9030300c0801e00c028404141407030f0582100b01000c0e449400e04182c1d902000600c1500e400c40d0000d003042c140d80e400740440c0e030441c64140d807034010340c2640104022120640e41608110020b03100c070964900341541d01c3c0c100b145020649000c1e440580f80003800c0d015034100b00000d0001c41e00100c040c1c1010f042c2d2581840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 761086223 1250 761084973 761084977
    0xc0c0309061303020109061d282301111c1701080303070e040606170c04170d260a0b490302030a050c0a0b190e2a0102010204030602030c 60
    0xf038000d0301d03000d00711682c981c403d0750141102c504080e03002240c01c402100701e181c0310203560a42d1a5203882c44c1d040381560007100080000035044104000704151400c41103001218070080e00c0d0b2028070704800b21a40802d0711540c0c50091102a4801c03031420441c192200b4410300c0c0c0307460407a00380c010f10342c0a565680400c0e900d942c0160707034140c000f81402036040c0302801c140c0180f80c1150030741e0396041315030b084485da6039084142c00341130411400020000001c4000c0c84001c1d040c40240544058101e122200344094914800c4401c8002882d800c0383c820241f10b004810b050750700c8038001501113000b070b80000020b05d41e00110211070304c64078140392240801080384180044400c01004180d5000111200d08071421000c00c58000c0c0164410805604018490000b402070b10442208892a007503495455200d5001e00700e814086084841020010f1b0300300c14060f0b07024420300080a0014030304500302a03055902040c11070080324018641c240d0169200358122030055030131040031034a90811400c18040c1d9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 761087473 1250 761086223 761086229
    0x1c020f01022110081908070236010303082701050106180b03060603071407080304030305041a060306040b0c0c07090b040e03040e0f0408041d0a0c170c0c03090613 71
    0xe0b030340600081c440a1404032100950b1009001020a0003c0d0000580c3c4074041a4088411030f406000c482c0058645c2c4d006001d0301040403110741040380203080244800c4e03040b041c0080c0040c01e050010000700703800595013900124440d41c404a0000c500410300c1d05004a049854929031901c03000003841c60340314900449080b4507001d8203400c2c61b9110030303043c0c0500bc00e40e01e190340a50200003040406010b042119079404506080a041030811344511540790011141074004c643c44104110070030810b0b0f090604180c120041210403801c00d1800300e0b0350780500030300003032440c4c80c40c802091210400c242a00c0000a6171000c0326501511500004041c107501c40c003c50166041a55440441c80b020040d10113640c000104c181c1c032640c840e0720340072440b04090002e0b60748801c10440031a04c508048120300c1d40089841d406034031402c0212400d0102c80607450300c41c0400002c000c1c041400035819290741e40201c0d0752000300d42c8444608011904510441c6010340d8000000906407016041244400c011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 761088723 1250 761087473 761087527
    0x7120207050108060102030708040513140915010f0e16020c0d0c031a13060b1f1e0e101206080307140c0d0c120611040f09110c1c020f0102 61
    0x3c41d440d150016a981e0160250050400100340424410ba06081c08072140c0c2040020b804660885d0751200082d5000c429203074010349400840810340410740803001f690050030114403600039142b40c00903201051034080c0072100310504c1400345c0001039208208401400c0302c0140f03031301105582860022901041c9110444080841251030f04034101c007003140d64030070b00586c40c07900030304642580c50100910113120b0300755010075a14071205418840424112580c1c41581754842ca480c503180b0401c1104400304298000c2042e2002000b01d6602c428001529461441c106060054032043c403180c00b0b0a040c0d0070410844c44041424000d00861540603000348450000340c3d0400030f444400c0c0000010624806013500c070f07036490200020100007100303001d0140100070010b048140301c0e1401525601c00e90003c01c812026001c00c0c0540d100c00c1c82000342050308030702e4152500401d911225120710b040e00e0700d600f0124814824030405402808a48a05e441c0c2d030000f1561083c4101820000f0020301070390400e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 761089973 1250 761088723 761088737
    0xe1503190f09120c080706020409020306010e1f0c06020906160309060c050c060a050c070b0a020709140f06031c02030a0e0105031e060316030b09010507092306071202070501 76
    0x2800c5000d4807030250003a8010100480031072220f907059884211a490403290f50784104580008102c0c3c80c40900058107112001584d2410b15100041a00c9114900a4483c0c414002c98413641880700c88101c40e600b080d802c2821740b425043c00c5c075000a000340341c0c5d01c07078004800044240c200406042c440c12200e00c83c3e122610820f03100d407030480d82d5611010000701035502c03020390401c0c80d103005070140c85585014039100d4907011403800158204405540711080070340d004500c80062640502c048809010b80b15070411417805410300c181103134040a40610901e403804d101040154609010b0220500310b11f0415400c070380b2000d040255a60300c010244400540301c400c1d03442a0b0f611031000c4a00440d02d5100c1c0d59040410a46c4481113441c020b461650305109080200c10010a88488407000f03500035891b0031028606500c1e6142074407130040c00c1c00204030b40070b50300740300c00303041240740c48081e40341e2013030401c105000080071441c00d00c503640001d8580d403036030300400850690000380c01007554800e84e1010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 761091223 1250 761089973 761089991
    0x231503100b040e03071104020708040915030204050a0216080906090d0c03170306061b01270501050106020c0105271c0c0b0910080c0d2906040b03070e150319 69
    0x784d20380c00360120090503803588085c00201883c040c3c0250010b10b008244030b910703069440701c60100310340d10035203c0300082d00d1035182001540744c140311301580801000015481c0c21b8440362421815000c05400030400d64010882c2440d6031150380503030348440b00c0544004001c81690415078280500c510080b070340400030401c9040c07060451000d913401214041c0c229030600322606070072003803d0400d034199001e40d0b5846494260322002080071104e032182c981c1e4048240035803030404600390368050300104250b6000e02001000c9907809400c940c045620048400c1646080704031b404102c0c140e94201e5603100245000100300d2420081c2c180000c0b5100d410b41e1400d2a0341ea8405c907415004640d4000e40c481a0329800f03010700c0380210410380c0c1c848400000545803c00d0858a20116950690090b0788035118600d5215240d501e49a62928200304940180c1000c0c82c180304100b81d071000401040800078403802803161500c7e0020960061805900225117030b1500b400d01d40b46140902c0d0100c2c10740c0382003001e0a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 761092473 1250 761091223 761091251
    0x1a04080f0c0d021e090712060f06050304080a090b030a0e150c03011517040c0312090e1503010f0606050306031612080a110607080613231503100b04 65
    0x7110745504003821410040d421034082010405621540d013030121007090800d181c541d100000c05104110f00d85070303480101e2120f000c0b40100c6802d90029202241441c00a000031a08202681d921581c80307400c107a500c012201c800c43e641c11007513000740a1404040280b2001618035000a190400060225090b00140642003042c0701c0c81a610344146030001c000602014444410511a030350160400b10049202a40c0c524480c490403902550140e116403414406c0005416454003145001c0c5480320095091280c070b211a104d0240041101c40c454200d5407100f07403000c0d08804002403040348108800780d511040a49203920442d2001d1007405240400041350340004803d10a98030503c0400104804540d50400305078400102013007800002e9003d01d102039410007030f03948036403295500e90041d81002c0d0184840348c6881c1107062002c5040050080c0300580200c000c201030340004104541d207841e100e0301b81c4002c4031204100341c7c00d030003080008840b1031102e404c094100311094500700318001d181e101c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 761093723 1250 761092473 761092483
    0x5191505092d030903060a140f09030a0e0d051c030605040606050d090305120c0703030b060c0d0e0121020c060c0403080a051e2b15031b1a04080f 64
    0x2c60381c00300058200000301c0e85107950308603102801030122450000d128000900e040320403500343d00ea407a220b007c6002001101c08440d43c00140c0507401c1306690030014941600d074001c80280d2000c110004003940604d5444c9503104503c41d4001e02600c072000494444c8440f00081110108007290038000e0005443c1000e21401301112081d5541905003650000305a0181c00740090036820800103205090385112040342150151020680c42c56980405140c082c041e41d840c0500b00707100b0441800f403001e02200101c1e404101c41081c0c40c041c0f4404103034100503a5605034840420183c0c0398003101801d070280107a8010603424070048120b810907035841100600c20310a6003c010814542403047c03151550094003e000c13000d030b025403030400c0030414040019454001918016a040182800d21000303040d8125030002580901c3c0103003c0490403a003041003100c03080c84010704030214061200710410400c46024050040d03564515080032510001072020b030043d000c1d540c1940210301c501c035000440020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 761094973 1250 761093723 761093743
    0x2030901020f0606060702190b130617010b120406110315090108030712051b01090b0402330702031204080a120309200d02030607021608160e040519150509 68
    0x3070300c0c5040c0c80c503401d100020a031340058840348d0300880400304003040c0c160040d00d03608054091500c50703c2d01d4180c0042c41d40d0724284a6140d4031b50b00c0b000522240e024003044440030625900c004d000c586503840d16600400740944000c01669011007844140d0340d01c2148003250407011188200380b66220110652644154040188051860946c10b03041034007680c050a12015061003503420b400036802c500382501d49039030085500d088070004100451900590030100e0822072000e440ba1309041c1400c41e80c100600320f550544050022545c48110340c4d00708039000340364032001d00344d07625140d0f107482c002d5131141011001c589141d141030346004224403a104200300650480c62100c032440c401419a001000c10b14240ca0700841181e042401684080220314040c241660080c9501e50107641c500c2c84149858000c0d0f66030340c0010361804060440c00d00c0c00400d55028481c81a656240e901e0074030304d070229180005a114604510075014490b844c01c2c1c8015010620000b4486581e401c00e0341511181c1c008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 761096223 1250 761094973 761094979
    0x1060b0301091d1c0c050d03060e0708150f04060f03080c0f0a03080f060105070f031d0409020a0302100507020904060f05100608040b09160b09040e030901080c0c010f02070302030901020f0606 84
    0x1200d02c01000f9030201c0b078442c3d05406414009030178450b03900d44500f0203002c004050082900da400c1002500003100c25039030700505518140c075641c1440c16604000ca1356151820780710b400b80c52801c01c52959164800c1b4002c0488610065035999a8600000143c000c0404241c05004480400310341c40b40100f04541d68a6041d44d40d804d9642c1c44455800700c440000c0d000504000051128500241d02c0c4c01034940164000c0e240c90101440300500a0b401c4070b0351104e0a400745003000341c03100050b00c84e0718114095031390481c0c80030a4200d098100b110103006400700654003480c0350382440b007400100e900840c3c2c03005544a080c4507650340c3c000d0b0007110b0541343c45030800051030765000802040d11210010340029034141a05c8201075010341215084010350084e100024000070403804919052003448840801403002e50f0902500c1c0001900020000b0b000c0c40c00b5110000d49007a83c210298441e074001113040900715101c0303826040003556034201ca4200e90140c8a40c030060410b000000803080c0c4030358001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 761097473 1250 761096223 761096233
    0x1060b09090f0928020406171e1c1205070305130f14030a03141605040605030709080a1a100510030b04020c0a03051210050609010318020301060b0301091d 68
    0x10100b1507041c041c008081c0181802244032281010050a101d032030114034074210050805000d00403c0225103d0f640420008020506500c249083c0030800d9880d01c071000703420346e0f041401070303210a040030700e101c03440090540e1210082d08401d07000820180035003114002005541c0d82e00303034260201d96064807900c80c0c0c003000c90a0b200c0040c2e0b4030010695903e1092280c004480042c0b0081d6255402c00480240400c2e00e80340d15005060020596950021060442040c1c03010b401c031001c0c01a100300c0c041e032010450004009101e0340e004050650080c030420084541503721401e050100c1403424a85c004c1e000fa80d44003003010070030522801c500f9180d000b403c0109250b00c941d015002480302c9080d168000d902405842c002d59000c1c001000703854041e40724142c1e40c2c4071743d840c4008940d8006110161428410105001c10b03241d0b4001e5400302e41c800e00300040c1c402d102001c1c0580b8100401c0000303601d50b0812102103001c00702c4c04091412184640800c0c0000c00941064103a02c40c040c10300c0d13005a03480f03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 761098723 1250 761097473 761097481
    0x614090609040b2d0301020f180a0e090607090504020703080f150414010501021504110118030501020310061e0203031302061c020a0906030e06070810150e0301060b0909 74
    0x494002044500c100502c00116a600c050200e80484604a051200e00d941e040380b001d106180d103102600d10f4082140210314100c2c161444429602440d070f04030000d03464841c122010f45e00c0d0000d03c000075112580032440c013450070142260382c444c000c440785030000e441da00c80010075046c1402541d10303450b4580c440a58550700e0035240c450580b401001c4c03000c05100c0000c1310740d050325248520344000301100c0100031150f0418002a1508140d1103240744000464020040071900d148041c00b0081c4092034101c801e07140803c859210309541e03800240565100109014098004402e81d0b42204c8035500d60228400d10303103a220b0b0325014898142e034050b800c20400036807802c4d40030501c0110540b0007414181850344000d8002c007088017034280d40e07040c1c60f8001081003909800c244410700420162605002c0800c10a2146459940280020050007661400b250300100460b10342c2c4060148104080d04600200b64001d14500300701d50181c0c040d519201d404503214808108607000c2880c06011200140c44d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 761099973 1250 761098723 761098729
    0x1270303142419030503070215040b071101120f0e060a0203070210271b0b1e090d060507020d1d01020d120b0a03030306081b03280507060302040807061409 68
    0x107030000603511201c8603443c0031500200c0300c0c0010103580034800654542e0700c54030600078066600fa480138007035901401304201d0b0700141c1c02103031a0560f0140b42880203041c0080141c0e085141240212200c81c1058829000c13b8403991000c40c00c10760303840440c1d105407200201401284000d07107103400182c1002c84480040724450b048072100010740c210441e071140340c07840d4003580d4004d00501128065403034011010440569a000406030008000941c070300644145c4403d0702419243c9100c10694010a035810903540d11442181040d03007007001400180307010302000f91981c000c03401d4803001ca800a4440c15141c120280c1805940c801030300107040550740300405666a10403005829103035610342c10001e5454450782103d00056110381c0300822010b04040110741031002104003801fa20200e20f540049507039002807000034144184401150700c201d0320304545200039400c000904144501c1c20000f408a515900070011119203800380d0b00c1d4203031256021a908410002c40804000f01072041c400070745 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 761101223 1250 761099973 761100031
    0x4050c030604111b010509070f0e1306090c06030608100209210708030c0705011b03080a020d02042403060609080304090c1e030e0c0102161202030127030314 69
    0x11883c065458244401c04550864065145440c8206039450f0402d1114580b020880c410240c581018500066403e00e043e0418483c40104400120120b590a000a1000641c810f606d8a034000c041510f01315210704014028256610a1002910540d004c1003000c190a00c2503a44031040245003400e404081e550780300781c400084900c8000c0e400b40500000b01d21500304014a140220705000d40f5605190500140124580400610055070000c50240010f90701c941c65070303401107519500680358810860100c2c000d0160340c10076500482d00341400c0f16100c0021040a03d46111658244002c0d170310b802088809258074030031031740c9070350080c0000d011b10146a0840742c000051403038007240030400303040000f4403000c0d58142800442e503584c0b11031401075405c0c031110910130700a00082404072403001314424407203420700c202402c41c480000b16108546e42034215483d100b018426011307030001c400007000600c4001903000c4001c42c0c6002c040045030710040605903c5a1805140034001c02d502c055542d1003c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 761102473 1250 761101223 761101241
    0xe0603060f031c080609070f05090d05010e01020708180301020901120b06192003034008030f130213020c0a24050906040807021003020904050a090b0604050c030604 72
    0x903010f4140d21800003036481c1000c0c610040543d88014a5003445400c0c40b00c42c41c0080d18620800c00385410f0161490703000750072074110713003000c1c1c0f440f410360802414030900406142845070065400002d0440601c42c044018041c0c1038070701402c00c0c500d91084c408042c200c0c401d0005c40da022034030000c1c0811120403141d2103c05c026a024010502e884145401d114010701d1341443d50300817030b04a032004c44024203104c0e41000e010070038800851030741c1001b21030704012000e0100e01e1510041281606042c0d44144800291440351010b40010103480d1441c000189070021282002c00e2008640003070203030f107049103030392903103a030044d144c2e03501c039110f1910780000f943c80100364480354030502100034000b600364010702106107100c90080407a001982018020345e407020300b61044030381c0600e05002c0419170303900440b43c2c00c83c0d0440c0d600c225801c00540540c0a4000c504000f5400b503c2d00d800c03c807842049401500c40948a402e200720303e5034400d0100000c44c0c005554403214000144000b030302e40d0810340d00c50380c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 761103723 1250 761102473 761102479
    0x1903050a0f110a0603020c0c042c1c03060501020d1407060908122403150721060f0501030b220c0512160f08040f030509040e0a0605040b070e0603060f 66
    0x600c402d910229010441c41d50140e000681d0010b00c2c141241d40601c0200c500d002c04070703424442d81407810b078200501101d000c102049443e1a80a0f541880030030851030011030b544100d0640c02100a01d00030f002071107940b0507140036018a0801c00010f80c4103030204400c800000350b80904040b60b603211040104848001142c402d0030400c1690305072000125118071540080d07080c2600c2030b031f408140c80d10080d850080c181c041e92010003500304d5982c07a40603141d4001c2085c64021010620a45402c20403410f500203040c40078500803004c25941e040c2c1010700196082030b00c0c1446030500c0b941c2889100c075005d0f81c0c800006030100d10020038180311074000052520742440e0042c108011040300320241641550060320380b408402e142805190445900c403d01d9001d0b0404480c2c134902038403114050b26542100a040010018405003503076503030b60200410900c0d49007251110b000c0b51804000410003a10250303031080001c030025054611400326104440005000c880c21500c95005106038039288040540d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 761104973 1250 761103723 761103743
    0xa0f0c080403140714040b0a03291303020d0801080a12020c06160605010b0c061305150f041a0c0406050d09080f0a0306050405100e0912040b091903050a0f 68
    0x400c1e0102d4032611003800b0340c0c024210103443c1a50440c6000341490081b4081d5062000303139070304c6580d074030401c1d170403640c02c283c1c8030310300b12401262100d281044401c40c0d20030f000c0036001c2c000e0903c2140d8105004600c650215004500d01c02016070380c80c1c000b41300d10401940308034000070020b0310441000700512820300484a001c08a10001900303500310400409107240c01d01c41107020310416000d1140180017030f800f05441d2003506116985c45080c0104402c1c0050310713050507002004010081c001200001101c1789041d030509500c1d07540100000d4070305969942c1c044200707002010110384580d009213040301106107000e00e4902c0503103041d004205000b80241d566440540482c60503c010444d2001b6840015036650352020050100e80540c2c100d41d000328640300401c000790440340120019180005d800f051203640d8400120300d008194900200300c01004180000d1a80085014062900b0f040390400f03410031a042c440010008148005041503201890300310102c1c410a09005003640079400c2c000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 761106223 1250 761104973 761104979
    0x60305030409021810140c070906090f0c02060106050a39020907020105040c03080f07050f010c020d110d03020c03041703070204050a23060f040f090b09030a0f0c0804 73
    0x40e040d41c10642c000c05816800040e21190380e1985044021000c104071080d42d50040084402402500c0d0303075207607800220002850f03145c0c0700c404010090041682110a020a940f180c1c074100160140310040000c01e0704090758158440d0002c21141c0c180c0341c1c1703540e581b801c004410404841074500420f00d040c00400e444850b600b404917802c0001d00b40303100000f0003201906244188030403c500100300608691525083c000001d4801c13444074100e0b83c00003078060300d0300100d12681010344503500d4014040d1054640c41c81c0d25a00c19001507134108415025240c1c56402c4110541d000001455200c10701c0d04951a8209803d00130703070103084202011405c0303d044c0364031004504005104058294065031010610008618181c060960b20142000040c00249141202240003c0c2c03031864421040c60250000b4030580c8601d211883d02940080c03040c002100c034030b4400d07001401940b17402c2e140e000d052000135200c2c0f10008101c40034410316640e0400942250001121010348a80f0110350700340d4100000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 761107473 1250 761106223 761106233
    0x1c09050307240f0206161b060b090c180d06061707181b08060f0a12021f0801030308041e0b0702210904020f07050f031908040c030807060603 62
    0x1d01624000078865010464507054201548840d45000300b000302d0402c4000041c0d60125441e9005040c00103001c40c0e19809041c2601c000541580301562200d07e460b01c80188111a003042041e01c0e001c3e14031220b540c0711180e61400c507215080040c5180c0400c01c00e0b5900383d00b88120440c81090040f07500081c260707141c6180513802c0704000b20646a507801400c080c001c40c00400000083d0407407000080120403450070031054501c070040192030a001c00301c400074146489903541c190404e8002064070203440d23111030040f01c40c0100180180e0003010382c03424015407a1521403c00d1340107034039a00d0700840d5030704c1e541e8101c0703d00700b0081045603480e60100c000f8003078049098051760503a208642e220498508040c0c02441c01c0c0c0c250192100f0286a0b03038005810103003142c03c1355080442545c3c0940d8a91058004912610641600400d5413289100040c2134078000b03c01b600030800300110070b082000d101403088409800c1074501500d440f0304228200300182c0d400c4003d0042d0382c4a103001180c402d0f45e80d01c407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 761108723 1250 761107473 761107483
    0x206040c06230f0906070f0b13030f03090606150306170c240c01020d020403051510091a130c09060e0306010608090f1e070515040e13050703060f05060301050601021c090503 76
    0x46a071f21000c0b034401c40410108074203a176481400ba0505d0a00b082603603d000703040c4103003240d484040c143e50b00842d0303050140e40d81020024007410b600c0102440707030a200040080002c0e02c00d0088100c515903a40124040100c1c0240609000500e0303030b0701d02d1241e0b001c03c1090b580c8085180240d02c10410102c034440c0401c0c0041d00d24000c0c43d08005840d42d240d030510600b4060704414029120400508010404038600d02d540c0070341d80a01000940c1445220702d622100700c0a041c102e078450007030641103038244001c1c0c12500b84104180d03119004950740d12000d80b4501c103030b04081e6034960030800040c0b0429119107036003580417040c4000c03503491000e04124603040500b0703204005c200c100100400c02e15860200448401007405941807840c0803000790850499004a001c0d5418640241c8007180d200c1d030500f0300000f060b503040002d8500c80c41e03880c50300c034006042c0d520114800a06010024600e4541032080a1050350183c000d40540b142040240c5a03c4245906400c20300600c0e03200810300703171002c1017 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 761109973 1250 761108723 761108737
    0x1110a12050702090a18060b12191b030309030605101d09070b09091f0e010b0a020c0a06052b02070c090f06030309170a060c0206040c06230f0906 64
    0x540c0c0d0b654006038010f001100800a00b0303a103603d424440c0004025103c04031419442e0b1700a03d001903000200c00001d4aa120400c000c00041e2003190340080106202c00010301940f480341c8160404104288400c4038034441ca48030160200300080d00810118559802946c5c3c84028013004c0c80c003007515189650881c804024410384a052602e08100800300100040805428121b081c2820520f00c070300050380d00c840041c041c001181c86440c80c40100014005544064100a20610304542c0c4815660003603420914801005114811f541640d0381042c0c2ea030f403016941d050b0340c0c2c58641020410b090844086005200f007040c01074081c1c00e030906041d0b101800f510f5100d02090810145032402b1002950f01d0556501421840c1035820000641c11110303035021625011001d03801d0003000c110890030303d00304407000781c00e0724149480310f43d03916404290144201e116400b441080d980355142200e80c03407202841e01c01c2c1c1185c00b03a089400f80c006603007d021154464100d55181070a0403000c5001604407103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 761111223 1250 761109973 761109977
    0x306040b0c0717071101080a151205011b080a1404020a0620030f04050316150c05010e010207060e0d0c0c05062803050f0a0b06070209130204050c1b01110901110a12 72
    0x17101c103105603072024842d03401205002050041d810f1410f01c203040380006d446000007600c1507100042c1042030a4000421030b0f502c1031440740149404500c0a0201e503002c139496954123241c029980050f07442d0500d01400340e600504035241c82824102d0a584190781105007810301411201d1813510404100b00510070701c0070341d140c10358945181c501494903001c2e03801c2d032802c40c6100c40034013480403140c4290200c04100141c600300550300e00d10300b00b0500401d0030710307000c3c1c42550000036a00c061062542004501192410849805005200080b9140710211800801002003550304010500c0c05c1c80203415107560024800d0b40451380744c81c4145034207100303010302d9005c2a00c0d101046400120a140243d0051039104280300c1c1e06007100c0001c4047c421120001c0c4604168004504218410042d6070301c0707182d000d0810031403420810306040068000f10003803a4510005000b502c10903206003e00d805000c1d01c64007682c03c042844005403850b0440a19450f400c0c810a00e202000c40d0060703556400000e429 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 761112473 1250 761111223 761111243
    0xe0c03070b1909050f04360309080d0804030f0e03060a0e0106061119030314100e070905031c140406050406030f021603080a06050a0618050306040b0c071707 69
    0x10b08014500040090510b90503c10011410070a507121484400c0405104450000361842c040d0b00c410481e0648a1140d1070094092003412407a940481544010724003940315002d555a5441d0001d0362020106003c0c00000c10784008030340028020094000c606641d828014801c400e0000813034030740a421120000002c0c0c407100a80002c450a11551002e002d451400c02c0840c0c1540007503c5c0d4840e43380180100480c11011007005043c0300354414089010800510041d604154031940320300843c40c018025003810060200341c1803400360100c0c50071686c024028190040407001c0c070b4408540e0242204043c460780f0354034258180c040034010006440c03240c4803191280c1c103140d401003c0701c03040d800541d44184100400080030741c141d075000d0036145c1d02d440d000f0040d07902c8002480243c8120f034440c681050040c000400d10b250400d01942c410007088608402c859a18020140e03264019240603005682e14000700302c3c40312441c0c00801285001d0700c1d008405130110080d5110580c4040740c161544000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 761113723 1250 761112473 761112487
    0x70302060414030c031b01180303090c06080112020f0f09011d061e1002010f0c05041a0a050a05030429041b0b040b09011e0804120f080a0e0c03070b 65
    0x101e10750542c1e2541458015401c00c0d55401d0007590320720480030089014400c2030f40c0011000301c250403150351240b60284400b4100380b10f2602078094454080221940d224180c000310310300b80704408140c100c0341036540c0c100c0460815001e012070490400a16604201103002c0c13070078551120344030a4000d100d02003001d003405a4414500c4c48028001d41080d03c5188400711200d030392103038414071402c01e0404907408420003c03401010390040500c1e035a00b500c600c3c1410b10b12058a500314010340115040100007a549040c0c404a80403584510341e1000e000c280c0a010320503040e0300c16006141d20521841d42074800c50078800c081450603800c5076030807040d28030a10402081041800261703103020307801c03103d2000450030014811002e0155010b0f0724400710001c2a20042030384140c1e000a60360200c68941d00040d040807000410b8030400700e0f010303108000e600074500d80b1284692480e60038414640d940e00304640b91360802c08050716040c3d10004052058a80d404002e40e01804031070020103012803429a1140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 761114973 1250 761113723 761113733
    0xc0102070608060a03121b06060510031b0e0a09090803070e0607020a05060f071e020a05100c020402090f120c030f011a04050c040f06020a05013c0f020703020604 71
    0x80c0d41111041103600d0040c000c4640324410f00009903603001c200c01115424002e0111044441714110703000c9509429464002e01070142e0104080d42c00507a031540081e1980c40307080c0c0950b41030742030ba1301000504801050f1b401d403240c415180c10300002011890034030350320000384007642c0310100251000140042030242c155003011800c2a160303025036400c0c0c1401d4043d0009200000584141400740c0320014441900505e040207c4405c95406012160380a20303844205484a02c8800c0490080340c0007400880c1924001e412402d000406076240440304075168240030183d00001c0901d60060210601d00d00f899075105520b1419030415001000700c144580b04140c40d1200d141c800d1029645080c0e1581c0054940d01e01810003c00d050b20082076507264086040314510175503020a101c3c0340603110120718168081100082030340a100284005c000011078004002c0000040b0318401c840b50200ca90407000c1c2d030b44002c404200c0a81c00042c41d030041d12582d800d0b40c2c400300b011001600b0403420401000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 761116223 1250 761114973 761114983
    0x102071d0c1e0c0c2e031d06090606010507051c090b040b070204360f0c060503190203010f03020418051207061d06040f050a08070c0311040c05191403090c0102 70
    0x7401226103055030a0f0170303080020f16550900300c07a0b0000a81901c241c000c1030103034101c1d2505181c0c1c080081d5594080c0c99503261100800c0e80c80760028051075003c61071541c4101e042d643c1c699089005042d2020312910511f000c01c2005501d02d080c44601200040e100e18010041c10050240380300d841d07903078005403040008480c00e900350103900503c00d509041d014140b0a940d80c81c41100030b41981400940e50401c200302c00c102d01d9004095029003330300820780607071010142d40221440403298500000082d0288143e0209020360307282d4404001c0c042001d494503803c812001c01d00c0d4022019044020b8486608042e41c3c041100481040003803000704100040c410000c0c010500e80400781c8180c03482c641283c03900340c0a007010340000c0002000b0707024000c00784103c4400542c040481c03980d590315481c2c5181c144000303100545144e0303084100c0f591641040e000e01f2351a1020f0756581482c008020442080d201000401c6500b040b000070030110b00701b0392040c000c50003220b0100c0141100c10034140028980 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 761117473 1250 761116223 761116243
    0x17070917070e0c070602040506030112020102060a201c05071116082532040b0a0306020c330c1e0304030309060903030510050102071d0c1e0c 62
    0x798003100d010040c003050007908907003000c0da415480742e862a4030300303081010f0300581c1c2000d640090300200010381281c0c00e041c004941c9100b81c080c2d405680c0d6502c4000d0403100620851084002c0c495521907d40c3c60f0b09008080c2200000c9441199100d183e402200301c44045400390080385501034108405041000113151060130310040c40e8030750707040c004400d881c0d005000f10400c485405c019159400c1e5414404400038048010050b0384036843c51081181c590b07040c030300300c883c2c0f90f000702000042030800703001c0c41a8070ba00103000c1110051a65580701c0084d07011140314503041c0101a11042210600140c92006c500880300380c1d440e4103199075a601701c1c51005040f400d800c002c10000a00b40400c03080a002c10008031442e26078487c1e031142030990103030000c03003402800545040c0c0d900c0109034259001501940c0c86000340c808182e11032005a0f40c4d0445401020400040300185d0703603102d05000a200d40c450044000707207040c5084a522840c02c03414080d03114450360b201081d032500c065800c00801c402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 761118723 1250 761117473 761117519
    0x90611070f0b0304030201091a2203081302010e0319060e0d1209020a0e010306090c0b0406020c0402090d080a0507140a0317091e01020d0605060c030a0f170709 70
    0x341c80c11022000c000020720981a500e080807001505250003940000c007000d4002c01c0d6410348140c4089000b800c40001c45800d007450365800b201d20f04d90310501c100c2e6489568152245113082e155021101d541280300081241040250003e50025840c00d02561180b0480ca6040340310002191070001c00f95407210480342c05036404408040c040310383c0040301882481c410040060301d0520360020440183c41604034000c14502c00c80000300704041d550006035818081e4016070603d42d2a0140c0c2d0810380306038852180182c0c00709140000c2850682d0080061181c01090500008820750701e21407250401108000800e20105806041c019414080458103c920000d09020061650b000d0100c0008000c00b2000b0360000740020303911103003004803500040d07070640c0c200c0e20004e000c03d80c0341c041d5010940c0e42c003589051450000b1035061803402d6506d000c904802641c2401442d5030110344074001101c5020400042d4003090038841544040e09009d0310480e0f5801089905016040d85054010444c04503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 761119973 1250 761118723 761118733
    0x2150a1202030609040209071101020a050a02011506081f030203070311011701080d03050411040614041103010531020a0906080610080115120e0307020901120b060f011e090611 77
    0x15950f07158421113901c1607040f1500b0140d03448d0b00c0400c40d0300200404804040d980300286141500707030840050046003c255009000084908092444581c003911175640802c008401103040c401c4001c010544c2d040810030a502e00e595685c00091600d80e6550060f1110001c5960240086d64464040e29100f401c5020342c100d19494850150f50701c0c420802940200341d900d1005c5020000e11510620946ca4000d0040c44015150504080049240d0a04a104038a81071111041c01c0c448000d580c1210002846c2ca00d0081c203540640c50f15810032203c55040344a0030320b0000100415102800c248092507a40300940307170500c000640006d102800d0700b0701c40d1004000c0c0000e02503208003188d05403620315403043d51301807070490152142c460840541120505041c2d1500c081c11001002d061a030303008407161201640d940014410002e502c0070302034000a000c10020f01c2c94144481d80030f99511043c589100800040441c50030941c50100c00480010210141003115550106803c4d50a141c1000501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 761121223 1250 761119973 761119981
    0x4020906091303210c08190e0a0822180f0603021011013801031509151a07060b0f0f010e0a0b0301030c09063c0302150a120203 56
    0x21440b000030190050401462604040c40d18107005002d00c461456103006001e0740c21511400f8041c16000c0300c140c1c06003900b841808109138807a002d1080a052544040c00f03070000d1580302d000c01a44415040b03801e40e00c02c810010500d40c0c4002d03000009058540e086403910320500c40380410341c0c007030700e403884000790400d0000e00160f0340c3c1803031550250303500c0c2c1131203294004020b09250150100400d001002074400d810016044178070743d0592500840705680c05a10b98a5130015400c9680f11061580740c441c4000d003d000010783c07544818038003c52100e0f070180203a034030030412240002020959a81c0c150120708c2208100c40d602490404400c110780c80688080c10130b005c60303841420041c0c41410042020304a0955807a2040224050080b102d503141d03581d81c40f41444408072455200706203425150a00004102c10420340901e1070511118010740700b5008501c3d00301100300200301404090344540c800000580d652002d000040000418107a101c02c001c8a010745001003a4034000741e175034010030400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 761122473 1250 761121223 761121241
    0x7030609090b0f040c05040e03090306360312070c02030c030d0822020409080405150c0312071b060609060608091009031e0810081617030c010f050402090609 69
    0x150f02c03960580c0303561450b40e150b06001403c0c509a41c00ba541046c82d051040500c003801000400351800160202c6000340c884450840580d000ea22494030001c1c1a44098a002400115481040054841102e00b8402c1c2407003900844082594a000401c4040c05488210b080500c42481e00d64801c0f005450880c813408405000c1c05401000200410070342224009800300c0c41081030b91464001d001000060500d1502e600b50358400e0085070300c950861403602900c0b05200c0202c130981940040a103042040c0c000010b801190090046010700404c0d1030034401c590302901505041d00e010b194007048141c944240f0204032171707844d0401c608000814042040c0c00d90001403848481101410000b21040103003000c4441080152986030065400c1400c5080181c0c80041c0c00c0c01a074010801800896480395080e41d250300b000c05045a03140a40400c002ca8008a091038841e0405981500e24140322040342d43d0849440082040301e00769900c05100c19401d119042c603901c500250f800d51051b0504d01c0384 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 761123723 1250 761122473 761122493
    0x1030f020c0c1c1a0f010506210a0b0603100306061401020304150504030c031514060915130906020d0b03010b010207120201050403080309011b08010f0e1e0f0703060909 74
    0x281e016205001c4140f08008154000406554021160700d12034035a1010b52581c2050549281009000f401d00105142c5025030803940200c41d4030541c85041106142d1038034489a009000c2000d6aa0300c134807008441d01c900004612a82d00010303840d0000342180782a00c00c48596130440560480d2860083d00207980020071102628442c8115100500320035404565510072070304003c0501ea0340754400020450201500206c18264500500c40b07070008070420170300e105c000c1f0b9015900502d20b40c00f141034083c8030010484124009091300c150701104401076070a0341e41a520480300c913540050b48a80c1c0091030300c100000400210020700c01c0e40407070b900003503951255010b2280010700801824046a0246080310015944203104c65141e2a007001c0d41030080c20300c411415200446040b04a40b01449801e005058a00850440103050f00700010545204030081000d10541d40445440310f050b2142d070605403141c2585242c0c00e0240c90400001070a80780780b6440542d035a828070ba5003500259100758 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 761124973 1250 761123723 761123743
    0x8030a090f060e06031801020c1506031b040c090305011a12030c070b130317190e1f020a0506040b16031b110a02191409190b01020f0d020c01030f020c 66
    0x44c43e16141d4035605000f88038492209100031980d132001400d40e82580300482d80c611f080c21354103c528010380e140f40c10b0544841d035842c16a86019404060700c005850243c1c440c108182c902d1a00d0070f089522030b5511800c5a00d4481044010a19454209c0303040c43c1c8110044030100d8818051402d20325415885a0345800a00901c00710b00380105146804100f000d040c4002190840c41c0c25062600004040c03419500c4402d00c00524010b0740c1008410301c2c041d40300b00e00c0c003071000741820340c0d00f0341ba400d01c4d04143c00b0300249410460007100c1060003c01c00401601d4042c501420301c481040c10091954004003803a00507240905041c0303062102804200308100280b0903444c01c02c1e6006103261002d040c18920f8400b00298010780c07004100403019032131140f20b02502d121055034103201020700100400198201c4070220442c1c001c601245500d00982c1001d51500701c180100c4d8203402d03803414020305280c0004075820041e03001008000196900d03000f25074543c1c070424403c5251030648924941c841020350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 761126223 1250 761124973 761124979
    0x31801200d111614012a030c0c05040b0a05010302030604090819020c01080c0a030b010521010f0b09060d0c030b090c1806031e040804080f010209030c0907080a050405011508030a090f060e 82
    0x440d40041c401e0078107000c50702146d00443c005292802520700a00724041e111404e89100042e45004070f07140c1058450f03104d50301da009000c021281d01d041c0044019600080000c0d401c240c494041a00051000002d0b00005581d2072060074182c074000b500a00e80140701d40b016041080003c14442950071150841d8200d112034500410190081401070740d062240c2840e510820980b41840103e04060142e05810b884584104400c0c0b03580e915003140c000c1c0220707060241d005000300400317450402c40e03501080c25062281800300300c40c02442c0c0041c1d000740040310044040040091061800c980061071301d08100d45c11680d1030b0560401c0030429138055610034a11451840d0f1401103010f1040322816100203006010444060200d80f803c1c8a000c0e40000245078000e104402420038540380590301107128010315640c510007039803180b902030042c02010f4000e9401c1e540e10300306c00040003240400e00018210030700c002c41e0382e43d522242c010700255044d072020100d020300050510030a54050700c0c24920400071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 761127473 1250 761126223 761126237
    0x3190513090e0718020c1b060f160807030203130e01030f02211c0912030e0108100e07080415050f0601030b0f0901081509031801200d11161401 63
    0x360040a1401c40d190b0442c4c00000c0503040c08043c9141e09800400c480e10000082d118611034880300182c2551817628200d501590504c01342c07040d2800403028003100921502608054542a20740c0e950507401940e00f0f40c01a080014550344134040e40c04828000c05220030310700455895a182e208000170b400400034425906000f01d68030303009100c4002008031008001743c40f044110010000c2d91000e62200303050105250020000700c04105034101107072142c060300d032100b03802000303401114110401403e0140324601d00a02040c9240a50003a510411480d101c516490400d820442c0c89041c42e403810708005401c06003040f4224140b03201198001400f1700300401d08078460400103c1c0001698880c136000045880006001500000c0380c0d0034454003c3c121000325103801c0105070716840341d0346200d00740c51503100401c2c41c83c0d442440b1400c101c4c1c01c0c1e00038005c00c4181c58046a400c1400e0000504002040300014a40b407100c1489281c40400d80001d10b000300c64948003042030300c504241d051905003c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 761128723 1250 761127473 761127491
    0xd06200403170c1609051b070b01030204150308070501020406030e1b060310050409230d0207060e0427060b060c060f0612150405061b070b070219050319051309 70
    0x800c0001080780d03d12130000c0111540c4944c4014014a82141c00164154003201d0300503071791040c68110f48000d90810345030582a0b00b142c0906c000303440d074a1110243c4170b04a5a0001c04199450040d1050302d00c503c0003d42d0340e620300700c2b0060a42e01d101803502d85039000304520f1510342c4c00010545a04000c10f40c0d03800d480b656040904544001d2582c0062b40250603c40030300c04008902c08192545081c1411042c1030719050100d440d40c1d41c81120082c00580d110b004d050060320300500781a103003104010000b062175045414041030281644080f03210f54189100c0719400c00c5a00e0090900203001624154102051080c900f0360f80c0301c1c0900480007001c100c20120b016038a03107020500c400740f031101c11990100320b030700c1e03440c0070702c50f01100c040c2d0312402a04003041c81615044205211010078032091410800a41c8683c0711062010780900154402e068070341d002d40c40e0100704600420f0098001c2d54a90242c0d4440710045013003544c0c3c1d281040f0307042120b40542e0700541c10103400d54140020000f80c11071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 761129973 1250 761128723 761128747
    0x10e010b03010530010c03140a0e0a060902030c2e020f0d0c080415020a03031406060f21010807090f2706060b070b060f04050108030a0f02010b0d0620040317 69
    0x420810701d0501542403181903503100f5050381200e500b210102d2340c0842c0c142e032466929411907042021015858008c04c2c020303004100aa009050200e00007825585920301c070500040c82600d000481c4100c603075094401d0440030502075210702543d42e090003d00f1640207105003040c3c80340c100603205009e11207540028000e2000325001c0c0e0700900124a110160608001e002950f10f00b1610310450000b400c0c007510680c0d07c5003501c20b4038091500604600c0c01d0040d64419620300d03401c41010b03450440700030410b5180b2009030111007402043d264000e40419800c0c2040c0e841960840b00810581e9410103410101f6802007400740082040304c604001c0e0400d03124a414000307044540d000401c40040850164203011900304400e0117600100d40c3c4003d05002d00742884140c8500348a01200d541051100c804803074080c49080309102e406100000d62190381000040030880c10b08400d8944503500c050208038a028031007139a1541c004039030103504281c82c40e03599100ca02400019581c54450100399140b080d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 761131223 1250 761129973 761130049
    0x3010e1e0609160c0209090f06010902070305070627060507110a0c510206070e06160b090a030f020a080f0a0e030a050f0d0f08040f020a0803030906010e010b030105 72
    0x5900904806c010f04100d044035a451840390340b010705038091600000341040c003d100320344509038161180c0b810040d85840780300040000d20030440e0b810f83c541003c2029056040c80d050402841084002980c0c28024401065a910700030042c0203a40141041400300d20114100011195900484002841c82d103402c03c1221110500c020600c034990882d542e01c0c251113182c143c400b800c0084002c0b0042c40e400d1404c0707a465000f40c61020125504440c00c61880c2030030700041821921074528244401e080da5642000103104a410400c50b4000b15240020158405e059440300b451510090003c804203440b140000c0c401d520304000e0190300040c107100e110380104030070700c8106001410f80d2000100740c1040b50b1122081e0030170030828045d911100e16032502510f02e203034840e081592915034584d00d5544402101208003c140da04c0401c02500060741c4108000548c031601c541c1e0041e050b0303075161594130100d440c011380100071010300900040c4481c1d16860b84540c090040b0443d1031186810a8000450035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 761132473 1250 761131223 761131247
    0xa030e0316050d09140d030e1c0c091b03020306130e10060605030c0904020c0a060921090506070f020d021216080f0d12060b03010e1e060916 62
    0x1901000c1150211481015a8541c01e64060002c1e2101d409000408071140c50503401100107144a01c0e60f04810740c141008031582640c4207003440c9200d003a403030000a0041d030011000a81103a8104c0111081240362124800240031001c014000c1110340c004400240c03041d000705008055011000030559034803594401c0d40d03001d44c07a80c00c2100200703540300c0c151031703002c800b07400b0408500700400065814403074400c0340e20070308502d80e25a040400060422001c1d5110850031807483c418108000b010407203e00c00c40b00418460302d94104510008000c504130529100c2900e81800b4512404008a840c0c1c1d100316110030780c7c0811503030803107001780c40001c0310114403150213904100c0c0c07156080c1d20b008001400d0701d460907030f070880e24400304c0d55190322940d5030120340002c10f80d9401122002902a0142c13071802d60304030f5541d1002c200581c40340c10100090b0000d0b480701001488176028004020b804030102240104420016001883d003d0082241c0040181824420b14040a4181805c5115844040903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 761133723 1250 761132473 761132501
    0x2031e0f03010e1501020601080d0c080c030309031b010207080702090915072105010311040e151603240e0c041206060305010e16060e0a3303200a03 65
    0x1c0356103540144141410490703444601501c0c1c1034038054150700000d107040c1205c032070340c0007400b40e1f015141c0220b60b0b10401450498100f20305100d010000941070014501c250307403441c002c60302d4800c0c1c0d003c5203440c10f0402e5242034240e40304125072004101e1400072980400c0c1c060307660f03d00c0e9444011285160245095048003010020028809072550182c041004800c00c0d801c90042d03520000c038450b089600038800103113040c04060078151141410f8100c4446c1300c40c002c02341c41ba444220300b0801c4801e94100c0d00c00200d20800b02080800a0309440350511200003c000e042141c8030216402c0881d4626010348003c9002090024103010420000c84018100c02400c100e00b0510a24012002e0314150104661075420405a50b0030400005403250580340302c400c9041c0d007107103040000d88410514181e001c1d0400045440030a9030002070005c00480c035505601d180d140c540040071280400e50400401c8200344c20710b04e003101d843c4486400c40e103001400e4605a030340d8405104007500200560640102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 761134973 1250 761133723 761133727
    0xb0a020a110a12081b03150d020a14180606160606090914070803070b0c03100f06050d0c140d02030c070204061502070b0a0912140303160e0d0302031e0f 67
    0x40103142c0c083c0390f89041c0307180c940580030b840d04c0c03100031482d905010030701034000070510000301c030748069070300c2175070440d001070000034400c80181c020402c590541d0f040400030b664100341c0500f0f20b0a0049656000072321a0020b003806042c04400110580710790704658040d00340307403d13010302403240a5210744003c04040c2010042a1130521308107164045491600c40140502d40d4000b07079204001c42180e2103258011604041d03592020101e08181d000640214410003400314081202d0800c0e0400c10041c04080d01d0b02c0d500d44a102201ea015a107000014000704039800300810b540300424000c0e2032030031602d4070700582c0f00e81d101c81d020001c1c1d0040b500041d5005080210004810400c0143c2c14035103201942540c01140c2c0b5544a0600f5103d030300c6107900012821071702007040580000402074100c1c0b00e0200d00940d01e20050655140d508251400c3c1003d42d4003441c07466900b41c0040141c9480a0709580e064801202901c010b91240075101061540c03d0184240340404d0715141c00b203500d681c010f003403c00c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 761136223 1250 761134973 761134993
    0x30b09033a061403151006050c0f0307030c050c010c020102071205010f150f150903060b0423090c190e1909060219030209210a150917070b0a020a11 65
    0x2a5105035124155009018030954045c11194012503071707215203440503566105918052007201ca80d800000e03035400c14040e100c03015802a90034402010050700903a5020381441160610304e040201072002d46060001030304c7d4220060743c0114030481120b2032000403403158265800c0c02405041d00c0850780480520306a41c81c901356042d00714481c1030703030681c0d611201d05036258100d851143c0000c0700000c01040305d01a0420001c1c1c3d154100c3c10880c00040d00200d00700100700024a0b181282543e40c3c9113500d10801003000c2118104140006081c089904500114102c0020040c492041c0501816a442400014804054222082941e0801100400841c0641e0402100039081610702007400720000d9810403042e0311a000755100f420000b00341141c50141201c9291010b24040321403003d03030242c0303903e00c40400d8654a40c0325000302d00d0740010503481194900b050142a000b10007641c580000e00403240898030341e0036441d622800091006035694900c00040e03440d2140e070400041e07580f08005a070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 761137473 1250 761136223 761136239
    0x100f0f0303090803040b1909050402030f011503090b04021003110c01020705011b170402010e040213052830030e150408031602040b06070309030b09033a06 68
    0x120200c80c0699502204582c072440d105440c4e01c198401d010040c841407200a002401d00c0d0f8a4202c005928180926806e9480001c1800e9800803121000c070b1f148a84010840c403200108400d040c1c00c118030b0100111155541c3c0c019200c0d00240c4003038040c030914017910140d40e0095108d45418800b10003034503118052980790a0103540860717411039a55003000e00d65001d0b240c540c8a001d0102c0360fa602d07001040110501580c1d00c4030350003030080c1d0400c01c50501100701601d4500c003d01e00c020103000f80c281501c1c24902400120021003102c400040160320072809141c07021040381c0c040e903154001c0410000c1042c11603088065825141d03501800b0903080f03070400c040e0042c40764841d401c2c0036208000032003190054606a4003840c0320b0b1807030079001000b0244052103400030301c0c0c0505100900000e19a000703400400c0301030b008200100c0c04a00d04d12014400c1c0000746030f401ea441b82c0f031a0000c4d0700d032282c0107443c517400743d0004412041c0c1104499102d5200380440f00d0801c540c41003401c0410466581e6400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 761138723 1250 761137473 761137499
    0x206030f0a0c02010b060d020c07093603080c16120509030c011e050f13090e1207020d231015050303030903030f1807030f0212010c17100f 61
    0x1c000e0407900d44558500707158010b0103035038410724001b01040e040c2282c2400b0304003e544200096046030003018000f10707003000144a440321a075128004407240b41019290350181d490810446000e081c1c0426240000a622404550707104850312031160700c5005c1420008500368031890000c16807803912400c01190b0394400042d0503c500b08404039803013031041c1c0f001914001c450206880100314000b00b08060b4900400c0180007101b81c1413111031138002d208810101c40034054204800440d101c07041410610010001c901d0050b030700c55982440d280c03e40d8000790460040c1c4000034480e4514507078160b0310000514104009550010695003071405824400005000001da400d85900725060082454103000003640e1083c202d100046d46581c9910b81e40c50441c142c020314800040201a03424a607404d02448a400114031421f41c120700500103204018502100b05190407444c3e01d800c0070241101d50003900c21155000e58000c41806481c5c445400540b00b031035402544902c4191070000401e54480d44c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 761139973 1250 761138723 761138731
    0x603020c150a151d06060912030708040f05031f09170c070602011a030a0b0603030c070906080601140108160e19050f0a030b2e0e04140309030304090b0a030206030f 72
    0xb100d000d003c2c0c2c03074180c1081d0700c1c80c00c5400301080704203132400500107040c000b0003000c0b6018014980c14918108010861450307100090440d41a0000309080101a60302d040c090041c0401700c000d0014200d004001808081c000200600b01c50b86901c00901404030403400d03030810f0b0503001645035a803084070076041c0d510400c40c17060800540c41d2030103202d4042c81b00804501461001409410f0740106c5485804600001900d039a91600080084842001c41000000d000f040f00d140080340303051a08040e942819016031081c9074a01035041d002407544e0b807181c5141c1d480380043c8080d501c05140c0300310880d251401481c286801c00300c0300e61010b0302a44540207210445204603992481755184100f4480c59480510005100540f4140400d4003030103000158156400241c1c01180002003032540c4029603200f650012001d580500140828001261036615089070344200070b40c5400440d1001c03d9880c440c9102e01c100040d9900c02c040520707510104040001c580040c80c160316802c19140100c032480d0152 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 761141223 1250 761139973 761140001
    0x5121008030403211b0b15101d030607140f0d0e06010608010b0a05030c0c10151a13170f070e0115030509030a120f0207051501080f0a021c050d0504050111010608070603020c150a 78
    0x127210304140c41c00282642c4500016501c5880c01c100d002181d20050700660b500c61b05014040c40203600f1a40c0f24403496503204c2c1075200074011940b5188000e4038101c8182c0100070f070b082003084022816034218003101e070003030b03458641030b503444901e110704904240c0351900c3c0c40300b8142010000d4854107a1102142e007a10315900d0071414481002c010f401a52048103030000800c041070500b0018911070060000100c10303400140c40c1d000c10104807041c1080766030303088050100103550044c084200f07680407408103000c643c141009641050022940e990080c0840c0b0810001c10004181d102c034400c2c0c1014541c0f00e4680030954031b84926180540d1180b152040c2a14034400110000dc0c554500042d1011800b21400c085d004a2140340c080c080300c42e0070702c42d0100c0000700c1100c03c000010b0082100039075018141d555036840c0e60601e8001040c0c03c00070302a0403104da040580a1201660114401040301c0b42401c0040e0fa404400c0031080c10320213160880713440e0743c6c031080801c01c40102a030400c007002c03d085 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 761142473 1250 761141223 761141267
    0x40606080c030f070b0c0a0605250c0209010924080d02061e040b04061805070515071a0615340305121008030403211b0b1510 55
    0x141c05240e0741d40c00400d9810081d901416040000001800051100751407400a80d00300b00780c5034440303406841003541c001c5071702c052074240e9035072158403040c1c0010904040c0c03a00b01d943d40003a800081181c5c03010b01481a0850f920b01c030120440789180320314844000340e4403ca240396551100e542c0d4070727083e0055141c00940101d90000f9807820186c030b0a8039403070000c468650f03555200c58a0302c0d07001840041003125801d50310441800040307034000c400102c092080d001401c00d54140818410916241019012032034414801d040004034488030034101c2c004544148400c66650030001607000ba601c485820541e0400211859402e603101c0f10807000e09a80304000d0090918241890714209801501500003807003030000d2810307011620001030b0060500900e04001070340711950103085034410751049480c071581188005d030350396200c40c61000c106c0c0d09003010102403004840038001101900c034002d10344000d120001e480b100702e03002104000e00000d8031140c4200c2e1002e0024000046d08801c28030780401c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 761143723 1250 761142473 761142493
    0xb010501020303060904060c05090612060f0f0a090e250e070f120203040c1503060e13030207060c0501020d110406271203122c030703050315010e0904060608 69
    0x1c116070046102031720802e201da4032603c0d0380000f4196103078000208102004400d43c21740d125005407000d0b048610689610341040d00c1040000e481018050f400303120440c0180480d907498801c03c80031980b1900c13012500d400700440c01801d000c510003d0030004002403408485000074a10082e040d20981202080d003500c491106a81c03185200001e000042c008120140401102d50042c58000e071092481c2007003252220241e000d889000440d00300041d640d92401c0112401101c50300360041c2e22880e02d1485000c2c0d54030001c2d101c0d07003517014203400d000040e0920b0041000941c101c614141c00d52a00f00911065903d000c802584070303115030800903240b41da80c01e0500e40004280301001403913030b80d01c090851034004000440b66140c002a810b01039420802220a001b034080d40c02c0d03a1110362105070100014000c0710781c0c1e0008070001024a5031040c00382000003500031088075080000c507644110100a00001219000e4018a000d90000b0411050004104040e00180c00340e17541a07090701e107003801d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 761144973 1250 761143723 761143727
    0x20c031b1516050705010504060209040612020a05010f090909110f040c0206040212010e010e03220b0703140405060c100f0b010c0204050a1b020309030601060c0b0f0603010e010e07030b010501 84
    0x24004000300008036014040358400d00c21000c1e0032801410b90510b1403d00e071090315030714215a812101622810780014900d016494140704100203840c158440302d400384499000305095080500640b03041c4803280c22011a810300424602d0020f00c0801800d2040c084945016034404250b19401409032112070302c40b40003807a00e030003a412040171aa00401555a40380c081003070307401004100080315543d544007100d11110078080d51b40c03881c00360340066075585559641103400640d61041340d131100341c4008d070511400d10718104603840796402d45003c03885020744440356481032055900c0540d01000c0094840d20424000c0b40c5901003d500900804c041403001c03403d181903400300380d003040c002a5580460001450640d000c141c010001c1030b0001110390f10f10801002160218032040007507440072810b85001d140400056003d05290b1a107141d0071803050741c58054a100181c00c14404e00d140308001036840e10258490041c00704690001e10580580004141c4c60304c0395400151929030188001080d154 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 761146223 1250 761144973 761144983
    0x70506060d110108040213180b07022802060d06261606080903070605131b060c03051602090a0209030105060f06070b0702010905030418050f011a070c09020c031b 71
    0xa41c110350b81290080e0810700444254400400403a0300c2080180a01c0308000b0900c0b0340c0368408441d51008104400500300820400c0d8000c0458046620511041000c44512041f4100003016012170035481007603031001841601074030002d000198500000069044802c002051052804403842c2030f6055000030396685401010409000a03410150708001c540d1255034416070000c100c02c160303401d2881070ba4a41e01075680036904540b1104c0712840c070030305000c04112910541083c0c0704204800c1443d050010b00020a41c01c00034090040c08070300410491160840030300c1040c1d0007440c503d0545400480031009400c15903905001b9840c0c4030004d13684d401c11001860b0010001030035541040c02d683d42d030510b0840c0003000d41085549031500340000038400c10141002d040102c22a4052120f81c00380001162030080c8040d040204c6840108101c88059402410f6400c0066503242c0d200c0c2c1da41000340d40d0003115844000034603c0083c552480031404009410b100200c4203105804850300d141d004c2d503c0e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 761147473 1250 761146223 761146249
    0x3050c16090b0f03120f0403061107151808030403051201080f01060b03040506130503040e01180b1c02090a02090a0807030302070b18060904090b0405010914030423010507051207050606 81
    0x40c0e0010542c0c00c1c0c00400d82d0068041d00000e0500d2078a0691241d40784030541c0d03011810000142002f08500702080415080e0080b03403002c2e90001c100c01ca40a06409a1a801140019003070400010124007450700c21070881e000e15807280440381582d6034510645680f000003181483c41c551800102191500101003102d00464100340240b4082d2110004002201c0c4031400844961000b00070000340003e408200fa40200505001091354440c09190034058545121900d44681b4408000c00c0e400200102ca12031445e07010358801c20b841e510910520024410714203002e900c14000030000400750f01c0020340d02c0c151f80c441c0d070945510f29079805120700f0724000c01216142c0c41200002d403a03220704160010384a0b01400038404a0b00210a403204610100181c6056400f40d4490560b2800d0201301c4000a00d44480800214903146c0360a0100001500c035002c19000590904101daa850b88a8000d0324061a089004c0c0c0c0c4428000d401c10070350070303841100c04840a006180005260389000a800c0c509 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 761148723 1250 761147473 761147479
    0x509091b060d0e1519050705030a050601110111040f0602030f0a030e1204060e03010c0e100e03071703030a3813060f03030905090c120403050c16090b0f 67
    0x504503910041111a0308049003040503540d030751038403800b401001c01c100384100041d01c00701503080c00c12209001210391a04200a4030900701010b100400c2e500c402100d0780a0821007001501e40c80742401210030081072414510258202040d9041d181c180703030f00030811502c48104a1440c5540e415090307840b400307210032111010005010b07103410240a908070f01c0d544400c0b881610b0040c4404216450250040c1c2c00507000660141e00d54840350900344290102c0300e04600b030401034450000700040300d00b076001025100304403140c90710480e0b80d01c0811160025082c200b09400c0203051164030a980d0f60070440382090b07080d060540c1c510516170110a41c1d41d0442c1c100207940c40b18491940002d45015003049210340010000c1c03500307011429548030310742c00b138004081e0510409265003401800204590441c91180c1400014880204000402c9a9890029422500c1140d0741d9044c281d4280c081d45154504034013030b80310610b0f2a80440340b001c00070f542c48a80100302042d050002d2140ca001d031001e541b90 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 761149973 1250 761148723 761148763
    0x3210906070807120f0c050901020d0309111509100f121404023007181103060f030f10470a0306061205010b060f0909040f06090c050909 60
    0x40c500c0740441c0c0c3c03a070100740000845c040103d00c01410444415000050015001050003000c542e0f0600c28a0803e08542ca400e1008010383d803501c2d588101601c001500c1280b07405400d00c4d0f003a902005032615814010854515084407400240400400498010024101000d03980300d090f40381c422880407000c155032007103040d42d690b402d2211581c04a400c1c01c40c100d0801c60b10300c60030844031062052142030700c0e010f4000603107801e00e044114031051408071115801e2496003107000907403906590b48542d08031102d40714540d8840c00300e0b08006280402d00102d024003592504c4042c660307002454261203184021011505121004141c9c440401d111802c01c904000d10305011704038800c1c021f2080f0001094145050741e00d65a260440d402c07540010941c218203090700c1d0501100f803040c0c4c3c4c4903071004c2c0c412519060141d03200c184948500c842180c0706001c00f0b00030030b05202403495195032030b50740300c281040f501c0d181d0704040b002d4000501c940e07031040707518000007820b050010070355400362609240140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 761151079 1106 761149973 761149981
    0x20c03070f0812070303060e070c0c060806060307030f1121010905130605151c0506070323060f0301051e07020d08010b0a0c05032109060708 62
    0x1000700c801c00002000350b928082100b202c003440040b450383e941d580c00c1c40e09900600c6550010054040100100511150000d000c8141c0074004d80042081955030f07041250311407800c4600c1c540014060020803207041c041c2c0c202c2c0451242821002c503440c2c0484410711101e1700021016000f440000f42c2d00c920120280d02001d01504a01c20180b05500d028100c4000e001804100207124951b0741c4002030444004090b0746040c1b2400031321503c0c900c401c0e065a041105001001550341d4003440c4041803056000b446491554100200c85542800c1e0380001040032000081269800890800c00000295428454640f080e215581c0c1d03102443e40b4950002c0012100501490955000c004108109500304603040d04681030800d1072a500d1603400405c42d0701c100c80c0d0740010b000d8807000c1103403103000100403004a1a60341c103000361600e5950b072801107a510502500c420700403c071114003003 = true := by decide +kernel

theorem cover : BRFrame.Cov 760971223 761151079 := by
  have h0 := BRFrame.cov_init 760971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 760971223 ≤ n) (h2 : n < 761151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
