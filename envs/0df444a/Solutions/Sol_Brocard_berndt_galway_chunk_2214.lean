-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2214
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:00:33.65884+00:00
-- url     : https://prove2.me/submissions/f6e47402-9f79-417a-a438-e0cbd510301f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 398021582 ≤ n < 398201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 398022832 1250 398021582 398021593
    0x1802090604140301141017010203070f0c0303060e040f05061305100b0409150501030302070605030f071d150405030c060708030c07020a030b010e010617060d080d1119090503 76
    0x40006419018601512040c0180312598100359942517009500090600c0100c007001d10b000b042214080f1190b126000c0c41500310745681e4213440d81882140d10440d1940c440c01040310032508101e130040c111030011800e265a40c0780c041000104503108a2003644a1181d10100030703071a24146080c6003014100b9941e03e040c2ca41050005480840e10b283c000c40c0945001030605211000600a0645120041c154802c21a0300312088482500305e2810390303003e50201c9400303e030b903490b086490f8070088440d1074024541402040c4050310903201e46e09030160302d25504024803540701c0000c5030075003c900117041480300000c08004600b400d108801e20340d802225101d05004160311225041c0c0301c0201000880000081e65004568031400d000d000f850304001c001d0b43c40e68403243c0c2c181c581002030044101203250305c030001c0c12881804900c2886440068141d0595804a40d1002150b0b042010241802500c416500c000400030b103020b0701d040b074403c003489142600c1c81c0038003400186081d08078a00a0300328 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 398024082 1250 398022832 398022847
    0xf020318160306020d111303020a080303010617070e030d08040303050c04030b0406020a0c0512090103150503030d110d0e1b0103061518090c051315020a08030604020c070608011802 79
    0x81040250459800071401350f83d500e001c00c51040244004980e10380c518002140d002c00e00d44810401ea42507038401c1c0d504811464860090715500d0009126000c00103444d019101c00c40c884010383d20380c1280765400d203031021403102d50000e800d2581200701d52001a08100800050680c140550341c9c10080c414103040c6020b0461f11103078124000100701400c225000950500868421404001510b4001069803500306050402110641c0801c00e024002810813050300c6140c1a56000e103001c40c1c1000f03005614003030200503440e016240c030300c600d0a00020180600081d02900d405400603890001000c0c001039900d1004c41d002c400ca1040682d0f0402d0b10f426418881601c545482c0c0b0800007203401d0025404103c40005441200345400c051581810305415142068000024051034040035089000c01c2c2d4560f41c0d1170301e8100344c01c0e071080016802140508045907442008682090001d0409481c0a0345171500602e48202e641c000c1001400190040004048203150b1101085c6008001e6140a11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 398025332 1250 398024082 398024113
    0xf0f02090102121e2209060501090302010c05150a091509080307201c020d0e03250b040314061e0c030711060f09070806040c06140c010f020318 63
    0x12551140255160000325505030184c0380c044070964440d1640e0301d41e03450403012030084100110244c0c000424030f103040c000c0303818002c0740038a500380c071410f03560f5485c100c3c559001110001b149290503241d6005000480d0740d22220395409034490072040782c011500c5000c0f40380c2100204c07401d2481d2841c3c41d15107258a400941e15004685c1c01c650540b40c10500e180c0c000c25200c80c1450442106100ea11850040100c401040c1d80240000c0b000b58003a0741c0c400c18041c20070342e11040e141d8102903154101010001081c080384c42c2034201d0044018014245645a6480501c242d12940040c0d03001e009808824102c0328041060f1a4040000c0c0001c888a02c051010094480000707400d051a0a501200250f42c19103d003ca078043e10344240d0895802c2c1c10075480c0d5044141d03054500035102d00500b0f10200c0e90110004046020302e500c4001c503030700c0301c0c60007001b111180706144000880310010001100f88900901600b400c00d00f01754001683d038100412084106203040a44040c10b402014040071281c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 398026582 1250 398025332 398025343
    0x80f0f0a021c020a1206060f1514030c0c010f0b040606230304020f040f050402090c0c071503090b0103081c0903050904050a3b300f0403060f0f02090102 67
    0x40341c00768801007a40d00c0090343c101e001741c0016800b0003810031001c0501c40c40f42c0015003101c4000d03490103016502e4945002e072540c50f100f020b6002c54000100003140144403c000c40c0e008424500c0e160a009100549c1170a42d0800c42c20490465160312000a03245814441c00e0020b1009040885138607656400e082503200ca040024884d209002c00014255111141c4502d89403000a104008026140e01c20304001c20007507505a0080030f0410004564034415001c60300d603413003c3c1004000d0685000210401c54204050a00030907484903007100c00210b88511260181d4460400e01d41c540d00c0d5525101060003a140d40c0c602214101596900400e8100c4102d40c0d2988043c4c41c0812580c0d5240340dc0000340c108003403443c0101c010031212000346405145094402d494400c0000002e000c0b21031100d43c5c0d88256a01410385588640758140c0707404036008005c601c903640020207401c7c8030b1441e02d12840342d042039005851032a2030b03004006a000c0180f148100c181c291140860809043c2c0000035943c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 398027832 1250 398026582 398026609
    0xa061206061703070f1712040b0f0601020c1c080c030309071e0308040303081b040f21110d03090306050a02091c0c05010e13020c031201060c030f0807030f06080f0f0a02 74
    0x14020600221002d152000c84014007c0c05503d20302500305494034800d0040102c4152203004002c50204080b9880800d00d8090b03401c005003e40602882031410000070703140345000321060142004070003140442030020b94403442c01400504411031501c81004200018800e010f0815000780f101480040c0d1403d0030303241604e80624105405a885900c82e4010000c60079251007080703000310b00021015005840300c000d944882440340500c10700c181c420583d281d04c0f00c0c00100103810000040380d00d07042003d40450b080e03000340f806a900f0b60383c81d21000100e5009640300712072680c00140f103803590f040003d100300e0740e400805484241240c05446561390030515028480c10030010040844565442000741d03000710311100c004542c0c0d080b03040b0348a641c4e58001d404d0f00c1c85810101d000040d51500448840e000030740c154840c08042250030368100c1e618440103001c541416969a99000c2c180750900c2030f040a01074050040c552840100b11103450b1424202d202c1c80d003584800341910068130b40303075022a41c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 398029082 1250 398027832 398027843
    0xd020a1202010b0d05071406090d020f1f0309170a090e06030708030c0a031b0c1206090b07020a033b01020102040b0313020906060c0c090a061206061703070f 69
    0x103005592000ca025241440009900c0001340c0342d101e00b40b02d004203081044038a001034046980c2c0382003060001c2e46c0580403000740d025150820550241c140134441400c80341c8001c01407680012451900c00b600b0b141e1030401800030355200f14020420120b10001070169812100f4141020b0081c140248041d4aa00070012100000c0d004264151400c100c44009490280b098070746500800400556411301d540d0b00390005003500071100c00c03801e0048840c015181d04420a070942c02d0808038400414240381d401102c8441d40d1300000c1d804500c001c1210340c081c0c5030710390141400b1150360a0060014466448160079101c00c403286420f14241190000608a09140039155024070000140d009000e1940203800700c0e4000000c10140d482c0010035070580c14402c54005e074054503482c0c180429401490800f845692107500c05441d54a40910b480741d0000000340003140c80c0313444490348080b1959640040703803502e071241c0050144000782071100240805690042d820803030541c030344405070703000d01d03c1c040c08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 398030332 1250 398029082 398029103
    0x7050702130c020f15090c1c0303020702010903021c050d0f0c030c020a15050c0d05040b1b010e0102041502010e06060109050d08190906030b0a0302061b0712080a0801080d020a 77
    0x4018001d012040400c3c240d9070944031040c000c4202e2030460300c400c0350382015900581d1f110741024a44082d00c04021500103040c0c802c0001c00d642c3c264000d5206180c1603040c0704881c0400030050b650002c03c1115080c20f21460111856546000c9103010250340041c4140118501e1030110558800e0045079420b8051503c89030355041d40c000f00d00384a80c00d800c030038110a001c082101c88550440c008007141e1140000b10b80036040500421541401540148170800078100001d2842041000101c000e84880100019031248181e200c54226805a4071052800300c56082c0b083c3ca068083c4583c554080b50140504003c4c0b400d1000200500b10a009551258024032100004c0c4020001668011352203049a1120170305040d40140c12070b40d007072058000190400103404642c0c1000b0315100c0460358003a109509002d40001320000004c0070b159814968031600c0400200e03d0f03010700c650f182c568025076002d607840d0038400c8000c01e806030581006401c1d6002c41701c07050b4a0355002031200c50844e0491000c94 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 398031582 1250 398030332 398030351
    0x1406010309111f1103030907090b0301020c01240e041505132406330e0307090b09010609030317061f0201050718030503090402070503070215070b0705070213 69
    0xc811182d0010b40c290410300749071031000542c45402948001d9802c0340c030740d2800c8031010010980d982c4403c885060f520707085140100881da01c80d411100c070000000b00058204a400801d890031203150b0002ca0b9200d1200034000034520800036040c101510302010100c06d28580307600c0e0030303078483c03d50402004001c1e600c00004050b040700050082c003145d44401213000c1800f5240c0b01c80750301d6544006603003601c3c1c40c00800161040141e0f03240d8002d8007192007000703008460f940302450110004134482c4107100c070700c903003851840d9018403095001d40741c1c100c9c00054102d04031091140b41401600000d0034414942d0052000ca50040750203a030680e514005041c0310350b5141c001c200070b49802d02800011111107205c2e104d0143c0c064028a10907139195803000c01280111218000c051881d11021741590410450f261190510750020b211081c081d40803280303400580e50100d0b1400c005e0420120f101d10001c02d1030001c0204415041e030308645149400350405a994002034011140340c1c5103450226590003090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 398032832 1250 398031582 398031593
    0xc17012706090c170d17040b190f02190207030512070507090e01140a0507050d0f020c190b0c091c020f03120c01060e092a0d0309090f1406010309 64
    0x1182d05551000d0341040c0e407a900c02c100050004141224840d600611000c095000e105101441c0c0003140154031038a86d84a81d201c0d102c0d0004080c000441403440c2000340309500d0b0042c060f07402c40254040c401651142c012b00c240380c020000d0b40002045400c420420404542c002940c540a004c00300c140c40e030b40e40d036075180a84c41c0810075072003204914242000c002ca01340301988003490703048104503a81615507451000701304035581102c040b00810f0381441007944c1021580d00c082d14641d42690010b181448800d5180d10b0513030710207011002058485509070410041d100456002010720130b0450802410100203030040c02c0103584401811b1841d5580025581c1c0c1d80b280814201c40601960038806000c501a50158080c460300c022940c24148000391181122000c0c51240340301401800e9580315503490050030840d14140380a030202108510600c0b951a400803001032442130310f03a10f10047c640b0340712400b507490401504114614140c1c031104505109108258030041c24a40001c08900c1d51501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 398034082 1250 398032832 398032841
    0x9070509370b0d030801060f030603060e0703031211162f03010621061d0d051b06041205131205030705071a04030620070c17012706 58
    0x8040075601c0e850005642080c4008014454219400e0306100d40e900c42414400103104103680203000849603001045102e118452602628025150114109580f80c8a06080c0c600181003554581c211000c100101364028400d1071081c0b044c0c4500307200329181048002010f00855003d0b1056a03808020001009001508400004d43d420444000c4007018110000200701e111806802503180103000301c1c0c0c4e40c103c0b40000d0150b94244424a00b1610b03a51703621406090724104400c0140001403400c42c100b2000d0108a2050605503240c0e515102c421041040d298517110300c4030010341107141404007051303420785420a0b840050501542e10702152022044040540d4000d00362030808802070400c00001100406145000d03a0480b141c1c5a141c01402d0010042c0d9480c00d988804100400c000184650f0840c1c1e0b11084880000b00045511100e05502544416000c481c8510403010a0210003440d04044002c00c2d45400200911b510840e40790340303c06480301d41001304a00a00d03804081001030f030013 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 398035332 1250 398034082 398034121
    0x2202040905060f010303020c04110906070c05060304030c02040c08010819170403030e03010b0a06090e1b0a030902090903090d03050d0902040c0c061118040c2007061709070509 77
    0x4555007440c04502603c3da032507080c0400c4005004285910410386828010544c444020b0072141e481c1441e0101040116806400c04461801a02c2000155a540c100145214501903290b0b55a2121a841008215890ba200100030b00864a0041c04154000242603035280c40280c08036100c6013040c100f6502e441203034240c48500308030008000c410982d0040d51401b8059040c0c0091000f140300104200b00303011140580800a48500d0042114103491180b8941050030140c0c11104038840041500d810745c0314a54400120707444903006000c500700403030000d600c03480c0800071b5800e110140c00000c900b0f104040b80501041408039810350400c02a41c8035400e41e43d401001004504c600c40c0300600b030407400803401d8514915011080d4041c83d100c200f01c035200e0080d800104840e40d042c0307082000411840740030008120000740855483c2504c00c002c0100007010390010401a031070705000030031182c8034580b11000030ba400c1090080003100024240c080c0e6134200e544200c1035651038111106004001c0303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 398036582 1250 398035332 398035343
    0xf100905090c01020f0114061e0405041110020d0e01030218060c07060f0801081009080d05190e0307050c090402030a1b0e180c090703060b0c030405010f0822020409 72
    0x3024070a5001c000a020410400281c00351142c0200c5606564200c41c034005080c0c11082001d000241c1526200c01009820b00b80800004503101e10980400e044440489040307815141e0a4014100e41c9000880f001d20400e10388000c041d0005c0c41040144000c0344040c905044c5134010410860f000320040003442d040c170010b0705d07150300d40104211081c0e481c4014444c510120741c80d035044080c1d591003118002d058074054002000445001007406004040210094421110901a007903034800c0780d02515004210050540f254041c80302652070460f011201e036440c10341d204201c1c81c40003940c042a032410b0114102c40c20b030303000d69072400800d0a100e5640d800408002104108100070410340740c3c40020780d49221000492036880c400185000c0000c510208070641c031040034411140342804807250b200304903190201d040b0341c2c3c800d40f000c000e0b00512156895a00045400d104c83e50340401810ba0821030351030000364a04201614109820109240c02c20a402a1202e28290f407190707001000040c1e400b5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 398037832 1250 398036582 398036591
    0x90f060c03070807020604050303190b0d0c08061302090c090402040305100c0f09060c12020705040f050603120708030a020c0c090702010506010f0305090312130204060e04060f050f0f1009 82
    0x541480e096600c12149030300400c4155011500c035900c00100386100f2540300c0d00461031902c1e2000417101305034203500300710502610f541030001903440708440c0c0c0c0000b5105000d0360100c1e80c00c003401181007110007081b9404640b40b40b1030803000740c0d560340072a5030008038402080e80e9070350840011070701a12890f00054528031071080e802c3d00c0005540c0c000d14105c4181d90300c2c0603204c0707094001214000a0f038844d48001403050b07484c400100381d110310001c000c0b44241c011075044aa80f10041802c1d81c0d040141a400c00340d0350000c024181c00c0501019601d54041c00400c2d2401d00140d86a02450002a007141d00a5502140e4094440710802c14411500b40050000b5a640b51000d002070280100b21400e900261902440c0d10025009024641c012540500a1410941d0710801c94243c110014005011010008282d10160b10399100d607001500515011080768640350a0807070030ba882000d14401060301e04400c00030f0145000136003a8008484512000250f101c694028260b03040329048166584e140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 398039082 1250 398037832 398037841
    0x2060c1606180c180203010b0a0807031506021b06090105040608070e04050a0603060c0e0f0d02150301030c0f1d070c06020d0f0507320306010c14030a17190203090f06 73
    0x201d8054003229400404031000484c070702400e8080e40028841d0f100360441c144001001d19018458040e88080d2030b1074002241100c9404601185099a11003400340c2c0000351b100f9100b41c07400115041100c0c2c2a50206e1030024900c000070000c1c8141e208110810402c1c4000c00d400c944210b02405004a006100348410300748040408001e05042c0310031a805880d00e90b02c0e120446c001c0c851910140c2005020054001d4414180310140d0790129080364070034007500c1c5072035050b45005c0155028501078268030502c21700b00001001110059007110031900c0004041807001a40e031051550303c50b1092511022140d014075008000e03024003284815004d081060845500103168405886042d15558050145600510054450a6180d0100320203403843c4039001c13003503420788010358100c80b0614142906800340c0d03c075003000300304103102807130150400103000d003201d6480707020803042070321811401003030341820035022000078010650219100c1e004800104d05030414083c9500e15042d80c02951070510340f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 398040332 1250 398039082 398039093
    0x15180602031201060c0b2701051311090415021b0307030f030c050906091c0209092103071b0c170102131a04030b060a090e06060102070602060c160618 66
    0x20b00e4151528003000ca000055591040c440202c2c12900078072120085e4548651811202043c8481412007103003041e460b56011401b40f1400d44507c40d17402c0681e0176812149408010b594500d0b0141b842600d0150502001c90352004090041724078201d40182e6440801c00401031120794030001401c2d030f010208180d400c0c9500100e04000400d103a54081007103580d010740640c1c40340910142c41d42c0040c410301c4141042c2c04c11380d448007600464400d4031844080c03641c1c00561420700444e141c0907142c11220f504a020491414502401581d1440c030790b08610b40302000401002c011a00161408080101c41d03050003a6401da0070f001d003035014104c940d070001d4610100d02079070101d8035000d501e100000e00041c0e412000128511050603507014070740ba061131a200c00c481ea10001d081e45d58043d00500c0d0000d031416451058050803a00d06024210761319140d00003a040c00904e03803003002035420110401048145a02c112400d000054090361a120f0036410f01c00300403c1a41c07103800c0031050300d0308540c05200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 398041582 1250 398040332 398040337
    0x1005190e0d06140703060f0b03060319081213022b080d1e090302210c0601060903021002010903090b0a030908030106020a230d12090b040b0603011a09011518060203 72
    0x10301042c03c0070194481840031001c4a01d18850705203002440d0000b4440160050000c0d030f0008001021186100e00c00d05140340500700d110400c072094540050036820700c0340c2d20804d6640c04501c1100c92000d03400503801042e990280803080a0008a43c0c0702d1030b940c643c1c91850201d40c020f81203a100c0c0d0300d9200000c09600140f1449803100e004d04c3c05c01c45d8804101c0c1c0b16001f0382c0101030345075019091002680030820700040080c2012518280d00380482490000200080c60003030503159186000c1f20b1540c014841070300e41034003d800c1164104111100400d030012202000c980348488950343e640c02481e000c50040100820081050b100000002941c0b0f90010350b45403118040c11800321180d1020b00c0400c0e410040800081e01d6030020059082014007405464810000201c00422640c840f41d4441010303035400c407421178582c484007003400b400c1d0409208804404440d00c0305203410307020302000602d462105100f500c415505404102c0c941c0303813040400b8405400000828080782e80c841e40c01075200c0c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 398042832 1250 398041582 398041601
    0xd050702030c010b1c03050c0f010c1d0103020903071712040306050403110a0c0b09061c06140307060c1421030109111614030f1b010b1005190e0d06 65
    0xa60070514042e1340d501e05040340400f05903408810101d1480e4035901510b15410a11074602c1d540a48050044841002c1c06004000c403616602c1d03c0300d00c00401d418443d00c20040000504151051082c0c500c141c40004841c03040d074102009821180d18000e4006140249101000f0424180450000100b020325005207018600c0ba4440039160742011403444d9490034a0440500b078a4480c000812150800300010310607680d02915a41c50072030080b102400398169900d5010f00341d13079160000c0280a2204003005000c4030214054550309181c56001020320459403800342c004840d09101f401a90300c10000c189030f51424102484207440e0581c1071001a400c24440d260102d402d01420203414000141201ca0244d0140794644080c1810b844001c2038441002c46d0f1b5026200c200003030081031103040041c024070403c50f4a040d04c100030507491507007034402c1142c01a024021034200c44032203036088001e88030252140c4551000300c2010940440d043c42060501a80010307a0800480512240d0381001101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 398044082 1250 398042832 398042857
    0x160b090108091204091d06040b070c0515150a080c030a11040209090c031906030209070804030309170c010f09050a080d020d050a0b040c0c080f07151805070801090b0f0403050d05070203 81
    0xa0007006c056a949602c001c0314001d24a59030100040e010034003c6842c240824000c008485845210f1700301039840a40c252250030304080034800344c801c0c40c5011902c20001d0103550010701094038000d00425650804008001d000007180b1072440c85030380344c41d8141c5072900c00061000c3c4950a20012000e175a03403050380c909140c40c2d2a4501421494424042c0908596010f0000086640c2e024000c0f103c1480140c012401c041c3c44040c9080429445c080351440038580c03120b10350741d801c2c0000e4541d08580748065a55081402d00c0710280200d40003003041000c0603005440d403640d6104240701040284038500c800c5007082e1901c3c0034400500d2040d4804e000460302a9400c00c105204010282c40c840480d950040c6814000c1108441002d030784800303000d1030f92056000e4800240c0c2d0030501001c3d1054140600c1400507409012400d0010030001c020091103d44020425501103849400031303cbc0c0c00812110200f03000e540860105403084017205c1040942e142d080201c0d081c0414000d41707923481040030080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 398045332 1250 398044082 398044121
    0x4050a090b0d080a0513030c1404110f0a180602060a0f1b0e040603060e0307020301050711030304031404090f0e06240d050c1c05160b09010809120409 66
    0x8a940c03280c49088907000c8020540d5405941507035441e11103500c0350b00c507141001428040345401b401160060005184902d0040c208a41003400400700d00500525007803085003080202210010000b084803060388a0b0030750244d40b00300e0100280d64410448541c0149450384890004189601040260043d8005042404003143c41070444c015a0000d006c07290304441c3c0b0a180c039402c1c5008800510b6460300242c00461210f0f541e4668000300c035258007890503e40c100059030421450700703100346030348041c580c01d01e401c1007048448030701d40d01d0200800080c10310503154544190b1409581c1564003d2040440a100500350400010003030b00c0c3c80043c01001d8415140410000d062a0380354440c0c42c550011030320322a40015003081150031403500251240d00030b0020042072501c1c5c002090a440c00300446c1541017280b45c0ca4102c1c5852000d20f0400880c4003c4401800354184480460703030b070843c09282640e90303034940c2c10328241480c1c80c03030f65080340e60180005c00107150b11041e00060380c65403031018081d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 398046582 1250 398045332 398045339
    0x50f1005030c09180d0203030405011d070303050c03040b030c0d060b0a050f09180906040b070804020108040212161d01050307030309031506080d0306052e030209040b0d0804050a 78
    0x50460190240503415000801c1401207820841211079202d10101000d5646145000b003590420516604003030058000100f08402c2c01024014020315a000c02e492140d111064904036840b040741d030100908002e00000c40c04030f441010001da4001d0100c8404166407401e2640c0403910560010201041650920f900083c04824078001d031845525261103151030212202004030b1154010071090398010310a01c0400f05130442c000e81c9510078003143c0b000b40110305107070070903100c3d40d54014082d4040112010801c4014cd81c000d030f2450300240e040d202e0a030352840d106845400d05903d0f50665200e03800307400e00064042078030114000a03c0140c4080c841da41d0321130080c1070f1102042d000140200e01d41240400c0014402150354000c800003041c000be06c1c0380c4035191981080c8004dc0c4040000340c0b1041b0070b00940ca0039401c43d100801003141c80100c0a00d01c140300801c0c1c015014204010315501181000d0240c0380c0d42c01403080b00400410956068085140101e1690064055203004040642c03020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 398047832 1250 398046582 398046601
    0x5031c0605031606080105010c0f080304030206010e090a1106071e0503130806132a090525080601030e01090c0b03040c05090114090601031413060c030c1d01090503030c01050f 77
    0x1064944c159128085682000019a81345202840441d52000c001104c0000324491401a40c090342c071070f602910304e952400711007125a543c0582354a0003500242503d600044032402c5048100c04199041511141c81d03081501c41044112010805441e003c0e8951007006008401480c0b609112000189141d131241d41d41070b81c822046540700c001c030464103541070128205580d24692040c030200815043c00691020b01a840a564401802541c4070000d001400108003248030844940c050140c2c80340d96410802002d40700c0c00707401c4038189075581a142c0c00301002900708100498100452800d4503a548000c1070081e4012078065a12059030003008c039180c584410043e0484036810600ba01100300e00003013000005024050070305140ea54034858100c814054980741c030481e601900f41114910174207100c1c080c1c1d11400c143c102014604288030399580d030010b444100c8481051002d412030b040303c40042e1821807407500080d03030603c00800e1751446241c2c150402c82c881c0c907005460250b9900c0b0351151 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 398049082 1250 398047832 398047873
    0x606091508071202150f0418110726040b03060a0e0405060a050717040809090c09010914040f090f050c010f080a150b0a0c020315012105031c060503 65
    0x1e0048a03007080c03030100329a0000c500082c04550005014900c07056041d141160300350f12a200c240c40c1100041342c1000300142c44040c0a10400e950441884641c28051500e000c1d4030400000a1000c8091800140140d418590468025220320301142d9140e0311903130300300c1c6a0b403c01c13980c03d8403d2844810120300c000108000902441e400401040503446d0b480c0c0b18005801c0041414041000c400d240062282e2034502c410301030f80c0166107007a56243c440045c01a0040000c01c40009004208001142a6842034840c402c0300d46c800d045414180c02080080c2c080d1103c0d51a9050040c1064000414000c0b2109000b0b08c841c801c2044a45118031900195241181803103030701c010070544000101c03207204581100b12241ca000e8050390b00d842d1200040f4420360010099031000846400d030000c218101045124010040820320303174440d62600350a8891140e00313130290301c2420701103040e0604002041054805018031420300b001c0d450100c05109004020500c241d611a10501070000c070b6490380040f2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 398050332 1250 398049082 398049089
    0xa0807090b03030f250b010b0a120501060915030b2110090803070f180f080115050d060902272202010e1009030818010905011b0b0613020706060915 65
    0x110ba810282100b40498a0440c1d40d8005c040b0405003d44d81c00c005031207070310864007074900c3d40c80254854030b459200600c200d02000c08070303007071500e0b01340140300181d0011100002c032161900d0503074001814500850180096a04040e0051100000b0f07100c4402c2440c0c0c4c0001403d50b0300d041341d543c0004042c8800581d42e4003900a04041410400f042c0494880e1003070071036203500c90810543c1c6401d2840c62104070383c102e0744800c0c1100e00700081442441020b020360020750034110504180c050600d000142c0f14042160018040c55448540c4821519000100c8000480c2c001c0d07070b900800c003450949030580c0006c943c004c040d020410704602c02a40ca00820300c0009070181e481c2c0d11440d181c407090100c1a002c10103000b050241c560700c00000513212500906200c3c01d10800140c0d10810100050310a2070650403c40c10b1040024500f06010103080400034001d410202420148d02e4080208421a0000c0c01d10703040c6d1400003403420188580c3c1d070048402c488407000e0401c250416800d050102005500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 398051582 1250 398050332 398050357
    0xa08132d0503121e160302030a020f0d0f1a130c09050303030106020f01180807020f0f040c11060106090305121602120115060e030709020f0c0703140c030a230c0a0807090b0303 77
    0x182e945c90a584030780e0255038002c03401c210051a26070550098410b580145004e5005030342c6461100180c68403d008114680c018500882401d04000c40020100da800d05000659144d4519101c1000c610608102c4010300024090303a50383d58658030001d4036142580f400d00c2c015800d142e0b0070b028020191001400e120381008003642003d20702d908200ea0605240e000d60750020603007400001541d1540308030001c10342152141c01c01141001d14440c20302070168008000e00001c2c03032041000c00c00200384000030942501080d5a240d0b1300903c0001c503480c0818010b9002000328140003032203403055000080c8400d05850440c08260781d480c00711140300341c07000c0440d0540c000c42410002d1b500707030703030041d0008581075400310303050442c1511110f207450229882039034601d01c06079048901e01400d000060790f83c08240c02074241d80d01d16441d04810703030009a0902242042070500030340300710428000c40f43c2c5000c00422104216070744980b07456446007a4001c901c0514070380008880039190000844140e0303041e48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 398052832 1250 398051582 398051611
    0x30f052503061a060301090204080105090c01140c01180c060e0d0210050a031e05070f0323060d020d030203040612021207080402060706020307050a08132d0503121e 72
    0x10395410028201c10f180000c0c1c0154240140c140c950381d00c40245000c0c00d00c0540040c0c0380e901c0e10b0003503070a696010b00901100e802c89039042e04a642e109420304d1300c00303602e88d00041e964000211068014514481d15154203d0700001c00c0c4c00300194800d0714003c030380030395903925865903110f410040c405c160640300a41c02242c01400200050080003e0075100c4058280010f200c1c0070049800c142f400140c2c0c11700e12196848041003600d9401c00300321130603000c06c0d02e020840c003d050196640c1c0101c0b119240c0e032810039582c00117580c0340c0c1d540482e447c08a6000d04160803091803882c001e540d94003d40513603804240c0200385000012900d1080d07820042c5407d40da054151200c80c010b07200076001030300a0b41c00003810454440031800a00003540034076020b03034a5a41e12410300400509140c3c015280c83c002900d4556100c0100d00020303510798403010801e044841e85980c4001a05681418080003019400701040d001030001d10020704902c40c2d06400c1c601c90301d4001c40d207045240c1d001e0442c3c0d0b070008140712 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 398054082 1250 398052832 398052839
    0x71b05090f042904051011030c091302040305011b020c010e0d11060c12090f09060d02090a02220302093913090c0908030f09062101030f0525 62
    0x40000c6007104407064582c0343d40300c2c2441d00720f0700b480c4075013203c0c05ea4941d444190208180302c0a842450484034140080c0303415401d02e80b40900b418854040000d100d01e0031003800d030441e6a0b05504450086511200801041c0311042c4910004007038038031040098050303000c40c106a94020443c0e4144644010000b050866103170351413080d1061000c0345180c00003006c0c49015141e000c1007005030032104d0300b141e406448690f40030400c0380f885480c24040f801814800180309842d1251030006503607070b84c101d424458954402d0303682002401038040c007140700ba03503d1110751406041d1100b0481924001e40d9200b00c00c6d1394038040c0034440720070410200701d56039408100043d004400b03024940e040c01210321641c42d20143c561040b8502c40d0681024980c81ea41d80065445290017484000080174080c020754201400040f2200050045480c490f0003a01c1c0010058540e032920f03040d808444c2403090b608511941c503030601864800c40c4500031215445070244d1118072101012400813000100007001050608 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 398055332 1250 398054082 398054093
    0x51c06050907030803100f05010201060b0a21020324061911071d0123030309240313141908160507060f020c01050414060f040b071b05090f04 62
    0x5000c41d032103014452002c000a050b0a005500502c6c20343d200d440001d040244c598441301c5e55a000a065a1601004000d0742d03240c0c034141ea00b509c40e0340c10030002038000f08400c038000072100002007a00328400800c10401c44640d0128100038110600800310600d040c1c01441300d20b02c2680300150030390640d10002114103100700d05c904074000640e0103803086e09959030301032000861307510a0060400354810052084181c868180340100c28440c0c1100b90501c2060046601d9201c2d981c0000d008807174a030508101c610b50860404120382c0c043c10b0450341c034030700942081c0030303202000b808848a500d44440350006040005000c01c4031190f016140a039100e00d580c80750001e0b800003403811309081401e5051404654103100b0400140015240c20030300c1a68220000c0c00c11a81c600c5440c1072150600040c0903200c0010030102c4040e205031074141e512002c820b2041210700a943c84545041c0001a07000100700b40c40d880403020f1003c1c8485041895295000c102c03034503d0450300c115105940c0b40000f404a070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 398056582 1250 398055332 398055341
    0x3090803040209090f10270c0e0603010b0319020103050c0315040207020d06140609061008190603050d03021e0403120e120d0203040512010c0807050c12070b0907051c06 74
    0x541381c1107032044100000c0c0c60b4107108010500d00c020300e0f603480d080300c001c1006c20007a000c140c0c0521040780003010035588240540c44240100c00a2400301c03000500d06427000d50044c81191001803c41d640d0500c80c680c1002c1210805204078000b03400d110118540c0b40d403800949004d668848404120307581e2100900000790000c01060fa4442c0d030000c62030012800c00d115865242a00c003140c81d41c0c0307203000350520890080161449001d61744124201149640c80441607410240340700310701420940400814001e0400740e04040c0060041440300188580c06500500914500072040640d408140302e070340c8024040e51002502e01d51201211400d840d102e031121586052008220900f04a2140e00a501d000c100c00d0103000940d00c0020305008038508620700800c00b0b03851500900c410002030600074200f202c080c12410034007101103503d40e000d800c2032080c103f4a0020300f02a81e02c981c0a03040c640d280d40004e442941050080ca400403d180c10b1000c100c401070070f0442c008241d454a19034030700c0002c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 398057832 1250 398056582 398056591
    0x5060c16151b0c0b070b06030607020318040504020f151b070e06010c02010918020414060c0706230d0506040b15091e03060403030c110f0607050f0903070305160603090803040209 78
    0x1940f8801c4041140700c00c040181c901030f4000c0d205592145007100a040c60120081c040c0b80c15944103202c3c002d240c012031211102094010f807000700c0c0301d450700d02c040340c0820b40c448401c40d4804515604009a403c4603000b9200605e141546c4054800a08641c00d448910070700034003820004103c00a541c5500904819503210301c18500400301c155107000d0f07903c031010000040081245c001401300404140c1a03070500c015a030444d0300342d1800c1403082c4030310790743c91b400e01c030700e80910400388408041e82050f025415050b100c00307400290f88a01004400008040444016100b40c0c82d0600c0d40c03102d820214003144000a00c1341303071a85071407480005c02100140c030790800111301000580000b5030742c4040c800d0a00840c070070f03100491a043e800b1030180040503401c14160055000d00c1801410f4407001660a4200380f1906215545d812040710441d0180701d07001c102d540500c19400c00000300b0000168015070040108070202c400703034070340400f1003e803148198050220002480070030b01600d0f004803040c4c0c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 398059082 1250 398057832 398057843
    0x905061b0307020d05010b010909020c060103020f130e0601170105040c090b06090d0b01031e050706050a20070618060816020a0b0103150609050f0a0b010905060c16151b 74
    0x2d120b055030004404840c0d480044586944900305011607507005161100540001041581400000c80c2c505d07036550414031010380f24112030721120140b41c03103007010050540c2e82414107120000e61040065901c500a1290030381d18403042c0300d5505041c0040c400d050140d680320543e24103180c506042040035000b45078240f40d005808100e0340403290340d00440083e0161141c5038a458540c503500301624142c5044403c56500746012a56100050000c03d42c20306a82850900c2d51311100c540c5001c03140350003081c80c890b03000041c00c9543d03c80c4c0d2100140440c2161010380d5819003080040b040070b11001817901c02e50001c00c0c40b07200460803034040561184000c01080c4100d484600b495102c0480b21603080e07000341c1d160081c140c1c1001c251026400f07418094044a0b80c10300c038900b003490801040d81d50082c2600e44031940e8440ba181c007a80320344940740052000030209901c030b03820302c01d0702070312481d4000c0c401d8081c6100040005050303050f4200002d80242940700c15002104400301d24070281e41086c0101d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 398060332 1250 398059082 398059087
    0x130507050d2006090109180f090b04050c190e0c0c060123010203040303090501030e1f020904060906120201050d020f040303090501080708010315020c1e011b0905061b03 74
    0x202a2140800c0c803000034096a034000d000d10744906110860280440e500d8042c0c10704102e130302890f0760000040d4048800c030184104aa440c0590984010800c1603c034640c51824290301e0000c2c800741404041c041e50107074041d100c18040b10410070904503041051581c1040f0003840070008001c4403401c0950100d01010020310782124414480d0034200240c000a010742c4030742142c000081740d0b560a0485603c401e000443c03800341140ca010300b600c0c0c4e040c482c45040648a5240040254088c410f8605008101002d135006080700c0c80c149010350000700009026500d4601c1c0042d007502103000d1501158880303040411122000e800440d09580304615904001d5020490050140c85070802000210b000380d03102c14805041c00001014403201400810410031403500600104500c504408605002d0000050307840402c00710700c40c1890403000d4828000740e6106d200030b211443c103400200201d1040c854010300c02c511346000b40c52038400c502a6a802140600241305600405401704c4249480c407c00c0300e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 398061582 1250 398060332 398060339
    0x8043503060316030231090302060711070305060c0706090b04030f0e15031b041d010504050903030f07030e010605040609020409050705030c091309020904052109030a0809040908040f03051b0306130507 88
    0x400c7e00c081010881c01607000804010241d81d000c1c4010251402c884080e0000c90300c0e50312016030b00d240140c5103e83c260b000003102c504024041c4d012186e51580100721074900e1505040140640407000400f4011071940d000e5099646440480c03201c915001580450a68840000c00340621550008500d0f00081c20400414600b10084a5054516040d030cc140810b6040c0000c0c4410f075a4040e1250905a00610500c070b0320f41540610140d200c0d00c1840d0010310441c45600b070f1809040e0780c0d440550058688540405d0103042030b00140300346c88900c0801e1005480e090011152803000b00c468262006c41408215401d103400f2000038410005030402240c4d88170140c001400585040c2c030111090b600007481c0e108a00940300f02011010301c40c400d900d0030110700c2c4020035154013009c4002409000005040744296881c2d602000c200782d00314440544035600c5040c007003200887c50000740c9061203500b491006444111564050301d00c40a400340510792200340000b2181c11103064102c400340500307403000c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 398062832 1250 398061582 398061679
    0x30f2104080a0b010918110906031c0201090210020c0a030b090115061d121207080c12071a0c040909030e03010507260403080435030603160302 63
    0xa031140c0303014642c0030343c0039450060741d10300f02c59441c420f040c04104202c02c2c030300c003142c85c8130a17001034030300d00342d6070b988980d81c0c0c1c1c8000070f0800b0f00031071000200540b01030784c80c1c0d031040d1305500400c4828400c0c1c41c100c450105d100740c03c2c0c0c3c0d0340b150340d500240e010b14128000d00000f50105002a04000550004140008043c040b0005046150025400204100760700880c01c4142c2214800050040da0118007140407240d003507031110040e1641468200d000600301c8200425503086540e5180d5840542e01034460201130801d07a40c3c0228000d507001c50410660500c00500440030341d010f810520115450280f0741502c903005030507151010340521540c4600d40d900740c0c40a00805104024640d13820386180d4040c10046071448200740c2008032003803000c040000203500540c1c03442c0c210741c101d5030341d00e00d80200c070300032aa40c1010816032a216070207000c1c040b000d0611700d20195004000c00c80580b003102c1c1154446108640c8079200c0654440c83c42d03100c03d5035038900c40d6807880c000e40c90000900340300c00b1a000e06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 398064082 1250 398062832 398062843
    0xa0207151710050102030414060702030a050d2703110d0f0606090c05031608091908030f010b07020f010f05070c1203080f040f03081302040e0105010f05030f210408 72
    0x2180814500120402280d0007007032036951001501280c0b1040504001c0001c0d5031380154000c2c00031900107e41e488040e56a81800c0d5050290f00400700c3d01c403880741c0d250042e2500094404c420210381c1100c084500c07514116240705c4102c00428008105078596241d4070704c0c00c2e40402150390807949541030380020907114290150311501401c0080341c02c5281a20300011544150b0007001000424018408242500c90001e082c0e001c040c64220860340750f0305102800c00410159142d91001c1e001140c0082140d6030015520400300e48a40c011503a03030303880d021500b52090001c002e51005e2011a1902e80c1e41c09002d00e000209070074500780b0700703180441d03840c1c3c200c0003c2e6411903d07101003212040420141e02c140c0d0036901c50200360464000f4181660380c00d82030040500000e0a124442000a038502d0140300d445008640050040c801c603059102c0c1a070080c1801e000d0102e1045540380089200e040000e07141a01040c41e10007002000b0340c2c0c1c410950454020822040010390070400000c2107481000f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 398065332 1250 398064082 398064119
    0x607170d0b0a0f05011b0206090d0b15100807030906060816080d0e01170705070206030c030601090b040501050f22180513200315090d1202120c0a0207 66
    0xa94a40c04008009141d92903070f01411100c0c0050005002599102c09192281c0e0701d160681e0500b60103d1002030554010780c0791880c0c001f0a0042c1700001c0c040c4454056008000c400080da500031505014009804401c444003030100d80d8800c0031807042da22a5005000c0103008100c009505600c0341c00369401c0040d81c02c0485104660408140304020b018080d0f80424401410405048070802c000681590030315049040c007a9075800c00104064020000c844a095004109640d80d1034100c59800b07041e001592018009013514602050880004049500341c4030140c4406080c0340320302811128036804080540440a0044102c900c07c0034131040c10f6000e0b083c00c5040c031074a80c156030301400c100d4070010400d058140d136911048003c9088614075240c800d088886065181078040e012038030346441c800c1409001001c20080214a010105011071603841e142e60304e00c07070903401072580400e034000c440550710710b00400008103195200301d60003042c0c400b11500554032020364a240b94000e2842c07880 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 398066582 1250 398065332 398065357
    0xa0903060e0717010c0206010303050a2615090108100e07030b090708100c0c06020306010c14061512070501030e07030503070308061003090b0408030604060b070602040512030403050c060717 83
    0x40040c804643c4504030100c01020500c0200440c480d0040000d56404040c440507082c000c0029a482802e03118440560408840c05500003004c40c041e58500010b4000702e91507901440c05103420b000a2030003856150496007180010700480341d13112220402001c52061510f168031841000100040c6135960070707449080100046c000c441c0c03400c0c034020708000b0003203c84601245000200b285158003c01d0540881d500484010b85070b54031000140c0e209031203490041d00900c201d1580c0000210005691403192500b0700b000c21540071294140300740004030802030002c9402290042c0081c1d44079a0110400410501c1201e507001e40d60f440c0d0a0a552042105800040400040020340d05000c5d6110524031494030303041001d8522515000d06203040600024881c010000c0442c9580c0d4072a00607801030b1110a5080b940c40c4524030b0314200940c490321a042c09084007015401035082c0201c15501101c1d00480600140d034829020011281c0c41041c040741c4007660074603500644150000070704034002101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 398067832 1250 398066582 398066593
    0xc05121b030c2101060509040f03030c03020f2205012a1e110108010b0c060403121e02040305010f180602030403050f07060b0306010b0a1b060b0904080721050403080a0903060e 77
    0xd0303c0306800d44003075400990241c2518400d00000803921280b41c0041d94143c030300040c642500c8413040b4040e01c40c101d0b402c030013a0700201c2d00065040c9011118002d545104244607106640d4400565503600e1032002c03460964461004000502c8850410b020b01902c500d00850454210f0742b034020b00006112415a01d004080c14000d0155030007149043c0074241c4514181c1c200b0710780c1643c2a40d56003000340014104a40c00604d80300300c1000360491101d001000c68454480001090480000e411612054402d50708080d0300d111800ca943c4500040c0300c0701c0b03000c0c9043d00c0302c840d11144c001e5031024108034100304080109501150029000e010702038401c402c0403407605650701c109403801006130003a07101091b003080480d001030381080c50303100c0100d40c5d0840f440400c08507081810003880e84a2110703821024010801040240810091210302d04c103030301d0390042c409c00504c96035003004000c0c111030200d9401c000a2010510920280030311200d50718107450310701d881c1e54959050780d400c0c1c0c24001259200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 398069082 1250 398067832 398067889
    0x81602040606080a1a090402060a02010b030d030905011103070c08130302061b250501030e03090301061d09070302031203130f05031e0304021c0212010c0207030c05121b030c 76
    0xc40c0204124810038040c000c1050a145c0001414040042c0000707204042c0050410b0307096000b904400044c51005003641d25507a8503601c091701406083e00101ca00354a007404854202036a81c041d80d0260780c0f559501d1203100082da03180d03032560744402030b4520041440b410001c0141d032200014516010035465000321201d96491252903c410402074500010421031900101d15400020742c00301c031400d19000c5180441007000c18258407512900f0394055092000100f100d10b80003040458491001c0002c0c02c8542d5280d1800d51100c483d400000d5040d0004104203940c0345a40c000755030001e103600c18004840005030b84030401c01e002d441044803950800300b03445200c040e25540804600c0d04040703030985146003da0020f58001c0c0310b810082454148150400250745801075548140340340c000003040038034034a04021759165080c2c4003c40700c0c03070810700c00401c103428034150550303440d0540c0c40140b401000c5081c07625401305c0b1002d00250140b1580712448901c3e903606d05410004016400d0307407643c6149 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 398070332 1250 398069082 398069101
    0xb01021f0e1c02010f050609190b0a080a080901021204080a0b15120a03020606040212040206030406020f04030f1b03050c0f03030c100203060a09060e0c090f1e1008010b0708160204060608 82
    0x6004050320302c08e06030182000880c0f0300c1901c1650411408200018104600700001815020290000c04284c45094030001c10081c44800403c07080400340c0132614034100d0900f0300b500510071801038013031680001d800300002070541c1c002c25810814401c4d032044d2886008021030030172202c1800603002940b190360050140354050241c81c0d080401681c0941c41c2485c010310342804c281000d44004e00a00d4000009414011302e80d058500040080c0200c0b83da0315583e00744900c444a010f281641c8404804007012a103210340501031044a03401400707000200541c00412028089403003145400d80400c101458004409000e0203200300f80304e1100507241d0800c0003d102811b203281d0020f1700710700d2070f01308c0611204481a4800313500c00343e05050203075641c03181700200da282e04240c15044c1e00240ca800001c103511441d0407a01003011800d903004454001c07443e400301c85c5004d00384940c2000640400043e0b012400c400c00a00340003580c44031152460f111075020500300d580b0342d440740d0005480b04060043d00d0341d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 398071582 1250 398070332 398070341
    0x309080c0303180606061b01320901091208090705131a040b0d0f08190c0203100c0e10032003010513020a02030a030e2b030b01021f0e1c02010f 63
    0x743d0708001d01661500030040b500300d02c140c1408035000c005544411004640c25046000994400600c1c0368182c0d02c454100039400019a503991000ca0011000811142d014402c9400c0141c01c0740e10304041c0c0384441001d4032280307400380c6440e016008680c40818a0f448000b01c03e8102d5910000c00038400309081c0703030030409000c51166944074609008400c10195034056200741d10395045500c03120007041500d401e0703a651040c10b8510b0700004004290900c5550070208440c2c10034000d406680b07444006080c154119905205094041000d16102006904040e4090428940181400180c0308040140c501610086901044800d1070002c01800a400d015102d8503802c01c00000a6080000e216406522030161100f40020566614089101d801040088880602040001c080201c9038000030003101d852102e88000801c0c10050080c2c0720b54400103014400440c2a00c012a5480ca420b0702e03400034240036600c41c01c907442100c00100300d01c000c3c0600124441e400d500009880b40c0303031100c40310a40c3e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 398072832 1250 398071582 398071621
    0x110624010e0607032106090b130b03120c15150a0503030f040509070504090903021e030a05030a020d020c0f061b0301050d23100902120606030a030c02010309080c0303 73
    0x11440802901d050388521081d150041c2d894140003003000494500500600e0380640c240c00c0d11410030100007003140140d840000c1d0808266540c882c45842003006409596041c0702051b01907000b0036220380700a80b540b010300903010808080c2d50f40c03600007200c000c08800c015203080034035491301e2080c45901d15060000600a003000d4010b58289040c0340d0401506026500c18a4003c8c4204000a95030510030000c0710040d29034494100054455400c0007917941c2000f0101648100240214043c06035002040c0c0382e1440390b0382d68051440d61007454070340294103c84080e80c007454091150700c00300401072001a08001200c0020701036031038811480700100f5a003c12040020a080006200503200c60781400882c0342c0085584460040c40382a8400e840300048018040b400b4003c1e21a44100180d042541e407540204e5000095144d4031480391f0301e070881559070b07662640c00075095800080c01384501500c3c4900505000401030301c652905041c50f4040e0076201e0240d003000040cc240f140480034112880c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 398074082 1250 398072832 398072837
    0x21c020f04060314070e1e1b0a0807230a121b08091204230316060f021002090a120804121104201b0f0109030507140105150d0311062401 60
    0x40c244441047e104d4024070401c102443c01c10000034210703209038062078607072244480c2c141c0d40d40c40c202c1c10010407618090301c40c54000b80100302c00c8561800102c1c0c2091400040d850802c0c54100c151500359003070b8091204000000d0f4071070342c549209200b802c0101c0c0c0c20b0b0883c2d45850700070349030003046181803860740d0441004243d0207100601450b80854441d207024040c043e100070500d14a08002403400e030503001041d00304002d440e8003080d000d9000e0585260086c05400305c50b01103091100c602c060b8041c841ea029084101c086003004030700841220101103500032140c0c2c0d45031680721042c5002c81e40c84144141e41140700401c560002d03080c14400c010b080d0a000c0c09088841a0111309280c0350710810740d5032007182d00c00c5010844000400d009500c94200c00c0002042074030b2013031070b0290880e0000c0d0815110b03d021281b2540c264a01801458443c407451400c03000d80c20f141c4002c0208030720480030b0a07010004c0c10184182240d01c100111401340c01414411000140903106034050440002c103401d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 398075332 1250 398074082 398074109
    0x6010510050f03070e0d0c170c031c0c0807060e16081b0909010f050112260a051b030307030b0f03010209060702040b040b0d1506060c021c020f0406031407 68
    0x282c480719030301900d0700010035140c494a0001c0420025400030110f2001034529100c128000a100d245803003004030b0784644c2429110a01410420076494018100c04039403000c0c80c174413000e02c00d64892190408076038818404c3c02d05008080d140c0504456191700f1004055001d0b42903401c20101200040c402041e0460042001000003070b0000701c03031815211094010890400400d407541c0082d04406c80150580320100a150b0f980d141400740111882c00650303009841120700b6500c1188000a03018150336111814601030010b5811036580d03110044004443c2c5000c460801081d0f0188020342c010360f116500850100030701d01c00c000301400c508500c18402c0e0b1040044c4a141d4413240140c1c0c03400ea804940020300e140c0000003040c00780250809040c4d00010314018202003060040740751340300346141036040001d10346076102540e2103030203c88003a50260726101d1221101032110f86445200e4405000751203504001d50100d410303225550011100344a1041c14440c2080c0100000001041d80c01c070b1805 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 398076582 1250 398075332 398075347
    0xc090b22170c090c0d09060f0b0a0e0708060301020409050901020c100c0903030c02030705040e1513021507140105090309030114070516030e090c030f15130f0603140601051005 77
    0x1a5146424912035004840c0d030f070001800e400c60801520320729429000248011001460140e0086c0030000e200100f007440c005c3d55000d907040154040c0c064944c030442d400c003030380c5681c0d10a8902d000010a80d540c150b40800000c950300d000c42c01075234058444440050f0f12103003d000d001d070901c000c084000042c6c507e081e140c94580c503442404001141d0301402d00c4030070f0560b2400441e040c02c0194010a800c01e08208200b41440300c00103412002c1c80c1002c2c03011400d81c8401c4415900c100725108081e41c808401191094903580a03001404418410350110004000c3d0b09426420f48808442d00d000d2a00049505a4039040c00c3c0a1580000140640c412240c40c01140181c002d0007408890030041c90030302082e10405000d6040c1905000c070040591129142020505005900403600003d60f46c00400110780c0c0c81c0c00c10481460b481d00028441e0070520003202070403006004454400c41c15641340c0030700001050050b0b0038101c6450129019184541c146428408070001c0d0048c0c5100b005000c00882 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 398077832 1250 398076582 398076629
    0x1c120507020c130228080115020a060b030a02181b040f060309030212040b0702040c02031e0a2601061701081221130302010606170103060c090b22 64
    0x15101c903800b1038070350240074030303000700c04000380911044000c02070468514501c002003200005c24413542c155507080300703076078840421011203219140260302580c803548502c000070b40d4a410204504c1c42c06030854480740c1c5550001341e0800c02034440101e0400c130b110f041c0440307143d102c4610070908a0141c41140b8041c82d160055113080003e01c85d071010903903500d260008040c820300c82c0901c590010303400079032201e4880c10800c01a40c4511000c03445189001d07000c4aa090010090b55000003002420003045524800d011000354880000c600c00c01002d910907a881d0042c1030018103108a84810707590144d81070040160001520f800381c68545419040100070301c160003e003001481c0d490f4045241c4802d540e40c580040202e05200d01c00c00400c000040003046004410182c43e068003d80c000e00c0450b90321130065038180640314038004003218400061003c900160050082031460f454100c08243e40d400f9080f919411a0210800f1380600c209a802c1541801c035082019100c11a6145108482030044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 398079082 1250 398077832 398077843
    0x12071707020c030a0b040f15020307030605100518040b0a0e090615030a06110f1903050601030b060414060d0509150105030d0906030f0b03030a0e130b0d03110109051c12050702 77
    0xc10030b6170700000103402c018440c1c0f241188180d006031409056a001d05c02e94002e9082140c0c904002450718000250503d0446901211310510f41c6039249084d28a035840c1510149000700107800540304c001c11080e070380307401d10380800030b0800c00c0d5445c1c2c0e1800c001004900b00800917041274094a003802642100390340c081005011603900940010b070201c000303130714000e89000303164000a40380000314076210090000f15002c1e080400540d004c00555648500540c11245680d15542c0c124005100c18040000600000d000107100140300c3c5080040c1e907102074040e02e00480d204c4016411103c040407102d082c0c04100b030301629044014040380f1000080007011070710030b4810402050340745e612001c1020499407290440384d2010f004d42c0d079507000041c00034020703011500ca074078000c0b0402e0112618005443c8102030006100a000e0300e401840c94034121003190b036660016200d5540d5480e40800214208101801e0b0400c550740700b00e004422190190941d0000e203885da40c41030600040091455000c40d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 398080332 1250 398079082 398079103
    0x140109020c06012c040b04051c12020a0306090c090515120c2104060608070b030c04030b28091203020c0604170f0301030804210b0109050c12071707020c03 68
    0xc410340c1d00d0006415020501136074040b805580602c000500040c003c041508512540c092812258500203407421036848840c1210308000150000d91080001050381e001001c0544461601040300c588a0f0003400864540780d50365004902804820411030801c001e01484000d801c402007400c0210042c5a40c1c040e10004140c10300030381000984604103260700c4035501e088144148000710501d020f2030000000c24460083e4101803290150000c1c1c1c25000404480c403038400030343e4040c1094130319940c050310888040e005440c26a10000505404221020611183c041220000c038075803030390781000300041c999018801e04040c0100500384a10b070002414a0700603612005041d2101c4112001071401d00031000740d1a82880000000018022000082c0041d40e403d00a2000001085202c40f1041502078600404a06288004100008040e0720017544081c0c00084980b6000080644044087c2d04071201004908040705641c88202d03405140d43c3c1c800c1c403900007892082c00c5100020b944400015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 398081582 1250 398080332 398080349
    0x212060f0a0f09060212090606040605030c060c010b060a05090f0d1e1511030901050c040609060302090f060a0203071104110409020f13030c0e0a0203011a070203070e0a140109020c0601 81
    0x407007550b20761841d0b9106426003500300c2c508648840301c0c081000740300b090640e4124614411003000c55a41d18003071180b08112040103004104c5d407004401030090320f420480c180c5849542e1380500309060b4403a203002f0a07202005075a200e40d107184070b500f041580d038841072880c3c1c01805031011150008040500001391482c80d6004010b400041c0d03c0c010428107203200418410130304201408000605000146004866450091110740e403a83e0071000140281d109003400030b012141d003085064001d03401400e01100c0608920059090b0304041222580b01d29820340050307000051050a02140c95521401000c080740c0a10105440c5103010003e40224000e03202002e41c0002c00d100c0904c10b9104a03421502d070300c4241522540e072410310110700c80c0303607124031001311154200060603205103201b00e0381600c07240c4400d0340c0d40036400c003041040d40d00080802c0f60035104601001c104405140c459a210381c481000114001e400c0c11900d0640c1801a400300c00304074010b001e814016000891110305440c0801d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 398082832 1250 398081582 398081591
    0xc04030c1a04260102040b0c01050c19050c010b0a0e0121030f050f0715060e011d0f070c1a010816150f090e0411041109240c06130212060f0a 62
    0xb2103a05180300d41c2103443c0e41c0b0008000400100c944003402c070700500b60008002c0c0c0c0c1d803885d014201d030344034038020300c51400d4034040128103c038000c401801d03640600c50000a02d040c000301c003041c55000642c1207980403002e40700040110444040c0060034401201142d10312a0250307503005400e9210709511301c000c1c4480807a22106543c218000e42d89100e421055030048025028160002001140520003403c8050340c000b040c82052004401c043c4100c503490342030705541703034401817010740c401a0103171042055005103040030542101c6844800c0075140e00c4c25a1341e526081e440761803d10120b26051a00414071001c1111700e03184600c40d80e121a460500900c5608c1804086500c828240c00140034210008140700034420780c40b030000d07890007040ea001c002125a1070078944e50390044400f46a84071550180c825440c2590350a4146080e248000310f5041c01070200c00c141c184441200d14911003d07031404804103626103280c0060317042600c04045c0103681020804c0e0110000001e000302d030721f207469 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 398084082 1250 398082832 398082869
    0x31c1814030919062c090a060b0703030b0f0d0b0f0901020c07080102040513050c0a0f020f0f0f07090e070605090d0b0c03040b060307051c0204140c04030c1a04 70
    0x340101d6920b0b180c0100401d158a0038011100e040d400140940303000166429136030101c40082c0f01303254615a41c2c00300044000500c0390f040194188000f03104000c01600c036400003c0070488030001e09400c41c4039407000300e1b003060544140901440d03400807040c401d81a40c1c04060100340f88014680c0c0000c43d41c0714000e0143e440202c0703035000e4031a6500d004007a05ca03032440052210810760151041d00e00c2258080408920540c0d0700b400d85505640c1034103500c03802c20241701494000c000a004161190056601c05007a14008600b001c4103001c078940550020200100200c0041c0143d00241092030700c10400e4401503041541da40c0c1085c0038110900c00700150700e451030350b10842940f011a902c08407031b00041c45c020580c00001c0d04140d0b030031900c104501021a00c24540440d0349410f031400030704505209215000c11184900740c1007070603a009641d8110400d401d02080401034810001111080e594500d189801881c40c40b07954011155040008040d40b144c034250b400721021a03004080601422a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 398085332 1250 398084082 398084123
    0xe031b0d0b1302030a0c090501060206071202130b03011811131703040503010614040515150f0d090303061707050d0b072106050f030102130e0c0c0708031c18 69
    0x1030002d003e5031503c5840350600400c04042c0e010001e45500c04e2040c04942d985031010303651002c041e07401e100800d900c43d41854003a1404c0e40035000a174070b100011050036580d052001095802a0464400c022005d09400d0791140030780078a107440d81d240340e2030724604100325002c81200385580c01845804940e448076640c1d952001c20644000e01030050081120315035a240782e600c601020384860b8007590802002841c103071440c08400030f514101410b40071402e03e02036140340c0c0039804010512081d4009014104004400f8420020910300c2a01c00181c034505106420802c100c2a40c400d804c1a400000c1c10301103900c8000100b0680340d409044919541c5035030b28159488100100b80b0014003000540d4808240711941040046a1043d140c070007581240344241420703403107151003480c07a00041003070400290250303c008640c0702e100400c500f03061507608001241420800c0d40904a03651010411134100c0c1040c0e03140140c4208a00c0d001c200456103000010800000c10001070018450201c14a15210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 398086582 1250 398085332 398085361
    0x207030f0b071e030b1503060a0e0a06080f0304030c0b161101030905060405011a010203040602280503030906010603110406080f0405100c0c060c03020c07032406060e031b0d0b 77
    0x2018403000000d140310414010010aa11205c242c03107102005203114003449200101c1c1c0c000d15014040ca01510b007040500002050094407040907107a03500030000303d0f100180a070000c502c9110000c3c0d50b60f24610f050400d034120b210307040800c5811082200c01e6455282d056000c035800d9021040840d504246001603000b0141600c02922501800040104000c010f500450402507990000072003010780c0001240d99005901544000d43c1c40440105000c14071000c07164641003614618400a00386035583c03904540041c0c0c0c2d0032509501220050040c1d68041c05456150800d0100090030249494001050030038050201000294a6008170b804e1040a02410155a20f104c2c000d000005c1c1c0c00600400d1001e0004060f901145440112213040c2d100c0d008944036507030035000900000341192074408486140114007c10690600180c9040c0700d0a402504003d107190f03202c46503040b045000b89820008400c058600a40103031101d1342007959008140d040740c1e604001e1280169541081c40320b1038a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 398087832 1250 398086582 398086607
    0x14062e05040f02190201050c07020d0f0804060f14070c330504210c05090a140a020315010c0b1801060e0c03060a06030903020a0b07121d07060207030f0b07 68
    0x5040c11210581c00c041e0f030b00148090381d401c640300d6021345032221040703080311415507107170044081c1003040d100545486c403001182d050040607900750000341036076440d1507540194401e030082800c034404010f90a03005240007030300d40c124900c0303145020760a65036541c1040703942c01000007480e010341c8075100c0002d103001a02a482c0600511010080c02104050040e41042c411071510642d503210700f820f03a05c014aa408205680450342c0020942400304108100c500200700320140d5641d480b460b88010309503510f241c014082264010703902d05100e52080c1885c520100b0381c9052200c039070403140006410b2803102d640500341040c1d18000c03800320032400d4003505c1180d01001c413020310714044c01030807034807400214000e03030702203ca082940da6036110990544044072800340c05038000e56003001c0810103080899074400401e1810003003410b06010800e046840c14000c41d0a2007007610010304800c4010400080030b01074500041140900c2d50b514480308040c05040245a44014000701da0090700590b10002c41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 398089082 1250 398087832 398087839
    0x5061602031b0c270117120a030614090f160c0c0f170f0a060b010e04051003030207061106060d080705060a0e06010e0606220506040b040314062e05 65
    0x42c0c160300310341541c0c0ea252101e01c14814400ca01c8007248030b09054007480d0003102409509411a840e00c40f02503440281e00c03900c0f04040c003e0480c202c0c041d0b500701000305042d09480d14002101410b00701c02c100225413007500140550700c0c00060000c5068001200c0380d000d000d9000e81003200b0b10703e5200301d6490900d800300521030141e0500200301904401105002d903204421500602e850791041240e8400f43c0302140131542d0440414a0081620354001001c03015041c10003000440c0514007082c12940d00300e940080010780f00506104141c2e0510681c4014800c82c9024100411024900e03030b25090040c220a121300c0d225103105c410030100d0010b654070150442c058a11901d008458200540700b0100824100c0c01210b001080715800fa03a800da00801000c0c100e03a0508101c03e0404681100c091107200020541d0710000680d552240b0080000d0302954100d21344440c41d52501d4861401c6146452100743c05c0002000400c00404001c858041030141003c1c120342c42041c19448040310700d0300507540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 398090332 1250 398089082 398089117
    0xd030e150d050c0906120705070804060509181501050706061707060e04050417090a08030301140103050610050f07030504091506080601031406040b0a05040203041b0609030506160203 80
    0x25100030540203000d61401466091080b981d0b600c0404400d8492041025444002032012042c91512130000369844019420010f140404c0d5480e031002c030350031690043d00021000120b07800703c2d00b8408045c540a240e0000d4468030340c02c0c0000d0000c2c00c101a0103940d4100607010a000d02407216030303080340c00144040006c2c40c040e448000b2103a5103030b41050054101048900d284005e10342030521500e0320480c5c1014210f84200007890050000b0340c40000f1260703014600c0c000100b41f07440103100070740c0248812070300240d548040d0720014098440060507507210703101e58620544a030b500101112482e80940320031680da002c03d440c0603544c50145401c480480c1d0310301740401c00c18200425034036040da4a19100c940255446c44011400e13120050106d12404200e50b0201d00c6c80e0030650441540b5000c0104680d940a884e240414226001220240c40c00410400116240c06c070080d0030700d01a140a203440030b1071034155155699a00d002400c9040d084100201e188150351003401550058031441e0701a02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 398091582 1250 398090332 398090359
    0x4020406020a171c0e0c03070906180501080c062a0a0303050a0c0e0126100f120506040b1506030a05010e010f0602070302040e03070b040501050f07050306010e0d030e 73
    0xa5a5605490b82250014003843c0161162401141512489000c0b12503c4401e8a048200380703000e040c0d490b01d00d60a03442204403100991b5424010140900421600001c2440c9000503c0741000c1e0841c0c03036000540d1500c0014040c0c0700020904d145a00c030b00b5140f0743d941d400a0b110500c02952155020101f220845140891144001c00c0d40a83c3c94040d03901030045031a020514002c548c0303100380f2417000ca103094001d09020350142c02040400d1216050340c1d1540030790700c11407a50b03c2504403020459580d08507002d002c44a01460840085c1480d50042080c880095540c03d6071a0406840035200c58400000030b104030707440c01c0c180c403400c207000741c07410340c0320b0404003041c01c06031800b03002c3d800d08094a60004140704800000110413540a580280b905a01e545c0034400141030b50041134407203000c10001074003c03c400000b10340c06188030f10000200c80c6001d110319400c030f8201414903010003804005102c00b40ea842400c04960a10858515505440500c2c003a2803140182c0c01403a0004401162803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 398092832 1250 398091582 398091587
    0x60b0117040f11010e090601080a1b020705040f020307020d03150f080a021e06121024030b010c08070b0601120e250305061b2a102a03090204020406 65
    0x3000161103000f8940d21507000600644001001c0b18050750020020000074101d9842034005075048010804001805c4102145420b001d82c1038070b00c9440546d101c42002c0059040910513182c1c28845000f046056050404000391120043c8540c84101a201c0d8465917411b820455010001c2c02032660000d10745690b00c048603159040360400b81c0c410240300602c0c0c18082150011500d01d200000c10561a111207054008000d05014000038441c440040010607207104419004404c0c100c0003503503506078a1031110003416150307032030350603410452241040c1001130403d40c03c0c0e54075254014030030041c643c0c236174004940104440c429108000c0c280a040191440045011038160907205000941e80403903240101c40c40c0d80e40c1c84010f099510101c000f5140c030307552110308140c011808100710b00c6c0c080b4040101100000c00c6454802e00050340400e5040e618003002062100d45c82c4030014040411848a80440c029410119051900444940c484414426444003038515801001151601d03241d0100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 398094082 1250 398092832 398092853
    0x230041203030623130e0d05070606080a1b060e0303030103022e050301090c0801141903080f03010609060806031c050906030f1e0c19090803030a0f0605040903020604060b011704 78
    0x5000d5542421005c0007840f107401170509103030000d0010500610090380865480e40410300582e40540d68420214000d4800c2c440e181d01c440c040c1c030500349500305218180b0201841c6038010070602413000040c02c0b8944000c401c0e42e04594040301c14000d0b0400e02c1014898003100490070301c1c00d0b4500d154000b801d0581100c0614142e5403102c1d001c04c2840000e01042e50040020b01075084548510002514240b9000344c03201080d501c0004000540c43d03136540e0303491041e000a004092255408001404440d61100094001f02400c1c9080481c034200003001c261561a410079041d14002215a10085980039000300c03401d5800260109960b8902201d103002d20388019565441e02820340035a108480b0703203503403065004200303400c005480c24209058602d406042d50784030100384511a1030000d00000c2c02c0c8043c0d0310075150103a0108200324115400c90884e00c19401841c440e40c5000700207030200760700044250744a980701e0340011704c0e0103844005131501c0f040040813500ba0304400040200308003a4108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 398095332 1250 398094082 398094149
    0x1f0e0303190e0106030b040204091407120b0703180b09160b0408100606051c06090504080d0605030d120b03030c010c020f0610050f010309030c020402040602300412030306 75
    0x1400c01158048929103404d941841c4005005403681001240251525501c509881c0b8801c0c4040d000b45100954050304044680d80100e45030090154242c1c240003005610b140d11141030301d0f0030002110a004500288104014017078080068440001c3e0f85001c104019a80441524080c000c0302d83d5544200d00603901a0280d258107020f07941e02000c0d000104c0c002c2c9030948849444030760800c541e0b2041041c1115000419059140d1203000010307008042d40b140a0117580a810129550301400418901341c40c80342c2c1c0041d010b54000b414001005900a2507154400c40c08100851a1001c0b03900191860107080704061031540f030300840a0341c05400040400c46030580400340d80c0199200390500109454611400380c024002a2100401d0362096000f0601103210b4103000000e201641c0200d000c81c0c01c04d42000c00941d2014400c1109821185203242c054904001c405500703c03942c101c82c95080c000c80c4150b04030980c8171440da40070540203400460140034040700858003101410b040340d01080c420301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 398096582 1250 398095332 398095381
    0x12090b0a0804080d1433220f0f090b1302060a0e010e0310140708010f030b0903070b040b24060d090812190c050c070513150b070308060306091f0e0303 66
    0x1143e8200500c070b943e1b0754004004020301004200c06801e941c02c101c000003100341d010341d0782c1e138003510030340400c2d907120f400003d26500b040014960843c0c60281c00400c0040c00320700072040c2a068084c0161b4405080700e480ba20186001c501c00100381b00140c940304441c14200e5498041c0364003503500d0303640685c4060350b10030340503c0600c0c864640c1482651884828003410f103451f120190148080754001031400c3d0010580411603140031510384031601c2d00b900986085568040c503030284000080350b1040c03840c800c161220907154034141070002a0192081c041041030541e26440c802042c08420070903038406007031854090541f450b010900d1402e180c1d9507804912202e15101a8001c0a84a1410f6a045032040b9000303000541c185001c05c08103200c8111501c1181c0d45901c1161050403c1c2011800101000b80d03605884c2d018038030340504403031401403540e4081da01250410628005c001070000d6401003450703001309084c005105d040e01401c1d504ca0340030b030b02d88000810f03c2000300c054032480c00300000b0389 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 398097832 1250 398096582 398096641
    0x18150603020d060506270a0f060c1502180411120412023310030b270312060301060b070c0605070314031e0c0c0d050f0c010912090b0a0804080d14 64
    0x202d08010004440d4023070700c5010070346180103201141c0205400312030785000b0307020b561423200c0030341e45042a80d00000d044607500040801e108090701f050b003d41c90000c03102000706414084141010000d60000a0000d059039900d02e036441e004a009010114510300100045d54065201000d102c0b440b100080c0802c856611200003d05410072103440d030815a40d02c10498040345d00e801030380034a030002c1d41d9807462580350194134400703100c00d0400040c20214042c032140312907481c0040416084441076401079003414004c200000018100c49012020f407095801c00a40303030b5206043c01c5860b0340c05540504d803c000000b06118a0080310a101010f8407107020381c00042d66910241c0e000240249040024507522020105e01e4440c00b13000a8000c0d404c00700364450a0940100d181c5084d40d01c07d500985040e101d02c1c2481401a600c04500400381c07107072951f060f00e440600640280000001031000d071a9a1001c245150740581d640c1200380345044011150145040c800e80b07050359008498140102404103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 398099082 1250 398097832 398097907
    0xf061d0102070e060907031401061706091003120306030c03060209030c011d010e06190e090a0207080708091f02030307030c0c02031b22020418150603020d060506 71
    0x10500181d403c03091100c88541c580d8030038000441c0b0b01a1011044c95100c00d030310954041c001e22094000c200d90396030310802d145d140b0007445440d603000e401c66004072031440c2041442d00c0c1000068040f02c0e840450070100f1018090110010103980d00014004e803500a00001031203601e0b000342400e002c00320280c1e030700c038517500d001951000c000350240c0811407104800b1240c1c075030040c1c5219401e00009031a091908019940c107891020100c0c2002c0c01140030504003044a0500d04151a880030305a80d0451034a003c640351540c0e01e014a072070041c641040043d81003010703200e40c0881c0d1505c0710000f1016074684200396000e501c3c0c0c2c1044030080002403a1590425500c0d05c00c03a610031420350043e0142c60801c081f0241000801d01060031150403195400785125420103080c01c0e2290507180800c0140c40d01e0801c525000d441c407064500f05030150406601e26190600c1d04082c408030780007801c0c0141d54010b900e03400005400e0a900183e0f0140300896000032020102c030726501c4000c200a007141c9403c42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 398100332 1250 398099082 398099087
    0x408130504090b011404020909090d02060c1309150b07030305070e01030b0f090a020f0c010e060703020c030d050619030510060503030a0203040e040606050a060c0203010606080108030904150f061d01 87
    0x80c00c04041c000c510443c00400106404001d0300c00703122130240002d8a400801004112000c00649400d6286d40c00110609a8250f0600c0312941081c25000702c50720700341141c3c600890303400390350040b14141581d07074002102406206202200900d0416951511403480382070143c01040d00710740b0000031a0440e10420620b6101c0c0c0700c0c017206020000c154542d8601030f907052101c2164001c0021503101e60800c0241c00200c400001361030701e00d840b04008161802d006004904207080a007041041c03500600c00f080450b14044243c400321801c405002849598040005081940700210070340320304041c40010060000101e00f440b540b4055080900080782c0d2041819034034407503000803900581050100344000c0b20203140c00e54100d07010750340100e412515400011107500b016072104000c00d01610810342103003000c0c00f03540010403ca0030241e01540c58100065101e10415054510481d602d11400311a008618110000b03060150011820785885100c080c1c00100d090140c11148110041008055803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 398101582 1250 398100332 398100341
    0x3040302100506060d09020d0c0806100501050306090f062806140c060f10081c080a0e071401090902030c0309100207111c060c020c10090b0306010c0312050408130504 73
    0xa80139002c54500100d081d8643d005100040d0100d0b804944604000e010940204180f006040102c000e0081403e00c3d203c1400301c03103c0c03a1300080c1800410700c1003040390380d85d080c0318540c44066103100c418141d032074000040c1c040302c003040b201c0c15003c400002d0724480355100c0e02c0074080e21a152a900012040c0c40342d1791602e402000040c000036404030000441d00f003645640340ea04201d03030564000e2100e0704c400f001c80c1000390f40540b030012642500104034031603920264450304044215000c000c0c2200c0d5020150721030059004042503104005d61400719030744600ba0100c0100b5200404540fa410031448040072340c2d0040d21940c4403840313003a072901c200c50308034406c5170030070303503005290341d41101080041c028941c001900001492950329015404940c01d40281c0d001ea014541c040c00384820218100000d51101c61101c4c001c0050b074007010f01004413490112038020509007000803524550f403604807941541150703501c0344681404240300401c4041c0c40034085c5044141040d1407050703100d00c1030000300e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 398102832 1250 398101582 398101591
    0x81006020f1b0a150c02040501050108060d03050c1f0501030212030307050a0804020604050d0b04061b05040905090a020a080303040213020307020d030b0a0b0a09031101030b15250305030403021005 86
    0x240c2000c10820140002c10300380029641000d03024031941035035418410311401941c00b960380824281071002045190500c5401d014007000d090950203030605c84041042e81050400040a005001404500740c0400300031001c002c032840401000c03072043d00361140c80034000c2031100300d01603451180c290203006000300c01d82e40f08600560324503092010f101c1040700e012034094416600b1500c1080003240030b44494001116071406040b810145003032529080b4101c03002c048001081c1c881c90040700b00c029920104807000c0707481205001c00d20303882d003a160a0030101e880200a602001c01c01c00000c8110300440614455402148c04d00741c95104040004142d00c811241400160010911014604d010350300c0300210000c058040140030fa00d4a450020540c0008034034004501440c5040007006011512200318100030718007441030440140110307803aa20800c40030300c007003240855110748206130f00b03c500080d003d01064150841c046d07420007401c194070580c1d098006010390707007004580103124050f1501a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 398104082 1250 398102832 398102863
    0x506060a0309030c20090105010306120f080f1902100501140108040501140703150f050307030803090c03070b071101090b0307030f0617070815060114070812040308100602 75
    0x30803905800880080c0201c9000700d05000303000140c3d5000c6902c88004052a8500041120480385200108642502c2c160b222034100350034510300b070096040702c6a40e044032a5001a01c001d03d800c480c034000c8003d025444083e072000c44041074018840450117140c01c2080b0498007652401c14034606c0d0035050311001d00855070300300b1415080440c1944159801580240107200005642040041c06031034540207840900000362105101003880c0a494400e50040104610090103285031201081d02c4000500c400743c0303071030404400900002e400b4030407030341d0f0224000d058035407864440700074a0007500156000d803031110302c0c042c003103600394043c80d250303010344101e00310341d506664038050101d029020b001000d28001e42c46890014203090215001040c010905000d443c0c032a040008071441c100b096206509440010700a010050f40c0041c0728418401c1100441030752040d00d03050004442c401d640c20801640d8443c1d00300401e156011180d14002c08040a081c1086980c46804990354900c8001c00c4030f2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 398105332 1250 398104082 398104087
    0x304180e0604021003020d0510140406080d11030c03030703090b130f081312050309121204030f0f290a0b031b01090e0a1a042f041205031c050606 64
    0x90301d44030045404c0402d40385005458804c0300a074400c00e4a200741e8205940341c0340c110381440360038170010010f2142c02e000d840c100700a40c54141521b984580342002d00d418401d0304807911991200a02c221410002500c00310ba07581e040000340200286010b11041c0e94085840d00495801c0107040c0d1015070a40d0017030302540c03142170f460301d030b01d40d2661203008010300742840702e200029080200c100c1c9603030040c020b05c00366442d60103000500c110030411844070007454101d03000019844201505440649070400600310400629180411400102da4005000e00c2c1c200c9403000d95001005c0c03003c0c190f1030742d440321254240d1980ba40e168203071001c81d02c0c1154541c200c1e13014405405500c5034101c280c980e0515020025982d24541c8012140d01070703031003244442d22070021a045542408009a0410781540d04220002c140c022a0f0919009403200341c1182480c0880000400c2d54901950f002d07205c000303400c1c1d00c0e00843d40740031956540088044a591000d91080c0710510180b8403c891240402400507403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 398106582 1250 398105332 398105341
    0x507030c02010e06090d061407030b011b0206041a130f0f030b090114073903110c13020d0b0d0b0414190b0603251a19020304180e06 58
    0x1102120b0300840c81e60002d80034409440350761b6498801c0403d5a0183d02c00140b000c2214901c070005410042041c000d06050500421030b99034001900d095441440418414a01d220b1002808a02c116403189210451810700840c80d4020f220050484101284041c0d08290b5281c0e03104148120520400300d1a9040d141c003040820710a200c0281d1201428000040142c207400306c94507040c0040d1248000118211211310f60700a00d072486030541a007a4400004003e2549842841034040e600e0050030441c0f50941101c19840402480400c0000140044164031501003554000d401004140151505140d42c1c00741d00c1c208034200340005900401083c00560f1980c071050803460034503e4907089846400c1c00c2c0000750302058484010300d8402c20b06103419003803c03020986021565070004103602d034807507103020352800b099046c44121002c0303498001009140d6441724405d8003407665210400036004a44020017580400148284d4070811400f44c2e05003841c8020b103007101c444203545000c1741e2050300480c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 398107832 1250 398106582 398106587
    0x1e0308012405090112020c060c0406170f16031805210c071703190c1719030b0102010603020916113f13240503041101020304050307030311010b010507030c0201 70
    0x101c02a17440000340c80c140d02030394103501d0000115a0110322841c00303d024040650b0280030301c10303030028065221901d41812080d9441101001d020303051303070f4012200022100d45c06034101c4200d07400d031101c2d244c0c9188180d043c5691100c4003801072919801404020741071894150040c0d9a40031500340041038058100610f0030010341200311141c00c07d1105001203030000100c02d003050040903031b80e903407407140010381e19205a00400a40e40603000c0d580c05c5c0f00004180889544810015005180100702890104c0041c0c0c010121074201940084100b4200900404601070302801c4981c15078801c0e0a000e004440140c882035a10301046a0301d0042040c65a054074105d0f40c14070a018114050b0b085200390302100d03581c1e50200e1040a18804005000c12008007000c08110918001c030002241e005030600c0c0090042c40014401880304030f9805188103964801c1060b10701400340542224915a22810050320700002981c0350050340d0308062200829510031401d071200c40394940c031580900c3d00b00c0da005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 398109082 1250 398107832 398107847
    0x8060108130b040f050a120e03010605040b09190608030406020604051b0306240402030106030f0c030204060912050a0602070c080d020c100813050d0509090109050c03040206071e03080124050901 85
    0x83d1114812580680c02061f80e81c00c100c002c0019980b202c01008400005060a4420316031099200e54070740b00114172141c84601d140340e03004081c140030125400380116441c00400f015000072038148400f040c0810402e4000400d80c6c0142c0c0644103c07a4030104c00032000030003900b548074160301a0402070110750359101800401c0002c440c100e00c88800d520071039000c503041360400d0b40140c000a4880c0e034400c4451015126010b03081003286030541c5400d050070405441600c00b441141c4e101007003003886105011052244040c404e0344044250750700d8007c0c0c204a02d940d0f04901440d440e6008400c101c00745d1038000920780819110181282e004540b00043c1680d6050004009812200c008681600011818803500e90040800d131502501e5800a0007440003642d0141c004030002ca16003401e004001d81000c0c1520b9129a0440d5029a00c94040c501081691564820200c1205942002c03104040d080082c1506075900c88200b201003526107200c401110609245a001046041280500951040c0c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 398110332 1250 398109082 398109113
    0x70e07020d1106060102071505070506430509060c070303030e0f0106050f09220818120a020405070203070f0507090b19231201050f060315010e070c1208060108130b04 73
    0x8140b801e242d15600c5050520b003007141d5021140810000e81d1103140b5100c419640d541c40d04a0301402986034dd50205600301c800b15036400240080482d4081260780d501045a4241e0803070010348100c2945c038917015001d41029a2014031600910005070b600d007005214a804480d40181081c2c100c64158040c0070a80201802800654844d4840c000054501012001c4801e2054140d6a5200e98070074020142e00b0100c465940710b6003030540d9480d8251000a02030020640454000400d501e0303a160a0b0325610903588000c210f0030806d900f40c41804800319001085481b142030500004031a041003100700d000c0d01c84541d01d09400214244401e6a201407103806c2413030301031000d4607104c404000065900440c1d01c40365801d603450b8003c005c450b05503100702c0c5030040320640083c120391822404281140105000f44111581c2c044002a003d0344103501410100d03420090307503041c40d91042c600414840c012940700703000c940350ba40411304a41214200801082d0410903440441c0c540e41d581e00f0321b4000c4e012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 398111582 1250 398110332 398110337
    0x1180302011407210b040e0a120201060e0c030a0b09100303021b090a05060609040f0f0b01020d050703030c021f09030906080c16060e010e060103150203160e0102070e07020d11060601020715 83
    0x550201c3e80c0c855100b2480d070f001d03401004001c0c1c640b549c0341c110131205000b07500070210b90410000300700e00420008540d80003140f01141544a41d0b4540d034480051141c52005075102c2d6440d414006214079005010042e80e0099080d01c010110407407802e51402c24040306542c1250b4000d0004900841c194456504840000c1001307141c40300c010009815a00045812004650b0742c404c0710020710303003d100d0910b00100a0000d880074084d80c000180c401c0c0540c44001d014162504a902000d5209010751480c41c400b4000781c21010f568543e000c00108450581223000c14029500450a60301a1040d20300c10000000c0e918036140d10f413440c000301d4060701003048442a80f00c11440c8030501003030040303480c0c155407080203045a40c51800c00000351504840c510b01154410000d00c00e202d03204c001d6081d0312040d141010295550100d004034070340109a80000041c01c441020f000401d40c0c00f2a507203c080303046503915003190709103840c00d46c0c03241c0040e1607440c00f6a008941c100310313412614880d601160140d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 398112832 1250 398111582 398111591
    0x301110a02120a1b1b0b0c010513020607031206030c06110f1f0c050d0504060b09070c0302070e0601051209030c010b0f0616080f040b0909090c010c031b050118030201140721 76
    0x2006500020031194001b0795810710041540e4070b00182c04d1040035030113141000036003980909030300803465178806c04c20040d003042403085841100401640044000b19071104080c00500d607030f480b0051440c2e41c107441380c54441c000c1c1003040798001e000040743e05420212010350300000b074050303c0c44001800c5018094041c85030501211021010311310a04d842035000302d070042045440c038800c02400080040c200000e2000d912120004290700042500a039821b28408401e6031301c0380c90041e40ca034003954844c41e41205140c020403c81c04408000390103c0d0407003100a00c849850581000300e001c61441016420080500401c0003240e1180e15600115008011282c6018091800b0380c01d070f0307403054002d980301c0b040018408c009414600e544983c4940c1d01405045410511300008001e04401440a42048600c5003000901c90001a11030740c0b650f4803000070443d6259501d54820484220301045d000343d4030f81500c00c00d2100c0e00350030031482070000da44e8600d010f9150700c0394003c08100440140c21100e076039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 398114082 1250 398112832 398112863
    0xe090c0909070f0803040605040b0a030b06070515070c03081504061508040b0609041e03050910080609131a04170a030f060b0406121107020301110a02120a1b 69
    0x11425101d01032070007140030380341e00b074200341c41c0c1c545480003a408500c8030390040004004007a0f10005803070039544000003c07543e9000800c4d0480c0a80800c080c01e41c0e20500006480c01003000000300d200042c0385280d49141650b41d00c0030103851030041d1850203400308803600c2c005940c44881d1031081d089220000d10000b071050f1030f1301c5014000c41000100c580810b540038180014069070b500c00380e60001d01203c50803028030702a910b4107401d102d954244600d940d082d401030010180984195014000301410304410810003e100821485007962400d001c0e0030340754081010320b41c8000500450b150402000802c0f954052600d10880a0051041c0c1e407440074030056441c419100401069012103d9502040d44031080c48186c0884e140b0b076000311800791f0100800c1281640100404000288203400000d8101e90407001c104588100c0c1002075165180c404031003491604400501114400703682154010400c0b00c2e0002e505100b164884400314049000540c0456900a032070119180b00d1075407141220f46 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 398115332 1250 398114082 398114089
    0xf0601030503070b0105030105061302031b03190609050601080f100911122406160c0b071a06031b040906050a05090c0906060a1404030506040302030a090617010e090c 73
    0x80e001125950800244101446402c26003103024140032802001141898000110484900c4124800b455000710028282c5d40c010018018902e4454400c00e0703807850700e19a29103842c086107103600c00b0b40d49011000f01d64480c15224040c8a187c045c3c481c0c41d041d4407189c0b100080c250005061500c000307081007020030040c00c0d0303005021003401300304e42080d25040f510f0144880311400609000790034600078804004134070b140031440d006171410b580c519600c080450701142c04d4440f4030405002480a60300002e049a01e000c000c0000c2c6001d4002220141c014003e100040d400a50b8010f500d584a5103003000c40ea507070101d001d0b00c07454000b440040d07890040e42d00d1400b80c400440700c5112045c0d80f5801c20004150510040a940c03104580d02405480c0c0038000880d9401551074180822140d01503518009a004040701c018540050071900705c1c0c5001d1400a5496001604a200180035802d000400b80e0140d122902118520941240709030700b400b00760b48855a000b0140c4882c2e1280468070341c500e44 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 398116582 1250 398115332 398115343
    0x12060a0b0f0a0305070503040f03030506010509030f0303010801180b06060f1603020109030206070203040608010e06030118063603080c09040603030c0b0c250302210909011418090f 79
    0x2a03400e07a40607207071030380301c0380280482c2c4d0001d1500c018044101b040200044214407480500d60b8503040000c4c1c01d4582c0e0300101d683c1d000d051030190300b41c481c1c4500c42c1950113001000e141200d10620003400924000c1c1c00d80c290304150010000c0040c409040458400e02c2c201c00604245407403c0410390030301d00c9070480941c614540f0300007540542d40da0550030003815070601aa950001e8680000e62a040c034010005040c00c00500c00c140609862001040c2d03503a500703400c44151170b41e008800070406070103401c10a0040000018078501d00000d0550fa00744880d5520060303100c1c0c44c001c3c04201742d0325565101510040c2005069000c07102042000e156140d0300c1d44920b034060b60007a6035584403d801072510301100c08003d80404103000e800e00c030031800d03800d05603001c8200c3cad0040d4a844007000d419240a174070b86020042c0f0001041d00758800d0242c13002c942c01c003601c080603007120f045182c6e9a81d01c0c00b20390070070843c0790502d030404200744040d4113001f03480b1003294018915904450207070031800c4600382445d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 398117832 1250 398116582 398116597
    0x1a060304080d050c130306050c0f0403150507090b071e0203030408010e0606030303040b0c070f1211160602071208091e0307170d030f0b1210060b0f12060a0b 69
    0x8000414400c684262078440c0a42c4131040e50380c10b52502803400340c5464024014400208040c0c0c80d10300103542004004141c030310041550041c15121030f201c1c6440e480e5a2001000c03004001c1c58480080d04d4a41304640d0241103030540300141c0e00e44451a160b1144c03c0b08248002101d40010080442c0180c80c05c100800003085003000000b44c2c100c14401c1d0030704010700500700c9482540b0a105000c082488210415001040306142690302c412038903003154038600740d04025000c0c8602149031000c02d900002081d81d40e11081c13091b600720540c20000560000424001c03a0010707803040009111002c102c3d42100101030040c5525401c190100e40000c102e450b42003120001d0300342d45107205100e07003010403541014040045e000c2103096940c81304030350b40f0705000c100e500826480310a11011031406a2009204400c007410003a04005280e02c03055944909140f400f00c0140351800001d5000f0103070040d50b9071340404c081c1300752408a021010241c0650094142c9901180058000030001c1c008001401c14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 398119082 1250 398117832 398117843
    0x161a03130236060913030c0807030c031421071101050109060f050a03080d0510170d020f0f0a11061c090b06010801030203030a1d060c100c0e0a091a060304 68
    0x360080144018000c400b03080c0c0907502c0c030120380248292595984412035002c20300904411140c035003400c084450910420018060f1000000c4030000d16074480c0b0440b000b2402502c4442a05070b12a00e040d030184642c40c0600300c411107800083d170b041240e40503047d0b00300c00c0030301d40b518420748000d140070308450003a403081c00242d59640f42004085902125600140801c55200c1d04030740c61901ca205181c496440c084010565403000a5182c2d00c03400506005030001c50340d04c48040e82004442c0380e4481140f01a8805807048440140c0c008400040601d0058101c5000c1d0554100311364402c8800313800181d00e980d00c1642840380511800401c2170011013148a0750010845900a0030101600003010701000d0410103681e0052000d0703100007046074601c45d07107032501c0c01e01074154441044c80009103503c240e62200300003420700305140c400140d140301e40071950030402096803029010b0b1030817501086200e41040404800b0801001d10360f00107401640d00d038140040c1d1081c03180000c0e0f0607a0088404884 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 398120332 1250 398119082 398119129
    0x1110c120313050a06051606150b070312050709120c09110301061b030e0d050115080a0221060403080a020d06030f12090f05120102070b04050a05161a031302 69
    0x4110b050081c007030009181c1901c1076841503060240c0140700b40304840403800c1514003003040108000d1640e00c40c0e00c143c001d0038000e11515032164890034440d40204000c1c1c0007d1181c4104003c240807521032940905010745801d03206c01d2400c031480300e1a01c9441c0c1d098600d4100301800040601c0d0750f0090286185000c030340c4569030743c1418405403800c8807140b07000031600e101041020009412038215800244100c1d100350380c1c1001c40c82c1c06405000384603a1240c490066000000c0c40035400140789604900c21240c00c50b80b1004540404000040b0b40f80c2c4400c035500c80b60100300401e000700c03a03254118108000c00351420310381e001024291349995004888d0030241b0032426040c0079041021440744040351421100312441d0640100f0340d41e505001d114855154070f080c900c0d440340258115595070742d108080c10074500c0c280c1413181e241c3c0c2010006844901602210100c42d0a0040744401926106100068051041005416140c000070052024150140860030140c0e41b25540211450f040540040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 398121582 1250 398120332 398120347
    0x5012307020708010608150405010e0111040501030e0303040f080903160b040609060305062b1a0117030a0c0f0212100911030d051c1e0204030b130f0201110c1203 71
    0x2458244580d1003440070f81d1512401b40607061000c01c01e00c422098022501c082600c442c144079004250039403201007250f180c165181034120025001d00b0444000b41c134208080800b200c10640c4903c002c07a80101090140302c249000144e00b040070f00803ea002030100c41003000f42c0702071215044403503003043e003804101040400c01304c0da001c04198054031aa280a00c95814034101140c0c50410640d0004280c0c100b400c40800da002c5403910620260341c000589000c1c086042c883c038503071500280251800c40c840102442e0410000008562400d200b56441103403103a01611038118403001503404903401452415011000d81e41040f5000d02c0102490000840c01a985800c000d00d5a40b40001d03800703134208a411281382d98121342920100300e0203814a22103da03c0145100040003001c40011810011740d0031111100701c664040c00c1541d110b9040d03000070ba141c0e2081c2d00821254480014940343c1079000f0b48005501c580b0f1500c0c800d0f11a07200301d80e2400203510004a90004c00381c0744890552011a481 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 398122832 1250 398121582 398121587
    0xc040e0702070911040312080403020f01060f051504030203030a050c010f0507030c0e01021605150909040c1d0f061002012c0c12030a1d0612040201030f15050d05012307 74
    0x50032076aa8a51403989018696500c51044018007841f290a0011120000301810700a2100c07450360203080001b0010182c0301c4283e00914903260241078010032281d184288241c480c9011102502d800800071400c10038020300c1160b05500002c2007180c5075490704c48095070381a41d401071901803212502c01269000c003c1900801010744541e070b05046604c905a441a50950070316481c0030707100d0640b401c490b007050030780b68118548038000420743c204800350f00b040284540502a042034401d4103100c02e80c050308482000a0b58134050f110603d92400150105900307180c604a80c04007200745000102e00c0c3c800c11a4038000212040180c603c068000d2344400c0042c04080c02414020380040328142c080003400004161380b809040752103001d0003401c000310404206d01ca080e0100d411001400c840d03880302da01c00040400001078a089000c47d05010b20260441203c5c051450f02c0040c480c00f10840741d1400041042030815014145c03159541c44001046200c050040c03900785401c9910710550504040400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 398124082 1250 398122832 398122841
    0x20306040b0307031101030902120604030804052109010c02030a12110c0901030503070303180c08010c030b03060912031f0308070308130c0317040e07110f0f0c0402030c040e07020709 80
    0x6502c2500a14400d00014220002c00c80900c4401e18000686d41c0c841d101160001040501c003019622648040004155200d010f481c0301d18400d01c291044409000e5820740010980d01c4850081e4000b84405d0020f540b140f4502c8942d03070b0005048070004205601c0d050760803560103410301c0001d10050101850b201003040018400e207402d80e2072608039031454440640b01d0080070001410076403600400310408461007040700c42030740c00005015240b82d403202100d000b4591307411600c007c07a0510070300344241d180205040f442403001d50041c0c6030281007501e040301c8560000340804c03014071030314900140300c0c40d01e0700249018522407500350303aa0f510941005400382c0801005940049000c0c41000c2c009444080d84204076540001c018085901030035145440b40555000701460350400010880c2040d80800e00c841c141c0160b03019a801441030b030200319151080ca6407460150303448038000036441c0c102640116400a01c00304141d08098a501e071400c1c00c0b00c0c09550050052380084410b0121440f00d208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 398125332 1250 398124082 398124101
    0x40b060d080f190318050709150b0d090b07110303130305040b0a05040302030f0601120f151b0e03370503070c030605010e13020105090f0901090c110d0207152102030604 74
    0x1001c0710308020381c6e85055481107a4050749100319260b0074113060f640300507107180c00982031b551945912039048085050042c40940000c1d184403060701c2c04030f2182c0c2c2c09013506042d100c901d0009185155034005807800c0c0d05500c18021402c104013000b000030100301da88060500c94060340d9407a070342c65146004041c030b814022141c01d0341d1030b0441401007101c2032030380000d104141c2d44415a03221603038243c144a8042020341405040403410448a07980500000001c010315010380d490354038100066a09142c0c0c3c504405076031565400c0000100c0050b0072032000c0741c0c005242802526080f8491a50b6071a096801c6a84102c0741c00003005014000c01c0329034041c45000d448100032074146c0c1e10780085a08005410000081c2c103100d000203014201c0d0b1602c82ea80301c546c11003d0030850346075a560040500820154104d5000903124046c108661540400da00c2d0514510768000c0ca0501c2c24241d905141075038640300c10060042c2004114400200710344030101c24078100c5001a240e140c601e00384410303036080702f2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 398126582 1250 398125332 398125361
    0x4170105070e011b0813051c0b0c07020a0803070804080601060203210411041a0a0519031e0506070306060905100906080c0c0708100b09040b060d080f1903 68
    0x18200980745034005451081c5040920713203da603108140c0c008000d180f040c40009000c2c800c0008000c84042c1081941104036442542c200d441c42c11011424401c0d255003020051201c058480403c5544082d240070784803090004012450030340d641d003070203403079548641c9085600d9100810100328454040c0501c0303004007a05e00155151481b0071b8076558031b145009a003182c070b110088000c40e0520080030619402181c015000700010304441911031401000c0e155150b2055114604c0030989041004900e00790800b10b000c060401c03400c540e00e18203602d0f481074840742c1c44213810201e03070301050082001ca4000c000b15100010010304100004100003600e41113a8018100e80319000c0710aa4014151021600b072840c1000c020748032007551204038443c02c000c0558501c1815070210340c6d1400400da00642181e0f031101044070341c8200e4144002c0d142c0464010348802c1c4141c4c00115141440311400c1d44e868460000e1074a4640381742206240c2e074000d07540080d11a1182d00700a1409034040c803509800c94000b9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 398127832 1250 398126582 398126591
    0x50a11030f0f160c06091106070302011d070f18021608090411070201050a27030303020c0606011112030408070c090b01080f01080c190308030c070b100f0e09070f0b041701 75
    0x51000e0002c009600c801044203a1b500050780c02d00146a600d0403005100030211540c94903e414000c3c00707070251120144203030b00499911130b03000b400044c00b0070440302a0100616081d15110000400d002c09009901e40c507138007000a03101c0d0b00d0001c000500c0c070512803c1d01c5030700e405140050104030744840c0900384091804100340400351b0b8000c01074a041000030314107041451501214560940c1d982c42000e90b03407548410003c404c164264000c0e02c15181160112105682c4400c011034406040c42e100c004035130406c08a03007030850b0079a002181e1140c001c0786803d1903c0c0d10740e5542c520500103640302031001542c0701110a50ba40e41301402541180c11000c080d035865040040b00b903111001101e255205401410740101401402181007006640002d921900e9241040503801c0301c0d4044041240c510805000003072611a100b1542c000341c940e0807004d07810f503d05142a101c1d2140002e000301200307125114000a0380401c02c1d1344400a00015100d41e9282ca03d0041000d010001d90f981550f4141d040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 398129082 1250 398127832 398127871
    0x30303010605160c030209012303030301150f090e0a05070305072c0a030609050303090f0106031208040618110102011a1e180708070e09061003050a11030f0f 69
    0x4002070b2a00f4a01c4051040048012407030041c00107215644000e4014080d1800080d1481c10440e0441840b1042206d807550743c0c03038400802d43c40344000d00910300f6910361f910190701850310074500c0581c0f00200c0d003419410030352039054460794010304841c5107807565141c808015081d030780740c000c0b1034100d90241000400f038401c0200c000d840e0728811000d0841011580d40030a541d6541007528001107800107070402001d102400c0c802d03100c0c0e00c00c40700444940b1509840c60204d210502c84c190480390001501306080d908080112401080030f4015500c4d00d03100d40e481c1c94042e0740000130b030015601c243c1204182c681d205001a0a6a041d00f610560081801413101803603200c001911401140c4500800114820b88001800f2640c200d1420950005014200b0072926000380300317240101c007a03880314580b20041100300040755000302ea001382c12a00d400c0031000003502940090344c00120003800401c1d010701e09080c14119030411150401d105907203c1c10f0062040001c0d48894011400c0e030140d076200f091 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 398130332 1250 398129082 398129087
    0x20411120a020a02071206060e060a0303020a0831080705010914091308030406050118091a0603011b210507080c0f2a0f0d20010608010c080108010b0303030106 70
    0x1040c1c40c25880e00001c10301d4040744203010f07220141940b0306204240111600b0500d008203c50f0203941c135a003181a01142c110703e0618000c10849034194010aa1044070350703104841900090001c0310211240c51114081d00b03103403076800c10000c102d00701110849191040342868400d0b01c0c5d10080c117000c400b01e414000424803001200343c001040d150142951604442000a80303000d00e000340c5101c00200900c0100403da4000d5030480f01e043c545045000a50301d180001c9410014006120710221301c829006c42b101003500301e0344200c00500002c1e5119030704040d4145050281e048500180440c11100300d41f049001d505200c01031a48000c208034601110050149807019000d0301031128049071500480f000b076412104100e045002c04143e84001c050f4901019450066107005809203111172550340380001040e41d154003890365509480140c0200f81c0d82042801401105203540362100814a803209008402c11030b0f11036522100a0f62506541d5400c5801c0b2001c4030f40b082c0c104200400540c0d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 398131582 1250 398130332 398130367
    0xb0718091806060312090503010b06040312020708070f080601140319060209030d08010e0a140612010204090c0e01020f150c090310050103081c0506180c040f0f03020411 74
    0x10080c04000440c01d40380300c910400d890004400504803400c00001004200f5003200013141404191603d0a0040d101c0040600342d031203a040740f540041e01403000b080070504544000ca030040b900e0040d1495180c488080608080c0590010900150960810010110100240c074014a00044110120f0310b80074002904e820703074030700844541711032043c0403400d20000343e04440341444000d0860383c0440d4010009001084240302d420801001103000813074810650058040c8a480c401402010f980c0d000c3c1003111110301244808815075007400701150f12401c82c801e0030040d0400d0703107403040601122000245460904984800307140c0114699501d1091507016042c2c208501c541c410780c560f41c581e0040703440c058003002d070382500301d00b458000024400d0100090110108520300c2c44444800091803c0503071b10b0940e6400e4100d800b4aa041d0442c810007a041a0844403c2c1102d034034050b59544400c00841c030a8021030703403030980c1c0c4004204502c0e00d4070410916048041038130f400c0001e40d14502c4030b0a07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 398132832 1250 398131582 398131589
    0x6020c03062a0c010c08060a06081603180506100312050705060705070f020418030806060c071a07050d050903010501061e0c05070b2d030609040816080403050a0b0718 73
    0xc001d282d10701c0ba1005488003074500c18030800c4001c01050400340b034020070100066880c14000c944445011824030b00c82c010fa584a00c1746519800d8890080c018110000e10240034860a55106501c3c00c200142d000c0c0a424020303485021511020750941c10200c03000c0e20745211603414070400b001680002980462041e90111044c20451f4882c0b040c0d0901400007034811800035801460003101c1c081c2080d00d801030b607642c107001c0d9403107c405640d00000c2c050244541134074080a980400000c2101f030700300d06500c44c2220002003001341016078542c1c6043c5030401c0c0c4040140407400c0411058230f20300702446018010a0903180101800314403140d900d00030301140120070204004400044180241080305e40d004000b103038401c40e514101d0070640c143c1c0280191a0542009680c2e400c40076809042094074040c1c400200b090101c1e0726a0341d01c40b405540320f00341c020002100031004101140054001d00020b50040d805801549030900c2c00d800303094001086401030022003204240104000f01502054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 398134082 1250 398132832 398132881
    0x120726100905160b2a0309061b0f030304200d1101090b0406020a021c020f060313020a0b0a0215040b0136090c0602120d09020d06090602030106020c0306 67
    0x30300e11420300609107260b405440640003203c440002d0710b1003280c0000d09000702c40301402c002c04800c500007150b00540c3c21142d40c80380e9000303000c0054149800b20040c1201c1c1d200201200708528480c107014248007010502442c0c68101000f00300a0013201d00c0d0890390240111800408055a42c001403c024040301004e070000200c1c1542400503400350360120042c4c500b003110b841c3c4882d661000203589015980c0100d0245111f0000c0340328240380c0c01d0724541780e181d00410132401d240c2030380b083c04404c0c0c000905030780d445401707021a100561181158003001c1e0420004256a8070f0703104a02a10788801c2d203010740120b5003084100000f00e13601c940114103403400620201c1c107802d00c2c1e0622040459000e890510040e00205a21010f003800c0d5004100031445806140840c5076034407001d17a142c20303d003400c070b400421040100d000c40d18001c2d44040a014401401000d4044c400e0319440d0895508450466000b41d000005001d141d40400c000248a40202c00915645c42c2405110810800c1248440329 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 398135332 1250 398134082 398134091
    0x30606040e07030b03070e01140607050c22050f0103020f120d030c05270907020303070c031407060c080a06090c1e1103070c1d01062c12072610 63
    0xb1a102e600081c8480e01c00a0480b00f42c941c6881404102075420f20461014040c0c0040201042c1000c0081d1105035421a005c0c0088011f40400e11190003100d10a02241540640c50121100e00310300c1580d00880c0c410741e141103075604501c144610b4000c4001943d01c00c0b03110781188105410006013452050721289004190006d0285060b140f5000700050161a84460403209020b003900081c0c00030f2114080303070000066101d80b00184d890344000c1c0c800c88000b44844000402227400790751084840304000913070300d00d003c0040d21008100d42446641e80002031058040c00803199150007084064011483c2c104044c072148600940020a40707042c100b004031044a0034009d150080c120650414041401e46c0c1d07a480e80d62400145070015400791030740d503d2141810010822144003094140c0b20242c464642610551203030341e140c010b0981024a00751503044810400d0740751801143c0099400303e0080500d070341403024080d8100c80c0030016259048200020000c0c98000155040c0d15080070000000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 398136582 1250 398135332 398135341
    0xb061e061603030b031005061e01140703021002041401020c01030b030d030e0f070e042001080402011d041d060a140415091709030f120a030b0d060908041a030606040e 73
    0x80c081c4c0035400c5050343c140507105003415070100340e40000744a41d030300b2144694003501d8003411409004402c2c0c521800114590b01c4450b01003029402401e426000340111041814607012900503603102e90401011089040200302041d44c04004100c00305800342400e01c05816038201180d9078540403210b000c1015101c1c0031101d40c107a01800032240f0044150203031911940c607081d110903840e03400c0e41e00b150040604c10401d420110b90a0b031f83c6c458018143d5030311640d07071101d40045400145144041021400002060102d82e0703441c414086d1a0b0462429141c041c18604039142c100b03030700288008002420240c400c030405002068141d4056030010a81041040d490442001040004401009c400000c407080c8180b846e03032400fa062400d01142141d000590803098181c450008000342e80d4484024813880b024180290842880e084014008686520407a102d5105944540200f903686050020381807040190310b0407c020384407807c40c01c0e1491401c040d400302d2003030f03c214410003107070502240108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 398137832 1250 398136582 398136587
    0x140117070e0111010c0206190207021e03010f09052a0a03020616060f051015140a0e090c180619030515040213050109120f0228030b061e061603 63
    0x140007120303c6a0080010114100c4082d688900c2521082c070040c0840d14008455541c0e4000c54044680c003074403030340da03558001c6018290070000c000200c0d459501c589850441491a20904604500a01c01420b0300124444c02541041d016403500d441460500c1545800303466204000003140c6d4182d81030b640c0c580c1c80600035102000780840051a0303904180304505a8015500114024035891501462040d52210000e0241e82c031100c80c00081100183c1081e20280c40d0b13409018043c20324103140e01642e09480004400c40ea00b15001d040055000ca4007200405001c1809040c1035000d8415034500b122481424040940c01d8807a0010076444030001b8901040c455078a44d01d0040c054800d40d00d8080c81c07075225120034483c0c00742600050460000260302101001d6031a41c540d001030a80c2c074502855000c0c0180910940b055031541a254603120303080d088071083d20030041d4010100708d05641003000403c41c03040008c882842c0b540c3d0a040f4100c04682e650b0040300c3c07544000301641d0440c0c460130310b0b0a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 398139082 1250 398137832 398137847
    0x80a0f0f080409020903012711030106120b04050601092309120429160818030d0809010b030d080703021b010f020409181110050d060f140117070e01 65
    0x1c010716408580052140d8058000d040002c0b41100248181a040f0301e1001d4000980780d68881c2c0d4644011701d5901003601c0341100244150060008603100d40c58503040074607070a81c080c0c100c468400b130800304018002d0074001c0e2405426114010300c0407603003c0010401c0c0b1017a281030103025200e1103000c518019010041e900368000310800841d111541c90000c0a12a030b000542c081034820710900312401c003c01c0c00c084030f4990741107100b600000042d07a16011840d0b0044070800c40c82d40400f48200c001a030b401c006c0c0c1e12000310175994007141803610038001429641003500c1c0a000346d001008110740700e078000001176880701940c0340060712040d0480d45c400404030355148600c0194a0403010000d074400700d80082c0140d072884107090001c2d075156107201c05800030004010384032800c4c1100600c564130f040e0040354109176041c40c000f810001048411400c88102d5405071080c202500c40800c100031400c2c1c8540c0301000b090801501d0b42c140d900701c00d2451702d4014074030001c2100100f11411103a010fa0780 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 398140332 1250 398139082 398139113
    0x307050318010b180906150a1203030e0a260a210b150c070b090f0603310218070801030201260a1401050d0812070302120412030b0a080a0f 61
    0x100007042d010f00301032020f04130240c17101c030080d01680002400060504658501c05040a80700c1d07620207207054030540304e44001190842c02c05071109005502075908002c6001218013a01d400038003402d10141400e8110034191200c06118814465461080e4000ca01e40c04541d602c901d0b40d1000b036000b4099a0014601c426100c1e9000f5008111107200e070034440e0103003001318003107001c03101d4031501c420318180c0c5400344410803540514540b056407620704200028503003001600103200452651030304c52034181c6540480c2c0c1d8810308482011203040d85068a03440740850f40818519101d03041c460802014134105000190500c561107003490070304c490701d9a14011148035003129010500301112a01c0251590b56000c40c0c100903400c1c000310f4a40f07004451460342d0b50340300c5030580c50003c1078891501c540100902c00340c28160300340070821811994045413441588504e42914a8920a0501a048900c20010140540507003030b030501c0034000014612001c00d4220394000700c0900549418a5855003c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 398141582 1250 398140332 398140339
    0xb0a05070f23060711030d0c020c0d140d08130605042108010806100b120702030723061f0611030f0a02061005240304020112020a09090e030307050318010b 68
    0x20403215548801c100e0b105010a42d8109a80e0540c84614049801081104000825400410005071040c00f0755211401d07010050054030742080390000010051540c0202c16140145a45202c96540c5170500000c520142941040400f034280400c0b03420200014140040c0150354840c00b140901c6114a1a82c1d900c054001006c02c159034482070082598400384944034540c8900d101040e1003108214014003503c1d45895101d0502e00107d41861003070070b01030300780c0c402d5003c200301800201e4200700301425103039580710303e1031b5402560070945403902c0002030041d074440381c40c2c1c14500480340b8201c0d04501290818a815074140e00808003513411441039410050302580000742600d074064000c59880e100e0b901c3d040015105982e10002c0c0034a02800c3ca28080000010a051080c1445010f02640d002801858441c00708882030450400326800003c0c01d0004c5540f410040003416024090240030300f440304c0140d42542030454001e462404090b011410000e80e41000c911016800d5002401044008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 398142832 1250 398141582 398141603
    0x60d0606052809060b0f18030304230102010c0210020c1204080616020a03020a0605130b0a0213061e0f170106030204031a2401110615190b0a05070f 65
    0xc09420780b8500551030800c281000790b030000251090184128000c031070101750000d242c44600e43c04109a940a003902200103c002c006080f840e032010000303840a0a403071b118a0000c2801071101703002d0550101a040e04680c14100302900040e03001c6100da107689102000544c48180060b046400c20301100080c044500c1d004c40e0020340d400d40000c02c14025070620141409481110900300c2e1140351416014000d030340008a10400500582d0040d50b2050100b2044680e6403500c5e542e02881090503900318072038075004111000791881441c0204003c159605081b04003c0d80f415000f03082c00c0d034004c00481484030506482130807902a000a124034010301c44501c05542e1203c0003d00290480c0c001030740c0050540c4806001c0080d83c16006001e81050b800d2400410324030104080710f54601c400d21410019103682000f6850002c10201d40a03004082c42d4030081c4402d0410701101903164110350700d00d0412803608000151f0f1030001c507081d0300190b2038400e41e26080c43c2000303121065120001007100780b01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 398144082 1250 398142832 398142859
    0xa0302120c09090106020d092718020316060801031e0f03050d0c030614041d03071118010b1c111603080f060604060c0f12050a02061608060d060605 65
    0x101d00a00030418101c8007070300166240c072000c03039440c1c00c2265102c1c00301d9404402405156001e40c00f8801c104501e40018842010020006050300d40190038540c8a1410165031011840c0a00034085041d00301c441602d041c510f450002070405006100240c4041e17500181d9090680700401e50042040c0c0245400003000e40d64035005180da4010301d54144514500010b08404c2842405800e00f11100c540c40500344081e1310041200034241c40240e4800f2000281c0701082062050010b000344600070381c101c0a80d0f5803140103010303004650481c01005092144018049800c0500c2030b01e40550b040580420706880303182c2c0c1240280600e0002202140700400e054010744108034400480900c242e03141011a04d400e0000404030005036007640d801902030200380a010f110f02c40000e4510702603200c01000c3c402c00d40700c00b0b007525a0705000a00042e40080c1518801d070701044243e8000100303400c000300f0040403501c0100340860280c501846420b00d1901c040078402c2c25040000503103001850710254548 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 398145332 1250 398144082 398144101
    0x60f1d03010e0d0908010e03090a0905092d0f0d02210702031b01110a02030601060e06040b0406020c09090307020312030a0212010609061d0306060108060604030b0903030f0a0c090504020a030212 85
    0x100d124405c850360030504000110302020003515807503000501010f81c02800c226441000c0c004c02418140b0501ca5140c4050121001c828024000e41191400c421454001c991550420a02403440c20782903001c10f0710140c200d580002c200d082044c09101c44110340e81e030389000c00018481c100003c5c3d0b0511a0350305066002e00141c0051124113002d880c0c0b00610991138410580b181700010000c0e40c107030050743c0100441402401d011079030b04401002c2c903142944804040c0c405801c250001c0380168000c40c04290703a418000c440355000038406004606020840e1700007079403101d981800e810240004004078400c404580c043d103a90700051502c0d5043e40da16a50010842805071080c00002181003a000d00100c0100000140415024000d0500f0790340b80350040d501c40c0805818035030400300800001010078003041c0900c5c0594449405150b032410500000c0c000d03510094206c01482c1d03c1e042401ea200ca070008071000458005a2303025807520142c0700258000e024615100c1030b00e0110b501040020358 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 398146582 1250 398145332 398145347
    0xc0503030f0f01050f0117130f050705090609010305070302040c030e0a05010c180b03130507050303030f040201090b0a080a0b040f0c08010305160f03081321020a060f1d03010e0d 78
    0xc2e42003110070030b80e81c40040200082d80d44200c1808510755481c04807500783d5284031580c0c4100340e04d4072403682c4207159483c0741011140500a4516810400003440341d231400e00f400a802c40e030b007180c0e41e0060b5419a101d9640710181488004d10175070b51602700100c03450003a00440c00d12450f000a036040e04c469804c019001c3c0c0f4880b01102d0002e005617814111160052007144160b5180c80da0071030441e500c083c40c1241c54007034800241d82c140314245000400e07a404100652169081c1c0d0341140792401c051002516030061031300044401f203024002501c00350341c0201764951290910f100800d018080b40b0100d401494044448d6203e18101454501a65040754401e41224400d201726152003211003005400c14a40e0b00504100d82d6544400b00003003202a0040d00f000400d243d8500490380d03a4900641210080469960001030115550300a514264881c44014117880c10120a25040000010400c0403001c25030409a6000440c0c58550748007540100104140e007000c44040d605c400c01c0150221 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 398147832 1250 398146582 398146591
    0x71713021815010f0207060c021201111b01020708192307110604120b04170a030b01030b030109020303030718030203010501060e0a080109030f0c081c150806010b03060d02010c0503030f 81
    0x215070b40c1c80202429403068081301019085540540442410300300100d801c0c0b18001c80c1030382d0120081500c0f140345a000c1c42521020942584460f95070403004e5141241c0552076004041c071030b441440303900007007110701048400c0ea18020101c140d000c1d5009206844100c100c840c00e0021151910440d40389010070001011028003178a142100700300904101311880c491800340b40807030343c0114a01000208507201240c0c209100e951904980c17490700720508200d801111091001a49440c100012540c040c03250010612041e0001c1c48070f114a80c012959a10000d00b285080040c4000c0c0302102c481c0404101c5c1c05598003c00034030403944c0d1500014410b45884070340d148140d841e414002070041c414400c800d50b0660546a2900a02c144042a107000314517032400e960710321741044401c08404e0380b2240c07160b07426203000d4001006520b0f900d000d580c010f03060f0002006917110200601009aa11003507030f40c003c00c2280c8100c081d5a4910048490402c4404c0c010601c0c440441401002c1b4003004100b440b5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 398149082 1250 398147832 398147851
    0x110a0606061d1c08070501150315140c1e0d050a0506060316080402010525030809070b1c0603080403080919052101061a130503060717130218 62
    0x1115049a40742c075407803140305809030b10401012011101d42401d00300c10a107140540800f17403e050907a1200340c2500c0c0a020600083d0140703040c240308000c0c8c0c2d41c00c20105070380300c07207410000300490312150424a540640340c01c20860010548400c0c00d0a92542c44c2125040b65070110b403a208a00d485001901007507820b165100e00307150000300c3c0c83c10314070266441100801d003411401140c0c5030b0300703580c1080c015109170b040001c104615210b4003054414050310701402e2124120044090a0007805907001038000c141030303000380780100607500401044c1d0740ea04100d1241501d45002c40b40100006150a500081000740e0104001090041c01c04c003920181c07400f90750004990540c4207a100c05c034403182c017889a114030781415400f21200a014010b03280c1c2c40c50300000586e40e46070340e080300800d00c0310041031422000018100f4030321340b80c40c0c41c10002042d050300100f0060800000c0a014112a9440808182040300002d102490a0060041c80e543c000d0112001c200c80d01006640c0d254003110030504c1e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 398150332 1250 398149082 398149097
    0x1021315020c010923090915180a1502041d010906091e020724020d0f050903040b0f0f0403121b030519020309063001030f060507110a060606 62
    0x901800410020b805000c140d440c0c1641d503040080072000701400c0f012140f29a20032040824070740d00e50403035207806407500400620a14000780010010b211005042402c105402c000c00105504001058030046a010385000c003c0f40900c000b020090180b98023581c1c4030071007541056200c9410304051411f83d00c1548040c40f070b060322003580c4401d56020714002c15103850052070008418255078080d003025489028289806035025104485600030b142206110700d40c001040041c03441c507481000c01c411400c403001d000a10744040c126440f401030388203401c1c1003100007903014981014082240c02c4403c0c9801d000351a01e4483c00c04c0305021811210090100b144214030380701000040d5074011f0300f99410303500d007494040401107010384209000c0085056205c00c0c0300e9060329954003809800c1601c00c80052001c80e140c040030019150021058000d10700c48140010310100c2c020b80880003010760041d101251341e4660200882c2c4440c4100a50b0360305008a01545c020003200360003100858515994051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 398151582 1250 398150332 398150369
    0x1407111216021206090601120519030201020d1508070e13050706051b010b03071503111b0105070804030e04090c0b0a030519060f120501020906180301050f0c0912030408010213 77
    0xd558840170345541c03485038003140c010000c0503d0041521403d0748104103071601540c0c550001204aa1034a000300d016035004500f046c0c4c103035568407400c100c50004c2c0b000e15070407a25084610b51620a14000c2d03190320400200040c41203140c00b00e064240d641d0200442e00c10a6031540c00420035005045424608031019400001840e414002d00d010b04000a000e449114a0482052140000480814149501c82c101d449070035280d05d0180035031014000c0402600500c0e181e8076400c441e0300034005014408460141300219610081031200121b00340e50003e400505810042101003541d1700107440325800281800e80e041d890b40041e80110800d10b000c1291118507845001070742c1c1c003401010401603100004000102036020580441401400014030344002e140c0480c00d02d42c03007225122000080403031640c00a00342441003940c4425128401a00c50625414596881c410140264410b02225040102921013070007228002c00340040215540c021a071519a40d0b04114410130f000c51002070000d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 398152832 1250 398151582 398151619
    0x23f24040203010311010f09181506050c1f0b040c0314150d0f230d0801050406030305030f061813051902150f071e0203060604140711121602 62
    0x890682e6800151710240b1800c940c01100c0040761740c00c081c1c0401005000009180b00781d550843c1500c0800304d0301144100681400d2407142c62194003440802c40304100e820b08103c03020407080b1100d0729411601444030a50088500600480080c55034010300d40038280b0400c0f07405500003c5171000000d805503059803894111203000702c0840c90580c0154140c4445400600075252080f00c641c403e480d003480c0c40d1308801000e0740300741d20700280c04142e520812a0003669604441080c2c0144002c4405020450640d5001840e900028041c02c5021103040082140381d600c00320700c017a0000e82851800754524100400b0201c0f04c002c07c41c1520680120205071080151608420320540c3d00074106e02d039061141c0a21098070340c84448101c80c8280280701d24400100e214032a58600c1111503051440d1064a004260600c107019040911580c6401c10342d214036045c0e0444c166000101e400c05250780243e0340b40340790503c2d1034039001080003070001030300c601c0703140064882e0071469000ba100c28a1129603012039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 398154082 1250 398152832 398152837
    0x603190b0d12260c0a1706060403060b01020f06240d120c2d1419110103020921010b060a17060105070203030304030e04050901023f240402 61
    0xa44110504a2000b000382d0090074050a04001c4461400480c1c40741d4052401c0448192130107900648006065030380d041d8040b48155060a0796071203020581411000140300c2d210318030000384001d44411601425a000744055105c01400c0802d480c011b140c2061114204281c18010544038000e044004d000c41c01e1031500140da060303000712032004c0380c141d041e400d0756070943c0d600f0100c0e80fa10b4070b0035401600d044000603010f04048222001c0c00001520315000300e240030080244029984405c0d4000c0d0120304101c075030b0704035641000480c000f242801004070b000e44500d4500941040d4030800c40382c0c504006101d0704201c2e00409000b080150310400c1041901e1260f108084005100340181d10384210b1541a0a604070805044c6981f400c03c8641c046400d50f001142c06402207040c0c1044600e40d42001d0141c1903002c041d4600861615016150b070010b0b680c811039042d03100103881801c51802c0d051b100045c1d0f48846a0420710006450700d4001c0c10041c940303411b95030072200e51003031091032141414000e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 398155332 1250 398154082 398154109
    0x703150f090e0a080406211406090c131d1003170a051e0307020d1404061d030106030f06060501091d15060409090201170403022104050603190b 63
    0x903115550340c03400400c10060810504101d00901945148a00003040d6800500c010b01898071000b440b0300901d0107110110403039903c90007846003010701c09400703c40d10003901da80c46a022500c40510381c542944a100c28062248140c7c40c15500030000300c0c0203018100000e09c0301140c108100c6150741e40c0e140d14441c030141440014a40391045149445030407049000c0c0c200d079851480c3c2542001607000214207460b0000391400c4100c0b40c000113105c207455052040b48081c08140c102901044a5000544d0140c452072080f0810080d00700c1c0400004112426200c0c60074200034000d010458076410141240c611045e0b00f1180d25180010000da154000c1c2200c004503031208080d002039001d44900601c40b150003c1c98083c101c00710f012606119aa0000548081c0444403000a018845803001406078900c0f0f00e2404082c014083c200030029a00241000039070815040e4040303940045100c0500500030391304007590200012003009521714802041c0544c081e03c40d40e0912a400034072044c00425200901c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 398156582 1250 398155332 398155349
    0xa1d0d0e0901080114071b12030f0507020c030c0120070b03091e0d030207060906060e0702010b0402070b0604090f1401140105100905040510052707050c060609060d120305070315 78
    0x140310034021f00c2c034507404005c080552540b0b070405543e5000c125034800708080c00f1070b0f40c40451800c003544e00e04c81c03150f10240600043c180509100300099454451710311850400c1034201c0919010441e081070041d10106410031100c2694555491000c20b820480d40c0843d9446002c0e04044101c0b036036140741400c01c00e400080c1070310b0072041104402940c0510070940c0d415840316001d20006030706214000c003d201d40b0100c00b0303c3e403d141c0b038002d003514845080103125500610101c8049509080b9041d0017102c00c07030f0b000510788210b1a2001c6106950b50000d0207180c0e11038001d845425040d041650b209008511003842c03aa250703010400b00c2d05400074808002908a40180b01c241055880940c1001075170300004001680e540000d6220fa200212520303025a1004a40b980748006040503034100c2158117000d4201603006100135a11600201011321900404001c110107440b10715400100c20b4200300c45550010018a010b80079000554510b00064544552500300700400c48004041c0c8003803d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 398157832 1250 398156582 398156621
    0xc0206150910080d0c060b040603080f0a1b0807020a170a170c01020a111504052a04020304060e1608030a030b0307050622080d080a1d0d0e09010801 65
    0x14424405100001031100c002d800c0b4003100824040340c01c01c41410000d5169807003130808802032810300c00381c0d1500c50941e0702031403e00205000003003009080c1c0d110b40f419050001d0711145090fa00303c0704940e0b100c80e151600c0d2030804c0d4160602612030020007005009841c860301607642c580d110042c8510305080c5000b5504107100150000b000d040385012400c8801d070000d414140381442c05403c9a002210b4034021641a00d003458440400b440b08030544c0d101c01c1e950b00064a41307501e41c0380d1200030040000070b41c00707140c03982800b41c0032070051101c0e018000604215124034040c60800c008000104400c1618441c0d42c030b001c060016080110015102018040c60805002e10300c01c0d0050020b5840595050050000c00701e42c5407680b8019280a40c1c0d0443d104480c010f1510381c010100380540c0000303e80c1e4021440e100d000503003001c0c1c10b9420002d64000000c140026904c43c5d1184010844400024001c042c241d001c010b03070004856100500407180420541da842c20517600b260414074600c0e0252200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 398159082 1250 398157832 398157871
    0x40f0b07050c0d0b150102073210030204140301060803070210050d0609051503010c0504051903080a0509090c090a050907050702030607080712021e0901020a0606090c1d030c15090301090b09010c0206 87
    0x449d82c42d100d4101281d40100c1d03000000b08002918484401d21000001c0e9001c6420004031040b019500c0a020059008210071414800007a40303d12030070201074000d800c55000184140c0c480c80c105c40034003075098420026240c0310000180a044180c900400f051014625070040d0b15040c8900381d075690940d102c0d036260030324001c1446020f03000d10342da0450030000034200101007001e4000030185940d00d5030308d00360344440c1d02d410001050b03005084090008400d009211031904d80700c500e030303050700e404990a0b4030650b1010003c81e0144901c04000f500b501500e0148440700f504007559601900c0b04d40c0310f4021818100044004a00a42141948211700b840c5840100c21082c0d0080c03041c100107105603241c0320542e4070340c80300f5074000790300c041d40c603540d10f103115025154444010340149401c01c9000846100b5000041c1c1e0b500c100c600aa440b40456001502100d0800310440320890000740003130100d1441d6050280d405034040b20204119420700000501291010449902c145007410307005407100c54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 398160332 1250 398159082 398159129
    0xb010f0516140708030d0504020901080a0305030106030203060d05100c12090f150b09040c05030c01090e151c050307060f0209060d0504030302090d080703090b040f0b07050c0d0b15010207 82
    0x280540090b209015540011801c0413044c07004107070102c000c10022138541004d2050152404050b4441c00907904030070440800a54880c0850741100c940f444c003da203986402e00021701468060314020a01c0c41001130101034007820b9040185000566282c50071107050721a01401990704003100240554080c01030710b40007454144a08020150818001820780345140200b00c143c2403d94080c0d40d43d00020204021a150400500d04c80c0402031070105905031805c80042540d40d0040d1600c1900c202101d9662250744410308051040001001c0300061160241051900c0354401141507600500340400818610441d0085640e1640c0c0035000e03610b0200741030708a00052501500c22000c158003001265155903900028004042c001d6042035503c01a910780135115843c1c90344003011111080c031040000186560700f141c12074428001640c2c0d14102860082d08015281070501e03403010a1a882c8018040a240d89600c510190b01801d0713580c192074001039a0315043c0e80b04441402921100340d0382da81c0f8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 398161582 1250 398160332 398160353
    0x306080c06031f170c03011103061210020a05130503030a14070c09060f09050a06030c1a0d0e060405070812090d020f10030506101403070c0c1205010b010f0516 70
    0x3d58001d1041c140083d10700c1c44000c10198446800b8099400800c403100c00f0602003001c4890045000304034041240c030703504101c0e0100800242c4141e41154000c1c00040d01071000b881c9400c00800f00719603031107607a500500203401c40c156104485a03c1e44011415080010450f00d51159980702c14030380b00d003080003510b0298040c510807210b541d00c1c030600140d0030145000e030f8405000e07503030700003841181480141c0c4100c600040c00c0c505841c0c01c06804001141007002c3c414240c400c241c0c228441d40c5801c59040525100e0300f18860f008901d044003c041c01d540102c0cbe41070050b07200304181d60704940d4a041d055a244c84403400104180420005440c2920300b0220105815102a101000d014134041c00100c41428081b00c6601103500c0d5800c104c030514004203140c1800303c03103084c0710311aa42c1c03071a0600b84500000303000400b4005251400428004002050001044e44a500441a0f041850014040c11380c28188502080b00c0307013142d504150140e8246c80d807444194042008080c61070310b4440111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 398162832 1250 398161582 398161591
    0x907271d0c0d0b061303030801030303050609041211031c0506150a141b01020d06141c060902040212010303050c120a08040f02040b040c050c0d110615040b09090105070e010306080c0603 81
    0x3c003081044503849480171490400940c02038175101c26a6140d41000740aa40009054510800c140400c100009000b41c000098100691901c42005c41a0300b400d58a94400c082c045a030300302503000d4034503020701d81e41c02151180009a680c071080b521546400840c2d80034041c031410100e0004101c603a69079068132301500b4481014485c5002050b8641007003800c90b4001070741f080e1b05980b11b01c0c0600c020407804000c01d041050541d82407890025486004900300e49040c002807080d42c440e02075900303544e280d030150f42d08107294140c01d41803540e407440e0107000340d40f04220102440c0184403161640f50411800e840d8196940e41300c0f81c00603511940e0b01d82c006000d0923003c03680259101c0d403d0303609031a588186401c001198865940c0c1c0c0910b92440d07440e20340740e00d51050400c11a60758680080c07201040998000898851100c008480080020086e000444101c0c1e0031424110400c551541c0c150400c0380208401c2d1210100c4004060044003a41c0d114040c1d800c4039484025643d0040c2481d074011a0300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 398164082 1250 398162832 398162839
    0x203150720030a0201050705040506040e0408091c14011a0f120106141302090a0303111005041a13170706020c07090b09010909110907271d0c0d0b 64
    0x128007002401c110030824100300c21a41c80440c07411101c030380910a0315089451810710505081c070b0940050080d1155004515008407032001003010400d4803030965252a100a10402c0790b60610186460061160a000c4d01d001034000e03c0c12f42508018814042d250036802075090050f5140018442940203810315503030848881c5207103030b90042c2c003803184c4c0010b01b109c0c06000d0707520b00f210001c1100c4001c440075544403203481001000400c0d6190001401103990500348094801c1c82c0c038050380d00380b001403444198001e062000f04030400c07080382060300d813842c2ca800c40c501154881c51111405848142401040c41040c0d650007160903941d200900155441450054504051010280d08084035548004003554541c00994510721344514103074058081c2010030400003445846400c494824021500c0c061040030000c950035600c685d101c640900c05000342e1003030103102441201d9000d400c5100e00c0d64280903880000281649050502d4001c080c00d40410341418440802d001c001e04540b02810f50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 398165332 1250 398164082 398164097
    0x180b120f070e04090b071106011415070501020a030c1d10050c07050a0314010501150c020613050405130605010920130e0106020a120806060d09021302070605041e02031507 75
    0x8066840c0e0141380e065900c10702d140801810160000303030a108043d4040803564001400611000d8103404a01d00800012500000400004046030f132140c0b1860030090000d5000249042d8510b4061308400d4103d051580c0f807420b5103544201500842d11021031081d403201c403a140c0350007640d200324007808884094009460100b1f82da540026410345403544102c50100c4480107501100f0000c0c82000d005186081c00a00086000080245201c00048009101d45004601e0800d81f48079594000050b1001078400c2000742014800e040c0d0a10015a0450760a42024004900d2003614002c1142c1591001440318080038015138404058000128500c15460028000107a10f030b1504a4140284050340190285030181e0401038000c0030001094810300c0605070500c11141c650f4402ca07031045422100014050484e840013960195007103d00110b181e0002c82c1c00424000350b17070320860045e0f104a01030441c4007070364144500203000308440a58150444080000aa14900240c56020445250014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 398166582 1250 398165332 398165357
    0x309050a08010b030c01050a170910061202210a0201051810080a0b0d0b01051002100e1e060c04030213090213020705060f06100302090a03060c180b120f07 68
    0x4114690503071050185079100d20300840f8500b81401081c04a079000c1c64542c0c5450003204014041040e0b51184400044106d400034146207000c0c4000d031901e258100c810f000159032825030301c4100010b49020391203440032240da0003d442502c0d01f90401c0e0914030010b040e0240f1140c0040d101500808900c0d0400c0381c0031a18108695900501d0202030781d6103840d1413041d4208513040d41d04455521941d28001ca044544000c003098110300c03030170b0450304104d491420005100200328142035100c114030100c02d0412540f00046400413501d01902404034101d0781c80031100048880c0d55400a64114495401c200018000350801001c240346070b0f00b9444010400b08007540c042441c01e80030341c80580003141e0204082c0c040000038171005030080d948041e08422414500c0c0042c1162204c0726401c014158006500760b4280c0f40d01c401c0301c00542d00810100103050202402400300c1c2c0000420900300da00c9001701040c0180c400043e641c00341d08407050000d96954100400402c0e6001801000c103000403500480b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 398167832 1250 398166582 398166589
    0x519090c1a0f0d02070b0906060303121302030d0207090f05010e04061112130c060e13020307020f0303010e0405010e0f1005071719050610080f06150a030204050306100e04030804030905 81
    0x20310282d810a80c3c01030ba1020982841c6104117000b0b0325140c45900454284803040d50001b007070b50584130002038a1046c0d616a00360400501c0170b542d2000750540502550114840d8020034001c085500e0340d407081c4852060f468022044950034052200100e1800e004500821810350190382c107100000317422450106802482900c0384803c850384a00c658140c0185400c1069840d0450018029400c050303810220020010304540741464218403d1580880050b840600c2001000c241e0f00ca0074050300d58030b5031200c0c0240303600141124150b5996080483c04030228000042424403200c00d000603240e00303840d8280f130340c001e080c0150444081026205125095425240419000352283d4500306520310200720904240c600042015103d030590004183c149174012440941c0801070540c00200d50381c480c000a0241d01030a2101950a00b021444030b079541d1301580200140d40d002c504444040d0303998803880c50302000030f000381300745001e4203404600064020f0307005c1a00140319003030a0b03410b80d4407040030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 398169082 1250 398167832 398167837
    0x20f060109020301090617030a0c0c09020d022505060109020f1b010b030106051909020d0e0607080103031b030c080d060b0f0d0501230607110307090519090c1a0f 71
    0x1400450b40000100200071941c070903038000388181d18541c8800504180300c580c43c0c0c09103100a0302404241083e4600b080400c03c4110040c1c0384600c0119251080d0404a8009400c442409110310070441540e00806000c48203249807550700c00b004104503800c3c04103407400b0f508620180c0303081e983d0078400901d1866013610060181038039080001101c031592010982900c000e90300c51402205012100307109020b4078400f160990311005005a91098003000b00390003800d40700d0700000d00e8016041401402d80e440100309040341d009559512001d440020805a00d030341d00320340140465966042400040c103040d02900c0800b88160300082c1151381c1c0c03804078070f09500001000111100000f001d540d0040d042c400c05024000c14440c106003041c2c02c0c00070010544003040f82a12845000c1a110100202070000e0b800c00400942541c0c00d02d569900d003400501300503141c443d6a039420280248a402013031045440480d004110903608a1a04004403207241c19030044d403400c1c0400300202c901500c1c00100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 398170332 1250 398169082 398169089
    0x30103020f1309122705060a05090d060606091d0c032205100e12090303090f030a080c0703060b01030b0306040201030c050c030c0d020609070602070b1602030f01060504050a0b011e020f0601 83
    0xc652800c001c00d0821411400017000401790010000f4005100540300c550a440030804241060b594801002c1c0000714909080d00005150500700500822100c0e4401e000d00b003120010070881c000900050340b82024080111400019a401880001d031003290711007403620b00c0b0f007501850009400e16515268103180035807403840c3c00702d921089414220001080161b460105690380390b030800601a000a880c1d00c41c0380c0c4014801d501c18403901c0c180ea0f400707005050045600040096486401e0901c250703c42e000da1005884c1949090f10785c8595501034002c1185240004026185d1a9680d82c011340050a550701807e0400c0402c0c401c060300340704100010440c2c0540d00f4014140303440401002850050014401c8000d034000c0c2d9010455540c0010701710341a102030005094860141c04c60403100e400065030060760521030001c541d6003440303040d0700079419140140c80a110603aa00301079a02a00c14071445640064204540790040c40304031042140140082d00c147c0c3d0741a880101c1c1c003407805600382c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 398171582 1250 398170332 398170337
    0x2070b130b01090902062a030c011b09030803060405040809150702040e030f030403050307180e0405011a031e0319180602060408040608100e13020f06030103020f130912 74
    0x38206091151a089880c0104010f0300c00780000ca00f2a40400e4282c00b075240b0305004840c99000c16120140000d0601d45541701075008c603a1192440c010180c068101e65130700d80c00081200c111000014071691030107041d0303038000c0d524524549034541880001d0800030410f0703a0211051280700b00a80d25505940400e0050407000c603201c7c5e0f03143c010407003110a022000d00316944204009101510ba007420783e6401909030824540303a90f128403040c1e8603800c070f10004907016008a040401d03807000c02d0342448e02560040f002049150860001c800c59030440404103030b4180c2c014101442652400a04902031264003810340381844040011000b40880284030500420202c900b08036054401d41c64000c0107110703c0c4000c0c006400c058841d41d080c0e11460140c070f4208070301180001d42500c0d5204d4000003c01c8410269011860020b17202c21b12071800390340882c4a01d80e1088203245600d072241c1920b042c1c9030010a902c03013914a0704108139800e0107407580e90308000d8039021500d02217502003e41e800c40341e4258 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 398172832 1250 398171582 398171611
    0x307090207051e0a030c031b0606060305090d05041e1a09101803020f010e0a090f0c02030708040605070f060c020a0210020d0f050d0f150f120512070602070b 69
    0xb454500d040807104298403165405a4400c0545054001190f014464160914002a401900781184d040c1d44d0040000c01940c841034592082084903031152044480b03d5908214548940781e1154441468015580000c0c00c248001d000c3c0710707a840c0c0c40340c5000040d0313822800303010b0b541c43c0c18201d03e24032210350b02104031001c40c04d050f0703608001ea000c201000c0e241c80c2880311143ca4001010003442c241c08080e005020b054030509859000300d0300d07901440d400400721001d4035070f02d0080002500b000ca1070b0021050030704500104d07490001003650318080c0d200031424101402d0041c01c4965400c01ca8040d69007495991b07842000c81d11034410340b405800c50354064000320407039006018501c12000102c0c030840d4130040310040d030207a1211102c1a40322040c6000740d0707520440403000020b001102e04c0c00d4a020310301032201d03000c02c0c52503030304104540303100440c21141503581d18181c1c2d40d0329240310301800c2c5800060440c0d0300c01156030b0050407001e200c0c54005050442e1502d48200340d44040310b6049001310031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 398174082 1250 398172832 398172847
    0xb0a03060c1b0c1401030f05040b07030b030c0d08030601091d1f08100b0102160f08160b0301140d080409021b0705010f0311040806130c1d04110f03070902 68
    0x8485190601c4601d03100744490901c1c00d035100b00944059101e50144a00702d03044c800301a03882504401074000c0c20000904c41404c00d0b040c4500b52250039a401000b09250107400d103003605010403294042034005001c00070705034a58903095240c0e413005211324100448414041541c11982041d9140e800e40c40300704903810b1800700301c445049054001284c54500102004100084c3d0001c0c6440d03000001410100d9a03801100042c1d01d0101505540d6210704041c00010038910030064040d000c440c407420444030075409090342215181007d00440500f0901000140080540380c549125103000142001c1300d1106141c075180744540081e004410b0164000070074004148170644851048030341c403009001c9440c688400070742610101c400890600d921404d400c4d9202d113081c41542c000340601001c0d00d510b444c219050365100001c412044034049481100070610700d40e00c441040c0494006112000e090f280c548801300c103d007001240988c40840c901081d05c103914203101901c02441010303c090380304c88a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 398175332 1250 398174082 398174087
    0x31805060412090e010b0d0f060e0a091509121103071203141005100e0a050a24020f071a07050d021c1d011b06090b151e040e010b0a03060c 61
    0x60f00e500414003150440700501161603800c0499503031462101c000100211030101c890003611596008110740c2164008010304400c00b600301c42900303441003070201b000b11200020301c0100c0e802d0b0300c0007400d000e41840e0003203201806603000a400240702e00489081082075503c1c80000c4043d540d01d000000d4036003410401907007194032110b070010505c1d80141c01144c200301c01300c1d151407002c940b01e00401907058041c900c50b4644180381c01c080e20003c1c01070302c2d0040d220701c0000c8040300b442d1401078912008400d000b01c000c1c404500c0e460048844005061598608030300b0351241e030007141100841d104c041210000250342000703100e03900b501580203082490b501c0e0342c440380007000e00c1c0c0e0100d090003a608190804840d404406243c261000d0030031000d15000e030100982403c001c0740c801840e131450500110107001140048500c01e1181403205402c01c40300302c0a10421503117550742c2248030011070000302601c1c03a103600501e041c00e1400300000390184000c00051000142a0300940b0b2103035035110740c51103160303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 398176582 1250 398175332 398175347
    0x10905010c03080c030613020c0604020312040f030b0a0b040504050717150f07020a05150a0b0f0108040b04080c1b10021507031104121a06030601050d0201031805060412 74
    0x2003428507500c00c14460310083c01d540b000800e0401409070001c0010040c2d40c450417000c64910002500315101d9103541d0703206540316010b5030180d00c0b81c800d1748a200c5040e4881805c80d4240d44001400c0201d1034034503907454400e02030280100340c0258070340750881d00780e443d14480c8a01c554014401010724610b4031000c54049005d034600503416800c100c101606008441004980040c1e54050f100c01640c1c81480c220b0610b800140020050f004d6140c3c03401207d241040100d014211504d020000074080c101002090350446224034080b864003c00100440d1507404081d511500800303a5500c2e10b1000d1000398100541d40e0440100c40104051003038080c14801001d5148011070300040104610f40110100c090340700400718001c00da1540480d240900000013518005c054051148404810030302d041c01005180760040501c003401d080000d0303114038000601364100e400107025400b44003040e40045000c1e04a0013803007048501302d0314507180001d5040209500c503a0281060380e80400560000070002c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 398177832 1250 398176582 398176589
    0x4050f10050312071b05030631030801030807150219030506040203010f05060304050a12030f0c020105040314070c03020d11010233150a0b09040e0a080f0f0f0a0903020109 75
    0x95021150320845480b041003200c14954011545c020114507041c42610041243d411841d090b0085000f8060540b8a14500395481222168215510b90104620040070840a10090006840200100041040b00004020351401010400341d402c0d1880100d80581e0b00c290712040c001001c0c06000141107900d4441c0701e42201e0105c406501c0d552419998044c41d4519008183c0b0034072002001c0340400004106406c41c065000e00180c55200c0303042c0010f0300800f4a90210900e0030b04010055905c0780c810300c1124801c5916885003030700340c00c06001c840c6060700312000031981c2c819440d0010000d03a8840c140b25075958414074904000154540009041968550800c0302c01008038044001c800c00010b9200011131869459410641e6101030703041c007407176141e51400d03040203003400c0c0422b00c1080d850080038400b006550a0118050f5242c00998400d1014070103031003024103003e40b001408031803000b4902e00d0020a42c880c1044083d00352496070798003500c454004101c140c0810030441d40c0180a0034000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 398179082 1250 398177832 398177839
    0xa0f0f0f080604080306012d091d0703020a1206090f0b1008010303141902070509070203132606070e090a02040803030a1d1608011b0203120a0b04050f1005 68
    0x50707103071006080c2e031050301a10040660401100144142c0d1080f00c00c20b010b00c1201d03051400340080995091030700c0e5501110742000441200c0f01050000d01c0c01d461428401d085100b100445e903400300e08500a4101c3c0189208010301c0440000000d407943c096a005032a44c6000028524681100002107950248505000700d86a06099644c1904202d9650450b80c260821400b01d440b0030075141a24403501a12072202000c2d03001c10842168006010001d45a0a80b407003a81c54071400016a968092261000940341a0030414820340c3c40201844031003800701040b201680036200040d6051102c100d031040009801b504103103000d40341c11100329030401c000f2041185428240f10303a80d912840010141002d02e03484034a035107a9075441d52040c03402c02c03c0207025900f00c62400c010510070326040c0e1184c0354866082905890b2070450851862a150320030f0340065242c0341c582c1138482003800006010891803540c46100b884541c407280038051080c00701c100d07409010f03d000c1c0b02c21135140c1c2c05900103a00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 398180332 1250 398179082 398179109
    0x307060e01080a0c05040f090507020d0e0321040f080a0501060b0403080304140c0301021b070905150d0618060b13050103021c11030307060c140309030a030c0e0a0f0f 73
    0x403039076008091541c10400c40780000c2001c0c4019242640c0901c11540718001061901da8000351103045039015034000c11981e420f4440040c2e40d07100807650003002d0a989503140c0c001c0b2650003c4290b042c0100c040070500b051065090995404090f20340c3d40c941d80c440e2000b81c00c045c0e10081007000a1107203070080c0c1000d0300c0b210704060554a400340c090000400040041c0030a9001c017000280c100107a45002d00300600941d5203600d008001c00400030b82c81006038440c4540d00b4003050a8955018540c031494460b5000160845540708002c42c2899403542610110b6544c81d8401203840d030950381d1502c040c00743d28007240340e542c0b0005200ca135590000f1080c4003103103040018001651051082213440e01814240d624519850900180c41185882e406505100c0040d004003000240d4104220f6220103448001c0b001940105441003444103c030b040314990000c111070711180740664004010035009252601e002840500800c004000d0303074008007140005e05d0b10412480002d0030984000c3d0440d00510036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 398181582 1250 398180332 398180357
    0x91509050d0302070816030e01030f1a09071b030806102c04020c01050a241a1612080421020709020918010f1d06030a0615050a08030306030706 63
    0x944501c088500c04081540000741c40c001c0c065444191a41c0040c0c0c0d001021000001c0e15001c1c008031500c80c0701030302090034110001c0503036000e0700c15041c2103a5040400003240c1004010403c0220000303001500380100140b2000c0c17910101300000b8040703407194556810303e0030910708000e0300c150810004001c01042100f00c0f80c0407201d503134000c3c001d4011311003080800032a002c0014060302500740c0344c404561030007040100d0320010303420483c0c00c075003503007a04a04940d0000d81e041d0701d441c3c00d004000d9880c07103e540c602108034522000b010100f801980c0c1d14200c0102e561007103402804001200c0008609030248403c0c400d030b800c0c85000d0006810402021100802d070080d450306494883c0f1212a9408a00c1c9007803074645c0400d0501c03070640e0500d540510741e1201d000d0720b0b850710070303014618410440c104401007400ca560700090283c000200209100c140d15541c100180501101541425400307030000240c1d81c50307032100d40010300f020f00d020b1616882c0007801d0524100c801d5121a0800c02030075800c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 398182832 1250 398181582 398181593
    0x9010902011d0f13110f091005030408160203011e240501020a06020d0f0c3f051905190b06161707080f09011205010e07030e0a0b0a091509 61
    0x3e0f1800749003590b498421100c0b00d80001d0041c14012002e40c4011000074400c0c81d20320845000b05400704044410501c405a0220202c505000846005016080c10488411007074080381082c2c000505c001c001141840b0340f110702d0241c0c2c2103812a0b80e50030584581009110b40034400c208601c072004000101c10217858172000030744e1641141c038041d104550006d1074445000040e00440110080004140310700c4940c004d000341000001e85018142e54103c0e1000704000c2d004585169034510b40140c5581d00c9009038001078000d25003d85542106030120094036901e55243c05083c2c130483c421585017403602d000d580444256004410003620a0300101b04040c03000c0119043d5407a2160046400100c05408260221203880f41200280190902007110301c60a50050018032505a003070742e5403224071180d0030031320040c1c4000b1700504482e203107402c001490f218429444000081e581c0c400f02c884c581015100d0042d03a200a48a001039143c5400868003481000d03500a0030024290004010011150300c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 398184082 1250 398182832 398182849
    0x212061e010c0203010603020909030a0f03020f04050f010c05060109051021030c0c0806010320040203090c1c0f0506011502120a08132003010b0103060b0f09011709010902011d 77
    0x541440740070100b036000d54609600c100003669000d40f2414550038044804c0e582c903002851000c0c00500c88144d031211031840f900903241e032a9580325205042c076042a0800840000d680034460400ca00c4c05007140205404025540c005e20031403034005594100258a0201134120360404450030001d03c0c0c4c1c6951589600003507100d4640c151a101d00700400d189414169800c06030f00104c0345200da200084244442050084135038400600c229105280b0001488103900046030034885580140c0c40d0641c850418148031001841d0040700001655100d84e640c400030800c001c0103544075070140300103010040c0c41301c2102d8808841400101101852407030703903500f140f040201040410001c100071640309100f1900e07144881d0303800284408101104411102a025503072031b11442903003040a4508154040d1146c941980c80010405291040b41c0442102c0796002d803519a04003e940e82d0400c2409600349030450050700380c40004100a507150000402030300c0e40c400c0820044540064031040c55464224 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 398185332 1250 398184082 398184139
    0x1a03011205010e0f010c0215131b0b0f1b06010b0d0b01090b030f0417131716030305041a121603110a0c02010206010902030709050d0f020310021206 65
    0x40c4a014084600d49540984254001da40c16446a010301044142c019004245170200f15802c0300d51022500c0c401c62042102a40c1ca40500242506c02c540442d003051421949400b4180302500219910b00c0c560081d98021003900c1a00400402d01582c840f02c0b0348400c00c0c804200c00c1c0146025414202140d580d8801c007240452041d503243c1c00c00c00980d00441c041c1c1c009203002c1c100186c681c9403142141d15400011103048800e0701c015280e03054210315900980b9a002c000000710b04005040080300384006840380304001c1548030365884184011001309154000e140b00760f4805803546c2c41c10f01a10782044a100000e4507260082c0891401c0400422525034400040c0081103032414900f03009400030f2500000300e683da10300c0080c00c844107a401c15a400c075158400c0c0e00700c558981c3c4c2c0707484541c100d02090f540c400001ea101c44042100d07262032040701c19854090081c0700a040342d03990009240c400080b5542c0800b0381c0214000f0910b4402080455111405403400c000c180c030030b0340c80701a01c44424070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 398186582 1250 398185332 398185349
    0xe03030106080c13050904111903321e100e030901030507120905010515010804050d2706030c0f050901020c040f060e040803010302090c1303020f0402070813030302071a0301 76
    0xa203000c44921300b48070740300180380280030141d40b4207080c2802c1c540190181080c2e8054940300c450300d43c100da0310541c04003c0f6500001d44101c90034000103541003c000180c05165554140384100240c16001d008421044040b0340c404501c0c2c404610352217040c100744550400d00b261900d10401840800802140c0c0d5900c000d11700003030155644042038030b901c540000f0300c0398854680a688020064158001f6001d410300e904680080b24598004640d00d04080314000e0103a00f00c891846903960091407513042d001d15541050861209807280c1503c2a8038a5000d200007030f80342d080c4404859007050015010021078a405441e0001030350010355110b020341d0401340910b54030481c2200401c030690000002e400c011202c1030003804d00341800422a002800300340e1190324503201042e40c40c5904011100081c417050701d080e01ca1352950f000c09c07107a01d51440398113030080c0e001c00100c000604900c00400e000c44201f25090302041c01c505000b0b00c0c0105c9034200e606003074401e40b16100b050300760300c0980b41107a1800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 398187832 1250 398186582 398186587
    0xa050709051f1203050318101d070609230d030f0318081801021c08010e07090312030203090c0d0515010915140a08030f120f06090402131506120e03030106080c 70
    0x1003003803c0c5a01507d0040045401404802c2004035851303000003480c000e114142a51a42d900c01c0354544451180c41a000410883c80d0100b042c0f070a454000c1e4000d4034203c0a990080c3e120030042902c41d08640c1d0300701c00040002d41000781c441d4151213040e41c0d81c1030580102c04001243e64941c5000d20980d544181d030446e03042c4408105a10030010100d40301504280402a00f150240203080c00101b800707000884d1100e1000201902d00ca201514105c1e42c01c01d0b0080310b44030403004160000d6102411001490107a8030400505403158000000018401c50052521400b20a017207000d07842e041c0c0104c000f05081c1001410405105510481540c40c285840d03119104004002045031301d00d540300399101e02011401c0c140200d074103c05040c0320000e0045840e002e55a04500d0340268004961980c2d0128048000c01c0160a04080d0401c80044111000607102e540c0100403070325094603400b010000701280c000c02801c56250142d5041d40f5000d03170007541107504285016201d03610007070200c400c07003001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 398189082 1250 398187832 398187841
    0x90c120c1d1311130303080a0e0304030f03020a020a030b07030f0c0815010905030d030e0d11030d020d02090909030901110307020d0b0702120409092f0f030a050709051f12030503 78
    0x543c0078000c414080d00700d43c2d40e150b056100310410020540f10580c0420000301c005138620405028200d032000040c0e002c1d5240c03e04683d01e0a80100c990101a011480342d5110f05005071140d020080c0030314011112070f440c51070300c010300909840d10114240706607810040c05203001604039060344c0c1c015000c0600001e518441e2801221410916031086525100707034a50114401c2d016400140203915103001d58030f507030320020801d4540d61030390101074038968001c00c500007800300f941d130240440c8500248054504800f810000b80050819511004582c000182e011140d40c0c110700c0801040800c000a94181051600010000c00e184280070f03040c041114006102c0031301c00d00664841d5144c1b11422603c59864420039001088612021600c0d0f25085612083d501c14000420745401d003140c4d030400c01c0c940d00506200c0b01010040605406104144440700001c509000501c0079001c0050005031500d49600306a99005801408200c004070301c00040c008000507060350014160942040ba40e00d03100c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 398190332 1250 398189082 398189119
    0x11d0903130b0c0a08030a140f040807060c091d0108070f050609040f020906030708010302310c200105100902070807060c0512070507060f0c02071e090c120c1d 70
    0x104e81c03070040c50040d000041000d14003075640114604d4140d400703008107c0e5112915244042816540500ba00b007003840341d100001c20a03080707206d4511044c42c0840386260703201c85905007045007010300715079803101e48014400303241d042069200030452800c00202d240c1c0703010041050b92068801c0741d40956111401c0502c00c10f015011030740131100c083d013202c1e030324541003100410386142800201e100e406040140110006101e8000c0ca20500128454100000d0500c01e00c0007803145240d10018032104004000300301c4140c140060340d203402d00e4004121480c0443c18004400200d400001d580340c07050000402040038074080d203c0003540241c001404100049080d40c6e180200802085442d03405810084840d5010001c3d00807188242002d01010007a441d500f01034404010f11070f030050340319803030801080410040065002503002c6205840e01e45401c01d40007682d00d00b060b070034007003103880b174020310035981c40d1003400200f2a051401e95035611402d0403038031400101c441620310441460b200d4480141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 398191582 1250 398190332 398190343
    0xf16050106030f0c0602120a080721060602031b010606020304051309080d06091802030d0e12060f0106021606050901052203051014040b0105060309100203011d0903130b0c 75
    0x107800c2045101c20070918900f104d0090514004c180041c002c4180c1703003042a002200355141640c0c55142d00140e03079500c5500b1100a40030400108001581003030600c15031304244104006813441e6805559075914860710ba203004407030306c55149a660324024041101640c0441650292303101210051040d5031000a888081c0a6010002d0041d05000462442c486014ed2000301141c0c02e0340001d000000c0c0030840d03441c8006a040029405410100724102d01c0340c03040c90002810203000300303003080d17482ca41c0d50301500d044001c03140c40094030072001c014449a40c040001c01d800688070b1883c80031003420720800401130300444100c107041c4003021909181190340c901000074030340301c0c005443c83d65a5803070030503d5072001d4203007041025500d087d80c5102d0701c00a24008520031500300d10041907071b91030041403100d00ea000078070f00003483c02050300c1114444035900040d802404080d00f141c0030500d428602103401c200180c1202c0302070b4000c002001901c1051158101240c1641080ea91228102d030307181ca0904 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 398192832 1250 398191582 398191589
    0xd0e060301060f0c21080117060103150e01062903090d0302070206070f03021f0e0c13091b05031006060f0c02060d060303081b070b0f06030111040306020a080c0f16050106 75
    0x10491740c08405c800380d103002ca400e480d42100d55580c4100e6644d805081550101c40d01400405400600060001c2a812102c60403e001c85200000d840e0101102081c212540da81003a84040e20484d0b010b1820743c030b90501000011102610b0307030720354205815030640e100342881424060640106480095644d000c05540300240c00000c40600b100756494020349420280c6042c040322200046010300c119030034415003c80d01000c0e001084102d400300100b00d607034035800031000003580d02e4041e040c000a0212518056604540000d114024148000c040c140268540c0d14001503161620422180354407145500c1c0d1001581401d941c582d26600114110344601442929900e003007a9000041643c420a4244030b201c01000140311400d280407038030760341d106a80000c4e10304404100030404034201c89103a19041000103000140b0010f00c40080380031a046640f056944690100c0c02092403504100c05640c4483c00c40022480e08450071002d07039490143d8040324004240e41034410341042030075845074000c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 398194082 1250 398192832 398192843
    0x40509060a0b061902061803040f03020d1403040b072001090b0a09031202030403020f0a03022206030506011d060f03120d060807090b1e01090b0a050702040f06080d0e060301060f0c 79
    0x209100307008041c2d0389020968070b483d03040d8030455104c04108004026181034505612401c0ac0043c40d540822407002e0420030300303840c13a100c0045042d4ad40002000148010043344009541f01e0659041c076494801a400445403500c4c0320890301041e070380c0e1001e03000c1e056900e0741c04c0c01da0b211001807004a45180c001d07000100011074021100318815000005082101e1084803121141d041e01c03014411040000d10000790407034850a03011401c019031160048180000c5680001c5040d0380e5118107141020a80c4108011055415032010041d00780404d682c0c0030800740d60500704082d107000881c2d611030304a440e104825502003090601c04020780c2129008108010481d0001500d5403c1d0328014041045800d1044c4513011152200326610f409075406450161a00c02441d854202c4810711365006802500070031404002c040300680d5a8803031400c68aa81200005034207082800a80c42c014224105109204040c0085400c07076480e1811281075a42c0e07480c0003a100f40140b030064502d4540310100900c4c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 398195332 1250 398194082 398194117
    0x4021f0e030a0c050f1e010f021c0810080a0506010e090f01060b0901110d02060604150302100c060506060711190b041d07030e15060f0604030b060906040509060a0b06 73
    0x6001e0040040f034141e91080740d814007800548410084410034040e100044401000000103c0b98080c3e10318000703603004c1c0c4c0103072110011410140c40000d40218036080200d46808240f0011854180b03181010b440341e14000c0281e5072949e100c3d980d56402c1445442e89040c8440e0010701900000d02c68845143c16645c020b10425884290500003508400c4007140016900c0c0301c29010603a0015048403900b21580203000180c582a080c030002d00310080502c3d084c03521071900080141c0320091040e040c80c0d481d544640d80c3c9111803401ba402c3c1c0380c0181c0094418074040c024000840d401c9074480021520484402e0001d50714044200740c050440d42c0030032a04040441c0014154101d652402e066080488960040b903aa0701c0c0258100c8810340300d455480c0d803002da444062901071128150704000c0062140c1002003010340052a9584541c01c2114009801018007040d410030104a076040351044805001501c1c10b683e803030742d407031800920400e185511899403e00c251100303000c0300d43da040c4500074400e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 398196582 1250 398195332 398195353
    0x612030e0f01200a150212070c530f0304060e0f03070b010609060f03050a0b100309060515090f1008010920030c060d0e030d0c03200304021f0e03 64
    0x13610b444080c00300b03590120500324040510354140c801c5070700c4400840c20941d40f83d1aa0341d0308486007445e4100448401c25100e64484c0e00010016402c5000c3c011000d0705404022000e410009402040300c08480b017500c40b4030000781c08100c0c44c0503100d0110403070350415201c2e911410820007515000303c1810041c005d403105585402001710080003824028001c0740f074140d23039070002102c9030384561042500043e041450815407034443d410168101003130520204042c8508400550030700c0c2076203e100701003a0b07101801010000e9902510340c4c0107a406400041100500000c80d000348030040c494103413a06842c000580311804043c030700d806004800d0003044220450b15151424860454001840410b09204000d41d8540003400300d00241c80a0991030030801c014561801411250b4402c501c64001406090300c048445c0c03040070340c51291554041107c60240d0840c007512000350a0034044a1400c00c100805612071410b801c850319042c1801c46c0c00d0103c445000c0b5403200004400c19414002c1e018803d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 398197832 1250 398196582 398196647
    0x2040608100b0a090b0304230303190203010b0f130f1202042910140706060f05031c050a12021801021b0310090201020304030c0305100612030e0f01 65
    0xc034071984a0031400c50340292150030303000643c06142028400542c1c000424480018600d010715006403044101c1007040d058028511600f00040f40311174081e5001000300100081410040481c182500b00d04624550414410300840d00c58251100100350001580d9401040340d40304c52001043c00400501c00f4640f00c40340b480000c1c0c142e1a0a89c130481c2440440c519100c4121103040c2c1d0307198004c07800c1c00311109800502c02c40071031504800c0c09001c2c0030b111111220060800600c0301922030500014035030705101e0041e60401d01038012502a0740100300170300d441040c4450314400040e1504025881c0d403100c22044680000a0650144a60002ca516004090307141c001000e60903090302507a003014504100d003105042c11084180d0306502080201c03810001d02e83c001c0380500c2c010310640f40b406440341c4580d159a00240d0003103c040d44880c000703507000002c9100c2c400190805c0f80348001c4910740750320f00400459502c006140724501061031980d05a000b9480c02c5005001c00d004605400101700c4074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 398199082 1250 398197832 398197847
    0xa0c1e02071701050105010306060e090a0e0f0d0203030604060906060c03050706110a0f1e05040308090607021c1208070906030e0c130b0102010f09050616030905060a1b0906020c0d0213020406 84
    0x141b5000c80d04022000c03540c0d50107040864421880a8100d040542c2c4400d1614080d226180d1058441e00882c0c2d069004840184041100b801e056001156642442c3c4203000c21580154412801c1034580385046c809683d105c480142490b4042c608582c03a00f8079030400704c0051405240c402c1c0c5545000454039a1290080794032a0764880036162480d4508006a0325181400f000e02041c00290302000305000060382e4a0181c2b01003e0003410300c03030800d0965404903e048005601c054002e44440341d02c40f040161184590f030403da010300e468001420841806020f003003039400f54000303040c0c8030700c54501079400c01c10429281c0d2200070404c00311040c00d04108002031126a03c901d0041d42418006002a2014003414021660007801003072950784020503261111050002d0b072003055111010034020a03400c106050107100c3c010000910341c0003e164215480e043e100001040c40700c10b80c2d0800c1a180c01107105c134801e4a082e01c4070801100548000b07803002c0c000760028100a44081000f054883e4481003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 398200332 1250 398199082 398199089
    0x60e070305150303251a040516080c0d03021c03020a1403010b0d0507020307080c010c0f17010e06121605100c080d11090301230a0c1e020717010501 65
    0xc040149403141e00d240350a0340700741c900c50360b01a8000c00a40e200f000d81c10407028041100c464002110303641c0c583c0c030000d1050b2403c001c803050044000c180310510209001e0280d20300100c90008042c20305e0303e880c41e0f0311001111384103803040e000d42e0424014035000b031080c840c2500c0d12600e03101040205047c0940250041d03210000010045d01c0e2640400e14600c0850b07050f594144c40a070306080007210500c01426006050320110301040c4074044c00250518007500141501400102d461080f1080c0106270360070000030740082140c200c40000e910752440085505484580b1054240c580d603000104800c4220244440101d1181940c070f80c1011041e01c0c2290f054440464640040303942c1140111a0074058420217048540701b000100c1d00c040c41540b00d180a400b80c2b012490030302d82000b00090840d400c07200c41a02d03155029015002007840b550410ba48214000030070001c265000340020722034602e86551130f402d581001c17100c180c481e000300840b0b0018400400b00c0c0f4225051080e4083c0030380b0f003e10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 398201438 1106 398200332 398200337
    0xe061f06020309064b07020d11060f071118010302090c03190906050910151406070b010303020a031b110d030e03010e07030b1503060402010c0305040504060e07 70
    0x50f103580900310b0340f0040d03103181c17462001442030740d03c4080c0f0440b10020401c16100181d603100b00050143c0d40000902103201030f01030114541d8814a00a01440040865200c0070844141c1110b0780c0c04009540b0300c4130780325410701080a607007002c1c000258009844000103015a644030043c544c090084010191500c4441400c582202c20320750040d241241c50301e00b04230030f00408000141c034015000320100010b00d4195000102c564040c001d01c1968289040e55185035503c0358252140366807c00301c80149540d4914020350380b00401c060450200d51105412040c0c4030b52a0030744000035401100c450135098084040044491880c00214148000c94000902c00c1e00e00740704034000e0002401c014040c890460400c50750020340142494035141110150900ca40c401044d60f9400650a0034445091005854103549038001da41010b0340080c60990000f4824040710380c1540a001e042c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 398021582 398201438 := by
  have h0 := BRFrame.cov_init 398021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 398021582 ≤ n) (h2 : n < 398201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
