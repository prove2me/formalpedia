-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3203
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:58:30.482703+00:00
-- url     : https://prove2.me/submissions/59d2ae04-46e0-4ef0-ac7c-4948b5c7b243

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 575899280 ≤ n < 576079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 575900530 1250 575899280 575899283
    0x8090f06090307121502030708060907030f0c21051e0a110408030702190522060f031a0a090c0504020a0e03160501091401090608100504020a03230121 66
    0x5040c07070400a040040d0401c9003541102e00b0718400e85000d04280402d8040105000700f6441c811407460412800140c012000204058407402202002441041c4a030304161750144144200f4400c5164030b40c809007440b1521101402d400c581410ba032074a4101b18001d09000320030090118500409440c2001030798080144400780311910b682d000c1d0301003409203004000030302e0150041c0d074440c02d40c0c0c410043d0501719000301c039000b418404001d0040e6070754040750122540e009528a4020480d1503000070203040281d101c1c01c040c40329403000109201c10700341144201c54480c40004082e40e5080704d038400711440550007806041082805200d281010b5004140307240081c20309608200c0d040340001e00c0c29406400000022480c04810080c030750f04030910700e02178100300200d0340c41c940380000001c111484500c00c80741040244804601003100d005400c0c0c01812003d40155600c2d240460050045c048a03d0001580240c0c01c60007001c1a0160055906955200c10051038505140c0d00070440740442900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 575901780 1250 575900530 575900539
    0x90b241207090b0d0203012c01050f0102011b0917010c0c020f03010f09150b03120f0313050f01060f05100e10020c041415010c03020c010c03171e010b0708090f 70
    0x4001c2000d218800140a50850078040507a50390305100b48503080059a003038422302000039243c0c1010344081010b400c0e0650b9419602d08003610a2040100e000d00600550f03010028054400320030050703130120451040d41c100140d15410703454151641401c890104010500060300031052030011b00e0304101000601c040200046142c07040c0040003c1102d02140d4104d5040032a084010300744139240c050a2a401c2c6c01310054041402e01c891002810b00c191090701919400c004009030004014085810006030840104ca10141c800303451503008000e107020f1040110302500001a45203410003171184040d140d9642c07001001801c20501088412503603805055010380804643c1507203e51046100d0680d2082d4a0070450808000e0581c03000c900c51801410000c0e40802200826000144126402000c3c6801140e882403810120380441892a5072418429410140455602808510080812401c00e03501c0c40741d0761100b4055a078070a5000041007481d051260f8151458840140c0248540151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 575903030 1250 575901780 575901797
    0x70303020c01050a0510210209090f0601090b01020705101b03021c030209040605060708031501050d380a0902030a02070206040b0c070504182406090b241207 69
    0x9549420f50b40111030405159940c1c408100703043d004416140010b142c55035840e00a094140e4500c4000034080300c010780102e1003600425500001005240c00011580c2c040d12140c1d41c450b00740340040c141040300540148121000440c291400ca00b480060401580700c9542800380c91240074425541c1c43c4050341075010b10350842c0c22002c0d0742078030b5512010043c0d0780143d0341d445840c2000103c1d144c0341c0200d80150400c0c040140001c0380710088a030000c4a400c5420049158180121920300c00d04110040c298180541e0407a1550700000120701200b41c100203c0c0d0014546010a401c03000900e1850350040c00e14404000030131030382d8001d40d045940d1210141c030f0110b00d40c01041860b402503002c54143d0030009440c01d4221400e100311320241104540610807062540010008082d20180c06001c200310b42010850190000444800001c0191400d00945d5590100100201800032106000340303040554491045814120500c0c203c000030140e07414010310b50a8080e0310361009215070103100000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 575904280 1250 575903030 575903047
    0x201081003171c0501050f130207050d260f06190506070b011d090703020402091c0602130501030b06041403121903060506131e0918121e0507030302 65
    0x10007100c0c0b282450402003503031a031524184000c20752000c24402056460440103100941c2c400341813507006a800c68006c003d200707038006428020300c00d0002c000d14030711400011811058000035101300c0c1c00340381c600d41b242650712200110842c510488403185501610f0001401078580800213440800c10319001d031202d03a071140c0109071140c0c00f07040c0640b06454900f004000601501d01000e003081680140d025083c106403402680d80d40791404021701c915008030304686641c60328054142d0385240d50360505480806420080001d5000c98039160040b092200d02050130b5000303010f43e0f003030040003500140c0340619000c401455513142c0c0d684568507000c0c44245c001c420004c00041e122496280145101491b21a400170301102c0040d03200c50300501e414000c0380101c0c4002c4000504032094001041030721082c445522038240900d0f006005020f281010b1703002030610110059200724880c40700c0380e12101d0707039030016210354000341c044520480184510001c0d062141005d803100307501c40c0c1805420003409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 575905530 1250 575904280 575904293
    0x11010305090111040905091c02030d021e1810051218071710050f010303021c18030f050c0f060304060902150c0a031e1211070218070306090c05070201081003 69
    0xc2d404041250740790710510500c403505228080820600004401c2c01446181009e510383c0100720140a040c1d50125041c940741b0f0341c007040140484408070302603a890940070b01400b85070514005417400b030352400d0000a003c40c05241200c4031201c926032403480aa6905500110384070700e0101944036800307496400644104001e0000b020740510704007030124850319104071000ca44005003e408460304240041012039004151152207081e1170b180d100c07040030816000c0d10603440440c2248030b0300e141000000103000c0c1c80d01222102c03501c070b0800d40c1da0100da06030800c103810101041300342d8410713820404140052900e0b4003114515202501081e8590104140c04415030400d150850076908401c000100309584003031035601d2510355112030000c00f030001d04000d0107820307869030044802d41d444401b411200300301c8003507a204503070081c000c0b14601c00d458200038089009654140c0842e0a200000c141c8000c0e50194407101c075a2950342c20f04154a64004440b0a5000392030055455240b03800480401c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 575906780 1250 575905530 575905537
    0x207080408011d0c03010b0105090108180601060c0b0903090f0904060906050f090f1606030b030a02040617120f070201210905030417070305061305070b0a12110711010305090111 78
    0x41c1d0f803424090650515541d8107041025030018440c0e40340903880707401aa0001c0075030b0300344002881e2040300ea9541c003402d40500c0c008080020b2513841002e0000981a6000e105d101030f252042c0e0190140d521082c031b0403075490160f2003070641c0c407080032105141709050220031980d00a00400002c031300181107841c1e9904a5100b9903242401110a00420503003090030003444400c604013030014400c130400c210700c8040f285501d004c1d820415494090740b40d103d660811103002410740040007000590395990f043e1000895a4002407050302800b100e070704031300c8186000c2e6800441846581707807502545600448803000440c00c0d40c030344904103c86045404001740306d80105507200e0001940c0e581d0030540c4482000b600310801207150392103881e041c00028004640320f90882000d62100d15890011f14040d4180042a0009003481001082c2001d00c03583c04243d0a803020070004081005806142c03400840344a0145c014108400c1d018009446501c25800b06a01144a00c00010102c9030321204603e00d51 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 575908030 1250 575906780 575906801
    0x1113703020705030f13060806030a170c01060b0d0203150306090d12060902122e0e0702030f07060501050a0f031e081b010204030c1710050402211e0f0709020708040801 74
    0x1b000c1e50b03005e00c001c9802a400d540c101c0301c214024488140c2d90f80c1c80a80d20480700c84050380301003011802d82a601025000440030344a84140703ea2a40014014500203400403104554280003030503450100c0e00340401c805000c0c990aa0190030070005844069071410038080b404074416a072081d00050b03000d01c9102510130820803c024030707454289050446410500c1e9981c40102030a940300110f4020744224011045944510780d044a41d80c404200741d082d8040c008190310b0059002030b28500f08202d83e8480b80c181c0303400f00e41000c038082d203902000c45000c1c8280001800784109140e001d100300e8103080d103015150321540c041c514258030742d07524a015a00400c032014035030b90003003020f10403c501d107545034001d8025a2a10002e121081c18009c0e42e030851101d2642c4015600c402003170075034464203d500e5800000e000d0140f00c014010002e2650340105005580905110424418180728007062210200c410b0000411200b800c0c004040020b5002000407103400000304800107000100303000d01e00c60310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 575909280 1250 575908030 575908057
    0xe010602060f091209012601031407080d301a03011a0603070c030c1b062c060901181202030d033b01113703020705030f 53
    0x3070800d00e01542a141014002c4240c0c1d420103040380040c0e84d41c09054400d9804246008001e842d10017400d034404a10203403038910750b0403104002206102c0c00040f450501054070080f50341d0140c0e108507080c0c40740b982801c4130000903403500c880000d881141c520361036024076102d100905110700442c042c003241c0b18a40d0103010550021005180751500384103040d010700205060754001c0c0030400005907d440000c2c80b041c184540c2015402c241031148000002650303100403420520382e401101038520381c113548070380400107100b184a4012040d407141420b840501400200700c0d0000040200700c40b40e040035281504000c403900940e21002ca0b4044580c0040011024180007800e00e40140350510680030242c60070f05091400000801400584032144c40c40d2907a41a1120744034140078041c01441d400e420b185660030005840d00d614554001803c00d08015080303880214800d044041130b0b4100300810070308210000c114800c0050103900142003181c8140b065900e04010300501d1485500183c01c1e00146 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 575910530 1250 575909280 575909293
    0x3020703112409161401210f200304060e031e030609072c03030d1802010f1d0d0201110102070b06091513051005030d080a1401080d0e060405040c11060f010302060d05100e010602 78
    0x1640c41c10304c030f2a0560182000d000080f824424800302712844043c1c0300030821540c401c40c4203807001f414400d8030540090003102d020010f00d1014004000d81058032154420707840750b00440e190340d020768170f8070500c039001d1008881c00c43c00c09154842204a10200e90342c041c00100408648040c02d4400c6082c0610724960001c25a070341c41c00018100c040701580142440300c99004000390001e079110b1012403c0301202c10341d81109407880125004015641907940c076600100d11801005050020320384501419910104d05540b4003030345540500c04847c1180d0003201c080c0c03003442805d8140c1c1000381c0c07010b0000549040300d40d581011034540342e10149403000048510080c86000c40b41e5014019100441d03000c0c103445541800c24240d110901042910f0a101050541c4c00482e11510107990040a00420411031036503107501c0070b0301c906a041c0c80502c0324040e290004207035076054900c1c00c0c1a250003604036424448510300703000003490040c1010a5042d001200000d0640e080c3c03455031301902c15640039240c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 575911780 1250 575910530 575910551
    0xf030501051e040506010e0c0d0c080708070906050a0302031005030319031407090605090102011d01020a02010608030a020604031d031209090709150302070311240916140121 76
    0x150704a0000100b4088802c01003480042100000c1c1c0c54155901c2d142010515158200803140354802c08002c4614981050f184080300394000180500c140c403036480b20440c80d62040d90440300300b0a2801541d000c82d80a2007062450382c42a07000e0759101041100c0000c1503911100040c0c41c3d500250300c0321038420064540d0b00782003a4180035140a946d250384e8038041908200c08098505040c0d4025501005004114250668400d4101040791007001540306200340c20708803941c0c041e5120b940c2c0310f00590b080210004080034008112541070082d58085c003165212a50f0440380c40741c03a051403284080e0140790101895905100480e46c01c0007080340316079101c0101c0c09122001d14004c0c948000d12400f42004c111000702c03186500f01c0312019103030060751071010780303029500b840c000880070070b040c4540c1e25180c40680500026000b81c840031000b4001a030780320f403189a9070b00005440f038074080600840801c001c0a03242040300340c0d8001410400758040c0301030007406240c41c1d1828005509030f140c3d4608038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 575913030 1250 575911780 575911801
    0xc0f090d0f15110a12090609030801060e0d0c1a0c030307050720030604120c242f1305040507030b13060302030a1509080c0604030816020c04150f03050105 68
    0x40345860b1440c402c0c00f42d440c0c070009845180c010f88003403c081c00180030f000c00c54804690711940f809035205808001c0c81041e0b040c004d0144009020b00750103e90301888200d0185880511b00020350380c041d102d052002e0900a404030030310165942c45940740d40c240040c0ea404181400614403681d030b05c1d03480c5038690b420341c03c0420381c5160540000c1814801c0480d4000d5545020640c154483e810941e014044002e02c3c008070b80120100401a0140c50f800600d010140c0c484031440d000c2d0340c4c0090301480400c0b980040764006102c4000501000c085c071040318003071100a180505541541d01c00c0070070300659504041000e81c0e02c1126820300088d40d585451910b460140c12680c0c4841556000f0001d4a0543d40441d564400c0c400020709401220411641041c0c11a004003003015841019942c444202413501561520241d5084010078040300004808040181c1c503a260186154000d141082c041d030240070060150b1013000603401e990440105800a080030540000c5119100009039031030040c2404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 575914280 1250 575913030 575913053
    0x7030203090a0b120703201c05060603091b04390f020a030503091c0c050d0c120c170f0a030506030105060f12070909030512070f05030c0f090d0f 64
    0x940f4100c6003803103d001201d018400c601d5210794681000240b180c001c1c42c079030781c0d0402042c4a05021b01c0e00095801020078101c4d01110110700c41c0300702030080e43c86100800000e80003c80f49122aa48800217403001100c3d01c00d82103203d0b101c06040005c0640000900b48820b9425104d03203e066208100f80d10584900e0382150a8001054a0441c10020140c2c000035111200720740040d04024010001c10407190062000300039000c0424000d83d0440705c2c03184060002102c0c60307819501e90284000c07052046000b1a03400082d55440350745810280031442045c0c2d08a8400c04055805001c00842080e80f6102c0c507005080000000b005103448202152008094071740040036a8001d0f41000180412030311020741c00c100f20300c42181d40000c00c14440d0611460040d940c1e126004c0303203040100500c1416081401084004124001c2110720360321004103071034840341681d20000081c0100005002031100c5030282c404c40d0906803401e45004122030014480c00750380c21059400b20840c1c0c200c4000c2206032200f4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 575915530 1250 575914280 575914289
    0x902042c06010e0c0702130606082e05010309080c0105010e10080f06061c060609150b0703021e010908030117061f0909060f0509011a010c020a03020d03050f07030203090a 75
    0x4201543c1032a150001a010261107a800100003294040c115900d0881c038071010640100c00700485507a0701c5004114220540b009a0350003014801240303050b0031034428210805540c1c0c5c201c0000d0385410011401014061026103074010706200c2340d13100c40b00c280580d6008003d524207100362800c1001c040c22103122150310002c1c65a002d03c2e40310644034804035106a11440480f4040011507000312a501e5090462400038165450508003080c0c022443d4006020707881030320454100e080c3c603142c0b84000d0b841940c9000d009640070810050050b141881d2050380081e00714000705501c40c0b00c0d42c4401442d0000c1c0c1149104440b5540c0340481144c0c20441181c2c0a4015001c4100c00b00c101065009810002e000b18141241c0b00c058803020f020f00c0e0342003081d1044044c04100494901851040d008211610500d00c000480c609a20707102d602c030f11507140d40030760014040f10003580b4560800030203600744070f0101c0600c0800e215440b0320011400140240e0340c0290051940d40d0342c210100200406c8a800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 575916780 1250 575915530 575915533
    0xc02030403030822140a050c0607020d0209150402040e09010c02010c0f11011b020a03082d18061008120301060c06051503030c010c030f09050c10030902042c 69
    0x400c10110390b20005441d00144290200380100408020440ba000c104c14005000318020f048010503010000598a840b03a0145041e00d00c0800c0d41000c2024510a0407001f0754011a4141c443c03000d0302c0d1280302c55401ca054014100c2e00c5d5a440004102640c001381e00c400c0c28004090100041d925080c0a40202c5803260302c0208901c0e528441c01400321318581c100f503010842c030003980c023040b15030950100d45e451110705c50080d040c040c1c07400300a40c0c0300078924040f00086c852001045030701c10500500340703100c1244051001e071503540301d0039504045401061007200b84034060002c0b12407541270125034007070304903004a000700754286148c00d4a80048541401da0b542130030001080300c80d621242408071550b1280700410103444040307010848007062540141c1c1800005900c003034480c4154024040241582c07024011907850025174021500388440203040c039003001907941c101e4a0000c00d2a5140e1100f800c0020320f4200382e802180842e00150040003200b04080540d0000100e45004070a21226070310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 575918030 1250 575916780 575916787
    0x2040905011a0412062405180712020c01020f03010e01030b07020606091306150905072a11011202040909021224090f0609031210030c050f040612030309060c0203 71
    0x4403101c1d440c0f060f80700d030461541d14030040781c003002070a8028100d074001c41e94071500e462992102840044440f8030070684159071010301ca085c20403541194500c90081070b10b4220100c1201c48031100a523110f13055411181d5400c00c12800c2c81c18148000d10f0182c00b0b01c6d150001590304614180d50840300250520065500c024204611039443d11003442e802040c440c0588841c0189140c410040c2204901e507500076082840c01142c60340c4a5406940b1803415550303034016031442c40c0c45416031242026440d100d8105808103100100c0c558000d85c000207441031501505001241100d441260026004941d0703154446540005620341a011001d0308201c1c00702404810741c006035012450103140d201440700064403030003c0c0c0941c40071701c1140440414482900c2591400003d503584a0b8000c0c83c0381d0103105415008151264194444001502e600c440c0300d80001e0304280030001908a00c07001d503944a030326081c000c14038642c00076040ba01035219440104501c4480d242c0041560040c802c2c240c215031060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 575919280 1250 575918030 575918069
    0xb010908030408030702010c150e0a020f010e150310150201020403060c030624050409140105100c0b15030316060f0606080c0405060c10020406020604030e0603072a0203100204090501 80
    0x44100c450555090808c0301d005000b5140c000030720034001d41000083c0b403401c0058071035218080b51b000c50681c8200d40c8c00342c078111900015500c14125088290708481d040c201d18401551400045070040000415a810980e549882d003d070300c44805001c80c0140d40114081003001680d01072106144200e05050100b1401e0041924100ca1140341c2200e4850403605171a54003800f0f407049902800465009008802e4000c0c03103a50a14000c0c4681340c080d540303d11403580e00c00c0c494440c21200d142d1241080b88280c0b90120041c1130f40c850b02d0040c03580350004000c00d04840b40403030314480706240f040130701003481d005651591084611940c45002030140e0070041002e07a40450003100c050740c1c011a440341d2a407000703d5450789048513104c4070b038004038400103000c01c44903000509280704500c2580c524600d20101c50038003680d40800d64038003003c29401c0740c40080e111658044035102c01c807040300074140040c4131703000a45407244907170701c000b803060340000e082c4400c0b200b60007150f000d45261001d00d000301e000d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 575920530 1250 575919280 575919283
    0x80c0906030c15040e0c03060607230709090c1a12090712031106160f03110d050903070c0b120103230d2a0b06061c02040315180203071a0c0304090b010908030408 71
    0x46040c0100007074140c103038080141c42c02100c000300009001084503207140d01c5141003070050640c0b2800b0749050012100024003188005500c000020a103001581010f207400ea22582100b0003a08030491801100408202c0080220f007403108140665200440f144069243c54203010300038041c0c00201e6a8284010f04698019d6071001c0340341c0451400041380664102c3d801e031b060081e01c00700d006031030418091003051403000000c5c4c00124002d0803c10a8295211000c403154403484150311f40c27540120004001040400d00b20340581d00c046d81081542400c1d040d056414402c0d503d0900d00404c6d50fa1040b10003100c0100d01e80c801c00500c2800c542c0920707041e07403a040e20606005000e40e1244000082002980c10340c0401c2480300e14050748103644841d00d03464050020744c003135075805005916003940a40c90140c2484d40c2c1d1596500a000380c0b00c0030f428a1a0f00700d001c6c1d00642c2c2483d2000f010820b094604000b08000c000a01a01c03070f0000d50014080700041818101d540205820391007400140b006003070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 575921780 1250 575920530 575920537
    0xd02270703052202011206080a060606080c070f02100e040510080601150804060f090206041403120708090d023c0411121b030103061a0604080c0906030c15040e0c030606 74
    0x2c0908105000c0d0740c0c6d500c400f40282030541c0103100c20780501400310b41081010380014080e541a5202d00c3c003035550390080581c01c0e010b5080c004e0580e18000c074400001d4207080b0320640040601d49841070f504500d03031000c182501d800b03807007440715541031032010080b101041c0480703405040c54000340740481000c0072004081140241002e13050030780c1d800e00a480713840517600540983e903020340519240d071341c0c81c0b03100d090301610240001d02034064203010420404090307003210341c1aa44a00c0007170500c804407080c04400c4000800c120707000b054104240101d0510307108129400c401c00d4030716080c0c40d09c04080103020b240249510500650600d01980750300301103032081e50804510072042001c0ca9490149010415249003032055000320000004070030300a240e00300005400251160500040039242031120b10f00c00da102d40ca40a8004c40c0d108096803409141c0346402090040440d0310300704980000603404509003000d10102070001408000d03802c104408075901c103040015007411440c084000c40da1612 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 575923030 1250 575921780 575921783
    0x4020a050706021612080a05071b110d140f101127180601110d0f03090311010606020f1603030f0804081e130b07020d020d022707030522 60
    0x1600459101c0c0d4240d15603c0c0c2d80410341e0044a942c100c1c0749030300c1000d005017005854108400e8145000103440030300543d60000300d141036482b07442c81440c01e03031501140c041035030500d0317913105500c001160301289600d21410003890110002d400c9100380302d2002440c3c030006011071040310b42840001c90f40516010140c8120b051080c1040075050040400c0c089446150304032907901c8a942c3c40c00b10620320652038194450002078907480602440803403160342d81c008907130400b40000c140f01c01c0340ca15144070350400058184a0308000b0b80d40023000700c169003551941c2d04880016408a80440e0000d04100246c06010590019410541e400c40d02d00900103a100c01c00581400306100120b0200301140c0100c904401100501d211022a10304410245030f100040d2199001d51641d0082581c00c102c000b191400c0c1e5000f80006030380c50550303080c40f046c480e81050a07a802000c00c40d1301d080031590f055005000d106040d01003119031902c944050212640940345404034524041c4044540414600c00070455 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 575924280 1250 575923030 575923043
    0xf0f0b0f031906020a020a0516062601150203161208010b1204021516051507020f0c1c0c06051215031b060d090f140c01020714011209030503040204050604020a0507 72
    0x809440700c086c0e1810120250051040c81031810000c8040000440e14081c0c2d6165501ea6100c417100845040b0b04c1c40f2610a62050369184000401c0341d000c01510061400703420303006481c107003a00703240040c00b00310f0007600540f4640c030702084804055510075500340c0500031180c15a42400d03548480d41c8401e03000104000d00410a1201c8446507061010590b05001d184038202041903115152803a2100c040e00d001001e002c9003440403455450000c11000440c6140b94000c018010703c0a080210940d10300c40c0c8004032640a81303600e40072980107096080600b001d03484440d90380074150941611841c00420144102810841b1203030300750b03404981c6182c4401e100c40703206162024080020590310901044ca01800e00c1d0058500402061a0028405074042d008220080c0c04541d51701d43c6807030110130aa40180c0141c5028040841c018403400340c15001850103951488984407400102e45043d00280c0100304040208421031800d805400d034400402c0c1c41c19400c20182420203801c502840304024401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 575925530 1250 575924280 575924287
    0x80a030c02010b0603010b0c07230d170a080708010501140301150e060d06080105090d0c080a090b0a1d0f06160501150b0a090608070e130f0f0b0f03190602 68
    0x74800d412010031000020405a80e0b960740b00b002641d107520980c400025070049980018104868912410fa1041030260211055960400300582004c8010742221010640001c110115104c10045c00d000c11a40d190440c1e42d0500200213041c1c0c2c44141c0c4400e0410060095200c04002d106003600e045a041c0200c1060403842030106446520003041c0ca00c0d0804004910035103100f2450b04070000b1603a000c0e00800003500d07500080d41d12120407800030404521100580c0c0d00050003400240146c150f14600b202c41162990480c5483e40d000d0481c95001414010303184503000303d01004078104540072114404520070b49000305034680070790004070300d51050600c072113000c0c40400c2d04600008035015004e81c0d04a925006404a0f9401c04810b200003c1d1a500001c00c2541c000d4802e14011155a00c82c80c8440c0710307590070048a0b020303c05441003243e480e2400209004a24020f00340c4030451000041a04403024060000d5845a00210b42c400e50142d00741c102c003002d0741030742c0c00c20035030304440090394 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 575926780 1250 575925530 575925551
    0x120507020a050f031903090206160317010602060f09010507200f03070614010b04080c040209120109050f010e0309090a0f0e0d080406050c0702030319031d0102210103080a03 76
    0x104001c1460151070b5018154180c0f07091800030000b402c002d01c500380c000e49103c3e14103400310101c41410070001e410540810078241590100c180060900e4424a480ca440100c0481c0341d101d03140007a849580980d00510034407818000b100c0b4990381c00740b400341c0200110300d041c00008003140500384030000b0240030b22035904081c203801e00004e01c0c1c45103a08202d0743d90700d00526054005141e070005100101140d20f00128203d104030045404540d5680c0043c4100e4000004000096100380d14443d0710441c81101d01c49100c2080c050484803c1c010b01c0600403100c0703000101420345c0d143d40292410340d002005807112990319114419001001d8460000b64010345030b5200c4010550880c40c100c0d140314002220700035652182032030784240d00c5004244603e0716840440b249601429200030351682003409644c1c1040c2040d1880303104e80c40d4501d03010170b0007440072080f40e043c14100c001c0c443d11a50000344c8801084007404a203000c0500150340001c3d5589107445160507801b0305103c24081544900ca0241d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 575928030 1250 575926780 575926783
    0x11010309080d060e060f01050c1216021002010b03060603010605420406030c090e04030503100905090c03011b05040b0f040e0711061501140a0c1415090d12050702 71
    0x2141580146003c1250540f0380000a00400c8205c40952064420060404895108105460045010000600e0300c0d600c0380941690f50f030070540103c038500000c3c1d95208007503940d2014142149055400024450104405150404d00000c0455000740c0c10a1004c100e15242c1d8203200604140381e4150b03580c2d010740600602c00c040f0001c00c03440d0035a40704580450114601100400c00c0307800e20380707040081c0fa80e001d000f0b48080721907100c2d4082c525103a4000601280c014001981e001d004a41c09494071911680c7c5c882c00c9481c1951010466401150444043d050034445e80801a051804500c1e0307039100064020654411401142e58101010503071420000180050b14082d00e50301c5080e00e142d16040000802e00522a07051190782e1240c0400300c2c0000d403c090304d03000e00543c1039440407800100c120307100a107503011024040812424030108070200b1841203295070044030300c401810700d9680210f801102c1f80c01c007501045645c3c100001c0004880e40040344a04c0d5582a8440896039903100d00059 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 575929280 1250 575928030 575928037
    0x50402031c0e0915090106080405030301060c0317010f090b1f030e07120b0f07080921070c091b0504060c0b060d080705010c0212090d02120106050d080403051002071101030908 77
    0x140c3c1004601040c0b20321428900e0340340300e82034030540c0c1850f9580c2e80d030356046a59640944014109400410040c030481788030340c841148690281c10154a81154131140140301c100903845490b1000c41403000b40005c072031a0040690070001140c0310302041315040c2c6226544408651a20b0516950340b0b201000c48009000d4078005029802582142480701c1c1001d8806000c103c4150a144440d0f00020794a98041c2051b54059040c82c0300a056071032819080c02c410142080040341d025200380310710000584a401072801402003100040fa10407040700800c2c0383c2464805031401404030510050000320740c40702d0680906030b044038039491070781c407108086640e02d081844043d0003901c00240150074400c0542208241070b007194211907600c006241441c11b9405604e2080d5448081d4040d040f0141c90000408541c20740d595000181c2141d0760800224002c0500c207084449100205042007032000601c034540194080080c103602c0d14000703681e420000d04800c01107505240d610301d104d0040c4010034099 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 575930530 1250 575929280 575929307
    0xe0c1b06090105041506150c020111070603150e06010f0804020a050603070201150609050a0e1807060f0f0c0308060910150201021b031201150509041409060703050402031c 75
    0x3034036901c0c20403100e9540600411078007924100d601e40e0300c40d03a0640e240d1003184100c9540d403200c0002d1405e4848102c03620031201100303a0405c8505002001c0042d014044071300100b82076100000d41c08139207121507001a441d039200380341080004040020a0360482c0064681100301d14140328607503240d100107071081e0740d0f41e0002d603009200401006540348c2c0562241000d034109a03915881541c1e6200202d82d150500d000d050780140c0021000c1000340700b401100b0f500a14581c00c80c5441055000507246445801c0e441000041c035020200d9122542000ba0b80200c50f48034504048008401d8802605080c00540818003852040c4d0000e03050b00001451400039051011a180d900c220f0307848003d01035003140403001c0700160105e12100c100b01000007202c0c802424400158116864141402c01d414010403204090080800c5096203e42d11445039446012500c0c003913218505008000d1450008000e0070601030524290a100160f034000803c0300c2104034a0b0b12824003441e04003401c0341d031000c20310310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 575931780 1250 575930530 575930533
    0x105060f070602040308090906040b10181e0303081e0c0a02190605090129040207020a17010f1410210c030b0108060f0c1206062b0c0302040e0c1b 64
    0x213000c400c00c0403040050540d407204650700001510b5103010881110a41d84016a1000010318408030f598010010311008a87c1400150401d96075014480859a18180c454660410012080c4201500039050070f40000411007904039181503102c14907503d41010b480c0c0f1111400106039901000d100300304803a01e01840c006454491707145850054040c0c14143c52500055081c01c500b107018a0041c1204130f6200f1a4541c00b040311800d21003403200951000e1000d136003000218202080c01d074101d4199500c5400b5001c0002501d004400d926402c46541c01400c840703000302041401002d415407080c000944c1d0481c40e1100ca80b180fa0750960310500d0000500401007a0444000010310065064441c1281da856007070310300c503940d41417056045050850b21442500030034030612109065506280c1da1110000e071085240c034021118008032000d01c5859102681100301700032201c811640694600540a030070700394202403c10032401d01408000700036a01d5000007180032028242d2000043e04008420f10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 575933030 1250 575931780 575931787
    0x70807060e0a0c05030d0e0616290f070804060c050408070f0f1a04140d0f050607090f05030d0e0301180c09060e0c070816050607170108150105060f070602 68
    0x151440c0d00d80b07819520946020004000c00501d6080214007551030760215550585024000703401c10415400040300707240b0142d1030061110004241d060002040c010041c1c907203040034410440c0300c00240d0000c0c05006101c112000b1312500383c0e00210350a40045e44842c000c00d0300c1145150450b00c0d0b0249a008000a1155040014000741a003011205449a503041c4802c131680300c0d030642105071014964403100c0ad104101c03c00c1480780a62030100700c031400420794865007032151110225040c031044169210b40041d001c1c002042e8011981e10000c04034050100355180c0b8040029444c1d40c1034521280522201002d200d42c242d80a501084c099000c1e260080301d0304009091290b00c689260240d1202c02d450401d011801490240744d1600c18008501114a800360503960030039542c03c04100100e2200418400a002441c2840304a10449066846140d8105191400001c650041e400080590403064524207281c0403d0303c0c117030559030b060360055582d982540c61310226118000c801391500e0300c0030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 575934280 1250 575933030 575933051
    0x8040510050c131a03180f0318031e1e0f0d0302070c0b0301180e0c1305070221120907230f04181104020f030c0a14070507050607080706 60
    0xc5000d0310b0b0f0000500301d10a14070383c0702d0103054005203072400c43c1c5544a2050000030700d496000841c040c5c444400300196000e07200000881440d5400c032403d00408a0481249040e0a08040000c0404160608180301d02d410611940c503403120302d20324000c048008010031401c006c02042164010400840049034100c1d100f20703c0040080d0030040701100e650411400026580310b84a082c2d9050715203003404d0301d0034540138100110060040e550071041e58010600807800c213954015941400000300c61004c955031508000007410300042c19426001041520651000c20b64144142c0b2140c1503018025642c50f03c90082040c904940781d4000b02020038100b410410400c00300042c00b0003020700b500e85a001900003002c00c0243d941900b84050141412414140424000080c882c0d000201034401460071061410100c00d944c022240c2c0e410070580080c4841d00640c2c4600000d070781d03654000001c0d003843c4c03503a540c02d038541c1d08600c0354a201e0140820f18006004490040b00c055640c01481002600f491 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 575935530 1250 575934280 575934301
    0x1a030304120b0627150613090605040c0e060c07320603072c0303040303050304170306060703050702010e040608060405100626030403021503180a11010804051005 71
    0x3401c00c1101e04544100100304182048034584c140540a6140302c0500413004145038501007006144400040001022602c141c442d030b8011710a400e020001d0a5110341091718203000d0f12065804039005900e01424010a01c8d030110780041c031410121115542c0d03100b8a82d2151400c161900b100d0341105070010140c0080414410090388501050040508604c64008000b25400304a4903440458803071009017445007680e49a81c1490000b040c8030204920801c40030a1079601b05400c202e021443c00000e21090114542058621601070301255240d40b40150104009026140c4d004051210204010302103a003d40210404800003800400c100d03a610035002c0e50390170007a101510710b4041c1ca110040d80d46a80e0046000b40c403d108000b000f01c903102d0340072030f2007204a03c503034000e540001d100101c016500c0d00d12001c103124a03400155220301780814500c1c0091702022406116602500d07403000062010048860b101409092560087c2e840342492418280350015180f1405c4c40e00742001a0b1002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 575936780 1250 575935530 575935559
    0x120d0923010b0a1401050a1806050403031713031b0b040b0106030c0e0609011805130606180302030601030308060402070b0c030a0e0601210507030c26060709091a030304 74
    0x400310024041020000d06010001140e400740c070316440b50100c1850550b50007100140034514451405500602e070840c2e40740285040c94011600141c00050200181580f2465405070074240b140124210b0030a14144456811466401400e00c0b4860400340740041c0710540010605400c500c0c650400d15040c03030551003284d002d001d002c0c0842d00c2d03d03c41c1008548210045000c0c11b20261900d890302c1c1002d0010344a481071154038040d450400c3c400071403142c941c2880402c03100e0105d0400b080c003504140010344100d0300301030014423514292400300003603500083e030581104d8250400d004036031903c4002c18040e2080b224017401e405242014400c0c51a2030f03038000c5220f04003160041080d10009182c10f5195030080c4181d2042c030511038144081c0c03240356130349025251320401c00c980300c070b82e56540c0340f511101e42d5034402d038080b8444001314030040320080c182c030070740286030b034040c180510707040c003015050b11030038043e20803c03e5603200350040d244007002240080f0300004003100d4a4a42e42c0111410001c1d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 575938030 1250 575936780 575936843
    0x10c1509030c1208040b061e120706030b15041e080f07140f0303030402040e0a020310050f071103030a0f02090d0b10080f070e13060c0c0203120a02120d09 68
    0x103207048070300f0b00d0741842061400d000e9640b150b0b0295680d129001000b1034040c400301300600c1c5840c1aa100b0495030b9a041214900001400252100524251028048480403007005004540d82e19503108089100c108441c1500e043d6035007901850010102c88403440785035000801940b1900030850100702c8000b64000c01c491a07941d00c00000fa0941e011f029528003801c0045401d40c1c028008a40140f9040d003288154850690486038a4842600000e280c924205c0e40b01400665480600802c0d13012070550940c025014286200700e1020602e039941e8910006000d035040c16514001c0c004240400d40445013a480f006048003005080360602c100700480c180c0f400008421400400a41090081000a0310000b0342c0c0160482a14088820168400c01001c080d1003200c8180f0322000248248103500c0072020541d24000c0050980c818075103400205140100544000d0017501442a80026a050002c04000303580303458603a461443c0d00039154900d0018140c001c07800d61107015a00d80b2501d4402030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 575939280 1250 575938030 575938043
    0xf07140d150b09150708131d01080606010509010c0318060f02010608010e030a0804061401090515181503101a01120605010503011202130903050306130e0606010c1509030c 75
    0x895850784862640d1080c41149a0001009100113086550300c5002d02000ca000b180303e20f1074607504900401500649130008400c203020891000c40d41c02000c082076000d024450010a1740b4102240060040e0040d0b401c00c504115049030510b00301440b1b8060010364100d4000c0035159152286005000c0b440c205c3c1080005600c0e00400180c0d101050140d82c0400176032001840ca00f41d41c10800301c1e10a80014070594105848106c96580424003110b802e0003800290780020340d600b0400094122590903542840c4100307850104002c0c1041c103049030035085000e000e0900c400d00d5a8074003081c14801d59040b241840c0d441c1007599889144086000c4c00012401d07a9003494a051102d4100101d40381c0d070060070b001031024001400103d1100da104860680001d22015410021541c54802d85180d60400c4000035008800d1115034103101c0c000e41401e00264805000320702c2d610022542e81c52005041d075042242480d40e142c18800c000f855083c800e251000107000320410360801a01d001c0450710b044800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 575940530 1250 575939280 575939321
    0x504140c0613031101200a020a06050c07091a0d050c1804080f0703030204030f050c041b2c190f060e211207060902030106050109030b0f07140d 63
    0x5071620104460011007034203900340b8070301c1c1540c481d60890211140080e05001802030051044c001040344410700e04400f000070160090a8818031000080c0b0744e00000500c042405482114500468200d056680700040000d602403483c82d5200b03127406521000d41c01901c40c0c03403098141b00000ca8041d43c000c8058600280c1c440b00c88810101d201412200a85010028400e01e6144080000201901802460054189078881e254061014030b00030045402d907104141d03201c0f841c180780c007800707500c1a00300b16900e0b1103080d0140042c2c07000078030920800341c1a801550f84103110781411301d40c6901e8207003e8010700001000e80740443d4410300c6801041da4035000e4560006200c1e00c0b444110320452000f511207132580000c003090b114030a04403490781c40766000754003480042002050142c441c0fa805650b01140c3c948140c0149030840748150066030400c801e2040030f101044506e0340082e0031440340e1030341c50302c80c1da20395008885900300c0361004015418002034846541031990404425180a00d114220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 575941780 1250 575940530 575940553
    0xc050a05013e011a090403020a120e0a0b0901030c020f0a06050402210706080a061d071e020a110405010b04051302041a0c0d08073005090d020d090605041401030f050414 74
    0x5c011240100141d018101620000b540340701c1201e03c03c02c89090424000c01d004000a4106509421100002201181c01d110543c1e050180c0a608980d60010380340441c070141e5090b48032541d41c10080d04a60b1101c01060440d10781c1d1a856580b40c55103040090755803654540d6a0b100c8280c0c0c031500000600c0c1c440802d0480005102d0b000c101c1d501206c03c003400d14119103820f10301e0800202101d00f131081002d5021580304142860f007024032160f43c0a000c03180c05500c0d0040603100d6640c1d40380e000d10b2030540148000844c01c000c487c140c403021201900000044206440603101e0790b00a402141140c541c0f070303098800c0c24006006a820315006840500c00d07100c400310745002c0100c4048001404c18440070014034269182003000e8410620b40354491203e411380c80040d12020748140a2681c8201104c46c0c02a40c10b0044114000c21b5181509036140382660040c032501860003054000719107411a130445a00036030050120764002c40e010301c510b00d03050500c0404942158403034507242c01142194407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 575943030 1250 575941780 575941789
    0x91801150e06030406090303020c1b18010b03181e060615090109050108070201020c06011202042d0c031b03090209010506120c16050313030c050a05013e011a 69
    0x1080d0303101c040c2c81581966516181c0c10003400300c0e80c00990526508015941a0100c248521500c0002810040a242c00604280042d408621422104540b00c1e40c005100203160181100d80002c0e0108441c100004940c0e0041e01348a64203448149003010801d038000f00400200c0d0952103510103c9880c0100403900400c240b540c41030040c2c80380080d070010b40038403981d8001c214854000c030040c40018200164070a1492400341d007a04500d401401e910170b64401c42c64640035089070f211000c405810301030006605442c81c10b20302213481d00c600c0c0d00c5000e00f401040c803e40c0040b42c04c5c1d20240a4000001d0780010160041c000c0a906074003402e181000400c480c10094112078a15030440d0b240f20131a42c848580c440250030180703505011508034440c12002c81d9041015244500c4180484205a451407404109440c0b0580c40b03c0c1c041c0072503030301c02c102d03d030b82080c0900c41a0074554111800300d040000403548109501400102e07001d130703d903622161180e0541c000503d02c4040f60b4007a503000c180d4002c11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 575944280 1250 575943030 575943047
    0xb06010509131b110d0c0606091a0f04021213080706061202010201110c070504050a09121d03011b050a0e030304150809010b150a050c1203040b0f040b070e030309180115 74
    0x10042c0c2c060b10305c0c3c4481c940308403e51010140641d4001a046403a054441c0c26030300381e0311450402c00c1c0385031240b131054a0455a040c01151341201c04624100f1820120100c400000304030041c1118034660907028041b40c9411034031015800241000980d890765402103000d406140142d0040d07282001d07002204149400b2918600c500100074540d1a252804000c0545030003800c440401d9103400030000003a02c1045000004099926071030600c40086075115900010725080d10b12a80c10815641442901c0c072001083c0750001d03140c80c40c3c3d210407004007030b10721103014040a90103100009000496000765485920039023800d59804006841d000402c03400da50000507816840309520900e4046007176204002c0c10007030320508045081c4000c83c21080c0c01c00c4103036210b20281d40c2001040004010042d8082c0c2d6104403140c108540d2801d00b43c4500c21104401003000040c8810010125110340e02001561100280106403250200010f0910440e03001c0070b114101200c0c0704600c1c8072881a001d60707820b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 575945530 1250 575944280 575944307
    0x601031a1e06040b0a03020a060206040312061203030203070c020d11030d050310061809060f0e010b1608031b0309070e0f041502090103090605040b01240206040b06010509131b 77
    0x481007141c540104100051506400301d0f54803103d2030304004010380b035601e03d410003025190041c0070f9a180c01d05024101e20000110001014603100050000c84034882e00359880d1901440c0044c2c582da5011001e03142c1d140302e400080d5100d004408091f04210040b42020000141502520303045440328009607803030b000030340d00c40d004007903400c10511020f44555194020203131910850451941d89021000403500346811001074503021140510a4403c1d0700e0002d8018a4041c040524008170034104d024008020000104203d00020200d4000d0040a540d00d0703450810707030400c584d60300300954034035507600051103030360000c20a00d00003900d8615410719052050360004505810500311152550003075103c9803160f418156a06003a501017662881031703911841c80b5554890f0035506000c40368100e1001c584115186144020140310100c0e808202d884d0070070341c407803003060164481c50016103517401440c41441e00810840c03440d4104000d241c102c022000c4201c0ca4000d800002c0c1030781214155081b01c003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 575946780 1250 575945530 575945581
    0x131202010e07050909070b030c030106020d0504231909020d2007060507020331080c060913020c1c08070504150e031f0b0f19030308040809030601031a 66
    0x141000b03e4240221416071050b010401d880b50315481700c040b00c01540003541c028038000c1c00400103225440d010814504150050b03f08a400c003441c021410760903d420613036100c400c00400c54104480c2c1c0f03c040420400030000b112403100141c43c2c08240000350002c0041c041e1090510191003110101c0c0f4a16080c0e440ca8021604d19000040d11800050000906118110300c07080140c1056a40d8000c0d40c6240500100c0101c85c8a00d20366030780c44020019500045047e8015402c00440d50b59488200c0346400001c2d548000080030310170420b030082c0074020306280d090148040510116044403825040c62901d07841d0001319031101402180d9600445c041c9d11400c008490648450318041c5d07402d51164900101224400d11a0410f014610b0300114000c0012a442c0e10701c102e80b40c0781c007a000b6146040c5c01da030103014411480f9040b03d40074219100c090f092000010115050100320011140c4811000d0200c5607107503500d02d040e041042420354022110340c0303030300701169145000d030b229404030310325511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 575948030 1250 575946780 575946793
    0x4050705030c0f0d110a020114090c0f03010b18060315191a0a060f1704050d11191203050a090b07030e1e030414010f0203190512131202010e 62
    0x3489a01640801c1d030b401c501040038030144118101c0c3d8001c410007481070a040545404c804040a801d4403e0510f1030f27501c0040040070088000340000c3c1415020b001111010699051440480e006049240ea0709811003030303007140d040c58000f030415030714040d410542c01c0321100361040d0612040345406840803018400b0a01861000682641000d00d003a040601d1010028000350002080303600594820b50214640d6900c001c692900101d03a140c00022882c916011441d00307544560315034030141c1c5042c0520450014040a0700e6040082017804040076040c40e005c3d013030702d051a407081e0040c8540600000d00f4100010960b070414040e5a081c0b644c4100a000b4a03160724001f600a46108812801c09100b142d90001200c00d08801a03107603011818003455440342800c0c5003a442d4000d2101031410300c102040050203407640081202c0f0368204816540c1030035000010103d4040c40344042a10352401d0030424040000b2010084010151103024034000f83d02001d8400e90aa810740030103254683c12a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 575949280 1250 575948030 575948041
    0x8060402270a32181e01120f0f0303150603021305060a0512090f0d08011a0703050f1804020f0d0c09140f0d0c0303021f140105060702030a080c010b0f0405070503 71
    0x1c03851070b40f00720010022802e0000e0740384810030200081302d42c141e04460a0400ca0071402003241c100380502051840030050002c00e0321a03400031455400700500783c80f9a207020301c081c9807003a03200c0c1c2d4103860000701000322680c4d01c14004020350040c103c5800b0010803d00000350074039008040780c400d41220703102e250811120000b03401904800420703900840c01840112801220144405411040315407280c0d2081d504042d88c0107a003104102d01c0b00d014550800001020a8210040c0d421002000c4046980e034241d81d4668000c90030400d0000e41c0140c000315036243c400d9807e01c003422060f045860100040b080760401280c0d403a901c0e115050030083d803500c03502441d041a2140461100c1d000d4000410100e03035944190341200103903c00c0d001a041113020401808510720120003007540440180103a10310f19000020610b01840740034403501d030008040085480902c400300c06641c025480c03503115240981c030325010306219400903110b900d11a004d800039180500c0b41c2070040749250703a8a070855903038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 575950530 1250 575949280 575949359
    0x204061e030b040f021e030c0909070309020310061d010f17160b0a08070201020906040e04110907030617010908030601031d03030103081903180308060402270a 70
    0x3030060004040e2030300800503841c0c0701c1d8000e10500c06907081c4010b0741c801903080040d01c80b68010b89001101d090800a1002d000c0e00d0a040d625040002c85144c00c060b2200482075009080f500c80080d0140501110114100001c0d41303c0c1e001c40c0c1511084100f0004c90740700000030b2000074041c469441640000501034080300b014800c0300504101c00702d51401c2c175000c40d0705807503071000d0b408800c0155000420314481644591401c3c3c004110317000035400d04810400203511401180a10803a041c2100001000c0c401001c10718100c81601511030103107400e040303000402400c0c090003907440c9108608a00003202c2d00502c00c82500c01d030006429420354840000440141040322604c0403030022021503a9050030013400154021441405035554990381d900304414000f80d226104000d261505405100d0000601388864075a0343c5446d008500d03642e5100002c0083c0141480081030b060300c3c10800104c00724070401d161011400300c0b0400d10440e96600da221803d440b0019011954950303401d441e045030384 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 575951780 1250 575950530 575950577
    0x30e01020606150f0f04080102130b040608011a070210080f01080a0503030412020c0a080a020a0e0f0a110d0626010504050d050d091403070212190807110415060f03020406 75
    0x4d0681500303250110317200c0307482c103981c016401c101e14996000075503207041c4030150280c800400c000c502580c201444e0003405008540144200749021703440c20710110050b00404110b8407150360092884a01c6021890001c10b041d0086032408003003040e042c00410050340009203001c1080d40480118035640d103c2d41c0e540d24840304c1403882c106521500300e001c48180d403504031841c09410f110300203220086a90042000401844c0d109400380c80c104001c0c0f01d40c2891411520703502018100c40400d460682e144001e40c184248915221402e191400100d440072002612504c48413079401400c0d050700111003020700300c40d410b44005185074407079104000300c1030180d8090a5640301c503410000f200d130100c0d1124113840180905003140c941000841608514100f10000000542c0c00700402154103d44640501c030fa049000c0901106000710b103800030407000404082c15114090130503c0714040f241c40004002c2c1a5020b96800300303410b502c120360440e20a1080e83c0807521070f07640d4400b41c007018915000e800d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 575953030 1250 575951780 575951797
    0x6010e22140a0503120601050306010c030e031204080f1015030f08040302180f1305030a0513090606080603100b030c010813120e0316050a140d0c060507030e0102060615 74
    0x40c0450744038041c4540500c0910412401040038555a60000c644c85640900060078a814090180184802a68010131941c10182e150812426960044002038a400c1040804040e041000100440d031100e010410001e050011400c6420366207802c11000f00781e500c045d80001f00d00c90240010004076547c2107540041034060b4202c50b02e00341d1280c000c81c8804e1a940e00001e40c4044c01420700850040c00e03507916a0003c4180c0c50a8144030040c2e030783c1a01c2c1d11812140c4401c0050104406605088080d8090014503500c0c3d0200301e5650364036005071644600f2144684207024442c00c04448001d40c0c0145032001340300801500300501480e0040d10100000f410340c0c4103491170b2002c5800041c0c4042014109001e0039100d9403010300f03410b01094540307001104031420950141030204036a44540f441c84c806c1e22461555213250003103000114030404000750024145035841d100c0041d0454004004251180c0030381e40d400740444d8202d0042ea916041501c219400840e12001440c007844900301500241 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 575954280 1250 575953030 575953043
    0x1c02060408030708070b0c27040204091d06011a16060e0102030420030a0c1205010209060a0c0c0b3916090e0d05030a020d0b09071106010e22 62
    0x7034451022030302c0c1d60081c0308200d5800030f000801c2400d1000c40c4000c160b20000d40070f129481c0020030610781032041e008440f0140465140205041d0b20b03a41c03078040d00c001e0100b074101040f69240d0440d910703c5182485404149600440e400461050194400782120104081030245482d100c0c1c045c51210500d180b00070744455a0352400310120318420300046002e580030b50b8040041d01c0d0a60541c000030300e159011035200e81d024405040c000781e5030716441d00c2120300000c0e6a0301c260075070b814100c0c00780c400c021038143c6c442400180312904940115002003194003c4182a000da0740360480e910852091922040200c0020f000d000480c0600900489550190014282007405003860040ca4000003900384042d03240c0b003020501001c1c0b801d10810401d400c24100414900c02901006400307840007400315032180341c000034985210902d581102141c50000b60403190790b440c00d0000201064007540c0c3c006101d004190001074003101c2011041e0150b03a0181040b0b4a02c200705589030401c08a401c0b089854 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 575955530 1250 575954280 575954287
    0x1005030f0601050a1d0d1505060901140102070909020a080105010b0309060a09030c060209010306080f010e12090a03030810081905010c02060405030405210303041421190201150b13060305061c0206 86
    0x1010310f06051f0310003880d0617001c00c80b401d2000400049080c16040702c103941c2440c9180410603a40040c6542c12219240000a142c0280e800400d07144103560304492a190b081900024039a1880e00040d8405c1403039809030b96507038840e40048026280ea4040150001e0705003040407011807a1540107000000301410001451542c07166094105031030004000000c1e591a80ea03015003000a00c150020081c4040000c0d2800c1304840024120021038000503040258440000303500840e070584650290884104072a06010300280c9880a02c5050380704440a5003020b009400d16800000d0032401243e010019604060901c2d0a10444054100b0700c000d084800340f070903194509040c80191302a50180240ca9140c007000d41820340780c828400001501c0622080a6603d042c44d010151000241900200107800c01c03071440032405481103c1c1c0c0001603441080001514a000100425001148060740440c5581d201010f42c200c0d54121520f94001900c078401c02c000e4402545901d40c0c1610081c082403d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 575956780 1250 575955530 575955533
    0x605070c1a06010e0103051012031103281d040221090a17040e0112060b10080924040206070503040e040f2f0405060f1005030f0601050a1d0d 62
    0x59044078000c00054206008203000381542d10000da1504083d0a080500c9113090581c0594110b80551240c0504a0486201d0f2010107204071522048a441c00301200d03104c7c03010b9a0001d00d09011003164486115551000c2100c45e8010241c99060100e64120f5400c501d60440500029500039040d01048500c40d00790039002d00307440c8455502906e070300001000d0080c19880d20000d0103058600064a400b0140810064456004c2c0c0490540e030a4140303010703482080d07240c8000a400c0f14500740d980003040000081c0f0003507000d100140300d4080041140c1a030410070150305109006000346455481f10900001c016080580061500320b1080007241c0c5815901d621010302d04005a80480b41d07254801c2c40d00c0140122580c141206410b043c0de85030100c40080c0a500030100b112510b44d008948901c0090b841c0e0381d50004210030300ba0080c21004041202160007002640202da680c0c15852294010078507a51241e4107903030010500740c83d2000105003a141d101c0480e0751406256a00a200000d41c20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 575958030 1250 575956780 575956793
    0xe210f0703080c0d11030315130905010b0906060a0f051b0d081503010b090106030f0b060a05070b0f0c090d0602040f060e090601030c080c0f0405030307110a080f0a0605070c 76
    0xc0d40100441e940f41d0702d902d030042d400c280b0307080080001c02c40c110302080c3c1d5000c008001c881c2c00c1004c200081c3d41c120b580801050a06105a4090340c0c680d24180b0a501842010b40040002c1d4808071590000ca64602c030800c00e25000303c03040e00b070005008400e08030010f4041c00043c05507445201c1191041d54400c504285000d2004844600040f400c00c240a60026880e1180441c0e503070403002844244031202c0406d041b8001445444101912407c1d0088103410581c4207221140703018062a940e080b40d00030180c940d9010b80405c030380e207050260010f022074a45c0484280079040c0100038030301e400e42502c10420a028142420345000f6130812000451000c5c1c194590000c0841d6120400400748072420400340540007000b0505060814000c903101070b50220300154030030410405103407180c64400d1000c51501443c1c008030f400d880001401401d000c09160b80d480b1f040d00c2259161805a11101502d80360f0b8040f158001c000e5201c3c0a0301000120140c1160751700014901d0301c985c020312152141d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 575959280 1250 575958030 575958043
    0x140618180c0a030c03140a0305090402090111010507030507091703070605071115010f27110c0106030b01051504060203031923090f0a1e0f020a03080c0d0e210f 70
    0x211404c0720708000c208100022501100182070006020b00714135581500c016042c0c0c4905c03018284611350008103a005607000b180350500540c0f000d002001f2070b18080c04080d00820060b18000089021001c00140c901d04680c21001c135005054091030170305581e0750b50b1102421010740000c05020780c82c03100340d41c01c103001c10802c0c81d85031707514030094041e501d004070300c032500e1040760000000c1d100c500c4821044101d0100040342c0e0071000c1d1000091984600a08190340c0c00b803c0d000d2035055003052000428004a503e03c00e060764001c49024100426600910402c0d100364440c032000350300284002a58403041c40102e440400c0d00010124980f0000e4100140240503262600c103180c2c0c50405000d4003210400c4541c40c13111150000709002c01140e03e600d411800203c500c2281041924200c90070031000039a0070007265800f07000440c00c0c0b600c17842c0c056005c1e00980c0c0000094425030301030800050ac1140225180140039115404800c140000e070841c801c0e0003803040c2e0703440c840e00031990041c0c0703001c1084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 575960530 1250 575959280 575959283
    0x3b0f060d05071704231002040902191817010b0904150b090709260a0503040303080f13081614030c0616080106050a02100c03140618180c0a03 62
    0x14145001140900340124003030600703001c550304004000000d03003480d0f00e00250030041703018400d5044d003a9000c103180c0b03103034241c1c911070090001c5400520042660050400e03004160882d800d07111041204444c092001c2c800341005d401950700402600341072445a4403070148440021840c0080341000c65255002510b0071605c156040302da01c40c891490b40701e401006034045858261505080c10000c00180d41c5010ba241d51104045a41c001d8034492607084494940420035690003902c40e0a00c81d440390020302c819000304014000040080c0f081c078825504c11000c5002802e4042603136201c03007480e508503440f0203000ea04030701c0c60f00e0f01281c81e1180b600e20300a4030500541d514080301441500300300c000340c030048280450480d511962508000c032035041d6841460720940322850000c04a00e4035241001d4200040d00d132003040128158160490f80a100b4a205000b1044d107900c002c1c041c04680000d003000d070252080c40440d10101c2d1207494009428641c00483e101018070350000b40ca0701800d68030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 575961780 1250 575960530 575960557
    0x2060112063b01090201050f0c0c0d1202060903040b07030e031609050613091e0507180501151b03140403081305040b03061009180602193b0f06 63
    0x100c44002c00200c0c180c0150301d040c800090090412075070000c0c066020710302030f05811070f10100700b00030404010807030300c58210b00041c188510203010b424403000c42035907c00c00400602030340d000902c5200c400001c031011242c41c20322080c0740501c42e403002c17103000e8105c0300102c2d414014103400201e4290300c00e000401419005a00203003504000381000f02e0b038140300f64005121420554980085101e2003204c014801c1da8a4400c00c2e4000340c0d1804a082c04403a800c69031080c4141c8850340e19403400366010a041c0e41016240c0d64804044050541d048070100c01071040346203554002c1000248216500984c4880d480242410b1079207950340c0c1c102d140c100070118000c103520f00c0810862454980109420500b090b405065241058103040c00302081c1d90181c0320703c580d15400280307511507080301124495900b0030070464070b51038a2410300310301080c212410b500003020300700380345d040d00705845010700c201c000400c550b0008001240f5910f000046a03c0460344200898000c81079501c4c2d1000134800303c2074114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 575963030 1250 575961780 575961851
    0xd020a080d2a02031902040902150d0524190b0d1506032715180c150512060a0504140106080703050103120c0510020a02011e020a0206011206 62
    0x3040c21420382c0411460000c1d801800c0707080c03070168401160034103044c1801841e0400100841c004a000b500ca6610300130740105c501005001101c0c088005007140c04507002e001e11494031061319140340b5881c0c80254a1030b5200c00030341203201e0324080c5110200c0001d5070b070305003501c40d5a03110595465000302140244058445103210000d8031003240c030f940601064101007007203110383e2800c20900c080c0100741e811013090380d00740b030b80074480340443c1d0b411020301941090081480b8203500c0032141000040495407944140300100d00181003402c0100d00d100555940d60038042a000f00c13103d250000340441d034100703901d90b00101c0c1076100c50007101d081c0c0300c1c1e4002040040d490258002c0111000408000c109407a11006100150011900014031422482c0841030100282011270900c0083c106884059100054500155070190410381e4440c41c40350060090a4501c201ca5040c0e00c40c501404005811080061005507010644d15110740e00910001445142034440030500d045440c4911f50480b0420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 575964280 1250 575963030 575963057
    0xc030203070f0611010203090303160e091815070e0d0f1a090d0302040b0d05040204021b010b100216060809031323030d140306010509030a060c030b060c0c0d020a080d 73
    0x8803540c071301c0c1d507103d002140b45182082401e61240801b429507005858540c004107081841080190f1030b41c3d50080200b4140c1c00e000740000c407240c1d601c9000a0403030144803102c0710580c0c103501c940c038400c1d03005494083c400410a07081002c000c140706011105e40289511000124160020b0050203881e1040001d08038200803402c1490032a801c0c5808080600400c010700010030020160790703007000300e4000481c0607107440c40014060b01500350440d0031504940c0b80501c10240c15082055003000c2528502807188500c0412a10303a1900b01c034240c01d4440f0942d040120394450605540d225240c0b806a9042c00c941e84802103c494881c0e1200320f511008185540c003510741600001000d800c200c0081070380250070440070704bc420355000542c4255002100190061b40500c04513810040010300f0346050780705070f01c0d101004221403588000028030300194840b803418030b20101c920360704200005044044900007040801c55070b03144126000116040c0000b900e001c104000050348815441c1c001e18084076 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 575965530 1250 575964280 575964287
    0x80a1409100528150803031f05331b03031501080103031d060c030408071a03040221010b09160206100b0a082e06080f0609010b070c030203070f06 64
    0xd00325220b0f2481018a00c1c00324a42e2181401900c21050703000b0850100b2681d020f01d081e4010341c00950540000001c010784041561004031006817902c510050f03003078a407402d120402052048114001040038510b080105504c0200d4041414030b4080600c0d0807030000304050304002c1880d410506138004014403c00030180003841080300000e18290185600d151401010300306000112010b005102450550a444400803144072880020440f941c031903880b260207a40e401c0c5441a91000c000c1d04016403074000c00c01e01124003440c0c0041400c05000c19110744880180c8140c55403040d590359600051881e616400e640610451120000a000140d1560064203182d40140150300d01c503440d80060069814150035a000400c01b45080d07070031551003a402e0b07c00d0b40c2a08804400004107404038901280958606009440c100e680380c82c90350300c880c0d2010012b010305a070350b264448030090040c01400c08a41c060915a402103442c903070640da403900171038100f10b0940c01c4500c02e42000c26081c040302e0380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 575966780 1250 575965530 575965541
    0x300b0a0815040c091406060703091e03060e030f040509100e012301210e0304170303060109060e030303041502090d0507080d1704030e12010218010306150906080a140910 74
    0x16400c0c040b80c03c40304072500742180010030b80c47c881c2d4004500181450f20501000c0007170070380b98004e113043c0a80311a804980056921080b41c4c0d4904006600b8040385010003518016001c0d0b403001030819041108000541000130881d0000b00085000011a1604c0ea1034240c001c01d82c00000c114403040d0700c000c0c143e102c1c7c1885141814001603010303900d0710318a8814101c0304200025800076005444e01d8109045209a40c41002001c403400e03440501131a0110056014507001d0320307241c402641d03448003583e50010040f403c03581900144006404900058100565440400c00040c07506000c000003524014400009803034076844050300380011074080103524084411418001044440f101000c080e40b07400400003800c2200040e02c25051f91201ca2585100c014031400035910b07140f6901c9010096481034882500203401c10f40002590350380340040c3c964490065844096030340c149070041d50860000703072081c1107066503170044400c004440040301d8040c085040250150105420107101a0303507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 575968030 1250 575966780 575966789
    0x170a090b010605130b031801051501080601090623040503030a080907050d0b060f01020a081809060406080331090207020a0509010e04030e030c04050f040201300b0a0815040c 76
    0x10304100004c40e0b20418003801080705c0a4030b03d010340c0c1e0703070315200540030b1203020f45000c03591982407205119610070701c00d00c4401884400c1c1d03509102c40e1350b81d50044641c06207074810800422045540402c0300782d1043d00894141c103002c030142d480d2603611000300b441c5500c00c3c07000100051b41c410a1015803881404000002c0400320f48020072064039407101203d485d00513010512a81101c2c03d0a4070076402440805030258018030041e070ac5075061b46444901520183c1414491005480042c85601e400e10480e400d941003c0011401c006c050019074151100f00003400754080c00126050300c0c55801540010701901c1c1d1040d015031521901c0c4180b001e0a41241c120314802e00c001d400602035081c0e10186141e000e5014503040b031400e90008042810440205203294002c1d00b000100040141484901070003140700b83d80d5800b00d01012840030345401c038032030019000846150b0f103481e03594859400102490500502d000c091656030724283d8502007520000c49080b048501c00c22003840741d002e00319030040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 575969280 1250 575968030 575968037
    0x80109050106021203060d0c15020c06070c151e03021e040303020c06030a060e040c080d0305041e150239060c0d15092c07030b07170a090b0106 63
    0x307504010019464040e82c1c001c0f40d98403031010002032010390b1011440c0755001d40122a0448045d221890b03841031820391040174001d4031a2680c54040c0341003e4089841e030a411000c000ca80c142040c600b11803110034a2105070801c6001c507139941700484503210a080310069905c005a80310410142103c0c40022151140542c074030602c42000804e4012910b03500000c0c0840f0182c0d139a130785002030a40104081e401100040c8105401c03c0308010f844075906066800b40b00c100e480c0b1070204082181555000c4400a015102910104000a8003c144009400d00c121150032040183d1500d100c00c981024000d0018206500c000300d10b1010f44000070700104d91703000c2d1351000004820400a40d55640980601d20070100021f0a80600301180d026803d1880b103510000707400c17503459000002421540348a444107000f2005029030094840800307009a0b207254000e000d0701455030301d402802102c020105000c1c0702100c0741030313621940c0c0701c07038a0780c131074a688403002644524600308001a14030580229050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 575970530 1250 575969280 575969291
    0xa0209121c110c1305190e030d24030605090f0a0b010e0718061809050901060509130302060411010c0c0f230f10110a060b0907031b03050406060e010b0307080109 71
    0x113070329400c2c2d41d00c00c1c2078130010011456031540000001000040104000503500d05403500c00551800b03c001c0450440b5035505100102a0701d0f18001101c00c84880941140940902000018025088994009050760030358014a21180259050955040e8111548101007005010b03101d1940c007065086181e51a2500a01411000c0e800364068580540d0042c00340340c68980614a01503080d4001070200e8002c2802541062041140a40010b006861185d070000c400220301119603082d4458480c0c01d80d006003059102c544803862180d917180d0300641000081d150100120304c1c2211600d00410300e55400301c0f10b030303480e041c200c03e040803c03d080c24800100080041050b542c5216040c0c180c020300721f40105401d094034105480d02906120a818140107020088007400025030054081c12800d492410791666034035400c40c1125a1614008801c4420400c00302d0f045c0c0c46a0320a0f039205102c1c0f10f00003140e507107442501c110131a0980c0301c0c07032400100000b000301315540180341d20b0040818071000e100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 575971780 1250 575970530 575970553
    0x50d0509030a170417030c010c0e0a0515071707050c010915051b0601060e0117040c0314010605031207121805060708040504050a020a110309090a0209121c11 69
    0x80354082c1c000c020300048640c1c030280c40c01500040855005006243c01819181c43e150b4010762241c110340b08200c61941b0f004891040a0702079004410714040003032072840914200350410400640010049030a0a4248400340c001810382001100c10307100c480c1c0391a01c4100c1464014909002c41d00b882c0e04200c04039504200940290003540c0c00c02140c1c2c2825a03c41441d41101c040013070301080083c0d918451039000050640c1c0013204035000038400c2c0d90b4013801c5e401100865107401c03c20344004010408078030041000c945409030140c0500039034400414003542e107200092504079401c007845000000090314a003000b044100403105100542004c0c00c0310740c48141c12031950451482500c0c02040e000581400b00030842046501401c001007040129003060340d490002500416145001f007026000b450312004400010b032960ae460090400c44e81d990307445d24160103074014070045130f0000044004004408c500b400002c40b84041440c40f0031020544440003048031012449404176600403440d88be0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 575973030 1250 575971780 575971783
    0x30204150c170309010209090f16020105041a100f060e090f060306010b0310050d0b044206151d040c0503040206090d1b0312030501060c1b090612050d050903 69
    0xc102e07955074540903102e5841c840c401d400381c070404000543c8001c08078104640340311041c13001805440d0308c5941540300a0140400d03400c80380d0544d00a44031a01c2c8425142004c2640c00000c0d5003c048402504040e43d607032100385844540300e40100c17022071180124518a4204030a6082d070089441c00004011300346000030903110501809800d03a030400000002e4148414511060300528024161186072596818041d41c0304006540c116040744100d080010003c08011164107203504071421920102d080081e07080c069030080707030b290798141e032180b6001034444015541c00c910700c82d031501c6050780c82d60460552010040084002e1344960310f0046a00b02da250b01c001580da1041d4180d4515070340b540360000141c1c1c64101d846001300031600b01c041c03c0241c015404128811280b1032200c240c0c24080e900030a5050310424040c000000c0d008040c980c0108038161008501980c001039a070040a0b01c41d020002501c00f03d40088e5045120b00302494100101001312502c82186440d1103824080c050380041d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 575974280 1250 575973030 575973053
    0x5030a1b0f060f1d010515030627010f020a030e0111040623070203070803070b10140103021305130207030e0a0506030408031e10030b090c01020d030e070504020703030204150c 77
    0x601426503d82884480858560103400801d0351032070f5610301c16020240d428040c10b01140c1c12480801160094207403800c000907800c0c0038079909a6041c945010051a01c001d120510128a281750b480d458403460202292000303001c0400b6594011402c00340c05007a090945000f00d5901d001440700304410072a2541c49007105410781080e6041d02c6040194441c1e2481c0f030b0152301800b075418011f000c400207240000000401000d03100710030003030030b035510211a070342071043c10311511018a500d1403c1d106a580310342d0007480f00300f24840c14550440e0710780011590584500110b20125580040c2500516801140b402c10f1540c00315001c1c0c500c2c604103c08255503010180005011403004008585a030007502c0c15102c04400c5a00c442c52246040001e103082d8801c10701c01078a01484442c041000310801040d40c204a15042e00140b4030802001070480c018003078140c00d18a01d010750700c030120b45560340d8002098014000d6901584460600103103a400348460403201303051180915600f00015480300c040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 575975530 1250 575974280 575974283
    0x1f03181a06010810092a050318030f0d2304080405130510060e060412060f0b060306010c120e031c03060b070309140105121608011509050f0f0d05030a1b0f 68
    0x4515101d800e0f1251000403406d03003484150100344d8020301d483c80e5011010358132404c00242040d0300c800d0180750403a00c81c4100c4158001810341002a1082804680c000712019460f41c0152641c900e03021602580f400000c0d02c04850304c80002800700101c3c6001c401827042520980010071007410072202060302100540304120a000003111880600c5c0d668070159001081501c40d00c51040b0309034a0310f0401000240c0b5406c2c1000c1c54284d01c0c00080c10000c0c2568816081a1550301c91148203490b083c156900c402810003c000080121000d0303a00d0511200000f0058070381800a05580c040c800b40503075180390070011400c00180700800209a10041c02070840b8a0460301402e6820310b071004861610501c12326040424540042c020207050b20396500100c1715481d520001310340d8032116440114407180c9041e00002c5d144400c02e1000746400d8515100c101c0b402080e002051500d00c0205002200003002590940c001189203d211a0418455404e81c020081c005172400360b103598044103040c1e0f40b50f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 575976780 1250 575975530 575975549
    0x7030b0f0f011814100305010b09190b0d0e0105130209010b0c1504081b030901090308090f120a061b050a1101090501020c0a050c0f1f03181a06010810 66
    0xd000d001640181c86003c2c0e480d03481942154800c2c2c59207061060501c042240d07501a0541041030221903201344601030507104128606442d0411070800c00203440403d0700b4203480340301c82c1e00c0d0029640c43d10600501d0856210040880c540c1c1504042c182110070003041220400c0201d100b140060780c52001060540d06e69040080c0c0b581d01c030b10140e61809940d10108280307250404184014401c506010307120480c0b0300b04500414802403380700e0f85070f0040014481c08609a035206000040c6d000e0f0143c1040d42e8040c003800d24000351500003d0507240c0c290204901034101040301c50a00009010710f0031075010440d8010b01113000341d04014036500c0f882d80a103080180c544810310130f400083d0030190500d07401034029502c41a2224101d40c554014040c00c40c2d05204942001800b0305044010307000010008105150031020f030300e052a0f2040c0400404001c156962510403445103004402a40540c027a80300c00707440181d1404c1d070313580000700a0500340c1400752070700400c0b0300c03c03090380c445009440e01c080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 575978030 1250 575976780 575976799
    0x6010e0909031204030e032a01030c0e04020304081b070302010f2007080d02012f090109180203160c2303040e091b0a12020616080d050103020907030b0f 67
    0x1114141540100e583c0356180b521070100780814103a20500305a4015411000e9500b42590b560b10344441b8814401c4110f10041000d98583c407560081c4d0082c0c4240703100c0e0030500c181c040010002012640700316022226030f0f20200308102d20018001c0c0701c0030951841002019a1800e6400190040d04207200300d4041183e50350751252074465040c2c0917460b0110031001c0b00da169444407009901c58912400740c900642c688643e40701080f0109000038400307054011841451070307070828809a1640300c08030440c14890190b000080c0040c490444c40a01c00e040c400060f201d00f08048000100b22038030641034200b04c411120000800d81040640711050110703014060620340b814902801c5000e9a400115512881000c008400901040c8400d014095811081010040f0010481100007602507503080258144849006060180041c0305c03003070711000d9140c0454000e0744c4050007513104400180b206c64031103004000314202020b075290003007100d0a050081e4010000440d60785c03076540740d80d24030402890 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 575979280 1250 575978030 575978041
    0x3030a0b0604090f09060f0b1c030203040510050c010605040c0503060d020a1208190809150c04050d2f06120c0c07080f0706021f0209040635030306010e09 68
    0x841100d00520b42190b0504c402c484001c041001000c0c2c5001c20354000342049441244000e06120b51481c040d001030034003d000310042060a00000d400d10108d05500c800c2102007400e030f90b400000824081c40d0380e507559440640107021030035184180d0005000c0c40c00c007071000502c250460306403907000509840c0510f82c08202c0c00003800b0541c8070350003500301800003012002840f4031500200781030001d0b41b810076030040380120300300d800a00441f95000c460300018002d4510102040c00103421104180c40e80e8201a200c1c0001540042d10000031161000ea03104040b40a0700300d0780c003d0815209000d00c1c40401415000030840034443d0f0050138180481d032400091b00031155900307a07a03c11a0407400c490b02e103511501481d0b500c06030454500d215120700540003643c180f0000700c80c60707401311751411303101543e030307041d0340c542c040d4225a1032181e02544401000c01c20201c880400161540325220b0300e6004542e0b810f5120150b82c0400c6980c590341c00030402c0200e20703600440100207926059415000300c0d40c0c0c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 575980530 1250 575979280 575979289
    0x71215060b0d0923031902010e100203150f0a060c0302012c071203020a021c121206120507050616082703010b011403070512010b03090c090903030a0b 66
    0x15001015600c41c0842c095080c401141c2c840b0f05860b02c508010215046404100e44020200003c1080a40e108001c41d001c0900c20003800ca95082c41400082a0340c01f071100c4140c10000e189104580c013507404020007826512a021001f450a02501d80e9004449500007184c0c0c0103d10b07015110a0090880103001010b00c00d6200000822403401046010007800c03040b810408007041c40700d610340c030460130040368403101c04103a00780180d4581c0040044407410360901203000c07100f1000b005415004a0b441c0b02107500040d9a4a10300f00340d80d01c07409000c810010f0307041211400e41000180c3c128144c0840002100050280161031081324030030f0725001e114800f40c3c1000540350008041441c0820352811a045104103000c80100460b80145184c1c000c000341402c035840242c81074005448091746c230343d5900000000b1034101045281c180c0c5481c00c00a541060340c042a030040c40303009070000c03c200b03400000b4440c4804240007112103001d2070809001e050350340d01025105003a202d5840b0340c2c0c15002d984 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 575981780 1250 575980530 575980541
    0x3030606080402010f081f090605040608030301060e040f0615030507030c182d1508010e0f190b0a030b0f06010807080c030705070209041118060a0b0f0904090b04050f071215 76
    0x20b101c901400a40d108c1d2000740141400d4410940114141103012544d00c40101c01c0d01d05941a03603440b000002035000400001d09000c4540d400280d80d078040205191910140810307840219031408211400c29150060889440f9007030642008041d848101c6000700d0f0282110488111440c0305c4107201034101c5109050040d150320030a8030410000015580456000700e0a0800203625100718a0381c1e0741888640589045522104050f09900001d00b00d02c0c165648011921441c0741c0007501c031203911302103100d030102a041607442c04084c008000285100c26646070b03200c5400c0c6461106410041400380451401030000303034031a05c1c00f0001540c3c2ea03104006503289142c0040440c602414141800508800365501487c010f4800300072841000c0183c1589502410000e403910f00500d10303280795620145c00031480300d0300700102009a40910f40e164020154050b0190780d41c2e01650900749080340c640071b00704008408a40105100300140b00b1480200d01049410044034074aa18480c3d095000030a13 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 575983030 1250 575981780 575981821
    0x62007050a0f030605090105190911060c150a02070201091203020c030709020309010c0201140601030c0306030212010c1815050714060901021905030903030411060f030a0903030606080402010f08 85
    0x4141c040001200c0c81c258140808490042c0070070032103600c13121042426140e045404008054040090084008d617039031040040078010b9050040c128200e200091460780320030b4411031641d0113803d584401210009100360820101c000461a1030f07443e034000b90010480e803042d070060381c0c0b21101c00401d140c000d00009680c40e00c014250b5440c4d030340787d10a1100030f40050382c808185611700321400150314014454600c10651a9044004a50341d0500450142c2210b000031810584c50300000001a107034920680d150342c905c3c03030000c94001407132030000b8400381155508004200d4240e200300000403100035148a814640d15120f591200342c0c4c1407804035201800d00b14006441080c080018640066005c0c2022100c1c3c0c117030040b504d6018440c100d6142c0415070700c1c440142c000f0800304000903818002600d1700ca001030308907030601808000800c1e00742c10440b91110802d4958580c0c3c0304140e07142c812032000d000d171814a2040d47c2050b40000301140280d075145420302c000030000c00d40c544441030344181687e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 575984280 1250 575983030 575983039
    0x1401021908070f0b0a050114030309010801090b010c060212010302100804170901052101030c120c09020307020703050f070f0b040e1f05041109100203040b030a0b27090c030706200705 80
    0x14100080002c5c01003409106004200e0202858500c0900d4040101c1d030040c001695401da8a13401d0010483c02002000049170603c6086124980081c0040c0090001711440701e030f1441c820362541c0140020b450840910f881040000e008000c0000c1561020400403a006814940c0b07504e02200141c07414410050220002260000c01c00c0c0c0710b00007000400d0503284030b1a01010314079680c01c1c42101c642c28003840106131558030708050080c110a54043c50340010340744100c49059a580e29a50305100210718082c0c80340d00a80801c0c88480c0300044c11400403c6030a1301c05190901e4904116240708010f0401e0403902c404003a49a000819101c400b00a0403004000300b041080c02e6100910b6a4840703000c0c0c0d40900d011520782c4101c0c41c000310036181100c0b106440036255a4460821800074000040110b600920075880c543c00c2d400c1100004900160246007440c4505144170942d152203889210544250700058003800055030064400e80300c0380d03042003410381c07184000c18514107000e41e81e0407c42c1c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 575985530 1250 575984280 575984303
    0x50f0325030b09100c030e0c010813020402033102010507030503060406150314060a030302070612110f0315041a0609040207050118120f08060904030216060302041401021908070f 78
    0xc0c1c3c140413841e82c0070116400780c20054410503001c16001e40320300c1c52040c03506800c044e441042c3c1c0d5016800d050390150290030a054860820350008007242c00545041c0c0119081c03da1640541000c0340c84410b01070103006158044031101d42c0000c20381d12400c500101006800300c00700341a030f1500d0b0030510240c10300c0e90201000c4120510014021b01e41c03502c03100c148501a40100389641401d030b40318402c1da41c0503030182c140c0d1420b21a01b9950340c0018140a580640d803500041c00402c0080040c01c50420881480ca0381c90621450070508070190308130b402d02c680d1605495036040342a40400000640c6c06480ca140c540c40c044001800a02600c10007510135400e00b08454441c4040c112011405845a8070001c0c8140d24000207c5103034280781d2009002c00c0001d03002c00da440c50321103003c60703016200303104480b1169100d260429003400980d03c20400309801090501080d440045a04040d000c00c0c801841092022004064a050803883c0903003180c000140410a100c07a642c100e42d1059000800c0c05d55 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 575986780 1250 575985530 575985541
    0x21110c01060311010215041e050307080412142b120f020706061203050d1a03010e1e1513051203070c060605060301080c0108090c1009030c050f0325030b 67
    0x3c0000d0f01c07072050790044c01600384200d881006007070b596000700d8100300610140d8086107100c2500000d55082030300d241c4402e000690006240708018006401051395081c1488080c0c034014036035051041c0b0201c40c5400104c0c400343d0340b04081004d002c0b030403020254244405a48081950f50b000c184030342d80411400c3c1030311102c5840d1540c0042441034421b0b41c040248a0f0340f05001c940c01002410003d0026504200c03202d5124000e0708009246070845118101442c01c240c0003c0c02c4800108072040190480c2c00202000f01c030030001ea205104070f03030b0050102202a00003400d107001c40140000f08090125480340148041002010440320b00010101d0784d03802c240740058100c00654108540e91820b0150100710390400d1025207049404d01c9009208a1550b1001901d9001d4024045c8119114401c201440c070307a02e601030046004003039161108400c0c154200b40365008000c3e0422402460034140030050b40d140000c070210742c1030740a090103544001c50307907640c1c2c61248581c0c00907054010103000d006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 575988030 1250 575986780 575986793
    0x6170f07120f140a0c020d26090d03050c21090a0525050406050a03030507022d03210406080403110a0303020918040b060d030306081e0d21110c010603 66
    0x2e12640d450f5000200c0c4c0c2d4030f180700d40075610240c64071030058001421301d0481901aa80035044400c01d10041040e000f44440d0b54414450222854035150f40b003440c10030003240d014032038280c0207100d00380124501190058414072400c116509960740805c480700048460f20f003480100c01103540001600c0c45598071140f8a441040884820204070000725030004280c5000d12542d4103d94018150110140c0b858400351541c0d00641410b9030095451403d405482081c001c1b901d102265060107085412211414036240c0040f804c0e40c002c201200700462490855005c050b14210b8185290030740d45a52980740c220b400d80145070301c2c0b221522620300c18070101078041d0040e00f4500740035030300c5000d11900c500006040718010703940034284200100100c1d81d5030821a14a040250003801d020030384c9651176006501e80105941c03100b9180d001e040542d440f036034080c802c43c82044160302d0000d03854407890041e6203802c00e0540950a2040da0383e6840c1701030b0004801955100d00e8404020006103a6a05181 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 575989280 1250 575988030 575988041
    0x15092312030c0114012403020906090a15030609092303041203050904111801050c030c10140f010e060d110303070b070801052d0109030c0306020c0706170f07120f 71
    0x141081e03004c110000c59404281e5011041861140308200868140302c1400d40c02503015855040c1c0051080265925070388030300240100a00d035900b0100c00282401e80020300f1103d040c0c02502c00c403030404050710042000da02c2404180b601e490030814203103c2021810340b40d449240e01c07440c0460f00c040c150300c0606030884043c0c14510010784081c00084c0440c841142a4800c3ca01c00d04020380d5a040100610f5200e50050103049181e0001c5901c0c090204003440d02e005050400c4204164035000d80c0b0008d4404102c046400c0040350581040039410710209511540c1c004003091b0080700700c6080803041c451402001c100e43c590160a603a910803590904810944088a454000c00c01c0940009001c0c10014100710f0b6400d180d108840c00d075a030f20079a0b82c5504241c5615281000520840440842c03640c2864500651041c4001641c5401880449040003103d038407000a1122880345012004982c02c1d41aa103d00e42203800303902d03507444c0d104c09c0e5082d4010b0035999842c01c0c03902504490701d42c09035010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 575990530 1250 575989280 575989301
    0x140f0d06140c0901021902060417100b0105130b0f12010806090d1407150e01110a03050606180f040e10060906050a030f0b0a0b0303070c15092312030c01 67
    0x2011901d540340b50703080403540726015641c2d0059100c60340e10200c080f050100c0355030340f030710003403a4526160780d4030440c0c2c1400800403001e00b0250406401e00305080c802e8031400031040804e0808908000c026034090b682582a48114260864001141840c01c0200411116074910b200f40c043e21a5031281480d13587d90500310703503103400703441940ea440080b14080d6070764004640c40304c030b0914903001103607956030b02c4140383c2036000180300d44a070701906410b0f9003800390451400d1200d402079160f0049000040540308080d0196000e10010072040c0c3d4003000050804c500c1480650f000794001403004041001004a61200411805104807d4503101030a8100c98121076003140144451a120350802034080c41c588802407040c4c44000305440020155841c05600c0340709441d0001c0c8070407460000c40d00396808000120f0780b812034684140892740702440d5824584ac51468290012400c20340f002c3d0011003078516141182e000940c0003091075890a0218440c9504007050300c2e110400a05810b0203030181146 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 575991780 1250 575990530 575990561
    0x1602030f19080912161b0806061008090d030908070b2a09101803050604030f080a0b01120b06250209160c06051308071202100207050601140f0d06 64
    0x3c90465400080c1c03d0b24100382001110b032505184001e00d408840c1984001c81d0100c1c0c01c0400186091001403140c8001e094a20162000d1320300941008008003151140005103c01c803424002808400220500301007000d0a0000e000206070400c90800e01401c44000c1c25045c0348010807129100810541441c0390f4013217020f20080c0301c540d00c030140c00d0040740d14280c2c10030316042c0c42094140c4201d800d004076a2502a40305c0d01f2030380329112142400002c8609030086038a10700c0c1803c0007540004401e900c800a00010441c01c0030310b6000825102c02411400111515070240e542696070760360844000c1000241c3d1803001011010700c0305241c401d8100140e1055800c00c0004801c8050310f1100240c1000355590442108034a55441004080180c080c059891490040b400050510401070a0301c0e80100b9902e2440000118020b181c044500400030701c207401440f00400041000a0302070560303c4804c1e810004610070b00c08910b02e1280500507541c002c0003202100d0234000700782e000180c0d200043c47c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 575993030 1250 575991780 575991797
    0xe13020a0603090506190b0603010815011a0703140405101d011b0803040501140414071e0e18070b0705010614210f030d0c1707081602030f19 62
    0x35000d40480303c900c81c000e00250400c00000d142d0143c1000b00e03580e5116041000600e01c0d000d4004140360790801d800241c000d81c0490360b008802c044404c066070061000e51001100c0c00403040610207107010f0001c000f01403040a10b00d0a00e0981746005032005024040c00304031204000d40c500401c0640a40d405c102042402c194403400c3d544200c4007046c0c0d00d48100d2503004110380f9503a48115642c0300034800d56995580e184500111003c2ca8030a9000e2070140143c00c007a039003120411410680c840d40400e00c0301e65031004201d2241c803445d0000088694150806c01c2c56684d015444c5078481d02400c1c20041e0b80078010b070106103901c404c40500743c0140950000c00100780c4600b100d005004101841079400000e0079941e070351003a00701c2e9024100414100540e208080340300703403040c5980c100e00080e04070075403141440501ca560010800482a08405100c072142c200240c01030030080300030300740c0e000116000031010300980c02002107032803000302c64080507922407100c5d0301c81380002e450200c81070010f01c555 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 575994280 1250 575993030 575993039
    0x70c050a060504090902120124080313060f0306031502030f060d17090f0a060201020415020a02060d0e030702040e100e030708030406150b0d05060f040b09010b130509190b030615010c020a0e13020a 86
    0xc151070744868000c1c0d01000142c140001941e568080723b0700710081544440000c00004d440600f240c050036a50369016031641001550b070702c0240001004e1074041c807902c0e81d211380070550383c030104c610443e001559940e480d89280f01040c4d040d03400c10307034075030f0083c000c01d0300001c480381c0c15801402120100070780c0d42da030701d00854000c03a203030111349401950080301800300080c8025150321081c130070107100302183e1400b903840e40410142c68090b40c0302030050704165010400499140076402d018091000a1480d1201607501d6203840d0002800141c42e09a5501668000581d5450307140c0c007419680d5400303034840003a00706040144c10100c0702c0c5401920301d215805958203082c052940b0100d4010000c58091703080c10307010300b1a50008a10465118005800007074a9221b10340d03000d001c0c24640620100c070b0a03c411608003600c404105a0740268171900c200503100411050f0841100800d10308165110350030b000040841855810400540382c420080c00200c1d81000301103080c40d4401c2e28924040c0350340c5c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 575995530 1250 575994280 575994283
    0x60b030f16080708100816150207060503130212120309011d062a040308030906060f0604030b0a2703120e03040504020706060801050903070c050a06050409090212012408 74
    0x1201038079804a00c0304404100c68501881800d9400070300c04502214041c1d48040700d81c0707031403810484481540c801c030341c0510103618041e400714804289400241102482c00000601c140300043c95101662101c90b041000c55990300502800c04c2890700480d801445d1120807040e03203910544450340e513507282c0310316a4100388810328030b42d008001c0f0030080d100030392b41d0007255655511103894016601c40a0301d2010341c9000d03c9405800518042c8001e56180e2401605592504001030310580c4545507045103c841a0344172002c460681e50300001440458032a4280c07100507040552164110b01e11400450740340101301b04150341c106020f40d41780d0855007228a401003c561103c00844410f4108003c2171000342010340052076450702c5050002a0341d503403401c4007421141e00790381c80e4046800010b40300d402d1001c410b146101900c800c448d0213121031b1074410050114425845039103001910b5159a0095551b00c9031080725103a100e20082c0b01810b02020300301480038082076034031814505d240012411580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 575996780 1250 575995530 575995561
    0x310050d120e01020124061119030c0c03080d0f1b1d060702030303040c080d030b300604060501150c0f03050f0f0a1d030f0a140c04060b030f 62
    0x40100121010007000042221a5800c07250818195034840d01c01e00f01c3c1e02003010103070399102e80380000103041c9401c2c5040200702200c1e207454050310b907110a030340c18a244405a178502d0401ea160404603059852841c000900300070303560001c1c10340e65010402010710f6083d80c0110300c0c400c0b2045000c210000c8907048006600031680e0810001552506200d000e0b8005503140c00703411030300209100c2c113000ca0b0f5030000c1c0c41c5900840e400ca912070901241080702d002c042040c0210b0300c01c1420188043c2d140b44012804100c0c0c1c2c001950110000d035298150a2000002d090054840c0c00c2c0581b2002c2ca401e08101014000030310407000300080c0d145110610a01c10b690542c511544802c0c0b0f100d080381c241c1ca0031110394104195540350340030108220005d0300b45000041c12080312507262801c400643c4d402d01100d22510301d1381103000c3d4100c1103400500400104210500e16440f2541700700b070b000700d02e203d20702e007030900e00d042034100e860304602080240040b1b019510540720041004501c1e03485014401441d038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 575998030 1250 575996780 575996783
    0x3011520070302091e0612032a0f06090a0b0a092901050a0503060f0c0c07060e010e04050114010f02030f040602030d0e07230301020915090a0b03090307080706020c030f0310050d 78
    0x40400858003070302d084941001c04940310030448c1d00740301d5090408103481090000061041168140b0010b00801c2442826803442000740500f0f0700e85001d81000e9150050360500038244090361000903d03039403055200781402d5070400c0e50034540011014010341030301c8010824814190700900001081e1420010b03040588201030003030070f016220f91424445078030001c0c00150a1140a00000310010010003c1c400101120b42d280c05d104101d1900242c0344070f0780d1040720f0303028504040c010b000415030b0f20341c0c0281c02c150a1804045180d48100c01324114001c010511456090005001442e554004043c00c072800d04080b0400c80c80164040841d501c011070310805d00c0700c00b4800004e20780e40d414140d621802c66406400503242070042d0001501d90603142c02e007602c0c40e031001b00d68018a424660140b10160034002003107491420242c1040340e0768010194014100800050440308004580c1c06995082c022102200e40b00c22850b5882030321504102d0708441700c3c440352040001e99240a42101d0f9902d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 575999280 1250 575998030 575998081
    0x30f0709021608070f0606080109020105040522060609051c1a191506200c150409020f04060f09060504050103050c1c0213080c060301152007030209 65
    0x50300c0d059210010790005440c0045910203040a0b4000c951100000d00d5400d200e0740e503003240c107159840d2003411a00207401c09603140e0b24105036580182d80250455056800446503111808182c040e0300c249207121a4401030614104500007411030380000d880010313a00c04881c4e1090200c0b81c1400f4040c0c071142c5200c09894096201104d1000425210321950841c1c1011101072030784103102840016201480607403419001c10b400704202069202146c4100b1000c1001c02c0042ca0404c00e40340d5542e00e0702c0e40303409807049140624003c0c09825540440f001812405420b5440340d411041d2410340f500030744184c10209452511b1081c155118484920039a1407031b448250815091100440003484020185500348101f00020418841d8441840303d0290b42c20401584c0c61000610003520800d440d0300a4034217030301004a040345982c540f01500d040d24070100e11030040a4040d00c04807041d02140040c015030105045124442c0000401c600007a01d000b91078a20741922900d0700842d040754098501a1314 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 576000530 1250 575999280 575999293
    0x5040b06070f062c03070c050108040b0403030b0102010e01052412060c030411040905010b011409061b01090b090c03010524040c120f0614040603170702041418010b030f 74
    0x910f00354072054a21030300640d150344100888038801c85101450b544944654008640d03641002604000c50024050070301e0907039858202660751220100010b0002000d042e110740b10321907164800d6002c81c40c407451110090195081948040e101003a80782960703404508448206456410042c0080c0d50001413540204000d940b00d410300d03400d40c2c10250040760001d55403080d5003413540c0e49000300b0600701d008034000509501180009003000080c03190305a601c080500150300227a6414041d1429080ea40070741d62580c0090800050051240c6c00c001803800c00c00800f480b1a16500003515140820168003c01540c0c480d0110000c65600340e40566070a11260701c1c0401e15400c090300034140940c914240940b008202c2d1f1101e00c2540c000c6050900c3c4640d4400e0104041d1020b1407007050300440c10b542c01c01200e41540c54600340d003640803002c40c040f15400204142191580e5000703040035024840c9481e42414251000034442c042524031092540c289101c2560307034603002c40c2d04200d00c0341c0100104003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 576001780 1250 576000530 576000533
    0x615030a0b030a08040303032418090c0305060c192c011205090109021801030812100f17010e06010e06120f120910050906070602031503100605040b06070f 68
    0x1a0900c416410b4040c040c0402c94000108040050409988a92000f00303032801001f4440c0c0900102070744800d4500d5201c0020000c016145075001e010590038240802e6010003030400c119900c000c0ea0000305a03108400c03c01c100b10345034002901d1007040c000080c0303640542c0c00c0c0c400c95442c240301038000f09007400301e040c20988203660804c41d0b4072103406040c1007400d00000d50341101110710403145801180d44540303c00c01103182c46175402c40c0404443c804481c0320350664072100030302d00649043e43c3d004003c810100d40e07440c04922960300200140568442c4030354442e00109070060a40c0c1454030f10791b0030008045802240403903814142c03011011981b103595100340030848051200b107402c1c2c529000304401c126010304240040d500041100c00c805540d04034100501030303004e1300f015103001003082c00d100d42c000980c2e4ad48110b072915a00f22901580b079031120100307180003440c060074181d8188914400b049480409400100c11600704460400030000e403d8207001ca01d01c9020b40c01011684400703403890 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 576003030 1250 576001780 576001801
    0x209010b03160522060e180f010501030507050f0a05040e160e04020a0309170c0d02030406080105060f042c070f0804020d1b03050a051c0e04050c0f1809061503 70
    0x4100c1031000c821030200240400c0d003184c141a401c07050025104000580d114103154058100f0b4038242c1ca03094034940f0704030140000317108060084504040d110000f00780300707034403440903540f17101c80410030141d40d011803001c0580725500512580c040c00c40c041c0c1c001030914101528000b140701d06a120712003000c8500007048002c2d4450094103061583d00d141304c2000c2a1b00611203020b0321052560310750b48442c5121007501c0c0640d402e0b2181d00f19441003205201a03175016040d5411990140c510b40d45407501404620918051a00032441c2d0224814889454218a2002e07841d564010910a8007580381c00408491a44003010404045100c644c0814010b0070030305a25240a0b02414402c9402200548080100182a44151616409010004103100d0103000601e840340b015100d000004140742406081c2c451217903541849556900300140360043c0110440d41c1c40c082094142e541c2c0e6480440b0f40c151440c0904909001c2c6001600081c1c0908194400080b25543c0c00701302d0341903695284044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 576004280 1250 576003030 576003037
    0x50d03081609080f030d1413030c150c0c03030614011b02030a05120c010609150b03090f0706020708011506090312030b091306050603120f0919030f0209010b031605 72
    0x141d04010000d0000540c44034140b260200c01c032228070295a1300d81e52841c03520140c0e11440c40c1010481c012030240190144048032940495500d0b0178080b02c4052a41819003604e0019002c106c2620300b0402e1010f22564010180c10034540700f520200301c01d070b489400c4000041035028115003c141540d070340b460040d0745901c01000c80f40c402070442c1c0c030003503ca9948a080c1035100c808000d0100c400701c0c020034102028024000500401c142c10400c40c440d000c5410441c80c0c04c1d101e01103203c4400004203202403810710414644124007401c4400c01581c0e603400a50f260410303c144202541f03001702c9020380d0390304421801c048418076602e4181040c2592101c0d00b2140d034003100d0b1f40038541d0794180300450341c07240f00c01c1c40e100e50301d0040d0f0b4460120642c2406001d0701c1008165503c00d800c003003080b00232180c44d102036030b0092404030f200741e45440c40c041c0810107004800300e0152031400d0411000040145008e403c4405c240300761114911641da803030344014140170503600c00400c0d52060b2181188a845074018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 576005530 1250 576004280 576004321
    0x403031e0615050c070f08010501180905070b0315090f0613050f07140715050105040c02061b0a09180e0708160302130f020c28020612071808030d06050d0308 69
    0x26100d83c540d1b0703050150001c1010b64400c10069444800410029144000301c0740a00800c4400384005d089540c0c400703403511014004c3c40b11111003c00890040c5a6058203030f121200068118001401d101c01c0013042c61008581c0d0b20b04c2481000038034104c01000340529402801c1001c81a091030b00d5409050340d03101c410468207840b48a0920080f1f01260a8070883c001910606d500010300c0d505000501c029207620b0354440c01594015001d2250742e9028000749600c3c028030001098a4030b000751001c48400c1ca080d0f010702da01050f4990320344806c8055030b03c4a01100c6148048982c500d40e640c00054075403d41c80348022031164004002c20240c00c3c400d64100350f140d0031600004400309180c203030034120b0b0003007030344a840d03a030286685000d8407aa088a980e00640c092406d40f00c01000c07035000072282d00c900500210303031154070300104400030300552440340002000802c82d602c141e2030703c60240e56a080b961418043c9820103200240c0c0341080803038071540c150550398034803007a920314080440c0704495144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 576006780 1250 576005530 576005533
    0x2060d110301090b210a060905030904091a090708060c0f130603020c06060402041841060604030f0b1f0603021210050303090d0f02090403031e0615050c 67
    0x280080d0340044a001140a414207030400200c034004041800740804250011030030440c0c9900c5030714000d80c1c00058100e2083d40c0701c0008503100c00e0340d15207542140105000f45400601f4101d0f03810811906404c0196010483c050b0248965902e412296136002c1e54490201a500804007140c0301b010b00704018852a880a01c0d460b02e01507a181c07180302d2040c140d60003000003039404142d100007a0005c1c060f0a400c000c3c00c8a05500341b40c1000c24412940c202029000c002a03903e0213a400c06e50504507000a50001060150b101c00386001c540000c941100b810a9070b1581131407002030300c036141c0038043d64242da0300f18440914114065030348102c410000350550030100c8410101c402207071400807040d0041c080c107a07005070300c03044580110f4010303420140c02a940d00408003800d00c490f490000907181d400c0803c480480c0003a00328101161580d42c819000b079007004900040105064050b04081c1440200c403098940c0b1803002460710f01110424001d2000390180074a02c030601502c03c4c3e0241002510080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 576008030 1250 576006780 576006791
    0x41211153004080405030d11060c0a02340608090303041211070602010c02120415080403170a061a0c07031103030c1b2403070507080f0c0a020f0f01080402060d 70
    0x14654030310700c0000c40e811950110700040030301c8241001d1120103038040107820002c0000e221038240980f100401003040b0320f108008120001502c1c420805003998450381c0707007103000134110b48400c0503020320307201c0c4084d83d83c18500e000001e500d449440b4440c400c50b9404051030554035241d45035200b00e0710402410040084000700e0a050382810b2101100404c004c1d00000b55640d081c40c8049d0405003103100c4036041e01c07c00d1000300081c035080613006402c40001e1810a64070342d514503054480c1f0408107412400c1d14440c504004083d079003036101400b40d0f006c840d561428030008001c1c8010911801502d40080c4c0c006039020000151810018180a82c004055a040c1b080d18081e05107030400c4009d841491a011050004503410b01c00b021001e44154100003030041c07810f11400c46800d100140154041000c0003540106000da030506450f01c1030390030401169130b01c4075008200d035951981d00e002e91285401c400344070800e1800440b00001c0e1030040e103412601c2e50f2190204203154100300c80c0741340031903140c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 576009280 1250 576008030 576008107
    0xc090607060b101205060102010b010c0b09031201030c0e010f03030516110d05060417030402010c1407180b041a030712050c0d050f16030b010902090d05010204121115 73
    0x265400d140901d03d507882c01190b05142e0700c54415100c0142144d81503900d459902d1501e43d80c028050a8040d400030010304003600c410807114034500c207145040d401c00413410000302c2080b4010810504440300c2d0144608944d0300c946c40038586010903c00200450810894400d02450400c25402141d000d000341c81d421840d02c001094280000076000c40395900700008010420142c40d181c0200403040c056001c1c114640781c2d0018110a040540140c808640b071101c580d900074003000000d001e040d90740c18091820100201c00c00250400c2ea0166101b81e041140d4552000192013110b5400c10005000f05003081c0380060130b00d06014501c0f010b8400c0d00940b01d82c0e10150b152030350200040361082c0c00800c00c100c2001c280c3c9050290840840001303654070002000400c1d0401d902c05d0544040980050741c03030001d000040c008030811600180b1740c0d4004200010020121500031030014080c8582c0e07407415070990200240c6807140045454680b00a00601c0c445804000b50008401c0d440c0c4104c1c0c001e030455 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 576010530 1250 576009280 576009289
    0xd0504150c0507090905010e030f0a050d150b0a08060f06040b0a050d060e0907060203120f060d0606090b0a050a0513110d090c15022409070f0b04060f080c090607060b 73
    0xf0750806a580c5460300e0100c8200802440b852006625690186007084804082034403680300b800d002104020002c40c8012400d045c0d82c0c460290281c4a0075010202c964410f1032030380d180c00c0f00d0303400004500c03020002411410020710510070520000c245a1074182000c1022125400004034131003003150034080700b010100076200340005400500440d205c20b280469a4618003405508102d085420500c03442e0468929002070b03d8001280d262807854030b580d507102082114123400170217002d60381000340000f60b0840c9680032000140c13090360725205035912801800601c1c0100d10845810091240703102085005681c0b2203041e1141d5006440c1c45c000c020003000b41580c01d00314094441c034030031410800000c80d04035010600f00c4c519002501102d80803080c85448030300041401802030301038400140350003038144a018080d24101d060411099110300191055800c079004030307004100742c0300b00030b40310380d0041941e0703440b070817503040c0c11803070104d0b5401408141d800c2000125115500d54030441e28946d127 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 576011780 1250 576010530 576010543
    0x61807030c0f0309152f040f0b0a05120703090f030e1e0112020a090519060306052209031e08011409040c060f052704050a0b0d02041d1905010606020d0504150c05 71
    0x4025182d47c2d19182000f486e0545035400d170b4400244035200f003112811240e0000305640f800c0d216001200055a5010025009007610100007050306060399400e81c2015040303600b440400d4010f891001503041000020310780310303c50f4005980440c03c440f1384405001e80b00d800400d001042450b240000b281c0d01c2d0041021042d01e418500c02070103034841c0c1031081d50b916120340700003030200301e6806407114001980c02d0342d054801c1c0c401c90f1040d51510030306000d05003c0c02c00307004100c8d1003020a103000d6000310401011054280119126032441902001b450b10300440303114002c0d03400c41c102d1145a45000401c1c0c4005903064021402e01c5028000100d6401074060110a54000418080386e01140241003000b19100104000e1010b840c2040381d00303407500c5061007c29220ba06440008000482013035090645000481c4840300b449005512007010200181846c45d6501c40d0000303025481e100c030b40176a194003680780140001001404104078403900e2944084c20004641441c058061054071000d04060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 576013030 1250 576011780 576011861
    0x110a0303020304090e0106120b06040b1e030c0613210804061e11030d090c0302040c110d2c04090b070504050a0915030b061807030c0f030915 62
    0x2c1010808002d559014081c19100d003040d0f8008000b01030804800040c20300fa2a080680211480000160a03484940c480850110020004c04d031400005264400f030075000f424807030203030040511500c2d440c108601641c1840440f021a66850350810030104901070b108684a41a07800c0e480411002c00c8145000304050641503480e6450056150007102064000c0311018040140351080203400ca1004025508004400a0701050a603407070304140310b41d810540c0010b548286450000c1400704e8000326920800e011003001d07140c0080c80d21200b541d800380540c0b041440480180c00b8404003125141c00c10380e011000a0000550145680b2044000c91007103611802190000038103021500d4030092100040203003510611006084280d828460b0006110051503900800c1c08607005595520303042044091400c056801071a180c030f4020702400a007801c02010904c0c0e0030308246418424003c80d070149130040e001d035068504406000004100c0351500c01e200c5070301d0310b1010b001c2c0303551070310380c0c10004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 576014280 1250 576013030 576013033
    0x70507031202010212010501081605030601051b011b11030717071514060a06051b012405150403110904030e031501230904080702030c06121e0c16110a030302 69
    0x1403075045e0300e5030960801038001c5070520464400700000c030010700c1c028140b02a464039200b91a9140c0e280184c55a0240010407140200c2d070481c03803a00040158016030a100b1886044403c044440b0b81c01e40700b5440a000c1000190820020700010814183c43c00c183d40e024440d00914088654440e45d40c0d00080c5c0c103420080c584c9800e240c10541c1909080741d0740100c0104c0350755205928144005d080c500c1100080580c4200e840f030000d81d60b034420350018000900c070f600a058580c02040c4038120025050054600c01e00402841e0540040b4580c25034050703942c0038640c10000001241041080e040042c01141088440d40014006032814404403000440305054003005504100801c4080400c1d6442184030a440140c11000b80e503074144007580140e000768445a4510761400842c0c1004001c44141c1e802800015142e1904450100d00610541d1008803001a441905084038940b040c15a848440040c00340968800e002c010310f124920648610a480301c106544001701381d442071681e0056015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 576015530 1250 576014280 576014287
    0x2040b0c010501080105130b040804030b0f010f06020a0c0605070c0302221a01020d050a140f04180c0906050f0705060a020c1501030c27150515120604020705070312020102 75
    0x6240c001d02600f4003501042009004501c4c0c001250700203018007901c007070060180000868240b001d0181203401031038100440c2078007854040400c00c2d42440038032401c8121028a01d000a21074404100c900c00c2d1940040c8449944d03280c00401ca8642d0010b00050380c0c0c014030844004016500c8180b8841011410b810b84074180021050b03010071100c20401d03074946482c000d040000c8c142e81c007150740c80c01c1f01030343d04149489078441c00381103504900c004401c2e080d4120010b03042104814460207001207c201e1f00443c00e0f006011981413096640494884000c11100b1100303001c4030b4064400340c050b0141103010241420751607203c1c40c0ca40a4240c0712040703581c0d40041d031030079a00010302c65503c03042844158814654910b54034071401204501c210740f0340d14907080c903502c5106403c00c01d00728a0010a24184480d450502c61041034401e58480c4038403510010700f0703441c3c0c40c0a140003a250002c4c083d6401d0760540d41c6100511000c2c2d44071384000c41d050b01442c9408130001e40034a40d075080d80b510303a500060310f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 576016780 1250 576015530 576015547
    0x50c0102091e0a060504080c01050f1303060516030905070b0c0312040c03031803050c1c05150106020d1b0206070c1505030108060f090d0c0606170609010c033c02040b 73
    0x5000390f550300461300f00718040000344038140e00000c1d000b072022000c0c41d00740d950341c07100f24501e15680100d0144031482c80307020b13130000140070312500071b07500407440315a40c82c1d42840049000d500311981d00f9002041a009020308020b881d0509000c1c1004103a40c10903685485120b070324040ca0000304503412502450b0800d0180b0616620071203941880342c01003542c07410316003507889090b0b846014034803c501c10318800ca8200d0300c01d01c40d0764503a0b403115070007022100c00c950800246c121078082400b92a0040c441d55620407215071180c0c2c2c1801c104d841c8846445d1841d800d940922420b03510000003a502c8100750100000c5604080c00001d4680302c00e56107082c0c40f941000c020f20b0400c4030240400d12602c80540502c80c40b41404121b40031040e40354140b400f8100118685a00a05500e50000b424080491412440034001082c11031046d40100d000300700484aa000550885009404150303c414042c18408407a1f00b40c1925000b81543d0303546031a0021a480074000c00f640e01c550044038441402040040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 576018030 1250 576016780 576016789
    0x120f0d020114010f0503100504020a15020102120c03060d0b0a0e0d0f0e010804080901051303081c0f050907030b0c0f130504050618190f02030705030405061f06050c0102091e 76
    0x20f002d400c00c2c0c40c0c0c01d0115403820001031ba581c801040020300c0c10340c0c4c03640410110340d01c2100d450014181e100340d1100b21b10245a0182c001d40100c50742c4c0301d0500d61000025025154001203e01c2a1801030140017090807640300e039002c800009000008407130b600e4200d40c010100030400a5409007080c0e83c7d049042100000040c42200707e50981070520290700181710005580f0f0050325000304080c68083e8a0301070b0000708103404040d40e800a0040e01e40000c1d003100420b402d2000e110305905254090000c007070031081450446804845a96072a040301d03905000003940c0c1510b50343c1107100c03240102e0030080f0300101c4030a19402404042982c014000f010002c0c3d081900a10703510500450700d2540410030b640850701034803402440d01140500d0780144140308803031507002c5400401c40486c01c645920b071200e80135240d54416241903c1e184101030000300e003408403885074180e8407001040300d17048501d05032040c0c41e02e400a001c080c04c2d0395000e10015100792901d00e1040407000c1c1481c55851229010030620 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 576019280 1250 576018030 576018071
    0x9010906050109081612020f0a03081803031305210d0509210d0f14030c0c1207031d0f1210050603010606140708092e030911120f0d0201 60
    0x4005640040d450038012028030082141107403841241b00049801c01d20000e80c0c1b4403c4141031940c440310b041401310601280201600c0002103e150710309540b10110f0070076aaa008000807030140e80c01c644424003082c10541410081054058440806002d0811015052884840c8a040065404640402c032803401c401c03c00c10800b05030030f620f50407560190000d0303100d14070102d00d0002c1c0f0110590026075984200c1504468507400e60040e500c82c28072003010042c2c5d03440721880e02c6040c415003410b2502003400c2d008881c95107516441e0001580455125690030219022805501c602c440c882c964540d02c44805003643d0380c4078032000c0d100010b200c101110440740040e00560013a071404401388200e68103c0c150046c04407450b1389142e02c0d00101d240c03000e000d00c43c90100701d4204100f17016030f0315440c0c40c100c5a003500f409940c45802c100f20b20800100e044500781c441c0541b07500c90800c1103030028113103503040b8249140c1c850140c603403e00480039403030b10303001e014004c11006070740d03030b45002c000d24080641d09d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 576020530 1250 576019280 576019289
    0x1401080d120b1c020604090204060306090c020f030406031802100806010f081905250504031e0b0619090c050901020c03060106170903092116050a06050f0909010906050109 75
    0x41002c1c07140c02c408680d0f08550311503c803110703c8080750070800355a80d00090320000d01c031006040d507540b0b8444000501621a80c0304103903002e03040c9405180c0f0b46001040b0210300406106c01141404e15019044010301555400700145605044800006d0707150f03000300d90b21000c2c0b283c0311054a824000001001c1c806001880d204000b26001071103101910383c1c5c0008091004010042115200c12010034880c112151500c421074415120219010750004090b000300e074050f48440364810015004890849000e0b4001081400b2aa000400c01d16012850000543c44c0100c101403103619480b1000481d410b143e12900450f20204d0380c46025039041011801d825804e8000c1d10b85540340c0741c4040d18418226500c1300130f001440d40002d1485804200340c1d440300c0001441e02c02c1090a2007400c51108a0500050300703240566820002154103c0d0a0401118005065046054a008000c40d00d68201c07203108080c0c0703501000008081e6681d5588180a0100c5a00004805180400150228400381d20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 576021780 1250 576020530 576020567
    0x12309040507060e040225140c0d020103090305120c04090c110d0c050a210806040e10111204080d0b120a0f02010509090f0a05060f0d02040f1401080d 66
    0xc0000003500802d00340100d988a0038411140c400f14800140070740541440761207107081d091110350b000300d50390240742130150240030301007410316500680310380310700050a22030340090b801187e080c0154403e90000c03100c030f40030349400f50074003890313241e00308901e00141e621400b100e00100303040c0603170152481601d124100604103002550303941c0e6012500e070200e440e00182413125003503080060210a102c040103007980000c00b14481801070703011038142202e6030200303000690403200284807820540700d5462000b99410041501107003804403000580b800151031604100c041c054080f000c1035441600d4003c6100320a4140c440d03507180d085a041f1010311010b0341c030500c0d142000e80c030f99030f8010483d641807640007005000c8071411800107030740c40d1203080e840303641050a032010005405074420a0340e00995046409000760789801003080f500100c80242c0702c0e03100e0070092444006243c07961000d08180709400001c5280742c5c00302251456a6800d90000100d600191440290141e000b0301120f0841515035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 576023030 1250 576021780 576021799
    0xe070b090a090207050f030c16120206030610030b0418021507020d0b0703060302120a030f020d0522030f2108011d07020f010e011409060f070c11090123 67
    0x4000641d49560340c0300d0041c1c015400500c0070140002442200160804c50007203d5a400d524000d42d9541d202008031001041d44207200420740c011202c10744000f00d86c00030519804c58448000300301c1d84850302d8000b4400d16aa842c6040d101c0d407100d0151406142081400a03600c125500500446120441d400702220700f0410a140041e528090f0485001d80c008030824074950b42e40c94203400500c5141c002075401101180042c041c0940041c5814245104e6510b5071003504030180180c0ea120000740900c004240f0131300032a03910303a081c0c00d40d0382408041c6078800201b00ea9030b5202d140300805201c030f06440d10203020b841d5161011000d81f00710320b02e18032480c100740c0d55890201010816500f00c50381042001060000c03850552080100a5102101c04020048180f080381c02c64002e04c0f10405950001d25420002469003c0110b59148220701c0000c042d03000369991502280c0501200b44103c41320041d0f2209030a068503030261950180c01d103064020507040b200035540c00c6940e0707403030081031242c402c12 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 576024280 1250 576023030 576023047
    0x30308180703120e09010f1d010e060f0a0b0c071a130603020313061b0201110f030402040b0a030f05010c03111309020a11062d091c14030a0e070b 64
    0x600c98040b690030803035200d03031001c0c25102158424072680300341d41d015a10030300100d0603120105411080703508041d1183c070741c65502c03451039130740007000d10130039040403c14030003e03040341891410564040401048003880c0b80d00c502c20300656030000c006032085a0300c101c00502c0f8041964034866030400485000c2801c00070001a115450042401003804164000c00880d1111203200c00c4502e20a6010300244194170b48405078a0300304200f5941c0b24010740c2490304017440080c0c0e04084071b0344240b401040902d559215002d1001030704000c01c1e15500700038010000004912040a20100c0700c2c882c90021641000070742005094540340480070751810700070040c4000721003107003c2180c210354041350b01580300c0c0031130b034800e89600ea094500d000e11402008100440010100141c4001580f12400300e1444826401d410401d600308944811843d8003030340c40180510204404210004002e1610520501ea0001010f405801c00d03600c094a081e19040060b103400018411030340a0916650290b0030560074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 576025530 1250 576024280 576024283
    0x6081e070e07200f01140c040b0d090503041a040807050f03030a0e0a05060c161a03010303050c01110a180b031b1608040f090b030a1101080712051003030818 69
    0x103442e4406006049045000111a00f00d0442c0c4a0200c4410340d840310300711030001806030030200310408004242d640010001c003001020b0701e00b03442c2d0300c41d003850520b148020a04010010400d0030f5603248001e0000042c008080211041d18003540540c150b2580c0c034001c440ba242c5000b540105101e091144180d50b90f0303840000541c3c400507184e25221441211075030209000020f66005207070800d000103000b00100e01c0000d14080074444e0302100d40192695400b142c410f406055420140c84c00c1c0820040002c2032007034001c0d01c1340d910480000501e07112603c20942090b400440c0c01004101944d00c4000e03542085040e20b001403018011151440c0360901007640c494070070f03048a407070251001c2804086016102c0004001c40c0d4083c0d842540c0d10340303d80501c1881d6074140304800740c0d00e04081500d2100e09002c0ba05071055617101050540600140d401510302400040c0200104a0700f0a0114043c1a0300e0140c140958460040f01c014039083d403c0082c06170704000d005256440000d070390388131007100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 576026780 1250 576025530 576025559
    0x120a050403080a0b01090803030709031e03090524120a050a0b030c1903060603030806120a1e0212070f05032a09090a0605070504050a050907210b0406081e07 69
    0x43c0b02c400001c1300c1c030f0030200603207a465040d0007c04162101104001060350048240000d40b40203401d505031080c4c0900042c243c10360071070707002400a4285c0f0810081803c014949100d0211241070503440300780701022000150300005d0a98185981010501285055500c50160081c403800400d0140030303c00d1010a80da40f2030b8488150152205079105a0100d120b0000d40c809181d0084040c0a03003552420b008241480c10b84116100721101d01d01010007850014440c0382580d0310a0200ca4680c5001c811604000b6121209981180d00050580484442400800e01420b804043d81604500309000e1520b01203042d140c0d12408101080345d01c5d075190f017102080007010f10481d45009569207200f0a1814948400c2004110070b040c14140080d0a81100190080e1842a0f800f501c6090f5613900308451460143e60760070106c0c130305040d81414241e0000500d020300c0208040400c44007055000300c2c0450b041d5500020080d0400b408071522002040c05c0404071501a2005010841c20440100d070b400c034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 576028030 1250 576026780 576026791
    0x402030405120307230a171005061801020d210506040e0f0d030609060b09040e1f05070e010906080f0c0c100204051c02060a08040c03060501030b0403080a020a0c0311030c06010b120a05040308 84
    0x41d10140060510002d540c230100161102504041d01c4404800e810040b0052a00d41140540a04182c0d58091481030865900b65000101100005003402068000928000e00881e410544501c2600c0c0b47d0502001641d548600d010001d000c0e00c0c0c584031008080720081d4104160150925070200004042c0b2029079000a4044138001280f140c0312103124a4491000300c84921044801014158810254061885460070792038101c01003400000441c0c24000c03a000301c0300420392102c0818490021959465400100e0009540c58461507070046460103400380390f040c904507000a0b0500c118100001558204501d1119001d0016842d90019080c2d00800002004202104002405001034404007070700854215100300910358581c104000aa20b0840f016004160443c0102d01d08105610803100c80e50002d5840041030385480d54125040041c20b17040c4084e03480240400c4410410600085001f460900746041c1d0380d800000b00d000c2041c2d0001c03e540750b291300c0c04003004086030b048400581d112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 576029280 1250 576028030 576028067
    0x406020a140609030a05180406180c031103070c0f020a090f0b0a0605040302130902040212160914130e010e1f020301050d0b0c070f03030e0f0a0f020402030405120307230a 75
    0xa58103c210b4179202e400011f10a90b0150810800285262071600b4400d441c2c404400140f103240646034066050b00d50b41b0303000241c486000c01c0026402807140d44140c074510300c6074481d6081c180030360300000d0807105030b504a455103e658120456400c070f220b11030101c00d072205440c025941407030807070042c10358001c42c8006400f5007106401112021195408041000d500410440d11850041810f030303070b48002141d00c0003c03083c5d104400d4440900818048080301c440c00301c00402442c1100c1408680020482d0b094031079600c0343e0700e1118400003801410031055401001340300c10b0303d50a6072803240c02c0c0d44045441c4e130241704000500503511002c1010b010203810242c12441f94032540e1441000b440307041c1d8040c00002d2007095210401d07906402070010000000102c40c0120800c00142c0e03195542c0710001005800250515401030415030091540940201c0c182c1e10024641c008600142e4070880e82c110000b404036031603800d40300b40d00500c3c40c490071003c20801e0924084003006444440c60f000c00c10000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 576030530 1250 576029280 576029287
    0x30b0411130905010218040b03070515070b180c09010e010e060d06090605061e010203120406140c0a1d030619111219090b0c0a140406020a140609030a05 67
    0x141e140c162000760244001c0c0e5003040340e8140d504003503000390000130b8000031480402d8900314041c03170280036080301200010060310074580340604003c40c070021000820b250400510030746002c02d81c07503010684940712072555000c00c1c040320203249003000b4101032624800c100c100010b01001241603c0715041d1040c45500c1541c648456000405501108800400180c1804410800c1014507048075004141c25200440044a008041b502c81851020418010380c018080c84505041c4090159002809007900155003056681d408094240c111a00180c078000006c00d81c03007456110a45241640c100c00403202d1405d0300100094880340c024044000c11b02c80880030500442080d400703503540c0410414100e6640040c3d2607503a6207004100c41e03180c2c0e42c0403400c40d810401182400f403007940713543c0007000204036a5003d41004007070300860900403c1105002c034035405203c1c0302000303001a000d10b0300108001440b61900409904c40020405c403d034210310148114424000281c81d02a01c0a0411549 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 576031780 1250 576030530 576030563
    0x15190b01020709020f121b090f0609040e070e0601090e1503100f06030c0b13060507050f01020d0e1e07090e0f060411240d050c0d0f0c0f0207030b04 65
    0x6006425003180e0380c01413002483c2d48000079500020f01c0d40040c0c1c44403465182da41c101c6208140d01b052152007942c4032040240840901d0504c003e800443c4004000a0500b0b076943c000c10100e80080700130407100e9100074010311026640c2548503911041c2441c000a14500f0705141003020702d0040d0502d04ca02c12801f10348052590113016283d0340f40741220381000b01c0f080d2148a00c1c0940140e00c82a22240c005810101c0e400343c880046410f00550780b1061080586040300c04c440581c0080005d0f20036000f100c80c00c0c1aa180d00b03000410240704e0840001c180260b0184502c0d0a00b50401402001e006030720390315000c2c0300c00125a04048800012000481c005450412030610510601107405802560200000c0010802190100c0c840554414001c403c0c0300301d2101305140407009400300c01c14280654401e50000d80c010319484800b000c0c03a10b04200d07004034403900f60b078020404950302c0c1d40c4070180c0807081c03940108031150010a80c4010076071203241d5221034074800f0000c0c00103402c40382031f620310b400c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 576033030 1250 576031780 576031783
    0x106050319150c05070b0f1518071110060b091c02030a110a030c080607140c0714010507060207140f03040e0a020a1e09060207060801050315040302071205060915190b0102 75
    0x5c95503900a8900203691030881c1842c3c51a0360121f0310a00d141c4a401400c6141d420550030540c0000c400303030340428040e1600c0c40d054a00f551000940442c5100d0b441d0004411400790050070f00900c0607605080d100c41c4c034003007003005024030102c250240b00030010304c01d00560360020b1262055504880210025404000454101c0600d1303040640032018101c00024030301d800003140c1c1e10402841c1d03a000100c680259404896101e050840300e42640040f50501041c10005043c0d4540d0b01c05041c100e18040c03066940200381c1c0c210b90010398041d4500c0c0c40c001e110784030501100c021441c1c104065407800f424100005403140000c1c0c080403945601080e080c0104c3c6c080c403070071300c40c542550440c0c011807142c0c1c0f0001040d180803030040b41d00502175245d00041890050341d255040e500014081c0c41107185c14100d25072140d10041050341103116140b0b000401d040382c600c0380e008082c040d84c060144e6280807107407645800440030303201a01080c080100b0810070340e0b503010150304c21400580403a081c412400100d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 576034280 1250 576033030 576033037
    0x702010f023a060b120a02090a3320060108030406030e01060e090a0c09060b0d0504170c15010e0708010e04050a02210c0117160c060204080106050319150c05 69
    0x84140780c5403011903100c250101174480b035440044454403660b22066500282d00400308403581101c2e000c00188039580000d0381d4001a6003d000ca8041114010006045905030041280011030b000500c5007440229004003030000c02d6507100200001e501d42882250f580c8624410f0718101540c9940305020000c081d08040010300e081d020342c80032424601285a200c4410000c11a0503109401d800648646540129821981c107440032605181a401ca090080c01d0020801c5400b0204024500088010350026180b40200c000052480c00320071103102100400603040521080d1849040055007035100741003a06403400d6900f0030700c503500e40d8a415860a2070306a8000e501420003511000b00c003200100c02000c00c80e10702d0071248943c1e40d4600641d102403280200007815070202e8001000841540780c00c441d2040b0340e25240d040440740e40c031000126003043e00801c5003a516080100410f141c10444824248001100640020325a03952180c2c4201504c40b05440e040d00d42044604441c028003d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 576035530 1250 576034280 576034387
    0xf090f030a050601170a02030706050a0c02090103140d0e06190512040b10050904230c0d0b07030501151b020f0d060b011211030103062d050702010f02 66
    0x31541c0d4a4000e24003280c0340d02d0240202001c00401322a001520840006c100c460203030058082e2400c203082090844a036070003461888144405440f2020060b00c561204600071401a50112104603d00030410705080d810120b0704100302130445503481c266501c030101e6201c1096aa416004005480d805403914016120901c40d00042807040006009580d0b070f1840c0b0801e10078800c580c0d0030741c441c42044400441500d01509042c213011850745072003501c0b818201441090b000301c0b0110007240d400520090801a0115000103014040c0a441901070007103d015004c01090719500440c4860000e1440c0b0150702e03201c00404890200707109644540c0560149003c0260014442c15824204000a01001c2183c103001500c24000c0c0302181182c1c2c0710310344030803174400d41c29891a480d5881d0600a400c2030700360505c50001610703c01181060b51103c00080807020f041c0420300307141c03020340a403c40b0b0340141034280c218010007408510302072202c590000d4000355100343c501d0100e0244140e20a1880a40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 576036780 1250 576035530 576035533
    0x80f13120314240d020a032003070605030106021005270f010e010c020307030804030e0d120e0906060d020d020f03090d140313061d0d02070f1406070b07030e01020a0917120f090f03 79
    0x202c0d5448ca80001d030005441c1003a4100e41d5500e03500c071021101440248114001600b00001601c0d5500c496041150001c0325400386031101043c3e4200d0343c5010008110591590f403140c2494030300d480d001e0149011a28400e4020000010404406074491003070301402000c011082001508041c0600941110803c1c0608646840b44013480c04c6440400080e4043c1e02080003090b84c03107214500b000303e00340309400142034541400c0c01d4900200280d0021010301a042d81c007030000750a0103507410069841807008a005040070002c8150182591618001c1007240035010010480d44c10800d0b1407407106554007260024900c15110808064800109100510f5000c2c05000d10040c5600080c1102501c1108100380051551148001103058000c0c8005070091428090200840d4069540300e030721200f42d05010984000c9a480c042c00ca13401b5082850103d01c0d140810320607094604510264108103200400e9000603180d0750002070b0148000c0001680c1000949114a41b540100324012280280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 576038030 1250 576036780 576036803
    0x503010512151617150609030a0213060e010603060b09090a0e0703030315060306050f0d0507030f1a1509160c061104081c080f13120314240d020a03 65
    0x100f01071a04072900c00c03503400100303031002000401d08400042800741c0b042c154002ca04c80c0c854014440c550304240890399050103807002c07500168503404110040d1031751201e0700181c034a0600c607000b150302d03406070000002c0500c0c00b04140865501d00c8102d400c0208102c42e5030500796113801090000d4800c403401c4e40e00b9030180d003c00108042e010b0300700503a426295a110504551124400c6003140d823584a11944038a401d10310b620a4145241e9114080e030240c2c0940c2d084c40e03180d441b120b440280c0c0c01c0c021110120300c0840740f0390442013002560380005c03450a00203030380641306d40000c06440000e01035030b8030340070a03180c070b140380d07502482114616540c00702c070074000da1b590305080c207400350050b01ca00c40d02d0f8050000c14403c620540084815a040e01c1d4450348004d4071904854019100001c106100451000c4100c0d00480e01040340210317124010b6401180030300d80018156002e46000d010741c1414079480c540c910300044451340c0001101c5060310f548030750308201e0000a1400c0240e5001424000030503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 576039280 1250 576038030 576038041
    0x7030b0106030209040605034c020f13060f0822200409030c0c150f030b0103061d041709030a02012307050610050604060503070507031110021e040303050301051215 72
    0x7000d46000311061324090027203201c09600c16031000d84130700d4003e800c5088101c00c4c2841e0040d10b42c0501810628030a4290034001380b17058420652001d82c01c040b01041c80e851404040550098015500c5410354500c0d4010300b000000083d0002c580e044001c2c2071005a07800110140b07000701d0740c2c0c1c0100000500c2480b00c500c180c180502807141c403980569034000c4003c40401d1080101c84000340c889070300e984e144140f9600360390032001001c2d40c0005a04042e152180040c06007120b60304c0a40c030700300442540380181058038025614403d00c192100c42a882408003441a91700403508042d803540a0030050101f028105450725901c9a1001e2054508000f02d0244144400014600e100e015940e254400043e2200b00300b2141c2e018a114420004400b00002982540b040010b820101d1107410031001018010403218200341d10b04240e0a24251301152007042c41c61007010040040e03041141007881c0034150344005159102c1401442c4c010210708180f20320362001040320000140b54a180b007099410320303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 576040530 1250 576039280 576039313
    0x3111219020f03030403050a290406050a0b0306060a0504090f020a03230f1b0102100e1b2e09080706020303071e08010317040306020c0c1207030b010603020904060503 73
    0x1280d009038001c400500070200c9609000044034182c9030007100a1420720b042742d9500b84940101e040c50481001c200030401e540320070030102c2d280030310300c04e00004c640e070700d4000304c80802c840050700340901c43d030f010b0018061652035180b40d40f401d0350f909840219905040f401c28500200d900703200250000e0444900105115a038410060300c80e40d040d1400c041c0004800e4a10340d20009400c0298998000c40d80e001903100c02020301c90401c40040c0141c440c00c00240c00b800c000c03540f040c040c44001c0d4020040e404070744040c450419200480840d0368001500321201c1000c90780d10700311050b0210145810031840054004c18016005020b108100e5220b00d4031068021b4694000351181d1010610b10613169000359200c0d060b20300c103040035595400d01686180c44a1981c1d203030a064601103030740308010203c00300d6850b00041140c203000c0313401080400582000d0106070715585429160540000e0000d1002a8102d420700341125124503000d6140d4070784000041c01004550704c103d5252089080d011618800b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 576041780 1250 576040530 576040573
    0x1202030c1e0a110a1a070e030115150203130e0907030c12030f09050f04050c0c15060f03071503091b030303050a0b060a050901050304060615090905070302090604031112 74
    0x643d440242910001e000a40c0d11a51000d00401d00381d1341d14041625022005d503081d601402500e08000d01000c00c1d0042402c50701c1c80143c1004000801000344051000a000c20700c0c00d0801d48015413800b0340e0310402e50240d4100d4080d1006e400001d4000c01c103003032000c0018030051074001e102c07503107041c2e51104410b0007600507040440214034070004c1035004a00955910048400140c100c051590501c0f081100a0100404020307241d5000d0003d0550b0110400a00b40f0144c410301c00c000c07640c1440010000409021262640304c0c1e03104001c00d010355000c007c29030b4062005400c000c05c1c00003052804402034a58890741c4000301400b40000001e25906410880c0556100441000702c403191800b8000740c1c0c40f9403000040804c1040024101a5200d030008541c05800340d43c1c0024090b88800800360001218596000041c0180b9024403842581d846040d0b000022410214500099207003c10300d140030f948000741a15409031040122030715109030504400e0001001d8034a14540010450341350700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 576043030 1250 576041780 576041797
    0x50301030620040506090411041d0924070e190905070c03090b07080d050a050106110307030f0f030e0f061b0301180905030c030a02031b060402011202030c1e 69
    0x50422900d40120310b006601c0300031182c1c0b842c644030314140c140301c03e202031984403844185c0c10691318005144003110313a5000d00060034406031251507540c960448501413501c09071012095070048901e04400108040441049124248920740c1c6a520f142c0c0c10b91b46030b60322904564110881c031402c4050180c2030208001903c031084d5040002e070b1921481120817019859008001c40c0d01c5010500080c02c2c804007500a05125100e1149001c0700b942c1c0c000103554050303410344005511440188034040d000091200459220802503003402c0898600815a088030303d01c039070074030540040e50840039100e608408042e410a80c01c54000e462454815135a60208650a6000707006503441c04070b880103032404490480d000003941e1100c4580345482c09000305107401044469100801ca91841c45da801d00240c8401c00070340e0061508d818220603400d03048038094240340e04a401640c10040184e030445003071202803020312030040c0c41340c3d540c07a4030000d140304070250400500503c10f1920f0281c44014010035146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 576044280 1250 576043030 576043043
    0x60c03030712060b070218060a05040603050a0215031306051902031003020a060f020705090a0e060c03041502040b07060903020f070b03010504060e07021b0406150c0b010e07050714071505030103 85
    0x4d580d00e42d2421035009540000b90300c142c003844000105801e0800c91600b0140050075960350359580c6000074125907103070307004031a60f80002e450a400e6103440d0320308540b00d101c0440c6c160300e180b030400c480e030503102000b60004068a0ba108007060003400551400c0d26602a450001c40d0f0340d04103e11000c0c0440c00d9413000320305c6582d03d500041205442807030410030440707240d00103146090801040084903000104490040795844114440c0300c04204070450084400b0b0403070f10b5590034103080c8030b8100419010381084450041000300140d410820444000a0b0403000019191415140480c1032101c0c809c1c883e16144221800070400d00c2c48072004604850f000c49040191558502541c1e2151070112800005600100c80c0ca1411421010071a01c1000c2c00030300c0081c0168840b648400c2c007040c4401141c000500c00521001001040c2520b0b03030240c208119400e040c1c0c90503034030040041c4511200102414020807800c2c008600422000c4040e285010f08100c0c0308028081c001c001c0e400904c01030380c48 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 576045530 1250 576044280 576044291
    0x2628140603120a110313060807020f01090804050609013e0c0906010503040528021c0c0501110a120c120e032a03010f1a0103020f18060c03030712 64
    0x81c500000c01c0264420550400d9040c2440c090007a0b07498041100c2c0720200e40801c000301c0c0688030400401e40302811080d2070b024003d0411160003858007007000703540e0603943c1c5002d000c0c1c00410902c10544040b0b50f000c4861955a22403440100c9502c12103a51403182d05c0d48210703140000003118207030803450b443c03e0b03809004c0768000c501169035140110364900340c10080c0b0754046141c5505c9000155130041c02981260340d401401c5845800494800c12a44c050b0368031040c011045260425070003645e10340d0a600e5140c00000e40d101c0780c0c007007600da00c038242c14007000740341b000654042803008400254015624220b416102803000d0101100030008076504a2912000e840b45400b0300d4005421880c00340c01080280000300c2d00025001070102e0b4601c000d088101101141d903001d0158486041c4480808030b611210361510071084120600755034140740c01880f50003d2644a03009866010b50035000016411401c40c0100e4028840d01c0b4421015020001c10001c0c3c0307640003041f5448050800c1e50401a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 576046780 1250 576045530 576045541
    0x20c010309020927060a0504020a09051512011d01090c0b0a050414010302090d240b1c03050c0a0b250e010809070510090312262814 58
    0x495012141c02907002e5801004240c50300d503ca0302c444840b1210160301c0141d20740841070a0700d40b00d0210342000303095440d9001c01045040103d02c4100600d03402030140302e6424600d24004074036030401003460080307000b151240c82e10380702500880b441e0403140f00b07000e855410703800040f400b801c501c1e1416902600e9444000807060000304c229a400300350303561254241400c10001c00e44242d5503036402410141c09101c84030660b500c640655112510031140703440c44c2c00862601d02100cc00b0904144482c9140c4103003441181c41d8028100c2003401c0325031000f90070110514003a21240500308540600f4130404000030104485d00000300c0c010740149142d051551404180801000450001e05c0c00043d400480c0a00650181500350707041010755050300c3d00d10782c856000c10086045451210002000c9030170401c28810f100303c00b00104441e030725001c00a50300c903803a00e082965400100d5807901901e100041c00e030b21000101c4000920011684424001d1070000c101c0c0640102c5144064030a64240401e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 576048030 1250 576046780 576046787
    0x30d0908031618090b180f09010c0e100c020d050102040611120f2706180a050f030c0111030405040524030a23120f030417040f090f020c0715020c01 65
    0x780031080c80702402c1400d0b401c250342000030341417012885812a0074000e060140101e40840540f0654008034010868542380a0071429511a5400c120920031304031111400394640c44582d000d0120740d81030070712201c1c0191000c9980b183c1e01d0040a0065440807030046000c5500010030442d095a0808980741d014003410030745410312030032171a2954007a0420680f0680d140f120807400c0340c0060707039101c00a10240c810200b0180c3e40540c1d0044c4140b0342c2c8482c0c4030769030718180174240050f00c0d05881c505007205803200425a0768020102031414002ca90256141c044020000c546c0900005041030005082003101c070000d071061286c080f10030309404e06807413070380e4140014a00b00c6650003c90720002d003508200761245410311f014030f81003280175000c102c04e41c4150744002801c3d10b4045400c46d507507910346420300385801c0301d103082240c0700a01e04210411603501c5000e402003d0340c500c1c0000060180c119030103c0000d1040c42c40c00788003401006c10004803014241c480c0c01880d00706400390b440c070002100044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 576049280 1250 576048030 576048047
    0x3060f0b04150305090a14060604062309100312170901020310050f030f01060f050405070504180203061c0c180b031507050418150509090d11030d09080316 68
    0x1c0410b202d05041000c0c0541c46074000342e411480301410b4400c2081140c4a81e06605004101d01e0855401142489102d08292041d0001000700d141d141580101003c0300c1d0515006d4192854450154007020504002d071404064000315130018141c100001f11340342c0901024a00311803000f0344100e50001500409040c02100d01c10003c07011344040080c28a0304000a200401014540520983e1460012400b00340f007002d000d0011210f91109841c5030200304030590b040140031000b0000140402c00c541c6038408844010018004000f50300d95a400000c0303415065070400b080c2ca00d1a03c5403140c014005400d05800641700301030010311110049034510025201091a403641642c0580d07005088241500f018981198051030410b16041d5552020404568801319980c900e43d6114004421030254030452030040900746c0700c004183c07a00d2404580c0f5414150341103004d00400c0e528107035281c2420b000725840500f608208100394200d0f401c141c00315801c00c4400000c184204541942424004c0a20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 576050530 1250 576049280 576049289
    0x7030203010311010c0c09020d0911041b0c08190c1101080606160507090203091606081003150605060a021e0a08040303210207031d0d0c12111003060f0b04 68
    0x883c01c02645840c0112070f001c10030001940c001ea10500007151050483c0020301419250520100e90700703116007003004152074005183c501c00e91074451041200811402e441c1e80c07490507803e140c0e115403801e041207004d91144404500000182c0080d0340b80254008070300000301805140a44014000ca000561741c0300010386070f082c0c0c00b01041c400c03200d107080100c101a00c8144190180c407401e90341c0b0742d0309105a07041507895040039000320b0043c981c01d110840780b0f40000d10991608070203e09003583c0d011034510081c08003511103001001d4103410f650503608003030000c240150406943e000b18802c0292282e0b400b0f9595004650710b004140c20300000014a1940240c01100e014603140c51982d060701c4401c81d40b10768820304140c541e54148a44100d10241c03103564080c0e1618100f5103980c45040f00010b0400d52118840d030080760b0848007042d05248a8016240c1c0d250b007041d10041c260401d9945010182e9100340c0c040200ca24000c0314a90581080c000c0f41d00303988900c401d00e521800c18441c0d40c00340e40074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 576051780 1250 576050530 576050543
    0x406050108061c171c0506010801260703110406240c140d0302070303050105040509100b060f070f03020c0607080a35090d031419020c031908070302030103 68
    0x810b00ea0700e4090b00c071509031400b4242150314104503950311016210007901ca00c4503100702040c58062171150701d803094200b03420403500b001315103406000a040340d08180035440070750748100ca408040d00300e4004903049189043d4215070700b496807071400a60030018641c80300e0141341094000540c48010700c40f0489103610301144111001c4c0380000c102c81106980100340e07245250000c864090423800e0204100301840c41e60701694502a9080c060700381c60069008500440c079040421025040100d0380200301c807121900800c107880d006000a020b402410246a22044000740280802c40d1440030301c43d050b84281c00395448070719030500f0854140200c84002c1c04c0d54900708100c04c0070038861400b50034440c500446a400c50a41840607103502600b08844402c941000010700c41e07018001c1101d502c1c0184039240a104400d045c9a01c0205010302a18814103103003e55030b510078030380d83c41d0103031520300390400b00300d030740386c1c05021004503840b40c40311100004140040d0200d40d5081c800d00807a8183c0b5040718 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 576053030 1250 576051780 576051797
    0xc11040207060605150c0c0d030206180c0a120204050a060b1b0304090f0e151017070302180114151c090c120311010c020616091d0f0604060501 63
    0x414400a580804411206103648000108482e0380740e05002c450132110014aa4480e0001c050141c42d04200094003481249030300309041c000b80d40000c0c52513102c401001070307007003072003100c0c9200b17190015061619900410907500400c4140c050001a03031035500032070b414000e41e1507449041c03049403810b000d215000081004858524244c0e21000c0c42c180110500f1246019603902e003c1d8110f0310100c928074079450301c80340d43c00002d000400c40c0d5195007460140410b00c604101404500c0d50810b44191844e07200702140c4a0b9180d0001c0c402d0b03600a540180481c0012098403400c0700340ca540074050260381e8a601e481c1e40c4500d06004008540c2c07909405030b05890b2450400400c003801107036607222282c180d00d81c08280700042114003610000c100c2035190b64866146440c010b490f02d091107509042c90313071425500c448903c1d40025051307046280c006480c01c240900305000c035101c103440c1e04010f12115500c1403450240d60740c030451034480c041071003c041c45511040e00300010b941482c410a400204100b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 576054280 1250 576053030 576053063
    0x1050a02090102061303020a1a0a0b0a050906041a1003090302070803030408091203160606060306050303070f0f05030d050c09010e01020f061603150e010e070c0b01123f0c 75
    0x1020108065400380c0111440b0212079500c072741c2203010141c250b1022007400c10901c0041c5500e4081d0700c2c14000c3c102c4030000400d040030041502c5030002031804d440360b0313201c0c4614070908040c0c0034081e82040001d00000c8402d281600050080c00c101c410840052045c00c0c00016100d2010042c4ca024a51000ca15498814240c042140c100d4455000c844540030800c0b050000507488042c00c40380c184100c8000c50f0a926100d4007034110b07076540c0c1c00130340a6002004032000080d00c0152500200e81d1100d90261840c0e410b040139461405420b03601c154092a080c1845030340303c2550082c10126400340c1e25058003952040c012a143c1c2c844001508896010601149003504809000c0140001031300d40051508454140715200717000a50000180c40d0300c1d217005008032a0030b12101c0783c0c0840282404002524070b95034030007400030f05100c0c098070340d0110103108003044034203840c014400c95506000b07400510104c4c1031031a2803034086c0301103c0d1120603800302c18100740100311492071980c001011101c80102c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 576055530 1250 576054280 576054301
    0x80307260d0228170702070509040f05030f030f01030605010609080d030b0102030904021b1006120305071704090b0a090509070b07061d070f0e010e070f111b0301050a0209010206 78
    0x1554100b8000620b600b1a00203030442e01a1070b0030090041e5100403a4088901280013580e80141500302150440c602c01c1c0032541718540d00642242e8400143c44c080021810107605600815070040b050080c000144441d16176040c4000b4182d901401c020045641e03a07000c00d507200030143c07007544520303088540d2840c0075601950107028211410b0044da4a03103000780d40001d0890303000e5940340038031019140481804410400c0303234001440919034200200c1d41400780440f820f80403140c004ac1002000a8480c003000b00c2d021481c281130441c180505d441d04e4a460400c0060002e00c59614000d82e0011400078000c0420300501c2d010344088006080303400c0c104050702840307500010054030390503220403580030404e40255036030800c4500c05000d040018205801003000d41e02d01d9110b038032100580c20050000038007044032542c000d8001c4c10400c071001e550070800d070340384d0a840350003035054010701c80140c0000182e11840c00030075004a000704100c0e65403c542204a014030500c2c0d0740140d10200000342076412 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 576056780 1250 576055530 576055537
    0xc0f051c020111010902030610030b090708120c07091d2401210804060504060207080c01050909040320070501030e010501120326070504090c030c02060a0b0604030c080307260d02 78
    0x503e8004548180d1540204c0c0c80c0040590f00400701d1641c0340f00800034010740d986e0807900b107180500501035491401e4000d907a40c055882914845100000784d00b00d01c00c6007040008010810040c003448a5405105084004a0004014020760044800d0100c4c6606803d600f184071040d07070403c0d00c400b40d00b02081924145103a6550031409890b43c0e85070340104030460083e000410700f50340e44941c0c850914400905003800c682c040d5450340d200e8034941c0c107140e030014107860b1006030503510f44225a8039401c08403491840740c069031304514140207809411110101e500404d444080c1c8060040300f842413805404c03030703400b4410000700504510052000a10032810f013000c3d08241c10040c4800345500c46010b4805a06440400101d50005070400600358940100502c40045040c108810282080d010303448400c01840d40541c155505040e220543d00d010580f805140c00c80140f100d960b03150100036079203611035201610304d221000024200344400c408074044c0d03034403511085402e017820394480c1400ba40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 576058030 1250 576056780 576056807
    0x12280b1f03091a06010f1b110402253c0201030b0a0602070e0105090c030a092906131b080603010b040c020312160507030c0f0b040c0f051c0201 63
    0x6031035031800c41c00700e000c10741c6034490f014039081c0c00031003820110000350071019840020000d004003440040340c862400806220080e07049400342405540d0031001a0007841a5204442052401000d2102c2c0c50b071000c080038400c03442803031001d82c410034a15800b00c03124029500d80c20040130760340050240b0340400801116051040c1800304d100400c040002e921400d0030b421050060348002010001040c0400c1440d00510b001e4070f15102c01d0515100051b404c0c07100400d82a0b000b03458a4482c002c1040440c080c2280a41441c1103a07002c049898011001d054140c98080c4030705041140b0300d56401d0684111041020450307006040c0350035641c0192014100204415819540c0e14001e0f030305a10f41c0d014080c101c084a80c0555501e24450b410a025071030082e000500884418583d20841a004821241d4480e01030624550100141c600021880b014060043c000b141c490140010081100d11403826a02c90030f441a08046e15a030500c05502e0b503d40e1181d0704110254020405540100c0d480e00a01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 576059280 1250 576058030 576058037
    0x301050d0602090316030b07030501060e0603041b030804060302091f0206160509030a0303050103150c023c010209010f021501030b09010f11030910150902030c12280b1f 74
    0x20203040d150031020880c1d40d8002c0d14511f40d80002c01c003a5692500c01c06024203518107003108001c0204001c1802030000600c0280049a180c1d0380b00140049100010010360348911300701d541d40e8542000501a4000c03181807406110410a803040518030350b5014140e029403603004005a42d130703101c0303900c6081c10244508010b0207020051131038036840c240010f22038280292004202549940b0349a024244c960001c182280d15042c00100c5d85540030036800340e07002440c090000f00740780c2542d65002c415450303107070b0079040903200300781000705e0b001034010702064802600c50358044000c43c1e1041e80c4400369948070708190311200340107000040d00781004a421040100001035580e100340c4100c421108118150707515850302101300040d864042209080d801a00b1a00748a07803002100159004000c0f405900b40c01c5801100007100b40c0041c2060740e5030000c04500c0c44015081c000c841101d480c03055002010705408200c5040303151400d5024002c0640005001c040d50840140140240d15a429007a8006c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 576060530 1250 576059280 576059293
    0x10140d050c040b04080105010303080a0207020a0e1b04090c0e01020303160c030905091306061e090203071b0308070206010b030609040f02031204230307030812090a171e0301050d06020903 82
    0x1803c80c24805031001c0d014083c000101c80d41182000340c51504001d0180710b5a6004011130b00058840c0c03c1440129400000007100c03586441c40607081003101e1054201e00c0d82c5010400040c6074505400400002613035444605c80c08801c40012600c910089807038000c0041c1c000441810786201e01c081e0110349000f403509040d0b603921540003036800b00d401c0e00c1c1100f2042d040b0300d0000038482030f84a000000c2c0f0940c6a00c038030085800e4100b0b94043c81c030b885002c54050340400000c81c5980580388a080c01c1034000103a00c0071035214900a810440b05485000061181200103c0c14181c45801c882c0140340003030200100d90340b242d460700850b51410300c4c200c0c1c05002e980450743c040030900d0301400260901d0041c1d40c0e4014180984032030b03010812105144a80c2c8900c008001280380c6030116142040000c4202e030310356803050a06454400004d200414540300d4400e0b03c440e81000501802804003603914103020b12140f18030300708240c0820300955511604102072000007c00d546d00030400c010002d405e2341d82 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 576061780 1250 576060530 576060539
    0x5071707082205040614041a061201030308072f0a14030d0e12040302191a1b0708030a030c030b060c010c02060730020706090c0510140d050c04 63
    0x410740c01144041c0740c0b10441c050b90b8a2600b161a4845001d0401079800b0440e4034900b000c1d80c0082100500359500aa6a920310f140c110b80c4019070100302504080c010030b84e102c98030080482c0c41c0000344801d400003521070020940c0107100d0307002010030000d003042d4001300040e92050b01031303289001904c042c0c451046003507803000681585095444401e07400090f41e00c907001008260144c030701841c143e80160300900040c9a0503030039281603405aa1b010703114101118a4030b090754845e01d0306508050440c0b4441050a00441108401816030700c10308040c01c1c510302d45000074242c2c0d5100c18061146150010310461600500c071381d00109510205103008515824400b01007400c81e07002154a5420b6515511408034503a010810140c1051240c6000c420840002d04101c0807180d02070000e0316062800486443c8007040e94069407a0303c4e804c0341c8200308041107031030021150889481500d00030001041205401c03400340c4100d070070090f103010116180010004046004020091100030400c400b40000324 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 576063030 1250 576061780 576061793
    0x62a032f0a080c0f2e060b0d110f040b040f050402091014040906080d081015140909100317040e16031509020c070909031d041d031b030a05071707 64
    0x6016807824069190725400485c90080d10344040601041103410603004110f500381000444104034001a4002084500c90031140c52502c91066150304401000c0340100d040c4035400010700403500c0b90369101258581e11300510080e40a0122000d610641c013001000000f4020340610b4184007100007900d15040e11020b4100840c0c4003a0000ba00e250b004040e07584140360800344c2d0329081a1583c0c10311107898a4010750b0607910303660000340800c03c001043c010010b05500d40540c3d0742031000400740c004915000407135948901c114071054403584052507001c1191801c0030100c40c00d844602c203261816a036005000240980700b11040000c050b514200800d8013150200d120003d03225031030015a0300c00700040380a10b0b01d081504042e503002d00e0101207a00080c0c220780c01c0210003400301c040c2071801244000040081010031003084c41d0074165039200c07615100c04002070040842c40d40c1c0ba88001a000303060301350760b40226007104010480800402000c00c443c1d885206015840380c41851801d0072039980d01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 576064280 1250 576063030 576063043
    0x20609041e0e031215031903050f04060c060b04021303110d02090420010305010b090108040c080f030a02060c09013c1101140709062a032f0a080c0f 65
    0x4000b5400203c0d018010140380400b80d9040700050f60402c200c82c02181c0003e40307a401814115035403400c2482e1130790030507005405076014050000718050300c0340e644090160031600c4111048880030300d0080c514000d4039061003650389001410302c540304482d0a550b102c03201e1020441840d50301080ca02044d80050750b0752952603101d90b200b252810400e10155140780050720b803240100741450f0a01d401400304694080981d407d8050900e0304800c140c07198245850b01c403a081d001031900e800b9820100040090001c020a0411400d80c2181d020341c0d10404162440d006826525002403c50840384050100b000e0340c04501170b119074000300c074004000d5000c186030400b00083c01c0204951a4808946080038400c4441102e600d4030f050100780381c040e03401810b1001d10302600c020300401290748807852440300c0404240c5841002d200e90421100d0801a10030064068580040d00310400301c0c1d001040e8140c1c049140c00103010041005640c0c9070f0f58560584c2024a110103d41304440058010344000c100d007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 576065530 1250 576064280 576064301
    0x81911010c051308010c140d020c30120a020a0908030a0c0b06041a0603090705280b0c0703120309151401080c011d030703120305090118020609041e 65
    0x3495900e1600180030703240750f001c0f0350000c21164900000e0300f007220f402c04240c44942c2c02030314030f032540e0745080c542c410700900501d0241c2c2140c0c4506124042c0012650034603500411350001d852040e44c079070740300348a11441184940c4002c5400000401c40004250700602482245401d00f910120303150b00c45103182d600402c19140000752035100c0f2005100700d4205240e04980150b0b03040c800003110604103458108041015401940004006100300805120303100c05000d00610641300304410824007401c6811659405800d0030080000165410083e8100d03000408a4005481024034584030f01000724044c24401003490389865071400068400100010498130311040001d960690b02d100117264503058100c000c240c0e1004018180a82c2c00482444880740c5d90380300502894246804039050801e00c2e4001003901c00e2001c94281c002c0e41641005100d10288402007000d990440d0b540b4040f07025200700a504000c0c00c1000c0081c5040980080200100400e0702c2c030b0042c13940010407400c54404160 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 576066780 1250 576065530 576065537
    0xe06070c18020d0605090f04020121110903060f0708070c0c050405010b13060e0a0b0d0f09030507050c01080105010f03020c0109200a09050621010902100905100903081911010c 77
    0x80003003c002d040c0c8a840003034081640d012919107820070041740c1e041d1020700080e06101991488540c03000b0050a00c0a000803c1c100c1408511920740c183c0c020b68002d9080c0911070f02600700000d190f402000d00e024030038500c0d5640e429454890030300c103542180083d182a40c503400c0c80300c00802c032910745000d036a00803c002c60086070745074404040d00600c80704039082541007014a004982c520399880f41054186c41c1011310103592065085542d4004000905505290301d081170500c80c24550400050a42d050007903041d121a040d4480c01128406000d0140e04d010610302d11051901510980c05006100541000055104c0c00d5440766882c0c10340b01c0c0c0c040104c1c0200713399819458188501c2d0a0300401c400302040c4a2400c200c0001a84d1030004c09606a12003c00319950b40700d0344094100000543e0007400103000d5903801c06000304002c2c050300611b4040c40601402155840c0300300e07000e608480e000103e00342007520b83d401003401c800f04132410500b00201800004150f100a121b40a0164bd4544 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 576068030 1250 576066780 576066787
    0xc0809150c010c020c0a0504020a09030501090c24120f0e0a05061e09070509070216090212010b16030e12060a05100602030a080f0403140c070612020a0e06070c1802 72
    0x4074a90035140112038035021900464250551922070403409820b5410496000d41c454206900c11906a801984054055801e1080b15420b0103500c04507102520079401040624040790741800404035a40401c2c840000d680240f0740103220013070783c02109503044c150300c0802c01220604450f4984140313400155641e070405403e08c078210001000c1501c1c1e1003080003102d401464440720803a111240d41c441e150041000c600002c061620034000c6000a0b0440c000214046032282c00c008002d410058140e0a83c1220800100d0f0803040d000c1a145000768800701a1751440c2c0c07030b82c0c0c200c40b840d160750017680d003041170703014050f045681c1401500d10418114500160515041c283c081021905901200642d0010042d0b00303c1d00d41c1c4607000f2a032128512075a0304645d203840c40c00319900100c56042c0d0b1041140400c0741444000003040d080300300c45080d943e05451510070f8555604030300ca1000814041814040e03203510b00e0829030060000507003d14286801250b4420b1170b6100a8000d600c0140010f9001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 576069280 1250 576068030 576068047
    0xc0c060c17031618031a150603011701060f050d12030f02071b050d0b0708130c24031118030307081207110304030b0a0b0a030524010803190c080915 65
    0xc4038030b0303142250211303c2182d0a4555200c0342c0040320b11203080f42c083e100340e1b40000c0c481082410314440c03040d00034200907500c1d07075280c004000142068204100f55400d00c803000403420b075511224000c0d154002e040205d170318855030b101168080c0c541c40e41405e0607240e90301c205100b100c078800b52030760074044c10490703c0c094090701c1540102d102903000f1034441d0402171800c001040001107aa60310030828105140d0640b5100d4041012502a240041a01482e0000409e1130602c00150080c8040c28107522152000c809400342d00b13403101c040c4034164086e0701b4407401808400084000350148000b038180c900d01070b15034a9808a50313000c1c0c001002c0340c1140c1e1050040403580403000070000948017000d103081500f1640c41c40140c00c00a4200d00c2029120324038518165034070b6402a00465028045550382001c0002880168070004840e0200034218400060b40748030120845036194030000baa1484003000e1182074449800354581a55140024400481552644141070b05410140d000c03094986464 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 576070530 1250 576069280 576069287
    0x1511030709050f010e06030703140a020f0708160f060903020c0a030816030e1806011d0d0b0c2a0d0c050d26040302031c090f030e181003120c0c060c170316 68
    0x140010302158810807501c10dc4400800942d000240c0c4804850750740ca84003c001c8000d1072114501500380301d5861032070f1041080740d80c0074a40091003034007501c000b211018100651500c061001901002d806c00c0302e04c192210700140458481d00c24100070101a200340c010651404c0420016800046217505100702503800c155400b088023800314440030078003a640003040c542c680380c01c0e0003000c4010341c1740131a0b03031a0700762820b4500c0c291030030200d03000703034051071207105c01e2114480620040d034011680a9040340c1c0c8150854215281c1000c0184012040b18004132590000002801022844a44001d00c440380a80c1c0050056010358015612815a6481103910000c03004140c00100c2c0b800100000094a050780c2156240e01414421152040800400c002081901000e60400c04c0303081085064064101c400d02074038003404a002d85c0440011056070440c86140c07020709100c80f0345c9810010540305005c40111030340f24140e80d2042d4404071800c00300541080d00e9502c0e024000c00e0341108003591 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 576071780 1250 576070530 576070571
    0x182e0f27080106440303090a020103051503070308091c050f0105180a0b0630060601030203071b0c12030e1305060121181511030709050f010e06030703 66
    0x24541d0100500d95401c134030164801448000c1c6080e04000070f108225550307030300c1d5020780e60729000540b5600d00d010301c92252038030701c0401c040b070200307141401003201c410000310765007910b11018004050841c1152640c82e1300742c00c00080305510010f034410200741e580200e900740710040d03c244003c0c9444141d0074040c07825079000401e4604203084484141c41043d0000a0b28901641c000c0018001c42d01c600002c500c20041d040705034540340c5929201904601020111280408100010340700c00340c6420004405a00c025244600003036206540011180c981d24050801c1078031408d50b0740a282d0355400c07100c0c2c846007025000d50100300850f42c2d2294509284803028420640c100c0c0401451404000203020501c1005001d44070a201c0260514414010b5020300c220755550b41e5912200c0c040c0746024000c0c261040c940e05503185c20801e65090403044101902d005649982350484000e050030240201e050804902030b04100c1109507010603521500000d50203100e40795000b0a00e40000c5186c28007050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 576073030 1250 576071780 576071789
    0xa09030501050610050d020901030f060803091503040c030b1e0109020c100606050d1d010608010501081506090c030a1b090801061208030f090703050102182e0f27080106 74
    0x1801d080d21340465400300460b10540000c0c1c0300140c41300c049100490060074910074482d0000e03d009d10101e00160000054100d481041703611440645d0b00c3d039415041804151001004110556018800034842d840580e074014070041903228466440c21540201100a80c00701840070360025050307280e040d09201403403110b00320035020300005241443c000c00500c64007003000e02ca599600d1500b02c407480050903039642030030220004e01c107594031170500034000c003801c0c031850032035110304c043c3c01c03001d000080720591066070002c00e180e0981d0398044208003154802808a800c1e19562400c1069901d61a003001e40c00f0802075a44d218981d0518000e14210b9410b40c2000d45075984480300751000444403002c40f5030000103c070395140366440b100641ea00d82030154000400039400420644081000542c418200500450340d5440032004840c40d043e401c008811a85032a2030007801180c50705004d0b0b230740c407000c0c480700386032816614241010503891f11041c0944034804c10000c000c1001042c0d4240034030009403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 576074280 1250 576073030 576073039
    0x10906050610020f0601060503220803071b110405150d05010914010e12091807020a1b08061b161109070906122003010b0c10050c090409060e030a090305010506 70
    0x241301c0c211281e0360130051140d0410058008002504c10486a01081703000744448101c0350000c0c428903212085420031210b10b000039a0391031595514052059078855426000303040c1d8012510fa220511014140003451000350282000b00c203001910764141041c5050700803c00080c2d9451145425400d6151100c0300c0c50303803a81409240c0c02031100105140c03622900001401e03681d20072690100b60a032000ca028490346110030310411070429000b0031801c0c2e400f40b04c0c0000914000c05807060403d009114040e50303005601000026180e039000034a12b0860280c548420703800c00080b40142d801181c509941118500000201c80005041151146401207220705010524604288006054060183c0080030494894070007503624004810751002005108107456640e42e1145c5c41940d05501c01e105640c8a445000c070414002d02591240c00d0140e05540c80091403c0481010031001c5d00c6441802d03141e0a0b5a1a060114140208000d056100150b107903030f400f162a6003402821500001c0125026 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 576075530 1250 576074280 576074293
    0x3050c0f0f0a121112070f0f0e040b060a050301020d0f050f04020315310201110c0102120711030a0501090201080a090308010302041a0a03140f070f050f1201090605061002 75
    0x85660390100c2400380e9510f000c42200c08151401c00241400324210b0854000c07422581c0c11008900104002c029603070448070301c60f800c41d51040302000311f116500c1140d036060001d1002c1000240100303a602d0700160010001c00880da200d10010342242d1021800c14101c3d0f42d1441b20b200c40130046d00441c0d07400348070340301142d18500c0c2c2500825280c441c104405810520708400040001c0c1c11003030300e00a01c4000084a031703148041c5480c0200c0c10103007000e00b86d02090a2460314a004c1c000000e0030254004103a0280c50f0600d0003000b80c2c035540d00725910484074400112203803e140d40b0108804c42420f80154008500320b18203000140c40e090024025203802824405000c000c26000304403141101e034140e90015140d00011407065480c4240c052082c0c1c008100d0a0002c20320030910300c5111907154110aa40029102c2614259104228450074190000145040000b8513015894035210341025100c030a903100b6a20010742101c0020504a822581e070700c00b03101060a0801d558040407016000030800f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 576076780 1250 576075530 576075559
    0x3090a060e01022a191e060b130903120e01060902130e0f070e060d09120f081501020601050d020604030c030b0901110301270e030a0908060a0504020105072a03050c0f 73
    0x2101d036084811151142d1799280c400301085001c1d5840081420380d0380400582c0f800501d889030240c049a504c0034450807000c6540394181c0a01d21940d0f9a0561544800d6400c402c40d500c403001900c5004105902e955850f040055034420b00d0008110201886601444a5080010344039174540007503c0710700300e0b103584c601b00100716402c04603541d0f10340d2007180c2880d1501c10344102c0002401e14410001c1ca40309205c000d164450f41c010603d252040105d480d030407621703505c4c42d80c80c0c48840ea840f600c19005030b00100c0100107d0409000c00180d06001a04552400d07443c0e03122011030184a034002c8455505003401c100d6204000e00c03030341200805048080d450741d4500380354070f0b610180700a000c034258054030760510b2040c0d5207a4010038031064500c05498942c441d010024041c4d08840c800c07103240740966000074200015508c102807007643d0586a25040191b191038400904410b03110b40800c0101c800115494030f000200744030700843c8610300404550110806120f008802061514007501d014440d003071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 576078030 1250 576076780 576076783
    0x405011a040b0904020d06030b090f030c120706021e04030510020306220b1513090e0a0f30110604081b030d0f0506100906120203090a060e01022a 64
    0x741140c41d81a080342e10741010600142c0244240c00b603100b26185050400010030038108810b0b841404840e0540c5c420a91903001d0a4480c031031090040160b030010a404025004100301400b4945c1c01514018203000d005440c180c241e03007146902c5028040007050030802c00c003040140c0c5200480c1050203608506000020a44040005004040d04100c01d4802d48240302c056000030f1401d00000d210b11420900045509190f074041044803003240b0030b5036404203900d1540d0140c0050302c40b61200070303c552100c60f16024103031012200304641c40c202d004106402041c407181d95510a02049007400b0345c0b0100020f010788a1000084100301e40e411142c01c010100d40310b031040c1d070346115040c5200131841011112840c11403044040d4940090300d041803036150700c046030380b100780f0a41d003e41e48030a03850b01c0e440c01562182e00e00d12406001643d0300c56034010056060b009180c002c06020121409a0140c1c2c0c0ca001c10b45100a6038030806130b50220700100140580c141401d02050030080b0b1105468100f21160b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 576079136 1106 576078030 576078037
    0x10207060908181203030103121710091b020d0f050c0102030c030906130807030507030e0d050d091a0708210a0c02010605060a080f06060405030a0b060405011a 70
    0x3c0064101003e024000031103010081d400c43c0c0c41c582d2030480910310409802d0810450851402061192100e85130003031948070105501e003418150043c0c1181d4032840d400c0884c403680c0300f41055194000c1607580a058040c03524810003203ca500607a00ea11030b403424a089503100100304481c84203481c003c2c1d405080650150f071155180e501d102d51840300f0318100980b00b060204a2040001e015400901115100c1d05203c220070b1020400200403c500c11020b9071240c105a030301c01c03981035001058402030700012036a03041e256a00384c02011f881c021850010020303a00000e090403419980192821b140356941480c60207880c02c007001c00d000c1c1403140300000156003040c034081164940701041d1080405079560710f068643d103044210907020006006540c002104100108140d14140186040c00303010784808005424400c1c140f04c00c0700c0b01640480e80d9249803040c45800040b024046 = true := by decide +kernel

theorem cover : BRFrame.Cov 575899280 576079136 := by
  have h0 := BRFrame.cov_init 575899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 575899280 ≤ n) (h2 : n < 576079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
