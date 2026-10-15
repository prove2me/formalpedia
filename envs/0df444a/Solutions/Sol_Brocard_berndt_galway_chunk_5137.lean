-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5137
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:52:30.593774+00:00
-- url     : https://prove2.me/submissions/267a3819-43a0-4210-9e26-84df23ca7ce3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 923741007 ≤ n < 923920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 923742257 1250 923741007 923741009
    0x11190513060819051b0d09020111011104090f0e070e040b0105061903150305010e070512060f28020f090907020d27031b0e0f15040e01093c0804 63
    0x15100850b0030340d6410f02142020130f1080d881c80d028000002c1c5080a0388a03940901f00440c800d9864000703a000c00b03108682a01e041a68142b50100f04020800901c0ca0682c40941d49070118200070414000d0030b41901d04003109a440201d03418840020001040328031020369001d002c08580722402c0c440307144c04282c42c2203004d940010505075604400000000240961001154403500074000420481030321501c681e40e902c5041d0262129040e012849900842d506200e030011805821490303480d032000f02c0904103040400c04000440c004030b07102034051800100552002c01c00707080d56400c180000d10000420040136502107407c205441c000c0b0503801040210085001c0e5281034400c080c503500c0200c1100180d2000780582210319182c3c40c0c08800c0c0110604881c00e103441042181d981940400880c80c00722076005080d03042c0c080740b00f258605035014940804d259000000c00002c1641ca54964002980c40c0340400d0b40d030112004402034a07184003102d8100782e1a00d042252085a442444c14001d1f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 923743507 1250 923742257 923742301
    0x180b03040807060e10020c0d0c0218070c080c03130e040c0605030c04050619110d1b0309080d020c0a0515070b09190b041b08030706111905130608 64
    0x10024042c0140181900030220118001e000d480c4840d05d480601c00003540b20002c5005107000341d40d518070440707001d10446144180c010700b1408881210b0b401d00480c1280062080041c0030107086141e0111380ca4802810400f48548000c45d035a00340700f415115403043d41e0b480401e150284004020001d0b1203002d00100300c805a0a1064894496165008003801681c101523007102e00443c10759006440c0210805038004280c81c0d4000022050445584404948403047c01150585098011044000d003d061130705000340340c940a01c03525484158201340e40c0300044c0c001030b84000d209121a00d081c84a03603000340021915214056860700550169004402c00940340030143c1c0f000504010003840101140500880c034080315030510710789030410090660b0261885080b80e801d04078850790814000058404020003941024402c0d41d40001600d81200000b0200340e007030041d00c14808001c0041e8104210702d81766261030389400082c06070003042d10340c0075504010340d480501c0443c8001424501700c06131 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 923744757 1250 923743507 923743523
    0x809040b211b1e1003020c011401030c17030712030b04110309060c03100308070f0602031305070602010c0e0402090f130c030e0313060c05240103140a0503270405010b0307180b0304 79
    0x30940000c3e80203004180580101e0750920602d100709c03070014902c1d141664404c40c00941c1050322043c00d19612411060031003001d80c4100034107804136031302c030012a0b0030600915010481848041c04681a101840340c50721121b0000700500c02024000e1003030a900c0850040490705514288004401401c00c0f8031003c0c000401c0001c005090108224400d008180c002d2415581c034146161541004003a108043c0c03a0750141ca900480c40d00d01c18040e500350860310355600d45aa18003907080100a50004003215409611502c401c00e0f623031511300304400080c1101d4400507100d8030301d003070241c00d403006591211001e820401103c0701000e42d02c55810300b03882092030400501105450814170380790354500510100d074034a01004420300e0151a43d130b41601e214001c0180a00c9010000316903549180c1402403581d0410320140c004c5019400d48034500c800c0f01c0d4501408035000c41c010908445080e0400031030760000108002103207030464510054480d1030110500780c00d140900c03000c42400003800080c40c0c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 923746007 1250 923744757 923744779
    0x1403122202150c2401031703190b03010902090c1308190807030917011a09040c0b0a021f05060306070c030504060503061f0c1e0809040b211b1e 63
    0x2010800902d03c204c0d031501c1d12800c007011091408140340b0000d2100301c034a8a54094104c00d10030380070080d240290180c8990020f2408604c44903030282807042030b2550559a07410820300940d0307408907001d005040261001d07650b0b800c1745110400324240f07a04074681c070364840e41c85072500500e6a2125201c0b2500130700143e444201e11b28040701c5098490788003016001d0108441001104d040d4084549031100610040c01806a90140020b810b0700b02c501410b42c0201880330028443e0300c00082540403001c0c810362329450040b000e4202c03240408121508415682c030100400d50800304816a048074450510180c203500390b50f40240140705a00656003000008030108046031100001d0003140510104091464404280010442c405440051351486424031000030808280ba034500900c6030019550351400d0700000c18070025140352403034140c00003003c0420000249414018030f08400240e40074015a800154119014440d0b060100d403084010105488031500d0f51400d4000480c801e0300c4003501c3d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 923747257 1250 923746007 923746027
    0x12090b0f0718080d030501150503071103040f0e01090b06070519050a0b04030512010605130e0903090d05030703080105010e1c0c08030d0c03050c090306060d140312220215 75
    0xca145024000007500002c40003040d107850105039015405585d5a0803c0b07540c2e61460a041c40200391344041000c00c400700041194039101d041c000714118180000c80c0c3c40d04c1c0d83e9403d02005610b0036800795202030100307401170002c0030090003a40050302003121f00c9801c04803140c0380d1903240d415103034008140c062414403001c20810240068035031640c021504414902d0542000b41160f4840340c0e8402e01d0004010011401e42c2c014815510340d14841e80d0765507407441c24225100904070000d4140303000c42c84240b08101003aa1120380301e80d080c5102e41d0182d038480c0a40e140240c08403030103800640c14002c0c40012a40380c0d403584527a488542e12003521681e0708060b40c0c01e0042c040d0200390402c0c0076501000a441c119001140c1241c03440c00780c0d80e0340800040d84c0300f180400c0da6000e00c0b100d403a41904500040ba2041c5401070079031681d103004174502141c542d0140c00349440c2d68130180f0400c500e160100b0401904801680020980c40c909140740e0502c41104d17400209108510f0302d00210400e0081450010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 923748507 1250 923747257 923747267
    0xc020a1520010c05120a0e0312061008070e011404120c030b010e0403050304020d110d0303020a11030405030d0f020f100903080601030506030a122a052e02211612090b0f07 75
    0x5071810030003986c1c1e5030409e0040c0d1160b41c3c001200ca10707000c0c8a80c000d01000c0740d403040ca415886060340355204200c0100751001182c0c5a00c19082004107000e0600001c00e0540742c8044019820f4824400070068900e545460700300703128168049240441220201f101090300101140e50095044440031300380c260b6450000c90000a01c0d40e2035400c403a00034480300070190160b00034102c0c681582c03501e4510014124035a41c3e01e104902070290103402030b44214900318080c0e0304000340f52801d401034030700c0240e0121419141c414990b022301407084c0c56042e03403002e241e0032a2265401c030b0f0342807a09011503d420008280d641e6405100280fa0454044402c01080e04c507501e0f0076211558020250700140800c402006034000301e03401555240141074001d000c5841c1c0000040c0d0422450003d0607121101c4680701c070080d00045a00032102d140c100c10040c2405807074000c544076480401c00c03543c400000c110000d010a00603080001070602c0c0c514243e0218000041840d4400d403400b100005541c1c902170102c403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 923749757 1250 923748507 923748521
    0x21302040801021201051201060605120709120317011211100327020a050409120807300506060406050f070f170304050606010801150c020a1520010c05120a 68
    0x204652022a04c003040c1403030760400f24121a000ca030007022071000c0401640c01c9030583e04c106800700f0020051480650b40c6046c1141c0e103d10141018a5203541c0c03a41823001c1da007003420040300003805411455221030095200c0300d01501e101f002000c0e207612680d403022640446030204034800c0200d2641c0009641c800d4204943c190707003904001600e2404100110040c8140030000c80c803400c842d0340041001d040c02c1c814028000e41000e001c0000c0c1400f50400d0b154544003400000800c03c203007415580700c1c804c6860013180351205a102c40c00041d80520000d046032800340286104035800c20040041c6c84e0b204055402010038010f20560360041882c00b48940c1508450003803e5641c001e11a001c007a6005e80510706c594002d01c20b9520740d030345400044400c1c0609001d0740040c00d0406104070000c41c8100c3c5011010f0388041c25846c0d2091316a0082c211800140c50050005805200c020f00b54022402e09107907000d0904000b88014401140701800341d010b111420a9242d22407000200d001446070000c00b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 923751007 1250 923749757 923749769
    0x30a0f1109130902060f0310120803040209100b0d18060c0228150b06072003070f0312030c12050106020709060819080309010b0a0806010518100302130204 68
    0x420a4101840d081c1d08140a030314411015180c0e100d5030041140289070031a42c0c028201d610300400c2c50500c64043d04054005d50a1110413280468500240030110300358501501000380c80e4649481080004d000040801d1030343c4072088070400403d4182015036a98045000c0302042d44120328000c80109800321101420b0740c5c0c10004034008541e004550100d80e0510310150404c2c44410810581804004110003062403008514a0814800d03075400400c039000000c0180741350007015262100b080e00f4041d40340c038405038810700d035240310310b0100500c50080100d45480705c0704501c1c3d51118803102c00c0305241e86c000d2503159285a40e180f4840d802091080703000c200c04021558450400a6031101580910049145040000314403903100246003c01c111540720105550f2600b5a01d403201508040e0040072550340301d0f600342c8070a960700d42c0090041c103001e03401408150314050410090788062a10487c0c4007511704280900d40743c0ca0000301040c1c03034041d02e002e2031655800c41c80e00000e00c117580c001d13 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 923752257 1250 923751007 923751011
    0x61a090604240b030f01120c051302070813080f010e060a05060a050d0b0a0b01090b03070311130306050613050919170c0c03010605041109041109040e1629030a0f 71
    0xf050320905180514000c0e00184690001c5a880392400c4100c194090805016141941810451407801c2010302c40c90000850000d81842d0165903465413039006100d881d06a0900c0e58001e000a00302003164000500801d00240b01840c49039a846894002c0078041960b41da0711000000c4941c0c8035280c1c1800200805003007602420070f00e040c101003025050310803020481c20844205c12640c4190f600c0b00c00c0c0d40306110110320b141c43c0c0c00425001440d40d520302c1d00884130140044640c5402802c07541340294040c40020416140140401c02e28943c0061101122032500042c460f5100c0000780b503012a001c1030b07000050b40c203001c0c00c002d040d5001149042d8120792000070034450341c46000c1444100d408094009214003902e9a0801c003da80c00c51000c603050766030a010522541c1303004c2d0040308852a00358803440c80c10404801080c02e407000040280321640c00001c0301c2c0614200c001c20100240207044040700301c28a40d003041140740301800702c080d0541c80040041050000c00351301144111880c01c0003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 923753507 1250 923752257 923752259
    0x130e04050708010c1e080901200d051f06050c0114310b07050702040209040906051b1204200a061e02070e0103063204061a09060424 58
    0x4554614076402040565401d0078541000342d8041c0d5862024014404441001807001910031510507100900d1031a26648801e1816030148040352481c07100481000130070355a452006a400c1a0340f0040c20b6807660680226800ea1000c030b8109a120588110307143c1650b880d0611041e490241031f001c1c1101c8020300000d0180003801e8801e2003680f810b481c13030440300d030b801d00a075504100c0759800f000c1c409045100500d000170708440c40340c00100000747c4020001030400c2c94410124003105c000300001c6883c40c3d0381d1018004010808964000c01c9a07410b00321514281031000030381c0300441b001d48018401410400c41201618581c18204403030f031030141c03045a116036680001001c41d03100f09400c01850100028240c1a14408100c29082c0c6d130545400e01070baa4690b0f56042c0040c00c03600c0d14901a03490640404a803046403086024400c4100354032102641018200a0101e0b0f010513001c00071041448a1490b55440307429060790f20210840d00042c8103400c000d400100e02c030f000c4124125404502c18 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 923754757 1250 923753507 923753513
    0x70507061404030f052a0307050102130e100602030711040204080a06090201030e0a0b011202060f0a020109060c03061508090102040b0f0c0706020f03070f06061a0706050f0615130e04 80
    0x3007500c0c40760340a59162036080c0c007140025260340c8500c1e00d80581550f40706060302c44040800c60401d504114036400ca0389040c105843c0e030b5007285c0101c1c0f00710201d00c000340390402c40400001c2c82d198004001c200d2100b411031426201035524851450000e007885008130180c402d80e13590b581500d00803d440300694403000e05510b0300c0c0c40245003044c800c0b0301003071801350a013285920010b0480119540004134070902d90800301100401405000c04a034070400c00c202080c0350f40300300309c064008440c00e50004200311243e85002801d45854a54560425141c50000c1191001c01400b200e1043e20500f8207010315114a80d840e0702a115581001c0b0041d44000340302c1d0840062000140b076a0640c1d00d054540301900e480b01280c441603041c18001076944240456804207004000207918140f1805c40010324560381d81042d5035002782c400001c2c44224012131100180000ba00610b5881611451075040078989040003c4802040a600030a000c0011612401d00b1107040a0140546644c803003983d45498a89 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 923756007 1250 923754757 923754791
    0x20316060e060f0907030807050c0d12020606041e0507020a0507120c120c03031805090c0304050d0e01021c050d0f0516030204051f03091a150a0f09020307050706 71
    0x608507501885107100060900d040408542d000d204030320003912049195031251041e03600044815600340c0240d40c80300c0c010303130f851007112800c051191030714091f1014410000717030a004c0000c0425004509140c201e00012524460703820b0500c00c401000112074440d210102d00d42080c00f80000d2140c03144ea0008039400d0300005501010314803d028407101c2d940c071880f9000c4808100300c8000c185070300c9580217000003805501c2280041d1108501040d40a0381d034800110b1064064032940044a13001003808188002407010621501140c00d003c01000300020000355501c00d5040e00100d2000141c0d921800b2900c14022034140c0b17904101d090206034119030b105d8000345401c1d604205000250460000014003031700984040b00d80050812401c5c00310070321260281c0d4403801e0154201507945c05007000054074424010340b00707004441c005c4840d03c0d1503400c40758519400714080e442844258020003040210030344041c1940c10341007006d070300c0741c0321402e0a0b100c2d4080d0040c011b028500f002803080d0728000d62 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 923757257 1250 923756007 923756021
    0x20405040c0f0b040f0311010c1a0403080c090a0b09010c0b0a02031e04030504060302030402040e1f0b01021b0d050114040609030207050a0b03060d020303040801020a021b030303010e1602031606 85
    0x2450391400880da5094a200f10344200d2140c034051800030413003080441d09500070034414010604100f2102d20503551084410741301a00703c3c4402000c09000d21080c998401460755000000b55401c0707150801400014521000d148a4008060800109210300d41d11038811080040c3d44031603c12201d0624140c014040d40040321007030003d99418804155003004d21030442d0280d50141c40b400e00d46820701400318043e61000700240c0c0c0083e110340403c060b4110030003601d0a40c0010020b02d07040710a041c3d0701041070354014001c05045501c0075140011421001002e088002d40c11030382440003041d5031808078054111801020003584005082100740300503900444480c030320aa007600d003810740b00d50400c55803244074014010b0000080c000a5420b04010b454040341500082c00c072802e02d966080c0c12400e80e03006000010042c2c110f000910071a180d4171502d6090020f044018604560408045901142c401040708c40900ca804845071840c2d03000380101e405002d01440e00d01015082c40c02c02a001e0800303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 923758507 1250 923757257 923757269
    0x14070c021f2a1505100b090f0d110a0e0c0406200114010608010e0106050901050a1112041a120412030e10020403050d0908031b010f020d09151107030813020405040c 72
    0x12020343c003008540c4c81040d201d142d40c60302c0c03146901e0400f034100c0000e4200301545034209125801078541650b4015049000c0e030b00c2400004580c0c03044809001d06071000750320a01d000087d0400b40f00d84049400169400c1d188140b4000c040340540e0810407510240943c4a28465403900600380c0301001c4195030141070307c0e4142c41304911640d842020390b0085c00c091040300002001440f80c0441076110740c00501c0c0510251602149402000010b10708229004002e541c0c2c0040c0001c0400554890398107900203003141e040f40078208004400008248080144020140406105803111050003a48003181d44c050800468601c01100d841c110001c0d4400d000c22780e075511600c07080c42d10783c130b00c60304d44a0159076207040a14104000840441c0d2441c0d644290404039540300e00c1e00d00506000f80c4041c1419450005005c50a105542011402c550316600c10903845400d00e542c12001c40d03021401c40b421582d05280c48a420303950800400c58401704040b000758001e00300400d1005003c00340c0140d20544003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 923759757 1250 923758507 923758523
    0x16060c1107120305030903070b010e190e1009020a0b21060d1a28150609030f02102f061509011e03020a080114070c021f2a 54
    0x85461200d03545400910880072000e040095070000030b442403010715080009101100e0800001703030766000c44440f00340c024030701e081501d10400c000d509441d5162806d01c505400c04024800380e4280483c1c503507803800000707981d154607580c88500310f45810b554080240303c160800c94850705411404003036000c0f00c1140902405118000c03541618040060402d4554070100036040b0041c03264400c2e12000c03008211078a102f80c2c1d003900c032800c00204a003072002403940101c00a01c0424583c60442c011400740c0002040111050b410300005040007003111880d60115440c04040c180d030350046071841d100140c2010500c0422614941e200800524520f074070100d0415201c0ca607441e21340ca0003442000e000c1e4240e10100b00401040003581c8860440002e810300781500d80c11039125004079000c41340750303805903207142e659484070703095030f11040d00203034004c151032070310003400c1089030009426030112070702905000940008120015004821040c0c5010005294910121202e200e102074403c820030103448070b41d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 923761007 1250 923759757 923759777
    0x3080319050f010506030f0a061214010509060c31060e0f030f0d03051b0a1d04020304020f0402130f0f09060b0c1c0e0d0602030702010f1401140616060c 67
    0x1420000002c1d0503200e001e4405411541d910300890b148030f03c054582103145039100804203034210300ea143c000304107000d22410300501301852145821900300920010b51a00a20103100396001c400c0300302e1301c1554a55801c1500582d440f8104078000f110f01e0515000c480c1c051500042c82a041080300e282514225415403052191030145915031060a60b804c2d43c581141c250801c0c0d050203070b0301440d002010040c3c41c0d400300460300c00d009100e80c020000d00340440c0003003031b60703d0b94488040031540813a0b0040d81e0070350450800d5030200e1002010401d100e44600c2e000304800f500c0c03002d252000070007450010401072025540300b031100d891000702e0090090840c00d011001c602801d03154100c900751040c2d840100f07105003609002c24807140402540000700304070000191010782c3c603844111a5103000303910051f82c2c0e00b800b52020342120003e80341034030410f0070300d07200c2540310a402c000d480c1102c50140c6c5005411000c24001820317440b4402c003042400c03401d03050440600215510909500b0f001e6120042e4134 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 923762257 1250 923761007 923761021
    0x10f06030e0a080405011101140421090305060c030703020c060709060908011109090702070e0f15030c0102210906070813050603040f0818041d060109020f0d150308031905 75
    0x70b54407190040d0146108120400a41d440f54103200001e0519000020341070380140c103a0301c00b2807003d80d806c1da00f10f181280e03520300c90071031102090224003550900b421020302c2c5948958407040000d14041c1d145c01c001c000684018002c2d0100c0302481689425115146003502d070103800400c2c0d5000e080c0c0010801c42c000300310342005104200210342d9002429040c001d0400070080d640c08020145400c60254030b800003000919803480500622405030844131615105800a5a410300c20540a11030390144201d400c190b600829803603803030240c184030710141401e007181d0143c481c414844003641012001903c1028421100090083c00c0084c410950585036288104540c1c0c0c0020b40303005d044402d070030081c85c0004e2311810042c031421024140c41c8090340e50039000a412034144400202804030725500000700b4100c180032841c00b40100950841c00c001c00584042c01e00d014101c2d400000c19540c824070380c4540f18a200d220000c44d404150259a07140c9501842e0384010a442c05020503030904000c1964 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 923763507 1250 923762257 923762263
    0xf0a09141f05101a09030f030a090810091e0c080d0201090b0a0e15100b031302042a0e030304030b1f050114090105070f0204020c0705030c040b030705150f03010f06030e 74
    0x103c076201d0300199031444104c03951003a90f41c008519554180300d0326070307102e019540a1019080800b4240c6816a42a190540c084c0c01c1c98485100c0303107021442c1a01050004040040f20140b0084c1d40381e0305140f00d902071520010308140d03a0400e9150f40301d603054840d003456054000000c0644202c481841c1616001000d03000d44c0e2078100d8a0541e500110454040c10b4096001c0940c8a42210a4020031958614420800390700a91700c4a44d445401c072200c400794102030040c814500700020b00700e00241c3c014011080c02580d82c0e82c00380300308003200003180490f540400949010356044002c2441905211b14a00c1c01080b80020004e40030704010000509903000b080b00c1107070007480202a900d4003002400444032a4025031040346e142e00b5543c001000758403184042d00700100d03040001d250060421040500e442c034180005440f40c0d0400d100f107200c903140440d554046036000e0f114401c44900c0c0d01c2152015014000a254a07c000800002050220480143c044540f140c400704918083c2d650002c1c0c0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 923764757 1250 923763507 923763509
    0x1091b050105071b090f0209030f15011203170c071a0105010206070806060c0703030809010b04150b0a0c050a0615080f1b01030b04050f060909060f0a09141f0510 71
    0x80426003c0c480385020039110342e122000c1c18a401061014640c40d401d0b50400c0758000301044840a90110760b0200c40d040400983d043c0ba0004401440b1104011020340c91040f01402244040c8020f82561000c15000301e80c0300e0410501f001d2003512505e00301e003004282d44c2041d403051f01d94521013100042c21000c415411410713075406038042c00943e6540e200c292040000500000e41003030003040b43d1a0610b000b402150042c51003656240494244000310a003514104440d691007a882e2403812480008410050700849a0341500c841c0c8074507400906071a407034404040504540039454143c0100101c036405114192100140ca0034007948503070358a030b81d0b104505040401a405208a49041c4112400000c010300052401040740b594640200707007610402d1319100900445901480780300d1404081c82036102c08488014511450101481480c004001d0a4206001d9642c0c0102c400e00801c80b17400c200c4d4036010710031070f44224102048111515215080c41d220a40380901140100d003003014010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 923766007 1250 923764757 923764759
    0x9150b090f0703090f141e0f1b01030b06160506070f051204020f0a0306020d060602010c08011503091703061e2b05070807060f02030f03072f01091b05 66
    0xc085a8803404150020402c0e0282540d040c00c80700074180c00595803001d4412620380001c0035014043c02007c8440081c0c80005821320385070440990304030305ca103000424038608400c46070500441c0d890300e4016001414270307000c40c603007014002030740143e4840c550896482d4070f4030400451b0025901c1d00d1040305c41761481142800010020040308488584501d207082d0010300040854155426000c00030f2040704940c0c4c0101e46064000c10b03908019030322882076170300078840d80c0020310a2a83e0080c0c002c144410501030710b50464080e001214442e44258428501c075540105045907072901c5140e40445034208032041c5110b21204107110b503214560042c900b0121101801046422061030f140c240307203000c28140384541c400a000c0351000305004208403030003042c10401130601c09082040003801d441c2c2150443c0150b5100b0001c1c00880001da508a079404061407419410040c3c8205c01e01424150b648040756540c1c004100d0400321020651044801a104448548000764124500b444002082c0326103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 923767257 1250 923766007 923766031
    0xf0402010c0605073005151809010e011109130915021c1b1106010303120b060702090702030901120e06040605130c03030509090718090b0d0609150b09 66
    0xe000284650011504140a03040072841020740c0100301444507031060705984400040d030309580e0034520704e06c00c0b5900042c10141c6036644a405001281c9074503d030382030701806030a2600024441c0002980400b4500600324024441d0341c001c041511410b81080d051305102c5c0380c1072105001511301c980b0a582200c1d611035404809046808440c030003d40040d48020254481e8820241d038482c007620034001c030425010030500703510009410081c5407032000360103414698003900c01440400d8100091460002081c0008200e171030042001c94000e02842c50000d40018002040c07100503500400030f0030759690280d07a08018400b40c1d16510040c0c1d0075040324444181c11080205022030129084203500001d4040400c00e814020384d101d81011055620960004802190f040c01c0d619041142540000c0700f89008101003541604441407040e5500c0340440c000d0391144803a00607141d0b001d070120519006030b01007100301c40c0d03070910048c002041c40c00e0348001443c1c0003035044540b810710100340c0244031480e10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 923768507 1250 923767257 923767277
    0x702070302040c090e0f04050c1e100504120506010501080901021312031103070c09050a05013507141c0519050a02041e0f06080d2304030c0602060f040201 68
    0x24800140300f0181a2010420b9021020030140c2c00400300300d0082c040d52000d81d1407441c190a02c02d0604418210441c8112084030221807210705070781c40034803102022900b075803100c0304085c4155011b108581c000c1030150208800e000034840c0c0400d00034100c5200f030720f494a4507521404998200d00c501c03040e10004014524040c455640d000613032424461003030400e0030074101c0c41c0e24840d00e5500081300449502031441010700034406140122608034860007814040c40d418030850244000030600c0740340c100403451442c16010b055802c504a5841d10b1041504c240c251907010000d4020039001109002c0c0070b101c03030282c00d131002180b9151000d9401c00c02500000c402c0308000c1c105031f88040001e0f2654170500540b04003580d914414004d50142c0c40e49950845040d01e0004c200b910740d695030201d02645080e1080003400030106a0850390700482c5815900301e800c0b90110303018003032486042c0507003180c04a030200c01c108000380c0c0c1c4800e03140d07240c08880302d039542c00d20407410780401110700a00040520f12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 923769757 1250 923768507 923768509
    0x1f0213150e10020723270a0c0804080703082511071703030705161208041401062d0e1005150c030d09030203160308011401020f030f071e06150e0702070302 68
    0x1078a54403410080601503465070240000c41d008402601140384140b1000c00c1c07001c220514412548e403001c035030070b1404441c9810b46803000340d0302403054094103011400c000aa661070501c03c240d20301c01d80c0782100140f914121440200802c824409000080c4180e00d400724010100415108580c010301000b5031950361820001c44031a000091192402250f031610034000541821001000f2086681ca120f280c0c601814000c590182c40b900d00c40d00e991415a051140190060001c0710010b03804ac0d07a0a80560b20034501d0b262103810b81d0025480c02d60000510451500d0f40140390122101150100c8406843c000706142d60320840f01c0f0030106600c1005900a00d0400d500507042490003801560b0402d40706a0074603585441c141800c8001070b0745c5800503c0104410070f83c1140d030311790a10007450801c0410104075924170424001c22122000422044100300c050040044100682109d90400a015180401c05042c010040c110100c0d070b0b08101240b480580b0500c0392081c1c6081d4010041245150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 923771007 1250 923769757 923769809
    0x5041b0614090d02150c0d0905180a0209060c010e0309040e070f1a1b06010614120604020304051f020c060a0902010806090a0b04020a020304050a06021f0213150e100207 74
    0x11012078020f0185009403803005c541070040d040d40103560001c1c0185a414080081910045801162281114000319504903512900c0380d58001c500c1d840069540c448000019290b0050a68408030b560810802441106c0088090501980c0556090142c152040b688036107401c1140a1100c002801070820451051130480510082455080451070032030742540d20b080c071f0307403425007a00a950300010040080310341c840410820b9840714164581400400201181107a00c05400c043c0306640102c00304041c40341c2404160f05021624682800a1006594003001394000000d010300c5409a41d002030b0035140140150090300b94141d4603a2410340d111010881c0c44140980012501507031080041f241d5103442c070050110544940045031900d18040c200030014800e600210219003041c03200341002044007069910710000003a02503120b03076180c0c8040400d40107a0780720150a000030a400d6030344036084034a0308041c040550300c00c5540c03150718405a07a0f9001901c03c40d081d0103a00c1c1281c1501807802 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 923772257 1250 923771007 923771029
    0x1030506070f120203010e07140328020c150a050f1302013e01060b280e04020d09150c0f1115070f08071e08040206070605041b061409 59
    0x90404407100c68142c3d100b1401c80c0c0090f0450303135250910303c06004016812501001c0380108100d090b40c5585080407640f201625001440c1000310010001d0181c4d142c074580507184034102c10002c580d1070090700c40780c1020251054403179032603242c601004200411045101507100d08407605001c000342c2c000da4011100070034018543d01c15241c5800b056940c003074603080c160700100f031180a810700c1407003100ba585085401a0b840614030010810242940c5517200d83c082c1846040c4902d08503604100c0700040c0d81002425903541d13482480001c1300205240b65520149a89000d480c43d121034003084211102100e031803000001c08140300445e500c1075139200744188507080d0844010b6861328440c040000c0c031051030554401d000314a03c0325240c03601d103500440704c40e40500a482c1c55000190364802c0003141250003100da00c01c000380500003074155280ea400700d60802e5031011341003080b860030b0308280c482544c03005120030780080389100000b2144e00c00c42c220311821810b1502c40303150905900401c8220000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 923773507 1250 923772257 923772287
    0x21206072d0509130c1e08010e01170a0c08011e0b0d0209060d02030334120f090b0c1005060a0302010801050d02010e1e1512070809010b040e07030510050103050607 72
    0x241d940302c40003030045030241040441c841d44681060100b81e42244665100041c0c2c0b0320100010701c7c004211501400e43c00e03d044500d00c038a114a41400c0c1c059440c2019500702c005000c00400d6000050940015800010341c181c40b940700341e401c00000020346056a4280031303083c0c3c0c08420a00c40c03202610781950321503000b220003003840480c10700540c08282160407911041140707500c0c030040320400001c26013091001007410710100c001180c0907a2240303501c4400c00000d108000e13580d902c9d0300c0054043c5081101410020307034401e0301d51009418680d541c5090307003074110031a030505020540c10b041a0390072800b582e80c140c580128a81c00c150a000d00661407a00580c10042c03e12540029030b1140c0c0110303c804400e210a00001c941f821003400b80244940c18404511081005101510042000e00743e80160307282c03424044a40f40c8080c1d00307014200212069a0007841c1481d122034624001524408891190041c2c81350b04080c03003240b1040350070910000d04035410010018100c030303100384290754683c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 923774757 1250 923773507 923773519
    0x3120a0b030a060b0f03010203010b0d050402060d090b090706050a09031518030507060e070e0a051f09020403140601140d0c0f120302060a0902130e0307021206072d0509 74
    0x109003030019141040c1e040068402c5135641e42d100025041c40d0b101c200c0307a10803d800035807865251084944035442245507428445079100c1c0810f0031903891000300c0340d0344400e0803810300203107090341040310300c03810700361105462031060020021711280208252910701c80291035065540d851034407003408103169100400700300d13990f07999000aa071a0301962454000c0c042d40e40c0130749a110740c3c58079104907036507843d821a6681c81244104040c44040c480d041d8440d20700003000c0707101d40314801130b004880c445090728150035410010101e0004820742c00380084a00880015441405503142c6075103030355080c05291000b000c0c54003c05903a0400940001d8128841c1c01d108550a80c2c0307164152240a00340c00000780e081c0c2d46540c0e030040c1581081901d4210b014001c0030002c4090503400614210341e010304011410f80c6400035503000003014416102c20301d4015104940140c44c200015407180b5084880c6000704050180000181c01d032180d90100120030102035030140b01075404141ca45402807091141d00107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 923776007 1250 923774757 923774771
    0x9080a0c1d27030712110d0912151e1505090103080417030c060c130506032403030408010e0a030f1112030c0d0c02012c0a060f09200a090c0203120a 65
    0x45c0c0b40120404038a010382c2d039641c1c000d2054a4100d0410712502081c40c02c0015081c2c00b03221181041c80340c0030185a0150500c40701c0d4407800c0f0403501401e0320309480200707202031002d0600c031034034241c000d09804582c008900007120745030400c10424880c203010150101c18107000a001903602040c103d02d10259000c2140d091004080303c00b441c02c4002c5032203020381c180108104250040c004080350113000e00b19411343c01c5203404120800c40001d0140c0001a1440e60b03c807109c80c584060046802401d01d00d0700034010700841c03004071a95184075844c203c0006106000c4a81418820100c06c6e40d802c8448015140d041c00fa0480080c10f0340018010320b02c0e06d4400c201d49148402640300d088110081034001040f4180c94203064000c01c4034242c00d528800c0b00218010b082014045807110840e5805500003c00100311801e000052000c100d0007408000b1000c103e015544038007103504407608080b10010700e110b888040e10015243d40400a8015178424800b0201720840d040740c491344050192070000e032031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 923777257 1250 923776007 923776013
    0x50312100f1e09060503100f020c010f0b03060a05010302100e041104080a0c0609080a201504080106080c010f0c020f04240506040605091009080a0c1d270307 69
    0x15100750303001180c80460101c0e40c254500c0b404420900400c1c90007810491355292001081c0c030f0380700f00c02524901d599604241207c4020f00d40c1071300d00441d0150020411002c0307030f540000003000c40054a43c4640720704000601c00700340501070301e41a00d5004e07107a1006000c010710152154010115462b074016103844c03a100030440c0100c080c00c000c1c03403488000c001080300782c20100c44504040d00078100708105442c090000c40c40c0040d403410074503406007110f4900344445101d150f201e0b0b04803c0050780034414100d4960702c001000080c105840411000300080703661030070341c5942d8010741d05400f030200c0c1408240c070910380d005010038000710303002410080400044d000086c04486040500d0050329a400a407600b0020240c440b001c003905043d034040c0d24040c01c0c8030b0040e156000b40307d046445401c1502c80100e169214401c02401002c0038002c550750176005251014160720240140b16000e010034061051005105003035a005d0301300030110901c1048040441e40ca91118080384a000b888100140800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 923778507 1250 923777257 923777279
    0x209090a09150b030304060c080405031e1203060d120210150f0b0c0a0b18070324090b04140c060408060708070801061d0f0904050607140705031210 65
    0x1048240940018941c8114600003101490120944045901d0f10794180d0181d01c00104403426140c01d0b0500409404071494910070303034400d580000d9014001d4084d40c001d032030710440307141a80900d401c0c2503400100c00c156600d41140003c03185564403079a01302030440454041c4a01d1840203043d4810f81d65005401c01d901025104c40500038000300c0c0140e001082111034404020001e010011780251502d80c0002c003490b82d43c40170300d80c05020403203c0c00110b0302d04216422542c0402829109842c0350340d0340c90a050b2a4236200d801120b19000500401150b001c106220f524840c40d403002e20b01d81c05883d0380d19458034144108104082520582e010108950b5404014200800d0300710020710540c1380403a402032503800302529260520524400500040d50010306001c502500c00f0880d82e541e50300040000c8510f85032002468100910000340418003101244d03240c86171002d52216501c0402400e1070034030318862020003500e150000d010080e5952001e442441d0400c56010700070701c8840d158040b04003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 923779757 1250 923778507 923778511
    0x32d020f0d091506050d05030d1d0a0804091b0c060c02010f02040e0105040b030309010503041e0b0115030c0509100c082a0f07210f050607180b03220501020909 70
    0x42c200c2c044203110100f4140c03070040001900068410070714031002c0780d40e41666801600c910300021501c9001c1c01e0291080d0100f08212009403900312150443e1500b082401507010703001e940c51460034129800b512880303c41d40c2400c0301d107940e0345603a02c580306500c8110080c480c40c1142c42c1155251007024118032400c1c000740000e0f01000a05041da545004204000c84d466020303001e005c2d400c107000302d00c030580c2c000040c0ca6009400007000302d0607814036a46055004404080141041501c000205050103448060f13040090b80f03840c00c10280b02c881106840c1c2d80520381056071b2004104e100f42250354480d9140c9090181f09501007424048465481c5913006440d04a030490040000480311603038000700800e10110364000098207016050141000d814440d186003081044900c3c0e0340041080041c801454146d41c006091325540d00741030380014075035011000c4d04955504a22000b29019070100d0072a8011201018002c29000c07009002e401500a240c0c01a01e141d5402e02901600c0d03124070104074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 923781007 1250 923779757 923779763
    0x81b011e2301060f02010f06060507140309060a090312020f070b09190303180e0606041202010c1218090e06070309150633080402060903070909050607032d020f0d09 72
    0x412a4000f201c8000d003147c19211460f8510b42c2808000c005060b00481101c0d030954010b040b000114030f03030740750051451041869560f0400000640c41040641c4101c01e1000e982c4580d0b000c3c803200a60107422a59034000a0050500c3d0b0051241042480c40d6a00204229040078020b4041b206001c08598140051a8801d50100310200c1241c3c98102c148040e2602501c1036500848640c10a2000303d805030183e0700400074446082d50b5402c0c25680100c00070350003158019040c042101c0100e1004001072815080f040301070300c4810011031700300450b004415650f803010004298903961030b041200a84540c202c2551062410040d606809410380036000140c00925101d4024200f01c65040c506200c8040207421030000460521101e43c0e071081c82540c008d5011034901c0e8840e0740c00d00000b814082503501c007e10359072410141d102005000702c0c00c107114124540741004400a0040350b0150a5800c859001200c44054130842482c4000d5000c2c1884081c4402c24a017060041c40b603900440c1e018841c19 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 923782257 1250 923781007 923781017
    0xb150f0d12020d090609090b180a15080a150c2303090706030605031903051902150f0f0c0304061b020a111e09060d050307081b011e230106 61
    0x10605030100003074103c0e0f40b003030710304044203900d0924010003952442c010856001e07101e480424980d580d02d0344620000103c0c1c0c4110300c02c0d0074000c011700010910944031002421201c14000b84010b80880c403c680c06400401c02c100215145429200500814000070140904c0d0703110b071160212081c1c82e01000d0159410026507070f08102101c20303d01881c56110404040c20040103202940300070410305980014503094000ca124189001d617514081c51091283d040a055001c020f400e500103940044c04010300c1280e00c040e00c07000b0300d000b0528003c8500040416206010071184200c0d03c000b56070003801040c00041141d000a47c0d115008c901d6000b840044c0d0042c030450042c04050701c0310300a190070840303440300380e81400ba0540000c2d124444109114400240015803551209240802d556500000b941d96502d0103140015484d0811036005400c40341d00320308846074441c1441011064041c0f0340c100b19401540707400141c094800342034804c228160306005090540e1002060501030b045a440d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 923783507 1250 923782257 923782283
    0x14130801110a09050a0b0d1a1023030609061309050304060807080a1e0207030e090a150b0715090201023a0504150c02120a030914010c0b150f0d 63
    0x41c9080f0050b0003144c030500f001482000f04440240c1202c041510702400450910a20048680000080c00d2200d410094080ca82246150f0010707468041e50405000d0250305400f49031000708034041214142e80001050000c5201407402000c0080042403a2401150340d10b015941d03d070840d00207500400200342188248083c590b0001141540a0086482045800c000c2d8800c1d40c404021076004100c6180c0c00034103c1d045c0340c03146521300c0f80054068082015814407101c06801000b19007444200200180400b04030511100c04640d029500451003a40c1e07000d501110100421568408038198030403643c140c09910010900424041c0101d090039020f000010700c85841c00120b02c04030802c001c010413050201c284403c00c140c0a0b1011031412000301e80032807010a00c28a8136032030400356072140e0440c2c9000c1543c0988104107603200050301201c0200400c00644400b40303a0100144441805030004103107403044000103041d550010100c030007181e40c030004500311080c0014159010614941 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 923784757 1250 923783507 923783527
    0x18020d0b090709170a0501052505040803120a0f050a090203010507051303081b0f0601051804110f1c081315080a090828030f0b011413080111 62
    0x2040006000003607569100ca46056000245400041d001d01d000c8a0040c0f0300f14070365141c0404c04100460352040c001c01c21400c04030350350400411488079080c0780001c03140d58040841d01c00c00607207085a070600c00460428040000701280032000801c2c02e50060b030344124002a020842c040d16005640300ca0001540f000345005040c00d4a00081a40c1c050101c01c0028485c4100307001c0a00003201c0d089064240c950f119140041240521003004440354452021a8140a0720210342c01d41260400c6031011b09242c400a0400c4072180112800307040e2000c01c2007032000030704004050341c07241c8000401c0d0ba04269595184210380485c2c2003815664102e001c140503c40c14550252000170741000310700b2822043ca445ca00034415880101212038803925024000d08001a00090310300201c00180c84001d111140d0580050b960760b0407100e14002800c00f604141240e4030b030310070141c80000c1a520038240c2c510301000d0398043e5100c1d403004042280f0545000549110078820140910400000140e540310415 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 923786007 1250 923784757 923784761
    0xe0d120e010807030b0a050105030a0b090403020d11011e0b0d0b011e05040908030606070816141501081c020709050106050403050610080c090612060a05010602191707050718020d 78
    0x2803041c3c041c5460490b800c040741e5a05208081201c000740380c015034a03034a2803007100c0903003081c480c0e00d504094400180700405130003181c01c10800065540c3c000c8003020070160300b420f8072013402100d64101b401c1003e11544240d281c000704a881c01c054819114400035646150301c0c0c510981c00141c1841120206c084030002a0b40b896009241c11a002e01c05000d0715140c000e010310000c1d289502c542000030701e85041003184010781e080c16440c14440b040b200c045060400303030038480500300000d5000d000c0c1c01c540c170451003072040c0b1305a8007024010108080ca10380d0100296050148241c154403e4103000036072150280111806051a40c1c0d525485070b1443c9002450038202408010941950040501c41e595000030340088008007144e0680344d64842c1404604000001c604550306030103808108503d402503904494103e494030fa00f203d400c0000c0903a0581028000701000380390190b07500c2181100440580500392181c00740080c0d851040e9281040200681c2c2c0c2011a15410f8010440d08281c19a80c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 923787257 1250 923786007 923786011
    0x60b01170a0b010207141818070b1207020a0c03080f0403081c06060c0809090a06080f06240d0807030e090424050105060d11041e080601050f0108070e0d120e0108 71
    0x81004603e13011a50010b0400d029006852081901c180d0010b1101c4600500c08e8815800d01001d6450b1107440d94000781e0742c0d44c03190000302e0900080d84081440240f0020b40a8041a0451000315000d800c640c0d4504042d4010300a1202c0c0e51014031010010405150040001650040d1410182c84803070b03c000b0244d641a50040c018807441d214654042460075048656006048960303c000b03507218031104004000a0300801010700c500d84814600040015900c0e00442280c00170500c0c5909d0044d800b00000403012400760010403001c005c40c00199140d0203070060074407074240500c40204070404505a99001c482c1500c0c0314121141d10130303a540104042092082196000303002540c1003c01189003031081480d016540c51b5240707000c500012021041d10064000481009d5500314010352800442417180181c8a160058000001d010301c0c007031540c0030380b40c2c3c0c06840e6010196a9458141c0d8401482c0b40020342040d0509001800a40c460640d4144104180c59043d80715400d080014100140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 923788507 1250 923787257 923787269
    0x20307090c050d090c0b0a02060609062202070c270e1203040f020f0a0f05090108010b01080610140706020c0f160b0903030702090c0c15070903060b01170a0b010207 72
    0x36120052900603480011209501420200403620741d909103011701d086140e03540700c0302c8454408501d6200036640420090f001d801308030b0b08156251100c01c02c008900a5000c0305191381545c0324809200d2013140c0e0003030500f56010b4000c1d030f8a61035035900c2c40c4014500c015203510742d10b1010301c20640005460301c03901113440411001442c805058a00c6890306100162000d0045e40b09200300408660b2201120403525901400104e60a030f032310f07090400ca2844d00e028880c810301c9148004101c1e07000511a00880500594516029403030360380c24001c8802548101e4010080e071208994204480140102592846410010b80d2032401d41c9032542800b00071003100000307801c4500f50340307100510720002e10305807480c04e9a103d640300b81100000380b41d0722130981c1c02500081640708001d020a510005004410340c5541030354404901c2c4001c0561101c82200c0420126020541c2400442c3c9590b00004e070b00f40b4103060140205442044045a00d20102d40300d01c1d0030b940b110985d40c1c0307550f4103001c46402021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 923789757 1250 923788507 923788511
    0x6020303070f030603020a0e060d120315060c050d0c0c0b031311034b010b030c091e0c09090406050405120f040308030c1905070308070503150103090201030b12010902030709 76
    0x425039000500146c4140300c8c0c0b14000d900840132070800e039528222650841c1c2e00c5241030440345080f103000307405018540081900078201000000d002409110007018465020003c0e142c44543e079801036680b4080400b0980380c002a02c03030f000c9005070f1100c00550080e01e60040010b0155400e00d4800000100d03032070901e020f17801ca0b1002c0c0a41030211844016075981d04604d0b01444101e010203003a800603428403135091120040a5504113600c10361180c81c500d1400e0f000d0703440599002c010301007284010749a41421204070544903481c500da51013015088044034094070f14014112001400d466070544055940ba940c420510013008410400213000307409500c003142c10040d0f0081049114001d0b880302519801c000800070744200ca910046072901b1080380b0050072149280c0708011718503001444110045000007010034445802403058038407420050500c0143c4107041001140500490b9034200c0c1415111440c1081a40d00c0d41d4070f144c0321806240001074158035600415142c07114650050074024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 923791007 1250 923789757 923789759
    0x50f0309130603080a0f180e0604110a1418150c0c150d020d0608070e01180218120c041d010f020901020a0b092e050a0e0706030f020f0406020303070f0306 68
    0x1030105050b101030741c9150415144180303902d03031b0a0380c00002e40e01030100f41c0b80e401c0310080360781034007104503030702400381543d081008218241c1196070500c64030740000c002c6140d1078100c030340d0280010001c1018407040e150300041e0108840110301320341e40c480c03414010700c00045468500100104086071207400121003440f4010b5802d028003095114080e40c24200c1d94002446118070005600700c14020400744c812524804d07515003036480b000c8004c0c050300c07440b083c2101581070240558001c0d0b648550000d110104a440d0110401c8000c18984a204005000d904210202691a2310401103d154040c164203240b9840507411401c49003180e60300404544103100404983e40d00003807030850b0039444203448207540c588034500351500d80c4001c001c078080c561482132080c0e01c1c07041070085482c88001ca2420b00183e20f90403807001c1941e240000c01422a03001580400200b407003500314042d00e420b50398006140624043d58035000f40e200790050341c00b5900c00400d10a13003a501042d8801d0501552900300012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 923792257 1250 923791007 923791013
    0xa0908010f0203462909010f0501080c0309160902130b031003060e07090c050702151e160c0e010323030f0a11010e0109021c080d090c03050f0309130603 67
    0xa81544c41070940da241c4040c0040c261242c0c00d600c20304008100066445080d10b02c00b207401a940104495980980c0c481c03000002c080310740d40141c41c26503005840300b12140c0d032140355241094000500340d0740c00303116050405000f0000080c0c1c58004e40301081001d070383c4580d0308ac035002c8a035285500400440c0d40420400c4854118100600c090b29449000803540070381204480d03180c1b00c4544c1010020a00d44104910110780040052030308034403d403410104d210f030303440020440e40111407843e4150340210040f40f520f2a4030a00505650006c14084400c0c8810b83d20303500d221080d2a00120354003511480180148105442c0031324012460250300302600000601d410745034080d10444640c1c041020618803903050140c003040681401c280300070070203201e41c03014850107043d0020040e4000e400030604152900074034505105581e0704214194030701541c3c3e02c58030b0010812500c05481401c15020f01000003142800042035207511540219200c1aa0f41d08001180c181c1110400f8003502d007400070000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 923793507 1250 923792257 923792341
    0x1504150b0d020d2711040203040302031206010915030608010e063907060b010e060a1b0812100609081501030f060603081c0f18080a0908010f0203 64
    0x10004000348056110490803c400d406041d5034140f2040003410030b1066401134a014411162450240c100c10a1300d02c070100901003240b00940300500160010040d01d04040f071000050b0f1340141041c507240c8199581c0c2c040c1c902a00014154500009413034010406c21030ba803d01680e4044045030001e04203506010704032041c2101010f4290030496407144041e0058010502032071080000881c0151f40c42030145881002441d840040c1030100b660525040b085040031015280d28546c0d40d00e0b940295000b03540c800100c01e00340d0100311034201007000b03540c000781e243c05e03921802014400c4007101c1143c200403025122202682098a640c5d005c0f4501c22940001e40d042581103075000007042d0041003460500a0181409030405003e401d030000741801340884d60340c001032900c201d850741000840c1d04848103005960101c0d804901c008026a15a0046090807009181800325800c0071203007541c0d145002d900f9100d201c0c192400d41c40c0d021041040350380000740ca01681324400d001c41c0c883e2030010051910 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 923794757 1250 923793507 923793517
    0xe06190b1804230406060f14040c09030206270d05061803070201080103031101090609050c03072304050c0706050703091a070f1b0b04050a0201180b0d020d0209091504150b 75
    0x100c484920008181804040e9001030040c1c07010040b800c10523502c0d102540c6c07440441d4041c890140b86403543c008503241c0700382200026207034020301480c070300a0400da040d81c4000c246814840480614010458141d60b20030203800c400c3d100700702421041c40c1655100800d00c44000107141c2540040003040e0060fa4058906410740742d26040c01c0c410550490700b00350041c00b403a18014611844c1154071424040005140c4803000030860403290031b03030b03140c143c4002d1031002c14046450291080c0c1403200c0b0f40c5426000141d0248000c0503850401440740c0754082518810b44030760002c240e42c0c4a01400344400105a003203003c8860000811030b05028000805032460032229000f0040e00e9041210802e208038001044660444031549281c10a424642d841e640070840803404900c107164001080b00344c23411887d04580e0007041d12401c0407000f00c0740d180a580618014184944e08005040340c6036034004007103028410400318200301c50024828401115004100040045540c2e801000704541100c1110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 923796007 1250 923794757 923794811
    0x509090c0d1110031505120c060306040b15033408060604080708030d05132118030b31033c0201180c0e06190b1804 51
    0x5100400c0d01d09084410314101c18402d40d1200d200e98002c109035500d9001003d1901850032800d42d0903035568100444000e1041d0221902e40101c42256030520340741020f183c1c050406440814105803010010f107603120808000e480e404004030038000d500c010080002c002c5448520b0380e1a40da1900041091090134040c2094100b01e001c800040003500d84e001500c0007442410110f0381e10940310344c040d40d180d0304403c0f07400c0007813460b01000520814504103e1410781e0f8100d102011040c040744007284c2c25150010322201448104105828080448500040154001d030020701c0c0c1c0d0305008200000c2940300c400c0c10055100f00d80c0b420084d40f02d040035220420395150802c080f02024946401c180e4003c0d039440b00c0c5400c17921010f2140d14880134000752807440103a0713008011905c60814040b8225214580107005848044014000682603000c015000103000301203040071000181e80c1d0040740403036049540f032004041401c020924480044c0d00294004540a2103408034540c82414143d005400170 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 923797257 1250 923796007 923796019
    0xc1603020703020319020f030c01051b030c0706030f1503051020030703090b0c0f0a050d020d1b110102030c03070e2b02100807080601030b15030f01050306010509090c 73
    0x40600070011140103581c0074003a40c0300c2d81101c9901802e5541c0c12941070740221848280303c0c7c65072602103407420314a88140c4a1605040b01d221984c0d0301710581c4489400c4501c010403019511480400802009080d40c0d40c4c08030b403056907200b01e0400c1c0c3c2c403180b0b082e0030b441d4080c5a0910004da40407a80040007980050700058203210300c0c46450055283c80010400c9406c004244040c2e25030507000700b1403c038080c074516001d544445641c90010310074100841c0c41e10b10244a101d550710320881c000d1a001044c001c003d0706141c02c261900c41240c0b5003090203551140310701a0b071484075400c400000d43c440b0302d6400031420b43c540444545641d201c024480c9040141541d0081866600d92170007045805045145031100c090400e086a1712030302c2c925059105803862028003c0e070700e1080100350310a05c0640d9414034952110001035001d014500b0b401c0b9440740d00c0460034240801080302035449040804000c0c07119514003c10705040c503d040e0410341c01140c480041101c900c0f000503504c3c102c80070607140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 923798507 1250 923797257 923797297
    0x1a012f010908030a090c050d050705010e06040503061e01060e030604020d1a040507061403012d0b0f03060a0b04030206030103080702060d0c11010c080105010212031e240402030c 78
    0x22140100000000100300c0390340881401104d510660250741107511810301003858030b4480d41040703d036100e00c9100902c40d41c40b06006200652092031003030301a84014105506058507400000d003041e0003100ca9a0f0200e003800008043c2c9483c0268060041969003008034004214401080d00c0b544004d0000e0b0280c03410101c2142000101154030016080c0ca1040712490304161a000741c842a9511942002035020030f0f08940c0510a00201e9040b240c080118001c0c1160443d45000303900401e00510360154406003000489203080401407100f064289046d41e540d1800f0410007aa11900b41c00c111342010044c00b0502c01a2204c0741201d055075001040c0584034041071002400ca032050301061035000e41020007000340150011200b8016804000091005640c52441110080400d10407603005a21616480080c130451000070341d0484141c4003111108804540520202e40060f51401e00003040707401c5005000203880fa00c941860f00458041d0301c2e604000d01e402c0320304c1c0902941c060b003222500c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 923799757 1250 923798507 923798597
    0xf0d0e0d0818030d0503010905060109180504020f0a06030c0207290c0120030105130c1e0e120f10020406120e03160c090c030605090c130e01091a01 65
    0x8009040c0b10801011981141e00340c00740204581c200384031b050052070512012991660250803d602504c000c0e1030540d9a40102c507000c203014000142c010790308a0003081c3c1c0d920498507100842000780030241c030082043d4442e61802854a440d1fa88480480c00b80c1c1000c03801ca1107512250918200350904056494a1400c500c2034014182c625031960b10450700d03039000000c075580c4405141280c0342102c3c4100140d03018115002038442c6100c140300001d0721203001d0070301440030345550110f081030782c6442060300d1349070310c0031428a00700c1d0003446503561f104504908900000308001e283d080c6400ca010750400340303030400103070944016130314805406850b030211000c541410401e40d0310603107401c21030701941c421034101004062154014608158100032910700954002d01500302204da01805111b0281d40f1030403d41c0007a089044c0d02d010141c8c140c8000210b2800020019019108407180060398441000181001c2d076203401e440ea041c0007152040d088800202007a038400e84004d40168800865524 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 923801007 1250 923799757 923799787
    0x3131a04080a031e020c090601031d16030b09211b031b1b010e120f03030711010c210905070f0f09050c030c040b0d0b120f0d0e0d08 58
    0xa00988414031038588890700f0705520203500344100440702070020110780c1c50350080b40ca4020030305a00340c003c07641c100460f850754440e5110701e1700b501d40f070850301c00301e85111049a8144001150110b0310a03010b042d0500030300202d425125000a107000c01002085060241a951001d044119101001000c10b02c8016400c101e461880c000041c01c090f241c3d260350036141d0002095241c4182102d901c50030245058121143e21032101305c4a05031504410f4000003400c0103a42080030300c521426004518841100b81c1007080518002d6107035489a681d81d07040c1d2640301c3c0c02c44141805d070504004040054a201d000030b06120104605d1031007000c90401100e041c100c0c03400840d0313803012641d031160800c000796210312045500142c2ea4498030a2005407603e40c09150b03140800c0d1800d55003204100070802001000c400108242c0403050408503c060287c00041c000c2554003248401903005407000076812a403d108141c51034100e814004a4581d000000c41c8540c04011002070a0513400600c4004480c910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 923802257 1250 923801007 923801009
    0x80d1103090a0c050114091201090f030c030e04060b03070f030b03120c0105010905010506032806060905210d0c0f02060703020a140d051c021e190203131a04 69
    0x18119103950381c28080581581c400040300180c403580b1070f00344042055803140c10146d40c400c8101c0d13901401d0070408000c00188440b802043c00d950b65840d5080000074004200843d2294040d4641840e0700225041c06080c07000ca40389064819131a0040500480354140140d030b412000c035280540500707625130801d400400c858903a0b03540c144203041d62104800c000d000140b4940c50034000074061640e032804500d041d40c0c0207003e020b0340501e081c03000034a043c40101c03102c04124111200c20302e03810104410002224400e82161001035140b000030b019500709802c0000e8403008503036042e18000010848242c0f6a0340216036241044101c2c0446c10500c03e2804e4958800b03900104444c0c1e0759451454042e585500c0303860100c41444c42100114000c02e00418483c1a1220a4462503d040c9198088150200c212084090b44a60078400c003140604110980d40c00810890301c59a941c1508240300407801d0400d0610004650003040b194141c0b008568034142160710401d803a0840682c1c3d41c908442c00c1c011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 923803507 1250 923802257 923802281
    0x50f07020d02090405010e010b0904020d0f051005270d170c04211a070e0105031e0a060e09031c0504020319060504030f0f2003160501320103080d 64
    0x40d0f0140004d210b01035020710030002d5a10700800c60b1124250500420075811980a0751150070071804401281c14142d591030003522810507a110456415144000c0392416160446070311003849200b29282d21201e40300f45601070010041540104200d0001c1c1622011f180d4100e103070300d601e00440c255a03804400d032006408170000b01c4841c80c2c4560524140f0007103034030058075103003129128144a10300e8885441e00070402551707151466103001d00107513181d5201900110200c8060042c0c85100b0343c40004482c0150400500030540600d00382c00d03a000c044c2c010b880601e6a0300100954091009081090752044071703901e00110303c135951800064240043c01d00c41da0011400388008100304101d03540114400c62190311810200c50034000121034034440c4140348004501c110008081403c01ca1758000040d1800b0f4040764507101880402d442c080c0f08680003182c1c240e4540c0f1081020342541c0f044d0001030b518a204501401040e482d0100c20410184000751403910001807179880c07140c09030000c46404003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 923804757 1250 923803507 923803519
    0x110a0311101209061a0f130203090a02090705070302070b03060102030a44010f03020105031503070b0c0a050c0d081b071a0901030e0a111021021c0c050f07020d02 71
    0x66400d00f140a041040071410b515100d48480341800e203400010081e046c1005804444421015001180250300262440e5000c0c450042c481c80180c0e5a40c03016407043d4007a030303107140d250003a5103030291400c02c4d0394001840051060081220f2030f40c0c00030940b040543c052520f00c02c600050000c00c5c4e420604000c243c1084200d10b1070f40852440c19890007110b8401125001107160786c0c5a8408000314080d00000340041c230104046600c008c16803c0340641030390002c00f9120010303a243c02148140e8401001071001d5001040d444080c86802c2c0001c480c0c00300c2c103444407070b21440650b507404030901c80c0506100140e1001c903601c8960b0081004294041c00031010034002d020b01c58152000560407251005001074140a0140d843c18408a00000551740c0200e040b40224406810400c0f41064408803004218407212040000448161402a00b014400e001a40c0f40705140c0c0d030b542c00190340e221055030541031202041c3c160b80c3c804111040720b070700b1802503a2178410720b1000480ea50079010000e58808 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 923806007 1250 923804757 923804771
    0x10f200705120106050906090432010617331005091302010c0809030c040906050105091305030708090109090f0e011a0f0609121009110a03111012 64
    0x2800088220035900100e4401941ca40b4000b510b5007600c84034094140c106024501250280c1408a00703160402c0c440d4070610040f4070480003082d217078075241200300e6408204500d428240d5600b0312030440507180590341c2c040b402104600345942c4200e5100b4400003440ca08200303040103c040d00d4401c10a54100d000c80405080064090040020a0103032610504044003c83d40a0b030b00065030101481d410b846404103401c0541b01c0c520b031a000300c10120b4240c062111000c0030307a0340c0e0703104001c0c1c9144a01800185075042009004600c14002c19104e0f0144103414540082013001007952113896124005030b41d103002a80040351529980d42c0b017000b14609107201038030030304a0b41d0401420110707884002c120b000110201c01c007160003040f0600e034200030b804c13100d030180d410b049000b89684a8041c0181c003440c180c6c0c250031803030003010383da6542c1e020395079204500420110704865895490111141720b09d060440e1034407000c0810701c260b050700c28903402c0800484580100750665907542d090008100d28 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 923807257 1250 923806007 923806067
    0x12041202042703020706030228031e0504140a050a26070f0302010f02180607110904080a0e060702090a090f06020d06050307090606080601180906090603050c01031a010f 74
    0x1482c2544403c0380940103164001c92100e01c05d100b90350b4900d03400e0714002c002c03604500c1c40d00c102c1400b20041804043c0c58201d41d140a403041c44c444140c40d15246800261441d0500303129641017030b0540320b45096000a1403917008a4000100e8204c400c1d0842c001002541400500c0c6802103082800c4881070000401c2c3e5409020041c0780350f0180ca400f03a0002d1280c614603030070301422803161511602da031544011006485003410030180c04c4041c4202c1440140c01c1e41c40c0002100e0940c103d9088130280710019a403030340300c1d90000d02c0004e1000140c400034100051a800034145001c01008080010764030b010100c180410210120400e0360429000c55540540c803060300302400090141c54007910500340005a035071414810b80d001c540c2c1545c0c8407203080e152240112a0000d10381e00d13070b103c48660002d02098084445c403842005101c680e1000039114035514015040082c0002640d05142c680b81000351218591007403405202c900340703840c0f00211441601074450300207080d610381103000c4011440000f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 923808507 1250 923807257 923807321
    0x2060126150a0c0f1425050c100302030105010905040c0c0609030203041401082421030307140c060412050c2409070b0a030b0a0e07021e1204120204 65
    0xb031501920a0001d03211615080d18220f506034582c200245000e00300e41e80361560b000c041d00c002007000f9020420a244122002d6161008076001d603295000315110b080740d490b10000d9249440c40509040d41950b24260021700052003910070640030340d07140c0d82c0c10f100e00c40c8513115003520190b20450410001d40c0504000356640c00c60b009001904101d0240c0d10303c2980110440740c415000c540e64002c00141c420004215500ba07800c005030041c081c00110000703820011060514142440011034581c41c0c5598001c041c1e01c00044061040c01d003c000340306c40744030007103040e5901c603802c40b42000300e080d090070040310071303208180052485024916000703010801240e07544046d0308144400b1101504c0d44c9440c070b42c0365000d034400c1681c0d4130420071580e11201d009400c41400b0000c0105074401c840e030399010250704004111b44080068000d41c010f0030100f10000c03c01602c0c0c50718072008000c3d02c00c050b50100e040744128001c0000c1d688403518005c04554503600001c8c0550303070703020200280d01c507407140c0303130803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 923809757 1250 923808507 923808511
    0x19081f05010611030d0c0e0306010803030f0612030a110c040e0a0b16050318120f13080f0309011809021b060705130e061504060207060201110304030206012615 70
    0x45003400c1000000b19035101d04144183c1e10000d101540c500f1418121000040c0242481d1070103100c1000c0614503142e505201c85402003180070081e6590385014441d156640100410310762184940c1c001046690702c000095a019000c28101203194000100600703140c41e01c03001d100d540c80f40c1050380741040300c0404034100821074492007000b1082c0e1506c0b03186000c441903ea2149001070420700010b46d2440502c068400c18000c05000e840302084a44201c85043e840801030b072010b24070000300b641b0950415600240107109030342c00783c040740e409046010388a203d0b0160050401c02d51038240040d8030081120400180b00881e41196560542c0c00c420f811100704103c4540d9600035000010170950080341102d44c1c0703003101c0ca0440d51050a00900188540e0003034410340e0009501d220740c23903581050000400c080c00903a0000c140340303440e2250007425a64420124803441c2c009001703000000340c00007906419204441011018810311042c1c03040104004a9084818232a0f02c0c448004014240030a0b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 923811007 1250 923809757 923809813
    0x309090518060c03040807080f070f1a1008030a03020a18060c0317040f080f09040501140310151a0c03070807110d05060a05150405012c151908 63
    0xa40b081c0e0780d0b429250303424002124080c1945008000384400a0b01140081c51100c44c4d5101c0113042003160344600c0804501c0220480c0d43c484c03003240b1944584100c2020540c440d40802c0e103020300d9420000d40c541c480c041c2d60014820325401280c4182c03204d0042c034036103046100303188070071444c1ca90f250310040040700040d4080d070202d00d100c803000ca03181001c0369005204541154160a0820855030b07000c0d46d07a844008600744500742840700560a540340c0c0603950085c25030314003003810350426204140c2003071900d103450f0856514280c0ba81c04800c1c6e442c121f0504980c0c1500b9036045411302c3c0100070085101d10f91822100d0f020004400040000000240c42454000c105e440894540c120030300480c0007203010040c000f40d00030000619039850070340210341c1c0641d01c880714104081710030300464140c031000e0304842030b010f0308003101c01c01401220030b4440f9000c05241500da441e01f0004108000141d0f00b0401c0303800f130180f42c02c040c0c2c030a1604078400700091914404490842c204001600700628542d6000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 923812257 1250 923811007 923811013
    0x11817060109050c030709033c0308011403070911070212010c030c03020703080a0f0b0a0f08300304020604030c0e070e0303180409060e010c0507120807080708040309090518 76
    0x100e8440001380050f2071013014103132034102c0490308584802c04940700000c6401c44039404450340e24019910b03050454098107603482c16410301c078018500509260300582001c1c034a03a01c0303c01060b00680c0c00082400031986240d0000585c0999000310003420301c118100650006603c40d4404114801540070510304441035600308100407a0f1f4400714164803525401900042455001c58140c0c0117560150300c1405032110300203406851100450700c04907560748210b45c1e4080020007006140c80c240091038000c0840d841c810f4400d000040f14100502024452851000000c4001001c42d19050105d8000d56040740911010960712002c000a42c00c049403506c0020385011403081c603a00b400001c4d104410b40b82403007024400080818803006059610007541c02c1511560064003005080c400c4080014482d5100346e9140c0c900e00b0102011035524560340c040007132420030010900d500c000b545402010910702a460750700c807424103e030310072016005002141e24040c180100903d0240d0740d1032038065000700b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 923813507 1250 923812257 923812261
    0x61509061212180d1a07021011041a0403051c2615030f0d0e031015030209090c0105030105040c1101142d0a0b030a05010501182901181706010905 64
    0x42c0449a4141d000c01405e040c90300c1215100268019405a401000c610490300c82200c80d4010310f00781c40c242d44101266030300005041c0605102e603a504c482c1504195183c2d89003618541d5819036500f40300f480031039040740c880e149039030162203102c201888103108480700c00c10b20540105904480f07000d540c4085030b030384164120304a600b8007243c41c400d50300d0110090900100c2c940301c01e542e0b428844100580c5401050044ca540741c060b4440e50883c180c4600c0040103c60961040c8000400080c10711091548180d540c4915a03a10400702d07415960b0a80d0040f8001d96140e0007a506240d00020092480d424038001c41640c6401c0a00f152161204102070030072104510161804052207290b09121404d912000501d140041d0308501103440020b800c4880b401c522391185401c4981c00e0300510585149a80c04c451400030301e020760150f030400484182c141d03044408407602a4481c80c64050305009a4190b038042001c00703164144018882500311300d82000000200300d4a8040900412281c1e03460f040c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 923814757 1250 923813507 923813509
    0x906170c090114030a170d11120703090816050f0d090e0c0903070305031c06210221030f030f0109050105030d0804050115060507020a0806150906121218 67
    0x2401040300c00040e00c818400d0f42000001c44103801d60545441d0144141c00f482c4d03001071400044070b507074445041c1c140380d200c4182d510480d042e0b445c20741801d91524800d0180610300e54580c0869074101d06103003800101e9400b240760800700e50060008410350048055031131410b2050100d038a42801002d50300380e5512400b030a4055030b500c48140590b62803485800001005c6215141c018240d00c10001d0840d14200d80d2945c0e400d1859000300325030070f0b10742c409141442c50b5a1060240b1000341240d60104040d428040080c40c0310303c602c0280c06403195074540301070b04075210790240e4a07295505003030580750784998000245016520a07180a07000030f6000000248040381da02ca124140c0c0c4005025007580724080c20b080b10b9944d001b500030383e82d956813a42c9100c4105540b094200c014101511101d48607201130042014498040d84442000e806c40310400c100e801e28003009440f440c20494a91655464860219214123a6641a28001e11074648005402c40e0f130344015045003c008944400880b1001d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 923816007 1250 923814757 923814763
    0xa080a050d060b03240301020f0c150f070f0c0303271104050925050904030e12010b010806060a02010b0a0e0f01120b06040203180a0b071d0a060c0c0906090617 70
    0x351048504c450110408484e0b18100444260b0401c5c020700144c1800d0321136140c490141e00c4803100395420391215481458010a130000a03a22002c40b481f114030070714010b00040d020030510003441d0308202e1a4944081090f02030b80c8903801e4428110400301c0f41880305c0c0a0f0300401c03071018100b51600c1029215441051809004080c40381c04220003403e44c42c2c07442910a081c14000030f81c4481c821080304800b00d016102d51035070b10300c10b42c002c1d5030f80c80c58030a61a0510010b00005003e41c0c2044e4101034a022081c0d80211084c0c0c0c20110584a055454070328500c00c80c01031848505099200800c183c0000719103d050b0505405407a0034800d46e0706a0b662603946e9074119480c020018042503a000c001111490305a000d142d00560400c01103a808000c480c5207814036100d40801c451001020042c4001c60741e008040604401e61a0052079905502000107104064640308210400006030550b10812801c181c0b004014642c81405203c09a2106401c1d00680414000c01100c4211100044030400c800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 923817257 1250 923816007 923816011
    0x2090102161401050f0f030a05250903030e0a030602120601110a1a040f0f03080f100602030409020706060b0313111e0906011b0303092901170a080a050d060b03 70
    0x20200a52441e0b040b90042d1200c0d00200d4005805001c2804180c0c031611890006522600c6403074000120791511a0340d5031512038080b038240201160780d81854852036000360750441030302d4160402415894204000540201080e00300400450000c6080c9540c6010204043d000c0d984c00d13200c03203c0c401d0469851540c2e80d9024040a042d01c030340c114001c1500481010400c0e0024002c0302403014010352511111040f209044041b800a07003000200030614000240468000e4208d00e2450f21051a100e4005c1d640e0080707024001200b82d0018000041000c180e102200924005145c1a281d182c80b00310341d0012070711903900b61507201288450404518140e4144982a0b800c0a10481100c5e0840180040000c000f0304d54ad051041029400c03010748407202c0c0040425219a0f03001c9245201480c2c1000700d403640600302000141600c8403080101d003120303081415130300600310321021b8654003502c5a04c2c248580c0806001040300003000250300d5880402419101c00240040c040c80781d407849294001c0c441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 923818507 1250 923817257 923817269
    0x30138030a03090915051216150f1103070615080d1404090b040e0115090f0b03060f13080403030306031a16180f14010206090f150408120a0209010216 66
    0x105180501c04203105a20001c034070401e640c017041020f52290081074240b04441e040807016031103801c40700d40c8036891100a070301030048000000f40458082c0405804624014003030014400c402000b0f0742c20310405c00035241031541080c030a10441c0d00040c0c401c0c0c1b180206015000c042c2c061445075a03034080c0600804900350308030801ea149054a007041110061600c2d030800e543c099100d0240705a01074090040c80c0c80fa51920340715182311303490190450101e4408210143c42a420b00032041c00c10b40c0e0108015610100b9080802e4a655802c03480c42490792030b50800074845803010601106160303050307024005483c07043d1050141076491607112000d1010403594418510300c0070901d090305610644850303005604444141c07034559140c10b05840c10311056009014010903141c0901159030741004141c0e0081e0420000d00100e4541c50708280d01c6480000341c02d0100300c15070300070030304111000c3d0480f1342d41007550700c140843c0d081c51103108000c0e50020a0007401031181510918204240e00581021100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 923819757 1250 923818507 923818517
    0x503043201020a1103010906050708100f03020d0f021305010e06012606060a120e01141303090b0a05040b0a0e1e010909151205070e0132030138030a03 66
    0x210f541d074554200c00690941e40d0507548071074070b0000040240c001c41c0e00400c00c5813680810740c03404400c401903e007078651010602c04202d68080015803501421001c52503000001c131925084c1a0010074400c0350109203201e4a0780c034117000085e091114403071090007120260703035a0368072034000468107500d05401ca81880c1e02c15400c1c1d020610030700d03003d0b006265080f100c0c200200d04c032a0780c407503010880b1045440c02c1c01301c0c1d44a01b4402e505020803a42258400ea043c180c003050b01d1102d44004103070480c58000d0345103c4a0010303c50160380d01800c1070740e00603c4501450366440b1400d8000500d04815101103a000e0410714030000c3d841400201d8203014104181c0d05c0ca0744203031500c01800050106041d0400c444195080046603650309500030441c4240034400a0004518015001c0220b0105900102280740c80030010203000c20190500d0036080d0004808030010403480001a0050056660141c0d0880300207005401c07049010040c5a007801c078035681141c102255105041d12080c0000300140055 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 923821007 1250 923819757 923819773
    0xf03020a171c110d0c05011d07171002040902071703071718030a080712061d0402030c19090b0603072a0b0408090f040c050d020a0c050304320102 64
    0x444145041141d415a4078000402d0b04000001904003d04c5428040010b004d50050106114090140070403041d10107801c0303000c003150441981c5d00d8101900600090150103503c07070204800030090742140500d241000c40d82c56648500500080d40068400c03180e04a400700805020f00381c04003681e00c9059251202a0090050623203021000b100903c0c03c0202d0380b422180c9060f442080000d8080780290703441715841403e103610058030b0301c0d85c012000040c6d14100355040c4a00303c42c1c0c005005400380441100a0951103d10010b030070402d420020a0300851450070107041c4483e0f1600d0340b0103c3d0f071380080070424104400c091201c5031000f10707204004180c407040c030714180e0440c1e007945403c1e500610200d005048415034408540304000d690541b1109408141507080c2d16100c04a01001c1d07808460800c20750440301c2c0060460300a0314416130601d640400d1125071180900d281e4583c0d1640202600d95854851168100c00b454a241007501030780d02100100c00390701c4512004d464424160010481c2e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 923822257 1250 923821007 923821033
    0x73204090201020d11070305070311090a0b1c031205160306050114032a0705010c0305060102031c020306030a02151305012a030c0f05060612030703080c070804030506010f03020a17 79
    0x50a42c12501b446800380c0040851414071404024522400b08400c0440c0050200000040081d0413058580d20308508007145a46085050342c03404075010300700280000d2400e051b12408002021214250708220410225044900d04c041004c41e281e10704004c407940301d000440c1c09042010818500e084200041350300088861482d04002c0e600000401d0311802c0000c05200541018004465580d190803452009903014080d04e9030005080c40114101025402c030080c0c0d140f661807203200352a80c000040746540d01c003801007003a00754010f04080314800700c0103000e149680c04031103407044003101d01c0b0002c82c0642c840d0030202d501c440b044054000d424441140001086039905e02141800100819400010340d0800404002030007803014006514084061003100c41300114040890b410400100002131b030025141600401c1200c1415102c0c130345440c00b44039078030030750300040c01c50702c690000040c40316407403c5107006036442511401c3c00b0703035a90342140101c0d03a1901060710b01500454031442e58 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 923823507 1250 923822257 923822267
    0x1050109090b060f160515040c050904023a0c0f141e180c0901030e0f032a01020c1e0c1c110a1403010b06091809073204090201020d 58
    0x1901e0145d11030401c0340311309650754601c5c05201e42080007030880e8450420052080d082d440d5001001c06442c603000754070701980003c8a65003c0802400040300380b0030306050a580d5111031407000d54441d404503190b801355080c04034880c0840d1245021100d0104004101107810030510309600e10068201c855402c621040014176608402c00036070000300400303001c000c982c1902603241c003d035002285203030b60b01c0c0317030380300040560716410010348065205019160903400c00004072440011301e00d015901c0c00311414003100754201600b030705c070311198008552001d81c5040450540400c05007903150103800c4a413440341c180c031100b500d507405503c41c0040c8520840340c449005a500f40b20310070342d402d1004500038000203110604a030400b98611030034000000841c1801d116600300302c0000c0701e01034101001280051001c550500402003d08000c2d030208101c0e0204010308409411101d0f16042c2c100359070030302040e4040a051910321810b1203000c850b4043e0619103c0d0401164041c0d0290030000880b02003030303035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 923824757 1250 923823507 923823517
    0x360302031207030e0f16091a06030702250f03150902030d0f03180b1305030d1a01080f0f150d051002030f0c0418050a02071a01050109090b060f 63
    0x254082009400700981d0030512292080d4419240040d210007030000d003600d48444100c001c0d502e07900415046084079100d00c1001c0c1180c0c4880c3c80442d00010341d03d40c07404090040400310b50081c5d0080240043d468000c1501042200e03004143c08003241c0035001010008164459540030845403981440400c80c1032096060035540d00138086119500f030f0b408a031400c0c20908406000a580d094000b0308154540070310f12140d413844402c15015070031303a111081c503d840905540c4090014055070010460240241e07000f007c540300b4204401c2c280d80588039090a01d904400b40002d401400140b14280d407102101d010341106031090040781c1c0e07802030003410020b4031509694000d42046055000840420a140c0360403a9a5070240c1c6038200b020107081080c10180148590740300910003840003004840080e101c4072180d54021034503440b441e4416000f0320814070090071210300d0710101d440048448408030b048942c01e9940c900419500c8140e2821501e03281000c691003c000c000b00307000116840c020304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 923826007 1250 923824757 923824763
    0x31704060f03180b130308070e0105190c020607050705240a0c050313080304090c020c090f100e04050303060f0301021e0708251205041d09010e07090f36 67
    0xb41580f50a0712000d08205040f6400611059421a000c007055845103609822250700e00385070030380400040000e040c0380111021910001060380f1001215441401ca80c444150040e140782e07954a80d506015403950301d18043c3d94080d0400512130480c020f8450038400b20180d40212103410b0640c2c4440840f2000000700c41611144000d000000100b010b0119820040201c3d80041d5911441c0c90040c1e010745800411480075900045407500c1c1e00d0b1500302c0307000e03449201200c00c0101907440544808100074a60458215100003c00304410001e00000860041d041100c0003102c43c5c441c04105401d0340b1a03424101c400c17800d02c010ba140346a0468000c0c020f045d118210b2281031012001845902d2241c0d003111042c404c042c9200302041c48480120041c9a070218034206140a0400958403070440d0403403401950908200002925900c0a5100c0800a00403100755801c9507036504d11440504401c000340c040280c81c2520070206c8090848802c442031854050a038513801c400c842d0702140010001043e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 923827257 1250 923826007 923826041
    0x91c031418220c0509210d050a0306030f0f0302060f040503090f010309081204170a1d0111010e1f060e010506031f0605030f0a0c0207180908070c031704060f03 70
    0x1200324000034060100003c1d07281d5611503c03043c0030000c00650280114040180016510052142d2a400700d40000845400d0a100380c1e203480c00c00080f8014480c07503101a011043c0b05142c001001604100300348114043c0c0e003150300035200d0b0001e131010741909640060840d80100280440d609041d901407004407014100000c603142283c0b1030782d4081d84541b288110b40d540181c10007003008000c40c45100c51a507001f0340701c0d007000d150440180c0000200e07980d406074411079891003003890384500e410f14200000d0304000d000c1d00310110b40065a0b07092044152404030f4001415244201c024403c03c0c00b01c0381c0701c0042149503482d00003403000303590002d800c00f404541c034054514108004528144000c0515542e1035030303207140c00c0e62541e180c0003002d40301444d25810b01a403589410340c00100002500c060b1f020400c02d244138009a400144082c100040030303850040307980300c00e1242030000743d001c50307009029402c00c5003550450b201c07152045000e440045a0402d40140485110381d010120020141c104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 923828507 1250 923827257 923827309
    0x10207091802120105042109031b180606020c010311040b090415030b04051b010e1302190504090e0c0d03140403080715141911091c031418 61
    0x4203000d01d00c00d41041d00300342c1d11394082c01b0801600302040b550b030450300c0e280c440185095001c005c1000510f0300c00644046c00300c0d60320450309c0e0b08c4107666030005c000303e0207141c52080904240c4006403040e817280740c015008400b100c903c1355020b4003070042c900b00c10307075000c40c0b40c00e05105c0b141c52541c200d0301c101500103941e840c0000c01c04a07541002c0002e140980f540c0001850301c0c0c604145081d003810312014500e9410350751204641d81008d0700751004041141d0800399000d4818450009001d15900079920f8051139003000c8419810600800640c1c00c807800074000c030074944031042c0d80d40380d08051300354200d0f02e4502c0c0c01d00800d00c02c25001304240754900b8504d182c540e480d11501500d80020a00b95484554442404c8040c3c05610418020307901e030b840041c001c0e1914800400c0174810354203910074030307686807203054850b50310304400c403101410000c01404685015010520082080310030032804070b404005c00d105020201c1042d1035044000300d02000c0c0d0310040c0d20034800541c480b141c004002980b0100c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 923829757 1250 923828507 923828509
    0x50112021303020a0303021b15030117010902031b0f03070303080601140f030a0b1215060118031a040c091104090f02120a05090d030204050f060a0c14010c0906020c010207091802 78
    0x100301d40198000e900800c0c100340000c00408038023a40b800c541d44100c041c00d035000b42002d07600c010782e03044a0707074440016146001c49048a02401318440000e505024025000c03000c0304101e007400340c4092040c0c81d1b00b00015806020b02d82c2e07400b0036002c06030203d40c601c0001100b56108035501c1c64151410f4030903038108000400052074a4000741c0e445400030ba2504660303c2c05080150804000d486180010301d41b00340400700540d0030b42c0b40134100d941003090449001c1c3d4800018031600c0011540039604080c03060340480184070822081d64100d41100c7e91600c0021043d60502600150742641480245010b2814010800a00c034054882290390340030311000e40c48c400706421940c402d10400a0114641c0f070000754250804075031103480000c1c140b044c48141704035110100f0110300000305071501039403400443c4041c0d41105940c440142071790141d01348004c0303401041d004900d0501d090740f030303060302c10384c60b01d4059071a042c980c45400e00590003924200040e5206403c4000940c064000c5004100d015030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 923831007 1250 923829757 923829769
    0x4091407120c0510090807030b01150203271801090209120a0b010501202b0315030b040813060203090f040501080c33090307080c01170621100501050a05011202130302 73
    0x41e002781c1d804c0c40303010010821000824001d1050b4000e501c0518644051521940004016803c40203269802c1000c03282041d03c650401040a00500000000c80e43e03580342e0300e20196214a21042c080c64642c800b14055040c0080d0352100d0540c000c001e06d00c0c0f40e08100044510710002c2890001e500c1601c40c07500c00d03600f0b0074001091014000d181c4214941c05042ca20b4121540100d9040d041520340300d82c1580541051038682c050341c0d1f00c00c1035192991614241314109000306110701400d00d00107040080d01d1900000140f01c0c1c1c1ea01501c14030403d9003d14108003c4800c240b05019084c3c02c5800222001e01d0300c803960194001c1080d1803043d109238040890102c1d42e20003402001d9031000083d0301030161404000380d40040014000a20481031900002019208084070300d458081b640000b00f0020f03030b03c4650b410318011440c6a80303c2c44065035144075954007074014008000e00e14000012406084c0b41001c0800d841d81078440501c05140541100000e60207d803280c0340c058402107003c0700598038a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 923832257 1250 923831007 923831009
    0x90602160210140a050912071509090c080402040905010609060b043f141005180a0201020d1d12030c060112020f1e04091407120c0510090807 62
    0x42036603844000051041c4684030100c4a418801e10030342c1500c850340c4410710411202015401c0c9000c0b901d4840c002d000c16081c0c4c00050303030b07510f550203640000720b10420818001071078200e50340e9a05100302d64888407001218441e8540200080d074160000f030241c14582c100d000340701e03c1a0700000301241c1d209440b0084402a13007190021071000141048034403d031242041d0b03416409203442c1106007149105003a84003140b075041c5406040d420011081c03040c0c0300b44110300034820805076504550091a0300c001488111003000c00c4216584611000c20400903604401540c10780041c0030f161081b40081e507000003010407821440403150115642622070000325001c0a50366001581c480404000c01810710405800851200320f100d2540b00260b0380d20070504201e410252140902803e500080c0701075491b01c5600b494006080250306010016000400351a503800c80003602e40e41a00c3d205610040c405090000d018000d08110500042c904003046c91850385250402604141d622480c42d41041c1e45 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 923833507 1250 923832257 923832277
    0xb060315012d030b040b0306150d0615030c0b0a020d1103070c0b0712110309060f09030f0a03030c0201090f120207050909030d0b0f06030a0b010905030f0106080c04060b0708090301090602 82
    0x85440e0b21054150540130340088600100c2d014440c0c0074100c000b0a0b070307445008191000e1f0520084c0c1002654450442c40141a60440401c2c8040f11610800f0b02120713a56100850b40703840c9081d1700094600c40481070714881a000e5019040760301941208480700b000d608802609070104100ca076001030a106190b1006100c0d100d10070b6100c603107904252550b016618082d41c24084c521402000b4090040202c0c1c402c1c3c02c0440710303640c55500c0b1001025640c001e504065805228103c8052800d41d00016a01d000c0e0340b19603410b20402c00118001c038260340300707400020300c0e001c01000701000103101001030000360340032841200d03407451741e500c00202d400c08145d44c090026040011411342c102801c0c092540b18000503981d0314101031548022644602c402020410380c81c1d82c940c148642688124050f400070080113046440c14011006111300804085c412520948100a054650f81c1028001d41c000c5901041205050078407540780d08007103a1141e40c1c4140c0c195a91203244c400280c02e403001c3c183c1ca60b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 923834757 1250 923833507 923833577
    0xf0f0406110d0f050105031204060302070c030212030c120901300203040b090705010504030201080408031024170c0405010c0303020d05040b0f1810180818090a0b06031501 75
    0x3d012076007011220180c200d980a034000700f40b4800201c030103a04139021110300740380042e039424172410714440a0801d40c01c002d520030f070350110100500b0000030260075031907002402c0d10f40e159038481c8642c0043c07091048803804220f082c81401c004a02d030020034240c8030742465500600321000418a0202d0b4003c480031554414008144403c0344420029000034040a003030103890582140c0010303010200c010401401d62000000140c907124055030400010104074040d4024011004501d203a040e0b0103002c0c201c001014007410042221510b60500d028807440c401040c40d15041c40f0045038501c02ca02e10070341c02d0503000c105020008441d80705d0785114500800008015041ca1075214400e590040e0510313000c10052110645c6111012929400c0205101d00004664107410b0244c0400100c1040180c98190041820303850360001038400504290b0454400d82c030341e40c50040b58012501e85210b4681c00107014000030300c543c4c00041c400b41010714141000b0a1000e100d480315807407503c601740d48030300f054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 923836007 1250 923834757 923834771
    0xf0a0801110705100b0d0f1e03021c1e0305180604152d020a0c081201030b0108060705041e0b0c0c01081513020f07080a11070e0f0f0406110d 62
    0x2409103d84c003010500c01100380003030240100060101c800b403010240c40410110300c80801c0012400b00c1c90076102d03000c0c0440075100350b681000b035114185080a540d81035043c81481c210b8502c607403a0f84003450b0711600da5054200d14154200c008110080047e410340000c060f0302121503504200c043c0c031a611030343d0302400280030380c159030081c0d070341d4000c45100106110007022090faa0003070f50001e543c2e10180e0016158245a03100b2120702d540508043d0020100240302c41491305000f0000c0d0503203001e00c8100c00c03d640d8a40c80d09903203103400c13251000002c0f0248000c1c04a4880c1e91490035401e022440012111030300ca0b44418a2075019100341d142650228103c4405542c01032100d0703078842051040721548003274020100d01c0042e411842201a02e43c001a02416402c440c400d480001381c001c207110391034001d000405030800000d0703144100c0c10b00c01d11070006504010403454612507140b01803030f0b020540320303400760040c0248044c100711401a00e40c85110241070221010308817800104801148074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 923837257 1250 923836007 923836013
    0x604140f400305071b0504061a2b06030602070c0b270406050901091b080702030409150b12071d010f0c02010c05120a030e1506062811010b0f0901050f0a08011107 71
    0x311050380c40054017030340d260080151039180a041d985100c0882244141c20a9419605541cac07010021445698502d002d130084140041139024111403486144607004403a00c0e144c451183d030280d43c0303c0003410071030040f00716610078042c42c8060000c8000340000c1055500c40c00003603c80d031001d81016407070b0ba44d2442d080034881482a0000c5080410b070615003260300700500700035100d00c181d0103100c0c081354441080740ca036642c440890034000c0c010b41d803a4070340b80c1d58030030b0700b014203031030242e0b01200001c821003160b031003603100e070144036158200586502c6040407007240203030303030803003410b401a81480484400000424014030003540302201509040d0754403400120b0186c111414108417010b40da115070054454551082c28094002c40101e41881e100d4213543c441d071500301110100f40041940740e8034040d00d030b42d4019040c2400549100000c1c40a007246a040c42481a070745420a940404c240c00104000d0800c0032722560303040400703000c0030b441a0f2141400c03801d681003805669098007001502d5414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 923838507 1250 923837257 923837261
    0x219230f0d2106050a060f140708070203160b0706090f0209090102041d06030703170d0c0203040612182910030507120c0e0604140f400305071b0504 65
    0x2c240c0380560200300413810800401d254440c1c5010724405d000d48103402c0c4800c03038000c0b0520044140080b04d403555580381d5181c020303010b070000f8008030f00074850f43c200394407076441c480c0d812802c1d100003a941034144900d076101c100281801a01c2618404924819a4090384a00208030300c1a01100000b5035a10b103015801c5956800105600c01b031215180180000f5030340109040007281e41102000050704982070700310301c2621680214a10b030b9841d001040c522141c01002910843d4800d449442d1aa2072094000098a240100300e0800d80040d0300300d48001070010190b480c00da003c0341c450035034002c0c94100c6100720380416075800441c0480174104000308041005240080c0c1043c0c903d02c654619241c0d50300340080000d000e44200c000c2d6080c0000c4550300c8590102c0900a09400341d840d0a041a40e500d0345040000e580c401500e00d0f0500a090000e1003401102000d03180042100c944040d0050000d0441502c841007242000020001c12012841038400c1007092004001110b008501e06810401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 923839757 1250 923838507 923838557
    0x91a010f08070302030a06052d01030b010b030c1e0f0705030702030f0d02074505010501030e0705040f02090402031008010507020a0f02221107030219230f0d 69
    0x80e954011941400103841c0810341d113001b158050b50100b220b071140254100001c7c1040404203d1110003105d040c07845603046406412030b070140b0560313106c0340d0302c40344851500e2004440482e14040b04102c248101c044814202c84c107045507246150800310041031001e442d42c00841c040e50154808240c08065241c00d02c1090205018840100314000c503608000c0e45811462060149030008550200d03030300c0d00d00d40391400c0b112004403858082d01c03260080da2482501200040300d4046d145c03400102d103d500074420420000140c400605183d1310b091b0400c4050644003180031a507603002e11220610307841f0360000d14090203641d0342e81d01c001e42c144403801d400c40e03400414850865100500490100f16088040b105898040c7c1e50380030080704aa014288070170448050f580754a01c2c0924100c00740d6002130180c9032080c465404d48484442c0031498100c000404000501031440816105481c0b900001c140e01e001c0a12405850f01009400110350810440684004c00f083c48542c4107880c0210710b603170440c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 923841007 1250 923839757 923839769
    0x130504020304020a030206030c07050d080a0e2a010c050d050726030105062b050714030c030a021c0c0801050f040c0c020906060c0f0309040e0303090a1104091a010f 72
    0x605625050700000c982c1c134810300c0b0280c010f41d00003001c2800100940126001260014119010703282002340c028808401201c6101c0740c2841d180b482d00e652070010400445020103080c0e0140f0414005036448017803c0c2400039117040c82400080c180000e81e0a01a22501154a0f2100d5845501909001920b0300d850114400040712601d40c8105500011007901e0640d10251601c85d00c0f24501034008411850341d1421000c0c0c0c1504072562120114a504114132604041d650723800d0a001020b0001d5082c08140c800c40c0b100d90040c000501c0900003a0301412101010051601b98a600005150215252a86d9480004400317100501c1f03a07040180c2512000c4d070007a0b50070004101111001071074503440210080c0f1a24030324000c80c01c65520710003642c400c0304003603007905d00c244051700c02c41d6503aa001e240824051400c048003136420090100a480c80307840081e000e0503144041e540c0c3d100c000c1c1c114819480d4050b0782c41d040c444c0400c4004d4151f403603a003007800070520740354108900800c0e4035225602403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 923842257 1250 923841007 923841011
    0x5060105060c0a0f1502031f0915030b07020a0212011a180403181701050a11030402030604031b06020307080601031b2001020409050c13050a0311010c150c05130504 72
    0x30410201002a5000d00d10f90400c80c6a0202c4c0c12a14202029580e01c1051078800340c0003000f4002481c01070b9841d19281c0d0a04028021030640c0d0740000c009440d101540e00c2100c402001041010038120048598804103a1041d00c0300c0000760390004403a0a18450800061b0b9904c155214407400c2441403038180d5002243c01c40d01d00c02c03000301c080302034284c020070003001c01426404034400e0300d09980340b11b0094080c1c500d00080c00d01d95180703500d0003400101c0386510741d0760401c084c1c2d04006103c5030440e0301481d00a0041d21840d526620251224070010703110882031154280703041d01050307891010754003404180d03498241500300a400101542c500c00800407240300c0c0103261342d254a810041c1d2440d206c181c800f01110790707510340b05040c1c0240656400422403500b81010068030703031550401000c0d030120103200001c250351240c041c000e1500040c0001407055034010764089180d030280c0a80394065100d0400785140b44c901f40b000809494541c1501c030080b84021880038400000080b0302005000e065800b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 923843507 1250 923842257 923842267
    0x4020607081c0c03140a02070b0103201816020f03031b0904050c130905070507030c022806030e1b010e010512071d03030a0e040f0605120102070506010506 68
    0x50051003100c0300200740c2000040d216000015008150401c2d00c4060020069100c0d90322000d000f6001300241c4450a814080001c2c03143c0c10a07109403040c16412126400f800e038259690403c9001400b000407a040010080031042607031128504064003000c10190380342e5090120700840c65a125484003015900048a15014040004192541b1106040211a41c02101980d04265124411005030010704100030400743d424004000c0120400ba660034404840e5603503248000c9600c26036042000030810030041020901c144d030302034805800240340d13400e1b2030907104510105a145030640650021407810820080390184111f0400c603a005010700003d220343c05a40004185688141e0b040c0170411103054656440f41c820b44a2824224000e08654103004001034038014030f0280f1030070709c6811380042c5c101500340401038400c1401b29032500d005100c4035504100140c954103014a42d082d64840c4000b80d40c4d5203424181c0000169032000603a107850710300300b450030110141c201900803001045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 923844757 1250 923843507 923843509
    0x30821070c050604060c0e33070506010306020306040e0a0b0a0c050c0a02100201110d020d183c0b1005191217071a090d140913090803070f080402 64
    0x920030754413540c04440094140c040d0381040d84d8111494140d2604088018041003051482d2000400030159180183d100807a10b400048058401d0f0324006115800510040001640580195810010051010498000c034241c000e241820b4410141d813440b21300018045001310702d204030315005001d49080d03494440f08104055465020510007070040040304c01c1c0e4448180300790f0005110000000f0305039507403d00401d4000c080d41041d01403130911841c0094020740e0b200c1c001c52a11170030f0703480001c5600003103d2004040e1403401e0080305c0e804003000102d240341c03030060405c00002c00354801d0200400d1828200351010010416030449402050001c090f1a01c9207000060001264846d03d46800010320030300d00b9000380300001c00120b071800004a0b40800300300d00c0011032803104108110601075503480701000c50356a89241c02d0305002c1502d0501260140f0003540080400c0440030340562003045ca0304900404036080c000098501c0040401403050342c1d03601595810400c88180740035030031402c00350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 923846007 1250 923844757 923844763
    0xb150a3207030e0f0d0506250e0d03350112020a0b030c0d1a040f141302010905100c020310270203010b0a0b1c0204121b030821070c05 59
    0x741c040d00340590503440740b01664680b074101c880c404000c0d009145458043c50300c035030790342426204060784c01080342c80e0075042440103900000c207010300c0c0e03184d54141101900b4084603004075941039080104007401c0340c0c0f2a240d03091107264032590f41c2248810710a8815413100d8440b1046e08141502300f604610303003000d84c1c0c5419421301640c4008240701e80d130303480303c8074488039038030581c3d9044403840d061141c13003107489001d440d5005801d8419030742444000160f40c000f8088440040c0f00c0d900c0c1884510101d01610a1000c40603191071043c1042c44900fa11100080e6a18480710300d14400105055034201c02c6003000c0c0581e841c9954041c41c02d00075018214008201440801030041504401c20514001d41d90250403040c0840c00242250100c02d0702c60302690040d510086006e10007820802d03c8110b072002501c21601103641e8084050b00070403003991102558250a400e83d90151400340d404008581c05d240100386240040346144542800f80d6442100c0b88801001103060040c4040303d40040380c004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 923847257 1250 923846007 923846017
    0xc03030306062a03250302060c0a03021e0309010606020304120f1a040609050706020a02030c040c09051c0302010605060f12060307081b0a051903060b150a32 69
    0x101c1c0c030141c0f02c507880c04103141d602021054108902c0700e06071000b01c10242c04401401008651400d03a400844c1e6240c400001135a10000100140e0105001444001058002e414440b8184c41d001d0b180c0710300a060070804528141c0041500d0a0001c280014082c00344600030003410b4500280d428980ba00103044035400c55280003030b050104421886040000d0111400075011110074000564205410001e000b000041d00031525481404070204065000043c20780030558001d0040c1048002d800601c80070701001c01d0040144000d04030041b50740d0ba101039000c60008815003101c05640316a0034004c0c02d40d0f440d9030140b80607010410041c0041c031020821203081c0740c03503003600881c1f03034403000d001c07924000d5660b001c01500d00815070650442100032400c8120124100ca0701614941c64030204048000f6900140010341c104000400020b8019082181901e40007000c0c401246442d107140809a4842c0c8840c0e80040c00d05e445d6040c0e410310030051000e40c02c46c6564088069942e61016554038450 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 923848507 1250 923847257 923847259
    0x32214030f1005091009030e010e030f07060c060608010908030f011a04170f010c05090a0b1809041e08030a150f14040b0a030b0603070b0306090708040317090714030c03030306 77
    0x200c4000420f280070800c040c540b0020304150401c0482e0690030003d1200723150204050020f02340d4000c42e911407a0004641091424010141048910f002019900f998202e10120341c0317282c0780c0100040c454000e114096050f4041d43c540e0fa50392815003203488041c1416040810780e14810f0220a010881d00000e45d81900c0da0144000a02c2c1c060598aa18104801c0c0b09801c05600705000120f16650100c044c211442c01610803190a0351a42c400c0300170740c0655075012114030001001700c4200c0c9040000c03d034000e4003d019094030244509990002101240c02c243d540d00c00002c180301c1c50640510414220b03043e0a0040406076080590030707400741140b0b10810800c4c0d0b01025001005a40341d5101c41d1252500900e102da030319503280b600c02c1115600702e409a2003030152010005520f80418201c92103500010301002c04c540c0c640c4404c0d2603000c009002036081202400395803c43c202c1c650501c600406003000200f0107140b030441c201c0c515940558401d03009800265264801d910004260f9070040c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 923849757 1250 923848507 923848511
    0xa0f05070302011e0e010606080c07030c080d0609140f0609070518040204090b0901081504021003091202012721021f06030b0a0501080618032214030f10 67
    0xc603030030101d0140010000303400c100343c201102803040d4003041e030211024040803002030217420350b540c41c19982c0d8001120281c0320407004201910009200b80f203080d1082d0300c14124142071115210040044071410b03007140519545d50094601c0d00c68403600e281e64480c0c3d542103507500c1c3d8a03014005c00c0c0600c001038459404d201c000b003480c581c803c0d98448107d05000001c3c06c11902c3d80c0c1e881034103002801400d003055015089010010442400220380480c0e54038003040b10b80c481382c41c1c50b4240030300d040c4030200c041d0415644502c3e0600081c040305d440003266980b9070003c40c4900c2e541c0040c0ac08201180c0b101c113920394602c4d018800052611280a1405045134112003818150860690400b840560813103d50000d04182080750b400070740c0b0a8081d640140d18820f015692508480111b072402e0007681c0c65076005c1400114914481b4010741009110b84040c0c0342486103001b2140316082030081002c0c5c80140d0042c00f4081c02e1031700b20f0203c040e100c0c114002d0444809403420540c44518030301228100704e0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 923851007 1250 923849757 923849767
    0x210050408090415031203020c2e020301090504060b0f0f120a02091e06030304030f0605310209130c0509100807170609070f06030903110304030f02010809030a0f05 72
    0x14194196041c0350381c0503100b4040c0c1c0003a8400184e129400c3d00049603c152a102e00c200b05078402d00c261424681c5500081c000100b5034010708101c0c0f482c122003100d600c5c0d504c02400c910804940099802060044400300306820075262a005079080012880d00540c00040e1461706c2d0b80d2903400600b0701c4c00c0c09681e24100351001c5807050b4213000703544c0c50181d04820a0424081380c00c1d0003c513041d50354141510803e0080d2500d00c00c0541324030942c1b0014103586208801d40b80840c080350302c000d03040400e543c0321000f200d001c02d4108040c0607403108034aa6895103401c400c4207508102500031741c00315005044000d181c03141c0d40c03000c421600b00d004035805081e1420001e01e01c0310440b0f10f000068250141120078050b0303250040d00d0300e000301c0e420880690103043c0114104c01000030300b15081c3c60700c1520b04922182046402c45c000c03c0210700c00e034104908040f10b180012000d000900c00b030b60150241c1d2407042c0c2d50380000b600d0340802401c0c00c0382c2c941c41040024a6a984600d8250100b02d00b4030b005555a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 923852257 1250 923851007 923851013
    0x1021b03060c07020301110f2a030409110d06060905010e0306062803050a0c091a0a09020309070302041e050c122206140603120c1f061e180c02100504 66
    0x4041c004101d02041d41c7c00503501c240241e02c0b002500a2400c00c00041b079014080c8019800514060181c0c0700443c1c0c411311092100302d50940220b4650526000d12034200071090f002c4e8015684aa88514085680e60b001440196030114288001010076001071001d0f081960100d2a00d0300105525903100a0340c00b00342940c90308000d00c600046802004a9119280c0c03410144002c000324418641410300d0703e148100088441c05507062164001850200400d1510700f2000283d4002002400a4022031002000503a600e00c9072803940002407504403041450200c8400032200040c0050064850500c40e2640c006c41d03150880d82d105c500701403110794104101400b4180c4d05183e40d030007013001e420a0441409034507541d28541c49820128111410705020340c00f405042c1c410b240e080c40303040c3c204044d115100c00c54000c88070380c50074070b2410018803240d0390158500e000400c00f5800581c42e044e18002c000c40c0080180203088011102c0302003100d50000c82c0302a50751800200403c000903140c90014083c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 923853507 1250 923852257 923852261
    0x1290301061e09140603061801181b090510031b050a170622030e19080f010509010213030f03110d0909050f07171801060f030201021b03060c07020301 66
    0x600a0060812a008215250961041d80c6001c0c041c0f80c50726019030122029034a450507070040c580030b0701130700e920703181c0108051840c04003510003c402d64880410040c4204484000b6204a0081c0295100f180c001202400082480e50014442508240070720110103c0070702074000304d95100500010f041e601c424030b40440300c0260301c0a40e10015454001600a090011600640c1c0704035040e11190707030740c030084003407600b80600c80b0104401d0441e401000082c05022031103403604008012006084403c0c44d1510084116000b009050300b10000c99010508240519504010ba00e0000d5007850b220001d0310004e0a400d20001e054010a07901050038503004d14101e040280070350b01500e014041042c006803000009100c1c080c0c0880c03030100000c3d104484419164000c0590b541c5001c030341400f8111140742c00303401500311741da0f0341d01e400001c03e00315000744240c038000c00ca00a401e001e4a4503500019042808050700c1d25400d528405444156a801041c81796010241f812003c0d11001c2900200e40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 923854757 1250 923853507 923853509
    0x17010e01151202030c040303030c02010c09120501060801050c09010f14072406140f0406120602071a16170906070807050d090602091504081207031715120129030106 72
    0x20480c40002031101c200d803241700410070b60b4000d8409004031080848101c0c200c41c1c00109200000e94540414080b10710400c4034100030600a00020803840d0320703008000c2c21140f003500d8030030381c00c1030002e0310005958002030103103010484c2d802e11510216403080c02c41290321840c44001c0c0000d05650342c1e46855445044102d03043d03c0068800c2000c2501c40c9004429039210061030342c481d2003604030140003490300f0300030902a1940d040d80b0000c640342d260f036060b02070b42022008880741c01e1801600d600041c2000c56a85c411076401d0101840e112000381c2c0988401d01a10180030361003c00010041410301c006039140d007040b580e282c804440d035110348045641d0f0041c3d9030005512820807c0040500a8076009030501b00f8045915114440711000c0e001118822840340c1501c54014441c0020101500c05c080d001581c0a81071107089070007162680d00d5140011140c91410480402200102c0d04100c4200c0c1200c54034030000b00700390b1a0034510460249405042140101c021802c0e0540c0342d1400c0d00a44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 923856007 1250 923854757 923854787
    0x1113050126131a01290d05151509040c030c0e010e0a09021308070807060f051c05040303200c19020301021306080a0f0c0512060f0a1517010e0115 64
    0x1903540f01c0c80d40c00c400501e50a125441c000903041a0504076040b0403c01001220000d00c09140b42200c008800c5002d080c0c014264491030400c143e080e1015141c0c2c08044000144540806551f2001d4a007000101e505c00726000c0f00305845d0401c0010290341000c196903800200b420000658001c0400040701541c00d500404006030000c2a404e818010040c001015607039000c05450100f0344510140d50b90759217034071404001960703441e06052003a01030301c014846840300c4140c030140364000700950000d9840c180c404070f0010303075140c4a400108502d040701d0310302c04243c1000700345000d00d084661a900c1c800c2101040010142c102c841f411580c7c2541250816505601615801ea98843c4080e08462085901d0800142040300e4001a6080352044209084690300c9090034807013004400068440e00921140d0803031035981100031541d880c01c2c20380d001040503480e0070301111011070300204810b6060074611149071f10000180700c1c0c0040d00601d98155260400034800c40b042d00402143c140710018515 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 923857257 1250 923856007 923856023
    0x6021506042c014b0207020307181406102105072f120306030f07090203180f0c09060102030d09110a0815070e040b04111305012613 58
    0x500000507064200280d16441000b004122922860b0741c40860206007030030048014403c403c004402c0c00e40c4604c2011083e01e001d0060a00c60301d0350209141c404e89403c00c0366604401d40903481d0744d0741c5902540c0c4807580d0f41c4035804c60506060002c10b44288480400206008601c00e0122a62500440451a560405000340a03c0c20f0030314000e0034204080700700b00880321000300e00c4003e4445100184008000b064000d00305015412803084a81e040603001690500942c1c2d203c0d108050100445800f6080c1c03000c00695a00300115140943c2c02e409029840d242c2080e254010314200114907480e103054140c4003900e043e82c4940040342103108465a400000349004114001d11112000b2a6001c00c0251ba54008540c0c407943c0003507494040210194500205200156007140b149090298184010300702081c514080400903050f01c0400030002c054400106d10200c1c240d0414403a14000cbc1000e00741664058824030880c2000314814005c00c01c48013055002c1454034407071002c0c021120b6044141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 923858507 1250 923857257 923857331
    0x328060f0b0301060816030f0c0302040c090810060b0d0f02040e0103030e090609270f070b07020f0a0b03010b07080f0a030203040b010f050f011d03010e0a05070602150604 75
    0x140c04010319420000e00c1c02513190a41c0411a8140042c131040b110051080d10f0404618665811169500891044079481c011080000068a0f14064120100351580310101e5980c10540814644100711400c2c100700707820107600700006e039005012034400c8485441c021506071403101103440640b1450b4003d100300220070000200b8154001000030700384200b1503400016442c2c032020801c0701c40081c3c03000f050251034115510407040c0c100c040e000341c031000d9600761441c8440c0803030841c3c1001c1c040c2e8081c3c10b04080004041c421480c000301104030500d03003100c9000e40039041c00d41c03402040c0414081c80751741e0180011408140074040b801d680d001c40c0d90101007551200e1003a00140a034000769822074107010304c000045441e0b4102c00c40002506ca02074075691030600050300445000c0500d078120300340924401048861a10f007800b889590101d02c100504000c8224a02a4a0700c269684420b086400c070601c4401d500c000d0888083d00568100c60126804007400304040c108074005081c1184983c1c124a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 923859757 1250 923858507 923858531
    0x216050a181b1214150f0d0606140111061e040f0b0103080405090603070b18060c0105010b0703230703030b130501060801090606081b1e040b03180c032806 68
    0x80c40050b0318510f40c4148402c04010300354210071601512003500c0c18640c1d0707010354000e041c607070014000440c0003031031341080080988404080b1041c1e90480407080e190904015541c0d40c02c28012000390042d000103262514207101582d00101404001c07824400d103c4001c28144000c64069a5040d6080b1205100702d580d07d00e0240032a034418481d0314010011000002d14a140109052089801c000c415620305594900490304403403254000a078000001d002440d0741c84d00921955020b04000a01c0e43d44e07901c1c2030304000e441da0070704400350380192090043c2d00650780c103044150760030070340c0c942804104101c03000c0000356035007410101e034440d1600e480c1c00004c0651b440801c090417114140070803c00700d034941034201c0d070540c8200c1300009920001b41c0406107403194480241540b00b122520609008003000a080d240e41c85540503a0201e03901009018414070220b94121101e02d600000308818404c220209445040108242e88224880b0703070b800c9040b40614201481765580410700300400c1d01400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 923861007 1250 923859757 923859767
    0xa02011a0d1101030b0418050a11030f071404141009110909011211030303070e010314130303050a06051203190e09040803040302100c020c010216050a181b 68
    0x611a4180018024400c02414140d2081e00000d0704489482a440d03000b20054000d05103003070025812030f40e103811140741c5007588000f0a103403c3c400d00c05005081d200e81004642d000a0300c20051081c0c010600f401c1407040c001400c00708484110b03413205080c0142500080041c001c01800203487d0310408200080300001c00c184400b92000c0c0b1200304400c1c00e80030309001340b13802186022030300040090010700c920400c506d40251540c0c49820324003c00c021a030042401c6400a5031544d02180000c1200c9240e0368060103001c074040001c10030314000c1e10700300050000041000c2030150505640b02c012400c4070015402c08009800c01a0104504501ca1282180da940c0420521507220002c1d041d1201014461180c442011130014864a0303a034580d91546045580041d00031408d501c80d903011140040a940655060005140c0281103031100642c0013a041036028949a00b40105014003440143c0e6030300310f20810740e03410741240025000051400c500400d034154448041c00111039804a41552003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 923862257 1250 923861007 923861021
    0x2180f04170918090d0801060f1209060603080d06080604030c020d03110d020c041b02061f080a1430070201022b110c0d020609030109060608061008030304051b01140a0201 75
    0x100d494005c0c13600d4007260405c00a000c0d81d0002003800d200b4402941c49008070921243c4030b0000082c1192091765010308440050780308580d10300d0085098107040042d4411400104041000b900541c0707000c3c2e03801000140da5400007845082d44410300b0061500c15540c42d03040b21081800c94200085244020350346528000740c0030310443c1000212000070000503000c1e4400300c4260010700c00c0da242c2e401600c01c2d20342c1c80a580a80d4412040340014603800070000307a078003140910407003c0070740c410314130403030500f000c3c0040050083c4a0344060b01c00380c0c0c034850081c0c510f004400d0174070362a40560f2004030f0031701c24009600b80c60322403c8040031445070345481804040403038540b905804404001c8041d91110f240352a80c59100380700c5030410b005810488020240001d000300001810b10075942d17528115403090308881840c0c1d100404001e60f085e994214003003c0c0118900031411450036076106507440f4130342107401012201103c114590799010b41c0900045410f030380d800a80b01d41a114000f4001c104c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 923863507 1250 923862257 923862271
    0x50706090219230d03140c030d020301050f120604081b0a320705150906072301111b030403080d0c020601050d02030d0e06091203030402180f04170918 66
    0x4044203011483d0b1002034414a12801803e819400000d40d1400d5445034620030030031480703210420241c0c000e17079010b000800c4400d110500041c3c0700d5040800740003401c499240514055480340b07101209000000801e10b41c030a60107000280c3d1003120b0480307901c0c4500c00c40c0c202841842500084801c00103500440081d032102c0f008000e19142d04048a4a81f048000c0d1144030282c00500081c0181d060180b00d02c42c4250084409903d80760305640825080d42c49000d050b2810407a12001ca01104001d080155035002c0c084002e0000306200d199040440c883c80b03c0003090705083c00c0b2401b00c45201881034030000c0d42c0005005071584003100110001c5c01d045041480103000b4140085814604a070810706810303005802005000c1918105590165400000d260f2005090005007026550356080c7d02c03c105a200c05543c490415106103c0050180e50200140f4070304c000400c01c50714035102c1e059034401d4000c1e034041c3c0303240b0340d4907400003042c818014a40d8010340d8160401140903d54585c607400703112 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 923864757 1250 923863507 923863529
    0xb0f03031c0b0303070201080f0a06030b09030c0105010807050f04020c0c091008010c0201020307140711130e06180d05130f0b0703112d07051324060906050706090219 73
    0x244034003c0503101e22036090000d0100e8801c0c804174075050744140000e030b40400316042c002429500c0c1d072601890010b0456145640e13500005000b0010b01c800e001c0c8034010100c28000740201401e00c000030712014900507080380030701c0e40030030360341072011080005d0030b500d0384081c00003c140d06114005281060071406290f885600f0400000102d610500c2228070464165a44c00c402d80140b0000715030943c0b0003807064568a1342084101d03500d40e24880201210841c4420000d0060528070b8000e0178004000c00880c2c202168144c044102c0c0d030082568185074205103806541d13003802c01080d0401045035040103807030201003580401c2d684042c4d40101240f0307009071513106070404c0c40d140705a521684d080e60b503001c03e54000d410240580307414940d072100b01207080039101440d80b148041440c0000e5808802e40050b143e8103094421154001d01080d880c0214101050060030000003510050701c1d481503008000000410000740f0038650f0011300707460b40c000d02200702c6907401d03402c41211000500840d003900b6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 923866007 1250 923864757 923864771
    0xf0f030702250501020307110d0209011e09050402030304030b22050a140303040213020d0908030c0703110706022515020d0e0402040e0f090c03160e0f0c0d0b0f03031c 73
    0x1031242d69082c0450303005034015854004240d50b282c41202c648551140c00c054030350801e00059943c1d100c803901a00c42610160080440249505030100d410791000341d00074944024440540c40110440e02540e41140580d50a03031641041c113503110300d41c00050403509101c0601e03501048404180100d00b10302966148001c2f488400b01c0540301e11040d140294401e200321031007000615107401170918011b2400002a9034a040c2d00c0360ac3c015403080301c00c09090440000e0300310030141c1149001c480c0008070001400342500303004020b56500d040c400d03400d203401700355070800c070351151a14130039405003a04084421030b095025201035519003a040a900101e00d5820100003241031620a0790704444032040041050381b40d201240680031000352040006000307030107500e0070365141040346501541e80c003811341402600e40017004052a10141c44521501c41c80b10600400000300740940d00710003000ca10000e014044400004d000024003840b480e018000408c00580b0391080051002141c443c082c01031003a2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 923867257 1250 923866007 923866063
    0xb0402030601150e040e160603090c0b031b090d30030e0c09150a08070608090109030522050901081f0615080a0207050337020d050f0f030702 62
    0x1004505411000190a404ca400c0c200d01d403507003005481203990000e648034802c00a18104800a09070802c0d80425103586035041040302e2000c0b403800918850709003d046040c604001d03411810a00582804a480452007032940c0e92032441150210781d11825071013420b580005400782c0001e889071040e02e400c418041c0d5550007800390280c074082055401c040d1a89041090821035022006070003101e080b044119009010b485042c0c4207005016110010031082c2e1a1042c010402c290003045200b40340d060414140000e0381000585952030045a00443d500f090204e25050090a40d070120303078003550303403000020001d6001ca02e1052422800308404803202d409001607007a22060702c1808c0400c000c4605c0310318558852038040d074000c01d0644000d03140084985480d881e40e000049260403ca0182d10120310302d8403021024184004c4021400c40c800411440c065140d640360f514000078028005850240d4600280071200c0c08511907100c03a44a040250000703580b0002c013102c581390280118600b9082c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 923868507 1250 923867257 923867279
    0x80d090b1501080f160e060406030219050f030a09050a05060406021e0324012003090109050f0a15021f050108060112120f030b0402070b071803030210270b0402030601 73
    0x841e51800d031061920361a845c01c81078624281000450811000010112040d0b41d480018401070101d55001b684074030081c900810000200c2c0c442d0700030300404210b69912882d1102c213480c0d005941c5500040c1013403190a0487c1003a03002000208280075220800080141a6001d8441426035000007880e901901e981001c03544810740ea2094041107100c1c0040080030380002d0904a40818503110402d0121032846002401080c4000d07440707a04040381c0035a0710350740028548014002142c02c00504c4030b172240450500120390041d03107880c100c00030820050034006c11052402c4885080380d120003401c006c4204c402410b0038040c2521a004100001030001804002c242b032a58103d1030101c0c4143c00350000340c2d287c111081c040d505140c0c417038000c07203150750b21752003d0f005260080d8058041d0380340144004119000e0b8101c0318011042041091022aa0000f40ca49884110560025060352034100c1034203110360580110005080300703400041000b11014156000300e20980454040740d8031031854203d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 923869757 1250 923868507 923868511
    0x50f150102031215101706060306101818020306090106030c1b0512040e070201050601140f130803040303260618070c0606120510051b0304080d090b150108 68
    0x40168010700007030066500c3c070707080c20fa0041840030490141030300000100c2c1e41c0ba000c1c101c502e404100d40c880b01e42d40d5018110500b40c0d11180882d200c5140d840d00c00d0000d24801c104101c200c00b00300204a61894000308840020090020410100081c0005180603400380d401100d8042c0100500e0000280403402406000600d558542360210a036002c1ca4080e0200c24031031030700b51220710030032001800042c0c0d240020000780c14032036a5800300389441c07500a82501c0000d080181048510807a512803401210240e440703003080014074542d503510b06080098510801c1d0805111400002800001c054002c1e00320014044107d600c44480c0541700310340d201c050b0007114115007010420841d080d400302000e00041d8131202c02d0801400018058a401c822120b4940040c80340001412000041c0304081085000043c41443c082c030143c606a161a801d0700d201d100ca07010881c2d004000f09042082c81000c0d190703140001c0d402003003071501600780032241d2282a0790115000e002070f01001c2c03107075104134003480c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 923871007 1250 923869757 923869759
    0xa060c141b01030b0306131b050409061b0c031d060c0f03040503070b090901090903051303050606031009080405060f0d0c0c0213090507050105220803040603050c12220503030406050f15 81
    0x1a0081c40e454039022380e61221000fa14100d40c40032040810a960380e413180605040c064080080c081c4110940384050189165902090000581010000903801140304200318030b86041104100c131040041011030061001c000100c4c0070300c0074400041c3c140003000d0f00444100724101c0e41075540e112945502441203041164016800c0b10051001e102260080881c492191502915180b01c0c1d942d90440403400741c0049440d17400c900188030b20b915082081c1c42c0c0802000310100060b0005540e054807602ca00e114460140f0307408100b03000071121400c260380b604100b0490a0003030103242d18000f02180c049003801c138840e18042c40d0701c0c2c2603540244034801d6116403000c0203140315802e0000542d2150001c00d03400c0096100c24848000c603040702c4000000a00b600e100071911075007001030140c1503e10060a07206843d0007402040680e44c581268035800400450420398040741c19249000710031980c49019086110000a00040107242d42c0598411b40007078240351583d49500900342c00210112a2903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 923872257 1250 923871007 923871031
    0xc050c0c0105031302060c07060e0f030616170108250302011b15092904021005030403140301150207060e10030b030c0d05060a05090c0a060c141b01030b0306 69
    0x10300303650045000710f410822410050034001e406500061707080d4082040c10b0316540020740200002900403416185c07a0700c1c12a4081648001c900110351380d841d00409103804c01003032690300d1010310301500401d40c3d040480c010001040d81c5038090251b690340b0b200d2a4080c4e1000042e0f200c01519898035074481581d50503981d04403443c0c5200409100080000401e42c0d007026000920922607005119a18010b032044d00038a1501043c0309200c664002d08000c00900042c40b04100703c0165100b5001c0e4945101e10300740203803280c8407030804460314945107820180000e8008001301e2034214201c50214200030310b600310785056480344001ca80c030b0f48500c801c1302d0300440c0d4a80d4440e01c0310300076080828030050290840721140480d038000f03405188143c07416507260b04540140f08040c1094007603a503011014000418100c145800400c104a01501c1550b0030004007800100030004015010114400c06004a90001c2540d000c4180c000080e070b00010302213443c4c4100c001c154140814544d10070890a204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 923873507 1250 923872257 923872273
    0x9210507030e0d02062a100e1e030a050a03020f0d0902030d1103040b0c0307021017100333050f331903241107020907110705060408100c050c 62
    0x3c2e201304061100c242d520a06c034000191040c040c20480040040d000300f801003190f0038600074031750803d1802500e41020401951a861a414001089501c2e64400345882540e42112840c120024001c04007584e4210034000ba41032031540e140d412014000c0d00803016503009500b120819107642214101000c500c0d042030104000c940d61403005042002d0b00c1405a82c42d180c041c1d4009038040c05990030000c041080416088080c0b8062950f207903007c103001a040340340360b0640d1103440710200721448200c083ca40c01804100190481d081402e803d0000e08001d0065050010344490701d0302084680701e45031542c2240100140e108103841240b0185044544c1050780c01180074410310348090600183c100b020810000006880c0c2c0c1c40f16401750500c0328900f11032800d90301e1140199461000c0486880705c0074044480543d0f10303480036607041207503400c1c407071907003d040f0003170a08118490348107aa206801050000e800d54000c00c00407104804010204003002180034195214015041d03408039036070090903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 923874757 1250 923873507 923873527
    0x9060f08061c05160e060a1d0402040f0903030b0f0303040f030b060111060c0306190605030a09051c020c030601050109060f1413030f060b01020105010b070609210507030e0d0206 78
    0x111092a442070b140c11041001003948880d49446034601000c100710500600c20045a081c4013401908a42c04139400260a1325111149070380700c8120b41121503c204000c007007030465a0f1a84404d121240c2e4110600c65030b0814240039005002c580d0110f4000e8072038481c40001441e0200850301952540c4034004011419511012005c10700140b41c01d05000280c908130b01c03054000c0180d0392140f046141640da4901d4140305001101e07802c1020404002d4000c10103000711038102082c3c075480600ea0b80c0004e440d04040c100385282550000300824010404010784040320360200d0f0840d10038509404a030b8880e6640e40044680715620310481c4001741e00c040074890392034811681521340c44002400b950070048910420f402000c06540200c40b031886840070320040104d40d0080c2000048240000c0080350714100c251507051107039080041400d40d8a44400041200304483c0c03003407a007510071060890b503618180240260f44410301c140e012541c00c0c0f10810703961400c0e54090b40c0361540904900d0400d02401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 923876007 1250 923874757 923874769
    0x31e020304050109050102030421020703031205070210020c070614090d12050403170703260109090206040e0c070c140f121c020d090503010e0a0b1b04120309060f0806 73
    0x41d0007182e1954035084650042071090002d58000d03400f41140301c0c41728924035079060410781120307941015500021410404079400c1060303000d6005e5180000701c0ea654506070200e04145e480c1110402d502d00c042151910110001001c4090316001e40701d40c142d40b0f12024291446010340f00c0460b0740300700912607002c00500c451072400d004280c0c03170800030b0525032295100c0c1c41100280c2c0c51031a018001103030b00810f07d540304c1079903d8440c0c1c00c3c0d1700c602c1801c1d00d891401c0c01079a405009d811000c90b16801420b0031525060210b600515840c004840341703060041c004c810f0380c0e0113440c059030080c0c4d05000115903002244c1500408080003032121103070269140501c10100010101c041c0c0c5400b44050340f14080d0080032940d0050a05603010340314609040034081e0030300801d074002d0781c082c0e0f24044443c1c80425000419010854000a002d0010b40c0e508030045108038010070500e1400c20081000241800c81032403c041c41031080e228180f00548644040740c01402e65180c0700001045d00e00441c2e4903040074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 923877257 1250 923876007 923876011
    0x201030b0a1505120a0213032405010e0103021207180b06041205012a021f0612031205071b0b0612010207031d01080601050322021002010902010906031e0203 69
    0xa0120380d0341c65940c1d102400c1404400b100c1002103a40041c8006007041c07810341e5560b12440d00c013004c41c103001100101d5000e070310450100801884020b019003407080e849448080014480c032106003c15a140d2000742481402840101e001d0180580700c1d403c1c00c40e0114000c42994800c6030580340850703c4c2242c3e1406020184556904248104008034140c0903070100d006285004c0e5002290742d40d01c0003c2807610078041d0094101c1c0103201070300c03501c401e0303404100c5042c81400b0702c0c1c0141680b025644240c005244aa20a03044140b940144404140d00074006134030848070160304114030790300c0c070101b5640c24400c1e41c5d10303505041c2c0303e05140c8002201004071940054028100d070300790561074401242264082c00707040c3e0209111404045840d2142021160b6040003842c1c149114145480040c0c85030002038540c0d040e5030000704c48c401000c03026114059045400426000d4100c400f0100a4003d02c0c001500b6800140c1c85031021402c18000d0040702c01021039134111400680341c0e01c240c1c00080d000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 923878507 1250 923877257 923877259
    0xd09050703301202040e010801150b0306180402030705030604030f0f030c4a030f0703022d0a0f03060e06060604150318050312070212040e07020a20190e040201030b 72
    0x802d005c04100c0351401e51019018050003000024030640c40340550410321040c2d480032031019420400c103d000d07101c14603a00d2464501c10311a0030b241c3c4540c80080d0402d003c64001c980c140c0b143c8000c020500d5070141da03001d20b01c60a034031511a4003c40303420880944130484040070114443c2e039442c4c41260341f107941ca403211600d44403282800e541c280c00742e28805003132030034101001d00f80c0c541514194030f402e102e0030411044070401003002e9855980814405500c0d1010802c102c41c020f600328078041905100075080c1c80c0300910b01c14029840b00400e00c0b003400a0700090b40d01c0da144c500b040300c11004c005881742c0030314801480c1030b0800d85003c0020354a0611504c40d001015101d100009080400c4414041c219204402454480890b04819910040003c1120341151b128405c020100d04200302124241c803007585180e1055665094164a0559124002000000401c0001400c4040900ea44e141c900c1c003101c03401c68240d6110068148140180101181c0105d41c0c4041001507009078005001694 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 923879757 1250 923878507 923878511
    0x50c0d02010c15020a0906050702130509150f0a0c02010e120a050f040810180807260a021b0d2a030f08030f0a0e0c13020d090507033012 60
    0xc00c99642c1164029a61403002c0050340105107a400f0541004810001d001f551078150304210b580c2e0002034502180807001041682c0e25170100d60140000d00915480600c281613501c00c500300301c2b40710340440f0402c4031070b02051445d150400390b8a501c1800317031200c4d0080b400f00800c50342d410912190701c00d07403180030100148072080142845507040784019000170f01c1264090001300c00010380742001d5801c1562031021080140b45ca01000540100c10b44482640181800b00c084002c1c2c0101c0382451a4484c041c2200040416100760742580000e0705440c650482841c05292000a0240940e2500d404030003030075544240c4440c58040194840b621300a1410b15240b9151981c0f910303141280440ca81041c0c442c41e1000040002000d80e4001054000e1541041001131405500f410394540907001c500c1c0c0e100f0001c1070f0950440d50026016a031103085447c3c820004c4440c140f510680c2d4440c1031004580c4072010340e065400000400b401d0242d0349a44005190140044481c110348182c00441c180705030395 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 923881007 1250 923879757 923879777
    0x3050d11071203020601031a0106020307030e180a1b03020405060a030b04060e07080702070602160e100506041e0e07050a08090f01020708090306132a0b0703051b01050103050c0d0201 80
    0x80c4000b00d10b00494000c0e00079049035419070422180c40d401440030390314001042c000402000383e0000403180510f816150256a0070a1100018407005071800014040120a8184210408541e1050b03101740c40601e2002c10801b0000010340a900aa1061590100040c080340f44042d009030006500000c1c020710015040d40c031428841402d8106031250f10002d0201000c0107800ca0f010030864002d444103000400041d4100c50002c895150603008202d102a00d100110300c10200c41c0c070310a4040e003002004107488a48410041180c8115001d4208647d580001c0000e08820b04d10200e5006d0320b4540d44041c030301082084280c8552030b0107400c4189070711580300c00247c0340d207082c4094009207101e01c2c10a99180c004008041c40d254003d405403c1e203500403a08800090014214000c058001d20000f60300682d1034441c0400150083d8840c1c0d0300100300003824002c140e40600102625000804040703080040686c0c1c031800c886090100a0040d03000d49130140c814079000b031000001d188145010308542c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 923882257 1250 923881007 923881019
    0x50a090f020f030a02090a06020708030a120b03060a0b100507080301120201110d0302040e06030f0d03110906040b0301031b0305060c0d090203010e06101a09060f07020a120b0c0403050d1107 83
    0x43d900480f000c03000c440e80410501c0207403500d03070381c10402170509100502100c3d00384003420761a0f100341d030708540034050b1074000204080025080040380e420010700b640d100340340005448002d01000005c07184078038001c4210418080c001c41c1030b00c562030307005030304a0700b5030f800d1412003001464818002e80c14402c1c1e241032030f12510800c002943ca40362443e90056292490210300b04c0000001528031880380e0010621040c01e03120000750744913808158134010038403c03a1075641161038400c8003070b0f0301d800000010740424894650701c011412070344101c07076810780c0f00d240307022000d01002d903400020116040314000c9003064144901400c1d4000c115000001c0b90300350340d4006407c50300042c04241c1c054001104101c040c03002d4407800d40040000905040203541e150710b80700f009100303e40d006441400045900c0407a61621002e4560340e680c0904440400c80c0c0b034040312044100c0320042140e502d130b65040081ca20340610380c141d030201c030b034044020003c10741c0215041c0c500c030000c400c0503c6188900d00e00010340d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 923883507 1250 923882257 923882287
    0x60e160c080a05090a09020a0203030f04020a05030a0308090f010504021c08120f0a0c11032b11130b040e04020402070201180f03030318020f01110a050d030b040f06050a090f02 77
    0x91080b0340c0350290344005040030f00c1040d4259a0241200d103105200710090070f034001c82141d03400310403901c00810079031f214400141003003140d800582c4c16100790000700c4101500300c0001c60283c0f040008a500700d00c1c0d001d0703400d4280c2e00e0444000390050f060b0300140e248200f000d44480d10311440b40d519141400041821154003c000326400800c0d03006d00010320800040c46d10400700c00210305c0c60480007a0482000d02c540e0b910800b020b803015160030f2095100c122080482900004029035001d1191950115248480b5003046100d08604412510001010704480085a0890b1510405c06000766915001c01c402034101c03500a03814000b81d00d400341c40b900340004691016004001608607043d0641c14000c00300c5103000484a031140d1440c13024009a90341d041d864680c24001d103409407403030814040300f03818900b00310401096403041d03540c014516505504442d002c4030081c0e90420918000203070400139614988640340d00120701c40400c1c0403c0708180c0004080011280780586031002d0702c00000380c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 923884757 1250 923883507 923883517
    0xf030c0f0a0c0201120501060816020c030f0607080c040302010f080606281808030316350a1529041e1a0301180e0a1209060201060e160c08 61
    0x2001402540b40c0c1c1c0c08540e0010510b02814078019400c04c2998105070000e000003401a208860122180c1c00918480d0310030030166444900107000c0d1030740c0001e0111585d544000c01d40f805030208100301c001901d803510060903501100d030141c0d10541e00070124a02a1103415011381150b0704807034100010048411f05452000101080d16035000c801303910090014070750806034580807100c010a903803c00c060580041503a4001c036108805204960000c0400d40d91401520b03e0303220b0750000015a1000f01000c501b40400c0d1415034110748038a651070401c5c000898002038241940580043c50501c07145000001ca401105003800100e030f509038140320520450f4000354800030317190010307000106d002c0294240502c001c101c3d1000540e035000c0c0e0407034900b0340e50005000303140700c0182e81001400012016040420f00c200c144050783c0a10b0064140100c6c0a094112032038003207000b0b00c3c000288940305200e10b2088803c001d484071060340310074801000b06442103420408204940c0e0000700420540c2000385 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 923886007 1250 923884757 923884777
    0xb151002070e01080304030f0204050901140a1b0e06030a090c0506040e09010b1906140405040204060305072a0246060503010303090b0c0a050106091d060c0f030c0f 72
    0x1102251a040000e12140c0051300300d907905030018001000024041e43c0c12045566044401042c1b665071003000134010094070070040c89003c00d081c00c0c814031b00303500d6101903540b070310301c50400b030459254213026070381340360f029080c183c1040003040050041481a4842d200b958411446000200c3e9100009613180d00580c000c00c0d640c40c400000e111031020240b2410b080082c05807007800304040302d4007407450100300c00d208207003e00501c5080c19400b0400e4500b1a0007502008008546a50302c0da00c009004080c11910303d400f0070b05c0300445400301a050318200c2052200319042d0418a10140d00340461515106541e40140c02011140510442040c80c1460300c980d1002004500702500212452599501d901035814000100700510210ba40008654240c40791503000559990101640628000e45024003801c554600540428403040302e4002165040603650340b46030a648034095141c8844041c3c0d0f10030401304082203004004941d11001c0c660200110469506200500302040480c1d40310603107074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 923887257 1250 923886007 923886013
    0x106050f0912060a0c090e06030607050c0c031e100b0916030f020d09030207091a010318020406030c062d0c0c0f031a070206060906061e0d090507080a0308040b151002 73
    0x2004201b644485501c0c000d24140000e9025800d200c0042501cad464098490820400001801046010100005141103101030100e48100400311318044c01c107140189250100d005003041a658144076004c2c580c080d0000030400c00e000e450780071103000394034000302c12007082c1340c1c503140d010050b078583d40301401540c0400700c030110b00b001c1c1c1ca1500a050a90079000701c8000b40c6407600302180c4180d6005800c002c40070a003030005540020314841c6814408444000f98401e0901c1c0003c800c00455403405411075840d500c81050701c0c0100c03030341c0a070314801d903d1308080000c2180d0181000944104068402380d800783c04068041d68a442104211514541040d45c0c00886007641d01c00704e201c50258240d0008040c800351400f814042d00041500e4005001c46103d02c4010513038a50480c00410140801c81d40b10705034a80c1c2e83d0460551001900e5a9402a00d050048140018900001240c0d1140d030a600d69135400c129503480d81c270403426440140c07903068034845510400820f81c807401c8240c040a200d503001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 923888507 1250 923887257 923887271
    0x71809020d060e0124060e0105090d0312061706041b050306070804030f0e010e12160f05120f070b130b040611060a2007110a0303260106050f0912060a 66
    0x300700e0075a000d0f441c000120174501440120171112a104034400e40d0114034181c50002103120040b11b10b4003074045415070001031a40910704241d0060f52400540341000b406014150360348940000c000100b9072552941c0c2c00160002c0d000501071003d1056130001c04040e9241c207034803100400d241c0502101e020001c601c545083c0014150010603182c1410041e1801c4003401050b0307000200700348a4800664000c0d00782a80601c5030303107002d010020220108000a2a4440e51600000d02c210118450320303000d0f005000c0720040c00750001c01c20408906c040030082068a24250f49901c040d84030594200700c1002891002c01d488002c140100024031030f540d0342449005689142c6410603402501c2000728a2810108200a441d0742851010041d00050b4280e11100315041c20120510075801c07003940404092404000c00d9002000d0101102000d9240b41c00500341e180c6c2a8030180083c050080032071801c1c419440d101075200300901d882d1070064401c1881103a4000011f18003038007900c0084c0d0098494803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 923889757 1250 923888507 923888531
    0x40e0109051b160609080d090b09160e090102040305060112021e1c030513030f03200606330d0e0c0d03030b0a08060a1a12071809020d06 60
    0x2540d03040200003040020145490691048034402d030f034511600b0300c0c28030044900784103003580315a0010740c00c01c5035a507035507201451140c003c1c00c2000085580d4042100402d5143e44001006806550340700c0000c4499400c11400d0000180010304402c0107640800c000f1001603010f000c0f20380244540c1c4400c8a0080591040020303001307050600903c240e0070b000075480c103540c1304c506084c6101d803c12000d030b17841041e9040071580b5200d245011417856410340000010800401d40303681c40580a5500c000d07000054441c00008820a902407441a41c003800c0407030b44520b03000c1c0841c8500301c0074044102c4001810491144c071407083c1031500e060060081105180c414003402503126082468010f00005190b4000190380b11403081c01c00340400d40d0324805040300d91a502c00540c00340c0240c0045844900d40050408080c1402180340a04081200d0701803610341004c41c040d850300c860078009001c002c0c3c20031b1021080300c00040801031005032a03246400260b01c03001e500d055020700480e80440c1c1a00d5000e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 923891007 1250 923889757 923889761
    0x30f05030d14240108041106090414070215010312050a110f1b0f01090b031302120313050d02090f07020c19031208040f0b0a02090909030a08090c0a0611010908040e0109 74
    0xc20280d828643c1c408854043d680e12031606a070042d440785a080103c510000030407124022046103940080c9060340640d040c4003803140d020320a81c1d140e401c80b040b054402c0841c040340f00b0300303100091669007404100c00c0d41c14000e0001d0083d4060358a41030040d407014205484ca08108001c402182e40c104035100d0341050861101c10302d00f8103080e00c1ca001d2441041000804100f400d00c125409224044045501341e100030364008040d503001080141c600b010004807a4603944121440000f400714076200256a04004071094505500105400c40c255a10003000f400410018030100c11170154680c034556603030300c210010402c02c0096002020700f5007185400248002d4401680c403e02c07464004001c00144110160f0440342c2d40194100c01070744901c0d1400c0040e005500103030f03622003a401c00308040410000b001c0c2122018665402c0d0607034a40c07541054030f800f001d0111030b0b00821b8070b030024051140500002c990394111000002502c00b0241c03a800c8507504030ba0084840404034800406c41550b2074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 923892257 1250 923891007 923891041
    0x4031202041202191802090d140d0315060903020405040203011d0703030228120e0a030303020903060604090314091906030501061103040b0711032a01090816030f05030d14 75
    0x141c8081a0030500740340c19442c003050031089800362031ba00081c040044c1c0c0c5540340e441c0001e50b48041e00040550460a81641342c405203610b1800191601050030070006081031080c0854840d41c840c080594216000d00000c0c0c60024000c0c1d80540d00c880d90105001c0e02e520714044240080c0024100c09401c0d49002420304200c0b01005036032803400c4c03804680214032001e0f49281c2a5003c120b030100340101c403038191a600220108070703600c0358440300000b040c141c0540050854100460940e00241e0300c5070b04003c11600c011002400017054a25410500140000142907943c0300500b000701c000c0c0b2040f0480203004150300b11100281d103500040040a030400c040d0030306c252170480918105810501186010b0040ca100940740010b000450045a01d0500c103000c80031280606e01407020008040395114040c4562416001901e030f020300207212800070070a450188140600812028a140ca0b540b0071100e0041c0b00b51204c0c0800c000c0c424500c0740c1c0e0300c00d03210200c400310186074881c5004400191140c403d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 923893507 1250 923892257 923892289
    0x30e152817090d030c0c0c120c0f090207031e08040224190f08090604080d06082a04020a05041707180c02210a082d0a0507050c070e04031202041202 65
    0x206c4000900000c00b81c07245107041d40c1154642e05600340c3c3d14201140f01041c0c59009000e900312080000c141c4242030780003001c24900a45641425400040501d17414100304141040001d130802c2c04100185005012554111601103040301110440d07001d144045e44040c584230281300da8660302e04c0d00107030441402c0a03131400b0b0341131120140c6400d1213401d03201c040080c00103018040004018002079050307403102c0c001d0a00c0004a444125022880c1d00c01e2604030600c034407a60000a90707198892426000b102c040c100e4650b542410185008100a50144281114038090141070030201d41401000d0001908040505000c146080d0858021342000003410203001545040d82414000342180303030403034804030820700e020002d907a0b6800080c0412003c041e01d0158082031403940c0fa4002c45003555035130140000c4d80c4100941d455846040d1114800d1950300d0760f990f0008801000340e811401d21059100e80a0f090207090f2804e406018400c9034030580140c4005010002000d040d81040e0030314400c1001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 923894757 1250 923893507 923893517
    0x12030d061d01030213020309150405061f0501050d1a10080a050903120402120c090703021c230411090a0603110f031c0c0f030e152817090d030c 63
    0x411a008074880510701e82c0c145c1d403440d400101082004108010b12500800702d012303440d8a40c2001d103000f58840509545100704500404480c280001000c280f8000700d0740141c507107500c0c0c10740c990703446005010503101c4d1072110003080310361800c2a01d51010340e42e102022a5920165880d220020b44200e5202070203011007644280a4803c003000070b50012a0043c1c0c040315140c0351624504000e61403c00100503094010f801c40091200468141d0007030030380c045d0301248202d0a03000c1400b4207400c031510b1511104805030a42c0a08100720b590090098201d405508441c50030403407540420080407003510700e4110281d0b1000c3c1001401109011500790440490391a0310100c003900000b5540e0904a0071240300742d0358460010402d600031100f04103503d07800744100010715103c1c2000b8000c503a100c400140506140900309130700c19171420440c6d80c01146040e580b0a541290604000e9100f03642003580b091000c0842d003581901811201c0a12840c01c080050880036a00034005003a031b5968640901800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 923896007 1250 923894757 923894759
    0x62811130e220620030a0c11060f04080c07060e01030b03190816020d060c0f0503160e0604051e0f04020403020603181c03060501020607050a080601080612030d061d01 73
    0xd2007800189804994694000004411402c16400900c00101c200301d840d4030300d2266030740802010010314032035681b0b10300800c014981000306a40d034061718070b880713641d503006080000d840c0b88100d10410307049400f5013078280c18410748240c0e403071030f00005402010105840c220f0b068915a85406240c6041d1000d03006059008030f0060f44903c940740d00d2400418034100170519003500101d030014418119001080b00785e140800d401c01e80000c080b21811a40041d04501d840f80c1c08600a0b42124042c070401d0b814072040580c860401c03106118070980c1c095000380100000035059071121642c07011030f036242ca040d1004244103010810141e0300614038a0080f801800100003503034900c0d00f0b80b903000000251242c445d540e0744000d281098962000300c20128800100c2202c0c2c3c07035041d4000403d1310b00030b070200c0300036403100c8500391040c0c0550360034200003032500400204036501c54025150400c002800e04100c03c0380540e2858115000880c00c07400ca01e507618030030404105000c807400040058200800340319 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 923897257 1250 923896007 923896021
    0x703021306080319300b01020105010b031603140a0e0601050901050607150216140c0d11040c0207180e01060b09090c070c0509070c031e02062811130e 66
    0x24002e10b41005801114800c130310b42100d002d8002c1e02c441c9220103a0741150361803409162401800c800160009540c640242c0b0341895005215840c1a04e6942c0d83d840d00710380d07500c0c5800d5210203d0000b803408150702c441c03504a005513040d03070141c00b4100861000c2000300d01562035a05d0040141d22a07407040c0d0043d00100f101d900d5a800702c1700d0041d0885401045103049510381c20103403281011074040000d01510b0b400501401c0e45001c1d1803000d4000030340e09200007850802c070007109110406080801e1042c2d0f4021030b480c042d0311052528190f401550500ca83e103c4095031030700741c1c55607100159a141d0450000004081c841c4201a1001860080c204002200403e02503003000300a40d0a8050010b1030344103118040001100409000780030040e6840e060340d005000650b0740c0b4085002c40d0084007074581c40d051020080114061581c02854243e44158201c1e02c018003c04a107000041c6510520b010510b860081d1002d80c0c041800036940e980b00101c603841039071020b030f0100c0082040e0005118030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 923898507 1250 923897257 923897263
    0xf0501051b1911070308070311011e09020d12021c080c030103030e12010603030e1c020d020906010e0406032006030403090b0304061e0b040b030703020a171c02070302130608 76
    0x5002400d1001c01200d24a0980c10b40e480391044501c0d0602d03102e84e140000400c001180200f0b8924030030703902d07543c49080c0d034000b044c00d07104180c1d64060080c051302241903410b003c03980144100d41c00100100108821511001c1100c05840d001c000140c03c44d03200c2c540640200444480e64904a141c00d000600d07048461a116000c1030000a040014002c3c00d03044a070f40e100210092064000c00030400d90b0b550b841c0107400100c8941069020b5541d90800c16110000009941d07031083d009014000c0600d040d40c2041000000104414180140b000c04403045440d144201009035100e40ca991a0f0507450082d413580b102c0940c642c2c54440c000400411000942c809011001c445208566549039111403601c0405814441ca1a02103000c40503181507025802c0d400151b00031500380c400f0041c082d08041456120121804065000b80181804011010b04a90407015405201c1d090307802a000400c18034040f0300241c0100c0d00140e1000c401407040d85094a4bd240c1c2000c100c0e2407c110a81c036000d03a40361 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 923899757 1250 923898507 923898517
    0xc12060603040501060b040e07031a01020a032717010509030c0a060e0a06050901020d050a021806071b0611120a0903290106031e02031b13120f0501051b 67
    0x40148804400700703042010940104000c0c01ea104006c03521217803075503540c0d001e07104101c4d689070000b4184501c1e81c500c040d00e08140c0f1012007041c0d0140095120a86040e215070401d060203a9988007012a0808451a115418400b41a000d1441c0c4050760141c21018207448010b445075807960000c0202c581c51000025600f00c4003603000101040c200d400b802d0322828200c2202001d08000d082c5000c02500800640c002d2984d82d00c62203040010391101d000c40812400794020079243c51101c006286400d103480ca01034440c0034441e2102d41000761295158043c81c02c620f03031142c00807030302da00e1200c0c80022043c80381b542034001400409041c0056904024400710045c40007401d03041c3c03080038100504078966854400e040c0d07440c06c091829603540c40c0060040501e0a00c19200311183c00500c110315055000b12801008400c024200c907881211f602e04866004000c940001c0228601c001800d8000c88501400e1034080e05040c0140d01c00c0341082420f55500805100d007905020031071960703000303510041c1c0ba = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 923901007 1250 923899757 923899759
    0x310110313030201020702030613050d080c0d02090a170c1804080403021e120618060405060627040b15040e100e070306090f022e0c031b0b0406050c1206 67
    0x141d58915141010b070700a01c5000340c00380d0140150f900300702d00728a9440070104810f01c9441120b07001d41c2c05507012242640169840c000740312080144103d50040c0d82c01805101c0001840c12030301642e0358004030080c400860203100a5001105e48200768500189044408600c40310340010304d1901c3d41e01c22405201d0360100a00c80d91610000c9d484d18240c0c5038a40d40e42c80400381c04c5022a020188050350380b00c108072151501250b4080c01b5020101c0d01050084c042c0b94801d0040040c0c1d04d8031420030104400400039192140450116032850801021110f405180182c50091407410481c01c1c0c803801030003200c150f80c019801e24200f4000d55000250700300b00c1d540480000148080d10725280350038481641e0019200e03d08051140c800c1c050056800c4403175602c21551840400040c074082c103c0d80958030300003142500c6200d880d18045000b0660406000c1c40f030718080900344a499094640d014170000300792081d00c0354034100006c1013014030a41d504003690403101d9051964528821000110040c119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 923902257 1250 923901007 923901031
    0x60412111212040c05040e070e06010512010314150a1b030c0e01030f150b0d05070c0f12030920101e0e0307030b130b0105241e030c0903101103 63
    0x14040c04441080c1c4c2c0f02402c1c00900070b2207401c07491140c160703a8513070902a282c01c009035440880d00c298000c9084071ba03800cbc014001c1124a03840c40c0c4640b8855000211401050f018002101c01c1c0710241217001d5104800c0941c1c00500c0b900980c02401852851070411400c1c10b250000800003150171641820803035030246001704000055031548809030020110f00811800482c901181480b00311014140e101e803014410002a603038070b5802c1300c00310a0400c000d000b1040f440052400f190a50184504100a0342408a84040d940d42d41c4000300a80808c030002031400d44000c0201450a60120020303c00a0315060301400d040e0030301c1c41c070640e074000111800c1c09a00c0311084040c1d1810310169006640001c5809c80f00d2400c0d40c4030225040d2000000c032800c0c15803400221381480c0200000c81180800c5106101114071111910030759489103038143c244c0304400c0c1040404448180055100303540c0b00c24116103400108041c946040785001620200710b0414080300b14130410541a030303030300078038151714 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 923903507 1250 923902257 923902261
    0x402220819080a03111303031706060a050304030e030601090507110a03270801020301090603031e090e04060b0409030e040f0b1f0504030503070b0415140606030711060412111212 78
    0x42500207120500c200c040d1704801080001440300350904801c100d90103501c90b0b00a8107c022000210642d041358140da1150702400802c01e01031042004d107070721521070704001c5409603002000900d8460241c0c48035054a80702c100304079080b6030180a01c011400214010701c580c40450b580a4003005070351800c00c4000c0c21440c0010300403010301c00801c0080000b00b00855a95850b200b441026003518007003980441e564403048045509241c801201810090b034130211906c2c103043e8420ba080c00c000d80b040c0c40407078a8010000d840e5271355118a00c2690300c01c0e211068049906002c0c07106a92003286064551440c1c00d00d62025511001450281124a0440202e513180090b0060707580d4007894002a005101c081205800c00110b200018050743c0541c094401c101a07503210541610410f01100301122240d40100d2224108034021f540c000c1c50500f4544100c80801440ca49007000482d019121a10340b1120028502d410614940d801c07ca0900a880484844040c0d12901d210740c1c28400220440000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 923904757 1250 923903507 923903527
    0xf0f010e040b0609210d0207080709020a091d011e03110f0103200301030218071d12010e060a05010608040506011a040b0708071209120803100302040222081908 70
    0x30450f50142e00c000d110354032901140f500d945c41da00445650000ca0b2140d03c0300030f85007030300001d41c51044982840013420f2403400c10107041e01a4024618800500c001c0c0a030105440600c1d41c000740103403c90450003501503141c00c05400ca52079808040d0403500d11050404e1002c500e00340c141d280490416980e001d62181d00e100100c0092202c40403500031004400c400e007030000019801141240d0086407100c43c02030304840c00b141d00d00002d99510000c9911a039101c031585c1280ca80002c41c080004045003018404041d8050965068509610240d00980704100d011200c0b481094050a800c0c030b001c0d50304c1d140996401d03035205c4040c0076440050099000c0b00c04002040401c9030003501c210f202e07043c0c40d42e07550701d001d10309030b000701000701c0700b0314090400c1c90020f0b40b2902d94202143c4510085000904a0b6210241e00d0341c00640524a40d500c030900100244c1c41318001010420000c1d46c030011a00320148210303040754901d400c8290340da00b04581c941350340e54102c1100b03a052034003c003903245d507000701e2a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 923906007 1250 923904757 923904769
    0x60a02130b16020d0c081219080a0b09070221070305070206030c0403120521250c05160e0f070c0201030507180b040602011401030c2916020f0f010e040b 67
    0x100003903201494109480802150074001400c031b0307030345204440c101e003280032845c3e200380159014001d002d13220301204190303a4801c160310340d04060074180010b00c8155001c04240380341d000b02c500f040540e014220110b208500c411091149119401e440383c00c0040a0360018003a01c03d04901900c9110040041041001444202d9008544c015620541d8400030382010740b8a0b0800800c0604850412071a01e207004680903e1500c85e5090700c0032544822040405100c40504100c44c0c4001c02c2007588100b40066800c0100344030b600000c11514008a1500c0d03020603409a0081c0068003001d0f42c0300c20700502a40000e00400d48990900300402e00e0742c1c40704800c0791002d16182e4005904110644c00181640f005002042640c02c10381c000c0c07084142200d184058407100b84001018444411800c00c01180d11394058281d5941c88011411811901403540516400a00d6040f010040c0246403504501e0640da0004511400390fa00507041e0b145240040c10344540781e058903000e980c85100c8103090b65521 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 923907257 1250 923906007 923906047
    0xa0902040b041a0d06030f060b0f0a181e05160c03050d05040f061e0e0a24020903160501030513031709031c0506040b0a0e0a020f0405060f030603060a02130b 69
    0x6030308003d01076403818031540030031090f030702035960301c2c41c1a270b040803030b0b0524148200540d14043c0560035042d00d0004a080c1ea04140c884c10460740d665070642e0016890138002c508601080c1000124803030800501d00d00e689060700030340384180a003003080321000a400c40c003640c8080420324400500c079511400c21042d241d041d960010403152910303840c28400f4100301c2c2070a0402c2440b401c20403441c90309031105a510410458040d10000700b00407084c15048545482c84901c2070200b601500b0074021101203450410780f2441801274902c0c0034014402035034540714282e44042120f194007600341c455180980800c000000c06c1403100c800e04002140d00c2030800031104030b2583c80041080c052000c3c80c443c00181000c0d80c210b44664181002c80b901407600343c41d0300042d1041024074410310344440c1d0381d4074001d60000d030940100200c240400141652150302602100c000c0d584469a039103008002c260510300014400c001d194410300c03a031091180f580b60000c040d6001d40b40307416034070aa414099114401c207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 923908507 1250 923907257 923907277
    0xc01090c060305070e060c150a0207060509030301170c09070f0c2015070809010f0c0f0f0311070602100b0f0406081f020a08040308130203010f0b0a0902040b041a 71
    0x11580c4006501c40d41a0f0007244642c800f555400c1c0254616010091a48601c0c8203018403a0300100448003c5d551791a0803903000454040014580701d880e90303500003a91406c882c000c00310741021004104207032065100150301c1011201802038100050000b0300e0240024003503c041020007521502124080d0a03070780307051604031600f45980300c0003251340104e2441c150310700c034041c0440c1440104004401c2042d1000641d001203064100310341c1d440115181c02942984000b00105c81d01c0260108044000d90200e03540290100303202d540140c1030241020000213214243c550111004104081d808074009944010420000c180721072000005000c4401e0107100755801450200001707410b03100000c0340c0492100380102e8112030240070144034100e008080080d00840d031640000b50010f031041881030b40c0083c1320506021042401d03004642140c0c0400f10400c04156629005034052410340d011000511942c0000d503d01030500792400401e000e03600c100e10240c1440c00c80c21001d8a0f015041c0c480c4c0ea01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 923909757 1250 923908507 923908523
    0x4111216260f01020405040c02060114010525080d0515030c01030f0b090a14090727021b07080c15190c15021201050d02030d200a0b0613060e0c0c0109 66
    0xc2805400c0f4001d5001c1c0c4a6030707114030f10340290745004a001203046070486101603048202041800c0055402d82d200e410b10121020481a40903030a00300503210b4000c55000d003c0050310391070940f0652040350380280010001c48021600703e6469900081c0102e00d031442032802003007401c2c103440b502c40a00003080c801c0394000114030412441489a5001c8400d40181a040b42604d480381d400701d58585100c1c1c00350201d00c603035140e000740a066101180844103400c035000140313050340034000024500311084414416400c80d50042054200803c24001d843c3c90460790790803000000e1203414118030510004140c00c0068105c02880c450040092642581d0000d00c84640588454032510082d4403546074003450601380300022a0505108232401102c6502400501580001c0841501d4441d10300c449a60b55000d01c1e080080d83d5a024010208000c4c880c2440154a00f080000c01c5201112070a840c0c2140c1d103800010003100b444c140c03045800656511041e03589146188690b40941880da0018101803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 923911007 1250 923909757 923909773
    0x604080a05030c060c1c02070c030b0a0f0c02031c0f0605030a1506061e18090f021e031302090403020f011a0108060a08121b01050411121626 62
    0x8503021000f00001c80c804025583c00d55204c01c8100e04a0161039034102c00c0b02400c80111001310260303030007010500e01500c035030b84103140d5a580341090900b0072160500c43c291282ca06442002090141d82504401400654100325415003a41260211191012200307900c0e03040840418046600401c0641005020b49540c40010f061270511020802c14282815180c60000500c40740700d620490008500b102da107915000600d00106da0702c542a01220102e2240b219000034400d01600c41da0002602020005da103440b6500180003512051078112482d485080081022465141c2d20710a071045d4125031034000e50b1541e09003203140c440ca07401d801c8415840c080c240321480d407541d1000c2c3d0310190240e9500c500b9540b0602030203000012489240380f80e61040c09002522880b02000d025500712071071852032104003c195460071340d04180c0b07054444800d6108194250300b0b10b2407030384251181c8031009213100782d0500d001e908220800e00c1000d111702c007003001c140c0180080c1411524802c035034001701c03402c01d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 923912257 1250 923911007 923911013
    0x1a04020c031308011109101704060c02010c0503010e060d1a0c0301030c060c032c030304031a0f0f06130f150f050103111b160602100b060f0d0b0604080a 67
    0x9600c5000000001002c00200103610001401401d0380c0800c03440c0300714200900c120034496084096200d010500c1134020f001c0c0c2c1426010b200152090f030040002091728540c07104041c0c211004044003104004080006100c1090010361080e0049810381e101c0001d01118103000e44915200e1114925488100303080c04428032102001e141070700d02810641c1503140d80d62400f0f560904201c40000c01141e02e408900c801408801054540201c1e00c100381c08078070480340e000030304546c025041114581c51207405804141c2d0458049a40071860748401c0c6002d040c11a400001c82400400f024850b046003078421030141140e4000d4010b9494000d018800c1e104200100000100540078420824003402c000182541c403902a0380c050605146c0c155140032408500403e404034482c0b4030407090320130a42c901089201120b4180c000b4900765026048003a041159001511046880c0b51310940342840b2042c1d80c202c01c0c100f10340c840054000300007400f4211c2c402007115405550710149460265007401414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 923913507 1250 923912257 923912263
    0x1a0f0d02090307052b02010315120506070206010b0706090507030b040f030206070201180f0c0b040e090d021b01080a060305160501080a0501031a04060e03161b030201080601031a04020c 81
    0x3110841c180ca61041d19041400f0040100944400c0d020b4240d02105d148282201c80e22481d59006260103c0c6a041e10161785c140380045d0341c41401c1c20003480d0f032500103021040c04183e40159081c80580311a5140c040e103011180100c1700c000c3e0055036141c00d580304100007003002100859110645417228030305410400b0b050940380c001a4094007405000542aa10602c14403c840c82c80c0c6004000004058480ca501511031140c00c0b625203000c401d0200b03d0030345a001420003041c0f501c1082d01186060201725003400500c15119040d9072108250180b584084240b10301c1181c401e01c0c060b1b0701690b070310820b60043c0c0015480a007140c056055440d265943c52400c2074282c400c00e072500381d0f198a43c6000f42c0c0c11242d00348009080580f010188507084422845916001801000089607608215039002d06640c018140c1d400c0c0340c0b042141680030400d11000305503001407209813400646196800103490040010700c0d8034100750b610311442e45404004400c1040c0f8620182007151500c80c06001c2035a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 923914757 1250 923913507 923913517
    0x91e0614010804081c1104210818010203040b1603020d14030c1602130c2607052808011805190b04020409061206061a04090b18041b1508011a0f0d02 65
    0x11065260074640300c50b101081600202300b40d4806807451620082c0001c10f000c9900001207541180402c000006840d540040a071101d01c00d9114504040081450b020345080d800307040305002d000c00300c0c07001d900b403103071030b03400c1d00d03441406500681d03507402c1c201c111500c401d5200310000b9400046100b854a00002e50340c4511001da95541f1040f010982003040072016101401c15201e0b51011900001c1d20705101e400500044880003000405248020800d00082c124030301c180c000144101e001006001e41681c11135506508086080000c2d0820090319962804007402c01000240c6130b2901c4000b51f140c6904403002070410100c00c01c00c003500c8000024807402d490206540306400d00c040442c00404c0e0800c0d09101d44031842013140b404d4034140c0c0b40405480d03203440c401e030302c032005055108072a211500320390310a070321038100144d4a41d0f40d010075480b46a8550000481c81100031010f811302c0d40c02503815410745200c0645206540d0b00152400110310414034001102c0c0c0020590802030750302500584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 923916007 1250 923914757 923914769
    0x160b0927270a110f063114120a08030108030c06070804032f030c0f0f0106120b040f060603060203060102010c08011a13090606090305070506120718091e0614010804081c1104 76
    0x80401c04400c0c01b1884008503000e5201c2c26000c1000d614054541140c51035234007a011001c0d10078020301c0c0e459460312a00300341e10180c41ca2300f0010311080c004000780b0080742d01840300d0800320040d0919450050099000c41c9405000c40c1844036030910503005c00c9100449a083c5400f22961010000162500c8030352808105c0c006100c0c00c0c030032949800c818003480f4203640e03e420401000d116281c5900356094800740090b00c808000280f0f03000402c0542c0586800785000b03090150b600c3c14447c00090844003a102140104000c0300014010f451801c40c50b09484038484251a4071200305140381040d002990744408030b403601d4010b001424540000c02c4804590250069940450b030782c80034444a8422280c1240555103c100015900c3d4091a87d80007500c241983c01d43c40181c4481d4800e00316603403160703540346050341c104d10441c401c0b06034019640a4445000000700d4540058006082d03c1700140004105030340103d0080001d20501e0a031386007080c4800002e2220b00022458040c0aa004e03014074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 923917257 1250 923916007 923916067
    0x4060503030d090b0f0402180a1503030305010e0604051b07030201020d090f12050f0f1c050f1f030c0303030203130f0c0e0108160b0927270a110f06 65
    0x41c1084c440317148054410364010700307024468100c00090790300d1602d004000c02009981d410031904210400d82c5000085c61080d20300091550500c1c1d002c650008004111502c92030502003080070b01149011250f11842c02d01103480d46a0010785000d90190052414950300d642c43c10340c6101c01c2c040000300c0b00e101e19004012040c0c810245610072505442240c0c0c0c01702031803808000d010703c0051150010702c255002000c022280c4200503504400f65002a1160075941010006018424042c03043c1341c1048043c80000c80d880f280f03075944081d16984079100250034564080000392851b042c0811810b8030582c441c215400710340c03151418801c02c1c1c0b014000c40180b2a9400000306105c24001206d64405814001c111044c600c1c2400104032071340200700194001001c1c3c5032021690500d200c1008000d003a00e2070071358a51500030384c100700103c1d0366041000d440c0c110ba60a40701008011070764030141900045034a150201c1c4c80e0100d2041d80e071003801c45802500014082c0011202004844c090035007000b50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 923918507 1250 923917257 923917261
    0x1b0b0405010203060103181119170f06010b1201050f0607050613120503090a0213110c1b1005180402071509140115050405150d12030c0c1a040204060503030d090b 71
    0x2a45001c01c0c11a4004051541242c1c0c02c41c10b43c0742c6503804480209c0b40b240c038004110b8564091882e6084000c00b00300b002d5200f562110130800c4148525805422a14803007402d040281106104210341031140b0750003a81c1c5a2100c1c07450303483e054101c1341c546802100b260428202019060999156888151090300034807034868480c41c49802264018151700008119007071143e007c00601142c0c04504121040d81d415410800c4242d0001821035640140c000d4113800a840319000c3d61040e400c8159441009040e40041c612900a001c2e0340011602d200603029001b480000700f0002e20070400003402c81c62424400803041c4943d9002040424480d501d200d58400c01b074030f0311600b81c0c0c4128410003c090401e1101f88100d050661100c0d42c001690121101c030790301d1170700120b21401080349043e40c5090310394009581726501805400c80f5800c0610304a02500c02d20303182c00f41d4010728071910302402e10361540440e05558468004078041e080080a980e03440922f1a0751800a0181d00800c0b41c200403d100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 923919757 1250 923918507 923918531
    0x610060c0804091812030b090c030906130c0801052d01081e100501171209010504151e051306031a010516050304080304061101020702101b0b0405010203060103 70
    0x800d161150368040d00c0c0c242810f042000e0039014000102d84040040d4130060030b40d010034030005011400380f8060f00d002409045603800d0290805000300342000400c010000c0c0300f4442c1001403455480420141c01c41b200f1851490b16100c0328440da4071002e8190b081001b0b200382d4618910100d48510000700071409a808030b60100c5c3c0100c41300b48521206500700751803170002c0081540c0403c00840290069412008248101d001202c900782c0018840c40c202c0410001e60180400161540c01c11a2118030308042e41c2c440000d10b54440d50054071000e10681c0300640c1264013504200310600040d2009104c40c3c844408000d003185c0180d02c480c8603200c02c800b030018449010348944240140211107070301011441301d0040d14107a01c84114503240b4261038240794049a41440603002030292100035590b2603150030360040204683c10901c00b01c59104105040050740c4043d401c00d14004541080703a69500d43c4c01c41168080c2c616031010f409520114200010003006500852044000340c07401c2080c00040d803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 923920863 1106 923919757 923919767
    0x12010e0a020f0915010e01111c261506040f0b12060a181d0a060207150b0105040326220b09030a060b120f061006 50
    0x100d80d10861414411622081d2422504150542481101d02c01c10a00c240c1c2c00e10b0500030a4844c00c202d0303034010880c2e068400c1c94102540c035207510f00c014810102031110589000102804241d0034110030f16000c64040b809607010324001ea07038403010000d000c44060000c0541c0500240000a103101800d00c141010f06294034406440358906500d0341d1302c482d400781403244201d0f0540402d1080301d840c401c41e00d0103403055110100798030b4460500c80c080065440f00703180c00c80c010514003805110843c4c00500c541c1b0700c210726040540001d808010200c1c4c102c507050030300081c0c040008101056a11250350701b01030300c5102500c1c04054059180c000340e40044070001d20706a8208030250b10032004002c800082c4040c00000f8503100000340020744039001c03920001d000513590304c1013413519220110062490202e200c2103440344008401460303030714070040b50440d007111840440812150301c94 = true := by decide +kernel

theorem cover : BRFrame.Cov 923741007 923920863 := by
  have h0 := BRFrame.cov_init 923741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 923741007 ≤ n) (h2 : n < 923920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
