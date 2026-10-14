-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1541
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:29:01.502214+00:00
-- url     : https://prove2.me/submissions/21e24144-fddf-4bbb-a16b-a6e9fd1ffaaa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 276978417 ≤ n < 277158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 276979667 1250 276978417 276978431
    0x8061c150606090f0902160f120923010315090c0e09070f1b030507120503070305060301061d09210c0705040b0f060d0e01020c0a020112050705030601050d0605090c0c060a 75
    0xf144c50500180d100b0004501e0b404103411214540da54082140c642e0841da039510840b0107421300110000d800304040010941c40302000034802c440001d1000d50321a0094651122860b400c0150060711440c034616140b031a00780b0001c228510340b0320070000345290369501d100e0f54208100034800c000300058910024840c18150a01805601c08241c08000c0d101e407a0100e40130341285000c0d1503a00801200811100b030b54690b01c0c20440c0e2010145101e407102d5941032229455040601d07088030780b036015080c8807880303106550040080b4522000d40129507081154034a07030481c0303449080011001c04004800000091100c5100010000c2101820342101d0421400204400088540c04480d008030f00541000c10b40b038140792202d51145000329114002556544040b001d00f9841d00c900c1c3c4002c03401b00b0b0904188009405503803280b64424032064a070f441c03450b2141401507460340c0042400541d015100d1302d02088a440303801a16000341c0c281d01a050720340c1345150216041c1103006000f02d0600c9c0c030740b82c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 276980917 1250 276979667 276979679
    0x1109030604030f0c0203010c03020711090f160516050601030209090708031c020904090302030d140906070e120a1101170709061d03071707080d020d08061c15060609 72
    0x142260000d42c142070110401804440c251001c10f22200007079450352030407800400140e0950020620540314000300030355407000380d0401c00c1c0c0700c0098540c40712f599614000550204416110f00325000d00e00e0502d40d092100196440086616900040710305800c16001002141081c010032074001203400c018140c500e04100301190b032030140c130120380e1620340220003140412100743e040b0760112901030014400c42c155418065540c1e80240c40100a480c9010170305441440b00c4804240500c0c5004081c0125803139400c03003214004503002c1c809900414201d0b03807900c0c0714410091035840910800c00080c259540e840098900110700d9210522003041e0001c200481d40d02915040035503000c0d08245c20014054140f01500c00183c5000c1901440386050103d02c0b41c0d08440c41100601200c400c030340d074860300c0d440e07015182d15441c1d158070056404140b0301100580500f00840e030001000c0c155001c3c1d080c40c04d030400c004543c80d401c00d6856000915030000b0302031040c00f800019141d85d05024010f43c0c40c0103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 276982167 1250 276980917 276980923
    0xf07020306070804080702010e12010c031a040213120212151605090108040f05070f06020a060e1f02180402030f04110a0f0506030c0c0706050a030b010c030806040507020c060c0c04110903 82
    0x6e00024104141c0409129007036590b0081c10f903802e0641c10080001c0d076001100940140201c4600504031101c01e400c6c109070f46060300031205211400e60010007154134001e4650075a9244130406c980c0070602c4041303200003410810421042e401ca074a1010b030181010341101072040b10702661fa00070004100410b071002c2e41c120207040d400903030107011200c0d0782078a801c20310700b00b80c040c0e01310a404250740c0c42c0c0040c50319030015201000718001e01003006001000d402807540c9030b02410040602c0d4a420004407985542a0301030400300180d000441c0b100d054040c0020202c2c0d204071a01403100e4084000d00c820701000c8810050842401e4070341d421402d040518045008019203c0c03070b880350000000088141002e1402d54040b040712604590b8083c0c0c0b1408090010703002800880c000a142c005810542d43c0300d03011680259815072100396a50710b0302424440075007001007544040d0300c036500c2d0051054031030f1001803a01c20740e100b000c1c0849800c00000c00090302d400c12100d8000031800d1111590f40e07034000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 276983417 1250 276982167 276982177
    0x1030b070525150e150f220f02030a0b040308152101020403170910090b030402040e0f070f05030d1d0910030f0c0608090d090e0703060b0f0702030607080408 69
    0x203000794114101d189001d028001c1c1102681401501301858034040c6000020501031011030000312028942c4c0e000c8841040c402c044543c411020b01d00758011100d120540c001c624030500401c0301039004105a00480e00e01240b8200840d00c60360345038100024180d20200d0181c00c01c030080a004400e00e0b48000040300c07010f2403c603515003442d04100c00100d04c6401d50403900107603445115a8040c1091400b004555008a05070501680004026610540c49554030b001641c010042041c1903031030315001d000080110046044103403050350360956022804101d004002d00e02030f84c0821885083c20281420101c5500c6410b09100c8040004007401041c50200c55064000b40c50403252651941081000044c444d40701030210803c042050b01804907900e01d10b0240c52403a15088001d40341c1005641d510034007800e5920001d1000401072020000c8581c915801804924001c984140c541c00d28844541c0a00b4007020503084c001502011818107102d466442030880c00d01030590b14040d16003600764498 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 276984667 1250 276983417 276983467
    0x40605060105070c183602131404050106080a020d021302040e0a0221010305030d0f150b0c070609050105040e060607350f0703110708030a050301030b0705 68
    0x160000644981d10031001d80b000c0580122910107002d94555003084c4031400b1041010b6220301b042c1c112213014100040180d62004c5c92a080c2c4c11046541d0300941c00a65280300413640300b851103e100740640c1c0e40c1d008003548050b514510180c18202468040d0840302180d200926580006210001603541c940780281519015112034070b040b461803000e00028410360304018119102c54040c803102030700580c06001042401c3d008404c03120310303840f510b010180003444010705507801001001050300c0701c0c0c0c00816040010758400715400001808118245420350070004030480041505603500303504001403402040c690401e05919801c00d00001c00d00d200e640102d080880005000c2903050b22082c3c100d0f44201c1c2c000700300b503158507a011040d10100b1140c0030000c049402404190f0340400c92481113800341c158a082d05840c1c81c1150303905403551110000342c01c0c42e5001d8280c00041c410000e100812400c0c10b603560721603581d030451601c055101d43c05043d000401c403090080510308020b9400210304182 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 276985917 1250 276984667 276984671
    0x803040e06030a0803100608010f03020f010c0c0f060e0414010609120c08011a041a06031f03080c030a0807110705060304020f0a030b0105100305060a1203020a0f081201060e01080406 80
    0x503402000c0b07440d0400084005001140001c10005507900e00b031402e00c00c0c0c50b0203a0780d41d5816640c1e19600c004080c401c0c08061341c8540b014006414640c007841021426a12950441c090076541e006030b00b028010350350044010400015101d509884e142c4221000c03c1c02040054800754100140142640403030b010305414822540804014010360490b07042c002c0082400902031602d000b92641100c0341300c0f00409003d0740c240009031100203500c034209c00d08000040d014900750b50f035100040ca1840000e41c022a142110305502201151034100144040e00c0444001c603038680c1c00e500b008014000040c00c880c00c002900d400c4d803c88480c0815410101c072000c07100651a51030310b0000401d807041103400c0b01c0d44040c003070300004108900d0a1105040307440440340c010701d06501b81e40c140d050340c800301d500c283c0c8419041824459102c43c206070f6a0f100f40244101c40790042f1598800900f0740c0c03404070944048102147c0c5401c194254a6105c1c094095440e1044002e0000000070705806c070003410040110b5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 276987167 1250 276985917 276985921
    0x102070b06010818100f0605010224150d0b070f090f0e0a0e010e070e060307061e2001050a1506020303041202031e03010503010c05030408040e151002011e060803040e 73
    0x184d01e081c044240322202d107084d6415500e000c400000144010303410034a295043c50f100156940c00800c04441540d5201001d045400c0701c0358080d06407450081512407400681c59107048161203803101c1e40c0700e0900c500010301c0303282411038002c0c0c0844515104441080706a5000340164582415410308894040e2003045140d1140503485002e00000b0410340600d40c030b4031425500d0404000781d0041158010120800c458072101c0a15807550514001c1e0030102d40c0c80c10a04051200e011241e01d00d2031614034010310302c0c281280c00303668880002c04055400d69140c0051110701202e91003a62007040c1100c0c10209070301c0c500400030b5241d001c000c001600e079100d08811620f01e14000e000700c0351b107419401f8004015a6601c503c100c1a90001e0054900079031031710080c0b0705040c1c000c004403806160071000c0d882c1403514101206803001802000e0703e4001c1c1c0305c24001d0301c003a1034003141040030004940010454100456020011080c0303480141051400c10904014041012040710b0541d01121940360080d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 276988417 1250 276987167 276987181
    0x90105041502071a0a030606080c0f07060b0312071a040f020613051f0207090603240f1b08090c0f041808041412030c03040e040219090605120102070b060108 69
    0x1260703555203d18042c40d410311150313042e42220b0004001c1407019440400429403101ca0444d400c4100311182d042c102c200b00040c420704182003002e4000c46100790300209081d9400800309080075100b80d64820b40720408134245040000032010481250074040d00195146400d4039584080306a01078080d01402c3c00041e64058000b20200c2030018280203406040c203404903110f508070b88040650030b1401806406000308241e5914080c507022a13401101810704603050031010011401945c120f200c1c03481d40e40b680c1b0b5418204500400c42e0307141e00d025110040710807110026004120052020306c2d940c000700b480c0f1001c0d580700f4807000a00f401c152400500600e000d25403e140d681001c0c006400c403a004100003881820101d0035020000c2c046d0b80c603102e00e40c4442c0c0c04583d0b901681851541b04d130000d120a011401141110f00e52180c001805980004483c90b01c400f4900900c0d0030000c40103464203418419030506445070302c18904803038000c43c50701c442500c80d41d4522501401709410405074002003000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 276989667 1250 276988417 276988423
    0x91507080112080d050103121d0a030311070801110703170403080f06010302040905190b09091b01031806060f0b12060f010c02060409140a0504320f03130b090105041502 74
    0x45182c66130707010015940c42c4c2c240100102d46032165200042c000362040980b80520581c4a85505005005001c5540c1165000d48021400c010100741a125000d40010000e13424003401d014002c9800026030f48241d281030080c42c0d20040307807805000d403441c2c2d41440000b96001801d181d2081c1c007828002240d4641c0c8004030060b10941c9e001e100d50b14144001d0141184070b407400d810380000000701c00c1102528080c2484070741103080345d88101e40d400c98840f031005049590030a902e8000305140001e080340c2d090a29031078002c1c00d1102583c03401d564201c02d0148002441c403950140441f41009400c2c094030b054000303290310009000074021005d4001003802d50340100d141c840d1260b4020403044d1182e40700d45030b4200400b289081d0711000781c0c00c18003013403110926100712402250007009c804548030001500c50034400c1c00741d442607080240140f20000140b0144070110341c9104800c051580d5030754541c91140884016003104000081c00c00080701c1ca40c2e084001c5074121481c9480ca041200c088007400c0e81 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 276990917 1250 276989667 276989677
    0x51f0306080d09080c031f020706110a0c11030f030a030e010605040e03030901051f210c060e0a1a0702090a020403020406140102060a0e07120222020309150708011208 73
    0xd500c0c40b580c0201100142c1181068003079803410700440c2e080d0900d8208050f903c4d02ca110f100031320482c8032061807101206640080010380e00483d80070500400c2c00c0780103102c0d640110100e0303000900e00d000d04410020081210940030030308800401d510b0690702c0b0516281c0c46031043e41400c1c1907588a002c0c2c1804c0080d004200200401001041031403619200140c03070b54002c40302c0110035480d050000b002403048040442e0024600319140899504040d0040382011480e640381016441808074500010644045100900707401c0d0345600b010902c00c0c00f4032105a0050b0005030000c14840c403201e022000c4c3c030095440d0300da01202c40314420f0321541d508100a1285030030103900542041c101141c0c001c030700409038121800a0342216031039910081c42d8000c8a003800d100160f02e4016083c10043c004c54988102000d42c0001c06201400744000103010b40c007980c40c9010f106250700402040741d000002e0004450075014041c0032281c910b004003005003100414003501c1641d44012607140148060751080c2d075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 276992167 1250 276990917 276990929
    0x20711030a0c03051c140307020109021504050102010e1203070807090807151704022101020c1c0807020a03120513080a0909110f0712020309090412120501051f0306 72
    0x190862810b401c01100c42c901c24001661244540c20f4445295400040d58040304152070307480c403030500c1c040010a00f07641d2000c3c11000466480b0222040507035103100c440e4842500544401756103914180002e429542c2180e440300c4035400c000c00190600c1895000c40c0c0e406030642c0340182d5a0b9135002816240204190005030851184900c0403501e130f40d0034013501110070040d80340c8400303601401c283c000b40c0100885000790000c0c018011282e89100f101190520f8000d01d100150610300c981d06401c2c0740504004811000c07050701c41011104a41020005070440014070282103044003540f4013402058030354800c5031603195200000307091094042d03031064406900046003a51800d610000400100e094000c0180319441c0160b034225541c1a1400c5a40124516180509001040c0c581581ca00d4550180308294041004120320f56034903030880610681c410403400d44900741400005110ba04c180c146510140e2900006001e10f56031100c04644000410314090742d42000900d0440140035264040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 276993417 1250 276992167 276992173
    0x30412090e100311060412020d06180507030b010b0a17060619030b01020c01021b040b1801060c0b0c250f0b09012403030903030c050f030a0e040b0d0b060402071103 72
    0xc04a20b003211250007048030300031859504203480000421185106902c1803c9188055000711001414a1880b00780624000e880c006000c0040840814081110507001c50343c41d000244103004001d1008210b501401020b60741300e0811101d03003005402442d0a10f10900c820405400107030180d074070181111644d41c1c2c6090410035112903400060090080c1d03002c0c0c94054001d0b10184605541700045084200c0b0408446009502401d4203000c01000662442c40d040b2030780e002d00301e210490301e212103802071600b541e5085410704181091910400003500541202c078040000780c000290b0f00481c0b450342607040010201c040d0b05c900c1c0850180740c0c2e0210007800129a5010000381030410350260208030512070302407501d2021161a907030f61003114000240850880603080c0086846035907200f103402d11500441d511800700400c00303032841c0c1007807a403440058403440c407030481030a2a001d41048038000b0b5405069204465950b58010728000b0071050250341e0100700881800281d04115000c0c40000d025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 276994667 1250 276993417 276993421
    0x15040f05070b0f09011e080a02250b1b031006201005060a050406030c15090929190302060d0b0406081e030406050f0708071b0512010204060203030412090e 68
    0x1108072184c00c09040709001c90f0041d802d81401800344551109081c01b20341d20645a81e4902280400940210313091003580427070a40f241009042c50008291858052041040705140000e51480750384484079900e0f00000d420300902c00c0d0002101541c6050b280380b414540c1000f20146510098200c001c89600a0b40c0301f200810307251070204e031744013900441c000da0381a010070746c0701e10a0100b6a6000c4c4001019901c4648040100b11001d140100c5800000d20f4002c04456440d030054080e594032000500c402c061882c203441401010b001000c00005090360800e11030510310914603900005c40c403019015000c001107001811207254094140c05070010010483d00c2e440e44401a40c03408900410051045401d0410011810010581d001c81e240d960340e603840e0120b80c032451595500f00300c0048480103000d010603400a40240703181c0241c0740d040351420f842c1c02d245c64100301c0110008550802c40b030344100003e000f8158044116330b88503800c2425107141c2031241804560f03080090344403010300c00004003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 276995917 1250 276994667 276994687
    0xf300213140402030106060e0105031303110615030115060806010c080903120403150b030d1215120c05190326040608040b01060e0f12010605060a0203120915040f05070b 74
    0x1c0d555000e5402540200042a03d038202918582c0d5942c8a003030101e40240001003c1d2800485000b41140c82032a001121036806850507150400a94040182d1115442300e0140c0341001d00c00c607440503c81c007030359440891a00c403024141100140c0210304001500e000300d810302400034201d40c4030000180449440340300980140c00c6a4000c0e02041740c00f241d101c3c45000a442c51402000c5070303684000c1c00b510b210001701c20203548800e600c030141d040741c40c0c40c0c0f0014241031310014040001005802241c2e4019481450b00b0400050950800c600c1540d2010518051030140d0004070300b83c951082a20079a00c20303242d120041240b416088502a282c0001c3c04034515500034550750050b4411f205240c4940d88880042e40c0d2544000c2d0100e0b004145845001610701c0c144021101080403040002142c80e100e07000b040307566000c80c080c5c0d0003603440080d180480b0071105424075801400780000d04900c0c1511100072140d08000b40000c3c0c2401c400ea413a030014040180010030080c1981001e8641e1854004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 276997167 1250 276995917 276995951
    0xb19171c0c17030907151101230f01080606040902180a02071e0206181f18080705030714010207210605010506070b0703051305060a02040f300213 64
    0x50001c80e103206194009440b00040442038a000e07042c040090011503046c122484071a40104400c4001c02581083d0181500340a00c100340ea504443c1c0d40e441c42944022111400500e00138141748003260320000104151100421019003000003180e0102d1801da450000900e41c2095144160800242d11300380011402254010300c00c5a200d120b50203256643c050312440661285600a5000345040003103422002d1140d103034041e0102c0051500109602e000c03801400d44030180c407c1c10101d001b0250362440284060340b0b9200034001c60004000107418580842d888030581d1155584030000e4004c2c001090307009001d0b48018260704800440813031f10480314505007000303060081e501545400f0001c11030b070809100700e401c51504010b81d0360702a120110200c0c01028018110988002d0081640001401c18000030b4003031360400d100941c07120308145d07030805809103651002106d0103041007111400c0c985002c00c0300c500e009000f05c1c840d58501c070b03001150310146401c440124481c5090b6070184040042 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 276998417 1250 276997167 276997187
    0x717090604031b0b0c13061103120a020c0f010e01052a0d021b0d030b040b090403140409060321020c0a0b070602160303020711011d04180803040b04060b19171c 70
    0x1904104500d5544040a41e031230781900c1244803a40d0001c10404100701c00b00e4808507000f00300c0312700040c03400030350504540c04c0c900302450100c150794454500500440c002d008080e008240b004007640c01b4004a01c01580c01511181e04840030140481c1c400c40d40c1c41207a040d140071840c5d070300c450078281e0318500d1b095031540c80303406440b07021a240c11550305107400d16209003008940c004e401032410f510396842c156038441119955180d9040104008a0210068020103000794404e008140341d4410030311600801085009410b0219444135600d020103564a034a103100b00c0d8080d800c03141d958211414031800ac1c0c802e00c02061840c2d007050a541003055490381c011320155000c0e140f006000301d00f0300011680b14100000103150801e2502d4600098609640600e5440031034507032070351030440d8a41e202c407403541003200c09680751341004040005210341c41c003449981c03c40846090fa0340d21150000c00b0003001107030241110050040011410042c0700f0840744002c083c2009000c8070034407441400600c0c0c4448 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 276999667 1250 276998417 276998437
    0x19140d02090f0f0106051e0903100c0314090a020a0506030c0c07120201110601050901090e0a29010602190303020a03140a0515040509030403080a02070b0408060717090604031b0b0c 79
    0x43d0900014070144564244c80940000c2481d201c01300c41c1d048885030058111244080d4940103400940b07454010900c80e0010301e07280c81d10081102001c425645082c40710050a44d4160b41100b9925401070b9180b02450702550700c1100c65030b0b2292100c8038007840300d000362424940c0034820742c01e012614808406040f05c0e01d80c400d91303404040b42030301d11956417121003c0c40b0303903034000040c0d10062208100710380200550420240840d400b8030943c0e1105000300b0395400301000a00401403194181120302200382c6c5c050401c900040069541500380c0c031030200180c4e0005410598041070440d241c910a802c40c0001420511807240c4078100402944000c04094400442002c442540318040b410b045c01490f101c0c6804001460905255807a5100700780d000807601e80c11405044008201540d81c1006040a40880d80042c02107150080e4081c255446600a07030020801e00b0042021465000480303d074003030340c1440c0910b1801107a00350410f000390310490040220003410b041286810b9000003074180414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 277000917 1250 276999667 276999691
    0x390f2105130507032402180f060c120a020c0105070308010b030c0d0509010b120c0603061201060b030a0204181406190b0a0201051006090b03150a050a030503030901060519140d02090f 80
    0xd00300380180d040740700e0340c0350a00005800001c007c65a00e000c40d101347c41080043c080da0300d45201011032605007421551248110315012030311210084c0e04000200c0e08070800c1c204a0700d0700c1c1c49501c0c0608400014403958900b158000300090f4044070080039030301201c1860000344407509000032a98064500f94510a010309400108070180e03845c000f40d6002d24000c0038100310301c2e6032101d8040c4a02022142c06880e06036480d2900001d1000e20301005511070340741c140e00142c4540c24681144100312081c520888180c1c10951040300c0240351030100b070740000c802c40d5a103101090030404c1d6180c0c40c04030760000740405000b143c0c04003801d806401c0548680c02229a840c20300307440700d0701901d099250380103140d10341c1e806100041443c00c5584504006d020010824954540c0e03840018801d441c10340c008075400d40003c401c0c46004a404d01030080500341c22560595003440f07540356541900303094881c0a15403805503014001ca80c40390fa0310b4880e8190050164016450558000b222540d42501d000800d80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 277002167 1250 277000917 277000973
    0x110322080f120906010501050a12180507030311010506092e0909170c060c07110306013312020a030902060d060f0e090a06390f210513050703 62
    0x43d50108034030f4141d4005850f101d05254014078125843c02184140003046582c1c4c40b0040079070841c40300e0b5485c14030f11500051815a0031071074010501c40c07445210302c141d030b0306020a10010303a58243c04580c0c0b1881c4d101d1040040000024012821000700e16405070700300025034080f42000503a080780c0e07403950190545020f13920104000e00c14a1240441c0000b03140c1140d80480c034501d5245009080d00c5004005000c0c400c0499400281001000c1c1d0210244541d869083c00c074862960b2a869000042101c40c5400d0100c040c2004e000c110340c51b2074810f0756581c00100042003d010754056560603402500103629104100c170070703200516080c0503450402c1504c0800044004504502078800c1e50f80780060004a4403a6851001911500c205201c600d60550a118502947d40a40d41039a020b0b0801c0c064201105010203002108419804001c00c000c2d080d110f8032141d000011007842c4013500000090a5031581c5ca42e03046220b110318010700318011b410001040c0700382c0e4010765680100a8552081803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 277003417 1250 277002167 277002181
    0x31b020106051516020d081903020901090909020a1710020c01090212070f0909060e030705010501030215071a07140f0901170105030a020103050403030b18010f0603110322080f12 78
    0x36004410003840130185078581c6034010b0401c3d15101c140c082c0304444003400d110b4034100d9201d9496481ca500c0c0b00096010540d0130056a00c2501c000003080e03802001c01c82200190003050b200546801009184220100224a4640108482103407049199421525120a401d030b19010f007125403030580c4030798803071803844082440c081424812100340082d032038000d070b00e0800d02c48003825011109403640b43e910b01032a98141d00078402810384910a40c000101396046204002c8004d4411926034004402449942c00180c800201d40300c00c12500c60030000641d5407241c0c215581031049101903c1d895000c0750902e40348194102030880000d00740c0f5204d000241d8040ea000101d2700074401e10303a25070b0121040740c0140d40030798800340c0c00c20300a143c045611070416000c900d2042d0b1907081141030300070351001080840800200d032805000c040c9010310078080020440c000d10700014040d48081c031072116951010030000c2d0102507400e90310400340b644600c00d8400c2d17802c641d004001c0624003101004009400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 277004667 1250 277003417 277003459
    0x3040801150e09152d0c0304060e190219050a03030903060b1e0f0d140a030201050a020f041a0403060f0606030506040b0307090f02071e021c030c030f031b02010605 72
    0x142c0034003600d45400d60f0329940452172071020100401c1203200c0d5102a603203059840103116200f600b03002d1440340d40f420245005001c4072101a0002502e41000042c2c0c880d015030125401507458040b0303074070780c07034804e990320301607101001ca80c065030f841100500c00000701900003c006003101d001d501c0802c0007100140074080e0941218030000300c00c801140c03e4040503d40140f817507044c21800790003110844080e035111048205010560301c40c0740e01612141041550900903039900c058120301c25420102c028110015a000e18043c9018076511411450a400309120a03a0021900b10380d09204460042001c00b004000714014480000c0c01c1c800024078604140c010840d444402400400c44a498044101d0041c510440401d080365001c00546012411400d8004920351000c011588444d48901c1008584100c12030703040b00391a17001c2080e0001c039030000c800311035003a01800c0c443c0b0b02c0180010228000e05030f601d040c6000405111039042140c8c0c2c158800415514280c4140841d1001c0c9016588 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 277005917 1250 277004667 277004683
    0x3010f09030810080a080f09030d050c010606181a0f19031409070603020c0c060d0b030d11030a03020313050f2d03181207090b04060906051c0503040801150e09 70
    0x9920fa00401c1a5070004d080fa41c0285141d50f50fa12090741032808c02c10019041c03120481e102d00c00a440442e0840300c00340b00b171285c50002c1c03c87d420b00306002d10507964440347c0400070b441900f4000010503800f000c88042d00003103840380381c080744a0039680c100c6030401c000300c03510280381030002038900207588450302c030212000c03405129008000d190303581c03600341c086000c2d500c402078a48040c02251009003090700c50402400d1100e06003100404d00c440c4103c1030602c0c100b0000313500010041400c1c840070b656000402200c4260301545005603883e40c4038640c003120894107200c003c00310310030300342c12026044010911700c1111012240c44000f14501e040000146c903940c44118115800070001181443d0046100d01c0f0214400380201264640e5588018149220765014009454481d40c65500e240360922410003c1e00c05920100021410600030805400d094110459141143c01800003442010000d4900400e0a1070091002e036512603000300b0b6100e120310031036151154030004070303a0721800803444107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 277007167 1250 277005917 277005929
    0x10f020a020405060f03191109061f05090607080306090106030203060f0d021302030124020a0f080d1d03040302011725050706020406090302030c01030615030b0f03010f09030810 78
    0x4200159020000241406880294880d400d4548043c07151420f0048817140200c075036101295070b0041c2010404c040449231405d10030311a04042040c180c0d194928000044400c000028142c1940c41c1c1c1540e1030300c1214207440e1701150226100d0101b10301c241c000c500c1a030058440c15240d0340c0e9100150240d01054540540c4a02045c01010150410705007240c6224001030030075100600b411505400c980c02070f001b945840201960320311017041c0c0d030f611715016000c50f80f009080c200070300c1c0c9800d0612881c450000700303c00000a80d5000c01c6d2880d4100241000f50725101c10021201c011840c1d42da82d0042c84121b01103a02107560b14210480003003a503224400b201d80228552084441c0400500f542c4095141881802e21111012910701e1001e003000d0601e5460b01d0859070708600406142c142c80f20b246504040c2452801d000b03d144840c92506101250308000c03940c4207440c40000d810481c00d00140b50150310b004100b109004450b0010041c450103920340c842c0d1612650f04102d01c4030003900440b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 277008417 1250 277007167 277007173
    0x3040b0f0a031a0a09020904060b030a06030203071706160c140708070e06060d090206071a0105210c19051c02010311040e0f19091407090e0714040219030911010f02 72
    0x8000303805c0284c000f402d01540007440054402e41f035840c120746981040c0e070104010740d42d449013403046040800021016141d4032600c11400c1c8600c04030715981e40401840c05240d20350185180401a0080240e082000d80c400c280c441c0c1c9032213256005580d04c6061107402c1e081c0c031070040e0000f00c81c4ca400400d10700852000d4000c2e49800110078030f4001038110040f0490300f10204002d440301080c089049100d003003c11803103a410079490581042090581078103032005034214083d00c00c3c02c001002411040300d0100780c80c01c0708400c403000100d4000c809141c3c071464008031101030b5a0b0015540109110045100740c030304001100c130f0b200681d01e4502841c0100c0110600c0c0b000424640e0001c80074140d4007403032100010203c10010340c58541920740c0c01004880f528041c2110012002040c0410009040b9545042000c07000c4080c00540d101140d205815044640152424541c2c1f11501103900c2e0244141614401c1030114000500a02d02c85105030340d08800f05c031481c84a58840d190781150035100c3c1d030007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 277009667 1250 277008417 277008419
    0x3150605070f050c0a080d0f1e0c03120f050a050c070201080109090c0306020f071109130807440a120b0a0312110601090506101103040b0f0a031a0a 65
    0x90032009442488161541d21501c800703012242e4918011710050456030300a00010401103201808680d01e000d580340038840c9070004840e00c804603512000240441d46400c0304284030768241601c0186039055410b03900380c10000301691803c2c10744c0005000c0c101c086030420159039540034200150045c2440240001d00f107200411850300c07240c11001f0014055504240c01a99036030f1800304903880f580c01c081c85500042041c60501a40449141040905079a0700300e076850410380040c0c0f04000704000412071500420900c0030b02c8094941c4203400c410900751b41204145140c2510800c030388000c0104004201d04480c16007006140382a5031070f0081c542c0b501c0d144c03071900740e46281c007400d199a001c07a08020403081c00400700340c07039004403455030300b954860800350000e481c0600d04100d41600070240c0142002c042c8035050f201c10000301c0c0e50802c580b402c08004884c0f80701c074504500c00c1e0f50204640d480041200d07404001504014045080c040e03e0400801e480e810801000c00f1007608966401044124 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 277010917 1250 277009667 277009673
    0x6070506040305032e18060e130809030607110d030905060a05040303020d0507030c030f18020108130c0e06400204050301290102150604020a0e0303190315060507 71
    0xb01a40d000800ea402601045c0d2600f03030050140b4055000640004045a20801c0742c2c100701401c40254083d1a00140811030810040300c05284014140a400b641600c84d010140080c00c02681d460700801000c0d500981010f45009007004406442c0302010300664004c070158a00910079000309690210241c103040e594030b407040006110040050342803503020802401201c0c02031280c288030b00080d89000079440200d86004048a0010744c02c05075952034621500d1105a1200032001c400341c2c2460000c04c6555101000a0740c0c01c0c04400003001c00c9040710300030551f10103c011440c81b503e802d645090300345202c840b503862116400b07101741c0000c0103000030310b4200d04032283c1c2c802d078507071080d010140c50143e645000c0382c00c45400e524840d111000209418407084040a10f4100c2c3c0b100910080020440d000903003408108050501882294000740000007a402001e042c60380c00001815652140340010417500c0c05201207890f070000070316100740c5040c0c50311002d68507015149140d85160400360301d50703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 277012167 1250 277010917 277010927
    0x6040b0a05060d05010f0f06080a080409091a04140d0903200102011b0804021201050c0414030c2805011806080c1b070602100506010503040609240c0e060705060403 72
    0x1900d0340d5084084200d10f24080b50003401500f04801030124006100f01c1c150f030380e5104486203900201d880790001e41d908000300704400d0a50b01035807031030f000003d0456020318020300e01c1c070340d01070fa41d21070076500f5001c01061040b0543c0011410080009464100d100d2000c110b840b1415408000c0600e85280b400e03410125102801620f150018000000c040802000c04911072003801c505000094007a400c00c0304506241002c07604495040009010508000c0900c1c4114002ca004003001102c520002800642e4104500189960094040c07600c0040488501002156401303400c010190700c0400080c1a5200d8842c1c11694404c07070713041300051410a0400c1798070352409031601c01c22440601c15042202c0c481ca861100410480008040c02450f09601034105035a0720f05500b0303100d02c0d00d4200700141c1d0300002103a602560240c400034501c00b451500d181c20100882c05200d00b40d40720303a0090745140840d4844100c400301d070b45a45884503c01d00c1000700d684542c08008200d60851404036002034010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 277013417 1250 277012167 277012171
    0xa020c0d050d0b04233315030c0a0c03050d020f030109050609040809040b042301170c3a060b0a09091a09150a060603050c09150a020c1e0901060206040b0a05 69
    0x4102d01e06c441c050490070b01e0042d000a034056440c0705c070a8413000507207844070600280700100081c540c2585000c84009840d800390058000c01d01010041410405110b0400c4400c0c1c0406070344110b4440c81023030b88400c12074000340107035110940b03807001003041450320013031042c0301c0c0d50b02c400e1162800e00e0000c280006801400c900e503030050b45403032505521421841204d0021a4125040019507261048440031501c0c4103c3ea02000d80000c00801d0b5581c40d54445011041da40c50b100d00403c00352034180c41c401e40e00303040c3d07109205511681041e04020315a00080c44002040b40c0800200d074441c520350040300c5008100034208050a9030380c0011000b0b49405075030128100d002d0b02c00141c0d44500800a0030720032107502960559440081c44042d4251040c2038010207008040c40c1407189490200f5050645c0c1040855200706c0400c0301403040b0b100f000740740c403c0440500050010303d20300c00d140006042607050288180008000404c0700ba10000340688200e8200b0880d500d603403599004038009085c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 277014667 1250 277013417 277013431
    0xf0e03060606161703060103180f11060f0a0f020c0307081506150406050706050f091e0709021b100c17060103060504110a0e060901170a020c0d050d0b0423 68
    0x120f091403030041910102c000460980b0245080ea9910f0018001011a10000e4218041141c200c1100d00400c1240b469081e4a84c0d0140e070308108080e40c1c00000301d135030080c00103080302e41c440016071001c0c0c944e01c260b0000b04e40d01d0395004c0311980c42c0050100358682c3c0e00e50245010560081c612600c0411000c4c00e81d50f001000078007010b494052680b10040298000e40102c0003107000084e400080059620941c1d41c400c003071810b981e4070341c200304101c9921810380000d60070b1000c1801d00d03541c40c0d0310814009040117181183c001c550f03e110000c418001c070364030755070218120301030064400b00d40380480c0141d2640a440d5502c0703000741c2030344580d20b81081c0030280c06281090f55a80020416486030310410361528240e813170064540b180000010000026880f00c5409554244904001660400c410901081c100c05001140742d44001c0c041c0f00a000d0741596403818401c1d410000c040540240040211501c1108107010100c0c0072014442503d07441c00b916001783c100303d50041c40760050240101c0e04070700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 277015917 1250 277014667 277014697
    0x3060609060301080618010c1413081f272301020409020324010e060c0111030403030213080601060e04050601210204170f0a17040314030a0f0e03060606 67
    0x3148001c100300da00240c100300300f1680b007201071021000781e42510850424000b0000c2c00200c182c0c40005068a250600300c01004c40042600401c1c804581e40f01c2016101102c100d509072903400071041c84410710074003e80c07000c030f1408280b41620102c0e185031a00503a840440d0b009210300c5659100411195044005200b204c1c0f10b0359000595800c1c00148001c2c800e2070405a10fa0412100701f8a1401213215000e4101c10b08911001d40d070398008902c445034110488040c4c1c0c031007c042e40c2c1c01d4050503408464480c00030703000082004158041d40a401030500d031003050b400300c0340c4614890341c0e21002801a800480d8000d00511040e14103a001503038480e006141c02003645000030380f0001c42c0d25541640310459500840d050101119480c0e010180c42c480c00d00400c01402803000c1c01e910f46200e240b02414031a00b408010410f8500031003154021640708240396032400807550040d84982121418600060506449007110b5114070105005604010041e20030340d00ea100411289522600e03051600c42 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 277017167 1250 277015917 277015927
    0x30b060a0b0c060105040608010902090f0916030b090d020a0f0209040c12060b040c050a080c07050f16242007120515072d0e1c05060a060b0d02030606 66
    0x1e0710103001e040302503540001807050b541000c04100c19541d06400c0320030f80d0f81c9041c1448000d66034003031086c2d82108900004202c6078642a022504103208111407007070124842000100f00a05210414403415810007512503c402c0004100e0710791114000c080c04605034425000c000d8a407103010990414412108400415651241c0d0000182e1000c001e80e5226514184101c060400c0d003d08070b040f06051034421328007070700703542e02400242c4040e100501a803000300b448000c0110420102c0e002030209000c5030052110034040000768034280c00703140458990035264140d40c544504052002880c1c90700d512040c0409010031606002c11403454100d103100d204000a418110045142c1000b400f51000c1d2000c03040d91000381c42c1e0f084014108904101c03610003a580030300490720105040d4000b0103165075044240960854135508001d5496501219100288001c2100102c455402c1c5200f601500d1040e80c8507142542181c1c041d10944094080401544030070901e55030080d81c0c086401042c0a0502c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 277018417 1250 277017167 277017179
    0x504120305131e0303050a02030907141c080d0e03040311060a020a0c170c0d030203040303050a05091903200a09241502070b04060f0804062901030b04060807030b060a 73
    0x44040030a0f0312410040700e102c0038981c2c9801010380c130540404044d491410290070031691101180302d14007052510141d50032035941d030305000b80110081d0480052032100542040d218992004481c41609440e00da08044902740c080203550880e0703001102c0d4001c2c40c19070410710001e40d1045138884e00714080c2e941107600141c01e4540c41c40203007401001c8508802e0310022345501c2d001c8804001485080d22510722000294004119815650700d440d1a6480780c0309080283c6450040440c49984084c00251940603415504810f00407207000300b14005013000c1040c025010700b0048000c07184c0044000d041401401c0450700a43c03100e40e008101c00c1c6038040e0302820f106a080301030300000101c1043c480191441035041154002804000e0001440c2c03500e03020000e41110240a0305000b8030400a0000d010b002c000d9211035200c5094203046100880c1c40c21030311078240c100f0b400050100c0c0c41c1c03d007001600e080c244510381c00e458100004000541c2143c42d109a24440103109690080501401082d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 277019667 1250 277018417 277018433
    0x70b040501232505040e090d090e0609150a03084003111201090302010b090705041202061602030a060c1b080d050c0d06060c020405060301050412030513 67
    0x12503030052000040018101c0d2180d0140c010048012880ca91501e050000c40d012250003010390300361800051041c001008002d65a42c092507100005828500003000140180425400e486581503a40c0910742a00c0704070724a40d82001f03413801d607001182140042e691107241124400d030064010038848140f0b60300c1d40e98404a6000ba01d10781460801d420380b9200c0c0f155110b480c0e90b501c04030012440340e0b02c800225685641c80c010302c400b0344400c262001026442d1189007405072800c44000091191202505010340a0600e400740c9900901d01d11001030601880707001501c05943c0051030260700c0007101c2c4c0801c01e180d0000001400f050207054503000040c0e500304456076034988292401700380003201ca03202500401002c8000310b00316080c2c2e205800001c10040072107041c0d000c003501c0002e0315210008400028000d41c07000b018001d160401c007180780c0c0d4108080c000f01d01e02c2242c080c412039075100c3c249803d070345041e107004002008242c0392050700360282e01301075445400705084008801c074544a1602c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 277020917 1250 277019667 277019671
    0x106080d05091e01020604080307170106030912052109100915061202010e1212041e17070302100e0316060807030b01020712020637090305060708060303070b 69
    0x1020a01c0042d0307046180c1000c1180c011400900c01c005144012a0350001c0d49803039008000500c1c8010000010305224000c0614114016460151030041d40c0c40d110060001c00404006503825117105c8114035000e0311903012151401e00654549a095900001c0d120403d80d0141c081c5901d409079030f0081c04441d007148280040f041c0a0b50b180242c02070380c100000b0460300a0740003c614050302601c0d150150340c0012008074802c00580b41a100c0d070f0f00816040b41440145485107468090001e400103030b0162160388062900314804030b1224240c2d171a104864184100110b02d42203030804d100070405850811400b068044090030219200e00180f00000e0400d0070300c20410168001c0030b107090041660008046500143e10b0604000a000c54030000c0e64980d1603102d80a0720300d98007103100b001c540760b4400351018456903d4408212406c400082c0e06071400c0c210042c09244240d038000b919a80c030400c1038100322034104020b000e09482c2c5507000c40729448010105605407004011500011740600ca5842c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 277022167 1250 277020917 277020943
    0x4051015052802010617060c04030b070509030607020105060f030715050c070b04030503030403030b060903060103140a050102030a05060117010e160c200901050a0506030115110601080607030c0f05070212010608 92
    0x9111790802020401410840e00403243e158031100822501c1c0382d000c41110240c0750066001011661014002c841610409100d0368041c003c0c0c0042c049141d405400542c0640f00c00c444e9103051108140505546400501c20300c400054010f1003a041c26006400400b13802105a040c2d407251515401e107403400703030f100d0ba20884456000008000074543d252003040c3c14640215150381c6800b03050b40000360b075120180400b0348126110840c090081c0010409611010b501000a40d140d140c04883d030001004c08560250100da44c0907610740d40030004440041c1654a480004c040f55210b41d00d056071034211010300750061144400390000030540e8501d0703d071452001c051006c115001c00d1000d20a0410040e0700182c00f44400742d4080c00680d41f503405a82c103442040b1104001c048209804441000d4000c4232586540550170022034201c0c00454042d105d44e06d01c3c2c07828040143c8060007103882609040240c000142c0501110300140390000707024613a110440c0011800c1902c0b56003180c240b802c528441 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 277023417 1250 277022167 277022171
    0x9061b020a0309050d0809010e1309110f191401021504050627070b032a071a0112080a12051807050d050d0c1707060b0405101505280201 60
    0x401c0806034001194000f070141521200751400c425515400c0c1c80c002d0003e240e040c021000d030071b0342d002c3c2c55111080343d07143c4e1031940c28460000a401e004d40682001301c803184c040c2c8405541c60816050180c098000000c002c070301d00146c1840d00500d50030704c62101583c3c034118042c02090706028480205103500540c00b13080502454188010440c0d42440500c001126000b14a09201c02040010401c0c13030458a100101d1560307076a40745410082c01a109215481596120003000e80212071480604109441550290422614103021650100c401d02c16460244203000c82c2c80c0c0080c03502405040c030a541c500300b0540d03810b49440b4103010f5070011a0245000f0706c00a003c024040b800704030201c005c2900707075940307091700c501c548407940c0310602080c6400500ac1009101010800162140d00300700b080307175000d10307100c02c070700c1c80c003080942241c102c0b46101d141014082101c0d8580c2100c1e800484080401c0d004040c0310f80003040e038058002e14440c3c101d91100d140903035004109209402c0c1e142d443c603400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 277024667 1250 277023417 277023433
    0x1060e100908100204061b08040b181206190b06070f11030f010e0c090f0a05220f020405012103030e07091406090702030406080703090f02040c110f010c080a09061b02 73
    0x100401515a0b03d418071102d00544a0302000706005102725819561400d181980c0d50350200e0310700c120400f4500c40c1d15001004003203615050702010179424010710003410401d08900303e10159a00b0380d510307403560036445802000840001801c041c85500ca20b803042a49140350140300703001901344029000802c05070394454a110624081c284400c068040d41203510b6011410600c8a103011650024900810036035900c011540c1e2039425090b1003603483c0f1440418410004a1504c0c81c030b61960b811080340100d042000103d1a0503c81425400c200c1034280c031043c2044164404501800000d0700004003401945408290440180261002c0458908002015003403910602045080060800c41190021700c000d10040d6444911300341c0180d050302d0089410b001d5410034001301140d08a000758050306c1c0c02840e0703090613084081d2002100380c0ea02900e9204068041c0103003600e4000141100181541c00060010840741d401488200d0040e000001e644c961002100c04064031a20301c1c5000d60b0114007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 277025917 1250 277024667 277024679
    0xa18050c0103050a020a05030f0603030f0a020f0601050105160b270a1209060815130513030906030213051302040306230703060b0d0f0b04022b0501060e100908100204 73
    0x4154004001404c11450282101e0300180240809888034034690540c4010582a0b174040098401c820409484295511001c4201071b42d00c3c808260380e94807a01454000044540c0500c06480c0803a40c0c0e0700c500020101d803603449403500c150040c03807503140007050300f15410100c00c1c035100c0c80e6005038128010030144440b82010008400e2428490040180e201808d211040e449840942c02c02d1060340c00c0300104501130700280d0034642600d4542c50b00c078502400c008100c440c001010340030318000e0701e030340b40c0c034a44601048007a442504140340701d0b000886005c12a03403c0c00400c0407005243c68a00600b003a4403655504240c40b011a00c440d100382c80641c51183c0403001c2004280c2210003800e040100601e0001414000d000d4010000a216650071041440c60720907084001402c1006008540d160341044418042078298441c200d8121100c0f0f0f000407000c281441028181e400035104c0702c40c408101002c2184a4004909070b104110f440a00042c032148200120254089210030141e1141e003010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 277027167 1250 277025917 277025921
    0x403111e0a03080604020705030405091503060a1b0903050304060c050a05030a02030403031215061b120f020714091b04090203040f02042a050d1d0303041704060f080a18050c0103 78
    0x3c0d004c2e1340b040e4410030032013000480008c1214200e03074041d0340c85443ca5498403410100b01140c40c11190301800b03181d01300800005954044c4848107403401d07003c0200c4403c16402c6501d90318501004001d50b10410051040c14044c91200034020b1040d4110b95105215644041c01d6810040d407402c0560300c00302c2e0600c10550000f000b04510b034840740c002c210705d200f0180c281e0701711030851007000113228945416902080701038004580b03454000e580004100c40300303039000304110341600310000103006142d0045890b503030140c603410000d100100081c5190302c440318000c000c1c41001040b02c00102d820040040c02c02003034005035204034000d402d554510b440c0c500601003074803a042884c55400c034500400740d00c020040c0324080d0f078840c59850200e031034400c0c000034040141030072812094410702c00041c4d020242400401144214400d0f01c102d603102c040f2000c0c01031540078038052000803805208120100d28403c900c103a901101c22034011910740101c102d0b4040102c1712060942c0d003a0800007510145503094 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 277028417 1250 277027167 277027171
    0x6061b01021806120c0a03060e1501020d02030a090b0313050d02010207030915020a110a0b180f010f05030703050403092409050f06090d080d141f0501080403111e0a0308 74
    0x140c2c2c07410300e4401c0607100c0c1850813400810f4030202c400c02048100d250340c0b0a41c0a0740c00381030b1b82c80d4014081d0030b00300c070000c4110708140b0840c0d005214909103140c4091003c8151a951505078640d804441e0a0120560300d41c1c1000b03000e0007200102c1043d100201da0104103c60042441c0c0d00016500c0d55181001802428190840c6a1042e404040a00760f10750004280170300c0f80e00484280701c1d12074101c0000705010710760380c401d600080b8003040e03250350012080c3c13030344020102c102c1d103032142100100b0054030054100710240d40400e0051000400b414069000309071b10902c00d02e04002003d458014420107091103148015001e10400841840281c009a5810103030608656105e590799400b00059518403c0c402841d019041080c166000c1054031410b484085804120070b110001c40901201800c0e03100f1600846030000211061081c100d458041c0000c1d9401a51001c9095680392000e850240c1503c14403c2c0741e100300d140d010712400100010790f80c1020300c070014041c26203030790500800e14400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 277029667 1250 277028417 277028419
    0xc170a090f050307150804020d0b0c0d0b090c040302010c060603050d05030f0f01081903050c0d050910080402132a02030307030b040b0a0504050603030d02041e09050601020d0806061b010218 83
    0x10b64017408080c648140b034030060301181c0303801ca0f00e55507148081410043e00000080255041038140300360101c124020303002e041c42c00103003042802e003c0002c000c8400015102c1c80c2401000b008144095403144469503171081c09210003280c0c15075642d0b01e4515004042d400e035000a5000310900c0f00c20700c2000f80071900200d452059042d25410080319039111032184032203084c25143c0840d04020107001c0c40664034102903030401d45144503600600a0100d41c04944031707611901090300e4001c000c5000d0030220340201d401621030700c600c60084545200400a100460601c0b06822800494558a80301a940c6031300d8541d01850300c0303007418180541034400c1e40032500e1040c0c0c02c125903642191107000c008801c4490449000c5403648464021074194807490004000007400018042100e45164140c135401b814080c83c2140c40660300c02d102000c5490640e44580160014058040e496124000380ca4010344010f003801d14001a890a1400d010b5002140607540d03500403545100c203c607030001c802c4141c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 277030917 1250 277029667 277029673
    0x209100305070e060a14131703071203050a0929010f080c040510170d0e0604060c17040b070609170307050415020307080409090501050c041202010c170a090f0503 71
    0x10600c001400c040b1a810000d40980c3c40885c0f004680b0703101e0000f003034900f01c104800d66030b68085100750416200060003080034080101200640b64800002150b001a4102d0010000741d07041c41011030242070701603e410320080d11409104045040c40a100b8a00d43d441c3c0c3c00700e035420b80d000100c8844010168070602d08d90180c020100030405d400305850911540445d40054039039266242040d4a0055400c07000340301d038100d040190041e40018544038540b84640345c002c10120890200602ca01c920b009440008400d003203100006003a101c0c480120176440001541841d0701c0c2c070003400e4a60003004040e03030150703203a99010040c0b00007400d40f5603004c004504000e207107140c5501c028016210314420101000003400301012000d100340241c521495110103015600d554070703100c0d2409040c0205c5c090720300b9440d007004195803503003210807501101c160389041c5414445907001035840552515055800800c0d20480000c2003c6c1040203007000561600d84e420418100400d0711562412178100c940031354 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 277032167 1250 277030917 277030921
    0x201120c0207051c050d08040501050a05011206020901091a041a040305030906180a03030f0f09050f040b040b0405010e04120e0906040e030706090c1701060b1801050705030304060209100305 83
    0x140e0102e60031081c0c80f0152500303460308030030180315040020b000304094464064020a0303002c1aa0001d540c6000c5d9020700028001a11000351180443d402032090030200750320710301c000f000101190044c01005405050000485a98180101400b03407803002e4517414503c001420301000f402e4000442c001200c40036414241800d540d1210755074440c017881144109000324200f000f85640c4080364000c80300c0030b00190400350341e03803030050b15400040d0492808030b9a003c0403103c3c1280719004080440c0e00040040300e95503545414840100460300c907094000b41c460007090b4150301e4600901d4001c0c10349022821581c500b6090000481441115a03800c104541500019030782d1030740e00079034111104590015070391344107404091852141030760052076141013411450501c40300701c00070812a0407491042001c8560807101900b01d8a280c020640040028002c000a0142071f216800c825441818050300d080079036101d041c55a00112011208680c00041c41d6007a810161950101a1410305043c4098 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 277033417 1250 277032167 277032191
    0xb09041116081c0207060903030c0809070302060a02150411030708060c030a18050d120c020a0f1b030c030809150301051806060f04060c051c120b060f0307020a020112 73
    0x5107410005824041c0c08200d200540000001110701d0003c1e0701e5007196200902e244c40400351002c80c2c41030b00401c0c9071170100c103825409880402c1c4107101800183c40c2881c1582d0822869030081903280b030071441040c0034498240d120105990240e030040140c3c511040300328040501c2e24040f50800c030b9281d04008140aa43d508400540740c04c421190000300d03010424140103d4040340000e0003404a108400032070320a00d801c135403110b06d00c1044040602c4002c0200c0020b90741d40114990041a040c80d180c0c20901103804c40c9001544c41090000365a0300710361b01d8583c20311212854000b6100c044001420004034501600c150350356040d1426040c6c11985058005007018044074110035401d0411030024019598243c00c440c800750505030700588a41d00e8620041171084098011512842a2860b288825140950758801c1e081d56607074400c05c0420140a08000d40f588040040d0043c01c140b000107450041c2c5400b44d480f481c05070b4014030585403140001010440e10710840d0802601d41101400f01b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 277034667 1250 277033417 277033447
    0xf06010b0903120703020a0804180f05060d03120b0a23011b20091906081603021903080d0e0105070315060c0305130e07080717011a12010b090411 64
    0x52514040e043c151115890b0400f6810081c0c01c200c02003040340001404a2124144c06200d230b2909242c0000700a0805450000d408039041501c150b41e210034020a0700001030300c2050700801c1c5822003070010400f5017401c0042801c092050304101040900b89000d00c40c0f418a807a0101400e0509182440c11503c1141c24405850f11548001d061902c2404892524251041100702d00340c4001e8a5048145420751079100d640e80c3c4d5500550071340381002c03000175140d800003608118401030040a00025403a42d820403c2840c001c0740040304003114030078000007042c1d89002518040c5080750340841c0444900d03c5407400c5520080000c0305140c07402c0c10600c0a0f018a13000d10b025551103040012400501d81011b5985001e03078046819030b680d034180d002c145000c1881d2550b005610a484000480e01d43c076801742c0d0707580c540200502c4c0310085480104528020103881c0344412603100025441c200d420102c000643c0c400346c2060010180002c1c945146080a124102a094051002e82e040c011a40848070b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 277035917 1250 277034667 277034683
    0x3061b03040201031d0703120e0a030b0c0304050a1208040b01050d030f0e0103091b0f0b04030b0c180d200109080304090902060c0f070515030702030a030e010e0703050f06010b0903 79
    0x10401d1780e60100d00b0501c480d08080e0304c00c05102282101c0180d541e80c40c2040104c030034003100c0b90000300079030900c0c04c90342424a0020300f0390303500c40781d05842c5903162002c2c1305198200030320603141c0380310341a145408a2052640c2164801c840c0c0d40c0e82d21140742c242403503404200181c0c03245000c0c0c1e0880c00040c0c0272a9026804440b03841d240c2c68820409649000124040d01d2205070103015112000d043c12040301050042d20304a9446c8031502c01c0a541d680d0324481d66004502c80980100307510400104071200108c002c0070079419070400c1c040381821072004110b01700a100421a2038810810b005d41c0c180c3c9018101c010090400d113071104205080900d0291240103521a09401c1a10349141c44215940c4d50f0907941c2c007858041c02c07034a1120b030845035190780380c00520415000382c00a66241444030070341c10449226030055001545401c4181004400600c40d0041c280e10a542c2d071200f0705020803080c010034000b180980014208071079a02680c81c103040045e071014541d01010070842c00c098030003040c028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 277037167 1250 277035917 277035919
    0x610050307050901321c0b01090b03060411040b03060307080f0703030c08070807032003070b0f07090b04080a060b120a0219080105180d020a051b0402040302040e03070203061b030402 80
    0x43c600d802d1404840c18030408410801c21071704040c00c0070120280b00d9805080e407000c0282c050101d05044801d890102c504d00c1e008903001403d00c0d002884521000070055402140203807002030300c1e5224640004850704550400541d6401c004103000d80740c0b508203c00c0b40035020080103000302c0550007104503542d042d1884000c1c107000202c004c110a0000c0d90041e0348510385c00032441070307031030340286402080707250a42c1101c11504002c0e0200142001c00200703445080b40e0150071082541c17145291104c03040f50040c242010040441c5000c031b240300f004005000100600001041c0114103450900151902d000000d8000d140807000149010400078410f1541d9405070b072581d400307800000d07040a108a0b5600141e20540c280010b000c00000c580c18002d00c03000003e001d480190160304022030b241c070611100030701641d010143c4954840303e80b407001080c000f0020401803520380e50354049020f451280004040c00e800110780042541001e21a680c1e210100496614500012010548150101610207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 277038417 1250 277037167 277037177
    0x1e02060c0913091202060103020a060c1a150d050c040b010813080c03070803091b06120f0a0e0f0123010b071b090509100606021612060b13050610050307050901 70
    0x82c0b2180700264083c4084980142c1c3c50241d0030000e60000e965024203100480c05201c811000203482486003040c01407131a0f00c20741082c0800000e10034246681c8018040d0b4141d040c45e1102d0404656580c0844204184691701405041a251040104a070441103250f81404601001c0102840716503205180c41355010310303107503140c912145100e132a40c000d4540040407034500006008448400003a021700c0400403248005045020f0414058540141c890030ba03921122403021a00075411440c0c000d50010ba00d11000a80b4000b00b103815141061801782c15019942d114024286a188101b05000740c0056030320301c0c1903a514203640d100c0c85214503080036141d400f1012202c822410700c556032100601540b0790900050900c134140c0ea8582c2001403901903064030302807000541d00d0020458400401400c51024041c9191201c1d0420b01034210004503981035443d00700b4152036440140c1502c640307092a00004480c07404105200907003041142020902c04244200f00a00f5403000845040740001c1c600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 277039667 1250 277038417 277038439
    0x1b1e01050907140402030a0924110a052b0213080c040e0a0305030402042009090a15030213021b03030109061409040320120a020c0d02030726010c1e02060c09 69
    0x210b07500030300130080000d00100058001c00c4180011271548602c4100c00d410400858420030f0f24001e10f1320038600e20901040f018091580c1c80501444510106200440c40151440058560008a80c442d030411544009401024400224104801400c10310305940400030003d00316046681c550b080c020080401200000280844d1070b0fa401035044141e643c1c841031645010710f04086820382001d00c6160103a07080c2c400040702c955050158000001801100441d030034159000e001c0c820840c51070184009400708000c00007000404c481d050102e4914000d19220b504156500c019075205911480300a8000811381809950f10002142c116905040a800141c5040300003501644408840b01e240d014040092941d00c0810b0010180c3c02026401e859500107200b0802c5487c1c01d520074042e40590000506008400d1580b83c44004510090f40512500030540540e07403d480305030340e2410010340d001450749200664809030000c0320343d5a00152500785080d2406508a008445085204066120b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 277040917 1250 277039667 277039681
    0x2b0302040b13060f031505100e09010303080615030103050706030c0e0904120e09040f030e031515010801080d08060112021e03010e1303080403051b1e0105090714040203 74
    0x411200100001c03081c030341d1545006050000d0745000d038803900b004990495421107030540300384038410088070f20001d581d035600c2c02c0c0010301c51011301e843c5000003403219040c0300600b10756030300d65914006d610a58a04110341307019014082d82c100da0b007126510007082440144001400030031800251012807400040b480388944088490446050403160040403220a0000f4040d8103801c0307100c2a0019110001c10008080500504080846018140d107880024290001e445141d6411401c10020101d44481111040700f007103284007690507482003600b242c0c8030041c958101040d1801000c45170003405240070250350282c2242402000e00c1d0402402c0c80d0740c850001583da054505107049054504001002c80c81d00895079482030240040a46800001030442481d54140340300c016415901d0880303d489558082e10950840b04a0701d082c0d0b040340e02c600410380010420903103140000e0345440e00100b00c0790083c608503075001d0090b00440c0c00c246801c0c00400c1551165905040095500517904d42c0c40703e13 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 277042167 1250 277040917 277040921
    0x20904030e0603070306080706020d022d0d0207060e010503131407091107061a0d030507020a05060d0515030601061b0c080a08040801060905012303070305030c030711032b03 76
    0x2500385a40b024022050104559260f0702140950b8508407c6032101c64076210240da54500c1002c541d00180d0110803e151442c00d1401103524004507400c0103410340c034513440841d0404281c0d00000c001603000c54004c1010a502003030f407419504081c01c100c0e1a600300590b00d010320a000e454050280000760360101d840031010003000f0010125100c04100c506904412074039a90710045050304d030f007400c01e4040494422001c8000c816a0001400d800f40122940c0d01038549400c811400c2e81d0221408500054507102c1d000200b58425410b80001058070300088094114460422403900070b600c04401409a40d80000c056280d91200e02000c3d460740d00c55141076410804560004039039401030b10901020801d51b40b000d40b041d225004002e21030035844121160071175100348a20850610a64080000c0d507003000b1102c160007001805440d00c9545a40f075203440c50b4002504a10b499100080000074888940641c1001c101304802030716407039065400c1c24020000f401010b0301409600303c02800c080e402a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 277043417 1250 277042167 277042187
    0x2309090c0306071106061512090a08040306060e0a0902030601260114010315110703051b12040911071205090a0e0108060106110607170604140103080903010b01080c0702090403 77
    0x202101d00b58034040030001d000c01c030110700044080c03240c00003141c520307e80062100780d00300c84030b200c40d4103024070048400d42c1014041c1c11b0f0304040c01540c000d100402c0241000700003840c05003c0c0400c4440c5001403510220000030040701030149464032010040c0e9003c074a45044800d2100d4072583c1c4480742d81c005082c4071680906034069841d1050074102d40056000181c1240d000e2140c1103281034000c50b1500c15070b89580e00111f81c00703000300401d00008c0c0c040d0028207001a058048010510000c041300340c030300410790022404e1481e000c03504001005a82c00303103481e01c6920441450410070956621031500c3c18a581202c140040802c5003545600e4482c089001040d6810369080c8559590f609252a81c20070b016400c005030300c40d03440000710b1000140c01800348803035689a00b804801400e0078000341501030300d07255000d600c41000c00d07090048288454060340c0205104c40d0b0b00d210302d808140c2100d0302c0d028202d052081c0c060401852034200d409660241380c040e02d119075556107501d000c41d400d00300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 277044667 1250 277043417 277043419
    0x1011090405011202010305070f02061b04180e0c0f13020c160b0712030504021f031517010e0724021009110f032a1c0f0b012309090c 58
    0x380800008260045036420f81c1114000e8808021940341c40104075140d0301c0201c00d02000d6070100011802d240040b6007040032404541c1c103e582031580b202040c00211f03030000d03d80035040c2c2c3c171405108100301d01480600d181a4044540300305880c01e080100b110300d00031b101031200d05580030031100f280c1c0400b0300902100401c010326031a030180e1903a01c0401e00ea00301200940e036000e01c03031038003c09580c042d10419011300c0c1c00a0412070702071000700340d42400380040100d40b000c046e140c41039040c114000302c6140340a044151018107001c0d80c0d03681541c0c00c6400c061110035140e80458001c20200b00d03002c05020041000703810a04c80404d0040040e86003000c040c5010000a14000710f010501c002ca00045005100884100706000900d00400d40e45458140000c841c4001c1290480340044140f00c185c0150f1078060f00c10207050b445000450a03d0b48100d4080c0c50003c21b0412581c20064040c2429024000d0107190554000c040070b150015a10b00301c9010340600740c21780204240303c8007045882034040c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 277045917 1250 277044667 277044671
    0x1093602030109030c11030303040f060b12061008010e0705060f07080705060c070203100e030a031d06040506040b070f090614130f06030b010e0f041d01020a030507080106020f10110904 81
    0x113843e006114a00c40101135801d081c6514144595203130100841e40201d41100140011314082e07203840c0000c19000130380d2940315101c0520b030b0481e00011701c070191040b065580d0252440b0310303100b149401e5441c802040d0015820269051250f9a6502e0607100925290f0714440c0d12449280303005d400034421454003620394820070040090b0500007500030402c01c0d100360161848160088c0550303068600d40c6507001080e42041c09140f20013882503110110f80e0030002c18020010900c083c03442d04103681030314140e035260403040c07c21040c840070040c41c90f0001d40700e141200f1070203002c4000905105c22401034200300705203034030346100c12032804058400d80305414192480850381d45165400c0400e15204240200b4213004111440f5070103481840865003004e00b4030201c10340d0302000c10000f45900302502158089594800004e54406d202602a98a203034800054a0504034400303062141e050340700400f10341c041141c11501c2500400ca00000002172400422807800300701103d00c2a00840ea00b2541042c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 277047167 1250 277045917 277045931
    0x40c171f0606090503030c0d11030702040515010807140403080d060b0307090905130f06020c0703080307030603111512070323041b030b0c0c031b0114010936020301 72
    0x9009680700c081140d00c40e032074110900795640281501e0740601c54941407980c000c0b034034441489011310725650f80e01d2040300581e40340c0000350b4001811240c06445503200000140780c0128a035030026840740d040203135400c06900541c0039105200c0d451040d8040280f20001c04901c50301120701d203410600180031480380190301c0c1c1c503110070300400350041071289070328150070b08000c9200c9500c1115500c0080343c201c6040d8441c2841c9440e004003a6101c00040c481c14800c00c00000003191a000c0914041c041c182d5010801514500340b480008802030421845004040e0710510002104c0c011a12643c50080d004241a0b440e4001540209210015200403d0341c0b071402e110791a0b0b590901c90710840c4644c500d4407908602601c01004c003415800300503c0607c06a01294005e0f43c50000f90040028020407245007803454024a03403400b80085912056030344a17409407024403801d02086000d86410721040052002d00b0508152207140400700700344c42407450b100d1000c203c200007040d6080c039402400030300c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 277048417 1250 277047167 277047223
    0x20d03020a06050f010b2205060f130e0c070b060d02090106110708030901020d1202090a0905010303020f010b06090409031b0b0601020f0705010c0803061c11011403040c17 75
    0x2940c4400701103410514110000f09001d0f900b41e40941078038817407075041e41062820204d02444d581941d043c880b2084519100142643e40e2100406003045007aa581c0d07100c80c1c81406181303c2c500b03a6000301260360000b80810441c0000e050a5506164100c2c40c0c0f40001c5d10351a0100d6460308414101039002043d40c00007040b130b190004610f0441014803411a40c215980b010342030b1712801810016401a0000304103180300512640d540c90103070a103aa8010719008801d8000354001d602c2e07034043c014440d00c03800100309268040c40700c0303004052210001d10800840c000041c10511542200c0c2d4407482ea02c4880f2000e040c400c0b8501c000a090090500c5440106800d0441c1044000c4840c02d005100e80b50301c8400222001c1203103000c44a0607111040a0508c42d912507015420041503182c2000000c203a0840a1742450403d100307107401101c1000782401a0000100072428220006200013810814440010100411401103441e05c0e19001841103501e40d5840c00c000342c10305007920113a20305040c1d100c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 277049667 1250 277048417 277048423
    0x11d040b030607021c11190c0e0a1a01180b0a0e090a060510110d050a030e0d08090c011d060306010219050105070e0a0e060d1713140609061603050403020d0302 70
    0x1003040101080445d01d14510485500d520315a90800a400c40f900c017103680d040c0706051000291142c6001041035031104800e4000c00001c44e00d0492007601d55000d00026a80c26030201011502840e22040d00b403150b030011180f00340c8510034541c468400250030b450721845016036802030f2000411415082c2013180c0844007030300040c029684515441c80d084210305005030560060b2070a40d0010302134850081c44250740c82d8114031002010715441c1c0d207000503469020b001004c1e0400c01034840d20f0b4141807018406143c0130403950464144514071040c640e030360420810780d00220301c0403600345550f991110f0040381041951076010008080300c02400c1c081100642145e8811012030f99a00302940b02c800802070905000c0c418038031065601ca0209807141420300c0d840a4040c041c41400b40d510034403010303a1400c0c4d84010450030003182003031014442842d00b80d0001740c51440880e409403c12048000090261080889204a8000305d8000c0f0007094040e9094a000b181c0081c040c1c84038162900303000e51 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 277050917 1250 277049667 277049683
    0x1608040f0602160609110607120f020a0f03110f01020309071e0527090a1104180c08070e06120312070c12050408060601030e070b0a0203040e010f0302030d030902011d040b03060702 79
    0x140131002420b0141c46d508155046d00c8496030401c000c1514017142d0703c400d4030111080001c0001310b0194001c9030b00840c10707164003546624403954402c8511071030181201d0600d00025901c1146034010030611195540004112040d00c4024564081080e0354090545005006030301440c0c1003600d019149102c0c01c2c145518180a2564603032480c5280d455882458135080300040c01004240d900c074580900f8141035104003458561315101d100000360359201d003100d0390520317407180207903600021007030051071203112000b60460410780e0302103050020f040351651203009a5801c1c000029211000800e1903110300a14100641c100c1a03181c080002520000c10980c42401115014850080030400c10b5103e44284124485403c0c041d080003030810890101d140e008690410440c40305004c007107070556440381503030700034900501209541031540c41410f0401400c074841d07005051410300b40d1030240c0d811078400c0400031100c48a08005024290008004113034144201d601881340500f009190350300003514070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 277052167 1250 277050917 277050923
    0xc030615020a141212060d020409080c0d0e13110d24051f0e040b120604050c010c0309050922061410080c060904060e07090504051608040f0602160609 66
    0x620074040140c05540c4c0d64807040959400c00402c010506002d5a00808180c01110060110019050315000101510414203040c1d501e48400115170700c9142e410800b85070a0003050030b2100004010704c00003003102454060000c02c0c01d844403600540c40e00740c20304540c1c0d0701d0f05145040103e56820217a1a5100700d001100082c0d1342d598000c080760303901e0101c00400d00d0038807040c10922a060700e20011540725801c1c0240da90800e444046650706541e6001d01200740c1010702c4014403403482e180c105246044071200c900b07410b01041018031004030340e02090850030b07070350103445445183e140c080880048074080300c410302c8407600c248030305020059181c00c8158569075141c1115101c1c2c5a402c8914560340c500e120b945c016600440c001c1123a82020ba003d004031900c01400014140d98030500342550b007400704c4051000540b10fa1046c0b1844c50284034941d0041c0030000304411149e212400500828005403010f444000b10041400070056107804580c8400700c4046280000c000914112014103a81d02080b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 277053417 1250 277052167 277052183
    0x803090303090c010302040b071518060209030124061b2118080a1509020607120f02030301150804060609020f0a11010203040807030815090114040510030507090c030615020a 76
    0x160300e4030762286c003d90b4141d13403011500519003c010382d10f6040450440054000454039004c2c5a4404029000d580c01d0990103030f1030143e914542d00081508544420309410a441801c2201c2800440e09404030030035034803e41082e031070703040202011500d0301d4500d000c01080300050088003c00c2100f01c20a5800c1118561103002c04200748411490060301640105941944051125000300c0c60001059031074951065002444100d2038020914543c0514000d5130980660700f90510b0095001d4a1225912207a1001e9821941000c49204101e184080c10b4800c000e0085d01040034031480b40d101d84020000c5d84400c40d6942d11070b0504d080590400f00610b4086003844911280d940c0060085902c260b500c10802442e03c255590191085080942a80b00a0f4265140541c05441f11545c40d07000e003000c0581a0344200700501000142e50740180807112156a045041000850004108040c4c3d0440d40010904101c00f00d0120020035095000d816590110104000c0c03031a004541491114010b00c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 277054667 1250 277053417 277053433
    0x60b1819051005180f09070f030b04060909020a0e011503020306030319020c01090f0e0606070f050105090109140a03020a02040509010b090103140f070605033103180503070605160f080309030309 85
    0x41000c0c2c8a0b014200c0c5406c0041d14000803c901d103c0c420030080d9030b802e800c0001780d1201001c0840c040311000c0d001000581d070f440401d4001c2d85400c000100c0280240c1c03040c40250760400d511480105005020340041c960080040391290b82c040c0140e070004400003c581c00c1521554400035600c401194500d070200e1600c0d440851002004003144080e40d021609100d034580310301d801c0c4502584051019503444407203214000000c0c50a010740d50081b000140003148403c640e041c000f10043e050300c0d40485070b5010380005000282c002c500d030400c40f501140c00041c15590281036501401c549a0496070104101c4004000c0214507003400c6058010302044441c68410510780d00e0351011039004500102d20b00f80001810513a0001d41900c4c02444480182c8600307860a000c42c802c11800041100490003980b11403041c400c0241040c802843d04400802e42185041800782035031081d401c0c250703e04425441c148062215240504440644c422911540d0345000018143c803900169640c0c500c034000c4500d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 277055917 1250 277054667 277054669
    0x100b1314010620031b0a08030c13050d03080a0504030504051008090d020c18070210060b0903150c160501060503070810051605040e0a0b0406140103060b181905100518 73
    0x8450000038000c43c00841c6002240382415440c1c460344c1082002c45d00c600b00144001a82c0c8070061400740c07480d00d0b00f403521220b03400850082610107400c030398020601e04948001082d403080d82240c001d50b1641d00081c00380c0310b40c14100d84a1185401142c0c0080944a9442803658001d661078401c018900903a00081c1d17a00100f2a211a5042c160359804038032410344024075000450300070741149480c0120f82e1580103c030308c0101034500d6680010907804020450600c0f07402c0c00c0c4128003e5a1111904c00c07030526043c06020a030307000350301e500303010355050030540e804218095010a003c2c2400a044682180ea1001c1a07a501e03c46009124200e50a04000c1464159942c2e40361a82880320b07110641864207204019005c0c500c024100d0b0700392915610b215a0780e03220791082070064059a2402c00091009600241c02e4940300c0d80000d00d4840200519811b5904281c0c40095003541201c810380324030050404034403240c40907004594003a0000b00301e0b900c038a410000401642d5420b00100308003420b808 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 277057167 1250 277055917 277055957
    0x2406080f060a0b250309081c1407050a050a050102040f0e10170a0b0f060301110405030a0f031403013201020c101b0c14060a02100b13140106 62
    0x1448203074201203101d00900004901c100540120868151400690700d0000784001c2d0030b02281c801500421403010007400300200c2804101ca07040000304440170b07540448d04006002c40c4201c40602e025420210341002006824044054042e403c1800c80d4010343c8035041482c003d52043c440c425858929400005900701410702851044c8410428292440e140603036003c0000a5180c142c80036018040c103040000c2c0b441d481c014003401c5815845200780c81c0540038542100c00008c20108031640c00c2c0010411954002807480c010f5038041404401525540b5058689980f600c0c0d04450050b400700c004110407a000c03001d03940c408404000d480036400c0081c0e5110091031401e1020340142c0000f04080d10360304103d0b07800d04589941c0c3c034020307401400c100c03c7c28000c1c80d280c282c12611040200d00400c941c050300d04400c0d40d8070504881051401c0b41c030450281d5110a00d808590615485945960f50759883c1040d211224a104806110344c01005035040f030003440c240030b6440880c5601c034200383d0a415031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 277058417 1250 277057167 277057171
    0x9051e01050a03080a030903030f050a0506030d0525020607050303070513050904020f0f0a0f08061609120f110d03120c09210c24020d0215010303080a2406080f 70
    0xc0006540703000080917084001e00920380e070a8041c507807071342c81560603540d0610176244195280700f80080c003401d10401301406d10454a28650170840c0901145011003007154000828610680740c5030541030040c400b08407140a4640d01414500000c01001102d030b0f04031009010907008440000c41c1103032078604100c0e8070078054034040c2d00402181035502040c18000010716071000002e15503080d955691400d03554941030340c0c102c110715401c1a401e103d00782e002c00f0ba284140d5401410210425410503020103107290701200007410311181980e141e414440902c0c08001c407020003910102c0072540c107040250100080814450310186801c843c00f07003580c0b080c80c1c0308068404c60348644c03002d0340100036111034a400740c0b00e054428640b1090001000483e600484d42c100f0f0850091201140c20101c020782442d603400f6203682503400010442c0702c0c6030070f80c0201074152a80340c207166002d91034002c202c000030540141c40c3c0004c060a401d0100d5a40c1c0313410280011211280d44003034240d48d801c8540030302c0b00c0003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 277059667 1250 277058417 277058423
    0x80c15030a05040501090c140405100302010e1507020301140412030605100c02030c060d140c160f050c090a0204170115090504031b150b01020102090904170409051e01050a03 76
    0x41400410100c0310070707030030007904980900c2c000308154580d602e46c4494034449038007a034040481440d5040742401c0a010b03581d40302c4000c000089849207560000303800ba031903c1002521940040c0c0755012503e1200091380c00240e009070080050418481c50000c024505460580700c03c0e150b00940d8400a110b4003403803050720300142144808254404066038000711100701243c0c54000c41783d00070205d46890f005007c01c58003007030000c104456100d80300121084040c1401ca00240300b08441c0c8011051100520301c2c140e8041540c03a112401800c00c0e0b0b050544d20302509600c403005d40248003030006a60050b201395a40c481b405d070380036542607034014200d900c2030a10480c030703914010080203644041e40c4510b60260103410000010380c540c1b4a50800c48401c600100c0f0140c8180d19200110740445c410041c1c802d00a0008600c0c2c40d255400080b000007006000030b01c0380d04044491405803e041c0d080c0c030300404c840101444a418007541003292071000e0355620610070040e8000080500c2d107150b441e030440360 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 277060917 1250 277059667 277059709
    0x9030b010e0c0708120121030c0b10171b03061b031302030607030b0307050a03031b03140408070608160815040f0c05192d0c0f1101120501050a09200c0601080c 70
    0x2003691421003004ac018860501e12802031000038881401030fa880c1c94181c801005080401e040c1a101584a01028401c03402903205500b04682d20030204503110346902c0c0c1c801c49a44a54514403070710107000c81c4a00c02034140c010b600501005a815030820740d1000f108409a584158541c02132101d5802c903484042c0000380c422421480c41070b010380110b50100e00a10340700502c0c850500d81c40003554410340c090945a0301000d02001440e60200c00584c00c9400b004004500d0040210020701003100900242da548034100c4540720b2650b981e40c400c80341d18964010501169134000030161264115503060b4034503c8400c007440040610a540504800070319525166030780c000d10182c00281090701c85d42d501400320f0501c004001ca1100442c40008170300c00c0310342c60500ca4000b0001084141c050380f0201481d420040184115518001c1501c107413981c0c442c00003952403070030740070849844c0322540305900020001084c26441801003a03c1d410b9910800407200310300c800b81c0a200b004494001c1c5129007403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 277062167 1250 277060917 277060937
    0x40e0711061e1503120c0f0102031b0d0608010c030b041b020607080901140a02071b150e06090a15140f0409050402131505030d09030b010e0c070812012103 68
    0x929440b88083e04940b044124005922091010a26094a2580449030b14a0110355114042d4003000b02c0c00142551400079810b40c2400e9000e104000e01440c50710350300e6900400c4001010f4001d500400003004803500a000c0102900700c00360050841d201c03164001c5080206a00000721044081285105664010551656210000c990340b90010f4a80c10b02c0795281c4004a03807c03020800018010800c2210044e43c1d217249107040c413210745010040400040007140b04010804c09501626942c4806062020000003603000080032071280d094000d5002e40c0040d40818841000314040402e0509a160044260309014030b0042c00d000c2c1030780e0409104000c00040c08a00318503004542c010344050001c0c0d54080d80ca0411000b44e0f070700c0012207580d050b980b14040100e4941003004444610b0782d41082c80d20a82192901100b58005000b0400000182c43c080754040c3d007500126001c10f030f00404200c0e141c041c08031040484180030711981d0281546801028802581c0e65403221580c0c2d4913413240c0c5002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 277063417 1250 277062167 277062211
    0x8160501030203090a0f050d12090201020a0303150810060303030b030303010f051e0603240609010801170a051b0f010914040f020c16080601060305010e15030102040b040e071106 78
    0x20f0340c0028080000c41c002d1019030000500640d400d880420f00c50130290411448030700000345440c08000182e64000d04106c02ca00140c0d0b0041540c0c20241c0e094a004254a50201301c41481c1d00040c0c3e0026095104036030000401380e8103580487d0a5034883c0e5014050a102401055940c0c0001e000f1032a100300c03d594100f2241c41e202071600640800c0e42d006010003c074010016103642c01c1140c010b00f0391415000003100b90404000c00c400302d80c0040f5511030414440c1c0c0700003403022805002d0f40300d035261404000000d0360301c2040701c1082150301004848640606072200c045400031650030500840c0361035285000c541c084d103410416642c89900025540301200d0400c0040c0c0f0266818481c296420404401ca20704148141003c103078180f001600550b2078810002d180001c160300c4070042501d03000050000703590821800e134120340401c002190504c86c0b040068020320440d40800780784500000d0016203104126520b500c0307a0040d07200e01c0c58001c094192251140750840e9034110640400080400d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 277064667 1250 277063417 277063421
    0x706020c130605010912020319110301050726060d0b04081308070506090d020114031e1605041a04150801090e010b0609010f030902060705010219050405011b0303020c010c03020901090816050103 85
    0x81d0008044401c9d03651116031440f00341c54007002c2918100c00e8912402c84a04090080c5500601c091904410310308a603854400403c0c1c020002d030040c81e240002060f0507690300001407801a8000748074031400e05107464018099403000d01c03074240b0b40c4141800002d114a000c90004210744000c0c008070302e0002808200000001e003258101d05205240d40d6003203034014400083c5d0321613241c40c441c00c1541c40240301e2281406500500070000074202400702d03940e4039400002d039022509400c4540c0003030002c40070308003864000c2e80c0081e0540380105d8005401e142e4014802d81c101e03030303018004110384048040c00c1801d03100f1260410f50040400c204181003940b08280000000507545400100b40002d070b8005006a0300800c8150f0b19a0b40106504015020800303c1044000380390800030f103054905800600880c00c607608580718079a0300509407082c10300075011907401c001c0810003040a02c608030000b0700207400044049002964980c004203501c0000529200744058904485d25054501001140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 277065917 1250 277064667 277064699
    0xc09050702071818121215120c0b030c040e130309030311101b0e1c0602090d0b07031401050409031b08040b0a0206040312060e041b080706020c1306050109 68
    0x80c07040c4c0da0b40484402d050300502070f8007038544510140c040161990000410340d2400003c01e01c110f070302d4111000c14201840505038104c8650440e08044a030842c101110550001e0b4029030003500c0c0003040010150004000340b050319a80001500b0a45400c5080100145c00400050101d01c107030400b480401e0140c2c1d14010364000d038008480d1031041000310101940c0c0150f240409038110032418800b10f0b50401130031400c10909441e64000f1810381c043d050003c9003501000381c0300550004104041c4e449010b03120a040342c000d5200d03000d5090000f4004e000740445c03902d4000740080072001044619103800b41617401ca03056a5101112580d81078680400c0100c0903045800ea0020080018170a481c4006441000815006040e052405040180404d40c1c2c40c0114030600b494440144011410700c51203070b4015400581d030013090440c2d460816048a20784d0041c0c880341c45a000001a4198000b44003029181d00303541e00c03006200c80c905e082007968074a000d15030104142c0d070401d00a08183e141240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 277067167 1250 277065917 277065959
    0x2190801050306041b080a03020318040902010f0f020a1421160201031805070b040e01080a080403030518040e100b090609060d0512030703021803070b0f070c03050d020102070c0905070207 82
    0x14082e51b648054914051050308228003681011840015000400240100c40b00056405004011007540020300385407001c0c1da0354080c403203040c00c049620340c800c00454120b80da2003480c0901010307821400351355802101c1c29661501c5104454040c0e44010841600e503200c50f10322002001d181c5030303030055000d0030043c0007c101d02240800894042042004070800074008032500507680d50401c06200030050050b001811140c0c046621100041c11800c12141200d415281482d00c40d00c0d4030103440b000d10011101294054101704071a1408100405c0328040031000d07807005c0008540e50014440c0d8900c044642586c00030381c4100149a500301070204101c42840313001950349100b04040b41420617001610040e0001c1d5022403125034203101901e00e009070b410100c00514020f450f28040707a402c0d108d600c0c4680c240030804a4407004100c14185c40d00051075000302920705001141030024000e4000c0d020a40c0c02c54820640061400c40e1440f52500600b416400341010718204503d0350a01c04004601c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 277068417 1250 277067167 277067213
    0x203030702030d0527090a0e0319020607031802060d0b01270302010908060f1f030204060b03060f0a03080904020703050d1a15120411030f0d030219080105030604 71
    0x140d0050782d05111210300d400480d01c400b51a880414120700212450041e1010b203007003510f030300705503580e2800301070b980c00a824180402d0710458030a505065000c0c1016108000001c9034090b446542c011400a00c01d003920b40e010419215070358001021200d0480010350410420000344082c0c80346e50300710200020060408003c1c1c030f6410f904100031010b070381400114030b8404190a01c210360b88400c61130f009195003401403089092820800140a00c00b80410004505a40030098040841e00b4000000d42d0010f200b089166500d0181400c240d01c101c907200c0c0b05028014440b0103515009600500b0340c0c0c0c1009181d41001400b2051100070360240c10284d0a01c00c0900000c0000501c03406000120020740d0141c0c02c00400c2401131003400040408030a00844040c4040442074117800d90059019411188000d46441706001190034890140d00c4d88416010f50031a02945a4042d00145525503061064203040705800108581001083c0102d9602d500510081004600f02031039a0310301e441045d042c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 277069667 1250 277068417 277068427
    0x70c0b0705070b030c0c0d08090d080402030c0a03060501150f050a212f030601020d1404080d0f0e01021b0d060b04020406030b040623060a0216031113060b0f07020303 73
    0x40503caa00704440c250a1201c000800104014050000110f1010306041c8013482c0d09054000c1030311518030382d00c0402040700100000b0103545d000c210b0900100005003100c1c00342d50b103902b8060040c000c240152032a0004489100d803100e407140500092141079070396041e0a00f000d5403400c503000440043c0800a000c08800c0f0164850654440c4070026010094424000d515184032600c05801d400e004170001c080600810404d82d0b008220401e041c0424a025080d00f41c2c42d8221411600440e0442940c610404003181c070540d800c9480501c090485490394114600c40b1801280e0f185a281000580c01e410411070000f6401c0500416a0031440f8220101d000b0300003101080487c2c0281d80b00d4400a51640500075050a2522460b0050405041d140c000d40030882c0c5c042c14011072103c2000d01030f07100011240c20191091144100052151920081b42a964103102e015400111b00301d82c803400071200100d52081702031284508855000703a0850070070400d24200300d02c42d08207110a0b40c06002c2088 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 277070917 1250 277069667 277069679
    0x80328020d0519050411040c050c061501090f14060a0309120e0109090e0c063a1b0206010302060a0302071b0f0602060c090907200a03030f02070c0b070507 68
    0x1401c00d0600700d8500060343d1418800054140aa4050600081e483c02c800e110200e00901c040d07030200341d006e0b6000700b00c1c881c240a04803018840e100542c156070046205001d0034840740e6600310382c0c0c50004d83e01c0354840d9840d03030904041c04401d480f03400c2d0346180011599403582400406001408400c0c18000781482060b1075008020344450805000121030707c503156010740e00030340084003030144034004021a80b580000e4554440800300c81a100e403c0c04200707190415071030000760400080b004024012070103c24809482c041d0f6002d22403440d641400758040003880f00000c0d1311644c8916500500c0142d10b15000d0140c00c4d84a90404801c1540030071800d000704020600103191060211940100f0515050300c0c114103503403d40113081103401c03503414401c40e6002c01060360148107084070444810303100d103042521488645180c103000d0b1030504e400861034010210b0301e41440c0f0700039241484480c0450400c00f089200c5e1400080808045a4080c8041152080a0401c5038881c0040711071a81d243c3c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 277072167 1250 277070917 277070921
    0x1804051b0301030641010803070b0c0906090d0b010303020111091c05070924090603020105040e0a0f0e030306012a0f05010605060c070305070f03020f060d110a02030901021207080328 80
    0x5d41c0125040108403210541685c000c04160041441902035400c0030300035500e20481134030280c2040401600411850115a030f42402c9841e0b48000410b100665015480c01d10f91005091001303038095480c1c001011030414040301282c3c01c41c113005003022110b540382001d9610300d040c50710085c0d8081c460002d0204510b0090312a141070322014018190800e8403015018401000301d42100386c00d1800d0403030410060b6002403d803000d807000307640c00c540e07140c0e5081d0b5a403009061415240c40711904282c1c9801940c60080000d6000b503100ba40c0e10000c4900710040341c001c003001c000520782ca0742004c104030750110b0071000e0300101c502c0c42a030021030f045079900002241c640103800107030b045410a103801c20401c1002c004510051404520b031040184c0741d500001c0e001312145c480280640c40000baa01803001c041e41c05000001c60f109522070f290800c25900075a04c0c2c00c02001d1602501c5100c1141a0a030002400e50700e80b42c0d48002c9141c030f15580c600c514010729103d10f29503100035060898501c2c50395014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 277073417 1250 277072167 277072241
    0x60301050d030210020d0e210901210207080a080a0b01050a0c020319140d021207061a04060608061504032a0b030708100506070c14010509061804051b03010306 70
    0x6a64003041a10f905c80c9650f0422201c00c1501230000100d10800f0251285641a01ca0762903090900c00d00c80720f08034450302074030368440c0a0080b000d403000031140100310960029103110080340e0385102a030380c0e443c60341104907072035014024080303072003270000340400c500c0380541103429031010742502e00550340b41441e00310030001d072a0112002a4075031240034080728100303e400191410362000f000d00d05c000021801142c4070f51500503061680380d0f9075400781601050101d0068004c0070b4410440c1e199140c0300200418815988240f2603140c01c8d0541c01a0480881614162500181590401035034101c141440d100020026080049200303400105000003002844c4101c040380c07221505442c00c00301230148080290000c074800d903400e200b80004141d148401c1d806881041c840c0c18030071200e540041c1d035180101420168030100005480b440da1013503101500c104403040c0c0c0c05004d81d84400c0c0c2d0603100407a040c5008942da00080c0010000b1640f280c20044c419072000e14810700c26000f58054480c59180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 277074667 1250 277073417 277073437
    0x515040308041401031104150e0a0e0a050709090b06090613030b0c0901030f06150f020102130320011b0b191802090f1006050c01020c0319090b0405060301050d03021002 74
    0x10700f260f01c816503010b0040740340040300c041d0b80500d41401c000d69950f0340d80c583c1000300c0030030503260054001a101c40d2801070103040320740300305099032030084c0c1e844c006020100d031a540013410342040092600114052405010b00041c401410601c02c00207000054100f0a080d42269201d108000702003484a07000a003d0040c480c492603441e08040009019105102c03080c00c1b10514190b4100040c881c04112210442103600c0e00e0951000c10400c1240a0300440e409110304081c010320000c1040a50042408240814082c9210001c541070041d94807481110100d804d00000200080c00140c0c0d0100150748000e00090030b00700d40b0742c10036641d011520864501c1610810400c06213041d803800c40003051744030303c0c40782e0540c445151583e414811440d40d8801c02c2d06001c40851464410407003901a40d060468400c11030780c139074242081c034403041d48105114030003240130301e0404503902111904076000c0c1d41c8003030881880d59291406000b00c2e038850349000e5046010307a40309055040140c0c0004e281e4400c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 277075917 1250 277074667 277074689
    0x1b08030403031b020f01080907051207080105180c060f041a030f100311040e0c090703022223060d150510030506030d0f020f01050a1b05070b01051504030804 69
    0x4207525020b00788000400c0c02c80071079940c3c5440440180c0e00c0003000f6201c1e800a10f0b082d0b0441e2251207507a4904810394101d02e80c020120084503a0003100015000c003120321010090082d51641504a07aa40c100c0a03602449604442c0149101d418544001d0a02e00c4410400c585031541d24408040e4221018480c184031083c0001030002d810f844004254202c000f030900d80c41c0721032135035407a05041c041401c0094016903c5080c1c444cc104c400b4000680041d4000d040c146262030641001402540b2051a00e6a80c80d10651048112142044c00400380c449082d0700110304090b550030f004981d0b80c2c40300f4082d400881084010742c6015180035000c00c100281c1066600740341064200000f04e2a6807170716508141c500020081079503030025184e4600c07829410103607040260958100d003032a0818490884039800d08050228541141e0300882e52005010003004504100040071145440b03004d001500030f021100041c841c034a80000740030f180c0314013104090320380381e40c0755034000f1345410603485040d80003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 277077167 1250 277075917 277075919
    0x20102030726040b0a06080118050d0c08040308031005130c0201050c0901120b15070b090d051c150f090e01050604020c070306020a02031605010c0f11191b080304 71
    0x26044500c01949002801402d004904001ca44110800c0c00800c0680b031100044041803030b1140c070b984580007801c034410003800300e1060102605281d28100300c0884003407180b0540f800c0c3c550b2145419141c0c03958441222442c051450b10f40d242d0341d0304041c2880340f0074500078100044560350b0000880c4010640c481c045980c9920200181c2140c030010120714a961080203140780350b0381d000150000c05094000000750040800d0041201c802c01051400003000d0006484e1090041041070988200349000441d094104582030848140c0224800f101e501300c1052460703200c00f046500308045918103044541b81c0641e41c2c0c280916280582da100d45034841d6201d0540c1c0d0050000c0c040e66600c044142c8065150036410130820307545442034071014203603d6001c01c07110303000c9109204840e1045060100d5180080c034904217540203004d401c030782c2008114082101361001e800f40b426821036203401000b4106010001e1030060018400450481da2400348000c0d00810381000841c41c0c0181050b24000c1da121 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 277078417 1250 277077167 277077181
    0xe0301141914010810330807061704020d060b0a061101050108030901020312220c061205040203101109040e030415020304030503071e02091501030c03064202010203 72
    0x11100c19052114aa01000041c0440301c000a04102280400880010368003001b1010902281c00d048404013003103440758800000031142c04044050fa000031064410455858000392082100125008800074902c40014090700e0501c0c0b00042103409103501161001000740081c01081c001d40254012a0300d008148222030400d1150b01e000d0f011000056280580c980000703940c07809440381c1800a01c480b40002418072500c074841032030f004a43c0e0030300d01010b42503140c2030200f282c0707501034200020308030350f806010b20344240a0907002e030360041d0140040b00400159170001e0406104003450700340d010442c100903510b503440780072105000303103020350f40b03c9003408014001c00305d00c13101c4101154014402400401c6010046170316840e8010002100501c500d00781ca100009046c00281d4080c001204001c0000e20310040752880107001da07810800028450800d60440d1928041d19200c0803807042000d000001c64001c0704d00c10034007801000419010381b20509000f00c500307480e240050350080184140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 277079667 1250 277078417 277078421
    0x9021305211e190b01170f0604080703030b030a0f060209120a0809180405060a1802030d020a110a03051b040b090406091106070305090411040f09140108060f070e03011419 75
    0x3200510b49001102c0300d005484c0c070504e00406000b010845000ea02d101c0c9202d101c10090611105c0d00c00003545c106161070300b0651803940102e0f0f0709074042401d00500b02101c1c903010501100c520b90010b090010024140c890000035000050240c0d000030768030384c4000c0e001008210301e80629105039500340d900c04001007404059031407174515100341c10382c000510001502c08146198486400440002c03c13003901d07600849403041520f80070b9094015141d000421070b03408666482407e0040c500300c10302501c41400e202c2291050710015100e90040d00b030450001e001e80074032186e0440700501c0400d080d9807510000c0d03011113003520100e400999070300b544003c2001c002c11039490640d08507440c9041c1011030700d000d445445502003007407083da42d8030203081c0502101c00aa501500b00d8200203903400d500c40c603c00c1d0060003016604600c41e44000d000080030fa2000a06d50302c185040001c07d0075948a6172401d031445910045a143d01d0354a0355407081c3d05401e02110035100310b00146e6401d1415401441c0541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 277080917 1250 277079667 277079683
    0x70f110a0e2208120708060a0609030308092b030c020309090720070f060207080c060a05070614040b1e2802040b1204050709021305211e 60
    0x4091012100c04000d0340031262a059402810301c50030079900911040340c0b80d8a41190740004100c0c120104110806015a06007144600d903262981c08a079112082000110191440381900050f003403407050001030322800c03100350050790110403103084011204038031070946000b00810021144203283d040d500c41d490b0191144c0c0507040c0c00518a02140da0340400e9607810300424100500203560840403800c02c10040c401074210702d10003038920645c0c0325a15031409107138a2240c80c0c0144203500000c42d00000106181c00c0c500c0300240360900d004203086d804e4403e41c001c050291103482d59115034004038110501c03110f21640c1b00b030000044038a4031a2110491807000e00c0c0d081c40b00c80d4103004000e010100180751100b0501c800800c0450b4801c07011005000e8456504512040310020800310101600e0070351460189101e101503981907502d41d8140c4c022400f90507080300448907085e0f000c000e1800d0200c03410201d483c40d003070503300814210782034501d4404540000c04408014021060041c0c1c002c0c44409 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 277082167 1250 277080917 277080919
    0xc02030d1802100f09050d1a070210150b070618050307150c0e0f0603060d050712032003040b0f0c030307020c010e03030c07180608060702061608060d03030b0a0803070f11 75
    0x7802c8200d130707400803c40407107030080c1c500410b101090b544c140301002d0b448040032007203106030040d540740a010094a40020003120a031690400c44062811031613400d601e0140c2c3d0802c40903c1c2050b9032901d403403014140c0d075400c5d100c0380705001910001049080c00182a150f02070260b644407908032003030440480c1d22607102c4104001020004198036520f2041c1140616011500e0540b00d840d10400194030b8504010001d0040c0314030300380040e03174100c0b007450b140056000780c4918204805086500b4651000300390101035a400c200410b1101034100c030082c05001100c00c030428201060300349060301c1c50388155002c00159002101d52100703036038000b251080c1e115058010354100301501c1d190507982ca8842c051043c1c1d0002c03c90354901060b8039984000700400c9802e048450904041d14041d403210300030365800c1c81003000c02c80c4002c0c20a00501d10301c0d0003100098070000d403a0046490490084c008180019805080103000051880c0100050001c0602403694002c9804103403400340000b0490f02142c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 277083417 1250 277082167 277082177
    0x70810060309110d020a180902150702030a06090f141005010902040f090f0207060908180a0f05010f02070e191d0c060c0705041a09060f03100c02030d180210 69
    0x1880005480d0300341c60a01460580f1301841c02c020910010f880c54440e0b80010504c20442602e070060500150000000c090003600c0726180440d040d0b2180f48a07208401c00603405a0045102c0400643e00d80d02507074083e40508841189071a142c1da07a00c513031941d49190a941d5901640242d07407144001e00c0f5407801484444011450035181824042004945100d400401a40e07201c140d485901c541c0c0403a400658070213010800b0024a18224490340c0114404d640c0f10101c0c0b4105291900f080905d5206940310448611031140c50b0100450701c0000003010b0508500402c070b00040d6031a1030010321030040310400c903000c21b003080b0080c0c807204490f041c020444a000e102d061680303440c032000c1001a1501000c0d6290303507a0301501d00c2002d240c41c16503440580c01c5031804038804070050702c0001070000b180c0119010000794a0b440c042101c071b542c182c10060f5043d00212500c0c407400415600064441840e40103690030800d180d0000c108035619814200d000407403c0d104881140340411b0f01c415521124104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 277084667 1250 277083417 277083431
    0x90c010806012c032b03050c032d0702010614040203011415120405010b09010806041a0601030b150d05070216090b0d0813090e0c03060c130e0708100603 67
    0xd120080d0090051140300107090780c07407104850070014140c1c0700c0c0f000e000c60341c0400c00d006140f91040d13011813202c00d40d05d25105d020044548a03004580c0103005403141642542c544400010444144081104c91a00701c650350b18a42402c0e104401e218400a8000144151030855404150760352006041e1041d0701c100b005102c0c40b0790410542e02498016030b0750541a20512445004511801d230384820002504c80070007080081c15002103c5405042c0c0d80e90800340d0780d450b0030b6030ba109000d880c02494240030160070251a6403200a0542c400b40c14940811607518070404110350a0010150f1240840300181600c086160741c020940c01c000c0610040242a42c540364071680115a80a41e5140039211505580b241e501e9002c0120703015000360000383d03540008503200c50881001d1040c0c1d90030030b08180c040f600c02d840c08101840c1e144009005801c503640c0b164001d008036030004402082d40201480c0100d545907900888510842140c3c8032005d0509050706140016804c2da07001008040c20165 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 277085917 1250 277084667 277084669
    0x901050403060e071d190c051204020f040204030312110702101407080c0606030d0207080304052209031106010e07120207030306210c0503060f160908030a08090c010806 74
    0x4200c804690b0007400000300803d411050900308107107540240034000007284c01058010754055103e0098600d0010421540c050803500e0b000d9484400940010030814449488000184001030354803e20081032601c6004103017000800300e8009400660000341810701c8105040c411f8840c8020100044802c41e00b4003103250300060141e054807910a042002010303c2581200c850010b8174900c0782d00011081d02d607100000e559903a4403080300c950b8424428170301103a805e5030020501009464801d0040c61078541864203024a58044140e1680340301d0103070b864181c9440b028498030b00c42911950b5040d480c6074201103028545141a0801103044140301300340944250044001155040112009070325071800342403e80007084c0a0340304403e0b030355212601d2002e0144e40496503821510400040340c44a8881c0b060654407042251156400c04451000c580e06105103204902207a0203032800000c2e281c1c442e0725460468121079043c40103e050002485100f003000e110f4080001402c5c42c05080c2868150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 277087167 1250 277085917 277085927
    0x41503030c0f060204060e0315040519020102100507022b090509040f122105060d0201270617062403060a0f0f080105060105070309031e060e010e0606060901 69
    0x1100040600168600d07050030045040203203584141c00c01821519160b90301c0001d0020315005410510070f0140506040340680c18103601402643c0280c0108130840400b407010050314141c04050341540701e21904022102114011a8441c200c9a40541040030886170901e080c8015100d2000d14504001d9028800b40c0c0d0100360300003240d2044421070040d071120301300b13000c5604ca40e000103130107442010050a162500164000c4004a0407180450042d1480d0b6211045800c281c2d4000d50005105608401641c40303840030401d0000d8244091544940504801d500c4000715409080030070703140c507034400c8001d00101d000303035101e80700b0b40e00c0203641190341e1001d0089a0362070302d0040c440d401c040701047d1107403035005204025000c1e004e028441070342c1b910800030182815100704004d40d800c10300042c0081d4458000d69920541c9500c851407514110340e182001041c020301d031000020030506114011540c940600121803911400010f8108210f0300f4941c20104000c00c0e542c00b86804020340721803a607201c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 277088417 1250 277087167 277087169
    0x10b1210020304140105040b152d06040f091a0405040807060906021c0e010f0c0f082a0702040f060b18032d060106090f0b0a021f09020307050415 64
    0x80c00016941c0d955032901824000c0d50720301118040d882e1030104400c000c002248640103010038000d001405101170104492010700c20795500c4466084810603458849590607014900d0703004114074140741e03d032502d00c000200180e00040f41c5030f440310000480c00c1081c600958420205071000c1c07003946402c0d2031742c41d00c500c6a04ca000f0607443c0d440003898140100750b41941e54200741c090780142d000541407250405031000f515210050351801e0000c0141030200d106000b802001da0311354220340e00c41b6401c20340700d242004081d107200208072031102c0000241480007000e41580c0c401d415481c4c14940c0148422580d0a9460b03041680c90032900380480340018045d00d01030b0512a000c540012900c2d00440e0600c203140c4a21040d100c60f00f220545d900c10081c5101908544544c115212a170365020f084407040390310b1150080310001c80d1018484622410010710442c041d50040361003050032050b0b541c020504c0070076942d11140e070f10043d003c2186020b10401c8020305044600740306d03040000340300c88150700c02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 277089667 1250 277088417 277088443
    0xf030307023012031807051002070905010506070b01150507170a02150903030105041808032a04120308090f0a0506100603020408120c10020c01150b072a081002040602010b12 76
    0x2961045d282061010045040500400b904624100401940c003a60310009806000b80160500c40042418248402621103c0b60003990590442e46022888000c00481c5504841000001c101e990080b6a42051034005001c070003402a5079580e003101c0090401d80881007640111115000340300c2450300000540741501d90031240011904074000c4485400304d00000d0040803450040304119104d2802d540e402010308080c02164102c816031445900d25102d41e001d000310403641070f00e5600c040f900c543d401c60ba204024400b00c51a540b010322a20f8034180e400a8102e81d16400360341084515009040520001c1100d4142581042d080c41070040d164180800d00181049010071100b43d981c10821500250135101d400443d941c141c0400101d019194048103500d2078000307180c0000d03184081404840300d190308610100311710180b545940f15003600741022002c215824100115000b80c0c20b2115002061500900507030700e9151200207420f40d81680c041c0d0340b0650007251460003030f000108140d411009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 277090917 1250 277089667 277089691
    0x6110a0f120e060906060f0306070903060f1e0f1d10020f0405090a020d061203080a1a12070306050f01150503060301060b1b0106091a0f03030702301203 67
    0x41c200c60501c004064020400e24244199010b104519101040007801030000b940d0050401a541040c0340e942d01e819617150001441caa0070400211310320768001103420702002c00120300300c4020300c83c13011203090510346482801c0d690500602c1840c0e0b03904c504115640b990780c407010300c0740c2092800303500c3e0200f507003880000c143c001804840c0443c140080720050400148000070500f03006041900940290700120085880c2480108081d0b1007401c10752000743d0b1559485805940303082c1042c0160064040354840c0d0110017400c84030303075502c0c911500040820303040100619440c40c10400c09884000d80030001410000c001400a0000c44080c034020121328244603039203131260004a4014021030b4400b420464010501180010061040f005584c004000074421135854000316421a88030009010f01447e541c500c0c0d038054104030140345074140000b03068030b042c00030b5038010400c82c0120300f41c0415a032a802112000f10305200c0d403910030005003900109806200c4292851881c40087d0050390f11035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 277092167 1250 277090917 277090937
    0x4120204021603020a032705010c11040204141309030f050a23040e091c0e0109051507030f030b01050301090b030a05011104141516080c030304050a06110a0f 69
    0xd151601103034200050750442c09a080400e080007500c2c2c03002c41c0400c40014511282146052110100305d580f0100904420740301c440c5030000644220810700d00868001039140942ca01a1340c036807000d07100030540310a91f18840c1400c001086840805615640b84140c90591410040385d4007032020140003290b4104150b0b103401902080c0d40342c842502c0d2108020030552080000306010001820450345403010000c0c2580b191202281c07110325010b50303e2421800842800c50603442460b03141c03600e45040c104000000d46800210340b02010f059264600050001031283c01c00d54420301030411103003189020000e8001d100e000802c41d00c010300c5200c1ea11034940b51010703000e035000d22184040a602a00800041070b21040c0c500e156041407040170035000001408450b0783c24070300028410040341c4811a0310b08105180250b2032101118400c0d41e081606000008140b0003c000842c0500d0140c0b00821841c8043d141c442d0544650700401140d81c0018840d51084942105486034004140d0130118401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 277093417 1250 277092167 277092169
    0x702012306040e0708010603120e0405060108060415050d0f05070f1d190507080105091302060301030b07090b1b0610032103021909150906140c070504091104150b041202 74
    0x4c142900b24512075440e02000008000016216040161850301c072003a0b4201440104821503e0407541030307010803414000900c1c2403426500121503281d61032880c1c01c8803078aa90104400401c2000102c8241640d07030b440d54181303e400c0080f03000030130304d00d452801c6207420301251070000c128805821403681d20301d4010507001071100752404814040c2c1001000140750140d00284000020f10419020300d58074400719130307a50311300010b854400b50042c00d881c2c916441c6640c0d9865041004103903600300604e2071804140b500c8507100625003890041c0307411401240210b461350038a24013601e540500240100200000b034043e09001001041625080089903d44141a0042d21900c80d00000301c04c03e824a10020707540000d508030584034241526120444669019a1072401c00d002c0d22010480c80c00d58007455400e240000d04140d9140310039251851b550300041001d5032400722017200c44400082070613405040520964404190081444100c1c070b04e4804440050300c51402103041010f01c0e40e000e0019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 277094667 1250 277093417 277093423
    0x30709020c07150c020a09061a0d11030106020604030f0206130311010b0402040f0801050f0720031207030509010b03070f06140c070e180607080708061207060203030702012306040e 79
    0x50040c0f03600d82c6260005071100401445242c0070807881000c810340046189a118403c034010342d00c1283c0d42c0300c450012451459103640102c075091240301d8803183c0c000041581d550103140241541e03001051181014580544203616200403402103521400c2001030a800b1914884880c1c3c0c2c00d07003040e030025070f040354480780585240c40a95400c02d000040024900d11aa64040104e55403c2e008200303030303190141c14aa0980d0107907003d80c0010701d0210706c403142c204108480c40e400342c1500100ca00d420380500340cac8501c284084444401080d40d030700404c5004442030142c80074070202100075009460030584852101d02290040200700859001c480725207244807801c540329401654101c540310707a40c0340350409501408403220b41d01f141050f9200c120041c00010311502030f280a4490030000ea6500b107044421700d00c002d00499104980d006124403400c010703c0000c019180c1d5a01859491820540103800e59899842a80d0b5004564001c0d901c01d145c0c14a105811003012200480c01e404210b5081c0e00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 277095917 1250 277094667 277094669
    0x15080610030f03030f110901120b060301030204050c1b07090605030a0b0708100504090f050d1b03230304110a060c03120e0a081617180d02011209030504090608030306030709020c07 79
    0x1c0c403441c040541b03494180120250034a00c809070b846410314141030080505949200d0321f081e0b00440309100500c014a0a0b82240741d02c000c0740110346050103202e802c50805001e10502413000354002c5002801f00c41c0306401035001802003038004200e2600307940d48021120364001e01c0002000104d0010a80c01d030400d02110004110092007030204076410f0400d8000b00201c80400c48442c4a0540300c0101310f0300404030040400c80c150f4004145034425101600c3c0350300580308004140e4501c200b080400000480610700841c001c01c8544403800501c0e00f40020702a043c0c200c4e00900052644403000294000500313120000c040701c1c040b40c41082c0114452038503a580b1401400e0b03003404154607803908040103001400740d000c1c840307000600c100301c10901c01e40d00c600122040400c1c43c80100e08401d0800300c051045091042c501a044014070001d500111905070b601100090000207080090310410300440004e41031000180d0b00d14280351001039580c04040c810002c0761500495201004141404504 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 277097167 1250 277095917 277095941
    0xa1b020f031002040810050106050406030506010c0b010803090108070201051003260f0a03050a090f0206031305010c03090318150c1511040302040f0c050d0e010e0a030315080610030f0303 82
    0x102c41890a91140c1c0103074005018045191141c0240c00b182650035004590480707034541c4031145000d040030002c030083c003001000903050080b100d01c6000003c03c80e45d4500e0080139007401035a110311000000604244001d420041160706101c02d2105000007202c60408076680480c0880c48601d01c07650410701e0a2000c0441c005013807000c55000d0100b024200200200005c40c1d034100603039601c0d07441d01400c403406800c000c1e1030081c0d078184840050519400450b085039540c84103800b24501a96802c2c01d5070071500356000003a844031170740010150001c5a107402841d184404540d40c1e410202249401d854055042e010440c890195105002940d520a01c1c800b040d4a0b05214a4140c821b41381010390042c84204d00540c80d041900602100911403215560352a035070300340c580300240e07440c007010b49110f0018009555981c03d000c1000300040024500d0701e0300c00c0e240410080303c02451203020ba011a80856240e410280800004070424003200c020b03203500c18401c4c1c03206a900e0404400a01032a0018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 277098417 1250 277097167 277097173
    0x110913090b090114010608011805091903030b030c06030c0a0c081b07030b0f070e010e040f0504230f100218041e0501080c0f0d0302010b06030f0114060a1b020f03 71
    0x211450202c103401501410344180482040b07641c0e5001c04a031640000d10a02030010000c0000318002c1f02203800003608200840c04840141145050200445250305400c401007940c50701c0d10461410140b00c008030800d4103d070350302d080d0b240c200e604034000d211b03261000081002c4c4007051010050342800b0780e48009015207520f0180b907201c44c08035030396400c00d000644020419a0018006400c050300b07141c0f1030300b9550742e03801a0740d44600040d41c3c260440c000c00390b0300c00c0d254203031036079910b40f1445843d10a43c040d01e001c80d1600809401803901e5611f115140100d87c1082d0980001c02d80000340c164410324101070300580d91010360503070705845110003803410740c05410a000f4041c40010203205400e59020707007808200756685c0e126019516000a50441d800510340510034201d860201811200c007030090001182031001c050010310203600841c0d280d20800c41c4100140562580d181c500400800305072840c0c0d20b040e1803400c0180a4418940702e840501c1e2041580b1011034581400700c0c2c3c0c035004040c0407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 277099667 1250 277098417 277098421
    0x30b01030503131403190c150503060f0613031b0317090114090a050d0804030b160905010903080d050a0f0203011805060307030b0105190b04090204090b0103110913090b 74
    0x26840ba40060b110b0f51141d400c0c05800b240d46100800100b6010b6002070051810324401c94031040c6105004605a4111a001c0c50002d001440c0f02d4046854140e50398034155240f824404016880c0d510201d61806000144108104910020070b0642500d42050000c101d48400e00725a508064403900020000c0780100d21b00285100c0c0000504818002600d413200120b949201c01d01c101d000e03060a00345e00ca404000100b1044c00e010b03d45a81c8a0701507a07441d80f0302034032038580403035034482035401b808003004690103500d20039481110500502803d20f442c0c02c1061440d19255a54000d1401e016801a910408140e5440080e808a916034050300400c0d500d81d0780d9a1100800b15000903500d001f81781c1407000040035460082028000d480c0e2012003103885034204814004c0e0440c0c00c0e910959610300c0d01c10041800c110708400380005000107203025907a00e0070300c4003d505560b11031000074149800c1c0340c41d0701c1c01250741006940e10500190703003280b03ca1b040309150074041e12201e94045c2030b151300c40302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 277100917 1250 277099667 277099673
    0x130608040302010b090c16030c051c0906020105041709190303050a1206050907030e1509060123131e0504060203090706080f0601030203070c0b0708100f05010c080d06030b0103 77
    0x1002520840c02a00200843e044002c14024054411aa2000506020803440c0c003803004c0304600210070781c000c0c030b044078044155544151900342c83c89040c10030100c0c452010b010031503210050a0180c04184024081d908203560751903d40a40354003441c1e05003102184d1440e883d141e240c0d0000f0300001d10300d4290a4165a81000361090f4080e582190020744003182a5410b20722a00901c4102c6902500900c42a0307180d0508400420341c122000c41c00e80511140e1085203041e25004c14000c0500901070300e080d51400d0102c085480340e4002d1030704c0cc144030550800f0607980b000308440c1c2625460714041041d10f04080380580c50603100030140c911a02d808140700612549038042e40c4503940c0038003103031b14580c1c481e141610030220454501c1280d0b546800007901035403181d0080e5030090001d05100c40380958958800410300012200c0c0b0b0006106901041400340711862000020710301c289540311502e04000000b40500b40301c0d00d020380b55400c0010343d883c06441ca80d005400450b004002c4441d2940c59103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 277102167 1250 277100917 277100927
    0x381207030c0806060c06010e04020103090f0303061e050d0b19021b01140903030c0d060e0405011b18030209091002070f0507050f1f090806070309021c030807050c031306 74
    0x300041c1c00552140d001a50609045040f1559104440002d050a03803034540003428000c0b002740128101512800240c00203a0840c03407820100b0b00c241c4010a143c3d04004242c00d1501d040b410503403001c03401740c01c10003954036030760001c404294001c81054400d07a00c1c1c00f10000000c500c1814152a14800582640c208105140107081060404000c2c4800f080c0e14688204860040d1072044160308100040303005440b03c040107169184c043d40d03021560981e00d182d0560041320440d41540c07141d4403121499403154011802c00700f141b03881d0a10b61001d0242d40c45106410899000081c0122400d501141e08844200312080042d00c24240030355880305240340124284e103041e80121101d20038040081801c1c81c2030030030700907250b102a018200782c00100d42034204c00d02c4d4405050040c0030303060401141c070f600184800b80c0b00f4551074a01203158500362041c8003ca100b4007059040f03904020300e01000007544104030540040e03851a05580302e4514040040c1540b14046551400017500f00000903019040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 277103417 1250 277102167 277102181
    0x30a09051020030408030112050708060406020913060311190e130308070518100302070606030c051003060e1305160e01090c0302031e0703020f03090a0b0138120703 72
    0x710404002c10b02c425401008a80015140200390100c207100502030290041240890340340140c0c01c55445540eaa84802e08080054030300307542144e0005100b4001d424950624110351406000030440b603465610740249540403a160300d03107c1c0c0003c1c001c2c50903913459100100080c11881401d06000d0900512400751200c9145080703010413418030005400c540900299142c1ca2422071100400343d44c401d0410080c10610022002416420f0002d8000300380140701d003c0144cc03003156448603a41c180800c109200441c104040d0802d8201501071045000e4610f075180c02803141c42509107414510301d0300c2414400302803a5810b208402440000d40c900d5051100b50490b9200308041105022486085050340710440b01c40c0e407908a0349101c0b145011a03584070a60011241c0740060500013812041c2c00254070a6512440c558000e0642d00103101d940c106082c0148401a20311001c101da11301c188544141207000040400c0c079040c05100003a02d003c0843d80003907480050202c1a04c2d0102002d0014020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 277104667 1250 277103417 277103441
    0x110f0c01020f06040f0b061210090507050a0b070605060a2c01120f0f0c05040608030d0c02060f130206041802030a0501060e0d0602030a110f07030806011e05030a090510 74
    0x2e6104070100c40000495558041c0c0d400c40903030805d840304e9449513070401d60003504690300459400c22100d040081400100c60f154130b0a90b000c14200410b0400c0c03482c00916410081c0b08600e445800c11148200c10129201c0070350008000c111665500c0014440d411a54041c0d1390003840406c85d0300c0c0404900143c2e070b6980801d6600d075032159894507000c00c0003c00c1010020400c0c0403030407101001c01c210307058050b000d0b41b1460b404640320b0344038800304050795010341c0100b0699001144035a28511640640703102031a142c402030200749040540401e842a000e04003a44104101110f4800e40d1540c6007203801518541541d4414807200748140340c0258400c5426001d4186028004105540300d15043c0046401c020701803001c409282e110007000b03500103007241c042d80f5900c1c041c42c0c84491500f8003901d09402c0340910103440b8a81d034140034101c078000500c1c1c981044000350310502a4841081000d0940d0300310701d4038a0701da40e00c950324400180b61404e0090001d110b41d2019a801403c0c5800c0341d981014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 277105917 1250 277104667 277104673
    0xc050102160b042d320d02150903091003020403020303070b04050c1203030703020a2001060303021e0703080706090f0c08150609041b1e0e0123060a110f0c0102 70
    0x71840d0f441080c82c582e61407081902654034001c2101050340d030b00d51760319850400407500302403010105a800e0600003080694607140c00400d0311038401034050001d51406803114041c02031518000460035241e201740922039104101d007404141d80a40700703134162405982e0107011641d9a1200b824a1260124115021211441505030388419804d0105201d007540510100442c110703101c6003426006034102d11032074020041d0f190105c6028000b0f480700184001d9440000140031411418000d0a2080c010240c681c1103081850300580b0500015841c0116a00055056140c415a00d07140340070700b0071041c4c042c0c40e9020305540d05040c481010405412160340c681212411200e8200040e1446000c450a982c441e02c1d01d000140400d106924a4030000903400000320740341d4070fa80790119071b41100c2c46070901c010541d02e07051000c005100e01c501e02610014020a0740300d018900c140888048008040f4010314002c0340c40c802060182c525242510803140035a04030062454400b035031001030b48840f42c0184 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 277107167 1250 277105917 277105943
    0x10203160e2b0209131115121e041110020a0c0308030a1803050c0114010503030d0c030219030f0b0901050315040305070b150a091b0c050102160b04 65
    0x81e014080e2824500009000215203000319803070a030840312000b00d00c1841110300e40103000180d9a41d130880340f00b0303018034a13038000446240c20310035180110307042103500410f040820601e650016a058840c1e40021007480d503520707a0b44001018055140c01d82070024120b90500780400c000c00002080d20b080c03015560240c030780070807160899035040521400741032040c041d1020b001040c00706008691100f1244404581c1605621400c10a15100700064002540110b81ca0000c400f0a0240005500604070014855410440001d0b228821400310a441a5650b80d0401a542c007940549510a4298442e0412010a04800790190216070800200c03186012191910340c6098000769051300e00203002022420507510703003070300000c10180081d4203004051200c14001424586800d00c624940b184400030715094400303112241e8061b405c0a1922410710008604044030299800c501ca850b514000c0c1c030381d59040c207145009104a4000c80410b0210301c54130418840c0c0000c0450245104500500c1c4103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 277108417 1250 277107167 277107211
    0x7061b0f021b010c0f05070e0f010e0f1b0901020f060a091a2e03211b0b1308070606030b0601020d03020c10021c0515040b04140115021509010203 64
    0x1580c0701c40011408102032000b01c40c0030800000c0c5c007511242c030079070032106403030303100c0c0c00300780d04c09030300b04e5003890301c407000d4401442480300c248502038114a42c0ea0f0340e42c903a801c2000c0c060825100c0021840e01411001c07648000c640e01c02c111b0604000b886001f95260b0341440c90720000a0322400c241505e04c80d410035569146420040481845400c108c800251a0300410a00c6a4550f0f80c100c04d0340c1c00c02030485004800b04500017560290682644840d506142600c8000340141000000010884481500800100381003042050740281b004101c2141e44c03000d440c119091340100c1d00d0207461203240c24004010000005011350140e41c00741c00301c0e040c00b500d6090841c140d02ca24090448141c00c20020100b82001c2c43d000341c180226072000320b8103000c03a0300d0b108c0011520119049581d1240080004109040a2042170503540c400d85040c0072503c4824031004070014103201e24124201c2000e02d110301c1c54402d005030f8080700c21019031845142000403a040c080d401c1aa10348601101e03410b40d10000b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 277109667 1250 277108417 277108453
    0x9030d0e3a0f2a0308070512010306020d020408010e0a050f06130b07140c010b0f01030e0a08070303020c0f0705010e06120f06030304050d050105180a021507061b0f02 73
    0x15004005000350a03181980d0003102c9030040c00c0642002c2c001400c605011031a846006140241043c04074002c1d2040682401000c500c400b0b0019400d00500300040008009103003080c505480d0011005a0380c1c418601c1200700a1103950b10540640d40b80104907103c110000c0707090510a4060411203946d0041c500d0803e0300d5040a0724074030203101050020380006400030aa6517405031081c14040b1113503521500c0e56503e030341b1170103090941d6551844c4042c030500c0c0c200140750250500307203801c101c540700780040241c0d01d0884c0d50700503000c0100421140100351003501210403500c40c14064541c0080c1c0d9000441e92030138a80200c5020645176800403a03181068015555515a803154105480d2240c01c031003540c0890140c4610f400d8002004046801d46941802000c440c1c4510000203282c0740905c81080019501c8584040030f4001e8002c20002d41c0c0d4070b68140d199400c002d10140e036180107034540b880007454032900c42c940221044000320910f5420444103944824160241ea0100362020b0b40011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 277110917 1250 277109667 277109743
    0x70203040e04120201090b040b041208070203070f0f080c0312070804021309020d050106060908070f240c15050403080a050403082a0c06180604020a09020309030d0e 72
    0x105034072044001a0204412548905505420307000015004c542522a041c071000d0031101990104101c0090004210840041d000a04801e2510702c0c900d040220000b5102d110301040a0300304c00111300b120060201c4035105004499028139211744d80e1104044440d242d801c01a03025807028903a100107140c240c055400d4620035a0300514404035000d40d001128001c0140c541e00741c3e040501ca08426001580034802e840141000703131100d03511945441c41280c60000a9005000e038058040c8041020402c803034448a104e20314001140903d413041e260403a140c0d40c000101a01e110552030071510890540c0c3e010074001d9000780c0e03442c5010381d9005a0792050b611f041d0380080c0007590500000707081200c035100700034100310782c0d5034950190070808401100719000701d01b540c032031034000e142488201404d0703014640f02d5800450103005140390036000140c5c03c0341c861103008203e9400100140359030300b040c13044403000342003524100070210382c000b201965460360740c41600b21100702e0480c6904407050180101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 277112167 1250 277110917 277110929
    0x1090209151c05011b03060906080a080703051b0102191b0515090307020307080f0601120c060f030605100201052e031403070c0b280503041113150e07020304 69
    0x70302056010700060b030b80d4900c414400d4515550340c0c0400c0d1041140c0800700382c0380d44026640030595034141540c40702141c00c598071000300c603072104280800042d07460303064420702c0d901818000d441740b01000c2d281011003615907180c1c0305c81d480002c2e803d41c1d000849440070190f00c0f49a41e0000c0f030340c0070910f102e4004d14150707102620079030202c4401e00001d4001e0f80155840090a01901d0030085a940846d03e85803042d0082c01300c58002040c0100500e00c2044801e00502c01c501e01c500100c0030f41e481b800c001d60164000c50f020024505820300c00c1e14043e410a0005190140c030a000c108450311009000300b10545031080b0446054648000c50500c14910100d140304850301700420364915540c0041d0b076110180e40d1203c0380014400f5a02042903442080300914008030f060b035490b07041e00b0008806c00344518090341c0782d503811705000300c1c065840303c1540d07403040d400100001000030402c0013404025810034020495030070540c1d00d1300c035004403c003030000710344900000c4a000d8076844c0060340c50380142c0c0a51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 277113417 1250 277112167 277112179
    0x206120702030d11090310111210030b240f1516170d050606040609030b1801151701022508040506030403050903060a0b10050a0e0901080109020915 65
    0x1521204010001458000c0c2450046900e0043c812001005903401006500001100400e100304035040900c8959003402000b441008000e001740354041e25405480d60220002140c180003911041c04041c0300710145802010541c2d140c035090310148101044600b1842d01c1410a191028a608000c5550615160018402e0600446985840e0b01b560004102a214214501c5083c0c000c6a518140110a88940e42c5070981d01c5070440e840005507040030705801d0280d0010041080301d02d9000c201481a00e40c031141c0080c654480f402106400f003901008402c05528151200000982241003081103a07010681d42102500d481602d41c200d0144141e2000705104c09075244500215429560802521401d502418561520080b691541085a048000c64070003c1ca4510624042009660041c9642d1003130003202c0c82c0c60042405420003080e03034014482c0200c5c03071070155802807001942c40c0001a2400c407803981e44030401d42c060240c0d008181e01804850300441c050404001d24415101e0b0080c0030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 277114667 1250 277113417 277113427
    0xb030a0302120d020f1201081603050d0509131d07120b070f090e04060911060c0a030f030204030b041109010b041a09010306090f050405010b04090f0816020d0309080106050109030206 80
    0x256a182d100c0008a00f103241d08018100700f01d04900c01074581040100444405981090030300d600e06004418840d02e070102074601040001c500240c2c3c5c003400040c80c40d106464070464030101e110500900d024914440c240100c0369078a00a02c6040300c00002d440d805c55884590391248a075412228070005003101c081d11000a042600030340542800b81d1081c034015540f01c0d41d95250240840082d1350440d50140c40d4001001409031540c0344001c2d03184d0441e40107181ca0341040340513507a03485201d001018020b0181c0280303946030107941075038029a0003080305405450710386826140c00c95200c61007072182404034004200c0c0004442a9401e560049842c554050b10302c446902003900599109810141c450308049560743c014020058290742c1030402281500f45840d056007522501c0304100d0007540751114101c04625000b800185c19a00444210380d5000d0082d0f1004011002d6000a50040c046421180406500205560403030700044001c00c0172989540044a140303a1521010b9400801882 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 277115917 1250 277114667 277114693
    0x20438190311010c080d0b031b090601080627011505091804150f02031501180501081806010608040b1f03080c010b040e0106061101020a0507141f06090b030a0302 71
    0x9902541160505040080c0f190551710780c01d081d0b000400001e0303101e4441002001c10f00f01040300c13680410040b1000c070101c0d461540415024600108400d04010484001c10749946800c0f0f2601c05254040d450002c02e0b00c40780c10410300d211001c3c07040046040c0031030150300302e2034496403d450031203500610f0030f22006c13041da084a00940020300180c84407100c0000100c1c6003a024807030f41c84111b540d50b0001d604c0b4907100601c10003100c03000a019041c071059003000e00e0516000b511a006075082400d0031205502c6111030700c41521000824003a00e07110f03c10011804c503420403140d5200d10301c0303110440003030780d0388441d4400c014a01e84000c0820985040c02803000940140240c900030400000020f901152140042d054440540050707216941d00c0f1010300080c0c0e8070000143e4000e028000039480e0030640803005045100f0f03442d001d4000103500900d014160414829091540d008241c088115441d4a4100c0c00400340f034420002c40300d01e4038030007100c3e074240400c02154a1360103802030311100386041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 277117167 1250 277115917 277115933
    0x306010b0a030f020304031d01080907060f050f040803070212030414040506010201020c07030b070315080604030e060409050c040f0602011811010e03100903080906090c0402070204381903 82
    0xd9800060540352429a03160340c40721301c0618813440c004d640385000c1500203c6201c1e64413440c1c5013013504100406003005841c0308002006030032076400380b030700c0d00002104035401c83d01341c020703c01381840004001070700240c00d440c008060f142180c0220f404d440e241c82e071502459968460351249811508076a17480b16001d1810b903120590000042c00050704e019103150700e450030810103400c00c9416503080e03002c0c0700d2039030350520030505400c2c1e200451031020b41c10610b00c199200c1008000900b001066a42450300d52107200a440040c03036451414030240c1061380c10050550003900030b600e1070081b18000090002d01c14054805c1c603800e10400400001401d0b10341442850b0306101d054140407450b4401480c0d86c42c100410074603401c030440c001600310f40501e4002e04a000c0079121410320380c01207013400042000420780c26409030702241d0040e80d9201a20116000d080c4109a100643c52840465104008413160b03104e50349100251803890071401e02c007040f0f14190710388034440c0100a029420b000003000c0f8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 277118417 1250 277117167 277117177
    0xe0105040f0510050c010e011a121209220605040c1e0806060f0c010e0f2d1e100c050a050409150b0712180e0705030604091713050f0306010b 62
    0x913140c030030301d45080f9030121400d444030618010341e180c0d074840305101406602ea55010300a03400311a481a000b8038004004d13501c032410406820308420009100d6400c1e6180b9840142d0781d0148140d0788110110741c00d000300100118820329001f9410148007280f0284106482a001c41075040c2d40c0103803412060040301e80100c020030300c1e070b004902044864080e8078440c0250a00b0702886c80041031420900b64904d0401e508118100002d81c00303d498103014100e8200361007513180399a4002c40c55400e03540361441c80c3c24007003880c1c048070b08410129052080004640c400c4506800301041c48008075406003110349100e0119940c00190060009103d40402600a8040040d900480305555902d815070010160300c00741c0308a60a100300713503007088002c0c0c102d503006001800341d00150b00c00030300d4521840c0e4401c600038100c80803c90300000150941d0780e1540a040784581100c0e54404140c00c1c80c1480e2069808013560042c20080e502000805282070f12120b1381404000d805840c80703910b0b10a404815403c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 277119667 1250 277118417 277118449
    0x7030504050f0115050406050301060605193c020d08130201030f020f0408070e04120509180103030f110307020f1c06020d090c0b2a0c030a06020a0e0105040f05 70
    0x1880b422208105424054400c1d80302003a010350380c0c001c0c94107082004a9186034032090090341801c0d010401183c20009a0346640b415044055641d00009000c440511070101301d1281c40304401d002c04c0140c0312858a45000024050582000043c0c0510907a076078500a0340d117034001800b40000405000441545003170b054818100452059400f482060070b030303004443e072046802408582002818810031003500107140c42120b000003030800b500c0c3d0700d4039034120150301001d01c8000107501e84c29407500901301c44503a1003400304c0074480d48c482ca8010a400d4a095442001800d29101280e007944040211546030758020005030781035200c0d07001d100385512020001032031041002e040201195190004013200912100000b0312005189442c1c40301200c141c204141e811428403030001030040940203801d03658182030b03c00e22580a860040c520f04885803401580500540601c0d0003002002d4019100688064a6409407143c1d10001103d040c00f55100303044403241565030030851414118400140c0d40e075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 277120917 1250 277119667 277119673
    0xa030320011b022406041104080d030507020c0307050a090e0c090c0a0f030501051305371107020a06050f0904021603170606042106090c030b0901090b0703050405 71
    0x203125421074401c00b203010141058000724020301c40d03060000f003900b0950385085a001e1818800c41d5108000002c00290140c1c2e561280f81e45c0141e260416a0005c1401c50100c031210707445400f004014000550b201c04c0948100e031035404041c0740101c0e488055a0700038002000f558a440e11050140c201c07440b5560305400303100e400340d00c0341c0c0341d03100f41ca031148a200d248259245c881c41d100403d811014007800c0201890580103111540d10860a030113414a082c0c0301103140c0c2c58081001d43c040031803c4010300750000d485509903801000d2004180c1c8220190400c105444404069064030301c111500258400000d0340f00340481c2e40154041c003107030740b040600c56040800850100b0100d9110a051103406c3e081c0071030080030550f201c0106d140e800f00800311115641816000302d80113004a0083d566800344020300036001066000d070000300c0b00d17040b9a080c03061030301d14104110040c406010540c1e81d01c8071500021424801409207040080d0300a114580f5540c40000072002000301810031030f0340d40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 277122167 1250 277120917 277120967
    0x61810050a080303090f0105070c02190906090b040b0303071a0901060308032707080c0f010314010b1b150403200708010b100905030729030a0c120203060a0303 70
    0x40c40c1c01120202802c5480021036490501035001858038100440c07071500f80e0b0401c1c0802c00c1d000c1c1d01500c01c03040d51f503054824031204040080e051100c20495003014160034548031001a42076080d41246220140544007040b0306640c0009054407449101000351040c0104000c10b01c2502e1508a03051380b2601546c0005111900c1b50340e880600e03401501e0400e1021142c80603e40340183c2c501d04040d00341d110b00f0091601ca840d18000d6511100310506052081c0c807856600042a40641c00034000b0021020032080ba41d07845002c07880c0107070000c581941c0c842142043e0074642c0e000002d49031078201414141801c00ea135903031f03070300f207504201003816865003c20614100011240410185c000781c58040001b140f0030300c034182030004400c1c844400d5010044e480d8001c221949006c10481c00b916811403410744146640c2050354000c00c9200c0c42541480000000c100341e541d21603210703000c2902d9503911202e02988420a2005901080d40d4156108484030001c100107400364440924001ea000f01041001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 277123417 1250 277122167 277122169
    0xc0714061209100609091110020111131703040f0e06060702060d060602060903070305030412110703060b0906010804080a110c03030406020105092e0506010e152106181005 75
    0x180c00c060b660103516502c50200010814000d00428000e40456002080031204503110440000c41824100d03009252645407805420310030340102c82c120078540300c00c941d00c0541c030715172001554040c450000b6100e611000c000c1502400b200700e42c1140c100c0804038040078240070101c540c103c4050f008a034032400c204181c10050b02c1d00c402074144156607a0340040c81c1850440040d00b4913500900c1c0c1d840341c0e0020800e0b4800a42c00c001a280c1181e008503000d540314146820907222145030480e43e00061052802c000704106940e0804c9900c035109855101a0f0f49894006454002e0241c80c010910300e0306010311841588a42c1c09001c0000c541401c07125881010400729007140e1085e0000380c01070b5140e10070040500340c10003902081100744080c586022804444412121044819840080f511940811310b03681c4290103410010000419900c0d0f990a04660f40c0465070151490411190f00c108101c100f240c0d03003c0c0c003a40715010103813440300a038082c001c0340160402c00038504ac600303007d06030000c191 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 277124667 1250 277123417 277123447
    0x50702070306110d1d060a050610080603012a0e0d02060d0207030c0c0f2303030306150d0204061e0f0503071407051b1206040201021b060d050c0a1101020c071406 71
    0x10302d0102070300f4085041c6503452281c06d00c5001010031201d03030f003810248891340c0c86a01c050300040b00740b1b2170045400c1e141e410020f400362a480235159a246040140101c03010f805c20359201900038191500f81030384c0088000d00040400c82c04020f54024400d21180c00041c80380c2c1c0003041082c3c424544204101032550710440955503980104e030841400c14010b000300101c11580b040503144403520b038a45002c0b200002aa2840001d0045002360340b0500c0c4455101001419505031840b010025520f4544441c00140002e0708014640800c03005451401c900031300402c0c034000382c0f020560701d061466841490540340e80c1d0030820301c0800350004102210114100344252616405c0300d6949051a03202c2d00204400011110159492030300550284030041c0c1c0c000504a41c8504500592078401000e031000403d5402500402e031511410181000040d1a0400003400c1d00c00c004d884001d4142c502c05034680c202c0c0540d90b09190745901031002406007940c0e4800f00c1c412040d004240500c3c029850321050381c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 277125917 1250 277124667 277124681
    0x25210906020618251e0f09020f0403050a0605060f06211f081506060c071809020d06060513061424070303050103030801090b030a02120102220302090703050702070306110d 75
    0x2e500d00f018506101a50f030029000e683e040c417201c0300c10440740c1030001c25292034855100707500000745c2c001200700014044400343c400464100e801d4440191013400c205000d0b0508445492107803c02c0d00c6480c850340340a0041d2000e4858092240d0315035088183c850310500381c082d000b04d5800380708520030068122446000c0c009801000c01801c0300300c10391940415101c1c0060012445030300d043c0040340300c201c00055204c1c201c0d031161180b40c00039802603e008000b0704101ca0040e410144482450f000d200460700b10408885050316210800d000e00c4c0d20040c210b62440c041d00421b03000048014079189800c007451440d02c1d6400c004601010790789031007260540d020401c21004030751140010804e1640220442d801071166403001d01000c01004006a00c51009001c002c2c404e0041001d04554039009505881e0341007141c05d15280595001c040d46441540f20340b000b28840c041040c0003a46042c40ba010f01030140ca480d030014100360303040d075032801d01800c15107460998044040c088070200f0401801118 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 277127167 1250 277125917 277125973
    0x30412031b02030711030304120609020402090d11090603060c040501233105060403030507060b130e0606030a170a0203070b150102010e06010302060a030225210906020618 75
    0x9513541900c1d05d0503c0041c40d000c0f0300c0ca03210b60402d200c00c12242409000140415602800005109503e0b10020b0001d000c0c4d149087d40028595007840100480d400c5003004060b0b086580c8203090391258101036588600310307081c264065081c0700800c42d40d40941c00c080805401c0b405205000c40c0781c1180d1104a030028000920100120000106030300c07141c2030010400d0b0340d0306038405599424000030420500c980e200003010080700241d100c0c10305c520340e841002001e00c0200210748880b0002c02c80c1c000741c2420118a180c0b40110000718405190020f240c0b883c0c207900040700e42480e25020303c0054160058065803080d404104031071000a00140c0303820b4429030821a080800b5900d0b00002401c46a8080007408107912550041c005a03482a0955190f000949005030b80c45101070081842c0e440921030b13000600303c140b101a0200420b040308090b02c050720b0034410103d0900a81d00701c62504e05880341d180581c1260001c90030008480c900d010311110900101d502481164184c2464102110070701 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 277128417 1250 277127167 277127173
    0x6080102070c0e071b0b0903130308040602070e160c1506030b19020a0806060904061e09110304030504060c0309051207080708010204081b030c130b0906060f030412031b02 75
    0x3071002041c3c0f070b0400343d0450980d150079080c2559240040742000e448100181c840144040029042c420410807103070b00e00010410545070642da8600075400390080c2c0074820250003050000728070308fc40308000070f2203940709444001c540301001d5419205181140c005803109031039071032000303107218031401060001c610480d607880c0d140c1791103a4440005106802e801658600400c114990142d12420180c0c11140c00c542045e690b4012030005001410203510040919010b000f4541d843e02554040c802155100305050005c0510707001000094441110020086442800b01b4000c4903c155003004d0010300ca03080c02c201280d241c1001418450f0001c1c00e018860340040c2003445000c0d01480040e0040a1840081d8146810210055113408640f403100440d82e4290854400a41e420407200786c00c0382000c1c0a10031041c00c000e20400c05002c940c202680541440808a0843d090850441d140b0020841d165415074440780d4502d1810319540d600c800405486812004008235031116442d5244161740007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 277129667 1250 277128417 277128419
    0x3180f020906060901020c01031e0603050601090510060503161809020703030e01050106090e06180702060a14040308040b1f0621090209041407150e090a09020f0402070606080102070c 80
    0x4020400a008020b50b014403c18042c901d0141d03000908a900003509007004a020100c08a10301c3c4c0c8031600e541101c1c101c9003401400018020b0100c1d03402d041c1c400d101802e0210360f852039080806e8200521030440017520800008098600450007a88039000b14640542006030f071440c82100010242c0084400e507178005043d01c10160180300341c00c1410741c900002d002540c540b00003d080b80c40700d80b00d20031002100d000000c455503104480f00080d003000c1d0900210a00300010002e42e12042111301d201021310b01070010700c001b0450005a80304980c5542d40889540d282d03640d0240c900b030050101c0098840e5000d010b03860700700b0444454060185070392a07075061400c5c0d170302d80303070b00000c02600e4003090078948088a0301580702e90a0041d88903400c00b104000308100500c00c54a013080ca82d015900740300c04160801c101c6c0340d111600b48032480301210240c0d0192a4175040c14111503000c1002580842859150686428160068903007940114000141c0a9a40d08401d09a80c80100c04035100e00100c08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 277130917 1250 277129667 277129669
    0x1050604062f01020409020a2d0c1a160809010207210e090a020a03060f0e06010804021906020a0b01060206060306190204030b040b0402030f030703080f100308210105040207020d02040c03180f02 85
    0x145111055856108600354010040341541070390640781d0000003008160707860901403140c0f0030000e940d2f1194560440645140c5410401e040307030181e100001c000780354031012503034403031050080d01c25064016481104042400c0346020700c4038600c1100e1020b0000714107442e07010790b8429003024403503801d002c4056990703440b645005048940c0364220700a9200c43c00800e1108000108185902c0003003030038100c21503111400002d09903102000b0318081060925400310743d1590110701c01801920408041c4845d9803558010303611800c0440e041c54042c2c4c004000112002c0005101052012005000500e440d840c3d80703944030b074541c013218103032030303039501201800304600f03040007444e01c07908155000e542032490715500103000710070142c404010781c2e114001162810460031a9a4015640700c84010b5a54171400741c16485030f1503940b5070088070755280c000099142418000c441c00300c0e90050040c1c0780c0e544135608110040c82c1c1c0c4080c5c0010140c3c0c441d10402100240d02100e504140944049842d03414148 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 277132167 1250 277130917 277130927
    0x18071815170a0903050f07080909090f0c0904020d02190803040608100902030103200307090e060a0b010918110c0a0302031e040308030a091103030f1201050604062f01020409020a 78
    0x689007030311052410301d02c1d07800309500c5400d540f60f41c103850706d000b0780c0e40800d4107000c1c1080c0140c0c2d0700e85600c05000b03014080c020b02d00289500402c503550054404030b20511040118000086a01035081100000c5a0b0010300d0714644965000101e40340d45480c8a4951803007a00c0c680103a00441c000c128641d041c000d564480e482907070028826108158035560541d0f9031252500e0340a480700d41c1d4081d081e002843c0555082c13000380040c100020003044003031030207014181c0c1c824054440703540da6031400002c00382c5035210391008070640e0801c3d00968a114410741400001f0040d0f10560300303154500b030009410603002401a440400c1c020350007143c580e6400e0b01e0040001c01e048400c41c42d0440108002c00c0016001025603074084410301000400e404a400c0081d1a00d6200301d14550502001a40340c003034812910140c507811315880101c0c0303103036a01d80051010511840c003804001c41e541ca00804e10b0403040b50010103650500d19940790032808882442c60136600140c0290b41070a40100304520126405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 277133417 1250 277132167 277132171
    0x901020f061617010f05091b0a030603060b0901050306150102010f1406091612020702010c060606120609061a0a1107060305011403032a01110d0603030207051807181517 74
    0x74074626419035162040780302c41c1081750f205440c002d15100d1b001495900125000c1114159443d55144e42d0b82d203e010010010481808121000c900d00590381c1900d00f40809118180d580160003005103899014400e2188049007101c14110340d01d41111040e103d190f406081707052100074401440c0e82c00d0081c100180494010b00104080500b0504025031030780c4508004200311b8030200c010b0380c820303450004031035424440a0103003040342405800110140c3c070242c4215588000c0c8400c0080039200e001040581d1343c01d1091800c42507442c00c0c0080d4801d040b00040c80400c840741000e07054810316110305401c0003826800403010035940c2004000840c03000d40c801400310b004030080d516204400d00c0440200d0520140410b141c0908020611184025400500a10798100c5610340310107130004854013801e46030004a006010b103c100040d94203110307008050940c40b164900c2002d0b590b1800c2205c01c00345040f080071103621002e000051041d00c5409203021850259609e211903500210420300f11180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 277134667 1250 277133417 277133447
    0xa03080a08074103090a03030608010e0a060b06120702031207030603050319140d0905010b090c07080307030f090311010501060203040f062016090c0503040c0b0901020f0616 76
    0x180e103d03002800c1c921903800201c2c10034410012a000340b0450126651203840120281c0c414000105218414000084030000203100b583c0500c00242c8450b40d007030a0350500a8240c8155210000c001e00050b0349030008111b5070380203481d0508000f81618207d01d00002036448402582000a02040002070100b60a5001c1c19904060040c0d606e15540d40340e0328802c11a8154440b0090080d00f06450b00c5644600c40741021080d440e915011282c007100c00400006504030349540ca00542940d0504003e080d030741c4103011000c019414041b41d41c50701e5406500c010422070403d50b0b00d40440d40b10307109a20441b10014002c1c0d6804102c1c40302494950700311403040c0c21030702c10755106200c00c009174448400000b05452407880c0042052030940c180403004040d10425640c503006076500082c5007044101ca110889241a01c14802002600c6040e2020b200940d0003416004640000740400d50f00a401080046010b00c100c614501800b62a241048002c3d618800341903901190340038416802000c55820182c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 277135917 1250 277134667 277134677
    0x1209190608071b0803010b090d060c0e131404140106080312061c0206251a07080c0f07031b06090803070221030f040c0f03150c020a0506240a03080a0807 67
    0xc440d26002c0e824017051040c003240700400202907070191602e2400c001c0076a40311206001c503c00c0340344013900c10f030f482c2d0354464050744040c0007000180c03540b8000d00d0f10503a4020041c40d641d0700c0d43e032910300c40703e211401c0403620f640d00c600c0001800c1e5800c10003040b007a116090040240d04008040103110016007080b0403030150000c00800140c0d4541341100e0f12a05098015020340c0c0406552161892100c2405440c00307900300f070f18404140c0d100000521070012551280825a614109000107004e507400e84110558140314000000b4010046404005080c0120202c9401190340e0401030350304181c0c080b5a07501c03011003840781454042060611190051440c100c0300c3d60304c129640300f00d000c01000f03c0c00042450000c1004e002802000001401444c0d0046080d0f0b5202d0500b50b0000c0d015110b203121281c5041a00d0360301c148041803000341944d200018000d1510b40d450b04042d5005545c0742c6495040c45510400303107540c2c51803180001184901401d40d2640420350000c3c281d000c1c010100c809000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 277137167 1250 277135917 277135967
    0x7030f0606030c090e0612011109011710090c030f050403170601051c020711030a0803010501090e060127050a030c09050106030e03070305031504060e0405120c120919060807 76
    0x6800180140c2030b5401031709070902c1542c0c0c50000610007103607081030f001179528200400140f40603260040c40701403404e0700c0b44402d10502c20310010745076030102c40c828400146a54240910311854004940280b09846c0104031ba00c50010740c901180c106035421408100c2e0491113840180c2e25142d4294070290074204a07040c44480009102e5030103005141c4119039600003852001c02545d0040105d24134170160403201011500e1404da0060303402806170b0760118601c004001010703548061860322404040c4e4444001c20b15105030103420b40d1620303107916000070010101180b151a681e456100950241500a0f00c0910b0024244103c43c1c068012100300340c24006c4c2001907a0000003210388050f414645181d036030340c070308105801c0030004981856010381030000000d550710682050300d0046004500f40c619510325500003221501c602625910700d80c1001f0000c00c01006030740003030605900007910601403100ca210a0100c00400c60300400013040d00402070100783c6070b210150308203030800c1d80a02d60500c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 277138417 1250 277137167 277137191
    0x30b0f040c0b1c0e070b12040b061c031101140903070b060402070c1205030d0612150c121812020d081f05061605330f0708040c08030307030f060603 65
    0x481021403c0c554444e11901c080c110348008003c50002440c50000035502c0e28010382d60301d12200b00540e010399101d02079201044032807916072104000340c5481d0250581d40741b4036540a882c042e042c0c048807215550707280c2414404d00046038001e0f2044600c50f01a40d036408651411540801002c0c0c02207004a20611503500020b6541180c581910382d82c8a144800300d456240407031641c8501c0d08500d05060802c04000b0b503580c04044036164462280720407503102c20b005032610f01202e0318400c46d100001d00c5540004038100050b80609005d01c00d011140003501c0c0181c95854410003180500f2005a00011f22101180d0344040c401c2d41040c06500024800c02600c0310b002c1001c02c081c05014820310700080d1300e4402228400000700307403e80c803000b55851646040a95684090025510800003216000d4041044400303100c880c800d03e50b50070b1485585d280c0a00888000030002e03c101e40b42045418081040141000907600ca000030303a030085240d44600010f0700544055034000d50502d401c1ca1580504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 277139667 1250 277138417 277138447
    0x2061201090518011e0504170c03070c060f0e0402251a07020d08040b070e0d0c030c05010c02030a0b1314074103010b06040e06040e030c1f06030b0f040c0b 68
    0x1100b80f9034801b0800742c64908010501c0080c4000042e280c10000032200401d120100c050400503000c1d80b00080c0c5565210310640384820a20f8284000500c1c00820b40c0151919a010301245044c09004050054280c118450300301070040b070075201280c8480f200141d184030b861041307501513807601c06091181c90304480601034030340180c802007040e81c407040001c80c054428504256038050080ca040c5500909040c40b15800025000507502c100c40f400002c01d0315401030310342500ca9a400360040c200089a500e4010120901400340701080f000d05038090b000c03400540c00c141a045011001e071903010b19014055003107000b5070242400300c1c0d600c4603110a000c1c8899004034022003071101d240e0b00c4152000b0000f801003c8440c05140d00040c08200801c402560072451485180145c804202e0420041a000d079a80207900c0750400540c000f01d881c0748008240f461002990f01c50344400306480343c881c0c2d01d4071082c01c021120000d404c1c50b0181000103010481c01103500804c4601c00140c501712604a00c150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 277140917 1250 277139667 277139711
    0xa060503030d0b0103090804060c05062a0d060519081504150c021507030c0207290a0e0414040303140403080601050723010902010f0819090206120109051801 69
    0x504103550f4146108264081d0b0030207440c080e0701c0100c266a9985465026024940c0e1090a9071203124520000c2c1041c40a480314030300484200c4041c80603017034203420f103069903031020102425203902d4000015450300c44050320403040004518101c1c4c00b030305143c15503141600c4a0010350700107019105000224400f09a10070341003c0711407001c40e02c0441014241d20308407800105010603194041041321040c1e050b40700022142855082d40e0b84259136014054211201114126800050000c0000c024603a4030040484c2c03030540c00e1907a0700284200028003103c80c00b0b150100507402c10001c0000301941072085001d8a035079132280c1c81e030604003910010405003001700b0740e50500c10001000d90500080e441c0c45504030140112403a143c202801d1078601800c01044202d0220300915416000326004124039482682804040e0850102c924142e0015005020059810410802c40e411b140189103594038040c0c959200d001c56541008161500040c02e403d28401e10383e450309510258800542d44500c2c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 277142167 1250 277140917 277140937
    0xa0305090d0305270f031606110a0c080307110418150e160608061005091003061701063611250203070e01050906040f0f0c12050a06050303 61
    0x4003114070140b03001ea0f9a4483c0f4481c00c6155404d03110740e0660050001c100750665542614240c4891402c2000e05075240c528000b49a000c001098003480500e100e4614955002e000b0345c2102e1441010781c5800c135080006030017904aa07000082c52400380101c40030001c1003024156001c101c410781c59841003024028405000b0084482c2d040a2541441c40e030b0864142c4100b540706642d10b40c03180e038030a9000c102d10740c41050042041100099034625013015030620300b034119203c6070314000202c401c0110b00e1400940c0c9205060baa45d202241030496401c10130748000c001070000034180e040152200d84401e500c0129480b125103005258140704444040c000343c0c0c4030f031900101f076200103604040503600170f0310749540c150940603400b180240103c01001d4140ca0080d0291105a034070740050f4145803d00b40242c5402984000c046809818560f00038440310340c4400c0001071001002e03005405a41c0c0c00c60081c1c0018a2102e40a2120743d02480f9040e0800700950041103e24502400b00c0d4a03030140d10340314 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 277143417 1250 277142167 277142179
    0x708070f1d0621041203050c04090504020a0b190e100903021504080d1e020601140906031002030709030204060e070c080c1203040b0703050907030506010b130e0106030209120a030509 80
    0x106245803142c40540d0f60a070304034511048190740114021507621003c076000d0b280301d901d009800048600a101760380c054804207034210318090400c0c0b2410090040903004a030484044100011a5020320b4050a612a880102d8101107e500344000b072920120080c443c0c031401008040411443c2c01c0428102101d6064941002800444850010350b0041c0e40c0b041840d070281107500f504041e031080700c80c8010314000311000384140035200c0480e6254824015500550290506660310740b074032000e207a6010f00001c00304d072115002ca040980aa0300140c842101190545609000f14030f01802104080c09905400c01a5881d125800500007400401c0c0038000e402e000504c3c4140807001d2200008503440c4d6044190380c3d007018544480f01c0f400450700200002d2406002c01d50825003c91820202c03a00080240151f034280200403480764007207420000c030001d24050002d1074406250300d4a00070604c1e03460060302c90060714148080b18500b00c00c00a99500300419500c00a90888140c560341d40d070554030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 277144667 1250 277143417 277143467
    0x15080d020f030315030304030501020d020a090e01050d061a0a060e0f0d0b07050702030a06060312030f0203040c06110106091e2304030c06111b100c05090d030c08040305060708070f 79
    0x110f4291f110310740014045500020b200f0032251120f030010000c0c0c08550b607540300301907900d00015001810a000d46035021502c86c000001090468016917010308004c04440c10380500c100c00146c030110340e0340c402e1001c9501d40201e10104e20301000000102e00c800e403180100c81c0c0710b507a0b4640700b00100425a206200003c1440c009640b8100010130100c1d43c400700801c01300741c90781000300c1000240440c84002070700b42151112140058025680641d0388416032003800c900b0800140d803c07560144a00440359600c150014031500c042c040c00c4070140012810010f409040803612041d102c2c1f401c0c0703c84240da02c0d03001c40010000d01c810301942c01905441c066031551700914085000c0c001c200e0054604d080b020034101000190621107404104202040314031503405000c001082c1d5000500300c001103142840300302d00d1030800c281c2c1150032070300c80e2604e070804042a80d2a03500507080f43e00252035a51089040001d00351b00a0242130b0445543e0070200c801c0e91420342d000b0284040c0c9401841800c95003c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 277145917 1250 277144667 277144669
    0x7030c02091005030d021501060306142101020412110405061f17090f0106050f060702060d0905011107060b0306010506030105240c0f0705060403030503130c0915080d020f030315 78
    0x2e18100039100c001c0c107542c03c10100782c20096440c03021031141c8501c0c5591074000a01503000303110741c2e402c64510700c02d05081000d402042024090b01c100b80038170036481000c0750f11400e400070701c0207002a012014901b0000c0d03c440c00e0030061500d080c60401e00651900e01403012603a6414089503110308100c41601c2c60f03100072041180d128944110f1200b120030004140030b000300740840e01035480d8801c4c000800071a81d8950800003111000f400807900602c04204100150812100403c1e02070444074001c04d07106c14a076207041c2140c100b81c08440030313440003151441c00c028090142000f4140700b14000e00455040c4000a01984010b2142900c00c1000d12120396100200e403090703842143c0000c6810352a5801200341e661681c020003100c0c17030240550f05000c0744d94501001581c007520b406550792425581c410080d001c6175100841e003544c1551684e00e002070b50144500954540d4555581900010f600c1d102109150201c0070303036220155000445030040000d0700000341ca922161001d05824100034140c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 277147167 1250 277145917 277145941
    0x501030819020c10080403080609331906081506030a1e060312030e010614060c0f030412020a05030613150b030f06090c09070f0305220605010503010c020307030c0209 73
    0x385283e07802003d04000a001642c01c401420710460003a19a0010742c1d640604110464000300c403582c014948034000309980306210300d0740c000c03503003071841410f1a69505400040c401c40b122114030354a006c0320b4081840000e0344070400ba900065030342280301510703a00a00280795808020320205003075940304004051240c1d40845031800844000c4100302d030356120f06240501400c0010401d01203801c0c64074003801648144550300c00c0324508400c0e0b03d022241c0c1020400551f00a4800303013414443c00f20803400c07103c0144000c000034140512002d84d5040284103200000089902191198114208110300c0e10041d40c0b10304249a403111094484603503a402040041031100740032074261042e64008420001c0000d0130b940151000021501800d601c0c0c020810103000407602c0f040004c0e41c16a001004c680a5000b0503004800000941d40e103801700d032090140110b00074810b5914548401c01007000c1c0c18284180a00e082051018514211043e00c02400619000d00000d01440f1140e000030104002d0f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 277148417 1250 277147167 277147183
    0x140a020a0303050a270605060102031213020d0804080c01121b120204080a1419030c030f03061a0901140322080c01020304050d030c0504030c0e070c0204180b0109050103081902 77
    0x2090700c96441c5d120028884001480f0490121281031801d000301e2103640c0000140c0358400450014198240c0d80c00c601580c0c203e02100c03080b604181d848003103000188001c0040c10281003903d00600201c01214001803003540016039200641d85005102034652107085603c00000201c0c1c20030649011640c100030000b0720850b03101503020b00076807601504109414007812100d208240807210740242c4004060401c942896008000ca0305a00c901400280110060440b01c080c9042c0011000c1c5c1d51042000282070a10400d9100540018041c03120340e040821000b210b00901c40071030131403810048044404e0704d07501e07268071700c01002108001000207150454480fa506800299182d040514196648800c40f80e00389000c2810440300e1000e480c807803416681100d40040e600810b0340d240400c0081502030180c404010800403218200150b1950b01440070310908480c1355030b07605800340c100b1044031813040e00318084080c1001d004001080b03036141070b1034102d0103460fa60103d4900b45c1d0016850302c054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 277149667 1250 277148417 277148441
    0x51804150f0807092012040f0b0106050a0f180b09130c030501051311090618030a03050a020d0c11060c031210050103051e161107090c140a020a0303050a 67
    0x4281c4042508100030520341c0458107010b509228000200004081c41e0070f1050089038042d5083c0165841110f185031190742050251a105000d8065520360743d0801340e00360020340203d00001084090b16510660079460080f8a2030111501c4202e80d19000e1910414412042c0c0311001040d90500b41d540d00b0a110541e00040b00e04120588520002402901003403044601c12041c040e20010001201d004044a01c1800c56441c4e1030400403c04022140c0c00208480728a004900000d6400d9141041184219402502c4050f0ad4071000c0e40f00074644414101c0078404c12449850090000314004062031002808455040e1140130345030311503145008603680c030150712417080d040c083c1d5400c880c003910050300e8003030342e090040e660794050210f4188100310f4200112003c05c000110381a80c0d52200300400c0341e40d49031108039407019034000ca10b800e1894000c4041e0642d94140036503211b800903450f100e00c585d000101814440741c10400707921545403880241c24107841c4d00004540d0725899014a103030200c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 277150917 1250 277149667 277149689
    0x15210a0f150504180804060804080d0f0b041503080f18090a06030201020d0c110d05010609020c01060e070212070305031f08010504050622080705010f05040b090d05180415 75
    0x318030741c80c10600288a003601030f518042103540d5000e192507401c07154907040340e0031602e09803405d4000c40e50010000d00075100f10301c080c095070349441d0f62801904201c5806400200b10b40440104001c200c50461000b0b006d0b03d041d588003000060010b00030f4a80451600d42d0591304c0346507501e50903210004201c01c0340d50007020b200c2080903d402962000c002e80c2d000380d08030780008803064404e0341c00c94044600504207640d003030280d100f5450701103450040c081c840c1001040c0707103a40d2001181a41c006006411039039445031400d102e07100045011580c042c06501c01803030403100c41c0700840002d110384900601000b40c00400500c0c05203100410b4a4411400c0c81e43c4ca280a5803a240c29000b4a4140c1c1d04a5031030240d90085184040ba0b4826880d90340406044006406c0040e6204065648030078004c036029506c501719502c095007240301c1c1c584540d004144041d010710303001e0010703410b00d00b80d801e110041c40410322000d003140004c1814408007001c1940c0014242142900c5108202c026600c0112811 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 277152167 1250 277150917 277150931
    0x91e07050a12060614010816020f01021804052410030b03060705040303020115050102071202030a022812030e010c0201170c0d0e12090d1a100515210a0f 67
    0x400b20301c40c5800124042e403c2044125214a600c1e200200c881c400203000074101c0000c104c600c7e40d110104460780301140100ca00d145042e01070a400c3ea00b055201200310794481e10088002e09107401603030b52000304240d000c0c4d0881034581a5606100c0884249400f030142842c183c145903001c0e0303111f00e8450340e005040b01e07103d28203031400804a41c0280004c40055080c287c00c2248a80001c2202090780e04c14cc01500f845c500301451414420b0f2681010380e03040c482c0341450300c0075840780282c110300c0145540707980344e10910b003144050044c0c915502080030358075445c1c0d141005c07036400b507090b203078441003468408215412030004842c00785444090703404900d402c0d8103001038181004018072034103480030b100340483c038400f10749503417544032400644000200810041d81c03507242480280358258400c1c0044400801035070410a407800381140c05804401040100340a6841c012012400d03021b03081e070b10b0901d8591030300c02200304200300050300714040c0884000f164084260750080c107400c0000001c100b2840c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 277153417 1250 277152167 277152179
    0xb0901090b0d2f0d1110090509090f160e220803070215060a03021305070309050319021608030d0903020f01090c15020625020c061206090f091e07050a 66
    0x604a00c0e09440240d00041e43c44006400c10110400c40d142d00300c500302000203e10302c20f102558018100810800c0301040e030228a59841c9905a800ba81c6654000c043c1410204403803494081c004184642641c49640100001a0f544d1451a80000c4000d000301d44a5000000300380d001075121302c0180010380c0401040b180c01d078002181820203005074811820f40d203410060224480d190700005e500803c0c0d0410184c1c1809560300000d401c00e43d14600015904172036118182160882c401d5543c454419000c00c030819075040100340f1583d2660741411100078a400031455032441481c80d403c15042d01d81c66980180341c001d00c00316807503030b41a400a00440c5030500e04125802400e004100e11034415a540310a4107200241640c4219058400d2420a050760f40410307001d008260800c1003144240c1030001c01ca0340300d05024140d44403014100341154144001000f4086000400000c181142e000420540001c0040c95a00e040104890f001840065004160034140e8030b0f0005c0381c00c112030107000500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 277154667 1250 277153417 277153463
    0x7120e0621010b040812031b040b030f060306011d04050c060d090302011803020d141e090102010507020114070e0a0f0602070510050403030e1314071d01030b0901090b0d 74
    0x4400900c0005200340d030b03280d1540c01100d0040740503040d85c0e80d0004c1c509081d80b1442800440d000800f80c80986100500304c0207103201980710ba0401440c8601c040188010a03004110281d0000c500300c1c06000d956040030301c8002035075041400411108440c8000c1400d1003801d000001c40744102401c45603885a80c072800901418203000c0c120015072900807406000c800c0d41140b850100d0b415806400b0b03d42c0f03680803ca4401880c40c551140041080180103600c2800c14045604000194445911402004006800c645004040109590510444400b81000e10305855400784032030400d4040000c21b540480c02d040701581004014081502c0f0208001d90001941e00868074126640700410025260844903401907100c01004103c032030100748280d142c43c0140c0c640c81a090f0b10700040700c1d4039905031052980c80685220b80890116221607500c18103001c00c0100343c0e2000c4c2804c1c88021044004210b800c08140b041d141d15960710412046190f40300103412942c2500440d144040100610344017035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 277155917 1250 277154667 277154707
    0x60303081308360301110403020d150e01090b01080604030801090c122f0c0303060d1a040f1b06050d0f09020307030308011d04030516060b040c09080d020c0607120e06 73
    0x30f078203520900b40c1503149030501030394200c03440891440f82001d10703690a0001c0701998803801c8950440c0443d00c0105105907204106c0006202c500100d2100c10794141101001d80c10780008445401400802010a8100d03103c10b0441f080b1100c0043e5500c040b0100301e44a2040c62456142c0301d0030100d2810307100d1403150014900790006807603144071500156140680d44101c2d01050450b410600020b00607140110303000030340501030840c6100e14404902040e403480d0007120b00320f8244c3c1d5225024001c1c00641d0380d0341040e201156403005212030a089003d03145005000c56883c1c810f44a03221280c903041c064100540c1c0c10360140403542c1da0f60b100d18016040c01c109018844145c000d040034100940750b01c6502c203003d20303019203403545010b0340f070317041150504d100e000140c80c410b48460900050303468510521000c14401e644440b41d80c1d09006801d410007844800b0320301107600001113814560b0f62201140d040e190711120b90a002041c030441644c0d05081f140f0820340c01200481da00000644241d080d01d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 277157167 1250 277155917 277155997
    0x180f060c0c09051b2109010e0d0509010203040905180f0f1b09040803070c12020d030b04060305070b2b02250804060516020a03030509010909060303081308 68
    0x100598868036018100c4200302d503101c00c1240d400d6516010310b12801e0060130700307600c0341c1708440c030305031040400c40000d0701c041c2c60300d2115030356075425614100000e015002c030b103203118504a440c0103800d0b00001e660780128047d000b200e0365940049680e510a9440c000090388452003a00c20605203c420191104100f6014440501800015102440c0c4e050681c030700100e001060300070350f600d40ba2141c003469003008254000340110080381d0004502c05040d6007104090030b6000b09464005010000c003a550750001150103141450b80030300c006180410000300703407500d40b645162206070190181070b0fa420400b44d81810820507000c0e405602d03040c1c0c1c006000f40b48810301c054000d803035022040c4a8192075a400034040140502c014000c040c4a400107140000303c0350080c51145034960002000044198400c40104000048010a81d6003100e1101300420305202c0400c200c600e1030314068550701004000b032920700c8007003148004100b101d200f86c60301072a0310304403080c80741c2d00c640840e110207490321404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 277158273 1106 277157167 277157183
    0xa050c0120041d04021c1506061d03030307080105060c010908270604080709110d051005030f0d1425060203010e01170607180f060c 58
    0x15003110441c04051a03602c0345802a605014040c4a803020b41a4110004001c0541d40c0c41120009901241840b06203414052402c400c09407640450301001e9450104081401e03544028111060781462507419041d0740144100b45c0d41e40000c803600400941c2c92030041c03142d401d1031000382455644200c000700d405800c541d43c0041503002541300c08980300348501007500b16440382d0f00c8840b6241042d18250f1070942040920707a2541d129000301d4a0720390310380c50403800414950088074070484c100d8a04100307a0a2885042c0c2c0c250b81300d4401c8500c40c1c86113544641030041c0200307208440441030f031281c1c03091002d940350384031a640203030b0004410040d08a800820110b440c0d2004100c4c1031042c4c800503603a41c100030400e2100403040c2c1001c100c0c100e051045d030604200000b083ca400c0305140c2030000782e56440d064001504225504102d02c442034008001403803540060b941c1d14498814560 = true := by decide +kernel

theorem cover : BRFrame.Cov 276978417 277158273 := by
  have h0 := BRFrame.cov_init 276978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 276978417 ≤ n) (h2 : n < 277158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
