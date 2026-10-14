-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2419
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:54.732762+00:00
-- url     : https://prove2.me/submissions/3244125f-6926-4d9c-a00a-f2eb3a99a689

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 434892086 ≤ n < 435071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 434893336 1250 434892086 434892089
    0x90c04090b1f0b040e011d01051f02010f0501170705010509030a06110c03040e040303140408030406021e0415030b03031303020d03110615030d0206060604090b060f070f0201080a0e07 80
    0x1c100400c2c005203104040305807101c240e000e8200c201d40418085090b034500300249040e1400300d2004000da03921491459166802803003000d4000c2c03110342303130000158000100d8011028190001042060903070002c0d1084440c241d100c0030340381c44210146018a130060180344000c0c2400d01e006801d002c0d04500003a00c42811810007403405645603c94080c00311000142c3d0f402a00042c29a900d4556a1030501851003017140c04600103490700700102a80c16000c01e201d4061504000340354210390300d40e540c41300203502500604801110808454113000300c004000c00181060841100d1025000e680203020f481408014611a070002e20845c548a000504107008694040351111030344031080c01c0540b107010b41403a01d88c507540240300401542c18140f20f0041c1311b1a03010307000c913800001c8075a0b0490300d400e8144c5203039520a800704410001258243c104c1c08045030000d007490310340920003000c081c0c281c3c07200780d0441c1c0310203086000c03000390360700001555880444140c0500c49541c118035265103c0d02c45 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 434894586 1250 434893336 434893351
    0x903020d030e0d0c1e0804030b2d0c190207090e01021c021b01020a031a121b0102070e0406050a270303180602031f060e03070302100c0803010e090c04090b 68
    0x205401200b845070507000d9a2098131700070000b0703540000328185030074240d1040c0400e440c6c20f1030000200e1b1100d11010304588031184005081c80000000a203005000d8001809150154409115020194540320600d00c5040c246400400d01c0b0384c07521070500f0a40d80c1c810600003090340b040c01940b20b01203080d040f000585100100041c2d1b65103010040030551030b80000d030813940750300c0490010165034060b03000b4071110030340748900c1d141d03c02103008020180c4994a10401c6940003095204009803040d0b01c480e83c900d505006072400075444602c0e1390001c10b000c450036142d0356115418070100c0c000f030740300300c01a070702d070401400f42800500c01d02d02c0141c058000340201055034925030082d8071035101c1100042194081000d540c1ca013417890504002d18000148a40000c4415a002600e0341c021000100c449802034080c2c000e42d8656000c02042c81c3d4450b014a05200c6100411000980c181006502030f1140902c2c5039003900706412581c2c0b51042c50781e28076018901d001e0449011602921802d540703c0007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 434895836 1250 434894586 434894597
    0x11010807030b0306192306121f0204050109090608100f06050303160c050405090304031218030303020910080709031b150203031e040b04060c030917040e1b030c0307021f0903020d030e0d 81
    0x105451071038107527034a02c01c11148071450005000b200700da40050040f12026178500d0340d443d131070310700c410219225031180105030b5100c00640380310030006401041403001d40040018501e551031010230b00315400585d81c0c141c2420005440810407041c17451303110142c10141d904006a191038080643d8078451800b0240c9001c80c85401086014460000411840c00c0c0c00d40700c50115940f80f80281c0650403401240b031048229800c1a10464414440244034480b06c1c0d58510005145807148401188461926692450366550204a0300d8041050311a80c40b95a40115524503040c50100003060306a0640080c9a804109100100d003405100c2c41d08203800040001e9400601402500200f03c11503004014084a4141c04451410340002e002100c401c1040c9200603540e100c2c0c1094103600540c994404140f05001281700801e2640c05182c0c041828011164084410008005201c03c031344500e1945a890301d100c0010540e052285030400c036206d003000e00a080072002d0640d1070b10913035520f2004001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 434897086 1250 434895836 434895859
    0x191d090303041109190606110d0807080a02130902030c0c150403120f15080f0708011b0302071707050601170105040b06010e030309040e0102190c11010807030b0306192306 75
    0x31145c5803014880920040041c40c0d665500500b100c10b4141501071180207207904c03060014011075480e4400d880710303550800c1035920030071854025008a0340c1502d854003000001b06802e4414070055004420008000c1d444e000482a001d1420708603a014403c000d001c10280300000760042900441d12480d480003140395200540190002c02001d85040c600f0740f105000012413901c0818502280308040080e81ca5858440110500340c54200b1842c03130305000b03142a4007001900c20360150213094440d0440708010900e042c06045250480c0600341ea4541013a4010440800c220544c0513403940002c00074031051519446104c0c80a100510850500000000005a941d010b100700c0d0007000c00100100500300380000b20f81c0c000e410902a440400c0b50440107a84240c0c0100c2040c1405944007900b541c540544000440d882e082c0134141900741500c580c00c050381c0d640c0510201d44a010b200030318850002c1c5480710017056a6041201400401d120503030060115088a011035000105881c0302100380b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 434898336 1250 434897086 434897101
    0x15130303031e0f240303090509070215010605040806100302010e091506070807060e150106120f0905010212070305010b040506090303070804030506010e070315050d02191d090303041109 81
    0x3030451020440c646800f103407018404041d03018640c5050344400401c482168010803d6010019010140200d40a06410011460320b001d82c50341c0001e003072056414074268160300852000d000e030050070200e100414107005c0701404100c100e034000c00c5100011181c0b440c640000e804071851110382401101c4180c0052400c140e41a609a0018405825250b8a658a00340f078030054105002c00c0baa0b850604800300c04032503002564240c8001c0c101ca04031102d07443c10030b0a079600540005a00c0200d40c640b002c0c00ca052845200e0542c2d8540038100150340c4036172034a60680d44034802402035091501d00740050118801e1542a50240d410a031040340da0303522040c001924500814070004c150103400140070003080700104d5003074101c684007051074072581c58105c81501600d00760ba21100c03540e40310447c00c00c11482d00c1c0c44206910781c0060180640360700441100701c03030006140c000a05511148101440300805c1207846071344101079102840c1141826540c1f103084100618002c1e00c00c40c00c0f040442d958 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 434899586 1250 434898336 434898371
    0x12020a0c140a021504030b0a0b090f0a0e0a060221270a20100302070809010c0f060609060f0f08030901080c04180b010311070c030b0702010e060907051513030303 71
    0x4a5400401301e9400c1d1660844000c0da03581315000c120382c483d07041000b00c0c6101959000c0c1414480c0001d2035103420341d8555107502002c41e0001c1c0000380e02c50301c41c00f00b080507080c103014104041c0d0040c2d0000d82d40d00400c05001008030781a1603050032850982003002110010000a0580212006004441e690141ca1400c1c61300808820203060318000d500d56403d8060000c0307606007195410303074400c1d041d6846000154124000d422026008000400c40070049610440801090314420708400c410f03003005481c1c82c0308840254001031105a501e40301400442e00d01e0b40c02c1342c000c01c80b00b01090000350408080030345a0040440081c144159500406d00300c040090685014148901600e0360744d0028501c610050111204080d01107468900743c3e21910780410211001c443d000383c0754540f2140307155071f485c1d80000c1c010722000c02c5550341c01c04080c0e0704d01d00744590360044030140001c0040c1400d12003000425840301060303041740e00040103006800c070307400c2c1031120032039030035041c00038011144225503c1c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 434900836 1250 434899586 434899603
    0x1090b0a12050a0c03060b03040c0b072409060b060703020307081305120a031803080a142217010204060f030c030b09091f0b062a0f0a0312020a0c14 65
    0x250900b00400c200b0305004541c040040c14140e036400f446001d5580550302c04a110a582c054500002003005102c0c0e07441c940c0c010040544250280149006181d1803958100c0250b10000826a21411070307005002260040e03581ca9282100d00500d030281b0303030783c2c041e40d0703481244002405600d0100c1c11400c42d01700c14600ba40201400781c04604c0da078080710b0b080c0c1c0d1140c4603038008401207441039a5200c1c0000da640c10384000e07039500c0f4101030700e410b0814000f40d800e001420f0207024200010030070304281c082d0038034824216401e02a0824078050030711000b011500410000303035816038414402004003d900003e98003920099050000308600d4140040300903220401150b504100d54000b800002c201c009804803c06001030200c0c002c0326214524003064411810307455030700000601001040d00c003800c05100710801101c0c2030150501c4068442800c1003010403440d600d9070032942c102400d06410110401c2604d0400b00700f10f113000c1c42c0040261421995410290400301e14040e60041e8440030090740e103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 434902086 1250 434900836 434900867
    0x12051308071a01080a03170411060c01060302181012050a020d0c05011206030206030a2c1e190b0601030f1401140306090c120a1208101401090b0a 64
    0x16a01c0886080203041c4210429101060b42402c0c0c00000715075201241e0a00c035140c3c55503d00304a80022042d0304d5400a01401c25207900c010201020503a6803003100901c2c0010750000042071003403441c0100014510955600d40400099004000d1080000e68002d03083c0c920491101c4600059802c002d490054200350094000009403809024803c03003800f05000c46200340e8030103000424201c07040054030341c14440250001000c0c004205480b1040e000044c0c07909a40002080d8154180c01c080780d02000801a00d00070380001c252302500340110a81481802c0410004010100c6070400000c00e034003031a407000d4146080c01000c0f6480313078400e401038003213803410540c10b1000d00405898603070045828402c0000c64051520b4440b41800c0100f1440d215520182c0945003500d00a0244200c4051022480e490343c0610503004000640c01003240c404410255103480e46490010300c007803220201c40e0041c60010104401144080e1780c0b1414040c1035900403c001503c0b01c01d000320a654100060001d00d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 434903336 1250 434902086 434902103
    0x1602030c06070c0c052e0c022d0607050703030e04020f0a03060f0911310801050f0105040908090f0109080a1412030124021603230706120513 62
    0x4148250f0040d01c0c1c480e1280190301034161a6610303420005007244214226494031540d0f2243d81c4204140b0b10b5280b10a80b4904051511440541c009040071901c3c2a50210342003070b91203000e000007007031056404540c10a8401500e0080507440310743ea14120313880014100842c05229140645458041c0c4016800e6501081c0c0c550035140390113006410207001c0d808240285541c0002c00c800c550103052190b41110640b10302c2e120103801c22180501c0300e0410000d0034400c01c2c2540700031149001d030b500000c1000000000e840d0074200d010728400304e0103a200b40d209a040000e0301d8081072600e401c4842984003207418108800c65000107070390880032a0f01c2040a805402e10005c00d0001101401900a11071010754901c5030002403086c95074002800383c01250303164130303514814410108444807083c500ca80100c450b41c000c0c1071407840000d02c980c1c10888100c60100960b0b01c0324000122500c402c40a4100a41200790900380000c082c88480c6009480d080e8560010032211508150500c0b44260400d425 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 434904586 1250 434903336 434903341
    0x30c08130f032405060d061808031006030c090b1204060603080d020a020105100812070f0b190b0d080906210f09190305030601031d06040c0501030b03060c031602030c06 74
    0x1507200c0c0c22580000c1d800d0320b0498a009035143e141d41c0f0030640b041c0340007024110b540c12030352035034002004006081c0c03580c03106207200f00c404200100090b6201d101c82c0200c0040e054100700c1d004080c0c5500c47c40c1c0c1028000c0c4460280321004845040e00c2001324055a51401640d030b80c01c146010300080d40c40604021000540101040c2e06900107108401e1190028015034a1b101c01301813680f4128800d4000710341200f00c6058041c070740903004140050151920071007006064584520b50b09040e640000052410321055440c407484e4065040065011580d030404280345844078489031203044c45180c85882d0002e8204501e000b18504444490b40d842c041c0b10083c84e01c1414001c0e41102541e40d090a4170402c4801421456a401e5801c1807560550307610b8119154400150084d140c0d003070444252920010680390380407020095148107a006001410000d4980000901107c0d1040705450107174104c00100140210380000b00d82e0031081482c0c01400d240b02e2550100d003075000e24080c0c10600c1c041d0205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 434905836 1250 434904586 434904593
    0x705090a080d02011401140d052a090109021315110a0f2112090f1a06010f0e010806060f211504020c0607110f1002070506060904030c08130f03 63
    0x40241501c2c1e1150000c0040290704070842c0d000703090910440e0840c01403001c250585c0e050107000540c58600c03800031507070094020b000e03d2000040010800c1d8204404010041c0c0b14170389900554014600800c04620f000140107074862036000710b000f00881214a12003848240d171107821940a04040801070b6100018245400400445540c9068030026243d880ca80d0344600d010301d200804c403100d9107503030f01000342c041c2e00320780605030443e02a200f01e82e8010500380030a100c0000b004000c0c0400c4040c0039a8900000090712003a0922001c5d03040240351a500d944a98102c0c06990304550220b8010740c03a0035109120361903070b1007400c480c49485000e0a014004441c1e21aa003180105400000404581d01c65000d10040f8001d4500380398080d401040410001c90151030b0070302d01d0304504002c0d141c8a0090101d40752409041d0060707914926400101203045c05400c0c04025088a01120301103407030700346614001c050800544000c3c1c8210000501c009801d001268140020007500850030b080b01e65904 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 434907086 1250 434905836 434905843
    0x130305040b0c010b0909030f03070c02040f11070303050709060c110a03170304050c03030f0406180302100e040e2b02070e070e040506040504170f0c01051f06050c12030705090a08 78
    0x404ea405600001c01182c9081e10201c20703503000e1241292030380d09594030404212031641070440c0681c0c2080ea600810441110b076401465202a208800c5035503070551850000c0031a20010035110400200303580600580741e00c980080412500405440d62100c0c200c0c0020301c3c105c42c564401880401e501c66164100c401050165204a0140b81624103201242c3c050503240d1050188482c000d030002c110078004640980780147c80354601000a41c407507512130b4082800100b100341000e0106040e0a0000d200303182c41d000341407201e41d081c0c02510000c4100b8285840040104032100074031101c0010507000319108011070380091511a41003207413805e114901400c03283c3c411700f110b40603605000000c0c1a81c20180121030180303a1000c2110992100032030461011340011030b0240e0001010410503425541c05d00400b80100b18002400500040500c1158040700c150360081040c400c2c240014503014101081c03c5180e0803e01c580603035665180141180c0034860584042c1e4020040301001c140c030350000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 434908336 1250 434907086 434907101
    0xd0507180608010b043c180207020901050409080c0d0f080109050609070f030b0a0308031501080108030d151205012009030c0d060231050d050303130305040b0c01 71
    0x9801211119150031040702c045109001c0e800200904001c104109035049136007021212088410914a03c0c00500480172030030036040c0c0180c9440103400a1042009002c11403a03030300c561100451400c00107501055007464144990f51241c1e544150440c140030500c400c64004004441c16528448211040500002c5191040c180040c107003400104844810303100b00c4e0f0107044002c20b2461143e03101107003120709012076901282015240d60026081d80c848071002d401851140054036102d00d00070701004807135001e100400f030400c181c00004010035a000310458480980c1004085041c20741c0b1021250f864000740d0080d5801c0c0902d8104005200040d808107a4400385c0d41088540c00c3c0341242c2902d224010600120752540140e810500c803132812050104c483c038030480c0090700301012080007003464428812100341c00c52140007108140300741a03541c1d401404041f00e030070f0600000b94a5007952030200401070859542410851428107000d441607500510060880958400c52030911038083c2281 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 434909586 1250 434908336 434908367
    0x705040602150403021b01120c110111090a0306020304080906040602030d061512050901180f0302070b040b1206030c150a11030f032a0f03190e10110d0507 68
    0x40c00340181c10588015042c500642d00b5600a04a03800000400d43c490701c217412000b41407160080d805407980c26240038142540d402a218900510103002986003521080c40200440080820001506c3e81e51a440c8205880c2c100200603107903a0f980c98500854499020320592203a4040f400080c040d03400001030080d030010580c2808050750380c9264102560341040d5060104100c0c12440c450b102c9140d224a0317000c425400042201698a84001e101244814040e900b0041c9950000241a0108034800c000c2005444e041d00e000c1c0ba007981c207120760040808103810060504041103495170100040b504c900402443d100808079090702c10728541d40315420703460208070380000040c403402d00031059a114034480e011030b519550714182409035402d110502d00e000140e01c119010380300030608014000f0070402d0540d036581e07400d0242103901017900070007950000c1810300781054020400490080407900c410900403c00718a440d80c07880d05401661500000c0518180c100840329034854003141356543e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 434910836 1250 434909586 434909593
    0x30706180303180213090303021b0303010501080c0c1905010906060f170304030203030702010e030a0f1208091605040f020912160b030c070b0402060705030304050105100504142d0705040602 83
    0x28904099a0b10202070f401940c031050111110802500ea03401044c0c01e28480d150051170807400c03080703944441c91281c1c5201c900c0da0000c00140500d582001c00c941c0c0064506241604006c035801130740d0b07920545040d945201000c083c4104080050941196094940c0040140207954450048411100c60f91040c18007103140e03e00940c100003404812075081e00d8000d80035501c1e0040b2a00190f070b040d800c1c008416003500c215a520f402003201d000720700c90194899003030328490180039107000f01000d02c080d100c004c480c0c020000b0320040700410400042200e605480120b5440c00b0301c02d000d0007c1c0510168590000e4100d80064130003040850080d003405102c1110151042c1c032a1241520740c0800c42d400590054200040350200d0528945141e0040c40141414680303d4281c2c0c600b4210307001620121060307912002803100f0340d041344001d200944002c2d035040286648203c55003450b01000343c282130184001c0c406200c04100003040c17283c0f40f440c0229000d076890030a2007008020b90b209204100c01800f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 434912086 1250 434910836 434910851
    0x204060501030b01020304090e031c0b01020607090e16050904060b071a0f0103060e03071403120906061008090f07080d090f0506070206031509180c0303040f17030706180303 76
    0x41c040e200f0b00303c80e460180c0c01141442d0400e000c140041400311031000c1c552009114a50b190403201c0040c821050035000045060400e0b000060300c0c00d14050010000c2c040440340034051540c0700580d440d441711010700d1200d240400580b080c1e410f4070822040c1500107042850210303103250705000806415115107682508001c1d02c0090480c5844169644215011400010401320b0950b4200c20b0001602c0402c0e02c1ca001e5240d5150b12018200000d060840d801c00b00d04800305102540d05594070159a001804041c9040c200081030b50f01480b0038401805048000300d840c00104103d48030381003a400e81140e20441e241c1001d107075100503c50b0710b07074002015101c01080340442066003104880b805440710341040e010b0381c01c112072500010009a1140309540104205940da02441c50082c02d90b2a211400840c0e003040403414040840c80a6000354010401040301030111000c070320454010000001c1e0707001c036400006085208034903000d04041c0c240341542249d41c107104001c02e40203100b0f0f1410401031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 434913336 1250 434912086 434912089
    0x201509060c03041410020406030506180417071a0705070b0c04080a030311070f060606020705030a0804060c02120313090605270c0c010e0303010812070f02060706110d050402040605 79
    0x528003140c403080901c8052000c24001800d0f030404901c08070044044e42c2140004040751422030300590b2080c00005c1d03d49051040303d00346100382203c0105d203602c4009007803138141c643d26070107068200e00000070074000a045c0148095403441100e440080d4401c004581407041006002d5000150242d908c0b2400c00c01041c841c0c5800070881e0f0844031400b000c3c1800d01042d480640003421001020000003d0400c002400205003406000035103102c5c800c0040c2181c101123000b880d09403541c00490181d0f01c061343c103c010601420035101150007515100709070500034400308031031809941241600b480b0201b00c60074644900018101a1b480e4070b030040103065135410400040e055030b885200315003800551104200c1c100030700d240e5030011040c075940e4070301094088040d003120001d501080c4d1307a800c003100600162500b40b1428440a1000d92403508010407a1038030b0001d1074100c1c0000b44120000980c50701000a01e800c1800d211401000048e110340e5150200c002400c021202241302d10300d04072340845c45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 434914586 1250 434913336 434913343
    0x1e0b0411040c020607020705100509030a1a060a0302180903040b030a06033014131e0605030105030d08040312020d0504050c010801140618030a0c060801140619201509 73
    0x2845469005090709850001030100b12542701e8409820044108030900d11920100508111b042c400d81c0088489944902d04c01c1500c003001c1d04c100c0c4111031000d41040940d85a0b252100c030842c65a0445001c3c0d210124000e1452290758010440444040308001070114540e01c8102200c0c000c40b1107051142e208195100052804000005444071000141d000b45114458102140c868001d07001d00c0d00400a05410b41480a58480c4025000607072000030703400c4c008441800288840d040090a650402c00081c1d2280559a03840c410440904d0014007414402c52840200300070402c4215500d1441801180140600b11429501807040380560900c070352240d80e07401d048565060b1002c1505e0a400108642544640008170907202141c803030304a07554051110300d040910031302c14041082e20300381000c0c20303e100c144e20800081d541202000c032152100401c951080c501c9100043c5642140d40c02643c561000ea101603005d0701408115214482c1d000a000c580d641010050304181d58808503d15075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 434915836 1250 434914586 434914591
    0xc030207021008130c080102250201020d1218080702010e0117071407020303120f15181e09030309010f0e0d081003170304020f030a020d1e0b0411040c0206 68
    0x4002d08000a0710603003e00c10911140c00042585520314520403a40b280300f0880d8560b001508580d500041c25111004c2d02c1c103d00e00300c90b0400008011024031600041d482e6100408894280181c003840300030050300c1903200b481c007544d6540c0c0d041100032060902c2c0d401504516412404a10300a49203425903016209109420b07207c1242d201199035000c0080703500054072240304c000c004081c48000010380d024005021406c2242c686000a4607004041e40c0c05550060200309502000000c1e40001e601d4a15402da203407144030a03035142c3c6484a800c1d0780c20425082c410350204a075280e050151400b0701000444c042c20100009216019807464480200e03054401e943d017060380900c000c030303508078000c1134026071000f580c8121131050351380c07900c07500441c2c02d070b00e11007440400d0300004200440c0780c02401008034941c02c0c0d00915410034190f0100d59054020203018002c12400061b0a02800c445000c1521540d0301500a440d641801e00d4103420740001e0036440c52085081c0b04450000c1d81c0b0000301c17240b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 434917086 1250 434915836 434915839
    0x8070810090b010507052a0114030a32040201090b09061e09030d0906080c03070e0904060f0c020a0605010e220f14100c02030a0504092307050304060c03020702 70
    0x10081e24200c00340d401800310707960903410b01c103050105c3c00c04143d0900c825042480d01500e44121030340540c0741180000c031548985414056402c81070b50301c00c0502d506482d40410002d00c001104a1a549601d10380c59080491a85c450300710309040002c070080200080c019032003a02c03020030300360301c030706031a83c003400381081a81d0010300034021070ba50300001c40121100002081809031a0030302d00c001090038820025031072404540f49160810504d41e00c070740b0003948401d034000003a085d070030200c1000f01541a120007491080b8101004181031000c00e178407843d00486040020042010100303000782d1694003103401554081d02d0100001a12036442d29014412894441c030304403648200f100003000d91103503000580e01d6010028454000403907c1d00000080039a1a00070b0460030701030a2400c003982c0d902d06d00001150000c1c0408001d030b9401c01d059609454000501140c80401c200044c000e03100700b030a40349071100e030000070320410a400200071801140108400d010090501200342e05901c110080203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 434918336 1250 434917086 434917111
    0x90f060429160204111b07060f0201020906030708090709020c070e0924070e0d0803011715160c050d0306030c0e060d0b06030a0605090c0307060e0a0b070302030f0706020901080708 79
    0x400c01031415500902c5c25500303621955080110100c41b9801e118060005c6080c0e1742d02011042c450720340c1044000282040510080d407030302e120200400c0d80c900014111406000818001c24185d5909102403c00352058800441d101c1035140c13003581d5561038910601c1c001c03d8655001c9523032b450010a10f40d14500c03c0ea4041e0340385441400f004084448010482d00402010038110031080c0d071380814004400340240c00d4a0340303e504000014085124000a0f10310540c0003a01f00205410035100f0a41d0200812050141d0a0340900f801d8800c03000041d0020316a01a907411a1802605603210f40309980c012544041880e0321010114120700c400c0d01c00c26480291201828001960740401c203030702c61005004c0d150b225001d80da40320203891003911a00300d0350700004503004c050305007048003070018040380c50803c842d129200d010801d10b80f02c60040410200f000207007002418020001c644280d02c0700162a41d80c1e03070307231403d10320025004903512500261031500490201d0b0300ca40716960040c051401c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 434919586 1250 434918336 434918377
    0xf01050408061b040f08070e060105030907050114070c0905070906050a020c0405072c0f0a0e0a0e031908040510060b0904090303060f0303091809030203030c090f060429 74
    0x604140c2400f080d490f0140004101c0860b8611450f840b0b0001819410018038116051107070725088000000c2c038450400005004000d6800ca0000d503040848000382850241d000300c40c4103030300c0c1c0ca203d0002c014280c080345100014060001d03034081840785043d47e030756404a540302c040841c0c0364443d1810003401603101600c51086071400d82d108a0308160300e030030450039901100046195000d4200308040d07a50950000000c103030f0a000b40d401c45070390411034524080c24148064450103e101800a25240790303500b26010000c20704208a50b11981c0d92801e41c0344a8155080040c00601c013101c0448180c0034401155150213000d0146c0c0043c0e942c80703811241841912424000101014602074080503168200041c03104080f43c1258051130103aa100c0001d05d00b899000c2c0101d2680d030340c0031200c4a03d400c560304003007507002c400d4907004019285038a41d1601044001250b03184050500c80e4024000580011100510f5028032401c1101040404035144083e900b00c4850042c4807220040d039201111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 434920836 1250 434919586 434919601
    0x191a0705060f0601091215060b0408190204060b040e01240804030c0c0e0a0204050114040311011101020d050a0b04051602060c07050115080c01110c0607060e25050f0105040806 77
    0x4143c0c0e2089062501400c801e650701002c841a042010703064031414811020240501e90a00a00d07000d000d546484070314280c6002980b80c0e80300c005550300320300308070f0b45001002150b031260440c0d0002c0160000507910396840c0e10501d0501002032140c81c40c4032001c0030145548819800ba00c0b1040c03aa1501e941250740e560f074400b135841d8041c2e4001110719030380344c1e100410900e916460040c003400440c40016165801d000016011943c2804180c40605050004000003031440f60070043c1d02c0001e00c0c1c40c05807004000c400c54003a0044115800f4001c1c20502008880300555000907142d2008960030f00250b151070243c0c5680d078202d02c0001006801c10302c0020b00000c1c45c1e600501e0103a104000001d007014060412200e4446203401080942d0401c1d40e0b454201d40c1e06c0a0703c0c0040010501c050000c1400400c00500b441c818504010301c829103400305824102021702140b80d40c0340d0808514100301c0000c1c0f00201c801d4140d4010180b00384d0641c409011154800c000759001da0b50103030010042d6494648 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 434922086 1250 434920836 434920861
    0x4050108040609050a0311070501021209100c06050403020309010909150b130512070603110a0c0323131e0b030619030503040602010e0111030402010e100e191a070506 73
    0x2401520010f4036980a1000200100a072001c0340780640d0359954400e0104c1d15031400d01425a0050741150710030300c260300d0450114822503e5290b0110f607203ca007240701204c281c0f100c440039000541802d01d098100818142c010004058141c0e00766a41c0c01101d0325860000100c41010041006203036041406004905110004084070a000c81041016503038403000a0041070007541606e115400031441041181d4142c0625450b445030112000e0810300b034020f0040070394201e03820203801c10440c01b00b03a41c207012064000e06c3e4600302507104203079071b0b0000c1c0c008481c881c01c0c5441030605841c100c031400e014842d9254010380540c2c580c122030f0342c0703144c41e00c1c020860000c008100720001d080c00c214001000450400c028401018160000b01e10801d05a8280c0d003101e403021070001c0800c0080040100503a4810b10002c0143d00c200c81c0c090350303407103400402c80d440080c0d2151b0329001985200c180508a2400d54498120745060164500342d9000314440758460040c0500200240d01c494085800c030b00081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 434923336 1250 434922086 434922091
    0x6040b07020f0f06160605060306070c290a0c0e030c0609060906120f0a050a0c0f080702120a05070b060301060303210b0907170601080103031d06162d050304050108 72
    0x20300e0f03103030359039286000a20a54400c142c40c90300940c0031142a400c03c050f600841c1d511600840c050603951070001c00103032101900290007402c0d07480d44492408c010f0080c0da280b02c082200f240f01c0f43c60303600d400c039921701c01040401c001d0000300d9040e00c00c1306400e140000c1c450201c5d0201a2020741820310b02c50a002d41c0340c2003100c2003984018144030711907040f1844540e01c3e100700b0200304451218100f060008048810150440001c2400d049120b81226000114400c140209183c02e05050f510038008a003000d00c9842e00c2d580110000801c0c1c0001540000500506400b441c101d100d20307102e0400305802ca951600c0001d021840d403000560f151040d010945143d0030080c480840e807031341c040f000243e114104803200e0001c104075551100350000c4580d44280d0012081c00e04d1940d550441c0c90260110a141d24100f152150070300034514151924015540188a803c0d070359184042a860300c0c1700c8003a01c7c50300303403100b190800c8500855031448441003441d00e90404003540c079217401c0000445590303a00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 434924586 1250 434923336 434923339
    0x406030b0a050409050303220f0807030e030a21020c100507020105070b0a0504060c0c022803020904080c01050615120c09180103022d0f150307030e070506040b07020f 73
    0x1c0c04000a41d58607a130007071860715886500903640ea480d0203242c410190341d518011484c1d40310550b111000040d4000041e101503a040341c0d805842c3c0c01c16288c1100e0020514ac1101d405000e00d2110108010710320a0031412680b01d85078003ea4207400c0b0100700c0e55580070302000350340001c4206070310b280103000b1001020403034018540b0030701d80302860301c4514220806881000300d0580c0d49080005000040c030480035241424503001096080d20b400243c3c59003840140c00e0030341c40e40d106034007013496561340c002c1c1700075940034116001c41d00e02824080c5144e0002a41c210240d400c00001680310315103068a94410144404224102006d4107190403440700003c0c84050702c40b402300401c06082d61003150b980003c3c1c4250825500641c15481030021542a18028030104212a00f0b8412584c0442d805c3c05141c8a059501202d40300883e400103164542600036404541000014030143c5030341900014990084001240c030215a203100b400100d2080b446a50012a01030056400518001509440c010320 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 434925836 1250 434924586 434924599
    0x9091a010813020a0f08060702150105030307020108090f010e0c0306010e010303090b0f040f080a032309090408070204020c0d0318030c06050709050a1d1003020303030c0a050f0d090b100303050406030b 88
    0x110345da55a400019640c00101c030951000080044890b41003000325201030144080718072a502d4a004641d880c042e10000074140800d5030001060380d80100602480c07101c404000703024048000303005a45a8421400700c41c024010756001180034003c1e580c03540d049a5042e42c40700c40381c2d841c022040545800006180407004001c0000040100b114601c0c0d07006001c10201810f1000e50514002c3e241844011129007005603010352641545210825160001d1701074a46007080d0342c441c64107800c036100e1000d000350320900c082032811803448006010300b86c5a40985041040080070300c25413007500c1c082800100090b000c80400d07400102c0e241c000c2030f084001818840d45258407800061000103607134010701c85448062141c2201c035604005170a40010640380030402041c10f580104c1e45070b101c01030810215441c0040c100340c010740304008442c035945050222a48071103000c1503086c064601441c065541203641c00c04030f9000c9400d0310508e0100c96140c2c40e414034140c40d00d2410f0f0040e00b0011107007640080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 434927086 1250 434925836 434925839
    0x4090e030403030819230105130623130c0908070e011203030c1701080d02100203162102070c03121b02012f0105011e0303051804020c03070309091a010813020a 70
    0x6000320006d280b05001540a4100f56052100f0702c024040c18402064660381080d10030030003030403803003941550329080c64582008007445502181d00200078000010030140303401d482040455010080c0c10030344005206480210b5920300c55903140c03000a0150304502c1d42e120396004000307406940b04180c5005075080084101c04059001c00d0395a000340d10880a40c2c101e01c03608480f460381440030411601183c00110b0843c20311401020003800150300004c1030020000e00040100855120ba82d144c0482403000d660718540c81c6082030450816210407034000a01550303030709140740070380c45884620042c4502c1085040c5260011076504071480c006040b0300c0c4541c000b0000880c40c80070040300050704100080b94a525111003d000d5142d070f4802c0800410a02c1ca05000203903200007141c02c6a0004055480d41d8541ca0740042c009208a441c842001d21000420b0010150410341d20702c22507040640c1080195000d080902c56000904100c6001500704e400089200800c0c9108030006e900207070416035013a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 434928336 1250 434927086 434927111
    0x18050d1d1201051609180e03160515280c03062102030c1005040303030c03180515150f01030207060b0613080c04090c050f12070b04090e030403030819 66
    0x208540000d50040d43d454008100818070407076142d2040b29110300d06070160510703000d5110f00003a24903440d402e0b007940302d552050a46c101003050f01c4400080a66220384100c2d03600e0300c42c2d610035652000000b1181d451000405001d02446000c0a9030000381d0069420400d1900650040ca030301400c0c1d40606030340e0744000c1018000390000003007a510440780d11602c005503004161030030540d0081075226042441076841840d03404825034085980c1400c012511000d488011b502820342c0310103090b220581202510103000000075007980220780d90034205007940740c00c4c40d00d55052000107544e540200043d07261480700d5200b0341c014102c15000300d42c001900029000001d48070b13800404080c1e40d251b407100f030900080b0030034404c140c03800004440c200724140e42c584d5884402c0407140b0480744103049498540c0c1035510361104400011090800360f0350a15146d498103000d40d0094003503628454648664207111800000840d01a00d8140c0c44009650761204414862500c0402d44680100d80321118180c11 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 434929586 1250 434928336 434928349
    0x7060e010515030105010f05030c090405010e03030f0708090604080922020f1e03061c030519030e010c05040b16080c01320615130e01150318050d1d 65
    0x225501801c452500e034040c1d0403d400d4490680040394800b50b41d00d410852694005408110b031003003903881c280765584074100640100303200c2c104095039000000c00c10000c1490038515a20410b15500d03484a0780e100e02c164180e070355808540040132504104242c46081c5440da240d580340c02c85100940e10a40c000b0301c0501c040e60000141c860003182c0114034010705800000054030700c800c034040200e04624150001a4420070190400300d611452402040e080c54491021241c91600c00b070b8031465540c007523110080080041007191010340d460054200c4000384a0b9040314222244102014106044110025006040c0c0c29084400040400007250303d00702c02c2c010f0072074090008400520b44106a213100d0108100300b004086e05603901e208000c050354980f41032038000c0301e000040311703220000b65a1010701a07a040d00402d0f801d004500000034040000c1d041031119041c2c0b540c0900c1480c0040c1ca100080c3e09000348010f00380e0700000c1c140892140710740306018221500d070320316107098820f41c1302103a0f9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 434930836 1250 434929586 434929591
    0xe0c061b031c050f040f11150304051038030a1a040204060603020c03180f0301090c05130c140f0d020d150807050a05060c03040f170d022107060e0105 66
    0x1c940101d80314104804469108899000e24001d80c0d108103890941d07961281e00c141d1b1000103140b0307100014179400c10348442d00c01d44030312040c51480c940d4a082c03500700141da0707012140d80f520100b4140110b0b810700b0201020015181d0300529501d09070098041d64240c442c4030802d02c4290144194542c038004204510a6080100d18400c1886d00f80c0c14580180819500ca5070000c0e0145801002250711000e0700000311142d080840c85944001c4014200003108004980707540703941503003486400c00a0210445a0400300d030800c603605148440c0c0910034100703880721204114003080768458800c1d41098440004c281501140f40141d01c0c01001c0142d4a04030303040b240c4d10a107180d90303d514505440300d04458600c06070440300700030a80d81d0303d00030014070703e0381590050700e0141c200481c08414136501001554081c103401e1400803106900d401d800104000384803800704492040c5951080d03038a00105040d4881544240c103269005003641071100f9681c03011900326070048c0e0305c0ca4007e030300d8482880b0b02d070b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 434932086 1250 434930836 434930857
    0xd081803040b1902070501091403010f050a020a0201060e040317040c1503051501090305071a0405030601090912030501060f0f02164505040c1203080f0a0e0c061b03 72
    0x1d48460786030b10351151032250a0f4409080d540034803000d00c0346030707080740400045620204440d44c0681c01c1c140400d01400c650f01804200b9401c04060100c11000354010f0003c070503103035000304581d80c0c6d01c82201844c00700c03d4130b000d40868560302103544034039203070307030078654818040d100811049581c1c00c03e81c0700e080d82658031440000c0d61402032250f0342452003518038074202c0c02d1038107400350383c2143c42d802c0e200d030802e22404003071266480680e007480c1044010380d4000d10380102a1010b56a64070011800350a015200301c0d00c14200481031030b000c5009200d0742e03050300c800390350350f00c0c501d071004400755110314121982c2c0e81503124405000740500344411018000d40007080768104542d004c1e05c410014488082c03030003803101ca106118861814550340040c4881d40740301d01c010485850b1401c12031112000340d08480c1801e880640e40d4020b141e000802e80303024459601c0c00c010079584618181d411203401c3c48140c49540c02c40748040c00d40b8074050300134040f002000c5400b0100120b00a900d00d00d55409900e039030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 434933336 1250 434932086 434932109
    0x9060111150f0f040203070e060d050109050319080f06090703020f030a0b0a080a05190c0308030a0915052202040e010e07030210020d12150902040e040b0108010c020d08180304 77
    0x11210350110581160083c100c0b034910b802c54202503001a8480c43d15015060304090b07124002042c0340d442c000c4407100341d900032000300851601030a007140ca0750310004140200041d80d140d80c0603054441c4403400c0c4142d15040704440140c840c68200a550b110203800034003055020300c200c512078038481c4025401a40b4400703000500f03d0149040c08031540d80f5034010201c42c0c01c51510003004c2440400c80140380008003a03149450541498003401119650700040c000703e5001c41040304404541c2d00c00840c0c0c0e405071550780000049480c0382d4080d640d041740c00002c00550340b1501071500c040f860f1000203003880244081002e148811107030342110300e20503441040d40e11a0904005606101c0e040342070442c8180b001d002070700400b00703010b001d48201c42040c0304408d9985883e280c0200024a21030040c040200c0251341e15030741d9409114201c8019542a504210b940e00001501181403040000605a54001d0308820080860980704201c0c01000b01c00c404054411506501c08107000406c082c04400800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 434934586 1250 434933336 434933341
    0x10605131d0d0207030b09031303030203040e33040b1e01030b0a0e07051303050d030603061b0207060e0a05120604140d020c131b02100f0b060301050906011115 70
    0x41403900551900328000c0d800840000b44040d0f8041002c000b542d420822070f2001e5281c07000010f180d441b910094000190901c1004810964044003c00071500080b01c2e43d002502c4012250b1400407840b50302c1014588040d010744108405040014100840204001048200d003008143d0400a00300b00305d22140007012028060744c0c052090030507440080e80c800c1281c0c1c1c10100400310590004c0c01c0b90050020205c0c0e40704d5003d59601c8020007950740842600c441c000005030140152680c1e01045800d2414a6a0204070200600c06a601c080e00c0b41d0080142519000c001d482681c5109a840e0b0064038400020030551500402990310100c1c8a0044c00285094104040d911828486508254008561451340c04d5400544aa04401e0403036892009010088580b00103021003039100c0c208000e5056078411042e00841c0300c29400d060385a09101c06544170042c002102c0789150855032251040c00107021134140440a01c0d44844c06051040e070b018003482005103810180109024540011000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 434935836 1250 434934586 434934611
    0xf09010e0109031806080609040f141005040b0703020a02070b090301020408030327060106050a1407050a030903020901090605090c0f12040809040b120d030e160806090105151f0201060513 82
    0x803800b000717041510788088a0304001c00000d441100c0600080c02c48a80d0801d10f41c14840c840001d18185100c4004443d2421201d0354054040d02c1d0803070b020b588411841001460a0340203000721004c45a02d0f034007402c0071904008103110941c000d0300000f50199802c1c080854007034000c100540c0101c1c509008905203041b022883d8451000c0d08081c90b10a03000a001001000c3d0000c2c25540b0503003440c01c0110b114500385a24860a02500c14040c0040c07269407004814590401507203400e0743d00135a1800410783e25145202c042c1e038143d01c59140c00030000e00000300300425203c0684151305200030001c0c41c0408070003c841c2c5003442501c2c10380740e080000a1055081c9428483c50b4840f5005481107040108408120f070345441e200c0300c0b41010f254640764101e2540b801031015260032551100c92401c0e0a45607080295146001c94103c40715618140c00714880496900d40c1d02000ca00040031400800b40d00c3c0640cc0741a11200700781c00a41d03480c4d00e0003103442d590703141483e80c010301403550001fa200c94114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 434937086 1250 434935836 434935877
    0xb04080c01020109020a0905130804030b0f090d020d0c0f0c1e0e070e060d060509070f120b0303091909061d070c0c140d02040905010b01020d170f09010e010903 70
    0x600c0d041da85042102d030010780b6004104000c45001500005050340c1d407031032884010b601504010240c0c80005004030070400c296110a0041c60f07011807100041c1d540c4400156202c941890110260380142d49130810188200fa00c0082d00b0301c188060151396a40340d56100c00d10300c854000380d05001009803030301115010045114000d04041c0080580e608000102074540c0c014012424041c000000313508200b8401c50700130400611015028904500d01048010b02c41256034071641d000402010505074180714a000b01c82c011100200a50f1130918072000b00403020320704009c0103a1301c2d0b6a0010014140e400f604c40e1800400d18002900400c011541c12405e1a510080a40090080d8885c7e480049042e494501c41950ba002e800c40580c1d207204000136917038030f040b140001c0d48241466201010071006412080c01c08000b03800310703100d000031042c05440c90100d10164442254049000070f00f241d41000040360403500700c9000240c9800404c83c0942960007032003041e80811103140f4030420880c48079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 434938336 1250 434937086 434937103
    0xe06030907080d0203070c09020d091a07120207020a05010503060118032616030e010201020f040b0d0b031203040f020103091a0108070605070305040e3402010b011103030f0c090a0b0408 81
    0x1d2000c0d600d40326040d47ea070848030728580640d02207e540401d01d0b000700031096201e60350b2590400d8600c0b44811107503940c0d0446407001c5a4500c0060340004402c40000458003d4468165005003030b0143c190904004580c550001840c0760b0400c12540b0340c480b129801200118091170040241c0319500311004004504d40469000c110100c1000308100c0c200a04120388141c900d80d418508800c5120440004034007901925094031560a0001800582d030300606000706038070b96442000740300040c0c07482c0070141c84804c0c0503400140031174208000b0700056206002c40890a00c141000508460351b6111403101007017003a02c42005840e090018002d01700c04002c00d600a001a290851920030150b030300402038012032040c002035501140104131420780c00320b10a8032820005840032484d02128040703141d103640f03164404002d0b5207418898202944a421051901c00c3c94200662658070345280411140340010034900303c0d480700303001248031a038442030801c004000340512140c603035003403120b0f0a0400010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 434939586 1250 434938336 434938363
    0x20d1704152f03040f0816080102041d090a0b010b03190b060915040803190305090309060412060b120a020901081c140706020f3c09010e0603090708 65
    0x8405841c59032801984a422a00c46440c2c0200d52070341019076040c6507014640101d420490302da0f03408264180000751311507404848032403102881e540c03665010300300d12450240130030311422184000e01c0390685105140d040070410044a007000e005e51680d400241c000e8210036030307400001042c0001c1c07940c03202143c0e891a40440040217006101000240d5071f215401030700d03010700d1489440c0d03100d007000711003990014010a01500d40d118841c1403103509c6080c0410140000c42e240c08086031503d0300c00400c0d107004a00c05000145402e04040108058020194084030a1900c44080e8815a00d51484a910442908000340300c0105144100328121005801134040366001e00c103134690075409140300038100061130400300c800301e0340003c09280c80c1c0302d0042c0c00745c5041c0c00060b400100501c2c1c80002e0045190300342c10465912f10204014000c40750041c1201074890100360f90103600c0001713400074030b181074050610101c02704503400420000e400c1261003041c07541000000300a1180e041c02000c410445 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 434940836 1250 434939586 434939597
    0x210050406021c0c20070512070303120b090103020f121501211101050717030108101407090e060a030b09010203060a120308071d0904150b01020d0903060207020d170415 74
    0x13100784010031050740b2003401d0301200d0052860316000a01802203a01800c4050b200c0018400b071403c03400c0d62843c680c4800c0b00010804d03814444096024810b02c204444001c1429641d41d2840c1c01b0001c00f013030b966400d20b5000120895114a103a0308105100303d9085e1600841900d40c980703225041000071120400d2240c250307158070200041c226002040107a0b00901700141c8030151810b040b5410300402d1002d99042200000200b103140002524482101904070103201e078850f003024200b60308005980c92000b0940950051204214505855a02050103410004003d68a46802e8a4001c00f0b03207038902265800001c3c0010342c1804103e44025002902c100c6a0311403ea44d8002d04048004100c002006403501c5683c48140c044803040450503401403101c8164103050800303041c004143c030344002d003080c0f92510803801540040303485212005e9580315003400c41d1450b100d130b1003c0e600003001240c1c0b2280c09e559500009480d000455252a100c2908549850820320801c00104204069600348071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 434942086 1250 434940836 434940851
    0x1b030e0f211e12090d0e0609040e0c04020a05180a06050409020307091203030f140105030d050c0f070e010e0619092a02010e1501060f08070210050406021c 68
    0x2001290842801520390507100d0741d50a015405402042001c03103441e00c2e2000005150070518540b241c8203000e06454030075904d1600f40a00180d070f8a0600c1c104040d003000043c01507a4180c40c242d4009503500254205940b8003113000303000201241d01845d40207012072800300c0c8403602da03413911060f801003400907208800c02600b0080054003e020f148288001c00d5000000685000d104140000041c480101c5521021106245c05409040041d60342000a480d050039408401d01202d1100c4c101ca81c0034024001d1341d00612003c45036070f4444120500c45100d03240e68042c600500308044030080c0040e940005a0394108520242401c5018004511030b6101410003919115240d4911007214011400090040201c04103031407205c080400d00c0140d07190041100380b41c1c1e90107400204050401009403401c007a034198407120182002c1c02a013000440000c40d0b1240725018404a175003010b1240103c80c904003100401c01c040d9401158116001e0b41c001c113016034080d0f0a500020249007100e80c0034495007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 434943336 1250 434942086 434942113
    0xb1503060610050702030703030909150506161118010620100e10050f0105120a050c101e0207171911010905062706070c0e06041b030e0f 60
    0x3050090304a910900403803011204031401003080b1040300d603014064440c80c075524100508050001d1142904e1030303041200c84140c08a01d02804000e0b02e000914490405117210b1101c1c00c51600290100c59403080005c940015948440a001c1090000450500c4a40c100a8010040c07101703008959101010300b142c002c0c85030070205280d00503846030301c3d000401c0b07280107580c603140c101c0585a0a10072403500c800e00114410400740705041e01d600355040c000e070109268100d0b83d00c200c408405401c3d0780000d0181711030f620f0046501c0500c0744d8030b49007082c5103140081100b8510003c03a14400c02507804032104100490104e905660140c0120014281080c002010b0394800003008000404181e40c0c9904070344141e0142844901405000c0c01a640b40e5010170801043c01091509a816454200c1c00c0040b2900d0710008035160f00740d00581d0710401c03e00c1e24a101c51a40d0018100ca41c1c45078440030301e0002e20707503010004c00380e50308290b60105900d429818101c0c10100680760665603608440b5800901 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 434944586 1250 434943336 434943343
    0xd030608070e1b0409090f0620030103080306061c060806100e160201060b22050a0f0e0405030d05091c050a05090603040609170417070e060d06270b1503 67
    0xc00d8200f2001d49052400c0089040d8400e0303400c403a680a20300b040715400c0c8030015004c611050b04c510020004d4a6240802c0e144100b00300020307401001003000140002090400510b07000f4030094001803c04100300d0b80f0341c0c05c00411918400e0980d07500c450030400740d0010001150003813882c904140c0e8840c100107004608400042c951889081080300f0903100034400d50016008252031003080740c440290714030200039040f03181d4800200003c0c40c00040f41600d484036168007100d003640355039810745e860450500301c0a0001031090b14940018403500d08441c0aa00806101c0c54140020703080d0426000c1400504030308102d2040c3c20080c1c07d205200131941c100c8100c0341c200b80100c503250744030740d5079240803400b0b04001b0790018900c0a454007a1503c410810001d041a501650f83e0381040982a03800c5ea56500e02e6071084082c021980000701d81c1608020384524449402810042000e0309050740009000ca5441d01c00420001e201482206001440503800e8201000d103001d10300b261030340d90019a0b03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 434945836 1250 434944586 434944591
    0x120c030915061e0a031704090b0f030a0b040f0f0b240a09110706020415140a0e0d0303023906040b150316060504031401020306150f0403080c0d030608070e 68
    0x90102000341410116543d04d12043c00039070b400007a04070390100780201150150050310035024181c0c18440b10800707a00d810380745280c0031400600180328281007501c60000703100c80030f00706540c1200044480c0b00884c9492180c248154015501a0806c2c01c013141001e842d41d40c545980810341284401012003507603880841c5089610724603000c911100c0541c040d0358944640b0758010941ca1000030005060001c0c1041d18170b50160ba078071075044010010f05491040d106100b400c04c0010700a0401d01c0003860049114200c1c240245001400c01140b1403028012280114840c150515100e004001019080c0c1e070f031158011040c1c0141c62a8200b6a450f02c1e0480d5000e40b24151034140c50801c64010303101045a03551010a481415072165900d0001400c0d59001d0300040e100005000310401d0240014002c0320301502008d00500c4060000c8500c3c100e00390000300c110596040200000400700302008085c0c0807110030302015088044810501804881d80799000725055040f8440401090301c00325001d5a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 434947086 1250 434945836 434945869
    0x17010b0901230d05010b0301050f250302040b0a0201090213110d3201140603010e0613150e180f030a1107050a170d03110d0908120c03091506 62
    0x21510080404489082c0b0004110140c1000791019a841404015086801041d001303900030004c81d1280d04400d0004142212516544404120240c1d007040c5850364012400100707140050615846092140d62548444540401030b07458244100640c5022440347c494846003030000c111620030603601140728083c4100080a40307564010b80d001d590b909160240940703040c1c0c42184410305001d002c4800180c0d0a012350400366910440002840c04c20f02c2c101c7e41640c0041c4c5024240d40c0d17039182080114440384104005098031003607080c024489400f484400390100800280083c036202c100c60a00003c0e212120940b0b40c40000d0354011113401208440c425040792030040304003020048072620b02151039008036004080800d0020300c80c8180d000425400c0107000c2501c038501e1440e00100c00ba00e0003040400340645007040341c1d0752001c0039588002aa140315002c3c05041c00395100c081805c03100b04952103041120008100a4012018041c210405a0260109000341002000f2544083d101103055 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 434948336 1250 434947086 434947109
    0x20102150f04150216080f04050a3b01030212151602101406060d06151101050601020c0148050f06040308070c0519060209210a0b071704030917010b0901 67
    0xa5038601111008c44000e05005441160560b54605e4000d104130800c0d0019000d0a204100d0b8446010104e55403141c2035a10600044550b402c5408008484a10b03420040d40c3c4c1c421404a98240c0100026043c4295a5001e46004100b040e0201a08003ca00c402c0018014036020707a034030041603400302140d00076100b0ba5046803140700d00c052001c0200250b4100225041c08010b01c4070b96241d00919102c41401c0341c00081c03041e9115400107a030785188180445001c20349110082c00e68030482c1c0d440b41c0d101c202ca10f40070351b90a0144000c402d107070a00001d0070b00078010f0300c41005d002c0c80010080340080340e036500010480ba1034185c030018030400000d07101104100351610303044103000040154100840c1c1c3e90041d01201007052071304000950110300943e019142c80140c082201e120f0068503000000c0d140d000d0a03111480e5511118014002025542400320082130146000c0a801405129610948820326541d003041c104880c0404400d21003803050f8100840d0305030b10b89402c405581101e01d0381040c2c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 434949586 1250 434948336 434948347
    0xb03030c030426120414090907030201050307020109060518071512050403050403140c01034a0a120201051506070f0201090515030402040b0a21020102150f0415021608 73
    0x880f05040c05a8401c10164803810500d801a80c1c210802401143d1000100950200411003405130302c0b2070403070710041e81e0341241e0010000740d4020401160320805503c00003605110030781d1f6a500300c4005940400a220990740444100ea40400454014080300314003100c07070340c04c05c1c40024021b11a05104129140c1c581c030104017014081c5003990042c41d40580c0308281158414501952240c550000e240000e040404103039605184c2c00c600b40c282c150500b1009070b201041c12481c01a0a0803405000f010a4a1031110744100c3c418000c80599500c1400b58031855880c0c52002401d550003c2c04440740e48a150028891940e145002c54a0312039100031080b43c00480d50006941000c202d501c200d40000100b1007624855051030000c61085100f00c0d0100b220150800501c602c0c8400c9005a2410f1130240321841d1409001850f047c0545205104a0b10184005c20321107201d010140c60142007600d00c5800d01c810402c0c02c0140c03905d524250380046041010300280142d40314600c0f1000780c02d03610300045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 434950836 1250 434949586 434949629
    0x20f0403060b0a0923070e06091e060f12090d0e09040c03140a050708031305061e04030311060f070e0607030306080a05031902031303060e0102120a06090b03030c0304 73
    0x20302e07200400400c4002c0003c085405c0c1c3c42c12100d624000c102d410700713811000045c40f940c00380c0e001c0c0c50002409050b8508107904182402420200d2520000d400303d01103c207801540e0b0340100401c122030081f0301140d00d070100d82e501d030074440324050324065098009401009089512103900e07010030f80c0449032008140c88500348131400c6403440c4c002074100c480c401150381e200440010304900240c0f103282201c4c800c0d0340d921000b5442c0e0181405040c095148481d0800c9546458400342c209881c1d800101078810401848a4485070b2150780102c0100f100814450042d0b0306c207206041d403041c0d6500e48080346103171003900245440b56211400788100008500c01c2c003818402d501c40d80c050000700040310010407036420119903a401051314081200203060300b400010b4404410f846150a0340d620301000141990313100c10150882e83c000c06442e43d400e10400081c100e024580c140211400d000c0002c0b02c80c10600b41400352000716145502a5104014014440c81d0000445003200d081d42e6002a070703075180d0354 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 434952086 1250 434950836 434950849
    0x915011709280c1e230108241c0623070f0e0402090f040203100807060219140f1c08010f0b0a12060b0d0905060109020f0403060b 57
    0x10054000d000080801031242400660500412850452849400400b40c407000c8498a0268001d10140c0c05607010404003c0000c0182580c403100c00c20741035185d4a446145a0004842007002c1d03a030080107610102c2560460800d80c0c0000d50213a0070041c0140b40700c080c10300c61030180e401d41c1c0210000c00d0744a0250150701c89688846034845402c0c030140c61502e0744004035020074110341d88610041c0c004203408a000706103601054a041e2074500040002008010007904529001d503001000030105103542e0b82c03984001c620400800c0300c0341d0400c905010301c1516210301c0d43c02000c00d562040041040c5485482448074501d07901c0304604004104001606051440d40c03481c640407885149085c4030021500074286001c058996101140d40c0ea031000004016202803080030904101040b0000d4090f2088030765044418450a0202d2403d585481c060b40c6544507400202005030365900d41420440117112050041150c010b0075820000e44880400f01c911851000910103070303a075048440c9907240e45 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 434953336 1250 434952086 434952107
    0xb03060d15020a08010e07050301120f061b030e010c052b020409050c0a02160e24191d0c040b1b030f03040303050906190c120c02010204030203120702091501 69
    0x149415910f8002e41e5601a00c43c100c28000c071000802c0d04000102d03464841c030150ba04a4424400e201c0c070a90141d00d03011070507910b0380425111292074411030314010103800008111010155000220300190391130150071510307522000c900f0800108000300c1c0101c1c1043c0c8040307007040110311000103003a1480710f00c0020b00c038541c07107094101e0800e4200842e02c60000d000d05951102502510b10442d902e04180b0700d10090350061441c0902e000d008180c100a82c0c03001139040001101c04844030240f50400501905a071038291b10380010a208240881c0a12488850104000d45c00c004118100300701c00841c10b0181e401590030040000c140001c000900242840800f000303541503e03135038510960700300301c0c41d8422502640270a0910380851051040040d40520440c1404ca42210817943d080010015008183c400710801020480450b05c842c441d10600050080a80005070b03158510702c113060504242404504c90301005015240140e00d4130820f0580c84030700110319010010118006807103001d1507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 434954586 1250 434953336 434953373
    0x30b04020702100e13060312110c090906090f0102090a050613030f0f11100e04050703110d0509070510090b0304030c06020714010e010b0d120207050d06021804060b03060d 75
    0x1081e59842260011004030140d5030980310982030706842120117080d50000e101c0200b2108111068200c0203105904c0d140d1110884800d036541c110f45080040c00d0f0100588070502a0b4000206101a40d50100549410b4500c00d80081d424200c0c3c0c2c0c000130b04200f8113489810300500c0000741982d44110340e03106d1540610b0340700d141160715000609200c514550024003c80b030a5a20078428016845d1595000c0003442c80c50341c0302081c08220906110207400068203001c00d144d1520100c090300c4581c14058000d91501c01400140c62030105481464030b08076500207030041c25034202c0c100001e907208401c0782c00ea600903481540e0b00d480b14942140c0301d40072040054212840802d02d40b0800101c218000300c0c1c40c034800300a21001c2c46403600b003422a00f1078221036510524074840400000c0c040f4580b2042c0101d680150381c160307551003001c100404203001080b55004c0c1d001a40034420781c0002c41c082049001990200f00e01424000040058031014003900c0c4074181c02140b9030100542002580c1c0e00d41172 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 434955836 1250 434954586 434954599
    0xe07050c0615010e010e090a0b060c07080f150103080703110309100201020903070b04060e0d080702091006110613080d090c0602010c090506090a0e090a0618050c03070e07030b04020702 81
    0x302500040010a01040caa030f00244149942c0c8440d50f1240d50000c660f07100040c18240207444911079240100510a01560000f505004200f000c0301c00303000403402401510058445103158a000030300f403554100c141401c07030700c148005001042c0e40070140c030328507a458109018444a41c000c41890f5008120003ea4400c0350018100345803a410340241c18211416000c88290607141c1c0291203481c00340e8001d0a00080c44800c5a4410785000b00c074103140307503008030005441c002c010b0b004105544403c960b0b030341400c40b40c0c0b6400c02859902000301501318412074080c180d64200243c1c601851080c1c650042c00c42c450100d03207448080e0065102980d503a0780400f803490001c0d5207920107406814072308030102c04a0480c40d40003c1030704011048800d5814002c00134044542480c2000c2d4030f0110252201d40709114100d02c2e0340003d000c521071040303542141c4403040350201c407610b821031600723050740e0846000f034009120420501410050032504941d142c2004205801e054002c1002030044041c00780d485013 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 434957086 1250 434955836 434955841
    0xa081e030717091905090604090602040305071214030c060a090515090106140607120c08040b0c0102070c080c3703060f06081204050405060a0914010e07180e07050c06 73
    0xb0005000e203460907280c50f0300545071030070010130400c0c0702c4c17280c9a00b00f100b09000403c50f01e01a404400410b100d02d20060401da00c94071401e16100d2113401040d00481030034008401d1101442c20905414907410055181c14560444582c81c2d6002600909a01d5203c01c000d10410006100707160b1806400034a441c001c0c41d020030501d020704100e1003802c40c074406038100c83e82203050060441c1c000680020f1701ca500b880066008680f07811440360140c0700c0100600c0007081d5402c60700d0007858590601f000150f20f8038660b0800c203400341c0141e400130780d032035200891401c00e83d1071310386000000b80c80c0404148050503005c08228851400d816280138440321601e4084204000d903804038800b58110202005282c1c0c03180021560348281c0000040c02680c1804104003e01e016042250f02c031001500342ca2105940340d8085d41500c0d42d2510380441919400f0061040c0702d0100d040a40c840c220f49007030010004907074408241084d01c1e0041249080e90000010146809401224000e4403004110741261 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 434958336 1250 434957086 434957123
    0x70905370909050133031401021909030b070914090601020c060f0c070609030506150a0302060705010203150a1d060d02060c0604030e06040b0f0a030f1a09060a081e0307 74
    0x2801c407040c40c4846a5417180c0c13032000006184945401034100b07407000c0c840c03a90840d02c0d1440b19901941128407259003c0002c028000c2c41d180120b0b80150341038403040611801c51801400c600b4000303002408005020f2400c024105060803040c0c06480191344507200c2e0b0302d61742c2c0100c4c10840199aa65040700000942100e903402c030400401e108200001515215030319544102c4588819200242a0381d2009021440880010510000140c0004c040d500c1d101d9881c1c0c00301c0c0741c036001404103503110396004c010000d014a0640411003400411902c2c6500141005044441c1d00705604088a400040d0800160f10f500e42a80c125130640d0010000350f283c440c00c3c02d02d982c0d80c000031a004c5001401b01030f860001810020240e4043e00d019803481414002d0140c444030a40e00088820410192940c1c10034600741c03503a201e03044500c200c203840c6400d0440030006009a01c1805414140540c011200c00c0100c4100454a60780458442468078945440c4400c0d00b45540101c1d00e011700317032403032281c1c3c582000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 434959586 1250 434958336 434958341
    0x5090103380a050607050c3a030e10120b01031503080703110313030308041e08090f03070f06050703260105090a0c0f12020f0f030709053709090501 65
    0x41d800c11200003429645034820300c006406001e400034039562014503da4503d14000300e51400044c81c07030b000050700c1c030348154600507495581d007403030f80940b800700d000e21040c180d100d0021280580203407058400c0b56402d940050070b2140680c901462160365580440c0780d07a1098220318207600304074400203d05a09c9050100803076100c1a02140418003000d0b071b00c0303d03144c0c020080d504580104da100514180c9180c6054400004c020000c03226803905509451350180000d02403906203010314100381e112075112007031004031894400268801c0e845040d08100b80c104865400301618001d06d002070f216101d91a082d46c0c3c580c031080b010611003510ae20b20041c54010420104c2c101d0710101c0e0502441c0c0c95185e00c004c22a41140c03036900c0060401d0010500701401200c9189a441050b000149002100ca804070b040303401c16100b0900a00002052000842d842840c0a01070442103c0c4502d00c12101518140440f039500786407800034031303021091103420440d103544900070701c1100740070b0100820600d4910300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 434960836 1250 434959586 434959691
    0x203040c080c240315190303030509210d061809030e01030516030518250b030f07030e03040509090a06050115090b030a0b031507120c05090103 63
    0x54450b9403086111440e00f00c80f0741ca05038500c28084641d50050910760111036000421110010308049111030058858280c500c40f810b0140d8440c4041604524000b001e85501a000f03540e99400011042c2c000303c14540c2d0024030f85c003120090360b695034090001c0005807549a02c12207403040c0c16590804280c406410091308144260380b41d101c4048410019801c0310001d54508980c000c078140028034960180c3d001641022514051146444502840341d2400d94084030501d0036a02010100c0c09005651082d00054203540030310a085207403001c448038501100030101000c05440d14541c41c40c505041c01182d02600d00501022101d107020100c50359106625142160860314203000010b1054a012401c000420f0b03d94402e44082d00c0c000c07a5803103940000e0a05510079568441c44001079a0421004804012440d00f0b03c80c207203405074026148500d0100c00c495482e00746005102c01eaa030010858408840c00d00b4005080a07000965844c2494500200c3d11182130b0090714191501d01d6505a25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 434962086 1250 434960836 434960849
    0x618130c080a1b140103050619092c060402010c03050904291203040909021210060e0f0105090c03070c0c14130603081812100c09080606010e0103020310090203040c 72
    0x802d8410803960044214003e03200b481452080780300040280d43c0700c1c0c0c110f60307000b00f00241000694140c0170802000f550955110544080d668494100300e600e00d104008540788040010042014030f19034016110b40740100000c0c1000445400345003014092002c0c0c1c2e03030060000d8000c12440580382140c02c000c0c1281080707900921481f0504901614000002c0501c0041c1d1501440c1807600e0070f034015015100d2090308136440740c0c2090f080c50080342d00300546403042c8902040441c40714980054107208aa020300036440c0301c80b051006200356114036440c01d800c1110722155642d40e0741c602c80c04540000680d0340040c0701e00742c0c1c8200061005814a03107900d03002412200301415014845902007142c10131b01c801042900103003d11490800900c84211903180040c02505ca6600342c4a001420405540c1580c121b85e50346084440e01d0036401306480c2d019003030704001003a01e070800308000b82c051038031000f034141050b8000002842d490030308943c1c0c4000f010849403d544a081600c1c2c138090b410340313502810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 434963336 1250 434962086 434962103
    0x3070f17030402010207090e0a1709010f081006080414030d090c0803040311240c010501090615050d0c02100c05030117060c03041b05090c0d05070203030618130c080a 73
    0x51050298400c4034002c0798140c00406241d841c02c0050f1001d0500c0703d0840056004000f9101c000c03403e07480c06051200880401195940761140002d010000620566010004940100030b001550101b0b60300546005040108090351144bc2c001101032045036010492300000c1403845c0d441c10385800840c0300c2d61141c045c02d20382c00d48496105071f8038011403101030048800e00031031400c00d04060040300c041c0c0110392409601e0741ca0844003203035150301c0500306011070380d5030303400421690302948100400b07414403504200f091960074038010094001d0a60010380b03540d544800b05142d60080000c48181d40f2010340c20720040701c59202c060003035007003442045807142c1c1203c140706141c038010400394491810f6581160035a151600c5400d1440340b16094000146454a808140340e662110054441d40b28071103181e5907841c04140d824160382001d4014003c0d50720500500541da40e90f00c1c9159002c2e82c89250440d10345d500c02104402d160954200a001000142804a41c2d0361010a11102c624068a0503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 434964586 1250 434963336 434963363
    0xa02010e0303090f0111030f07050601180c0c150905010e240402030a080a0903050303010e0a1506020606040b03010605150703020f060411040c050d0c05040501090522110c03070f 78
    0x28540c03684030b03240710f680d031240d0240000116580070b5070750328004001c0b450859003080b0414058401c2079001c007005603107640c02000100500c0c03001403202c60302e00c45010b600380100e01c05900080c140400d020801464a5480e02c2070420b004030a034082140350350400000e00103c940348003015203a0001020705a00300c00800451400f6072008501503002e40c1d400307001000f8440d070548804480d0340100494000f045844c001c00030114208001850280185008185003814849004000c50342c0b481c190704003884d01d0300381c1017084940200740107130b0081007900e004c52841200b0700001c2c01042d107600466840440e611442c00e031801c103000600f07101403094086030481948404880d41d5080100c50003090020a00b94060a50500d0703084030340180640d003061818040c541c1c01050640c0e01c0c4030b64450001c0c401080c208280d60340310b00f1420007400e040c5c607100d1318001c0718a5881018840300b024402859110441000714080042c120b075a41411807094a440303252503d021741222200c1c84081d21420341e4640c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 434965836 1250 434964586 434964589
    0x1090305180f0f012d0e0a0518060f030f0609070519080604080f160b0910020c030702060a1103040f0e010f06020c0d02150a0309060507030603030212160c080a02010e 73
    0x684442c07050340104001c6841020303400444020b00310f080188440c2103400213944110b030303900d508100e2aa1aa443c2e9464122081e010300c21524100e600c03251044c02411940030ba08200b60502580002d020380340c044994900b407001ca07142501c0400003075039038840e8100700170546001280c0340702615800c540170b540c01180c1000c0b4101241040c000c5552981021003c140090000380080440000c00b44070241032081d412001032a0800004050360145214810014001d0307040c40240c2003c496600118284904c19500c0d6640f1700846400a018a000040a91115014020802d9502c0713240741140d98803034890401c0300c4802e070244100001041540e001003404030082c49142c045c1c0d8102c0d401801c05c402c000c410490218000c1e101a0707001890740048001307040c002c1d402041003044580340070a0903961882c0940031240d00030610010075240401c1400040c1d030204402c0c511121030b111641d1102d0606070308901400c45542c0081c4445a01d40c00001c05003404079610f0000c0d4002d8030790b00c1180e90140c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 434967086 1250 434965836 434965849
    0x3030212100b0a030c032a0f031a0f130518070f0b07030507060b13090309120c1203030b040f060302040b030105010b090402180303070b090d09030803070f0e030109030518 75
    0x34416400e10148070007020988241d000740480c0a0034500810046480801c1134182c01d444c0091f07007218401000105000b40c0c00400058801400303144c00c020645540c59001c140724640d402c25440303596020700110341d943d100140d031005582c2540c8100400d0510300c80b0302c00100e05041120005004148001070150b0b03100c03115004403410740a14914184555a0488076603010503001c5568503601c8900c10542e841b503282c1d100402c28585030018041203541005040303040c240d80301c507441c4001410444000344920034200210b03801717540540b410800b2864182e02406006800a4200346003c2a8140c1c07138407560070460440b80241c408100f5085160149800d0740c009015800350741310100101901030426500400c1e104a40d1030a02e4034003801c2d4000207081d60311a0000b0780301014107000740303c0c10380428444244e00d6440d40c02e00e81080b9103180d0700c0542c03500004000106120080d030413844501d000310315005c002038004001304002e050341e00c1c0142a40e0800c441c51800c00091030599402d504001d07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 434968336 1250 434967086 434967089
    0x108030c0304210506010801020d11133b07090815150303090a141903030c03050d061e0f06110a0605060a030b0405030406030f180b090309030a0303021210 68
    0x1801951400c0c1c00e20011500f00103070118218508039030030a80b1000301d84184078103400f0f0a0144005a9a42c06a0504d10306807960014001da030901e04005c0822480c00e040741903c212070700c50003000010004c0c0075450100e030900c004c3e421094404600d0020103040303002c0310144940800c0d280c82000d030761200d40b02c503a2080300808500b07400c0c000002042d1403042e08550000000e41c001c0440389440e40c1c038804a8503c075401e0b80003401490241c0b01300720036440c1c0300401020725085000c03803900403495510000d000d641d880d4000b03810700c02c001944441403403664003c2c401030810080d8950700c4034401c0000a01848440c4600c03c9001740d0b0380d5002c12054805c071101000d01d44881e005280c040c010341c8483c0000c1101901155010321081c0e00040010181c007480d6209500480241d82c07218600a0060143e0350030400f8612090b10b40f18580d41914800c0a828a0140e0008915141e550711a0090381c614442c00111680c1841085c060a0406a1640042c10004145045d5009a0310b030744101d401800100d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 434969586 1250 434968336 434968357
    0x31b040e3c041e02060315030312010303020319020c0f0402030c041a0a0906081009051009020d0608010605090609010b310824130510020408010e06010803 68
    0x14a0210700404031441d480342000241400350240c1d81e6922501c120700458044100090220321410041071208009014107980b00000b088625480194009082e40c1b00017441d40141d1220f141c103950440c1c4003001a2b820710002015803052551312810301a640e900b0070150344803004034040300301040c1032000c6040ca0404001404040a002032401000040e4000804040c1420024000001c91105085000b40c52100340c0401c02c0d07a5a03290080240784041c2c540050702401118001d009011301c0340c8600104440c8404000036064440b5295031102c4107455000500d00e0740081110645a050369201d4011039002400820a00f942d800921880c07990403100a640054001e004200500201c4001c0007501c0780e400c9140b4044c5800c00607048405050300716002c0039004800c0c01c2c050340c42c0420440000d064640040d0384150340300c1140d1202c452006000038050200c4044070010010304001005500074144429500c0e00d8031500c0250081c940e042e40a407091160030f000250040f0084110b4080008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 434970836 1250 434969586 434969609
    0xa020d0f15090e160b0a09060206160e040207021809010f0509120901090f06050711030307020d150605060301080f01050f040308011a0f070b01061409090f0604020c03070602031b04 79
    0x68031900c02d008010201080d0100e014503d9426410030410812202920400724080d4031480030240040042d400c0360031410035075110380203219600e045107a10740c903a680c4a1030210220301c40742d8045006070264101c000c1d00040c2c440c00d09240360a0040c2c070305d072088141400820040307600e41368040a03100e059601d6601c0d2382000c003650503c464840020920a001818507181243c1da4160f4000451080e601100000308007154070002c11829a40075001c448045000f10305240082e00015124001c10000400d454862200d690120196400c200001c0500a081c161250307540e2400903201c1c100d0180c00b9405500e01000a0809030400c20030900554040d40c0f403548aa0a044480c25100c1c0714500d500c08503c41417080154080d110002030062501c01c41102da801d51601e04060303e0054a10004060718209000e1a8295121180170b0b6038050412072401d441c1740c841a000c90001c0c46500e550f074129002c00107008080c000207800440c000c0715910400e910008009421102e580128003d01c2e10000d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 434972086 1250 434970836 434970839
    0x1205090d030c0e0a120204060b071209060311090d03121a1f05030a091502030903070c08031908101e0311010801050f0f01200114100e0708090c090a020d0f15 69
    0x140c4281111715244098400224543c0740c20099001e03800070801200d505248000b10100943d0210b44c0c08000e106900302032046c4202c541204146009200034980595400c040030414148114a881c80554881c00c081000820b8003041c20a04098141c10900408480380c0f812103401c503018400c1003082c01a640c950440c0c8402c08160301230182d10b941a61845208180c05a0841c0c0c180300031409541d00800840d6600e0580c600209240c00562210348aa002031003203511100200403d4038500005160012030f43c1e41e142c0b83c0b81d44001060b0001c1d003020803001840100303c01c0c101d1035001501d0103030000d06014503000c40111012030090207a190080d4000b20302c4020350400b81c40c0d1040f841c0303050516a11302c0003000801c420030010b400901c0c11a83d19008410031145840706043d410203c010a0f030f08241d41010054591450040d10040401c1007070f200043e00b01e6800c0c0000c500030b107030061240202c0e0802d1903c040194120200070b00036280b03481000c4011580a00c1649002e8007100d00110391607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 434973336 1250 434972086 434972099
    0x90806150901031b091103190e063705091b0307060c06021615061e031b030b090601050a1205070605180307030f0b06240a1205090d030c0e0a 62
    0x40d0f403002001e44c41500741000400c10315464000c4404820700349450580321b141607010000c0085420300000308103413800d11803000650b00454465031103490b4101d461039884900002004820343d81e00c210201d184000c5c0c5030ba5100b44290001030091403440d0840b2254500724403500c48044c0015035203581a4001c10081107828050842240b8003400340360014100b41c0f00c0d01c1c4005400344510011204401c0050300d08910702002c0c450711019082d581c0078282c01c00c0b000c0203074000000b1075010240c010044140740c900101109281c18003c2c40d0702640182e65410101c2081da56800700b800343c6c0381703c0c450080b000304452003250001410710750060020030910386441000d83d495440180d0721450000c200e800348140d6141042108020351041002c0c40880c0c0c11810011186500a05081d104031884010814800c0031490b8007068016640c5950b5982c0d41c002e00107440950040080c2001da606000030000001008960030b2444451610207202e84070f452481184c8602103100c5141e4403d00c2d114081c000c0d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 434974586 1250 434973336 434973353
    0xa060b090121060b0d0302070317130e0c0403050d020f06180a060c0e1008061003020906030c090616061505060309070e0901060e04080703030e0601120f02180709080615090103 77
    0x2c46000e4100020084c004070040b4a10b00c1880d0b000f80d016a0180004008100565455410103080164003505161589070a074981000e90321a10070f005081602241d200004ea2044a00940d40402150011640864040d4841904c0089039115008480000c3c800f000411000054540c017100038104c00c01d100e5917220002c2c903040302d00804000f0b0700c4009107029210007681126424a40c1c0b51821540b038280c003000328135001007038890109801404083d072641c0b00c0009890b00102c00340000394032500c0d0b50010510134000c040d4925010051098003c041c40404d504c000e8102e00c40c21b007145640b0b52030b0814088503120550340440907a00a1408214091901c0e00054000300a28000710344555240d41008905000751010f85d0035110005400003090f030988900c040e440c0c4a10007828066140803003115000e020703440301412040c0001a40b42c21507440d404e0310401c00c840c0501843c11030810304801890f1030068000c024581c825007000c02c0700c2d5007100b80380b038060101c0200114150f03821940caa995 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 434975836 1250 434974586 434974649
    0x908030c0c07031218090615080702160b19020a0803060f1801032109060e010f0c02030106030b061011060408070516080c010e0108090a02010e0a0504020c0a060b0901 73
    0x800340907001c8040001182e1001c20108030015170b60340d81515003010f000c0c0c40c4088540d030060b591549016020049080c00341d80e03003601900a420014055541c0750300c00ea003807007802841c03007400d502c00c2000464525101400781c05140c0c03000d104c0403007075001141c0699844840103030140442d242400001c06901d4100020800ca0310f019081c1041300c6c40310304105400d001d082c5c108407152002003207450048001240481040c488034a8400742d500c1c0781480181140156100080c1040010030b50f0300501406910844443ca501400030861a81d990504200c1c0140c00d0318840c1c40b4200c01c030b600b504154814a1060300c3c000001e00a082552103640d07450032030f980440400c6030303140100e0320342c00c1d0920900c407229401130142d20050240c2c481e42c0c40c00180a04501c82641e81804080c00078046510000154030030701d690f0a080000300c0000500024030001420352100394003d00004010311030700801301f490302105210b00020311100440710104a0500b60074040d1a01011a10640528110b0031074107104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 434977086 1250 434975836 434975857
    0xb030d090e06120a12110a15050a0e0a14120f0f0702010c020901080c090f07080a110d06090f0501091407050d15030f120e10110f060f010f06030908030c 67
    0x5140c0c40c1c19210301070421400000642d1703014548100c0800494020b0b80d02c44090349a4000740c01a42c40c1542c3d29211010301e2181241240d507104001449103003540c2c001e1070600441811113803044011300d400c542c5040030345040d0104e405a1803074007006c8105103054500c05040102e5041c101500201100d006400801c02603041141c0b0000c0d0b0030268543c1c611040c0613120071409480e50f004041c0500c220550054804040c40300c0100402580542c007047c182d4100300d0081c40401c41c801c0460a20005004102d0081e04c03040c60080c0009140020340d0220007950b100510a019170307079903854000201c0c1e015510507032140c1100c000007058079111b4002840b9480d0741c8840000d081c940e03c91000d0512802c0e0f0821180e0030840e2000e40107016072001c40c1036005909140c0030300d1410304100840e82d1100b0011440050091400300c041074403400340402d070040080c2e00c0c2182ca592800d0425502d81403401c0c4900c040c0d98240440200d0054406d014116607941c001c03c0c0c0603e50303292003001c0c0d02075a00040b03510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 434978336 1250 434977086 434977099
    0xc0711030106170a120509060d18080a020c09180c090c0d05010b04090b030c0102280813030c0e06090403051b011b0215040c09020c030c01020c0307060b030d090e06 72
    0x100d032441820000c0b0303e1901c407000040083c030000c1d1401440742c01c500c45598051210501209105030f5400084a180106555004c1020604070b11000000d10001000621501012524030304c46540058610529202100c000e11552281b03185a2002c181004c2d0b99000c580200403090500c0c180540280e410861211445107404111a540dc003200d501380c02c28030840030002030070404a0018014600c048030210054160f40c5008070000c4d55424544242c0d00f01010403074030840d5014040010f00d00d105030481c80403956901c14217000c10f008002d9001c120365140740030030089203002074441034a00c14800605490842d8486071415030399500203001d44200c1c000340b1101c002c4141801e000340c0844980031709a144000c1e01400300a400c090034500c603203074105144020040810758642001080341d8a0400040c2d503030240906890440c4038400c081c0480790b0001402440c8030714000001e01e6214010740d001c00585002c02d080580320741003805000b0000e41102400d100c03800c1c0c5020807a82090008028 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 434979586 1250 434978336 434978339
    0x7080a050409020f0301180b03100b0f040504060b090705120121020d05060a06090903051207090503070e010302030717030915042111030114070c0516030b07090b030c0711030106 78
    0x60001d907403006042450411340800104110200701008881206000505001c1c44200d900800d941d0401c03002e032460b80c243c0b01c083c0d0300c06079141c40c042e41c02e1000c40648207000758a0181402d00181480766166402011041c00041c0003d21540135031300608010150742c440381e40f07840301580d00b40c40c020050042c0030003010707814401a43c800d54161000c610030400b500c035500d002030186040726841e602440c105402c0c03000950009a0103401c9600c0404c10707442c00c54031911100e4080b00d80d50150b812030758052098120101c1c600c10310108240c12240b003103040f51016a1281640108200b0070749200c2d0705a8028407081e0350503c0c10702c2000482616507400f0307600300b690f2102030284520000c000a03610301001740903103091140003044140d2880c0290001c0c880d030178222840d61307418607004240b8000c129160040d002044030510051010300540061404c071181c0700c2c10802651503054845002040540d080081c45140242c1640e110352252040c050802c00c00d034a0321a8041d00b01c84e0703900c4c2d1555036840e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 434980836 1250 434979586 434979599
    0x5120118110105040b1803010b010e0a031e0606030305030a0e030421020102010f0c05070c09050c07030813020438010207090906020d020c0c0312040e06060c01090605090606101407080a0504 83
    0x1400004c031185400c0442c00f4010007c2c5803c445000c01c4030f5040003400c55001101780c850012a2080300c0d44004055803010745050400128140510010909070600d071001040c5640003004e140955020704041040500c048101a0307680b1451040d8101c0a44940302c8400000400007020125030060002240d41440c03101641c00300d44011320010302050b40850f2031014080710070345403005440c2c4948100300d10705002640c00c00d20b014500c8028208a84d1000290301c010a41c403000381c0303c0d0b90140c802c1c0a038000c603100904c0d400c070100115084100c020307005005407454281440c48043c1c0107801400c4d01900f44104000646000b03442a190160208944030300088a84000c041a10182020705641c1e203112082500340306800b400300240c000c0500c410301c448501d031103190b90401011680c1944c0c801c0b5041c411405001076880107004541b0b000c00300241c0003000310361107216103011074500202090700c02090791000b1602c3c0808150702402d0003500d0010312502e00030185019642005420030340e50b0710 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 434982086 1250 434980836 434980859
    0x402031f090c0f1a0f0d0c020a12090611030307080403030b01090305150103020a0f0b03130609051b030c0a1a0a020f061801140c0d09020114040306060512011811010504 74
    0x14885441c040d4408030030000508102e100c01d42407540c00030110301d440c41d03420310304980307006e0101c07a501c00030780d0780c0404c400541c000c00102020a9014401e6480c05817260b4001d00804594420200070501060721018000404811607104551075258030240e034a8607241100104641403200341800100380e8040082003040001040188510960418642c11881407000403003203076110070603d868032042408440c04200c10740e0381c820341c6041e00a02540550400c1400b0380b14140e0080e10364060707c0d10b40c0319a801c281e944651294070507000c0314140f203203040030300c6440360302d5110b071a160000c404070b2455292155402020241d15900c1202c454000803a080c50508809031040813080b00041c10514206c10203026034081e20b201d03070812000e2494030b151000702502c20902e03036801042d0f8908441045a0080054a0740341001601158070f541d03e92800400900050148520a003c1552161180b000500607011130200c00e00803100e0000169880d03195000314a11060305000003130101190958200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 434983336 1250 434982086 434982089
    0x20c010908210412140d03060501081504110c010209041103060a061101020c0303013209060d1403030109090201030b04090f020d030302070b0a06090b01020f2104050604030b0417030402031f090c 85
    0x41c0e030051220400c1c00c5c0e00b0343c5800e010700703c680f0a050514000300070310ba03005000951301040110101009900d03c1001070010400700024206440340460034100464055025014450003650b04200341520107000d5440c0d800111803403607200c401d0352020b01031180300b51a07290314410240c0016040500078050305003982c00907004041802c1c2c3c0d04007500d042e204484004441e8a5141264161503900c1d800032440f2440b00609207070140b0740c0ca80e0502c0800c5108900104202202410f40f40c403940c56009050113801c1d41c100070b80c0007074100144401645080e1141c0c0e40007a601c04a9001c4080b038941c24486034400000c000c0d014180d003481104040390a106915104118038040010145d044c4410142107900004803e41154011001144e04800004074020746403035603c00300c00545144c20b102d045510540d008950042004a000002c2000101ca0203010f60700c10070062514850b0400c50a80c1400b08640103985031340140b021176080d02d90686d145900d00b0f00c0280220348041161035442c80031005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 434984586 1250 434983336 434983343
    0xb0f090901060503100b04030203330c090307061b06091b1d0a05040b0a330602061b090405040c0e1905070302130509091f0507020c010908210412 64
    0x41048170305026490f01c00003900080c01b8041c142410360300072a9641820044110030714001e0842038140c1c00d0020300e4401202145440603110303183c070300c0c4050f187ea008a444c643c0203100d800004103c05000e100b03c2e0004480e24a5012070281031922001c014102c007020030b41d5540188a201c0440015600302030300a0001c0241040c441c0c070030f01e20f4103050701000034034041c042c074135010a22001903030203001542c114401d40004126020701210110f01e54070784104031024102c0410341701c500b508540458500302d64950302600d2142d40c442d105140515140390800504031020000c030717101c91030691700030f03500700d401004041c140c65142d5098440304030095405156000384240c1c03a0041000d140500b5078450740303070719095003440320a520081d030742485401890311400812002a400340b43c1045401610b100300e40c480c0400c00310781c01c000f03002810261207010050140b80c4041072070794001d406070012191030800801805650151610741480e035000c4034400f110b010032001074081c20103405211210301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 434985836 1250 434984586 434984597
    0x28030212010f060f0801030308040320071e0f05011b0510050c0c0c04021c051e070c05070b07200f0301020a020f0705090f040807170a110c0909070b0f09090106 70
    0x2c00d000a41181310420403801005503030030041c000294000c1906401552504101201404c40c0b240314404000c813105814881c4125400011380782c02c0000341044801c3e031500034580581c0c54224804c145040781c0140d80c0480d0400210f80500da01544e80005258010001e079103480074460641401d441c01a111200d6020703010465541050042c0144446131000f01e4085140c2012180a803c00080c0050b11f81c01c804d40d210009480000400100045072a07204100c900924100c9009480c100c1c0750342050310140b0880394082040d211400c1281c48030f41c0c00c503001c135516550040f1411210700c0350b05181030b00008006d4407a0341640f001d001030003581d02c0c19009030040000c0214200d00c3e1030300390f600c417030b106810250500c0800d04131040300903009600140010f84d50503441c18a40f517940c00782004507030000400205d0340c900700e41c400700383d014000f0b6140a4603100c40c0710302c04001c14003405a5012074145c00810040088003409070043c10341070b281c003280c1030a0100c0310000900601090380110701040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 434987086 1250 434985836 434985839
    0x213030804030219080d050f0c0d08010e0108060c0706050604090506010611011a060d0b03150a02030105100305100510020a0204020f09030c01050403200d020d110f01030228030212010f 81
    0x303004442400180c040d510504e00c650726103000d05079a14500c15485081c06000100c06e249000102c0846204080131011140c42c0c0c12610002410300c1424071905c00c04002450000c98420000b0450034096411a901a03050085a454200c000c0002a0115074030680d10108807000a006108203402040c840c0c0300d043c070303a0000904543c02d42e101c0601c181d0040d000c00700021100c0d0340380d40944880c1c0007040d00001d0a0300070400443e140100d0034502c54252003401c002c02141a40b03580046041e1181a20790004450038490250240d032420340344001810800181030000c1e040000441c85005181d01c11551084003e401003030407030340f00c000c1c404500003000442d00d125050822010070002c40c20b1a01c14607040c519220103180814a81031411001520480c420140c0d40b41c50104207030507001424217003c18a02d1403d1070402400301c0466018080910001d444d035030283c070944e58902d44030f81c681c1c0040002c004a281030040840448001c4c59400c0c00481c002640c0b501c10503000c0e0207481e031401c0d0100d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 434988336 1250 434987086 434987089
    0x1e06270a0f2114030705040e04060c120c231c0b03010606020c031b060d0c0c05010b090c04030303050402030f07030308010f081b0f0a0509090102042301091802130308040302 76
    0x202e420280321034007a01452203507641540d000240b00710400070007034030a4a94443e100201c4091240c2d900000103060014140000c3c010280d10803091050703140c41d0130000c2032902c0b00d40c4040d07c17800d40340d4802262054004903a2980825100b4140610fa00050b030b140190042c00411001a00005203102956614103107000b41000d21903880030700f2403400101000408000040d94072980c248043d0360b189000d640a05280c1c403040c2c103a9600051640040c03200d6075203003034010001c03417042c40c00b500c540d070030521070701228200390312120b0003418185519480c0504545003500a000050012030309489120143c54101c1420310002028502c40d6036206d005514103072030070090600c5500030088580040c5441002901d9803e000d00b1080000c3da584040300c844000041d8640700281e0119401c0711848082040c00c0b43c0641c010015102030a481c1c004014503c03101210859601c2091804520540000c0c041c03440b200112a00c009004039003d440c0144403030207801d264010354011600c60b600481c060085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 434989586 1250 434988336 434988353
    0xc1f0e0310020d0b0301020f2a03070b041509122304030b040201120209010c1e02030f100f02070507090b0607060c0302120711120f1e0c1e06270a0f 65
    0x3104e0110025401c007070034044000d2581c401c0880b0b400306406451101f401c404a04035100b160b14020741e0540e81c89400c1410400c450340f10440742240c00061410410340c0e4940c4512599403240e800000040010319a5501503070281e1011890410302000510403603200341d43d10000304050340c82000010442d0070301c6d00c0050482010b006101420500500c42c0c8143d90340e000c01d20018264000c41a0b94a84002d100310001c10141c0e1034010b900340c010702c5200002c225000855040881082004100b8004186100340403805000d42c0200290041d2104000800180c0c0082c62a500014201450560075503504401c80380e0700c070b4a00002c40d4020031074684140031311490550084650410040d0340c20240007583d19444c281c1030000650001003a00c510700c40f4244d080d00d21031141031007104403011300d2582c2050311360001c80030f203030aa200755455150031141d001a2000007100200040c03400780c8902031202261200c403c0c500c0c80618204401c1191080c0c00c02901003410f01400705c0d20b80c0140f03035042000c01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 434990836 1250 434989586 434989601
    0x40f050c01090b160602121807060f05030a0e070b0703020105040308180604020907140d06030b180706030515090703051e22061b02030d0e0c1f0e0310020d 68
    0x6001050b0320410145503214200c80751403400b4614100301c4e20701c510384140240602d070040c100204940741007041188034074608800d41340045003120000c940d221400c8811907540340b00100003d0003032010440000003600010044461401a04c405903280c4002410a421038641038006030f4441c0d00340414140c21020803034004d401c551070f0b1440398400404031580c0d00c10240c8024000c801038030015101c00e06c82c1c221910342d01c00c40c109244c1c1c0d840b07060086001134800c034002030701d034650030034041001c00f103400d540c9105140703281c1c024250700343c41c040d016030051400604e0b070b030f02c006000441c0d032070584c0e900100c0b140700b11601d071000200b9060405450304520703449102585907084031014070026a00700d14a8272191500343d0010400d01c100d40c60711001601d090b40305020062120144401c0d0290040064a60b050700342c0000c1042103100c149d0f990740d4900e804445500300d9450203164115184440040c03164000a09003404007030a040042854a1414100624156400f2517a40000a518000c061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 434992086 1250 434990836 434990839
    0x317010b0a1b0f02190303080109020705060f281a220911040606051905070c05130e120918010e010501032403050d030b042c030909040f050c 62
    0x80c20180024005030503808211000c10004642d000c1110810090380a100032481d4098558814045220003101031011207000441c0428600400854040424820b441c0c0b001c0c0c0210040403503845401c1d984404c0b40000e0441901001194002060f840941024401c044201d841c0018803190822503640804045068503200307100c40d40414416070042416034141c2d04501c2000100d800c50f038a4884039401d0700f01d0555030800d003404400600c060700302001d0900d142901c0c40f079008040c00401c01300d40078400e801e0300030203400d065001801141401c8640c801c20040744840012940f10030000545000450b401d46450014001242800350411030503c0310360003000c04480740154103146032402d03c280d05005003410550356a1451800c0201e0147c013044400a06040042a07502c9003040d40c0c031692072800391700c00709081c614507084500b0300b0303c03c06c04500c100c1c1c00c4a108031007104401003140c440340001310015200c140302248469a0b5843c4aa000707c0c0b02c0c0403e482840c084c0d1810a080c2106903c469 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 434993336 1250 434992086 434992109
    0xa050111130b09030a080a0315030c03020a0f1a0313020d050c030d0207180203070309020603130b0f040203061332071a07170d0c050904050a020c0316021507031701 72
    0x6040f292400070b20802211741c080100c0d81c5944880c4004c8005000203031000d4001b0041c84000401e00401c840741e001070320700986425084545070319001c8081156807065103032042a03602c005042a281502864101c0e01110711811640f20f5900060200d0307038600c4080d50150000c0003031881c3c500c2d04201e8122054203d0014200e00e07807601ca1800782c5441001032581a1030340000c00500e90a110358010704485500a040329201d003000c00030041c01c0050154102c07520030a05011540108a43c60414400c51f40107005012683d214101d00182c1069020200c07410556181c5281e61006034980300d550b0400408016403d01c0380f41c45501d45010510361001c181d03c1448100b25040b99a90012595903a8100c2455180c141c0c0828a0b0f500b07501c202034180b1510343c640b41d00889980c4d8401d005001c19402203500f172000d41c8502c0d04074803ca00c070302c0c20b40d410203900030058001803501468107040d04a0000f8030081411085500e149056031103280c045001a0f0000c0707040001e20306044000d80034007002c0920b07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 434994586 1250 434993336 434993347
    0x20903100c02250e04200604030809010507020d020909100b0406051807180603090201120c051602030703050303010b22080d030e030c01060f050a0b030f06120a050111130b 75
    0xa503e603290100d101c100b40603880000a211015420840010900f200b8210583e140c1810000b4002003200400c030000311700020350000f02d2500d079068905980c2c00604c0d003890107400070b005460729800900c0c201c1c2c00c84100010400075035503a1103001d214180d46809411403031120003203041201c03400006103100740d2034140c0c20701490b12884400304000403040c0221080c0d403207800c810388070000d43c8070800c0c48282c81040040b40e003d50640007030300068800c3c0c803001215182c041e0f042c2d00b5143c11103810340000d074044c040d07174100d10310003000b540100c0d0026003505c010a44035218141154000d03000302c50001400192200320b49002c1d50440326010b44094610320701800d1010940c2c50700c00c01d0120804054488044490940741841154580d09c1080000c120480d5a56040e44002d450391082d1841524200c100140b5000c0c0c031000c40c3d104001083c25840d440d981d03130b0204601141d4440c1088058804c100d42400010024814450810b010005040e03ca60301d1318504070746150315410a06040b00140300307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 434995836 1250 434994586 434994611
    0xe010b0a0803040902071406011409090d0f0e040e06010e010f05180a05100e0712051b090d081204030305040c05011d09090111070c0f0e04021509030a060f02090310 72
    0x1c3d182500d0031010b0169407000e1070304054070740494450011406002c1c4200005800381513445003c40e00b0403d07590000d6a547d003075149521030092044a50200380a40500c441092061124002c240401400013604641c8014550b01e440e100742c00c0130720b01450070310042c04801d00b450700b2013008001c225506052002d21584410f40c4010103040241c1c0d203522400812200550700403400d028100001102d0034615040308010024170404c00c542d4201c516110200c0c400c0642c400f5000e81400c0d21007206403801c21402c0511001304070080303040c0e039411000d01c04510740c030450401150096020340e9001c150f909080c00c1c4805031343c140c0d41c480e034140511901600c940c495040219140d86808917810790303443d91941c942ca17000d001800c00000404c0400180b941c10400b0001c0403105643c0090900c280954803540f482da006c8034140d8001e0360003020b040c005401c0408060007414440c1d00607068a410b0780c010b544440c10b42e11111100f0103401c3e00410004150308042011a440d500034000034401e0440004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 434997086 1250 434995836 434995843
    0x6090307020d08030a0b0d081b0c03070509040c030501290307030210050334021b0d1202030d0204030f1e0c051905100302030106170601050d0c020a14010e010b0a08 72
    0x20300041245030007000068031113201b035001000c1480080c1508010701810300d0450055448071101003480c14035149100001e5800064240303c4a50107002007102a0030407040007203404001700300b140c0308000b224012000410a01a2100781811204803541c01590415208069080340c49540e009521114040000d0794994000340c4400f000350a010b0b5598542500c0c14110380315030404070515048030b80c4211900314030400d00d945e11641c1d03035003603a052a4041104401c241440385a080d4032440c26034513100802c0c146407a156054000740100d920301715500d80300c01d0a83c0c206038070030307104401040200710030700c03002180d43c03c501512048041284407503030340c407044540302078000c1d60300900500469119000c036a060201c044c11006145070301c80c50b04200000d000e94000d000b4503002900c0600c18000c104c41d4110800d0161005841b01800c0004427010140281001c0e150b01d030440c81a1a8440c1c0440c03080c98020000d0b40c4410004601c01c014202c00900350303270407030031041d00a101c8054200407070078011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 434998336 1250 434997086 434997109
    0xf0d0503070825020705040e0604260c060108100f020310140a091d010b0307030b040b1e1006180b091309080d0203100501050703020a02010e1504170609030702 70
    0x40c02c001c0c0e10350b01c403912074042014800d00403d1022003003070b200502c0076800107030039021140101c5007480302e003010010320340d01c9040c140c500424030941468282000b00307401d1040e002019122851600740150007009900d403030f07400e0340400c00390741141a02d80f50480080c09001014141c0b500d0541c65800c0528410740d81d205c592086030680040700c01e8408260fa50250b428004149480307080c0710b0b01c0180032071001041c02d214849001e66203044042201d9013001304090341184e800c100e0001c0e0654994903086d6085000502d03440c0d0010000d000340c40b000542c0e0075058080c0c0c4507800506103803800d084c005010700c840ca048010000d2201038080200035104021140305400c19030f4490103070410380d6406d601070004000004c01401c3c0c08a450003912410798081c40c0f09a880a42d0a03400030395600042d1000d1007440c10140c0144c0100c1480c0026501a01d414034012502520444ad61030008050100940141e0030480e400c010300c1e0600c0113204401c120080c0c200501c0d501662424403ea8001807510440c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 434999586 1250 434998336 434998351
    0x6111002120609190e16060c0503031305010b0603040503070b060301060503030d0f2a090501180902030403090510050904051f061d040f021908160e130e0c030f0d0503 73
    0x10180015880c0000790005012104c0045080c0a6001100401e80d141c541820306841c040b04490301c0002d906205000c4c106c0382d80c0d00200550301c2d5031900801d038440c43c2030900e41951650f40310031a0b000107485da04c00452103103010704065611441a8a0640d1080c4405401c45110f070b03040c2007040c009a50080219901c44810070720000700c0d066515049805480541081410200503094000c4010a19500d119150359140d0385c03414125200d50042d80c0080c1c0c1142c04020440012500f4040340020354021a045400303800d02407180caa480780001e410318007514030a80094030105028030b4a0415009440e000110401c0c41c80e001d4600d0b10284502c00a02d00c510810040701403031400a0301820004815040b801800c2404040450703200c2c007001c4d501400001c0c4014120b03481c0100058880d444441c06190132400c103a00755421060308481c490103c051440c1d000400e00d00b80703040030505216203010300c003920000e041400d07101d00806041c41c0d103064a01016400103981150f880781c0c8041105c1c4c0c403083c0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 435000836 1250 434999586 434999599
    0x1305060a05040915060b03100801020a0c030f020c090c1305040501051e01180b03070f0e03070504020a090905090d020145060e150c04050603010909030c020a061110021206 75
    0x41078100700342c40c904a004c0800c103540ca00030002c142c01c0201002103200d600340950844030566164106400c0717104074906400003650360302860000070710620b030640101503a4030484400c01400000201e1202d02030f0742108481d540050881011110310f00844004c1000b140c0c10440c0f90304d03080104248040c10241201c1e10f0908188242c20b580c0603c1e00015101c9004076421809038880d500b074600c60b441600c0d010089900d214418803241d2041210b0f5080c0040074002d070100a1402051201942010030040d0a121001c5004510865a840f07038501c100c441e14000c21030300710802c0000c0c1c03c44900090043c00018003010220302001c04d0700c0c0b803000c0049a143c4c10181d50300d550f03015100d001840d8200811590408410f1500c07418006001340c0e285e1091440340300c03591038a2400b070f9128802d46c454280c0040f13003400101306866061380420304980c0241070020ba510000e60000d0f455018641000001c160900b0480140003800c01411100c440d001c40c3c2185807c41c070f00c003210880300c40203041030711031b04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 435002086 1250 435000836 435000851
    0xa050303090a0b0c030f07060f15050112050a0e03070507150801030c1505040302090c0a021605101d100807030b0612040b180f0f0f070e010b160206040608061305060a0504 75
    0x1300800441d111581d58074401615080c140c034111380600452445c0075002420540d40074555025800020102c44058603030858401d0f003010a44041c00e002000e0300c40315a07444151460502d024801007583c640300344050f01200f810319451042ea8100e444080c02003003a00310040c80041c1410f510a804d4810b005a40c2020401c0802d00b281c441c8141d8000940202c030010901c0440030746640a000100102e80a81e203900d0391a20329850300311014071445a0000030700725042012405203c1204902c03035070007216a4078440b450301088800a058050000260350a4100070481c0d82c14445d85402d1041115014a04103c52801d00c001903805480941101003c0d0b01065200c20964801080140744a058030f91380c0c1190442d42d900c0b0602c04069031b0460050103070701401d0702004100403040d1038840c029512942d0031700d40c803a011500407e804a8840c0b503915810f44c0075a5808000e0030041189075141415854a1020b001c1020f280b02d0030540c0242c188028404140d07a4200d0f14010354805880c009001d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 435003336 1250 435002086 435002107
    0x230a0e1012330507020105040b060d0f020603070903151b050313020d06020c10020909040b0403020723040615020c0613031a150a060e2e0c020a050303090a0b 69
    0x15005102c00b10054060025000750005508056040030002640104036a41e900c000a900b41da600701c03002801d106a1000096040c5802001c2180c030a024603000303024441640d001c650964030580b403242c042a01c4150800801848944503031808880710303000c0c8421482c0c6812032040c1d40d4410b40740800e021002c0000b80b40c00510020a2081a400034031045000caa02d051000007544103031040103c42c000d1218040e12010f0070f00807520780c03c501620183c241d980300d4a8490708803a014104404601500e040090b105091442034004041c0d44002e0800c104582020041116890303400342500400e40007500d00c02075000b18a175400540c003661113a9844501c40c188101d244503d400091442480a840740d58600b55141907038811800e03000c50303d00302405001000401c125501c00d0100007042d81100c00e089081070041c6420f408007200c3c0d44030322f4001e10f00c104802c6c1204401c8440010b8442c40e140e50641ca00024018002c0600342c01440c40d002c501030201d0581c2a190003904e04080000400c640074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 435004586 1250 435003336 435003353
    0x7140d0f020601063614150313060e060411031c0f181a0d05130503030a0c140d0903021606020d03110910080a0b04060605030f090106230a0e1012 64
    0x40817001070280840005a00c0c2c016142499003e100c50306605440b101c203807410003105c4a4440480b4805150942da10100c681902042c4180200e6400d519100c83e2001d0410400c4102d00540c820200041c01004400926261180305264924101007502c460b411480d00443c01488103603032807a01120f040013200f82903103520443d900c9425245001c00740481000315550141541d807000c17a10900c00f0341c5640c6030500c000ca420000c007500b01c1e0020008203000150315484a941d405050600d625240d00c02c55040840350041e60710100103588480d01002059414040d2402c5841240a440301c050b0800c58000d581d498154100c00c00d0558800c040e844c071090000070b94100c0e5a004020303100c0c7e40701a010040401909031445d1401500703004040ca51868507001d28400d0740c0240c1d44580c11a41c4406020403c81c0b070180010700c041d507031942d0100700d0382180070000c084800d10400b0309078441c2442d028420f00307003000e1f4809600c0c807a8200501c4131580240e0540411508030100312160002d00342000e400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 435005836 1250 435004586 435004637
    0x6060301091218050307090204170606010e0d06111c200301050415080d091e080a020103050627010518040f0212070b040e0126060406050a0204090207140d0f02060106 73
    0x5d0600c260680003542481c1a001041030b95060552281c0d001c01d00e00496988071016079029010400d04440b090f89402c142650b20b8006006910100300880b842c0c40d04031190307100f0340401511088010510411310082d006100410810221032483d4013042410790529000c1802072510860302c80f0a91450310030040c4046015103080c00c107542e40c81c410184080d18032072140c070644090284091480714108611001c460881e1004000780040184c0ca07401100203000040010f684042014030701d90042c400700c0070354500c408016002c1d6160354104000c00ca04010070042c012680c038840020440000c1181c0c68181c0090790603036101d03801e141d0040c00300f41400001d405c11040c1c80404a0000303281e10700809218100c40000e080c15039898400401c5200c84041c249150364683d00450214000801550003e51301860701d5000504045e1203d490700c040ea0f10510003958901e05d00915440001c1007401903c01d40740e070604161201c2028600e01a488110500c6090706002c0030482542a05042100070b40b0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 435007086 1250 435005836 435005839
    0xc2c0102030912011a030d050403121e0c06061205070909030323010f05120303070c210302120a0c0815031c020a05010501080f030f090307050402031003050606030109121805 76
    0x44401e10104090b00030808030001d00300d03001c6006110101e03810049140c084e007c00076600c07640381a0031900c0c1e14102c0300014040808002002189200c252024603080e0013a00301ca90313501006141e03d0902c1400e582c8103400c04040d404a8081103400920005075260071034018120206840a007420168001c0214100024401c8079800c241122200805c0d00302e81a5041903200b0444961a40c0900400078082080304015600800214a0f51402224600a010303c1804400b003400314100002c00c88159a0034004042600454401c000680401c0c00f654403284d00c0b50704011454841c08000d0142c20050080c0c0c0c5400c4903486c0b203411030b8a0910140308604100c20700320108581180c8025504c4065040680d401d500c0c2000100c1c1d4918040340081c00701005200850801090700e19266141d8010000e83c0d41c1803042c140001019100ca002452290b0102284400030601c0c50030028200764000304040d02c207034504802400012111810342a60500301d18040c16014188000172071180342d160031a5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 435008336 1250 435007086 435007099
    0x6030f0c042708210c0d330e150306010501050a03090b010311040c2309010207080d020303041a04020d08030a181b050103090b010501030908190e01030c2c01020309 72
    0x90043c0803e51004150b9900e40d0440481a0740e828140c041036000c1c10340781c503191004100555020340c00c1c40d400c403500440304401c1d180d44c50742800c18070b0040c039004161440c0c114a00e0f10420420450360f045000d40c400e5413000c07402000a81440040c0c0c9402d414011141031010220300e00a07081c0c4a5400086840e5100c020030700c05584034140114807105804506210306d003010302040704184903254141e12822640c0c8822550706240c071401c10340ea00550071a034110300c0307901000a034070b032401c11200c50b007841aa00a99079030b04060420642c2640b610ba080544404d142e003d0000580720b1058200a00b9084400b464403030315a95451005000001d030800b00c90305a40300e141c020f000000944039030303a40092608000c00d581d05c20040d026141c51940103881c2d42a6900100041d50180d00000382c8107114003034207440d000031200044903100c04041e11a0000343c03103500d69441546c245c4a62042c410709414915074a008070b1188000d18071440d80029007007120040140850307402001910070011005001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 435009586 1250 435008336 435008411
    0x1503012106020a0c1101030b0f04050a320705120c030601050f070c140307030209040204050a020702031f150e071d0a0303111605030a0b060a030c06030203090606030f0c04 75
    0x100544d0359900c0c150780d80c0c0100b0b2075800e42c541c040d1091018202001d4900d0550085a500300002403500034203080c003c5881c1ca40094000c10020034103560081e00301d901e80e4400e04200e4000d00140c200502e60401d104041100011500b00c000009501070010380b5025640d075a298012503440c0600d500c24000e211000c90003804000c81e81e5040404d40e0304081030740d10814020401c02d6901c546521001c0e4006400d0030100c0d0150030581c000b01d60106140c107025181076056401300749049090541c0000014118441442078102d60103940e13440ca00382c514500100b03041c035007000c04035040035050f40207200318111203403d607840d0b4006d540350050f40100080002c543c3c0341409018400d119420000f94000d219034015402c0c1d0781c002560950310f000d4014078000030a40e03508a1085800350030f040e03100101c0f000c00000240d100c44414040c041990b800340e01da00b080c120b580e29290000c1c100c14481c1d00895441c0e21000320010b0b0714141684215404540c042c2150300c0b07810204040d80401041c01c031036055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 435010836 1250 435009586 435009607
    0x8041e0b07030e090a2d090219090f0506010e0d170309012403080a080a02070510090203151b18040203100e0c03060a031118091b150301210602 63
    0x2942c080560f0130b8800d441d507940d0f80140b40f4100c4003610148804000e0380440302803500255000817205209004000a01d000c1d683c00084280a00c1600a900310358a40020702040d1320720b004288a4120050f000e000f603003040000a03081c00703510347d5014021018400c07901c0610a20720000400294514800e540d40d0401035140c60207050524002c0c80803440312100050032000340d24241d0104e070b810101c031500f0400090f804a403651400340400f05115000d1010b007011550034460303490421841d80000078004032900c140f6080c00b01c035805100300c0c2069601040303003002c451281c103400500074480043e43c44044510515103080c0040d401608584040100040c4403040c90414041c2e800c41c00d0410304c603560302225038034503100c2141c10750381001080700d00b00300140c14141000c07202c50009000d2000c8a0700c500720b1000314081180c0c41074883d800700b0b0a01e44403582c1099100e6031228140d440c3e80c0441c8001c00104c2192006114100454003881500704c048024040c41c1c0030307641e40c401415990f6014065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 435012086 1250 435010836 435010847
    0x19120509040b10090611070e0a0e1011040501081609060509040f1d061605070314090415150309030e0609041104060c0605071b021003110c0703060606020a08041e0b0703 74
    0x2203001041144040301e946c03810000c2c0ca45d08441200301848802d0b5600785013180545004051100540709900042d140c4c2e402c00c1c090b0080041c0e80700601604d44d45454001040068080d00c001030501d40509860b15032035101c0003c5041c0c1d04a420065901e242e80d6010a000700b810203030340b0100501d0045034426061030380c5c0081d05020350200c00c4905513142c80361101c80c0c83e140b1155500208600704480c1000a014404c84400001105039060415050801003000e442c20490b500003c2807a6501c1480b0003001d40ca181548115180340c204000c08081d41d010b0202a02c1000c00c5104100128088595a0301c40d000311020310200c0502a032240d5855901810032448014100c8a60382014009516a4071401c51941d142400c40400441d030b01d00c6400303111f80140d460080401b09512004444040b649500003000f050034070360300500d0424954203090f0304554051f0810740441d000300c10f070800801c191b42d00340d4003920846c450465001700b0040c0710200e40f0440740d0090340d444401141640c02e054201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 435013336 1250 435012086 435012089
    0x6091309210c12030b011d04060308041203030e010e1f0209040e1b030c010c03120b0a170601090203010b04150e15030f06030609060711100e0f19120509040b1009 71
    0x100901521200610020341c241d400c084c11003800212401647c0540c1c6103503030200d800000d4042c000042c101d1b00ca86910602ea80700341c011407010142010a001007607414800c0003601ca10010003005900902002c5940311044102e140b0800940807218480c0401c1030707812903a040c1c0d001002041000d01170701095803201740c4000038208100300001d10303400c075080c00f01e030310080542d0581d9205083e240c1075406440ca01c2d000351076540c1f095a1080101c00a403119961240500101c980c0d00d81d20131a1003120b0b40ca4100140c2114000f1401440100402104a0b00742d41c15902c8002e800b000355105008120b40c10110100880e038401000302e8851026402100214003031100c1c50564041540e80c00141551076400392003200059001c0c000040b401403240c00800030705050f00c820b40b503281443d07008039401c0d00c0150341c003107409420200054a564038104038104050134100340c05c03c2011a180c4548180c42c80710514107091180000e428500341c0c0d110717403103960780000040c01d05024001c4101e00800c02d480c103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 435014586 1250 435013336 435013343
    0x5090306070324030b0609070c0c24020304080a2306010b120106050a021f09151a0a030309050d0204020403140a060501080a050703061802060c1b06091309210c 70
    0x40c8600f40266a140c0811007003502d401c1040c000403500d0311820300c074280307400408420802130b006d00030030b00050540c07007141c0c014141590010541e504900d040740e401c41c070b01c0011a066620070030041003d00c001041204442d80c2004041c404c42440388010b0090044849562500e405a039001041e951500300292000081180c25003220743c1c0c0b165801d40e80b520440c0751460269100c1c046030010007046984c6c038009450005c5001c03402000c00d640f1005901c01168a400909890b00401070070004410b003c4000c000c01111406102031031918003030030041541c06840e009400c642248000c0d92a585c04640c010760b030100c0d8151040401c0031240361103400720001110083d01380304c00010359880000d0300c405c0e4a60444040d00e01d15240d9075407040141001c034242041c500c03e50500d60090382c1d401c03000e046481c504002614144000c1480c540010303010801035446001c09008a00c00e545500d548500c040721020b400103405001420305031840c00400c1c14036802c28242e04203a48126901c0418943c80f20310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 435015836 1250 435014586 435014621
    0x70b180a060e0f03010204091d010b0f060406051e07051507180e0901060b031e130f03030c0e03011e0f020403020607080714070e070806030a08031303050903060703 72
    0x1000411240e50450700c120390000d50840e5484007603240c185100407200800900061415580740e0401d001e0318000b8845c041d6000320a41c40c01483d00e002c1c012041c51490481d5407401c0a60881c001034030714055070161303208111000c5960b0710041207208070000c080060b081045e0322038055145c403da40c2d40f06a071542001204400110740420300541710220941c01281e42c407003a003803c044049101040050047c2c2e0199240c000005242d000380004601804402040c0040a0030301c0070f40c080a14070150030b41403841c025211640201d80703507403241c0c10341c0e590602c0c002c0f50301403c3e0107084840d1201201d2050303041d40307404401403182c54240440ba1100098480a101086a20034000124083c40c400a50003032420001e090004039900300030111103210306194046102c1c03454205203440455004030344180070310390500141d0f50700092603983c000c104800404070380c2c00c5a5518001800090700c000d8a41d115100751008040c00340043d603555800190803241075140000000780a800c05c0d0383c94240d07604 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 435017086 1250 435015836 435015877
    0x40c0608131e021011071707050a0609050a0b1603031a090a020c01060807031a192301080a0c14060c010e0c090105030a0b010b0a0302040305010e1e0d0c080f0705070b 73
    0x174017076144001082d80050152a400c0d280c0ba080c101e03100034103a10200140604000480c07141d46591100000e07101301e54030702000302e05210074401c0c0000346400800e40b01600380917160200341d45c0d040c800d20391038bc0751501007540c1840300400820b03e00f84810a59020f40f0340002c01601042c1c40c0c1c0900707001d880000c028012981d039003a001e6160000c030300010702005a40c880709030100544070040c6800400c100c103040c1d020851a10168100c5401d50041c40100018804000c45160180e10031030140c10319501508005115954840038000c1a00c03980c003481102604080150750b038041a240c3d00200200240500d65146a40d95142c2c5220b405c484e10030810b98001294508001030b5510341960301c420464826401c06e00780c0c000c45e0f00220300d5481050f030208001300026000307024001c2200e40100c0101006101124030030035041a506043c84075500002811191540c4207040c1001103800000c500e50b0340d80748104800d40351140641c0031340f041c400d5081c00141c01c0c052800814248070501c0c030a852a8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 435018336 1250 435017086 435017119
    0x30a180b0a11010c0f020a0b040c0b040603090515060619110313030b070c020607060b03030412080a140c030708090f03060906100e010f15031d100501050603040c0608131e02 76
    0x6000f13005c20000164003000c85180040e00c004400b540050098008450140c0ea612101d8152782c06034021320002078072810620100320042045500903824091b00045074039018001c11813034044d100c140d940c8200c900040c0704686012f012009603200414054076520040d2071050010484c240c40200c81d49980100042d100d00d1040d00960990b40d401008146000e000c0c0d00e800018040c0d084c4403583c075001c10000064007028080414003c107109405894440d40c840c00040c280c152101043c040d03440d41041400304807038010080350035240c1c0c40082c1c2511038130508042813507603a01c9100c954041c840c00c41405403080c000074043d841b46101400d1b0703002e44c0303803901d45000070124280700e82c07106a80420700600c0484040703165034001d40054900000c180c02802d400100743c2d00e46003060405600601145e000c4c04545001d030341c1c0940f00035100c4914500b05517580320300741c41c2c0c680304081c1049099004600102402809041e400d50815521101c490744440c41a0403001a40c00891080c00b140c01081d551 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 435019586 1250 435018336 435018347
    0x90f09200316112407080f01050307050d0606050a030c240504031205070b01060305180c0a0e130803090c090708040b0c0f0f1306030c020a05030a180b0a11010c 70
    0x4442060054601c00580c1ca030035200e49104542d184410301406108a01c440510419001c614205030060241405c000b20060304030200a030100d0440004507005000d503850009220086503c00d5503404100c400c281080c100824641e0401c55221041040010602050f8907103181a100901304001410556202e030001d0300003c2240d040101d0000d2004002080b1284c0c0c00c9840c0c174410782042131505415969041c81003109801500c0820b0b03580040c401301700c180300100a051020b00d00280040b400c00c1c8000f8055420070310800108510510000d900c0640425401c2286c0790300005654076810040784403602d5150501405006100784000030781485d2103014045d00480d0403402d40c15040d201c0d0050000d070343e031203a41c5019402e0001c000707100746150600001d00c03410410880f0754010a081c100c1c01015590404001011540310b4442000400c3c008407c60700310040303e0422130300038040c80340ca200503100168882c0c9080503010506441c01c940092050080c414400c0007000301c17403400704042d0342 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 435020836 1250 435019586 435019591
    0x100e07060216030b0601030915090c1508150607021305041509080306120115120c0b030c040e0a0b090406021209070f03031110090507061d010f0f090f092003 69
    0x18102c0301404204041141e444c0b01c503420840601d80840c444440707444028071a103000210007550303551010060148080c070390620340039020000c006920b00c0c10501e4010101c03140a41701008007c603012803142140e8405080f18001c0b580500080c0c400340540680100a01e0112400c7c3c6950f40d003101241800405403046e108801e43c019000c5007507460320018030480b0a08001c800700715660700c0c40440701c40c0015003410b100504141c007002d0381ea040381c0c0ca001300703400a40750302c520a951414070500c418000120141c40c155106040a101c165448600000181021100054003c200b003024041884002e8004181c5444803d030011200d07200c0d480c01d03903a034440358418429541c0b07070003d06100281c0b15015400c0305524140c115483d070039083c00e00c01d00315085d4210480e91980801c4d410081c03260400660b2649201d021685d072141d00c5d250b80003030030088440c520380e410040c0c1c0215400c6090701600d803d10103440d400c0703081540541c0fa031408500410182040c108643e030307402940f602614132081202d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 435022086 1250 435020836 435020863
    0x106080a080403080c010b060c010b041107020303160f0b0f15190612090209010608010503100c08071209060f06180209030d180b0c1b1804120908100e070602 69
    0xb440d040c90754680c0c3c201c60b00a420b040700319540301c01910516a582c00007500c0411441c0340009800f45c80700c400c000407030316220180803150b003040c001e200c0569000310545001e04905240b030303100b05070765251032201d21541350002401c4030854000c1c056a51296040940300719048600382c1c801d041d080e02001151138080710152000c0e00b882000b806528400c5803c00c4c80d02c040c0c01d40108a2800c150700051700303a1000d801c003000068442004110a00c0c08000540c02c0d1100e1a80800ca0580303480d40041c42c03c20010000d0041c40300c400301d035074000c80241e407000140c290070601c108002d00718461000c02905082c41030007800d5405c102d0f0584440383c3c604c04c9030908a4000c00034108002030510030390302d425101b038804840c1e101085c5c00042d652640002040300101e4080501080f0042440d5071035040342e12804a4000d0000d2031140720105100da90b0315800580100481c19240e03100981103a00c00388580102da01d6015507642c051000071030781c100203a900d8040040e19100c80d04c0e954100e9881c480c100d242c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 435023336 1250 435022086 435022103
    0x14030313081b19020103050c07080702090c0c01150510170f0c090a060324050607020112021b07030b01060e0d03030f060906060819050114010503060406080d110106080a 74
    0xc0d40a500620480032100101c07549800c1e000522401d182c003940f114402d00b22403850840840da898859254003415004050b400d1003d10f8468241c680203011009000340507940116002c2c103040000d441045035071030002d0001100040c40c412442200744101e5011b1340b010046408440c0c0148460f0f00701d0a0550550034103680c4424000116038070151410a070b104040020000948800440d900580b1a07a140400c01c01c17040550307588000e0303604204500140340160705200a603103080480c0e48840c0c091804000c1d04401c45420b20083c403511901034003254500c41c095800c84000705e481c02c21240038042c425030603039a414060781c94029800100307503c01d00c40c3c81e06d4400079001380e000c0310200c68800340002da21a102ca148404031501504202d003c140d1345401c12802e1b260205801110340385e82d010900865150050f0700c40c514002a07002c0381486004030006a054a8984c00b61004014180448a0019038980c003e0072141c1c40e45642003965007051804a0303500400074004a0301e43c1d1140300d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 435024586 1250 435023336 435023371
    0x51b060a081005120d0210090f031d0a08100e01020306010206070c08070c0e06120a0b01050f03030c060c03160207030201050a030f0e0703030f0f180302040c050706110304140303 78
    0x854400600501042481c03440040c04101904d031080042810b4280c00001c082c40e40306808043d242181d002e1482101c2d0342032003007000c0002c54510f00c1d41516581070400300c2c2070300c41810411603401410348005420000e150000076401c0800224209100c07446081000030892050b10b130341c09d0303100440300580942e0241003c1801e00e8411419040807a000b525002e05110580d41d50005082640c0e00074885040340d10280602c47c0340c0400a0421038040c00020030f802c00680d40d413541101014480d49229407034030480c000182e1400d00c00c135000e64a07000b040e079025182c1500e08000941090729440c00d00010080b41300c40d90780c000200c031010741c1c3e016103407603003801c085e0b02c0110017903c031802945403650b4585104218802e02040060080c51194503680f40b0282c20120048c0345e24501020b10081244c1c40c400c40c40b8510aa0121006490b010b0701c0c0801c604414000c213881e40d2203503103001000c0d1854490004910390000c4003540c0181d1107580e40d40e642c0e10709100070310307902d0005940135210914030070b90 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 435025836 1250 435024586 435024607
    0xa0b1206270c010c0f0c261506010e030a020604080607170f0a020703090801050709090c050a051b0a121106060103091509060e1213050a080a1704031e051b06 69
    0x14520001480780217150b48040d21540e9200080b241540941200ca488030700c91243d1542c58164504011b000c00e0050100c40524004007030034860103001d541c1485504404c226080c0ca05218459000b600584591750704da580f210306513078891084800f00c0000d911000203004912406105e14000c0303082003e40c041c16203402c02c40f10300940c82403004405210100f01c0c0010390b07810a0103a203120305031a0310345007a03c502d011028015944c00203080410410308004040005030840701344c40c5c0000446618074030b100304081440303140401e81c603000342010f01c94840068806078408451144000500d003503030484e8445800660546040d44001081c4100d0f2912402c2c000c00c0a51040302c00b40d0103118040380d43e04403045c3c49410b041900c6001030a0000014800c01112540b030700700c00051206075400c031100f030f00c0c0076510354446820030b40080c0b01e489404034440b00a84080103560140d60000199400701e2941a018421511010400c45140c00313000d4491a401d09030284501040c10302804562a0455146 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 435027086 1250 435025836 435025847
    0x20d080a02070605010803071713030803090a1a010602070b030c03010b13031502090132070812070f0305161d0112050a02031f0810050a0b1206270c01 66
    0x30521200d03107030300340001000700d8801d0141c036008081150285a4501d030a0614441c2154070382402d004014081214a41c0f01c3d01c0b00965000310303900810341944a45800c13100e02c1c1402c01c0d10b000904205010010380e9150b03485100043c3c100c0700b050302125482583c1e19001251804116886160740100340010004150040d0003410301603401068100c00301d40300c1d82d420468008130140c10300c0d06503000c1904112543c1010b9040240c1c0350190f60030075040f549001c0c0750203130007070b695040c1e10002002c10326030304110029040e24103640031703007407511405c1c0307450a0001c000e41401b414010010341014081410f80c20442048802007010ba40c1c0c4842d5070841c801900b65031085503148604004a0b807074250281c035a9441028010103c2840240c0d0382d06100c00d48984113901850920f001500c102c4080003004030015034585407240e8100013260650780e5810441c008d02003a441c00c2d070441d4030704219018a03c3e010a0313561248000300c00d0181100314104c280c128107040910001d0380d580c0030320005201d960041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 435028336 1250 435027086 435027091
    0xc12020702040e1204090f021201060c080d11030a11092b060203180706020d08070f0c021c03080109020702061803010605062106010822261e0406020d08 67
    0x75001040c0c3e02e00303c3c4401850400025418581994041404c2c0000034850140004884c0e881000394100b0f03000d044440034044040c82264140649a14140d04000b10001551400c0a5a200821520030687c081410540c002c8500c048038902c1c20301d0460420404a003610340c150b13006004400c54018048181003e00640d540c0c80a60b42801c4103401d0018079240001c40c4905086048520890002e030810b43c80e040c0250842e5066402c8002e00c44803840c0c0c4014600d40c0b007181450444d50740150008103444041c65840040d401203101c010b80025407140608003c0803a00c20380d074042c0560790f00c60000c03080380103040c002984008d00704046c580e00420180c03000360245c4000c00001d030035591440020100c1e4070508400d18220503259004554402031074096038003000038246881c45103424005a500e40d4029039801d006c201c0703111110402e01c000198100000411000042d4083ca074280c5114040e030080040340307041e1112551207044040d03200d81a01c00f1100307650014418a25140001d44030b00c0d000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 435029586 1250 435028336 435028339
    0x70801030b162f0f0f01110a210b1512010e270f07061706030307170a030609110c1204060906110118111908031b030904050f07120c12020702 62
    0x1408604240b00c8028055010b04e0b2007241e000f080c0d09003100c0501425940c1140b00e4110b201c00c03d000d045039603900403029804d05000342040842604001c0240d000501140d010650040500c8840704103850b070740310051081400c04000940300381ea0718550701c174000c14115901c05188000d1019840c0c091900791503031084121120680e200208007026040c81d10f182544000001020010b2800801c0f400000450300300c1002d6002d180741060742d4441052010352550320303410b5000c1c00103000724105c1c482c1d440640580740b0806c2c148007004c0c20086000450300181030500317450003035a000d130603c0600070040390225021a104e1110007407802c001510050f00e40d405014040d501d5081a403080851500d48000ca1403082d001a03140c078050308140403070300d00e54040450041242a50520400b80e0001c183d41200e0181c0c030526401c40d1944a110341140504001c541d003182c1010248030189844010709803040b000c560b94100c540c0d96a0400e401620b030130500301404105911095a420041c9070001c0201500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 435030836 1250 435029586 435029657
    0x809010f020f03011e0303023712080108060609010302101806110106050a030b0606300a060501020a1a060a0509040b04050c030607171b03040b01050301050702010c140a0314070801030b16 82
    0x827901da40181030700004808480d04c00006500740c007810380200034540503081e0800140160326001000c20780000060001070301c1404402c51480d41e00b44528030f18044480c807410041d243e0395036400090101e0707050307420b002c20b6542000c00115090500c401500122900400c2c00700f440d4903440140509580285080d0340300004054074501a102c82908001942034510306040aa261024005048a0f45a0812070442d04013103141c0c03000c1000b82c00620300e00302181040345966264030300014010304080d031006070801d06d59000c00080c486201c2406100c1c078043c400b41e4215400b140201921139004694800100300c964164050310901032084d160f11100306c3c40700b0301e49919000d42c0c50340d440c0c000700e42c200d50b400f1140c2c0c01400107003002e00600d60442d0744d0740001c0c006001d030340f0b2028040c800095102c58004c41d022444070703c000e120f0303044410491141d9606910a041c400b1000f04071307d40c00d000c1aa0350408090215490790f4100f1000031120b602583c803540407942c11910702107140c00d1201801054007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 435032086 1250 435030836 435030913
    0x1212031b03040b070f030902090403182d060201020a081306060306050a090215030613021c02040602030c07050910170a0b0702010c02060f040506070809010f020f03011e030302 77
    0x100c0010041d03000d40e000740f082c50014a13068000406443c40f03128074608146c14030030303c0030043e19280203442e08140d15041c0a4291240c4103125884201c0c02d07030090700c0c5800c0e4004000090800240d90390b9540d01040d41c040e00c0d082c0c4507071040e800d0303100301038941001401c520b0010308104d03200310061442c2403043c0000302e40030399207880710703001e440066880039031300c90b500c20a410461814401c917018038010b050046080d4a01390000440075160f07204c07144e04042d000212855400c2c4042c0c2e2020088520400c115111500c441000350350f070b04846003180451040d0200440c10f0b1800034412482000c44001c03500c0c119040c44030313030840860410701c03804492060032090400035103003001051040210b640001502c4000351002450400041e154820303800b006424440810008100301c0c2c3e100619040a000340d44403860300500500519044080440c1701040718880519003078020b5040743d01120320009030203010240711104c102c141c40010056807091807100c2c804603921107d5503100398184a8280b480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 435033336 1250 435032086 435032131
    0x200303030106050d110f0405031902031009030c0507030503250c05040b130f0e0118050c0907020a0f030f0f050a1e0504030501050103050601031406100614040b13030201030b121203 79
    0x5400c046d030300c1d0800360800300c0d0500113414200059012031254512001999030f10703802203a16070602111100041362201080820716015903001000240e10004482c0441d0341c90400a40b20382060440c949e10440d4201c55440702030400050011070f030780010001e40c81c14079001c20080100004000300360072660351108007600e441e0610840b0340b20110705101213290340510403501e003165441c48400c001c0024043d40280450400608200103104c1900c1d0100e454035202d0081c0d240002803180108810000c400e01e9080641c0462040e24991a41d1541000551250010f45090183c20380100c001441c0784080c01c480007641003010002d254604104c0d00e0aa26512030034250380c001d030020f44140d44000c00410800140032100c1d2005e41444001e042141807510a6190007000c51207000108807078005e40c080005008001c440041c990440110b50741c0c40500ca50400ca00040c0c441a40031078900641c030716807414540c170300c000040180400303003a100781c05184004d1560005031100d02000354034902d200c0034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 435034586 1250 435033336 435033371
    0xb0a0c210b040501210206090a120303020903011127040b060a02061f0b0a0f1e030b0f01050a0e060310050a06020a140703020f010e0f0a060c200303030106050d 70
    0x1028806034010441e45585001d1100782c400607806130074002e105080d8034441c800780074a0003195960445006a48001c04ca00050719961560413240d804030742c0000020805416500030111600250300900ca0ba2081e014460400c1c0a03203081d502000d0300710903032204104820010041c0004005000140314403250000c501d05070020250500540d02c402c05120040001d02c442a00c24080045101c00e5a070804100b4031060251442141c01e025014607038604050181c03030150745203500440070000c1041070001c000d0242052045444c01002445140d0929502c940c0c1143c3d9400305030f07101e82c204020a0002e20215510080ca910403203040040041241c0d9a20740182e0b0081c443c5a005103180708660514580888400e2440a010b030300103003003007005840300c01c0c2c0521000000d081c6090280301103000b18183c55064030748698002c5c5801804180c1030781150102d140c050081c9541217010500b80e842d01840010644406d50560052004020f038922900007003808440300301340492188a0411507800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 435035836 1250 435034586 435034637
    0x4050f1911040b060a1b0f0b0609070807050405010e0112020f2206091211130e0d030213050d15020c0106060e030610030b0903070807210c0b0a0c 64
    0x141400110200418041c9110600c240058112400c00488003120b0005503076100703821203001404000c140c8035100d003038a4500c0039032850700603000c1514001c0c20301d0b240d0304801045071080d00c500910004035802e54401c44c440b078032824a940f140b03440d140c01d010041d6000f401484034103042217041c500800d4840c2c03880c009400d40021440035580c0721006080d42840d0101a4a0311000c4040802c03c10000140d21030000b0046407001d854446108a560401070034800d840b4503215003100c4106480c0190300c03d1940141036118011095480c0150170410403020b0388100d03043c1c0d60005280a0050000d4a001e030079055140b4850314001c408915070785012002d0740c001d071500880c00c1e5540c00040101a030404044020400708501500041c031300746200006004c02c2c0d00020703040f001d0300000100d100100301304589009400031040c0b51256820b00e0141440d60100b141c0f13045000068010284650164101d800c0b0260300400080082e0f441c0280d540c010f200d240c480101304203c400482100840c0c0741003001d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 435037086 1250 435035836 435035863
    0x402042013061b15150909031e0309020f040b0f18060a050a080d03050603031e030a0e0c0a151709030901140f07021507060617120702060306040504050f 67
    0x20300741e85008400303003240300d0b1010100001090a2a0000000c9002e8945a0703d000410000550002c0c1d1401c1404001015003105166034605441041410b800c4910b80c02020244101803415040000c0128142c809113a030094100322000d000e00890302d000c3d00314415808000c0c148010084901001035a103001d010380411640c040c1c9424448241031440d402400b522055840220a43c9801c0c201650341c2c0b41101c00100300746e954000715041c1d55062045940410000150700140c0340030f604096910341c4142c811142c140d28225020507148030200e116001080002d207082801440e00348810900640303003448800b0000f08800a05402c81e280c1d40c0e003801104100011038403041c61100152a00d040b807241c0016554080c017148002454031012208030540c161110924184a000000340300e02450000034007003803e015000c03a070108036401d000180500703201122441e41e030203450f00883e40301c7c244020f50030441c00c000080c7e4604182e008147c10a10034002c540c203403900d10785000d0424056180d0807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 435038336 1250 435037086 435037117
    0x16020f0a0f030303050703091e050a2f0411070b0703060b0a031b08090606010509032803021203010303170c0d0603030206060406050411090d051011120a090b04020420 73
    0xb481850361603c90075074494041d0508011440c442c1c0c940f5260034409a90314558040440f40c00000c11109100c1541036682c000c68010000c0140c4d181d9021040c40d0b0410315a8481c0c105402803403a151a0080c80124501c000c01546060150f0f2a0030307003e0b130700080900702410346445000505050040041c0075041c060fa600144852112080b8828120100f43c6901040032070703014010001c4022828507049402424403d0791141d000c0042824644804d49800f1001903d4610701405442c0803c2c903401d0a10941c20b64580070102a6607481c0c500007070001500050700b11100300400c03908020820341003100da4070b20508040e80078401100340c1d00c0581088005810036803d00c81c0300d0801e030185001500c1e003150107014a1882600c407969502a00c0701c0030b0b01c1100000c00d007030180f0405000c100210300018105101d130700b849548102c581d520801c02d0b05030314040e1800003070000308280f0030311041aa00c0743e03002255803a01e408000c080c10090500020b1031030009000031098101d14001c00c86140b03543d085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 435039586 1250 435038336 435038339
    0x2120f0414061b0d03110315011d0303071a0702060925091e180209150d02120a032307030f050405030d08091908163806120316020f0a0f 60
    0x600b660006c140f003150402041c014000000c0b403806006030550801e184c040260001000110704c0883c014000f50b4040c04001055014041c3d15403000e100340210704100319003504c41c3c603003ca80d03400c8112a200300e950000300c2d582c45d9240c42c04080c40c42c001500c0030701c24640e9403030b0340d607000031503184141c5619101c0c100407140c1c89040e00c1d4050300518180070042100044003c0d00452a8588010016500040b51004651107642c41121a01e4001d4004d000a01c03c00081401d060f030f64020a44d05601003860a6003943d80d196024614441911070201c02900f44040c0e580c081d65a10000001c80081c0001408003280ea40c804005451a11032150348100e214105085180e017014650900d29004480010300c6101242c2071000710707241130300c0742001e0020300c1e1264244540045010200c55103202d4070105803500308450b0164090901d550070080300c4054480382c0c100150880d050008050540003800200c420909461a0a0603e0b0018060000188103080040c661302e0140d00494901c002d0002c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 435040836 1250 435039586 435039613
    0x7090902310c1d1c0f0804060e0f15031b0a030b0a050d0203060408130e0109020c06070309030207050d030908010203090f0f060c030c0c151602120f0414061b 69
    0x2450181d42c420704020908a880400c024102141c009219001e01141d0640c00703c0c10302c0075401c001d50365400c0541380003e44914a4182106d5006104080c0081c001c40c420702c0c1d151038020401e580f44040181400e0840c1642e1003030760101e0300010003150440301006002da90042025004040820095030005130002d10101000001c044542016010344490100c050060b00d0000b51580c0050300028440c0d140d40281c0c1d90001500c00640080440c42e0b130800000411441301d070060b1480901150503540e00d41e4883c2c00881c01c80361080301c0680182e00c8400100290700f0460304c0c1512682c081e140c08800c50380c8608405003640d20036101004030741e0202003c1d42014400f401070052091007580035007a141000e00300c9185a000c080d054030620040012050b00310320042003d11580180c50880340102d19100d034010940003070500f00c88016010300c0d054002461090310443c1d103648410818030f8146800c0c0009020300400c4004015041682001407291603084441caa41244220500405c1ea4054000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 435042086 1250 435040836 435040841
    0x3010501140a091506080907080a0b0601170402010f03020d06030203011d070b0a0e060a12050a06050427080a030b0303030903030a0609061203110102040f1403060601050c0709090231 80
    0x41c4200700c440e1805090142044030000707414200d80d10303071a081c001e42d200c07810954141088c40d40300d00d2151140e864403204210030380f901c031445144262202016101e40c40c1010006520840b8028000f6110103001501c507400303907024012404080400085507900caa0120b803c513220070241c2d8940d41407c405c519a28182000400c0141c1281918503007030804840c0042c03c000b41c800f211034030400020031000e1803248185011050529561800d010504003401c0e010002c140f039010310f034061801c103458048030040344811210500e101052030303e4003403590344504103140c0115050703004150300d61024007410398007000a58012240302018540d281040000041203800c40e900942e0618240f0b002004020304545050040b160517040c04608000c041068500a2049410114100301e500780081011506070014800b1188254101c40403510740f0703001900d55009070504001c696014003414801c00449400c0440400c0c03018010000c1e4500c10003c288042048102003901894003004800c1c078002e0a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 435043336 1250 435042086 435042089
    0x6020105160e150904091e02130203150121090302062203200c06040f0303080a09170c010b10050a18061d010203310b03160f03090203010501140a 64
    0x5007402c001c8812420b0204645150807040c00f40d00c1500825020155212900180c03689503100d1686179001d0355101c5036100c45014403800340d010b155001a0200202403910859001c1c2990a400d158800d9980004580341030114a088201d0b800e4003030b41c690b012800c2d0140b5074501e07100c2c0e0064002460302840714014400781c6c00078111001801507110300441c1d084072400d203420700c1c410f45086581141c1803196240480140b034483d081f843c00540006c540205051040940c0d00c03923901ca010648a0117000d105885e1507490207094640c80901e60594410750744d00415120440304008560000d20f540003032032606049400c035000c15000a4810b90302a030040c0b18000545800b1445920310b800c200380180b083c0d50002080c2d0340440682c2d10862641e0003003058800030b40030700303901030444203100230030420201c43c02c001d1607016042e540c03001c61306803e000c3c26a40f240700d04410207054507100c804100c411120381114582851ba5401c0f0020240e107081c01000c0c040c0601d000950744464401c03040c4100f6070002d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 435044586 1250 435043336 435043381
    0x9031103040e040b040201020f060f0105030f01021306180b070f0c151413170a1b18091104050a0608210405040507110604050120070f032706020105 65
    0x300001d02c02c0810b0500310942142d007160036409130b40c5c0c8a10041c2d14100d920752400d8000e01c01c90b420000302c00c0c10101120f060310340c15800e8800300d101d00030426084c0e0261940084011044d08818010300f440354055043c03424122000780c40c0c10f0350740ca2045541da80710000c107a41001e0310305c0844060101350b040280080007a103400080004070050010030358010760b2988030001c0c90004200904000c21034100002d85203e440082e41e00380490402c07652020343c42ea0132540b03804410400003070854030048070740444960200c0d0092038640500c0320002860b10800807240701c5540718440915865502c40e141c45001c10340000900b160902c1030745464000c001181d044100740d001007020b9880c000b0015078084640070344000c20f41d5210101c0075181b80400468200e021700c41d280401c0f0078440c05410030120384001c0c4c01c0c0c1c03000d05442c10381c04d200c0303510400c200075204544c0001c0040000b4420950321030003480140520005680c10380c021058000d03940c3c070070710051303459406108140845500641e5003810 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 435045836 1250 435044586 435044593
    0x1b170118020f150a2a11151306021605030c061914030103110102010f02031017011b0f080c191110060803121003050613050f070303030c08130c14060408010906090311 73
    0x209580d846851b05040a0724501405940c0d0341d8105085004040d202d00c02064223205101c1e90b101d600007903a485e0705030915100d05600c890009528100801c3d4448a0b03400906082d241c5114a2000c0c4080f1807140514410000c0034517422941c2d80b40c1001850185200b000403c81b0074141d07800082c00d4030b00507001407c0c42481001444075000da02c81d03888089400da00000b61201d000b0401c150300400d11030748462500702d02e4110140c0420740c880d0314681041003640314034843c0e45800c181c0c101c0704d000e0030391400c0d1001500d50820392694020b80b41404943c612004450715107145100c0f440079a0b030a5401041151310100b42141070141044030540c1c08003200400104007407954849540c1c2d8500030301008199a00c00c05908180b180c107104951840070900101e8201540d40d10f4000c1c02806240d510350001503210001c0303503858041c0800143c0c020307000140c081c0445c0c105900d04550b10741c015616540540c00704800030381100e0030b000d801c95950240000080c0b8100070305025003d0440c0c040d02ea0708a81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 435047086 1250 435045836 435045917
    0x62105011a18150d2a0f030f0203011d0907030506130609021005130603020702060f161403090a0510080a0507090906090b010e01020313030f0309031b170118020f150a 73
    0xd220345c4414070243c491b00d04003600c000907400603030040c4002d03221547d4090000001040809032052644c0c605500c41740c001541d83e0b00e03100c20a45036146404000c00c9600407030301290a40486c0281c0c40041c50055500140d0026241c4c0050b0820007050005800304a010480c41c01418004a45900405176410194601600399001030054450ba106080c0040070101e000c0d01d0b0f0007082d9204138045540805524040100040c031966243c001d00d22091250503404404289401c1500071b800c0c8408003034a0b22015500e560550314003134940104940200140340c2400502d1000502808006040d9004005100c19185000418808808203a10306650080200c000341054200fa220200da820201f000e665030b40341d2070104c810108a40c40900494242d850302070350550301d04810f40441d111280b060084403070103107405003a60780e00301403030884024480301c04000d804c00c080c100080349030090071401b43d00d40d040b10a06e000d801c00b1303101c040014000b00f0405c81c030070513140d64452100003400b030340d00424 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 435048336 1250 435047086 435047141
    0x91e0b070e041a1203040f03111f0c06110d150306050f0f0106080901020f0c0c030c040608070e090a0b01080a050c15160303090507062105011a18150d 66
    0x3c3c0c0303014849004111982d2003c03540c01d002d00964016080da80444240e480c7c1e60304203a075815060600b02c52103004424030795800d0175204007000d440140302d034441e6100d141c0691513003001048145d21640f0501c40804c40707248042420f2207100c10400c0c0e401c80c010100c500714106001101c038000c00c061040400d500074856102c410107071450440d0141d20b8250f042e940c0384041180680100d46c4803044071400825516141c14002c01e51001c0fa410650482d4145410f172410001034074000d114940e8103400103c014400003003141c180984c0b022590044801060080d070b074421252509920003407040d0807000040c42041006e0100300901d40048464004803840c03603103028540d1051480078100d034864040954101030003900701d1800f05800400303070781c04071b9520700300a0031001500c09031416140c082031042c002250a8820b81e416540000300101c10303250a1002d44030035034002c50100b000c0b440e41e407210080c160b0741c01c64901402034610f100c5035125180c0c4000076042e6100e400514403018100712445001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 435049586 1250 435048336 435048371
    0x307030816020f0d050301030302011a0f1003090f050f0d030510090e0f06010e01080706020f0a231002191b12120518070b0715091e0b070e04 62
    0x40d046611141d00521100016850b0807840d038464540c82c0120b50001c08469044005503040f20b000750002e021090015108405d426265a00c0d80d501c20308240c0d5010715404d05852282c0d0300700c01402c0004841500f5141c2020100b0514002c480503400b4140805d10b141c0f0070b00000907900301c14103003031181d4109070034580321500240c0507030fa040c0c617038403079904950b90020004803150580700c1d8291911542c50301c4034000f50b11000d020780001d61099040001c0c0719403002030b030042ea118121010b00600c00031070703403402d10030141d55541801941c00d039181e48105050600250320100e007003000041e503e40c0792600c0b1194400104401c2018880316404c40074000014181400340d05a011143c81d9804005213002d543c1c084800c03c1c0c2004407842c250403c804e00e4034469140318022102000c0356200c559076010040f881c071901c4802080500020000848a010703600300c982c4c02d40c426034210817011640001451000ba1465060314610030315000c0c0140250000400210080166020320003001c200515240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 435050836 1250 435049586 435049591
    0x30f0604090c0b1207080c040806011403070305031209160302030c040b0103110a02070807120320122d030618060d0b090a060e0102090a090903030603120c0b060303070308 75
    0x903684a002881c20020412080005000c0221542c0c0c0c80341a0032140e40204801140d600000c1013a400c017240070441c04000340e80c111400f00c001089980e09100b500b84400305401502a0144a40400400014010310103401c110f41036000385c843c0c81c508070841d1480e1011a500b0124102d030b440b20306002503200860811041803068a010903410640380040b8024038a060b00400ca091010840d610650b9000c15204111000328085900c5951646484002e40c840020010081380c04103154040c806080c4c0130580603858000d064503a24040c0990441656200001e41c0e4841000300d40341c80c00021701101301445801c021a00c4500754540b00c004160400c000b192030718440641500003c2d000e036554039141c401a58046110300c0c030380c1801000c1980d0341082c41c0003110311500702849085101014400d541d0840c41c000c0000524901c6c02100c04001c1c8040c00c0160101a00c03003501102280d00368940f101000c29545e500707a0075480c0c82c20004e070601c4001e00241d00c6600200301c0300022a4ac01450b554 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 435052086 1250 435050836 435050839
    0x1908070e0618090a090308150d020d11041b02010e01090b010605180d0f021f0906111c0e01020c0604050a210f0809120d08042004050a090215030f06 65
    0xa6440142001c020380d4103045103442c9038800c4154040220b510788982150211a00c0b9131070384500307602d61904410101c49440801900440c50a02d04800342c40c0240d1011821400740000118005c80b400200d01039035080c488400c50b03000c0042c1c2102c0c80395824812500003a140b44004c21a0460543d1250440a01841203208200300890340c4000100c5101c4443d4000c00018000341562071107140c0214030036042181607100d080a032613a000441c15070240340004201981c0c4001c1c0d050304105050b2a40d210b01c1d280e038881842010000b03417078165210550210f0071056220b0324000951040024507140c484070100c0e002c0e5009200400254031155203000076540a0711060401c0050324110401c4891301c2c5a000d404890300400c0c0e5018041120001c1008460507900a0089805c0c1405a6984c211000c524000034001070700041c0032548501c407140c01c5002401e450000000550001002d40c1c4095444a41d650758a0ba0b0f20300840c90b10b822a41c005109a070780950444c9410505010b900c5c0c00201220b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 435053336 1250 435052086 435052099
    0xc0b0a12020a020c030f010608070f0b030f0a020c010507021506060f09040c050c070902180a06080a05060f0a0f050423040f031206090b03010e21130b0309031908070e 73
    0x380240c0248107113098100043c0485880390031450703070306028020ba84a544041e016828000c5080b001d410b0b401d0741600c800c20484d40c51903c4035100c0f070225a50051440c1c038126400c0c0f140b209451028098540074001c0b9900a003c044d0601c001403040b01c10213041103201d840200056500c1c10040010340700c501004984c00126130b1a900c000352003610501c0703900f46450142102c0400c08412903806018440888120801c4446003582030000205c1d203030203080f01160024000404245d455002144d010101902c40c1c01c41c8880750011074114010780d001034070b0742d020300041842076041603c0b840303003501c0d081d12904003807010404c040d002d0703004091310252a040c603002c42c140c01d16020301219002d844180c0010020951303901540c2d8024003503001000e06c69400c241071404241d20001d00241c0248001c40a00c95444110000054542c0801e48110704441c040d003001074640001d401a62241010802456a400702c132124005c130310502a0f49041881110000e0240e2540e00c00c20088982200341c506 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 435054586 1250 435053336 435053347
    0xc0708011a04051008011d0607170406050a141503060c0a0c020105070c0b041205010f0b011d0f060c0a051608030901050d18260f03130206041208070c0b0a1202 70
    0x4d900c007500494000852541c01c0c0020038829080c80e900301a028050401920b0031921081002c803130030452000ca11041c035521102050108500d07610050300407a00c1980024070741c40d9034500465080040300d402c40d400c00d210720503e02c50306051203110351000c0203c03c843d161540c3e07140003130002c9440f000040e0400c0340104400e402c10501c10050b00285c415001e281c2e40391950b85c0c0c403041018440c254101e0b0603508104d22503042000c0f601441c60406c1058454013101d1155840c0d00c60003c403100d5010f5400f40f022080c0c0300060300c415004102c3c580c01d2201614041c0110b0401a00d807801c04501c040c00c0488403101001000700c0401918821003091900583d1004404901c00240020451250b61510403540031800c004030319125582d07980c801981c02c080702035a500400c8050082000034001c81c00204001402c1c2c13143c0c0a06c10304110f200403e2541407a4441d50307100c004800b00d9000b01e548060000700c00d403e004202c50903030003c02030b01040903c1d000b40008002d10342c200400343d0150060700481ca = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 435055836 1250 435054586 435054601
    0x1006031a18060a0605011b030e01120b040f02090901080703030804150603050f070302010f03110d0b0a082a0402030910050a0b0d030201050109150b0a080a020f0c030c0708011a0405 79
    0x41e41d20340074081198401d0501100d0180100b900c1e00c40c1c20b0104400a40120078650300d89550100b450f015180c210003e080880103485800c01201403212442e55401c1e2181255154418503c5a000c000380050711079581500340090940180c001c00540c0c0e015840070000681d01c84030140e8044e50200c0100c6e020400694000060304003508018660301a0050604140c2d40000d40001164000d07690030311410110f080581c110346800084901c1c070a0200b040000c918103035004050445005446207010554643c0700700d003416107240740c0e00d1480e62900c004502c0707a00c084150b82e02e03101044800318618104041d0381a41c56413110f80c070108094480c40021080c6090f54402c0c40d1416000e00034074007001d424a07000307008110174064101003d00d00401013a00c28611007514003136801e66281d007440c0001c807134026a0b44800c000d20034020250200528201c180030003002e00312107004040115141c1409401c400d040c140c040c0c00c102006d0307250810f00700c1010414198a1180700e4240d800040e10340f035680 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 435057086 1250 435055836 435055861
    0x50f011d0a12050d061805100503070b0702060d0c1d03011407030e01060e130201020f0601120305030405071806090b0301050f0c0a0512040b0714070305180d0c0303050c1006031a 78
    0x10130441490301800044000140782034104030350151100f00110340c0d8054544610b05607a0140a4040d8452402400410f400c0c4c8010112103000400c60342c201445107a46c10305944a040c00c2c000029090b64402c01004a40c0c00c0c0c4410040080b0020b100c412103685055070810b40003800001003680301d4503059400c400a51208000e07214118811280b03240c148003217220310007080c0040307005225800a810700390002107091818ae6040c0407001c4141c07044d94a04a40da9000a8801c6d2050b0242140014801c1c146c0c0031713103d00c0005452400304103103141c81c1d40241104c65258496000344d04203070403c240c228404003440e0f404031035000450b44488080004494602981400c0807064003000c05000601621000c80c038458100d5546446081c103004034482c1c079502424400601044090240d10860112141e60b80c00c001c001500d90080701c8030030344030740c0d200c1038a540c810340103e0307400107180158200070b02c07811907451940c4506000aca4503542c0c4081c2c60103500c000c2244e4248007880071900b00100d20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 435058336 1250 435057086 435057097
    0x60f0f08060603060d120e0a080105010e01050108041505042907021f0f1401050312040e0415140a090327050f010509130506041b1b14010207050f011d0a1205 69
    0x8034190502c00703d0401f40c103080c06050094422200c148001640c0541402080c3c160364414140c030045928000056600e20300c0034100701d0b1802038640d60412a030b0354a1041ccc07881107009010f1103c0f24040800c200c00c0900c0c00c13000c226042d00d809010800710307903000030380c0e890700c00c1c0040c41d42440320a4030010000108060f018600041d130034105401080e8422258941c1a07c004505450007070041058070b54aa1280303128101c4040b0101c03000401107903003d51a00d060b4a0020340128001688091004c0b01110480d8a80c0009907180e04140505134000b5180081a1083d98103065110070050200c43e080e41511840344100d114106a0074079910517020358880340d0f0094038181207100d41700c4541c006802e08481541c0141d20b8882a00c042c010800c04036100c0062039101c0100c2501c030403d07200b01400345600d0641c7c0d44a084204140703840d030309100400065000340007501c1c0004104181d64203481d9203039101c0d0031140d840f143d89100d41c12b001c00e17800402d070f500c1079040c07950f500b02040503500350049 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 435059586 1250 435058336 435058343
    0x9010f0b2707111e070b03040312021e03090d080108060621030904020a020a0b0a0b01090e370e0a03090b03100f0b091804080a05072406060f0f08060603060d 69
    0x101d180750101c100780c03070800740c4c00c1c3d0022000360b4140da500e0381d030b0041150004032030240008450414041c801e81e040d60043c90b10013801d0300d40001d0b4120400b080186070307200b41e4510600358001c01200201c5584014845d0140046102811580c01e281e80002d21a0070f217a1030400c240c054130780c044c20003038104008840d0119009442951203070092240a91102c075900f0054412052610004100b0718042c4514071030400141c507481e14543c10003000f2041d0407401000c0540034600c58540c61a420405c103400044000610032541e4110b4141480c030040c2c426003001d5800e035a12404c10140025002500742064500110045481e41e6030714010480807075460740941c132089110400403401c480380c1401884426070030340701050301750411200c103401040100c0303001e00401010b018102e900e610401c002c0045601414404414a0500040415015840e485d401074107541c1c6201f00152500040840310003842400c000001c90cc52070741c0a072070712200604c0315200d2040000012070320764804d040316101540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 435060836 1250 435059586 435059593
    0x319050403120504060f030b010206070e010507060f0204052707030905070314030a03060e1015120e01060608010803031003022103180103050c271809010f0b270711 72
    0x1d01c2c0ca0040c19661140c029480003809400d100c03010240a130240401c11441070340107107041da0710503004850401852255034100407007008105d01082c0035004010342e00076000001603490f807902d0104651021900c040394151945c0e0f10194032743d044c10080b010341c0700304141404181c0c0d15213894118108400d9820041c81d502c0c0c0088000c585000000283ca040442900c1c00c210054540403041007949040341c2d004e401132400c0d58180320b80302111602d011b00611074101a9203031400c2c2c00008007520317030500003015240e40d10b01041159130381c400180c03401040c0031b0700070350701d18140546410800074107070101a0245c2c240b0074031040801c3d07101c00d507090034205400c2542d0701c60321813144440f4200003101000e8000b90400c00815900240042190740014440c0308901200030554140040a1941508950701c0318918064030401030150010a00c01d1402c440001801e003c103105d568116240b403000c080c004d0318034011340000c3c00350480710801e482c0b002080882c100d030f6500204445050030111380f50103501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 435062086 1250 435060836 435060863
    0x402040e07030906053607151e0c0b0408070203030d0e010f050609010510031806021209120f0a110f030a030e0c06031510090e1302011b050319050403 66
    0x550683c40100d20342d210b0391041c45030b500d46140301c5a405e00c0d0b4080e61403510205071111251051075400300b0080c1d40904017540c0103596122000091042c11078440e0000c101043e0a078880826080300501c100350329810b02c404619210b03203031160740c210300600040018000082075415558200155513421407159010700000d0381c09155079002c0c0600e0000b5000316410303d4049680c070b140c07564840c2d050350703006800b1520f0038a1304003080b009000306400c082600e0951211040220b000c60000b400580304030711402d02ca070300f40038000300d1030903042000f12410f50303400340901c0c0f0380f09554004480801a107480c10029408625407864248080c0100031074640c4000110f5501e040d8054200c91800c4507040d0584106c86007075001c0c040d01e031004541c9542a00c403402d01e501210710f03040031900c8244803030380b802d150030703a840b0940035003035070815108601e60700d02c3e1140e003c00319a8495100c1c070103020300040140740d00c0090741e580350b96806602c0007010486c4050500c400940c0c0b04405071002140c11060911080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 435063336 1250 435062086 435062101
    0xa110a0c050102040803180906010c05030306061e040f080706020721020103020d05190c0e090103020d1a0108212106240903010c0207080a02012607031d010606020307110402040e 78
    0x1191087c8281d030040c0000e80c0029115801503035000281600a000366185030389500400c40c217036001810000c0229400144030340624185009071002d040740d141c04004031801c2c4110b00b80384c95000d60052045600c042c07014060703076240d07411420030068203402c90034000c0480e200690190090005030000c0900d0301c2c04010382d0307803110403c41440104502c070402401009100481d240d0000088241e0040c1c114001080141010780c14902d03554000e0300310030030504c4800b24803c4c4c1e1000a07400700130194480c00c11201c0d1f823a0030b10440c911500f40d42c000c66180c118114440d81c10561006200c1c86d0340301c82c41c1c000403050f80744ca40c3e1344404020f2001007840d4411080452103402d03005421000c1c080d41c03818406400b03850001460b00c007640c10100081506400d15801180c1c0f6010070071030304031180d0b440c1c1707069000c60245c414801d00899030380d00e01180c0c40452948000c03c00a00060002035681080301c10450f07035030003204a6010076000ba2003401c114a04101041c040c0c0300341c0c0c2c09803082035081010480c14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 435064586 1250 435063336 435063367
    0x12030209101e09062c0d030c02030c090105090703110f0d061a0702091302010e10030504030f051305040f0e060c0a090906031e02030708070803070501050a110a0c050102040803 77
    0x8400c050102400030420048048a02d5100d500448011401700341c00c0d152035202c8103411044010040c6005400c00d02c0140101d5600340c3e0450007140810710310804a800c610b014480c0c1290100203840140c802c0d031400c00024108440507041d43c05069642d084501e0110206085503005071060140656642c960010392004050a110702c102040d42c0015514074114080112030304a900100f003486a62201c580c84c041551223140704074140010141015025111000f038840d0310301050310001034600c1c00e0f04010f81103032040d90360300041003410066640c0110440c82c61000703840040d18001034040c030140740d03000200b00c5401041e8051050104000a51507144001c0921251a503142860280d5441481060b01c046003c0207081c4010034051030071a4203041f040d1400680020b0842c2e400e6582c9910013801c0a15a8001c00d085400010f180c4091203403d0107441d800890145040204520304042402140500e40c002c1c01040305603851803042c00825010750b0060f0030020309982d551443c0c60540350300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 435065836 1250 435064586 435064607
    0xa0c050d021b0a0f06110a0b010306140601020d1d030a151506030e100902040b04050a06140a0e0402010806033421080318030d0522050a1203020910 65
    0x90414840c82d2040302410050203040444078800d065003581800c0c000103407102988031005240d80d01c50341c861117000c500c101c041c850086004410000310f19105a140d2442124002c15031415540701d0088041401c1d8401007403c2c1c60384400c4207900350304600000080c00c007120500090b0103140d00c1240c180241d80c440e030100380c15450400f494100c007075984c50241c0540f0720310400b101181e0052029440007041c1508009013440c4010310008806519500243c100e4000b564420121035880c44184140294482c000f82c00303020450300703500800d241007007060558074018002410000d59801088407520200027100071015032000c3c04001c04014a00b0048100700341c141c0f0700058122150000307008504012204900c0072503240c2c14000c07030113030315034550552000e001c40030110b4031086072040041c000d10280c010542d10900125550a11120080c15000051480c4802d0402450803000113500000d40c03020617070340012400d00344440040c040e0f000380101200300b5007100006038003034401d591007100b40070f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 435067086 1250 435065836 435065863
    0x2151e090102210304062d0501060f05090901090f0908030106111236060d061d06030a0312150e0601021623030a060603080c0c03060c070303020a0c050d02 68
    0x3001103d500c000503040300720110401c266440c040021901044454000d100c620307001c41e08000c0390407010354064541510541e01d0705076260380d610040c84419800030610040d101240b80035403e0503119400a15030400610880700640d6841c1c0c070b05042c42040d0341080340323201d4215008503140d6a540401501100e0074028042c1c91f80034601144e4500107400e401d682408840340b0341d488021501d01421081c03201e0200c902985030008104e200c0c11640e8400081440050034040400d0817403401070b030250305046014191121280400803c0816200003501c100c80c0368041c500040c0d0840301c203803002e0090654110050799100c100c0800b080079078070816450300410080e4211158003942e010f21800a24542c0500e01883c00030b031f42d070f18015031241010305803035100050550f029142107503216001c8a61503481111038100224441004000604c003a0204d94425806800ba40c901605128040d1041783c00c0142490380c0030038030015280c480ea0b400155140c1c45001ca0307400022100c400f03903503540503101e0b00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 435068336 1250 435067086 435067093
    0x140915060a0b12150d0c03021909020a02010c031803020309011202070501181e050c1512090106051e01080c070515091b0a050604050904031106040807030e03031602151e090102 77
    0x4c1d050781042111003182c10780140c0004003150030b5908110b4014800c41c40c1191607420704070007041070400ba2008160b45041c139000094a40380d41c40010f0141c1e024550708002103100d80382d08201294022040792120b820074a8200c0d0001c5413030322040d009028000004d40781e58600f4400c0b100c010040b1540d000818042d0885502e0745104081c440c1205410340d1004115801c40d4824110900b088a0440d2120311a0085281000382c07125101c2d090000803a0250380c80e80d10349a0030000d90405c810301c1410a1504070800c02c000c4038000001c0e000d42d1000c2c14003203428000144200070307c03100780220084101c04145045d8a4201240740341d603a44520004140c1d0032603403900c041c847d8900000e940c012203002a110030300307140c5403104100c6c003000000d0007901440100b85c1d0200342d1180a0044a1089100d418007075203814550400414805960440c00d0080c3d00410124461540100c5a84140f541c100c1d00d1580841815402d00c4240c001c461540611841081c2d101e5092491400901030a280030307802c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 435069586 1250 435068336 435068371
    0x41a1206061612050c0f01061502030c0304050d1a16031802030606040b01020313030b040516081903050906131505030115050904060f0315140915060a0b12 68
    0x401a00d8818142501032020902c1c0c1c002c00060203a50b905491182c41e81801030422120030b41403800d08107508000400c40c0d40d01d02d82400040b401607900044002544025410718429892041d507d00c1240140d911841d4200340b5002000b840d6400b150316102e00701610b03e86802c01000c1d5800c000f074490101400700b0b0910700f1b0301070310719a401c81220203140c005005011b19103814042c840101078a80c01d040c11400104403026a0081c8000600c00031032150038111030b02e103020306110f410507255000181406011703080030444102c0000e07056004400c506509649051246015030710381c4074a156090b0082008900203600c0d1740000030010403588600c54024030900c2d0700c081100d4500c0309000c0d103902020719900340d00b1041c0c4144040c11400da805000007410030786a40c04203041c0115540122041c400c030030303100201c55010380251141d001c213030035044407035061042503d84c440c0d00e0341d0202070140c400300d00004e245035075905025000f86824024950384214170007502080c0352040b6a01f4100e800c16001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 435070836 1250 435069586 435069589
    0xf030806040e0309061c060806270309090f0a38030a17071b12030f0c0302030a1d0909070e010b03010515030703090203100614060f0d020906041a1206 66
    0x7151541d15008105c1840e0080010241040740081c0c100c2c11101a074130040410503400400045005107100c00b003076100d050440a04c0d040d030700004500300302190400d0000c00069110440e0540d0050200c00b0408a2542c5040300c80c002004020210841c03503400e94a1003801c40400400031751030010700c1402c40e124040c0203062640e10300031400e00920a4403130742c4080b0701c04184000038060313442c0324107410b40442002d854900b001c0e801a0b0041c0300342030384148614041580040002c42d04410038201540001c0b180d072400b81d01c034000d60301c41400388408022940c40e02041c0890068802c0c8008040e540325041c02240303c1e80d20f9800e406601d0545855000200300203011601b66030488800410000480407500c91600c0b01d0f4201808038020b240d00c4041080050358184000c0e200c024040c4c000003440c524002c02c2013003c0c1c0f85900d51078054002000b0101d04020110300321148030002400141c0c0e00d5001d40701240340c610950340804440f90000c0c86a02d442c1d01000c0c020121100f850301e0304281d5884000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 435071942 1106 435070836 435070843
    0x7030908010509280c03061d06010e270d050a090504050f040501050106030b0603310501140604020a050a0c020a050a091d010203070507030305130f030806040e 70
    0x703010b500400c1e149040301680c0322078080c114150102a0715108241745130703800003401140e115407203103402d0728000020110700c880d10000c544140d80e50b00203490380c1450503240c0140010244078a880c8180d91030b0700070250303000ca1202500c1d260101200650b0a40d010940003020721444d02000a000e81d103a20603180714034a640304001ca1450a0320b0b1480c03c440e0160000414145003000b15603d540318001075030fa0011090441c0c4c508c556016401081e040c0c00080307200082c09400d404202082810f4121816090f8010718403000d0740c0b1903504000590148074480800900c062150416840c0300f00e00c08402c81e4009400301c25101d072140041002c0002c540c11006802e40c40e41ca213403c02d410070780d064510701d03008480210704500380b15030003c02c140304281d006001c264894001c5000b401d07200181c0c401496100083c90400c135090f18000d440f1501c102d542070b109520717161440700e0018011 = true := by decide +kernel

theorem cover : BRFrame.Cov 434892086 435071942 := by
  have h0 := BRFrame.cov_init 434892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 434892086 ≤ n) (h2 : n < 435071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
