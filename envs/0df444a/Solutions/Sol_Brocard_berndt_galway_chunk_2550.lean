-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2550
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:24.820365+00:00
-- url     : https://prove2.me/submissions/5f3df5ee-9839-4436-9044-cbc7174083d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 458453237 ≤ n < 458633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 458454487 1250 458453237 458453321
    0xf090b160320070f09060e01180f230603070f0b0f13030c060206010611120c031207030f0b040e0a06052224020304020312090301060e01080f1c0c02040b0d0501140901 73
    0x40041940440c80140840c101e0603c1e852f0400d242050016194070100b18010614030380000c0c0c945401e0f0070180d80b400705106000f121b10f8000d00c20044020350030301405c2c03900a81d250152500d0718046903070402c0801500119124212080203015403070b81040f600340580b0300e13030824a0703c901202540d141d41c3d811000b50321118290004070304005010038019118640e130212800078060421b80800380c007600d061400124400e15286224040c9d180c54003644c4112480c2c180502510f0400d5210314000d070030014500ca100200c0102150201000c8560749881940185141000002034030b01d60fa062001054080e00c13000d0040c410300016030b4000c101007860100740380c413141c1e4440b44071303012030702401255119a101f800010000940d00f0320200740143e5001600c019501b80702040d220110948080041e01000a4a041703010001801c082e40401d03509a8010100e5442a100e9543c050030340342841c00e00610200c01c1c1c070500000907424040c1c240070390340c0494001c00e02600e8041c030110b8100070b10003032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 458455737 1250 458454487 458454509
    0x71e0303080c0f0d0e0c040f02041a0d110307050309060f070522080703061d010c090b0f0405060a05070b07020601060c110a05041401060f090b160320070f09060e01 72
    0x60f42c4503084241182c600c448070182c24407030248143c1c5400e440d544813446445c0540d0511160810708a814401c580603a41c207020000e1800720107a8031030315940c00c07000c1c0004281e540c4040c20181107142601445c490740c8503030346044d941d00c2c0030307802c00b81008406026580c1c040100c0d014800084d41207003c2d61418404212407440741800c03034603250403804143e0301006580c081c082010050040c240c010722150b62803060100d2005c5654ac00307003400c031604102c0500004410070340c1403007800c050000802444a08407440d509090f12080000c940c0d6001c1c103883c5011450000f405010000141483c035840b001c00c3c0060000d41d03141aa0191060f681500c0040c0382d80080c200710703000d0b6921960208080c01c0e02510410a00d00040d030304086140c1c0a003d242d01140c03240e00d2249003a88118101c1e001d950300d001c000ca091500903010011200440d401c00c03800d014020b080101284100d8001070000a000c2c4010800603280c03460310030340e114240c0c102c821800d0505200340084444c0c8082c503070441d02000e8038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 458456987 1250 458455737 458455747
    0x9120b061201151712040b03011205100612051009080a0309020a03150c120207081206040212091f14040b070908030703030b010f021b1c0c08071e0303080c 68
    0xd190040288249200c0615100b10f00800c0d0205001c2d02d44418080c188125030951240800004850090303110b0011030f210100014000701442182641501f84150100c032082d94600c0104010742d41541c1000c024001d0900d2580c040c02070030060501c480000307004c10010009a41c0b9500c445110780c103081d005050300d17416084110f4441d1174034500115044042a01c0d800305041c044c0c0302038065a40b8500c0001c040b94070154aa10141c800c0340d11690784160300c42d00d840c000d012103842565000300103a074000c0e1300344501c0c0c0d00300c4a02440300740300e01144000b802c0455404071510480da4001541820054038023561540301d04440102d550300303e078000c2d0415440f6582c1c400308a030401415000b810042c04086601410950035812618600c9403d803200000c4c0d24400100702d03a04c05001c1900f00603404231980c880f24604141c0c540c3c1c0041400c0d003100d0829240240c8a5a910023043e40c000d01c9a64080e040c108549801000c0810440c400000e40071421840c40d28004c01d040000340401c40c170a500050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 458458237 1250 458456987 458457019
    0x150216080c030705071d0f070c06110f0d090c1208040b09030309100c03030b0f0907031a0303040e0405010605010e0315060105070b01030f0c1e06031104170d09120b06 73
    0xc15510340f140d10100700ea80c0c1e152104518189100300245500711002e4180116814465074900c01d40715060b9682c0c0c580401340903441e2180a07040d031403503000da811f80030001d0120b100580c2c0000c0c40c4c0410b01002c00f248501c01031602e100001d0007640711341060035034800a180040c544000720303404c954100301103580311212039000902758031600c8a2142e028101c40c01c05e803a82500000d5080303040c1d00989040143c02540424011241464480b040d846541400041d5060b4026801045112007031701c241c1901060348030110b403542e4010f070000403001c403403107080004020003406818081c000038603000c41c503c15144046035803500b44404800740c1841f6000003440d507074814001d844003240c006541c0c0740035503940e04000c1c0419480400640c2d407014115000304800003514508040343c0700302c3c240b00410301e2a001c1c08400401110702c404401d01401c21000810b880d1411400c000c444604010300f0700f00e0002900070384010259441414072001c1d1424010105411207485582310348255040705081013242 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 458459487 1250 458458237 458458243
    0xc02040f0507080907120f02100c020306101a0406050a121503060207050f0a02030c240c0102090a0f08060609070318030914040b30030c0307150216080c 67
    0x4080340a00352400d4100802168010441c80c01041c0d0541520401502c1d10f07244a1030642080303010341005c000b0300d08100181001c04080300c900c4c9071450400300e0035071560300081c10103800391406119401c0d41882070040d00b61544161a50070f0502c080d56207454507184014056018022540c81880040070840d400d4102d5230300880031410825402c25110f54580c6001c500a400c0070209881520803c00303900300300100080c40100c1150001c008001110308102080894000741d08444034032182004952007041c581c03406851221001000507803100130f180c0504c07500d0310382c6511030842001d000c181048800070119445411160590304042203558104084c1c0c003802240101990200c64589103006065102da080000c3e250490780000410304000104800e0b20320201c071469012140610411000020f880010844d030030740000000c011047e0322241d41541c0028017184040e810003d1a082003052030344850185002040c011800e0030116050008204007654000745407000c0013500320f1082d0303c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 458460737 1250 458459487 458459501
    0x905011404150e0c07031706151b030d060303031103040309090507031b09030c170c0405040528030e12150c0d0c090f2705061f05030609071b030c0204 66
    0x240c0c0344603107203091032860440580c0c06480c00fa00083c004ca00c01c0d0041406401c2010f019a0005000c0400b00c41d10309c420102940c0640e6400c00d00c803100030003200010f502800945000505000300280c0c4901d141006802c1d58a10500c455061008000b04000030b90080c80c0401982e50342e52000415a8560340240e004004106403004100c05012040510b140c0c0701400d03905032441008260003050341d55880b2440189081c01001860704861450316042c01d06900c81a07006001d64115018a0b107211059003003455649a000c58054030052250b00b41038100b03090300390044094440310701c0d840d03901c0c80da603454420b031800d82e40415080710042170038a003c4100f030341d43c5400c118800b0004150000000707441031840b03100f01e841114030b41c1c00c0042c882202105a0f11840c5107040798010510003140d03004000c010080115600c81e021010b18992021410300c804540919600d0329a924100b10003042007511006003500c0400800c222030070220f100d5800e0315044183e00d81404a420221440020701410312 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 458461987 1250 458460737 458460749
    0x50d080c07030c0e160201150b0f04030c08060a240302120c13020c07050f090112060f0203010b0d3801090b0d09020a0602010c08010b03060f030a08030709090501140415 74
    0x20303500081003080040010358003480d0445e10310443c0e102901001d0b0f00780c9882006c0b00d0001062803404000303690130500181189030005800e00e240585030f990f02501281c1e40e03000408164003000c10000300510078401c04101000002c100500f010b1078001424040b074544c00300a0180e0040e41e0f42a400e550108140ea640001c0204040034814030111040000d4202d291000d80c50321504c0d90005250a00c040d410f08200380140c5401d100340c0c2480107200007040041012a6083d0b903442001038107070f440307201440c040c0040e4544a82d580d00b4079078040341a5490700d1540381f454102c92010300e00b5940304084a60107100c40e40080500b903000180182c51511642d441a6001540050286030b8241c0eaa40302c003400502c21220b1800f16070300e69608030300300d071000140c03400450361407401804184560700c060f40e40700c540140100240324410300402e040141c0004121580003000c014802c0e601d0b009800070007c0e0400a01c03c0201d985044003203071420b20111402402140d4405100d010107200500240152030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 458463237 1250 458461987 458462003
    0xb1309230708090d11120a20011a1206010603230f070f080106020d0c02040e010f091104140f0403050c0f061006080f1602010b180105100801050d080c0703 68
    0xd4003070406080000200c0d04000c0754040d1041c14016280a00c0c0c0403201d4041c14030040c00e508111011030300450b84210501c03414030400755806140940c030210842d5640045c00008a05880f06444006078400d29019645c42400d00801d0441c07a44000941c00741164040d10380070418403a84400804000600b00189604100c200c04009000160250280c005c0780e00740e403407287c64440c4c84000c48020100303001d0f040040e0485040c503410307280305048662007140000c0c070000308007070900d0545085800d02c2c80400f42240d120b8224800384404400c1c40000c0002c1500d007070020002c4c01080480c1c8802c01001d05040007250300118060621800035900401103d100710f031080e80142c100303595280c00c22a06441482d100c9440418079502c03030411140505000032a10382c0b40c1c6c4032150010603030600c0d1b00404045642e61710318a62265100c551407030302c4600260340d100480d41000203221078001c0d001031030024855800010040740e15060780c60740d5103640104036a51130300034040c42c1d141080200c0d400503011007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 458464487 1250 458463237 458463241
    0x509090a0605150c0d022802030313140405090c0a05090414030408030c121315021006060302090406090903050a1b0605010e0a05060a0b03061201181b0b130923 70
    0x4416803009206041600045581244641504a9487c1180501c0d40c00326999511a103881380003141c0e00c03090311071005068905024800211403e00c80c034583c0183e120b8066600601600c0c24188a040d8110400310060014180701501203030444540b1312989000b00d2480c00010144000b2842c8645005000350a8903951070380c480242d5501e0b00301c2100d4081a01030f041c0c0b00080c403e940340c01c1729075050450b924640018a005e07400c00d000c400b0081403005602803450192400f0361030f8440c4001809403a2001a210b80031907060104452040c2c0002c05a1480c203000e01d800700341c000c42079400f00303609131400d9241d551050703261301201551100020140d0b41400300208400390243d40715449001c600f842004980e44e580200003a00701301d84200e01745403000300081041800c00141c50030102500c1000420b5038180791010380c0c04c030281110141d60142140450403c184c00325442d610042144040103810800502105107103040e59114165005070344003d94505807000499200d80318500c81034900c114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 458465737 1250 458464487 458464519
    0x140f04031a0a0506210313031b0b0c07050409030c05030c060403080f0412030c020307020d0b0403020609120d15030f1520030f060a080303071707050a0509090a0605 72
    0x10414480e42600010388080080c03015a035500c90f0b58410140140340c84a282c02c0200c808081c11070f84001c0345194041003000c841002c0d8010207400040d4407529519a00c0c0700002c20140361064260010350007820101320852048200103071003815650102d80001d00d079036940c40c0c107940c0d44c001024001c015000201c1c102000b480d0114506100d5030003078a60b24515a1400480d84000c20f003114000c0846141c41d0f13819100720311941c04411a80e4040c0101d0340303004c086800046080c00d200364102d500413048420001003590601031560080d40240040211400d20101c94889014038101001e10342d50b074039290400c2c240c034809030500950700070300101003124082c109091620300003810302401900b083e0701c09544c03100801c0c07510b0b802c4524101d82d50941c0c1395100310402444e0701524250f88124008004170702181c051000754000e54840e00e44a5940d01840c40051043d4001421042400030522035101c0060304a8219903a0b090101c808001e04d0f0746410800f00280b5064101c6900224125442c01003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 458466987 1250 458465737 458465753
    0xa0e060604050a170c010c050a230a0807050d0806090f07020114090f12030c040b03040c09050c120a06121203061a0d0e0c220209031b10020d050a140f0403 68
    0x61380c54800d41c1e1900003041c00554448119580080c590382c80907041c48045002c030201480c0420f000d1100050904020b45000d02e0051050f0b4203550035400062000c003001010450240d44100070f0600707650790b00d8403100241c41d144000f4526044c0700322850000c2e205510039441042c7c41c90700071003846a81e0a02d140100d03076a199006a640161080c4401c410303c900d0941c058911544240c5215031034941001b0801d12190409002118401485c80001c5440c4c1840e0007058480e205600000b0b45074500e03034039050528040a02000c038150701d0f00b41d0a000c0003110720185114190410380314002055404811801030003a42d00180b01001c504c2c145070403281512000705000c070300081c8140700d5140000e040c5134880ca1184001c07544440e400d084400c49480a100140e68600b15920042c2000d01840101e4244804994110070301c2c1001084664a8504480c0c00c5030b400d10b5920007080151801400a041403090303000680c1800210040c203003c4030410002c0b28030341004142c1291300d969507440d02a003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 458468237 1250 458466987 458467019
    0x1081c02010b0310060302010e0d0b060d060605131e060b041202030c0a0b0a0914090a2d020301030c090507080c09031f051501050a0f03020306060d180b0c090a0e060604050a 76
    0x8005011805c404600b03243c00030ac500c0355160000b03a03190031034440c4001c1122501404d001124442e032107103400141503880d101d00d43d6001195034004101029107402040380c100551007040c416518011043c030100b5888010360b803d0b00c11100c40e00c910b00c2801d00000c3d2421400c442c0c000e6001402c000046010340c4010041c020304001034440103000c0c1c0d02c8494180c4690b48514000e40c00c4010600002c0021006802660b80060100c2000b1043c5054140004c60402c40b850315071240768000004000701b0030600c406800411140d0410030040c149840001c2180d82c020344444d030007407804180b01c41565400d10550421503201c08030b1124000c40c091044003d4a402c86d08540c5018030300440c210700394003c07011510b00c002155610074000d4441e41c800d070000e42019141c0c50b0410424440d01c02202e040c0d103e200000d03000740b44104486403080c52705045032400200b6906d04a901445000e01c41e0701d644501c5010b541e4221100390941c0e41c0c03080800c0e5640210b0b84542d40c031120110001500c0712580120307074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 458469487 1250 458468237 458468239
    0x140f09040e011b030c170c0f04060503060102100207080d0b031f09021c02013c030f0b03010b01090504330305070f0b1215040c0203090f0901081c02010b0310060302 72
    0x40c2041d40030041030f402c039a85c08420380041150301c014804021841030499070300c13828030742c02c1509103054600420783c6a042a000304000c2003000040c810b1560301000701000342e140d100025450000941d495070307024022a0396120f1000c2e104e40103400666428041e0510441c1106201131824400c1c4140a01a241c2c0b0350050b4011107025403607010800c032008803464030300c0d0181c4800d54015040102e4845140c0c1c0104c0c002c0d0340710350940021074041992254166940843d542c045070b002100d41c14801140c108040b0940700ba8580f011181e1140d030041c1e810012a2011103000a105410f1030740a40e1707041c8030620030155001c0842819400086040f036010a0700c0c0104225070040d81c5801401c2c0e183c0119020340401d0003018000320000c2d450648103160b103c004000d1243c0307140d15201c00b04064852504805d80076070000b10300c0e20b0b5141441c01403002d1b000300071220170009500d05143c40d52289029020400079039064605100000d0007504000e065070740242c222032070120003031340910080036030740812 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 458470737 1250 458469487 458469521
    0xf0609100b0f09010303110705090403050301030b10050a180f02120907081b130b12061509160302070c0b04030c050405181b010210050a150f06140f09040e01 69
    0x51016420302510ba40c06188002d426020030780d0940c0c03003d40c0d50014003140280644201400072405441d11180726005500c2030f2200f985039411442c00700d0a80710300804040b0034080104080010790b80780c1280104840c0e0713111024070107003454234403c0044c105c03408102e85207070f00000d0826241c0c50b038920820300c2607503058141c5001c9920303640d4036510781310840050604080840801d90283c84c1c00c41801c0060341009a0000f01140d0040101c2c0100044000c07080c043d0b00080200203480c01814144400e242e0112010040c51900c0d26248801c07090680805080640c0801e074201009410b203181406000741c00d1082d074980340e07070349888006051140542c2d0300850070080071514801e0404090110f800140c006060307a01604210034450350700c0204c8040c114402c680ca080e41646003440342c0c46c021921842e01040703100036840608110080c940c88411504802d9004000e0030740d01c65030b0114130f4800c3c080d44503625912100c0000b00c601400e5107142d48540f600e03c80d8401d2400c154421381c0b0144014440c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 458471987 1250 458470737 458470751
    0x21040303091e0b0313050d020a0303061202010c26030a0e0106050d0f0f02030309041103010305010c0810060e040209060d050906060402091020010e0604210f050a020f060910 76
    0x4225442e0070702c40c1540e080031410003024041140280041c3d81c0c481015520003109401030f0315100d2a080202c00302601507001655440c0605906010315400f40c4070002c1c500051047c1d40d80028080908041d02030000ea4844029804080490085400040940c1a840c0d141c0c1011803415000704001c04510344158a05100003a203402d0842e44156141d07002420781a506050303880725000480303407003c100d070715001c02c0020039039907038543c0b10b415200301c100d90b407150300d960562800310300319103a44403910280003642d130402003580c15001c071050951f60380c0c7ca0304180440b100b00c04900a806410401944507502003800101d03c0203a9000e2881403140600f200c06940711441440220312500707041ea50025080601c07210313503030b0240083c1448110705029078400d100844500c1800c4601c00c600b109144e800800a01c4284060312100d640c100b00400c040008000380280050480170240020809200c1d021880c1c100d46402404101d0700720691505580052a010307459a4503a4a5000000e54603846c00c61 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 458473237 1250 458471987 458471999
    0x11e0e0105070509061308031b1e060c130e010b0705060f1504090206070b01030c03120513121a01080106060228020405180f0102070605060402070b07112104030309 72
    0x1e07490091000e03440d0940b500c42c500003408282e502c40c1807030b2410f20021180015440303000700010000d040c081c60003031155814403c081d40c105480d0003d550064050341954144028002c5003140e0040c008240065403107505003108940c20001c0c0d8484040d400c0000b000041c00086003004060481c4104180d440680c3d84540201600c2001c0d903207501c0b0002e20b241031030341c641060b40c0038005c4075000403d15420410980e844410882c0260800c0301c002d000c01344100b04100c6000320812010300c180c140a070504002c08015500300f4160f02c94030340c0c1c082e4018000c030b090210790301802c5140f07000039018150310343e19802c4440c080e14a5200b04c44c010b21849071484805110041a00130648440100c0411000f29800704405010060030102d141c0030656000e81c0c070780008000c4140410341e5000050b0321801c442c00c1c0b034802c98000510040c022801005484005003800c03d00c1c80d40a4120700b0314980140300b0807070b03c07480e040c44040015125000c014044100302e4141001c0c1045030b200b030f0342d13110703a075074881c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 458474487 1250 458473237 458473241
    0xb0f06090f01030201030509070915080d0203070f02130207020402070308010503121611012a1509050d03091103030409050f01090c02070623030106080a0501170d20011e0e01 76
    0x1158070360386150312001400198800d07003225400082d200b08850302192100b0036042102c4a0b050850222040030804218a41d0144581c50300204140041c5042030015250709812250303015001784100c2e0001054038003054558141c41d00d00307401800c115150165841c020f01800002c1c001c1c030348244103c0c1c80303080300500040101d4100c100b00c1c01d4100d403165442d82c0d411590303020b0351207190f0502110311942c4100107400b542004031240f40746441440c1703088174144298445001140c12140c03600b4003140c2408140006810741c08600d142c0303070004842c136050800390207140310304121030b5160200180000d510021500624080c031004d29039004140da8841050741181c4034182c982e00944c110420810a0703d0080d0004101c0d4500b0065030148000c80c21420304495009030040310100e20b0540c2030000b4512980b00b89405800350041d001c030b20300c05c1116400d94496510074454104803580c43c40d411058424800c000101144000034044000b9603d0b0f80d007594800302c0da48400c40c1d4908000042501014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 458475737 1250 458474487 458474491
    0x30207031e061a060d0b0a0b0a0c1a070f0e0a0314072d03120e090703061503110f091804060203010e0903042304150801022d0f07050a06090b0f0609 65
    0x1380350b2490000b10940c00b002801d00d10454660051302203c1c0081e00245510003803841801036520321003a80891700d00141c4004151382d4070240241005c0801810f160444080121038525042c0003680001c21400110725000d01c0c2c00003895955080c1c005190000c00142040039030300040702c08840705a40a014490907400d0040c88900a00400004c101142c41c29020188070340040c40d01514004540012501c0c206060b22400000780e581c5500b001807403000c010415600c0c03030a00e018800788001c856030f0740850040c0f440c1000812800922814281e4409489000b40030f08058204154905070619000039042485202d8880780884005412880d0101c11282039450000e401c2c840c0003001499103010807865440160002c0e40c1b00e84018042c094024880003d003d220000b5940c0e0b0300401c0080f040034942c80e5400400c48607403291500f603007018000d031080c01c0070758103a4a80341c984909009160040f140400340203d450014880300b07210600169521a064441c00c241a80d10390344140a041c0303a007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 458476987 1250 458475737 458475739
    0xc061c06140a0914060d0c08010c0f030515130506060d1503050c06040f06030203190914162912010306060609050607020306040f030509100206090d03060e13030207031e061a 76
    0x618006041d80c03611b04400f0000501608881c120151140d80c49400c507540c10043d440030a0022084a02d0560301d03019080c0d0110205440d00c0201c114074004c10350040d201d12010103076646500000b00c0399242d01040d600c41139180e0405100500c030a00c40090400300c42d000c01e50f65801007175101c60503810b0490498003100e070400d89030906140340500031002500041e00255000f80c102404098030f114601406c9040783c00b44d6825080c03040964aa945071480e110740320b00c99004903600400001c00c0c00300184922602040c1d03001030b40700764180b070030710300b4410346200e008109484400441800802d500010640f02c1d55190707081c1c0f41e038954041200038024417000a6155214100180006203a0042d01e0b01c2544a0f040c240d04040e4030000107500c254400d00c6600041c0d004404000144000b0071a035030303c0d14400e0a0030000c1c0360428002c804060002000b400e014641c001d01d0008162082100d41c009603040102d02c2d8014039803403452010070410001c156265814404101215880c4071120304142300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 458478237 1250 458476987 458477021
    0x309030c090603080d0f0906020c010b0102010c110c0d050a0f0c0e0c16060207020a050a080c01081005030604080f0d050c03090d1404051512071e0f020c061c06140a09 73
    0x80e110502c601908030b002401021944400e0b0710000103408e030000d05506020800089880f1030140002802c541541c1904000c2000403640000200c001042500342c1c05030560b008000100b203420070520303200d8207130341c010428400c1020320b01c24031804840d41410b45030710f42801d5409803141d00c039400c000c1c002c0d1204196150008601c00b0b00040c3e166004107800c034406484010159030358030000d407402d040c0d5031040da5140c10641c800e04007903a2100c1915807114481141300c001d2801e10000c250b82e00c0005000911034a4002681d2184010210669506466601062240c1c2c50b0101a010700750300103035050381c803074400c0b0750000340d0641c004c818242110018210729410706281004000d0810035120280140b1002003001500c00014035102500c181225192180c815080c0f0480d0360400c42d4002d01d20080010140d001c01c234065000c038451031107050880e121a00c80146ca00310b0080d0042c444200c954031440c101d00007406030365411211202203400c1b42c2e01d0040f955624552000e40e240c00b010084408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 458479487 1250 458478237 458478247
    0x11e0215010f06020d121d0606131503030e0d060c0905090703021c0513050a060c0e101b0809181803040501050403021e09040804030b1005030615010311070309030c09060308 76
    0x540f04440040e040418888007090281f081c1000101000b00161040d815400510411649007426540c00c0b280c03e42c0d080c0108429188840c49000b0f1071400d0200074204032509607030004a03a2000c40801c1915041082042000502c4102a01d0031500b4451980190070752000548864080d200b55681c500c42c006515002c048c01864140c000d0500628401d40040035900c10380101310208052807066114800000e801d03c0704081c0a0404401820107034855001403448101060703000c62040c596500c1040500c0b01b01d0b8a9142c0f4101900800c0300c0c9a80102d09560341000aca111080c240c0d003e1000e00101c48210710301401199182c0c07289005850106208000400046c03d04010100218203d950007170340c449203a03400200d0780d03581902c05869890300071900f40240040a51f2040e00001d03a8081280c129150001180e1140c40040555003030080420b402010381e4082e402151448182d1660f065541d5060303d4060074041c40c9000c1541c0c003510401c004141481540706000c10740c0c0d007259000c1c1c208 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 458480737 1250 458479487 458479513
    0x40b1605180109082508012007020a05040203070e0f0102030c07030b0417030106080a06050103021908270d080109050402031f0609020d02070308070329011e0215010f0602 75
    0x8040300e040e842d04104108200080c4c5000c140072800681c071022440100e01d01202d20b40142c1c00100b9000116140d142080b010b1030444a0929030001000d903c1440351545294000078030b200c60035074000b68006000004101d0200d40c8204080715200d000c40341000201038079401244da0b809213500c4201c00d584134400c140040b400a107591503100b881001c202401904141c07a0503400d40081c0d009201007088641400402c4806018400203000207180440c01c24203414512060b50b0760380d960305070600056101081c0384c440034150f0030407040c92400d00c035584d11805c040c0e00c1d83d0340c00c9502d0035030303000032024400403900c0039445c010180a01c7c0c0040080009000c0081c0c0f800940300400c5041d600b8035134440d00002c1030046800500400b04104100613102d40c030030f04000d0b19610380104500101450a1040c15203800c00619061501d03052603865030011401d48016240d404481d041000718141210740d441000340e002a21140242c0c0d101c01400f000d076a2900988620541d40c0141c00240e00449801300700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 458481987 1250 458480737 458480767
    0x1b10170606071502040e010518070518120d0503180a080702040b0303211803030601020d03020f1c0609061208030705090414040c03050d020703200109030b0f040b1605 73
    0x31900520f110f0088000d046003001c00caa006910850002c0741850040045161025144000410b41c0902060618101070000c01900ca003846280d42e082c455001141152a0a500d00502210880490345420250f25014201d074008940e080d010000750b0800c403081030b9020527020211584031f100981803610550821028002c842185509840188541a41600b0a003100c0710003031800750020300c0a0802c075240c0c000c6404d1512807540301e940200280215030368001041c02105ca028500143c61b03034140016007005100c0d010440481204503000c5059180780f0794000c03000c44a80c40b000700036280c1d481124031171039401c0d0300000c0c24140c8180300085000e1702807001441400741c010400602420b0042082d040307088152001e03104080035035414020064104440d905031f01542c0004d001d034a01e142d07190382c0483c1101e01c20880240c1640364007080c1b41d00968a04024680c090510380d0030745810034520306c0c0440111800c1d60000034540102d1a0b840100208060340b0440e692080d252020b101001c3c48 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 458483237 1250 458481987 458481997
    0x1a0901050702030709050415060302030a020f0123130f030c0909060f11090307140d0f0c120f0302010c0c0b0103080306030f010c0507020102060f07020703150204081b10170606 77
    0x20500808000150050f03800380b0004000d000300000010707850900d4200500d507000c0b0545a001650b2511106001594000400302d0300f455044401854006903500100d4050705030030250020a400f500c0c6650030a80c00602030242c220100c5a0ba0041565170a240001295540b002501344041031000740711026054010f80317005406001c000c6610301d00ca47e9604110340d130b4104a0003001c0004940b000380307403a00380710910013048003500408440032a80d00140131040d001c1c00003407180070901c02c134004002409040c04020300b44a0fa0768004000c01d03040c2030400d6903c0c0042100103500c0e150440c030f10f41d4003440080010942015440d80b06038215940c0c4689684040e1419900d0701c40c2861245c0e199109000e05912a640c2d95640b41d155040e510001e031420038042c10300300c000c2e2141c6d001c0044031a400a1100304907a000b210130250695810440b8009108070342043d0720038083c403d110329001d03500b0030103000031130f030151040d07a40c0001c0360b0012103407803c1c9110b443c0800d803a24000315040d841c1c000c010f86 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 458484487 1250 458483237 458483239
    0x11090408030105090a0209030a0c03061d06070c15090803070f2a05010e0a210503040206030a230708190903120f1401030f0501110a0c0f03140c071e1a09 67
    0x500c0c11f4a0900000c0c42d05040440880d08961310074001d104102c400d0158580c0c0c020015105400007400d05c100c0313a19018000c0902c8100321400a8034018400a2450203800e2202c1d10000c0082403164100012140d0003110a4008140d0040d03a000d8614840c2013030b4510750691400b00000c202041614414070b60025a00362742d599221005c03aa003846052100c929024456030201405101071100d000030398596600000a00c80117000f004090380b52001206d40c45509150000340c1c030243d042107481049a841141044001244204580740e0b0300304901074000d0401c0064500380e2a120800d40c001d03141280c2000300040ca041c1501500c030282900301070705139a0940c0c1c000ca0000b1045002a4990320700b60720a0342d200440807258014040284180310301d02e003002d8551807411030780c980c0241103450344450045c000e504c82201c240c14076100d5618010011240c0b40003035918403010901595408860041c1d040c0501c01c941301d180b070703145400b004d0313002c8500d0041d070f000c00d0b07940748147c140068106035246 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 458485737 1250 458484487 458484491
    0x11010807141b03030f0403090807030b06040b040e031c0605040b1309080f0d021b070b03011413090f0201031b090e090106030c030506041115090616081611090408030105090a 76
    0x303503002c03002c1440598450781401c110003405140c2401c0040000003541e11801d410b8201708424404a4119849603a2040b026180814054621000703d801050f40154240460002264215081c180e07500400d403084580c2d4001d01020340c982040204446400b0800e9501c582e407401280c1c0d000000fa08881c103400c1c041c03036030103081004e02c038802a00c41d40110885003085500040102c0c45101000c142d69858609100500102c0d080c05031350040e510040c0100ba4a602c120700d200749456440a444c0d608012500070203004002003450044404413642c50f0490100c1e0628101004d04203903020707580320f80306107031f5a2414582e103440385035950110701038003204581d5221600800400c1c91360004000840c428002400f051500b4205031400d203c6180280b4403a08445041d10300030026202600c0c03d55800300c03460341ea01c40603000c00d4050303c500c5090061081c030010844102d00000014102e44050040083c000e54220402c2082880c02040301c00801080041c0014031890070700b105120350083d045540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 458486987 1250 458485737 458485777
    0x80a111602040b120a0b010e0106080c130b040b0c0d0e01020d0c020a050607082203050a0b0c270109060e09010e04020d14070f060c26040b0301121101080714 69
    0x704010000c1980d5a41c11170b031081401134100b01a201440c0c0c010204070101c003000e541802001000c0ca0310151400e4808000410401105080155060003c26154140c0d41d519075603240d8500c80340d003140403001c0c0203014040c490f1454a000740e010106049050b405860300740300004054030240691076060b03030070034036094020030b1545513400101b4055025801064407500c500098050030450b00755181008000342ca400c01c0007920008050030a29800000380c405079407116181d5626000b40351011640d04a01c0040500101c9140c21b0402e115400b070785c0d000f4529849060a403114103404a100d42c11000c903c0041241c0022401074542051005203824000c0d146a103491000d00044400348081c4d0f0041c078070030000c081010034020000c0c01c203418402c000c000f26450385144485d21280c00240c0c00035290a94501c1d41c101c40858025005400d829522540c5440c414904e04d810400d040394004208401c040c0158000c0900c2d0b4420f007469a50250102c4030b40c403210003182c2040113011091a68405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 458488237 1250 458486987 458486989
    0x6120213110d2a021504080304060e0307030903060605010504050f060c0c090a020301081e030a0f030b060406020c030d05030108030711040902040645020c0a050d080403080a111602040b 81
    0xd403180d0f00000148a8614081c142c08114803180e4001640c040d13600003e85e43c810101d02480c82503201da00031114640340e0340c560518070007034501c0c11120405da00000900004142e042880d100940740641c000b00705554a82006480d5407049026880c0d104010401c0d251061038404014182e070f60400701035400701130102c2c020491403030f002e5030303002c03a0540c0110040c40140410080307204900f803800c03a203603804680321240c1d64491086a160b5002c210381c0e84021007203903000350132210a988000d005203680d5596100c000b07450350640c90070f29200340240b0b04126031503440303042a00c0c16504007101540c6411000c0c4d80b10280c03d00f15040301a00f01d0346070154140566540c0c807820380100640301100c94a02d4090400d08220102004004544900700c400c0d08003e201d210548040d18401c1080142c0da908008185454050b85c110020024490301d50242c1100390701c84007840c003561290700c030101c15032548219181660803d02402120718400c0c4040b061038042d2007800070140303002030300006074840c40350 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 458489487 1250 458488237 458488241
    0xc0c290f0c0717010b221a03060112140601080d080a14010b070506061504120c0510030e28121704052401051c1b06090906120213110d 59
    0xa4000d480303240214060000c1c030030003801303800250780e003c4600b030f0030070504546da200c1c2c3c94840040c0811460350fa540400300c22040d00c0818407000100608443d415a59900710300186030820108171894240c61508044401d4002001c5050394101000b604c003081601c5011690381400030000310307205440e18045001d01c0d0824400318041d00c84410499669515810114a041d20140010b40074902030440c44042494030025034007642c210400f00c40011314542001004d084058025542c005208400c103141e9030b41560140300030701c644800703880c0d0750114181e01c61100502d4155a6400282c1d440b0b00354006510042d002c1198806800c128000d8940700c280104904403c4400712519449030148008800c1803445801107800440380c0c6070704a604280c0440c1c801601c8840c14a40d10a001201e14100100c0e0341d00b2000040c0304031010003200342d03651001010203040b4441c20301c03010b15001c0301044d65101c08244a08030b6070050014804141c0400170107004101c803540541d0340e0001802034a071054041c3c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 458490737 1250 458489487 458489489
    0xd06031209050f01080f0702150a0207111504090b06250b0a2903011803020706080601031a010f050c0d0c21090e0903040509070c0c290f0c07 62
    0x16500d8105189003454010345840d2070740d0000c5103d00c0070f444841030301d0b03a80820055070118016040d640540c48408090303142103c18405500005024810440b00d610319501814145000d8600b0a490b140c40c803090211821803403402c0c20038003600f0401480342d00100d40102ea2502c20103400345240c02078404041c011409000358608611022080e41014440200d207969084822001d04001a0041c1007030b200c40601025404188608551a100c031290303400e600880111000380c00006406446240094860307900b8040d480114100c1c0340451038951080c4191140f80d25483c0354001014200ea0041d9061402040b5070800c201d01002403d206000a00c410f00346d09010b51511035540d0307260301c1d00200c1d012102403c11504500082c905600c05c0d400756050085441d240011102c0d40c4911a1043c114450341d048260054550028044070a500c00d1400d40190300456190790b0b901d45803440704050070804541001301d2415501034103c0d00d0041030090984e045030903407180c500004064410f080a0302c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 458491987 1250 458490737 458490743
    0x8030702011508031602010e041d0a0c081209091003021203040f1203020606101e05030a050f06010e060904061d0402030d02120301140f150a11070f09110d0603 70
    0x40c0c2440281c500c404001d62400b078854034028600317005a860f0701126440c88030f0006410042450010040b986903a84403a00c1c6d00c0884010511051011900310b68840b40094100e4103001d1940001803c00004070340708240c0000100d516151400f92810422200c10240124a25800641000005036240385c9803c89040e40e24014503259450b041030740c0d0003080c1c142c1c0042e001c03075412441c4400103a8041019a40400d00b00c4d070140d0700044054085817074000d0b501c9a11424428968500301c0e03e500309000e10f10030f0107405024000756075200c2c0402174142007130b05c8260110b484415444070328a4040040c000d01c0401800000f401e44d039034031168644400c14a072440381c01340320308180410350400b408900c103003d807072740002c1c20200c0e07508101c0f103000c0c4414841c0c840e01c511507803e051420354642c50700740d4003480028100322423903080064065056005a402c1808100c4203000c00ca0404004030b9443c00711110346604c0011581340c42c90341005812200c81e43c201c1c2400030490b24001500d07d2107101c0103140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 458493237 1250 458491987 458491991
    0x20d0b10090f0b1201060807110a06140a020702130b0f0d2102032104020114121801061202040203040606081902030d031107112d04050711030706180803070201 70
    0x101d09003110112071820740250f1009542007041e14414040507503828111040361803c0000c99070703201070843c0c2880d1085000c90440c014011890207100f4070303402032955103502c001640700c1600d07154036002c03c9100300c1c60029009103d0001841403901c680e4001140681e0180030b18903241107940006016002c07040c4201c50001d0790084286000b01c441c24880d0f10012540001e6103403203c061b40a41d50700740c0501c414080c049240001900316489a440b0410182d105541640c50305d011040d05035512100705e03100781c101e06804406450000d4140280b108480101d039840030b00b41099004d000107940024001d440141c0c80d61000600c84070100542c000702c0c03101d1030419000c0320040c4101820000000b6220b4201070504e020102100d002e1803c032101c1c603900840e0369001d09401d4001c225000514148a50244100310030400541504011220b410310112410480c0740d0b6242d40996103460100381607401a81305220a02c0003a84560000100e060301c1070782121881c009544483d580e1b84211049001030b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 458494487 1250 458493237 458493239
    0x4061a03101e090e16030803070311090612062412060607030e0613150306080c060c031b030904050a02120907031104020a03020c030c010603030809010c08010306020d0b1009 76
    0x581590602500d03245030802e40d44242410100c072000900d024400d51940e5074544030911110400007020b0310a0300f01c025111003a0b8a042521141c3c10846030900803d0134801051001d00706401200da104100514060500021241407028840c00910083d0440a640100e0116004010b80d600120301c042040c5d07566125800113810500030040d015031f00982c018021140040e030040d46802b00c01301c0540c0c9060f00d035808654001c04030011755009400e91480c044d00e00d91000d0345500030609407020344c001c07030301031103000c506009503881703501302084568009000040c0101c201880003580401c801048070304008011700042c0851b98141c499002e615070024004c0c00c200b01003104d05900101200151411310700c4c64540c00600e24124009902c59640091455200380c060b9065454600450080f207448801041c1c10600038042404240c01251a20b0300250800300c05009041c2c8642c03c642e41e00c04036900e180d1307908002e9040502401e980944074006540240c075030701b180c13411071780d1a40d40344001a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 458495737 1250 458494487 458494501
    0xb15180306010f060e061e04180b030c1e040e0d0f23090102070317030105130b010c080c0a0b090604051c0c03030b12061f06091413060305030d09050115120f0204061a03 74
    0x42260200d4880709d917080160907031240d940454408000702e0241c50702203901c81c0000104078141d086540080c0c2c0545850302500c0005c00010340b40d08105c1c00360302c0d0b8610340114060243c030402c0a048410000d00804c24440c0c2c50841c462000e4400c8200c1801201c108586965405040c070766000c0c014000d00c400400100a10b1800440e0251100b01c034000801c800e409810000b05251741c1ca26015152f5100010016500001004551169500500006c0081c00c0800d100d41c0c0300c0b40180d07815140d80c0300341c1403054181c188a60078510710043c192101200f82e455640c2c203070080d111903040c031580400b9649a0401c84841407140500c2405515041b241d0382c0f0400c441456400066044101000042c001c18040061403000c2000200b9040340d0041c60004480400307405001580c0009190b0700020a0b9101c403280710740c00902c0070a00c01c03c0203201c10280ca4400348400c14a900c110010074000d5a00a008901d28070b125809060020b4000310f402c036120354135121010041c089100c04164000200194 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 458496987 1250 458495737 458495759
    0x130308090f040e100504020a0f030302011a09070903034d0c030d12020903030418050708040b070c050f190311030906040314010b15180306010f060e061e04 68
    0x1d0312804440c100424142100055528011444520b2455a564002c28199910b40410724003c1540c40315902d15240c481c64024040e003815040f9400403101d07100070212034070703204001e50301c00d030000d982c0c44035420b2070354070b046440005411980031160005100c05049103280004019400031f4074291621101c1e22075842006460002c40c80030031500b1080d0b070b2001c60b9034003189802c004422413400e4004075000080ca44c00a21401c40002d42c07511000400080c0100c04201840c0403940d901c00c10041a030310181e05a6041c101207038020840700b003010000b80001d00486800c0c003000d000e070f0200d03082c8940460b480b500c0e00d0180c2d00344101902c185004002050380c401100c0300e43d800100b010710704140e000000304000b07000d40c0c00000c00050161080c5c00a089003544520391040c00104440303118500f40c01c60703404580c403680705417086000c190b080409038100010624121070101c24014522441c101044520300601c0310011b03401141003001d0314076440707140320340c0840c0c1c00c4850b00c2a60340c034508019554 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 458498237 1250 458496987 458497009
    0x1f03110f030a0809060d02040504090323040e13030c060c08061302040806130203161d060f010c1b1a030a0b0904031b0f0f050f0f031305041113030809 66
    0x44254010301ca0b4900054004050b02c58076030b000c2e01c0c416200c041072070b20900640159045243c0091600b0040d82c24075a106003100c0d12801d55007241d06204071940045035551160740254a20f452010b00031038108948202c1c030704c80140c0203140c0300480110030380d01d10b01920b0b1014039540020390700d83c05114061615044082000b00b1111086240c64035101505481d07102c01032444050a403c040f054040d51018040d45803406100011000560344400e041c01c40740b4581c4a07a446106100e900203601410648051000e0301030584400036406400d40d1110740c601c3c6001115110a00440000180200024564102c00881c0c1304c16a40301e00c0e200341c05400b2600858480d03032185003c08144070100f900072002802040c20101c00030b54051582c01c15070207203c3c654000800803680e07850300d80705001c4045031030640e19000505884010b0201d90000d982c9000304848011140c00c0d0400801040c03415a1284070100c00c1c5070751482c20038070340505907824a0901c3d0710581c0d096000150506d10782c94180c000e58 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 458499487 1250 458498237 458498239
    0x80702131a011e0206060f0a0e010f080c0f010c0b0a0f06030b0604050a06050a090e1e03180306010605040b03060f0402030718050603070804030f140a030f050a06050d08031f03110f 79
    0xe0100700035444001d6403008046c0c0318901821058081c02119100d00010a0192050f031894411070350351071098444491880c41001340c1402a51a06200e030b180040d1030f8a010340c816516450007150b16250070001c1c400103414844a603075280c118510280c5213000b00c0000794014032420700e15180040600080d20001010201d141b854900700340816074a00b8100c03801e40f800e2078800211109107160311854104003e5551901c00c0703c2d80c02a0100380300000040114102c3d696085201071100e82c141682c0d54420300503540403420901040c041c50000501031503002000502c0388030a1006940410101c1c1e00c1075030b894000032141900038000d800d603140342400420050f902d55181d840c1c680c1009014000c064801010010800c03c1c24030310301d03c119414a080203544060300e40e102161640503004141c00040a0315035810070002036003d0481d171191808442010308031100e100c1c25682c1f4403001d035100501d1507400c01051070075525408800c84040d4060362242c4c000b04170b6038030a00100814000b80240907 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 458500737 1250 458499487 458499527
    0x90a090804061d09040c0810050603100b0301090c0f17030702030a1e051c0e03031c11040e04060614031902011d1f030b0a060c080702131a01 62
    0x54000208500d084804071030161820552030703d03051a000c10f03d8550082890350250a031010b00050042c11034070313501100ca100048403918908840080140c8008885090345900b003007048101c504025003200d03c0f4030f00c004000007880c480c99500d0154594090304030b0380c82000014070510161840708041c4603000000e100860600d40c00f5400603546141c103203001441651012110307013880164016a200b025400700540b03001040e402107512902e1501540840040c2c410400b607849820f002c812105041e084000031400003030010841d5000e0b10914a961800030402c0200290390300c0c041151900035841100301184551400008401607100c2c144010b20a0b00040c4090604411002d50404101d0707080c200000b03140304402030a810f0b03c40a0304030941103c2c5503c01c106403c1007803240700d201c0043c02d0301c0410000306003005000b080c103000d008190200b070f000b07040306010621241c0035114143c401400d10080000380b06d8410251032029480e0b100b0900d00407090f14042d03070004a0301411184480c0d107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 458501987 1250 458500737 458500751
    0x30070b0d060f140105130e2509080303040f030509060a02010c1403010b0316020c0d0b010302031504020d0303051902070b06010f030e0c040914060f0f0c0a050d05070309020301051302090a 82
    0x103d5480400001805061000000b140707000d620400c03000c60020b00c4004c0c2800d0722071800982c41075904031001005110090003c1c5001405805280741209549000c0021030a5540f9980c402d032003d080c0344401d0701030150034000f040c055a07841001b80b003110495070000c100070000000c00f600c03480104146480004041c030050200049a1064030b510103004100c0f0003103030021210580c2031a440061403508001d00d094600240503541035030310b0499200398100e450082c1c0031801c3c80e22441c02510020351081944182c04040b80c840c0e041181c100003001050080c025584d000042264400301c0103c03001c003060f0007080351541e004840c40b07030420154103051190180c06a26662181c4141034001e11840d0b545013a80b00f4070442c0601d0b070540c1513a400842d03141c0d0030940700d2049684001c07903c0b40c0072001211300290240041005941c0300c09999100c50b41440740503140c001c040c000082064041603500e54820000d41e0702405858010007502802881d484458014841c0070b00e03005001e14511402c01203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 458503237 1250 458501987 458501999
    0x9170d06080c1f1101061205060603030c1e1606030c020d090302010509060f0714010203100b0c0601170a061a030705150406030c11060c032430070b0d060f 68
    0x114610801d9400c4680e1500215980400d540f80301369035000204541c40d140d00420a9181480e003050701900540840e10140e032010304256403403160300d960603c141c10a0150990900400b401900380c80d18181c1640e031010401904802d181095030301c40d40000e521070743c6d0500303410b4043c01000c18003903036072500140c0a410b41d00080c1c003600c00d04120a016803000100c0c0040480180c080c4c580b00c50380411610140c0030b800303528a010750410354881c0c01d54540c40c10001450345283c0100c4080c0f82d626000340080307070310305482122151f580740300d90701d42401102100000124035226014a00e40c10088105201d02e1040c14180f030039000d9000705008200388101d20680e1140312090f01c2c2252a0b034600842d076034018290450303581541d503e0311500c0d0311030f00041c07080364110400603501c55a041c0c2c10250310901041903040d01580898107468204010120203002044c11080c080d00e00080c1c2c60390410540c0d04095200e29100c0349a204451895000c922403414010074000c0790005c2130300c03405901219003001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 458504487 1250 458503237 458503249
    0x7030c170601090302131410030303050601081504050a0e241503100c020726060c0f090907030e0304060315050306011805070215040609141902120109170d06080c 71
    0x100010344109031608000100d540d1607040b01200c2c1750581502c1f40c0d64108602c0721200c0d05000c0c0422008241004d000890b0380d403017043d1044c400c842e125142d16113000da16007440002e0201800040d90951961a1202004010414040001046c0c0002c007204d0f041000c13100c204100190000f0b0324040101c03035540803aa0001014060b01c055100b0005061484a43c1a4501141940f00e91100d002d41d0a00200c0c02c0355201682c5810350b400e1080e07885603901c1942080c194401c40030361024001c1300303100c4841c60707080012055510495900340040e2880200b260030707245801c9a8000380000b621382a43e01480c25820705078070000c24080d4024905035040c0741720841001c1c0180c10940d0b0550366040000c000c0d5200700142e2420441c2c0a43d0483c0030f06160900d034016000d500320646001c180f44c03084220f00070002a00c054501000300b400d040da0003c070703420400410010520f070042503403211864000300b03410403079901c00403020070501a541c001e0340d003015003a5890356001801c0f0f500b00c0c4c102d0f0b4241c1d031100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 458505737 1250 458504487 458504489
    0x30c0b010b0c0606040e152203020f06100b0a0e014406090105090705070f030e03012d090318150f05040302031e030c1203100f050f0114040b0307030c17060109 70
    0x20b48a000c0721683d40500031070500308007081c81e10412303a0100c0b0060234150045203240003031511070261002942c1c2c80315009144655441080781c1506d081202c0e400c0c5c913204208200c040541458036074000103040c00c1c210a8903154000001720240307000f03009904000718556181c09112200f80c0c8040c1c0d840d040c00002d50000052042c2c500500c1d03440001800c86200b102100c00c040c0d48514807217010345403414000c007142c5804085c40d0182d840c3c41e41036241c10031404400c003181590303d0200b032041c661804038000030b000524021010700c10004414400c00000d984d044025104032106030840d8440ea9070000e261207001d1402a0520404000074809a100840d50078229041040703940c1100032000c10440c903500ca406051503860140b4004003c99005400c015801002400064101940c940200c408044400e229240d0b0100c01042090210350065007425066944075540a040c190785144140d01d96104441030380000b40d4071500000e01039001614620003036900342644610f0710742940083d00007146 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 458506987 1250 458505737 458505763
    0x5090a0303260402091810090503300a0f06080f0309180108060103021e03010e0f1002040e01290406020c09010f06080430050405100f020712030c0b010b0c0606040e 72
    0x1003600c40c0010242c07c000c49400440e848500b00003085441c10042e0722604964242100c082000e00d00307480c400181c0c8020603101c01045030304100c5403521f60145000b44201e42c43c04c12055200c240c0042c2010040c0491124908550060741d510112541000019507441003450745000a407001803040000004805066030f42c1911a5082e180200140f8840800c0140b083c82d071541c01c28141c40100c100c0851906186103140382203500144021002c98160300940c000c00028a001900421000c0030a0a83c80c58407050211070400003a00b0a42401c0203520036081003025a10400031b2580c00d003030030844a801469012040c8000710f0412034003c10030720010304040c00ca001da00c1c0b0030b07040c040c06002d00c8580c0c0c2c1801001a421801c083d400c0a030840d040b070b22a05100c2e481181960780c45c40e000f0324a071aa5802d0ba980900141d50403c0c0562000c0e51146000781c080000e141408400207000212890181c26002c0d03485446543c46001d09180c00d00080c40a070265003001c13100340b05280c0c00503942c100680d0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 458508237 1250 458506987 458507011
    0x408100c050c030d1107060e0312221719020d02061302100309020103110406020a150e06182d100c050a050c1f091b03150c05090a030326040209 63
    0x32642402e42d8284c082c08501070300d001d00e00340300c0050200c0000005c0c00101201030b1550290398440c1050742f0b0707100564490982c0360000d51030540000f0b100e14944481c4191900d0300c1c41c2069801048401460b200000c620b0240c1d01c8100c00c0d8413400d4041180035440703070300004407940101c82d07030380802c0714070341c0803000c0c0c02c245034403038007250300716030003a080350004d885072003d03440c1ca0741d50f1074000a541d2008000e050300c17040c246400c4901540418080c0780744042c0720b00005c0425881d2000b00340500d020b00184130700c80f400b0b14a481030454074112011034509220b00301c8031080300e85aa5165092940240810760010310300342c0040107480d040002c4e114110a05d00707200b034407030b003001112506248200b980c41404216003020a100426564420700040d40244141011600106410000d142d0395000107805004003014520141707400c1c0c0c10182010304030f0b25105003480c0c440030115410908039001240801c5000060128480d014031012420001d0070318846190308141d000301d401280007914582c1940 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 458509487 1250 458508237 458508251
    0x3110a02030a2301110315090c03060609131506080a0516080907120b07030b100915030e0f33010b0c0307020d03050c061602150603070b0408100c050c030d 68
    0x3d12031000305075034000020000d200d4040721001601065000301c1d0122810340c560f001303120040c02c040701001c0c8203c6011a03050b156454240800000b0b4002103a0705902030454104030f58401d21601400440004080d0f0685005080c10406007948000a00d200c0c030aa251608015280510704000180038070241001d40e25910b60284c0c0500b020322a030440010491140c00000c104190064404c1c031400d0240d4040104144040400904400b135010180000d10802c000b407003507011940820005080900b00094520741d90f60340c590501480e0b400c0407401d9000142401443e01d554480a00c1c060780c4101e1040c4040b020100681c1c1c440c8040c065100903400c0456145080ca10400c1100c56a036001001c100d44289546070050640c1d004038401040707401140301107000803007131454640864107103401070040512800281500c904000340000e41c90703c40ca84000a1350190300300244054161900a8407150003802903040980b5000d0715a4400c00c442002031008141003c01503841440e0b505034040707419 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 458510737 1250 458509487 458509523
    0x1008040302100e0601050406050105120f06011b1101080a2003090703060213140306040c05121006080309010e030a0c05060708040b16050d020a0b0a11070506070503010303110a02030a 80
    0x11400840802d0501c0c98110542c0d96070800081c2a8101c0700c0c11102400b60b036480790b00469860003048900401c0c43d6000c00450a400003840c1e1840d0321100601d0000710560b07603a03034100403846281505540003194908070542c02e5a00160007030348103803050b1040c40b580f00300313604861800c03c0c28944140b08400c040301040d808001444000001c41d004041036442e00040703290603041a056110b6104030140d000c01d40b1041c1d00300419910302c00c5810456070300083d4980800c2c01072030544a1041e0030a8041c216002c2c0c07442c41144954009407600100039521005010005000301c860384040910960152002d01e000480300c1d04201c003a5001503843d07a458100c0742c0741040003801507070055083d0100c0819405000c0d04030748820403044e801803040f01c038a050340d0801a40c40300558003015007011190742c0003900400302500000c0740d402c01007200c1460003030a51501070800070240e4481c03000590000c010000c1c1903011900303c500120380009020a401b89900103540c2e0034040b40010848840360003800c0d22 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 458511987 1250 458510737 458510743
    0x170d050a050c09040c05130824010305030301050d030e031c090515030703090515070e042403030e3f07060c1121010501090e0d1b02040603080d05160c021008040302 72
    0x8403100d485c28074001d59183c585860302c0e07275030340d62004442840b40340340c1100850110030014100c030f400801452030b507402c1209100120061441c19003c4c007010b07846028481d1020050401e400300000d03100980389000e14401804e6030b01c545d0010b446640e40d4420701e0f000643c0b21045980000c01130074006a901c0892800505108074004861110a003401c00c1000083e000440c41d007684000711000c00c410308040000003844005200301d10180c4084110500c002170195400701c260200082c68001c0c44242c0e01011200d88510007158410002c04120489080b80030b030300b0314112042c0003c05441114208000107240e550030324800740110511403460f6a01c0d85a99851841200140c004610342c441d141138001d02810f403c0c0300303041c5803c1c038002014800701d0f004165204607422950726547c0c400c07005c3c011200740720503440303042e60302c544c0c1d802000001480c0c9100500d9008105d0b5000708035403800d04d00d01000901b0214140061000741d01503180186c0c0d4540da0124549401d00300302403181c50710b06003241707 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 458513237 1250 458511987 458511997
    0x10510030e0f01091b15080a02222603031302040b042a03060f050909120c0f0c040213030602070611130503010b0f090f13170d050a050c09040c05 64
    0x81da020301d80340d5229807441900201340107806091010b004540c0d401c07130724111220324802c403180000c602c030035050194810225560000e0302900054108904025002c0c100010f45101050002c1e0001080045a400381c1802154104940790320085005c0350103500d44030f100007005513241c001040d00d03410866a45034403e010540b4060804c02486100814400c095840d890380200b0135000d03000c0301480319201c0e005850a44502c1940000c8061415081c44a80d200181c2807080c0340c002c080d150044500b809020344944080c54004010140c1140740d440d00b8080d080c0110f40c0030ba801080400060a0004201030449500c004010ba0b18039070790512500410800f280386000070b40c0011908043d01c1180c000c00c003078400c114001c028400441c41046001d0b82012040e80d00240827000158032900d02552580d031108e2407011980f03034030ba440d40c0c0c0c3c210884e0589540d000c0d03180c0003084000810007144101d07540908200301c03c011034140b040c0118103e00507840050b2255484d80314102c0d8807441901518 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 458514487 1250 458513237 458513261
    0xe070e01111203040305030a050a0e071502030c0f0a02100905010e0d03020f1f0f0204120303020702030f03130306060504090c1418150102060c070b0403031a090f0f010b0901050301051003 82
    0x143d00c03810546402003071540280ca805141c5400c00c00402e4020a85210b40c0803c40141c100a0002038900070021030101c5803101601c0a500003486883d64814052011250300006a800b81c07103038100c50701c104403003003003c1c070701e0341d010030041010921050741c021408400b40a8100d03400c02e2280050310f41207151800c01104240b050040383e0540c1c0c060340c0382c5043c15409402c60350003405034203001102d40c0c081f030150380b0581c68141e54020054020034040c0d402010850700141c2038a170810100d000c078520b954000400c80b50100b03421041003060107000e21929002c0c02c01114140203400306602c83e400700c46218014100f03030900210502d06a0754440102d8080a400d003508442c4603d4400d154204405005000602500a401c00904404640000c41d180c2e1503002d02d11075100d40fa1618110000c00d1030760710001c507091310150b85240784e559541c0b0040c8955104244401e892131301c15040c4a00c4c1c0e070103900107244c403e011311100c1e904d81c0e00401620705440042e913100c2c0c0d00c1002d81200b1806070180c00c01034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 458515737 1250 458514487 458514523
    0x90c0408031321080706200304290705070212030d060612050601090b0409050a060302090a0c0f141e07120c0c0b1303060f0b030d020d02070e070e0111 66
    0x15290144035880c200c8119100c003c0308038018a283c0c40e08101440500b02c000f0402c241c100103800000300554414083d0240d090710000c45c0480c00c60800c80242d00a5805842000c005000b41d55121211440204628040907903c1c3c001c0c100110064000d00581c80001d114904100c0b540d40f003c5c000700f007607070521500e180060054554605025000c46503038542150840e0070000081e805500a0702c86004442c6840002443d052500300c2401c0180310103007103503200035107601000000da07840b407410500a0080d080002180710101002130403516040e40c294082c03041d9030404a94005035007041d5030742051690103840c0c5070080e40c800390080e80f05070b00c0700400c1280c22014541c0d100e03922016100140d4404d00e0302180258440410710341e28040c0a60703840d0300c0c1d041280207100203000c940024046072040e05004c2590710010700084d041005000d00e150050307011022212a0700da0412001006000c0e0380200b19040c1405c00700103061540804550f414042e095041e8040c2070710401040e4500300c403030002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 458516987 1250 458515737 458515747
    0x30604022d0a120c0504060f050d05070806030607020a022b0206030903120a0b0d0206160f06020a020d0e0307150c0602040602030307030c0e0102070302190506070809041d0705090c040803 82
    0x100d240a80c21480903440003400701ca142002100c4584030718080452252150760030304e807070b02c1d2045444100e015042c8d400c10509204080070080c007800f40902610305500c42800c10720701081410301d0311070001d0018045510004a010240c0c507040306160403840724030580d490600300c035504040c0580444100941003000001001135508000c0081c104c0d07441d03903004415580c0c43d2a00048165115440c0c00e0354018030350b107a110b005107802c2c00240381030240e440080000c015181c8440c1e025142000d400c2d01d0441d0005000307016a0390500c009005140d80e8101508040f41e0b240c0072a80d05e262a00400c40c07164910085104458080c1e014016038940c00364040d981d980c3c803280003c0d01d9070000d0320f100000c6810a07104a015a000f06641d1800c0d08040c3d000f004968919002c00c49081401140c02e0044030041c040800c030b80d111840101482d03130103406c0c240e41c0d80d00c000017408100c49140c8106001040c80601c4106a01000710301601160811618600641c4903440415200e00c141da102c000316120000d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 458518237 1250 458516987 458517067
    0x1b23040308033105060f10091b0305070504181112040f02090c0703080412120c0206040c14090c0d02090627040c0f03090f050f060117010605010503060402 68
    0x41c00ca0a40400820300c41e107040c44121141003403c0406070300070084d0300b1850009030368801000a455124050189008595a95800301c3d011900ca40c1080100804074100d100300d041d8240c0285a0025003a1529501e490714141014010f0741001130300800c0d5039111401c038107951454600341c1d99002d100d115010724a007484c0c074001d03400e0701d40154100d018202d0f240002ea25004040180c4100a2701030302c44140700d5844e540d555031105075040780c00c03060001441c82510500b01c2842442520581c6400914003401c19040c4000f0811450b44a00450094100e85601c1c0e925041c030350b1078105081c04c150340e8880700e0005243e000b034000c15480300e0300000081070280034120340440909000907144140b040c1e003000781041c0030a40d0303150780080020070706202d100c04a02e8426449203580500941c00c50b520302070130780d88140c02c02492180500e001d07405600184001c07812241c1d0390122640005c02040014503160004e0668000205054461503001c00c00c0c00c44102e1802505901c1c1d1400340040b81c1083c144e42e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 458519487 1250 458518237 458518261
    0xf09040f022805120601110a050303070203120c041202011d06160618020a15050d1d061806010501030b01120c020106081e060402060310271b2304030803 67
    0x3640c2054514100c0a08107a8034012030849a903070810310101c2d0b500e0b071780300707801945c0350b400c44102c0b49620f108105152002c1141480510b01030403080c1c1c0696036074003081d000584890308c082c003514131000b001c0108002149a04288504895081c2032000c0e00c04a02210640130b499414a82070700440002221004425a000c24448241c032919041000c0c00903020140501c14540100a4101d0401c640034403034174440a03a00d9038103269901c0d00724a0004248410b42c150340f668407064800089581405000c000e0500c07801d64440d0300000112007000104c0207040c0da818045c401c4074141582c8e80c205c2c0000c0d074800c1d444400c220110302014040c0c8200bd6000a001300494852800103014045403003600b01c00228800d0306e0386607628000c022030303204da03001c12005a0020300740c4682030007620740000d03a443c80500000031801d03544002e4041c04020282c00019030360a09081102a610f02c45035003a8a9001810340c49100b00c08605225003543c440c20003d40d0788500c0d0005040c1060200400c48044048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 458520737 1250 458519487 458519527
    0x105010c052814061902030c1605030a080c0f0d020d02070602180901120c05100215040506040c060f05030703090507171e01060302030a0311070e130b090c060f09040f02 74
    0x10f0861810b02582500e0348035202d06003a50250b800c00300b5644001004103c0b6000303123030802403e4520f00d160200d20300c048000d0049042c0221031680001c41c040c401030f5084884a9403013080124268580721820302c00c1000c92040c404104600e55000c100a860f44038254140e03045640e120340c0441d981c041c142e0720940009d8608680340d00c42e495500c0042000d54107803c1030705081c0e0f4404224402c440c1803400300100900c1c0142071804502c11101d4001846030111241ba01950244000d07203203a003031900f800f141d00482908181b00380150700c0e01181300c069000007281d42c02101450001010f5080d80b4100d400c043340d56200100c680800704844640c04408500490080003000784014428103c07000c0909031440385c8000b0b545904441c0107000880e0180742030007028030a030000d441c0758a8841d5503400c40343d072003600d0010300403210740c0a150400119100261300321500b0001001642c0742080010194402d09c0103a100012010131201e02035100c1f50003102310180740860135500c500c0000145007a58902d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 458521987 1250 458520737 458520743
    0x90812071823010e0d080f1210031103010504030507300e0103050108120403080a0504090c050909061f0f030906020f0a09090b131a030f01050601031d060105010c0528 73
    0x80e081250b550b40d80202e0309203003034200c0074000f03002c40e0b10141c03101d8410390006645603508000402c03030551959600608144107165010247c10b0342c03411030505002d20000180c4c1c0c1c0f030003685480240004250040143d6488035400408003030030038603900a050501040408900400340d0000c4041301268204004202102080e40e0412130b030780c1c2e100305042d5600040310079969a00c03c01c10050022812070001041001c0d01410038a00d82952100d100c01201c09540050300060b0010a21403500d01c1c0001c0070a412a004a400c42480400041e80e10b01c040d08151026091003c668001070301203019400c010002078121004540b1468103035506d0101d688038000d1900041c80381540803580518601ca603403800440036012594002e034900b00400100288a01e111601401e50720840040d5000c12030b0f480c02c04000000452036040c100c0014042c2d42c58003074180c0c240c4040c205100c2d68510005161411580c3c00d2814007803c2900e4113000342043d82040114183c0121070360450083d4120407a0f054403144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 458523237 1250 458521987 458522039
    0x30311150106090e0a090501050708570c01061518090f09050609071d0f07050d0f18020a05040209090a0c0e10051e090105030610020f0a03170603010908120718 70
    0x14008000c2050207048102d02000000361f0346405d40700c0f110701030170845400b500120b25030072003406e080710103503000700b0107941c053b03911014140210025000512a07040090800f00102c801c541c6299503030301c04030b00451782c2c02559140115004112604a001d10076001426205142007119103030b034980501e40070343c041600d08001008a10021544802e2088440c02990032070717a00e030030404492961240112410017515400000101340491041851100300b107487c0c81c8080005105004040e0f40395846103200314818000c0c40010b89820003400d81c082c89140e00010121603503041a80c1e543d1310081e1140e00001f0741500c0c1078903240c0180040c01c802ca000b40c00d0b0b02039489102202c0c8038910444801e10b00243c002c4c0042100c90074110105804602c070b50042c1c5a42142d080c0034103141c1511a24141d00180400e10904d040d034124050154205030250000c1c403950311180c480d2004c600c90381e00c441480f90721020000d50782e14400d05100c240e0b1000082c402c03101070398442c00340d0800c5011032001d055101d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 458524487 1250 458523237 458523271
    0xd0b0f0105011412360d02010c023412031101090c18112a0703050606090c0c0d030905011a09060415090204030311150106090e0a090501050708 63
    0x140c003d0b0300c61100710100350740240c9010112a440019420302a01c1441c0100c0702e42610003400000720201080c00f0608030305030803c2c1201c40c494901d810610f004031403d5900d405d01c6076099a6010690301303509043c85003032010000c0516440811107508004407490002d80c46000304148180058000109000e0342c0c982290010f050440c80c200c40008100815a0a1803c41080408807040c16a12601d20140c800254101c50340d4034414140d00c0507140a250250030080c413501e2803596030490049190784001440380e181143c0c0c0f45551440080c0c580392047ca010b5001510500c1190b00300d07507000780f642c4280ca070110712080029015201c08101102d055007401c10b81c002da01007510310240100c4004040c1100c6d5150b43c42400001c0c00e0101d00b40281c0c0540000206125055000510040d4403a0369a404102d9403207903003070704044103000c0d052201c91a141c01040507075802002c0c0015140e40312102081c54860b044041c0c014070746603000910a5003420204a100394108001d107204001036808280e10b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 458525737 1250 458524487 458524489
    0xa200f0a020d0822030203070606150908010e062a0403060b0a050301051501030209010306051908120f0f21041406070e0102120702013b04020301051315050d0b0f0105 73
    0x50101c41241003c40c07940c205070162241040c1c4a12503a00900550b40b5002302c81d180c00c030680d107494000340b8584007035140c1d0308102a440450303d001840030381e00070410a003110001944403070010381006070324501401d5010318014500c09001f40740e0088480d280c0da4503524540308010304600a400c5200e200610f800284604041c01510702c20ba0b44010002c41c0d800d00a40150300035000800c0841c10199650408100c544850340e103a10420300f1740d6100351510740740c41015860700560503003940122005100c4a142d603c01e0505031650b00109050054072210350840109282401007484c0031035079a404240000c2c031402182c40c0e95000e03001e500740d4480384e0f5829400c0d1050003003002c01c41d00682c40b54180b030b03d004840342e018081d414414913000000d9010140307154164800f400c1480e20119070754510310f2400c00d000034000794800d020340c1c0030350640d0b2501000401c0e884502c0000c652403525480600013040202805c40044c00f0000d20758801410f007802d081601c0d0400300c4a0403207600402c0008101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 458526987 1250 458525737 458525747
    0x30c0307080c19050607020d14190b0606070c0e19060e0402030c060a0207050402071707080c010b01080411010f1106091b0901050619020f0d030c1b0b0a200f0a020d 72
    0x40d00c5000e0000c5c1c0c9441c4840d402d01c09041c4e81500c0030341d1582c00442142041ca0307405c0c40729000030710160106181704100b0b800c00d4900780e2006043d6501c10075080080400107003a00b89600110384c007041c221032703003540c0e0704580210600e105000345000915020000c1070982c074002119010302e000741c0480700c0e00402c0c3d0041c046244150060000540e006000801841c42c0a400034a10070303208190400ca45010310700442d1071500006011184c190000c14068044142441092110402460142001d0510380c0f241410751040111032410016110403c0a545004058400040300c0d0801103d000c6e182400c2c80a40300e200808103100c01265042d4000001c0c904001101d060301c40c01845503141458403050600103000003101042540204001915101400d00403802d501c40951400304841d485084014100d148140302c0d032884841c1e034040040071503000189280d00c60b00d0102d00203503900c10300140e0507080745140900741d8100e00000320102e00d1042040500242034041c2c0843b9040c000280068036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 458528237 1250 458526987 458526989
    0x106031a0d08090f030309030106080307140d05040306090f05150610080903041707090f0f270204020c07030807051b0d1110091d060a090e031206030c0307080c19 71
    0x80800424045640f06140c4074221121694000702180e01e003022080c0468203481207a440100c0030b0300003044803028030201c4a402e091300b50344003018000e90300b480b0201402c1070003a800060896503132a8940c0b4200561074051400290300001211200c24080a820384032440440b003413030084c485441101c084a003da510139014410701406141000c0c2040c541706161003503080415943d220340c00c0001400400c0c0e20443e40680c1800b40c0100345d40c540032102d8019181d03404021840c100303526074281c101e4a1940c4250317211a50440300541e079404c035406050b282c060300c2e800c040d1030b02c940001c148082190000c1c600c0000c4410802c0800e07104c0045040101c86000724001500c2088601200540e07403800031800645a00c1270f003001007413245c40381c02804d002c0404d60300c054211103092007400282e29010a000000b440b02003001c0c009104030040558030703170003034401d080b0719411120041055540c0c24009038504a90150480c0c8070241da0340d84103a075031f084002203a80940d50321003584200880c0c1c010024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 458529487 1250 458528237 458528243
    0x61101090b04260d060518041101080a020418091b06050703030c03141303110d0912050a1a04030807020303010b0a0f031b0c1704050f1509090106031a0d 67
    0x103541c0d98030b03920380d0a0b010010442c086190b400c00003003005003201c00c82c0903100700044804001820741c00c0c9030600420070b03000c4003803c100411a074100800a207100000e441c1ca10020703e0800a40d407510042c500c00f0b400b460300f240307030001d88c1c019081c50801041d0380460042d070b02829100840480191248600b008030740135080005200700242c0010078000e8120b87c1644800d0f1800069440d1920045255031509491961056403c6504803051551108684100407415009031a4001c1c1080e000f42180d402c9102d80c101e481d031030f010000240a0117201c00154640c000703610700044112011048640b4400300da0440109080102140d0603a10000543e810790700c41c141101e2600e80c0f5400c1c00d403003200f044035100c2c040541300d0701682d03045208400b40c480c22500907203403116801030b1031810081482249209503600030b014001082140c1d1008140b20f00340d4000c0c2c6851f030f0446c01d01d04643e4681e100703403d07209400a10901c0005441ea516600c0000040d80e1504a0500c00c03100800300154010451005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 458530737 1250 458529487 458529503
    0x40612060b07110915191508060f0f030106030f11100311031527070306121a130f150b030c030a02040b03030918010f0b2d04030501020309010606110109 67
    0x540f55070070b10420440e08802c41120025440e4021000030f040341a103664803880410b2201000c0101501c00c0328840c0c01041642031803400c5281440118001889030345549101d501c03d001d0307152458401b0351110b0b028680108020070703000c8041c10000000001c07080c00764002d00c4007281040119109221b040941c2a51100c424903646880665510303101341d00300003039070003101400c07001c0038a1003008100b4010300001091840616010501504071281c50707016000c145c10403006000050340964915480b603d00e01124100c5860f20f40c3d20203060103403060003e0200d02d508400c1d0b801d205610500d410010312800b8280f05200c441c00506449141d4458084d8265004440c2c07880140350582040100f05005400c5a04141100c0005a003511104400805403c5860018403610784e40d000c10401604822884034500049004902c6c4015130510007040200421a9484040c46103175086034020740d0800025904c0b07007031005046009020512505010804542c40440d58500600809040d95085522 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 458531987 1250 458530737 458530763
    0x102191e09030b0a0b0603040609050c040b060304060e03190207140109030308040f05100c09030b0f0c030c09130e060609010f0810050a0f02030708150108150d020f0402040612060b07 80
    0x9114103003800500740d81c40d5261101c850541c0343e02e038040512312480c002d0350089138881d03203800e1060410040c0d040343c80c021800c000c01a403103074440300d0840350083d501080c0007400c4540301400508501070b0071000300c04140103641105a496000808000740c03003280d650001c841c1c0305030307005541d042040c0c032004000c030390040000740c0820700285c445101240568155050b03811043d0032001250320307170214400810742e440014810301c540c8445036940460480c4904100f400c0160400c3c51500000f0210306140c880003e903000300d030301c0c0ca0151102d0500420b038188402d506805486882d4001292414080c1007543c000040d90900380030600c0460f804200602040341d000300b484400742500500c1401c1c0301c3d86844071450310740d0b1a840110310a00f110b075210209401e1034803001240203000a40241085040424042d0000c8815650f116410b03045031211821503c07413000c5040700c5982d055855125202240c0028460f8014000c04501040a04d04002054645854400c41d0080c46d4014002880c0011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 458533237 1250 458531987 458531993
    0x9060b03010609150f23040902072607020d060b030303041a072102071e1a01090b0a061d031b01020c01020f070522020703120f0b10120e0102191e0903 66
    0x1585c42d805001401b18034203542e40c12203d01c5a40d0181d800001042e41c0081d8002c02c2c8001c6001a10b4044c0703c01c001c1e00611800f0320039450050180d144080c7c49580041007040410040d944958000e45020b42901d480e85403038104043d5034444c508814500e80d018500040c4401c0c4100b01080b10141a001942c41c0e8041e5143c01e00000c1d004040111800c00e054082082140741c2d84208400c628401c06030140c0c0c400050901104605040e400522401c0c04c0ca8048034140d560350360842d050300d8142c60240413030250303005800c1010308403030f00c400c2d01809802c2c851400c1001004c1c9814103000203808490705000504012a55a20708281c0882d698004103018805481d00250030310412017840c01c480041118010701d10100d03403204504030007103000303142c41c1c00340c004160090700b080506003081044020644008a64201441050b4008000ea81420f04c00e101034580e1120303541e600c40f90000c545030741c4011000c5010002c00f070b07003940200d44041110010b50304800c03900c42c01c0d90644c1e82e0700070342145965 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 458534487 1250 458533237 458533247
    0x30a020313121d0414041b0b1b01060b1c050a11070c090c0507080304080901020a05120a03060e041e03140a09081e1e070504050f0a05060405010602030f0c010609060b03010609150f 79
    0x41410041f500b10380400154804104050030145c1066052000c01c1021540b0090840e45264800514441d00303102c1340d444804160343c550400c0018a00120b0340d90b49607041000100042043c0750901d82022072a6028800f50500441c282e640b0f10200300005055420165100c0c021500020b080d40d004000090010307a4107800707020301c104103004599140310256203c0d41807808111034032200d0b460200b01e82d24015414040c0d41c00800d101c00d608422410180c903881000000419440c0b600c0203040300d5081050311600d140c0004507a800b01d81c5494414a2200410840c424407030b80001c2d200c1d810501545040e0f0301080b052055408000b40500c04045c40380c0c00d81c41812910100550103503110020b07040e2242e0080521a03c02207150340060314100e5150003c441c1c0140c13503140070300e1a2a005004140e00041290000402000c015480b0440c01820502509468202a0404e81008400910b01e425203000d14162461600c4510900d074032001c7e036801450640c424030700011108120500c0341c0c0d00403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 458535737 1250 458534487 458534513
    0x6020f0a080d1d03130f0317030712060b0406080f0c0a0f02100c03021b07080309041e0f06030506090609060411060714160f0b030a020313121d041404 66
    0x81e000c0843c21010380305040301021070031140b015141d0000184a0700d04041c600704180038210034840340c1801c9055441ea00c0f550303002140034840415000001c07840c0c950041c1449070410010080500c00b0135180d00400d000c1c0d401070701c40c2c0e40c08180c190001c603510a05c8080307007034800c0d6101d1030800d08100701814100c4401d0150a180c1c03003540105800202201c1660044080700c0c1d106440c0940c1d9000f031844052800a202d50070400c1c1c90b041102c2c20700c1070340fa012003243c001c0030040f50b003c075951126000000f01c0c680030360412003845240c0141d4558007000f503003000d0101c0b40181c0c1510519601c0d001c843d500d45104882802c2a0342010001500080d2030542c0201d003a03602802071800d242c070395555180354412510581c02d459100d90f1032802040c0e0211059005444e08206129209207000322140c252b000c0034100c2030081d900480060010348009548490503900050404c05200c1c56001c0a00403442040142100100748142c80b03a00303042500074003003000da41c06d459483c960b980b9182d000c0c0d00d0034a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 458536987 1250 458535737 458535757
    0xd0b0601050417011515140a020705120a030801270507210b0f0105040b0909040206071b09050c04210602090a031a0117060406020705010204050a1e06020f0a08 70
    0x200b0710010442c1e40150322a4000400404000145564505e08020960030554402c2c01505072103000d10344d1181d8094001d800010345100025146c42010400781c1c10920290041c50300545007800200340035a0000c0c0c9800c10303e0083e180e1080a0362221212220b280d010420702410910255400c2d640d1081c0f50300c800d5010204c1e144c222440b43d10f070812502d15111210405282da40c49500201692420201c910280d010074204249803e10303150590419001d510f140e107206840c2140001c081d9162142124041d95002079862200080d041203c8000c40c0503000f600c001c28607080c000351b0319902800460303013a41c49816400b0182405038034241040400300b10100e850a40078080c80c000c9071034050b5040c0c00b85100d00132100e40e80340451800310350040160710204850484000340a2010800300e405904281c000401598a0b6182e0070331070301a214940c89948c0103481d10600040203200000c110b07440450714081c01c07006c140c2d294400ca0b9100c404440c03403d515000081500b002900103801040d00e510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 458538237 1250 458536987 458536997
    0x31b07090204030f0c211103100e030309120703080c090a03050d090806090c1807170109050402011209030905042004080105090d02060705090907030213060905011d0d0b0601 76
    0x6152220300040c0d8002d0740c030485100d40b001c603000c020800c00f10001c0c4050115038080c021001d2003810654908004e40d40c0207440d42403104441d141c152800d101007401d500303014405010844038200002d0f03890b4421100811140030305000c04203c0d041d09000c8528103509035507243c40646400310400030301d602480f075060380803c81480010000b2410b105052048e0102d407129900c0501d0f1009140c20302200801c41540758016000000c0d540d5600003024000350401e0950300c1207680c0f015403d4421882000103964140100d0300002070241c51a00a148118401e07a00c02c00c00180e1404040d040e120200d00080100701d4114050201d070034141c0c42a0b4002445241d50521900d0500c40c0d0001e69001d45c0003c2d41c265180e0302003120145080054603901e07021480184264942200020311500480882ca40310310141804a14900d109406070340d45c15180b059600e1802d40d42d0349002d0142c08240c89914085000011408a8a1100725a1098060b400b030040207504c1d11b10b0f17840800080c0000e2480741401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 458539487 1250 458538237 458538239
    0x17060d201504090b1207030f020616062c0d0525060f0b0a0b03010501080c09040c0807140f0f0901050c100501091b020a02040504060615090e0c090102031b07 69
    0x150721181c810014014840031a0354440c1050035040a4440d40489180100c5424000b030010500015040c02100d8000c2445595441c030b0384001152441444150ba41e40861a400d090a10500382e12a00c015100d0800744140180d41e9158400c0008001005540c9234006084c01c00e45e0074090b1000b88101440040304541340d04207503078048094051590240c6505940d03186030400c40071030348241d060150342118850500e62521490045601c0b05001c1c079030407c03032400c0c00309548810b032609492401e040140140568a8030b00300042000e00107c5504c80055041a1903100c414462000c030741110415000b210319000c440340c1d4100c4c02e9800703d0499810880b003041442d801000a012015000f020701030003048a515042414080c0c0b45621801010f403c50149070746003070b540000d0058200c07981641e0100b0656118280b85c0018940b5500615000c90012201554158000c5006003941c03001001d054035902c6604070410305008045851340981d0080100a880701c031030303c1d00c4400006034402200c8101d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 458540737 1250 458539487 458539489
    0x140603071d0a030302150606040302150f07080c062e0303180905130c24110c03120702041d03030402090a060b04090c020f0114010b0d09081917060d20 66
    0x8102a98021307030050b00001135041c0c2421580360b41580000e0200c89050070705045800003201e03650200410b002c0c0100004a210150300904161030003940c102c844503440d00d034080348980e2120401c961003c41d4202c44224550300d9281b0b41c003514001801103200c02c01c814150360f010765098020902c012504000b2020028003a1100d0040c1489108599402d104684039440c04142c12900c94102844824101c0d040d40641a0508004e4407804203524080582c3c44181140505101e0641091901401000010b291001d10017009000052007905d0070400c2408504c1c5c80c001100001400d090790760170410104001d0b01d000420b254002448943c0003070039541d54603134041e050748151700c0020300030b49540c140101c40c1c0e0103001010071610300d040207010b140303800010505614014001c07592034900c041f0b4141c0d88441c0550105800d1580001a15912081d18040305071034241e45440c2c00004810880b51000464509022401030401a0581054169a1342e901c0514a1440103200d1038030600510079040e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 458541987 1250 458540737 458540749
    0xc011e06050a0b0a140f0c06010b130e090a060506121609050115200f060a15080a0b070c03110303070c050f030901090315060e0c0310140603071d 64
    0x18441a062002852914010a01c00ca5000c294062404500140002d010094004d60b520842041003150655200e485040000c42c038043c0ca000d00115118403c008100301e407c45000700801c0008148460320360751358441c0d05414180803280140c01d904100b0900c3c0c002022600880e8005800a020030800303010180c080f1b292002280350010303540140f4030100031100541c070030640981485200701c0009030240388080c00b80e12541c18900c00c0c070010040b020b10f0040041c0507080344150104262505400e18a00c030101520410510710f8450781390b420005260700340000c00c002519480081d00b40c0958807460b060740c500412680950074420304800700c0410840030f1000b5841203480b40c45800c8401c81d1401e19614110341000c3d108420307801008501c1d030716038012407641c0450780d07c0a080d214090f800714030f0304e0240c038480d8090400148034000380084102824041c5103e080ca0280500d40c450740c0d501c00d40352801c0e404190b681c00250400c003180461384201c40700d1181c2c16241c40141c0e9000c01c4400402c40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 458543237 1250 458541987 458542031
    0xf1d070327020907030c020a0b192a0f020d180e07051305120a06020c01020f0408071404050114090402030f030a170105060c120a11120a1b05070b0c01 66
    0x10501c54104095021468020b0030070b42c005045140400c60511b0000019680d40d004090103006140e1000c00220401d44800500441e00150003080c405200003a248101c81c070072344082c51055a520b5103694280520aa0100001d01c080743d000340840400390205490040c0c07003503107072498080608000304490803144545402411196150b558500c0d109419402040c40c81d00080d101d507000701c600b80e0003c9000500c0b4107072982c02c07101c016941c09480c00030300d0081c032508a08038130302c0e000441c00180102000c2810f4045842e0721403032510584504007008101c9009010381c80360072545000400e40c0d8108000c101d94890320103002c03108a020b4030400c0905e140c0015a920000408214901766400c1048174290700403e8140d5000c0d01b0020300700142e54885d000041140040e00c40810108005881922442741b0808407506642030314132102e904405650043e0781e180e012940101b070140c2018407404252804a4011018091140c00c0280c5251140d000b000011925900c03180a1041c2250744e20002c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 458544487 1250 458543237 458543291
    0x12080d060b2505060619050406120308010602060712111e0415050301050303161a070503040b06030610060305060a0902030c09090f150d031b0c0f0f1d0703 68
    0x154603030321003580d0442d08103060030141d1206103501c000400002d0b0001005500b26404603403e03500203803801040400880150301880d4003505045001450462080b4141c1c3e51a0003655800c00a83e00d41000743d985e4481030380c1d848005a034015004007050000d920a4180e10400e000030341c0380134469100c500d0284030006004035803910002d0100b00c2c1c0420400d000315642083d0a080b0b00719850400002d840e0b0044d400300e00782140380440013030100002d22203038503e095601d400c0c81ea46030805c0800102590001c071402c648842454000c00c40a241c0020802d20429500d081c20903030301d09120045010b05000750071140c0141194401240094080c0080c40c8107095108025032500c14034020050800c50280103255440901c0c0700b4000ca60f6407841c6998401281a51740c00c03c06070051a0403100c3c080c500344006e40d801100c282c244200010078bc04c840884030a03518842065403a200c2c801d1404106110343c12050510200c615040b680311102154807007200d0a0024000031020355159203901c03c01d031a4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 458545737 1250 458544487 458544509
    0x160816061a01030c0309031407051203090102030a05011a0702191203260f011e0b07030309020a060e131806020c030a1b200d020423060d0b0112080d06 66
    0x82801e5590510481c0d071201c1c150300d418003a0002948000c0e2010954005a080c0210009955001e209040003000b00029041c25425560301d407000060f0b0003900252424a40c46042c113000054903510048540d00c1086256020b511f49007290b420028041610540051174440302200014031212480030441c04602035203e000862200201c00150348240c0b80402c246c11540005200209071610a42d42c1560843c0c4041e00c580740301411040c0700c020079030380000d00404001480741c0406078135030045002d9610035030328051182d031100703010340300ca10540c10b0150304038000c5103580401041300c2c2c0046101a10142400c0d00440680c0c07106800d991003002c410300309900015134101001c1d41b154103060b40710034942281d4041452555003602c0c44460b4411480d01d0340801c10400c5582c1ea52603074020075158001c20030006c1050902800c41c071003506240004101007103000007429428001045024903509c00c103c090702c0da0030046c1c02c00c0004a031b003d065904500900c52442000058401e00010301000015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 458546987 1250 458545737 458545781
    0x90e0706030e0105011a0a090f0303120e0d0219020406030b01061e0203040f050909010f0e060603150603070608070c2f0301020a0e090a0f060306020c010b010516081606 74
    0x40601920890b260415050f0f15002c0100002200c00182d40040d40c441d024803540e030600c00c1001c44064015402011852480a500200301608800080700c1c0c1d030f11419080c42400b101103c8c4980301c2140b0168400503030004a184c45c45100c1103903034004014030090000520f00e48a894890024209030448004174010224aa1603240098090500c01e851031000350314003418104008030280062080c0790048201c40082084c0350000c1d00710b1690009035400070006505840d122a644910a8860a0090180c26000501e90504414284c0310f07007000340080410600e007070021518200010050340c1000902e490300000074501c80301049a1880c54090b80c140e010070407812803041241012900c0c400da01c100a111040f50b0490b4081500d840c044800c040c1c182ea901009401030038803440d0401d91141b508502100f00101a4003802071700b50114020490140c1c003c00660f4036200724003035158000c48070081003000802a400608803c0341221082041d1140caa60f06400e490303110020109040907110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 458548237 1250 458546987 458546999
    0x70501060503070807050409081c090201030b010c1716140d0815031506011818060f0b070f0201020a06020a2d05160240050c22090e07 59
    0x2240007a1208401420b0700c54903000003e85c1d0345449101c0c45c0e000d01e448001c15802d21120388150780c01840306101003071441003140512402440b030701000700d01003480c002d1101681d52240b41d1901e051030b403085c2d0804c800030303e6036994410794200d00702c50001c6a041c58a038000041c0071488030000d408400c001400d80a8824002070640e00000b4000c0c40c414042404c451032a43d4009201c2d04940f6403d40405811744a5000407126440311803404828040c580c3c2001468868600f25240940740c20300041202c161a039454441c503461610400105101c2400180c01061288003501d180034414012144101d000b5a5000182d070000c3e03c0e21000f01e01c1e1091190b24a00400c40607894644030146088070f128101039001c1e2443c0140701c1840c85c0c4540d520504000c5490fa260215400c124000b8400108506800024980d0501024144000d003241c0e001814141090041c00c1c018549038126504041c4030400b0f1901070400154050302040070b81c40000b880800510a0000003c03031400a806035030b003006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 458549487 1250 458548237 458548241
    0x7080705011103240a0e01060f110d02070b2d0d0f0e0d0e120304090203010f1413050402040b090103150b190608040212060f10150905011b0602070602070501 69
    0x70080101500341041040a0f42e861413815000340402c1c3c0e94021003800c00740002c034100e8501600f110203449075050002c01d1082d00030001c0440d20141e55204841458034141c1d01c4c0d12403941604040143e4002041800743c0380701003019140604034003407680040050420416803103c0c1c84800d0050028000074400c9903c001400348081701101141c0900c81d40759400e08883c0d40e106849481c070208505508400c8255a503802058100360307940049a4a4903280d05005000b9482803246070724006184800103100f624003480c0e581103d00042a060412280340114000b60000400480e07201d41d42b45103481d0242e0307440380c40c240a180100180e0304060140441c800c100c80813280000e20610025180011081100ca8100c0641e0007074580700c180743c0c8942c80481c4117060b03040f980a60a0140d04104844400e58503d880c0c0b1414a03035004412440d030322480d100c903070581152180c0020b01106000d0040b94020b03140341c1070b601c0b41d0104d00000350600d0b88401c012600403000482c0d00640000341201440024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 458550737 1250 458549487 458549501
    0x50a09060203030609010e0901020f0721080903072d050a200a031514011d010e0103051009110d030216050609010f1b0f0b0f09010b010c0f0c0b0708070501 68
    0x2030000b9491400d216000481c820014803c3d1880688440001400c0d04000c1d015035014020b580702981d01e034002c618100b030202001c0c02e140301159400c1c480e0480d80b1032041e2a46400b92403600e0103185041650780360111a1002400541d41131680d60f454120308004005a44121070b02801c0502880181480e007002c00c121810030a012010b22007500d43e0041d07030360310443c400312075111081d45001d4624400201c054074012115141c2224104000204c901c0300000304100044c140038035111302c0e80c07654031038084070800380005403a41d8003507480e40d882054603a000c00340306805850480761841d0f207075001400791600c0001c200c005801c54081c5034040000d40380c100018140c1107520b1130605404a0000f41050003480c00b60b000c000d2809400150752081d0b203c100102604041020752404240c1480c003241b0000799156504050041d002920544041c858010b0b840016034800078410a01e4a03842c1000703a80d41429513082c4038104001404442c0180104200b40c440c80d0001d450356400c0c1483d500b1a465 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 458551987 1250 458550737 458550749
    0x141f0507080c0c0c12010b0a180f050c19090e0702010b011b0302060c030705090621070c0b0705090301020408060f060a0f0b1c02070b09010509014b050403050a09 71
    0x42032012060f40390000c42d224a44040503036000d080401e02281c141d01420000301d060390414506880440e5080f421321001d0302d5a1034001d4240105042c6c608881c044500c22100c001039180113100300041000841c284841c84007080c47c140000300c0c0c0350700b902d0b9040401514400f0150f955065001100d50308400440f11030245e82440d240ca080c46910080d440340310080252040d0040000010400ba020328259421440017401c459103c82844c0405500040c07040551508100b154000034946446020f40005143d40b0a409040d1502e60510603209030b0442e02595506540a01c00403480f03500070081c42d8494141202000a103080c940144040d411658000f600480e001480074040b0880c00c80494044041585400340d4084481e58028001e014440000b00309240781e50034040040015000a8000c040e43d83c000c010a070700700e015118415060300200c0710511441084254190060050001e0710800d0300c0340003414600300c10100045810488017200840c801059440405a000b034005000d410b07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 458553237 1250 458551987 458552011
    0x180705030a020603041b0902040e01031515030303050c090315010e133c05010507080c07030903060e0a050a0305070b0a0b0303031315090c080d050702010507141f050708 74
    0x711900428000c0c0300050000e403501180000e4110b62000c032485c0d200042180035800c5444070744501c1072a010001c2071105503140010070510405c0c020403031182c000442d03510b40c0c0d40000d69196580c140c002e00002800c10012342c00a00c8502000e071030901200f0404594103030324400745d6060403002d04011402800c0940e040c0c054202c0d0b140046c410b4032881460818242100c840c0440e40009480510184800c004c41219104e000703100700001500084d014a040e074a800a4607903400c120006140030f07040c0e020f00001c20011040000c00c1e1664810022040b00505407a12003c544e1600c3d840e0101c1c5040490001d034001581c2010b00004444a030781000e4485414030900b00301c070000030b035240000381c48000c1040c181418072041060071020000301d46d0403036400388668001da040000b024542d5110340c0000d03000d0002d01d0340c1da2512405c1103c5407964161185820079580342c98040320320001d02818082c0d4032600d80c082588035803100441e4242c1d640000f002c05c0b00e20381408001c0284074082e2149038140c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 458554487 1250 458553237 458553253
    0x80d08070206071d1f0e1906051b010608030c010f0203012301090320120606010212070609020a09020904390207051020070608040f030e0918070503 65
    0x940c04584150030580b98542901100300c803114070784c1007120800440b0391180c0b00701320a0f50b1602402c55021600d03140c3e40c480a680c40342040520040c3d4240550140c0c0c2d00700c11410603c01c1c18011000381c03800707603461419075500b60030391320b244c500319202a003101003103034070104009400981c01d01075004591142c50081d819545012099003072040031b51403081000442020074801c50b440b84800b4002190004070200c41c04160028004505094505a5020320222480d07212504ca000421034001e0303c040c0d00a202540580b000000c20b071300207070404c0707482e641c4540080740903a07a00c840c050301812058100594415405c0c08020071030701035140c1040e00b40c2d429403080f2406600702031280c44d400c4001c0203481e60000c00d00030413418504140c00003039100260030700e2810119400f44080c0790b06100a4480e00c0020618070202e50340d00554403c0c480041c1e030100c00207000400c2000c1400c0c0c40b83c4a814901c055040310b60004041030012100b00c40100c1c002004214000c90401c580c03270041c50140c000c1c0c0351803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 458555737 1250 458554487 458554501
    0x70603060e0a020a020f070f150903050309010f090f090203060a0801051e1012050604020a0602120a0f091d060411070b0a1a1801030b0105060f160222020301080d08 72
    0x941c0005007600201c039030100c0d4080b2503900030311446c00d10214850903107000d5501c58848840700e40b900e00072001d404070001100e054440c00b400141058903040f50095080070320f0000116407401e017400c488020402442c10001d2114920750142024140c0d0304400b40c2c407840d15000303002690a481e484880242c0c10b101c00d1021380c0082c80e0b0601c8000501d040040f80340e0b6140c1000035803081d11a400600081501d51414041c040701086803400387d8802c40c0c0180310305a840100305d03a00c03464010a80844c010802c18000030500494159103501e28500303010f02c08681d1000d504034034000c3d1708010003043c1c6e0071104016075498544508408845010001811300006072a01d6400c18401000c51303a0b0030369a4003200940f00d508905009507120014030b0071880038045200c020b0001005e1104607800002040046468903107a0241c40c0b90701228140c1500748800d07100c00010103c44140d060340c0103408a060900d40800444502105409850780960380f54589980381c0d1030b01c0c010303958440811001205204403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 458556987 1250 458555737 458555759
    0x809031e012706110903070803030108060604060e1f24032904020306060c0d0507110102010b0603040b1b03090c0a0f0b2a011406101701170c130b0307060306 69
    0xb40c02e800010010f007019507142c0c06080b0707103d81600c4030750500c181000013410340701c0040154141c80c4c080c1c00383c2d6215183e0350280070a6901c580162005080c1e0240040c42650f00380031544c4400094500b01c07016240e82d44043d0b0101d440030022161080c540ba0b0b0040503a503010b004180f206c0c0e030040c0b240c070109072801048203800c40c1943d000f0ed2040b078000022984946ea140166104120204296076500400b07140c0074180e039002031421202d203540c00c0b01e102401e41c018490b019080201401c100e01c1c641c0c1c0c42c1d82e941200310004215a0149800c0003411802c1c6000d44007451013110b01c034006156101101d41000507201c180c0d0b2066283d01d8001d1802e20481800100303951038480e001c03048111149881030340301114848203425041c95031815800d01196411491124001c0f43c05458820484501c00c004803410740c1c0311407003003134420405030040007a0440d003001540c52513040700a5034140300403040000c0c1160003012003403081d1610f0f842c003060b040c607060010500401003070403300710980c07400e505070079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 458558237 1250 458556987 458557061
    0xb060108070f022107120203070b100b0405042f04081e070306020a020a0f060b0907032009010207030b04060533060d020d021209071512090809031e01 66
    0xe4041e07081c140c0040c4800555060360201640200e0000006540186c025070707a0f040910251035005490001c107032906603800e03560003a5050500e03a1842c040c00e04080c0405440b0740344d0202d00386242d011021402540c41c107100f03e20409411261030345d07203151040d0340c1d1500d02404007070b10503d9446022040c90060008012040340e40c09007000d0780711a81c0070403e9050003800311010300305688802c245401c000003548540c92305d2a04441c5802245c60300442101154448040c032003c0708100307030803850005c076000d003c1c1110f4041481200c0c1c890343c0b00e075a8401440070a480031034406031144240410403004001c8814003104401034110104250b904106c80d0b40c52603480140140d100064501041c546a0103c42c48940119425955401d18403c400061802258180418014445c012075400e80201c086842400b03031396211110910100e403c5402081c1648048404041c1040841d070240c9040c01a2108038140082400d21101000101420f440030080c5150340ca406611f00381d00c01258082020f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 458559487 1250 458558237 458558263
    0x3140f0a020d02010c0b070806130501060e0d05031905090a08120a1101060b0304050a050d080114060d090506130314040302220e030c0c150f0a08090a020405040b060108070f02 77
    0x240b40c0312850005842e2803510b9500601042c00c440100700001780c1122021740150010f880d00c144100031400b440c411980d082c000d120000e0041c4182c03d00d00d20301002d01081450041c03041d82e1030181503a401c0540c2540c11080f0384c000ca080443c0c2101c192504035000c6009005490203072a1412000400e00301c50710408000301d0034014802e08241c040d0b5025030009015020312141c0a6407030909040070307551b4204d401c0088503203104460544501900c40c1c2d034614125442040000c1030303050f05108021094000c406a28030381c6a41d120198013062041003994002c00c032a5078404840c00860400070039001010b1100a0300e040304000030001601c81c0c0100e140700303007696026043d203000c3e0740c400c62001d0a0039124181d004e100100710400d07100300c081040714028030226030780d070a140407052040980c2c1c090842548040441804003c0c4002d01404c0040d13400000441503800e090700b0781c1d0000d001c803002682e0640d6000000400c1160380e50708004165000f00321410324003400a240c580095540811038014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 458560737 1250 458559487 458559499
    0x6050a0503070e0301140906150108160203090a0902040e010e01060c0b090c0d05030d0b09010b12310201030e150703200309010209010905010c05060609060d060e0703140f0a02 77
    0x1101c07648140995110900700138024441003010311180096000d00342d501e42024083d41020a04c0c03140030300741884020700306031a960174a40c0d03404400079282e01b078150380005600040040e020035948109008010341781c82200140c0f62403c081944942c088141c0148c62b21240d034000610025402400106c6078681c8805009816a9045001c50503d290440340da80c0100e41400e00c2010060048040c180042450310104481941102002001c500070702c10f03107400060801001c140b84c08624403460380a445c61101e04c1c031040d211881d8280940c0c09510350741954a030005003200b15039160042e24000386070040240181c01588507020030051016201b40f042c1640c814503020b084203001c1c0c1040481046481c4e00c0d032285048480c80d4080e5001400c0c5070300180d003506010032298081c100310300b069600100202466510f980900c00e10105c0030f0001d542c84018a0101c40c0000c00c0c078003500e00f801184001030100b00e031440c41c126036450040710ba1041d003038100340180001031f400001c00c800b41135011601c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 458561987 1250 458560737 458560741
    0xe030706170a021b01050f0a06030c0515090312040f0902040303050d051b0d0501140303040317090f0a030501020c0601170a060203180601060816020a12051318091b06050a0503 77
    0x80c0320b00900c9602c440305040c01103100b4020310b0b0603040d0700052040480360395804141d910700e648103048070b141d0701009003083c40c150014009400c22a149000030102c020903a46441020070000386425101c0300000e8510400090502044401034403d100a00318210b05604060039582d020301240103003000c440d400340d6a030300061000070031141000d1441002c002056a600405000311004d00824005c0c1c0400d002c0f4124408914200042190704491b0061050190f00780c0c0c660502c0704d0b0f07500411059500901004070b49103242d07100c0b005000118410800117a035600303400c0c1c10310f00b0024141e2001c0030040e4500aa10000000032804281061f0302042c0140d4907954600e25076090158600041c0c00f03813040200100b400b03030700014424003403a90b9005042e106580800c00320b035190840c5c04020300f5070003200910244503004001070500000c1c24454424950b031501c40300710000074152001c9443e2600c075000d00043c494900c25149003940720702c46031243c581c14404094100d125207107000d001c1040c0040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 458563237 1250 458561987 458562001
    0x60308190f0e22060b12090a020619090302030709061806030c090902130501031446020409120e030c31020c010507031d0c1005070804080d0e03070617 66
    0x1080702c4190b03c152081200303e84443c800c02c0607030450204050350386c1000003c03603604000000c840343c00c207034000d04440c6010841c0442410490541002c4014448542e00100051b50b0600000d406025940c1001584130700d040483c000b42c0781041c7c00c01014503d000c0f0140003182810f50000709407410490f01150705105032000c5045422440a2039108515000010007004901011450454070030401c88501602451458060f2114003689140900d40060541d500070000259600ca1552980c801c044110968010505132a64078908564040008040040d0305400c112240f00303203c0d00f5002020004082ca0210b042c00d00d00c5844170381d03482142070102d203414038207080700700c01074420110554440520b201030394040d01094910750046400c2152502403c8850b5652103091300d40b03100100301446e1a0000d10802c02001c550341010848200182008a02c7e000c0003071000717101c400000e20090150440051107103101c50751840c0300b600b0480042115581c42444420030201402411079140c40e458 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 458564487 1250 458563237 458563279
    0x7020c030307060e07060807091206061203020106050103050c0408071404021608030a0b06070206090907110a03090302090711060a0c09030b090d0e0306010b1c020706060308190f0e 79
    0x42942545880002107810401040d5008000b981301c0e524201d601d20f6443d2042070383d034484216602c42c00600006400c200348040d02d4040703207900b802100006800c1d500d50b66100e00c070381420881900580c0d101c40c010402940e05209030399200b0596541e19040508208503140c0350072061155800400c0c59140e1015140d440b80c0c11113445100b004007043c082c0075240382c0a00d0316081200c8200203240703407805250a40c00d045040310980c0d540284850315055900040001480001d4100c00030442481c0c80c01440c0d5804000c120603081c003a450354410945544100a00c44100500c50802c05c0f01106070030414040c00540d1f250003c03001e44010510100004089a160040da031014011852000c10304c4400d0001041241c5803980f242c2c0c0c1c403840380d443c18040c5503880c0821701c0790b01c00c3c50030b00304182d2559040500c0c070b007080300c4032070600545044100c2c3c84407000c1d079020f0380044c0e513400b0300020401c2000101080d90300384c2c0791072401c12140d500504c1c0c178050301a100000441c1c1c040d40c0146021000c2076460 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 458565737 1250 458564487 458564503
    0xc050705091f08030403150203040c0f0f09060503030c0c12030d021207020105071812110301020a0809150f011a0d06090b010e010e10110a0f050105060414040b0a050702 74
    0x140240909140050b0112106800c550400d861202c0141d00070964002c00f00849054030f4000d90060764502c2614004030003948010b000b507811070311110010a411508001c0340000b00031a6094028a50030324802200b03d81569120910030341c0204031000035500085044115040c040703c64807081100703091800c1c11480f4044a0031440c510000d9294511860f02c582e01780280f4155000304141e9580030400d889490794010740e030740744081001c000c001c075450a180900449110b50181d84a8000c1840400e09a0700451280e0006c1751061081142c00b110821000c86201e40504002e1203a00b00041380c0b174100d0f0018020b50b4110803421583c8071034040c10321304884a0601c204800c201460b69807102c000100000ca4820b0700044496603028442e601c106480816850000c007040f0901900c0c0348141e90010401e045003415005041410011404080c0e00b208610b01034000030410703140510410048414003003a4001058102d414031011510340301c9440d6020806800020716612141d90903450a146 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 458566987 1250 458565737 458565739
    0x303040b0309100b01110a0b06030307060f05090d080c07060515090a090203070611070e0703090f03030203060a0f030503071211010c05120c030c0d020f0915130f080d0c050705 77
    0x14000700e807800081806041c0541c44041054a0461300110741820000e0480c1d4100c0c0c2c00b102c3c0f500003140c4940d004a400075001030440b45445250342e90907054070304102c1d1086002e075030340c002c120700340c842440100e80071500d92070515203524100101880c6806407001c094142555600028094401c420b1a0080305100601c41809031406402c0c10001c4c01c040a030481c080d02030400c000405078021074032544504050005486018148100d54840100003000e04080607180d5040703001180301007087c50546400f954001d640c0e0f01c1c21a040c800e0500d0550311600592903000c40c20400300d880402610180c0703070f010100c2d43c580480030100b00d4014814a084a003c1c0d40b8000702c9000035a0804000c120049001c2d130300c6030184c0e940d407800d0324040c002120001c0104c0e80812070f040c000030095000f0010711090300348880c20107811601041c1a4a10406c03480d074500000140c0300b0f840c03400c0d41c3c880310040110750100807290342051a2a529803440419402c2845080d024050800006010702405454 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 458568237 1250 458566987 458567009
    0x180209040b0a03061d010e03070b091002071a0601050913020304140f01060e130c030b18010f05071b120c21180e010f03021012060603020d0c09180209030304 69
    0x180300d0138018000e0480d000031100e01402015030b9a40e01c10b043c05514054120b0130090350812038291611101d2036002080382e03109018402a480c0c80072a507101070141540195208a03801f1440700d0021301c8028094000340c10301c08103004020142d5901d11071107040c00540000580c5a84503440c1c040c1e61010548481c0d5003900403000608442d000550040c011903005101c40d400a0300c401809501c2c144c480d48010305105d1083e00c092000c9010107440c01e40081402e08000c0004100c44902421900384414820700745841e03c0900c80801d5000850b024078581d81c2c071407000501801d81e11102b080250781088024000101641c03820311417001c0b0442c5a0066031490f000e4941d004850003009000c52442c5d10200040c059004108180d030244914180d540c1c400110107000d08613000c111052209600101c1000409200a1802d040c42c0c0100780c001c05041d1000b6071207024001000d0252a00881c1c4841041901c080070044040d07800446503c0c0004000010303558032031100841d00b180304a40010310454 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 458569487 1250 458568237 458568239
    0x70c020901091e14190b0303030615130e0103030f11061504020f04030809150a081923010906060e0105031b0403170d0605010c080306010305090715020a1b180209040b0a 74
    0x200c01070b0a84256030300805e0782c40301640611800c2c01c8650030901c20b030b0140e000340001026420480030f444991019407829904004144e01e01703803011080e0740c000c10500c590820040007016000609200394007214106421041d4012050b240d0726031005102080c20785204a05003015200c90341190540c3e144042c0d0207980e140c481c18200e8655100001090041c90708124800d04080d00f042911001c500941c2c54505e603460f0705a006040c034001c1d00c0040703100d6644902900b0200300b100301c10142445c01d04a491490361500c08100c4c2100d119500c50400c2c4080e240342440103a034418200d0380e01000c00300120380028020400d00e12140a030b034100500360721480048440150404000d4048902e00c0017061003802d4846004540325188400010034541040c03010485940c02900070b6070b4007410f074a049030380f15a81d43d000300700e0a00300740002a002d0382241d0702075030038001800340b000c48030350b08041d01552152408449140f01500900007030351150340400c18520301e69131070704428040038004009450203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 458570737 1250 458569487 458569511
    0x913030e040c050d0f02220302010804030302091302030a1d07050a031506090e0f07210201030b15041205010506040501060903080703032a020d0806012c030a0303050708070c020901091e 81
    0x2e5100d020100e65008800480780001f05000f141c91095941c103030340303810094036039550035806500464042584250306440300d01c0403030703035030310140d40304503901c1c1c0300070400b0820b100c1502c000050f0404500b02c41e4010400600860703c403840e01d002201d41c003641828000b8000c0c0000320090207141c100c0ca10180c206109c00c00030000002d01810342416400c1500e0350315564003801418407c03815103010550300340014920166000b0f43c00959880000b6103486400c000080342c569040c2e00036001a000d241e00c80c843c11040c001c0c02d1007100c3c0d00041c240d800304403550501401900c180301c2840300402640001400c501014802d400c091048460305c4841e00310740e0040301c1700400040c840c0c0b00714001440307484d1201030600d01c2072154034025003041e104c034071201c000020441d9411400500881852180c0088030a45440412017040c00a000b90f800291a080010004111a02c0a80a002005525110030002d0395455007850304403003140c0300024401c14a503819841140d20402c525905a2030b0134450780329 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 458571987 1250 458570737 458570741
    0x50f0409020307180e070f0e010801360b09010501060314040c050d0305041d07031b14090a1a030a0b09010317070f02030d030609050903070f0b15120c0913030e040c050d0f 75
    0x2313580d80c500c20a0b581c3d0381c071340c81c4250032242100b0499201d18559051090000c40206c801010702d528083c0580c185400c640328210741120550308a07105030f5483d8010001158103110324081c00d1001c1e008580a030401d07450303641c030325040e0b80141440f803070458801c4401c0501800445004003030ba10084030a00d040084001030001048803101c2c0400d0800b5000003c21442d1402040c0341134003500d8400303c50610032105003040e0008000150446008400481c4c4072280c0240100f10341c03040c03a10540e4078541140c1403000d036144035070001d004001c1140140001458042e00003a00d81940c190340352110681d09004000b151152000794050003407a41d18000c82d42d0607041841038850865003800700791074449000d0756034030500c44050660000c080f034040c0050303611000c454000c4400306041e0580d0080708001101e240000301c52408550140c0c81c0751500741013500700300c5c1d400100c0402ca0440704146403806410414403120803441550784480b0601c0580c000d000b0384003400f47c082c0c0d003001065080c00103040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 458573237 1250 458571987 458571989
    0x15081c0314131101050304410303040c0806100b0c0106051503091c200f010e0a030305060402091c2303121303020d140d0f0204050f0409020307180e070f 67
    0x8082c03c840036001c9040d405801100e004552040d55240281e090b015454800140a84003c0800002040c08441d000700c180307a03c1058402000030b1a0340342050f107000d20603a0410392040d055508958200150300c0c280c042c06004070307980c0240296445407012803440c014805c58202c0d0754420007840c141e008a508580203188076072040030890f00c940f041c0443c0030210308005c81388000014249080f02e00c40111501c01c0520075003030030003111503030241d66801c07030b00b5101403101c02450b0b54003000f04030092541c180242c9412590a603000c41c504916600400c10415880c0301034079080c030380ba00c1000c007000040d180341091041421030401d062500400e070f5075220f52150030300c0b080746a40000892034811a90059040341541900104100055100c00380d41201216a0b02100d2000c140000c40c4640503034003a004800e002402c0059449041c00200009800c0c03c400e5240950328280c1801d0060b03d00041000c1501c442c0300212940c41c90040070b940150480c809984501e020390740d0002a802044a6100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 458574487 1250 458573237 458573243
    0x30c1909031a010e060418050f0f100b09060f0303070b040c15020714450106030e070512010b062d0f0a080709081c0315081c031413 58
    0x2030750745402410b030054140303001e004861602c568600460014505503100702c91910220b208201400340503140d4600b400f52210698455070000203039142415000d11007030f000340e00700c0001080601a0100850f042100013010b8502524182901d18400ea07802c20690308440d91102400103140f805241a600c42a0148a05212200c400d81c0941883d0b0000c200072060718100c04081c0c1034902000100708002d06400e111043c07410b80e1101c2204075000002c40d04800115000d124060040f10030041070f05010140e00140415203000322100940ca17010914004559080355154003803d440200c581c0100007020180d80d200d0400602c1034403040b010050441c07011900c98078107500f8564624000321500c199074020105800801c060f1107a21301455805801200914040d000e203515459810f262044030301161202c4022102c03006001a407501034202100700b50440d89468a242103250396503803d8003801004424840349025940c644079a029003e005108540207402e400c03e80301c0da02d50100208425 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 458575737 1250 458574487 458574503
    0x190b0703290a050406030215030411060a020c0108060f030d0c03020c060a0e040c02010c0c0807050102091e040e03090109030b15030304060804050c18010e090f0706090e010807030b0705030c190903 86
    0x40d1031a00b1700c6035008494000e0080090101410b00303113041340c2e00090044420401210515500e40c88090240021a10a40007001400061400900042e5005118034805e21412801003016100801e10341e00320180c605059454603254a400d13820006841c20355038004102144440b495907010641d0340c442d01c0203807001c012410002500320700740c4d481e01c4031200100358035007091000106884024103030140541c00040c108244400002c203142c030440a0946403807004000c90070700e840c00d4400c140280301000c0045140c101c203040080c000c1c10803444003030070035051240003410101c006d403120b043c52000202030b80d0766a80c440c400901594030035203090700c15225180c001c0c0401d003007400030f550303021007074101c86259a80780206082c134840004000c81441d0266508004400400f0021a400392460391070f1504110700b4250001c1882e48140e00c00c1241d94032890003000810ba01c0044241c0100091810555030794510080012511501803024415040c040e51400480d502140351001c1d00c2c0328401c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 458576987 1250 458575737 458575739
    0x304020a231f05030c0d09020303040b1903090b060f010e0d030816020a0c090513061a0f010516030e1801090b01030c0518040f09021309030f02190b0703290a 69
    0x102141582e15190410041041080800c00b506912005001510303590303c0c01103846501980882d04642241d4822404908046050008280195207506030000c507032404001086940e00d80d14045100036141c64024695400b122900382d20490354103e080c40054002000d0544500d001001c2c96000c580c5004240c1360148500c2650748046040c3c041247c101450414580c1440d000c80700410000d0030754001d0213015408000054081c0c001c091680300c100c4003d415075403510080c00712401000ca5450b04101003004030b91803500102c80d00218054251a0590803000d400000c03403102d501110607850960000400054900b4040c0c0000d44080303000c0e81d0500000e080c1c120155045d024070150100c1184801c156442d00e42099030002c004001e100d071000c19049466008103040c04107503c2c820a9650320346582109250b08986624447e101c1c9200810b41041d1080345418440c40d07041004100010010100340010b200390841808102c00c43d2411400c0008a0340d069070710074460a02030700030450703610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 458578237 1250 458576987 458577019
    0x13091a1f030b190b030c0c0f0706020f030a1704081b0c040b0d05210d02160506010b040b07111f03152304020d060b0f071e11060304020a23 61
    0x1083c07208207115501c2200701e0900744080d01006400080c072141c025802440345180e02e540820605850307910500142c40c40310706010f8000c5c01c02011907041e8590394420801c41c040340d9071052482c04c82d04048104109551510310302a442840b03508020428840c200d0a020100c450100b452000bc50701202d0400482e04000148002d03c4001340c00038109070003c44900b0250000500c0c0030240f4000030408034030704514008402c00b260084550038900f00241c03003138241049410455180503200c044441402e103860074100b05440d10911000070901203041c840c1c1c0300147c540403696145541c00380c641c200480035240c030040080240840c103940000b411200090031500e48000d80c64241010001c10703021b101c0400510019600c00d03104659456900d41d4000340d0000041c01801c0d0b07080c00080c589075103c219080c0241500d20080704c00c07a041507050300c40c600007010020300201e040d074144c684a4482c1d840b4000102020500e034005804000524907514006540104288480c0300849a420b07910480d04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 458579487 1250 458578237 458578249
    0xd03060b030402120a0813030501060b160212010b1e030c0907020d180b0307020c0310140115121506021504021c0203070807081b0613091a1f030b 64
    0x22040e2220312008201040140c20045240c8a9240700b00003103407800b06083c1c0d5030b07408540c8001081000424251020700811000707008140040c082c40c4882810901500c6c4842001108140700038810300140c022502c0c0760000703401405418070020550054204420031071010044816502c0d4401d014025040c1098909000000d014100700d500514182642100c10b513a4050109407005141c0c03520080016034000d4a0000e44c420060b0381c0c0070f008611040300a040c6003411004000e1596800d00c8090b8201d8460045820f0444000b041da440b8000713413403807042d902d0001d19020000c0301c070b052a11101480c1181981201105c8881d4229010051031070826403c484003900c00079485401c1e0034049003840807141a104003d40010252071030641d650080b01e143c03040c168000d00c525080f42104030108004030b44400c1804005846952804010404048410815024038400c95944522100b81e40b400b05480c0c80380040d02514204070010041d01380814030500c00d1011001034180b00303000116003844 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 458580737 1250 458579487 458579489
    0x20d09060b190b03070504050301050a0b0102060106080c0f0a0309020d050f07060c0b0604050c0f0406030b0a052704030e0411040915050d15151e0602160302011103070c0f080d0306 79
    0x1a80c2d85019420040c2c1c80401d41e01c040c08030300400005202c0400c0c60340e002e1041500800d101040060f02002100004e41450416400701e42400868010000b1418029003102c111104504403a941d65402c4c0100350014182c00384082d400c032a645a0100400000090951403400c0fa00c0403142110f0340c40200305c4410164070380082c08641c207000401c19500b8560801500900200e04e03d905101c645401040b264216500440c006a280c0c0c6030040c0600b800503002c00a08010344450040b10290b207450441c940c0900c000707003600c9800f40300003001d0603c01c442003400300800134014092103c200c02d0203003081c1c0240c041d035a407480c50b00c1c14601c08003032840380d2081222009064081d2480311500e6a10000d840d240d00b40c0c2a441d01d90310804802d0840307982c0303a005808600254408408040d60521005038990808003d40d805a40c01244880811b0100011680c5c246440d001141440f21101c1c214013440c0d0f002004001420790229811119428240954019a0464400d4082804118141c13541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 458581987 1250 458580737 458580769
    0x51c02190204020f1201062a0b1005041b0e040c0206010e07050c060c0406080f040519060204090e03031801090201090612090c06050c160b0d0c0909020d09060b 70
    0xc40c5518110120010410600c21400200010308021061a10300080c0c1e1100112401c4616040300500205411591220380b0940d074000072005c1441488131b031400e607446414040c00000c140b10004540c54903202079240580800b44c000d22084003102010220b07841ca0032410404240521409016410a8851f04e0380305c1c0d2103039009020fa6441e2191b00c2e07519040103005042005410020010121410050a400380130101812a511807401d0001411982e019029221800e00d08092001280c400201101c0030400480704050350344091038500002e203e1796000a5401e400c01440a48222012029505c03c1c05c020341103c2c025806049124225040340000a0100b140414180101482003100d10403040822000003664504c030303151404200500c2c2d000200207900001c607080100410f101209001024408505d0310605240c10181207000341d00d0311204041d51004c081c8407162003081101c000342080380c4110343c0e407164055a02c020f4140301500b915680d0420460380550b041c00702145c10107983c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 458583237 1250 458581987 458581993
    0x81b0303070f171b040906080615010507020307060305090c030105150102060903030118050705090405130c140102060103140106030c03030e2b060c0306180b03010f0204030203191e0807051c02 84
    0x95148a440200400c246091300394410600c4049590f0785244208009040c00a0050981c4e1401c07244400d16030152034601c50400c0b8042c01000700680340041c5c07003001e6840c14140480e0540c2c0700c1400914142210900c668076608210a101006000082d4042501001e81c2501c40c603136032b8000c400399284028820109803040e01c400c80040288958003031500100146000c615101800c000201949c401b0f8649514941c0030801020030446074080250003442a00c3c1d40412015061001039100d100c14800909003401078194140c07428020344c0400c002c1c2d0f40c4440307040c11241c2c4905000300a1140b40760f80d07a010b80320b440702c0c820312483c2c50054918092138443d25000034888a6a440006d4141841c0001c20306854040111301d1507048101c00c0e0141e041c0d0f18000580d840c24108050a407403048980c15a4940304104c00d1015840104400b14110800e031183c0ca02c098162500e1508074403078020214591a8040c130700c00400103010b00501d4030900070002c660401c0028001404100321000101004d80c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 458584487 1250 458583237 458583241
    0x14100c03050d09020a0b310f06050d0f0e1005070903020901050d0203120a120f020a05040b07140601030308040213270303020409150807060c080d09081b0303070f17 72
    0x800641000b05040e1010700013078481a0b40c1c3c110500c041d0000d100303492800800100410f030445524130403411f108110030302442140d240140240c2000c0390b43c000c81040140010300f0780a135079599003089036a0320780a60200103d1509a001544076401d41e0720b004039031801d04012480a80c452950039098a8000300340404507464542080403080017840100c2c6c060040507152070340404044050011800d80f601c94100000172030304401c0450340c1c1160408030280c814044074034050341c000300765001e40300c08a8000d661221981040ca09080f101d08080e111441504008010141e01000b001c0c010b61081c0c484503601140413090310f055030050032440510b102801c25080700d003003c6102c265035803806400c0051501d502ca42100c0103655800c40440c0707010300348020811602004100d00c5000304407616289105000310394072401c0c140304643e0444030894640030400180500042280d98084a03401c000160304440807495480360012250030000c01c1c051190f080841d8098461101103244842c0c5500c819 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 458585737 1250 458584487 458584507
    0x120e0d0302070203100c110d020624030a060c0c0c0e06100f12060305061e09060601200d030603150b0105030a02070f140703261b1614100c0305 63
    0xa4200c0ba40981e454030a07854031204030992441040264140f540d03a03121284030301800140342801d80000c43c02194050010451078810030881d0400401045603500c403000e454500017454203100e803034094581440c000c0c802d240b154001d507080f1455407081d800c0100032582ca040048880300e048812503081141c0b41d10307186140344111400c4030134012034145907000351000e00300f03034040703606a402c1200c0960250307080c00300d1000e002d003005032142200e0703e0300055494090070958036180058042ca0521108210031202241e50b020b64038040502c0b00d00300c90400f030301c03041d004010303000d140320a940410310166002d07140c44030381c040d41c5498503060b16900d284d500d0b0140103000035409507000380c07603010120a4060000340075140807000341c2e103440b0084c00d40ca400c600b0070105104040200b100340300030786000032104c080e20f41d0507580541d558901151a80c900a050769080502800d8442080da140507000310b183c07110701400d03625100060310310300c1c2250324807a002d480490a510014020034030601c002c0e000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 458586987 1250 458585737 458585741
    0x120903033f150a03051f09080a080403030b0609011d040905011b030e1903120f02030901022d03160225060201050f0c03190b06040b0307120e0d03 64
    0x501080e05075040180e0340c0100c448800d0411240900020a4800140103585107003a81500507040200c912080641c07030f60740c4203592962001c007101d60403807100d802d00110203a1070348041c80c02d80e003003188a696107051403c010110b001c1141c04401280c5050b00990303c40c1480c40550310201e906840c2d2a041462641c10f01318808002c02056034040c1e15046400c0c00620b0a0182d142c1140703000c001c40c01d50340c40d034840c0030302500d0010446030125809420071200e401000081051095003500340540c0070b05808c1e0703110000c1c4c030307002d03100850180c00002845030702c0300c0540c002c0000f00c22003480b0800d00002120350624201001d44105c88001d8140b004c43c019201d0030103040d403050349a0040701c8080848541c240981c42c00a440610390007140c00041001680a01900782e00c40c43e0307410840018905910070100702c0c0000f80201e000c80f14840c000c511101d2040e44000100ac000505490701c465440402e001c1c940c1c4100c4851000600700103111401e8072160103401e2040f1810b2015010000c0c1480c0c040700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 458588237 1250 458586987 458587027
    0x908030405041d010e030405130902010903020f0402130b03062106011a0c060403030f0509030702031b01141b070510140702150304051b0105070b0115090305061812090303 75
    0x34403a103c280100b00c500500b4410040c011128402940e00c3e1031a000400514215588100000c50b00744110240141c0c0d201302c07103006030ba5048130080c03070b50b03004040031078000d004e185030f01103610400c4080030550b40924000340d8407038030381111204072a85082000e02d25007112004a420240d012074014000f105606820202a40c0008000c0d8240070f01151103503d03000c0203407416404250b6542001178005090f000d03440d0700c501d0324030095103130103825404a40c2c2d46195044180101d480000c81c64007a0380720300d03201d014001c840b4000d0358941c141e0194040c1a02c440201c4043c1c13070720860b040043d080c02c0048c0d07440c40703284c599207800d451601000e003094001c0d032040000b00d9100d202030b104d4003600048900032b107001d240904014130762072500100070040c40042c4441c079414402e042c000040043c06800920b03055445581117640c205078043d1050308c0e0310089400040042c0102000c0185008802d01d040725003491100403540201010302b10300125110f0a500560140c208010b205290902541000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 458589487 1250 458588237 458588261
    0x6030a1a041403040b030601030b040b0d0212100c12061d0c030c09040501060210050c0313110a0914070e01050a120203250e04050606041202090408090604030605070807090803040504 80
    0x2d210300540a03062030031580150413680c2e40b00404018000c59591602c40c0c1000c0440070740d42040508021400030ba4888d6a000000303104283c00e0950140c2403c05100102c20888074010034820074810300405440302c0710b2951403260041c9000030001e0701140301d896600940c40604191402c58403004c80009071940004c4c04902c2c1c654003000b04804585540c850b80e0f000305802d5001c0c20341041c1d40388024050701c0002c1d01c100d402ca51700f441480400320218280c03019095104441c108600c030440013050a00b81c0907803042c0d4001d850610a104041c002000761031003203219581d4001075040400c01581e041c0a02c80c401c00005201002a280c0580c25038001c58000c0100403992001148040b480d02d40381340c0e072036010000100700e10150381081c101806120b8100d40200c071080e082c0f80c1044031300301905208110182c80703000410085414007208204507a2501c0c1c1c040e011a5407291a8240a00038110170340711040014042000501c44900c0b4441c9070702501c06d80e1018600c0d191800003080050084c01c1610 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 458590737 1250 458589487 458589503
    0xf030204150c03020d14090d0309050301050c2d0d0905012c01150b09010e06040b030408090a0e060a031209120515100609030314070b0f010e06030a1a04 67
    0x31481c41851494180c1c004407940d204441003505140007030510740c43d02c0c3c040090140f02200f54584240c00800d480b40000c0580701100000504c0c101180c9034401c5a00450b015440e1030207210f14150f507100100317001a9119100e100e408c1c0b00110440c4005107132800c00a111900340402003031102207070080100e0a00450004c11703240782c107803940b0f039035010000c882d881084503104039028a40c90a00a01c1e45914001702c080711200c1c54018940034910031880c0003410000c4c0b1001c055110341c8c9400c2900e0142c0718040c9641c0c0c49160500d42240940c2c80402e125126004041000540c00725444007180701d00405800000b813545556100203214a200a045c0d09210b001d03036020840c0d14801030300703000c201c0c01180208844030701c40084520200000e0103100210406072010b00085070403100b04001c0780e5161503d41c1281a0403451041d142c06441c1c0020a241d40400a2000166101240760b0584032045105802030311444200b55461501c0344c2c000f400c0540c807640810044241065055001d4095458 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 458591987 1250 458590737 458590739
    0x40302180c2d0309010507090f030302030304080f1306020a05211b120c0105040b0106080403020a030e010e06070503030a050f330306091609060b0414041401060905040b0609100f030204 81
    0x942c0040c0c000301c0d030f5503446039900c800304000c0650008a4070000d1074041804640c41d030450310002c0d140c1c071009102411071a00042c0364032280740100102c0d45400c40140038420740301e4072040002e44400c9850015503da2152808032400301101281c00500c80548a081528081c01c00c4928254031180c4001c00345280103c20b0149408400000202610b40c121030000945c3e2a1500c0d101e07090386010b800640c1040400000c00000030380000f400741e400341e094280403480021400049031101684403a464002d500800c15104001d030002c041c6004200131842800385644949801078201700865811580c1c9010405c000c0c490300d50008240d0b540354070102050464105200031915015040c2c5804005a210a113011702d0004000245070150440d070b0428071601d481d1001006560107580540100c188034080c002d60141d980b940a05411071248020014542e9241c0019040c54210700c140790185080100d40722481c5021801c60b407071307100000e18111042201081c101d0301a17003280d003088181542084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 458593237 1250 458591987 458592067
    0x6060801090c18062c01020307080d06030206040608010305011406010519020c0909030a0f020a2013050406022205060d09020d05030706021b24060a1a040302180c 71
    0x203c0601404240e00c5060f0320030f940030700e89014a29030030001c000c0c4600c40710709030000baa8044100d64645400025150f15965207100c480020b1070301c2c3d070000350f102400180005d02e050304001c2883c1201e02680003008003450540a081581d20111992070002d84100410300c9609000310200b050b490403403044601085407440891580305041da498000382d8408160141c240b94442c1c84482108054406031910070041d40da22000500c820340840038001808104480940301c0d549152040386080c103050000d4281402c0450081d448243c6103a02c5043c47d161000ca50920450f80d00308561002c0e000380d2401d48541c1d00c1100602c404c11080343d002d042c020b032000206e0001c0015001d828003079840181d580000061400d94040264074134a807071340025152818103100038440c9040c0103625400c0314055500c0200041c8500e0307981d08030319107811440f200342c403070045e0079030140017540c0c426520090b1003000c482c80501c0e490011508250119403c00c82d4180b40e100a80c41d4004900c0025031105409040324 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 458594487 1250 458593237 458593277
    0xa200303040f03050f0d3002030403080a0c0e0108160c08070503040f091418012309160e150301020403120c0c0e09030f1602090403020d030f06060801090c 68
    0x19004200880b6520028001e002040c08100c20300704d40741c0c00901e01901980000b400b00c1c5026110308510414202815003c5101941d900581e01e001c0c040071582c07440e0600e8003502c3d040056900d44841d40c030303150401d10700c0c9018141598010f40140c40e030055139a1541294600c422544807500f0030844540345070000183e02c94050005184980c018585890400361220030744c40d00d81e070010000364144142c1390003400310141100e40024181704050b2140130308850b814090003200384ca00c40802e00d601003010800da21001800d0145031800e0640b00488801039000039462000e000b070031800300b40c0102080c40d900c000c0d250600c1d0008042c0000d4101941d170b4841c103e9003041e1020000c041240c2c0303801e5100f0400204402c0000d46414000c180050401c0104684e0b64081c0c00c40000942c4000030b44400108490b0103101c0c20a6401000042d41d0314292600a490340198204440806c0c00d10300c5482d0030f0346071401b40c00190b4078a13540d01c4a00380c0c60040b8a00107450041c00340024064020080c0701212046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 458595737 1250 458594487 458594489
    0xf12090c10020706080a05132a08010f0605030c01020d23030a0b011101090b060d0c0f030309081006080c09180607030b19050607020d152c0f0a20030304 67
    0x10782c01070441c0c24074090010709074500007420010540d03d0300c010010b240d1810400160360581050f600841e00da0780c1d401c881c0041e0349040907900f0748032400b9000240500c0541148212501082c028000184d59009141c0d51b0f6020303095890158001c030110603c2140b080160a00300100103049070380001859000440580c01564804119a1540d0b104201035030001c0780000c44030080002000101f90f2030b1202d84900300f02602c141d04c41e604051510092000c07180000c00039241001140d20b4156807894081e00106442c810744406000b540481030600c0018070496044502190240c807800a521082041141008249a00e0484901d2003090030810800c01c83d84103400503200003515140517010005281c41101c1a04850003403004248010346a10341030301c400c1030b8103441016440115141074018031811188030300042d07150154170000c3c49a10503131980f00da0828020103800700c2c0140110368603480801400d007500d910400190000030034150204a01d4405104c000704c0f83c940280000e8115446 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 458596987 1250 458595737 458595769
    0xa090c1413060908030903070317210f0711030a05090402070f1113020a140904060b0304050c1504030f110f0d0507031b2102010507060f0f0e01020f12090c 68
    0xa81c44041c4540c540000c2d40001400e203e00085040451013800a41e0369132260000074034081008080300e85001c442001c1c5c4104440b080c4c01c000d55082e01c18a024545041102c0d190840d00d03000d80442ca141d8000da5400e8041500d0b04043c41c40e2001680b0141ca03d6804100c07041d4006508114a10119400d44014481284240080722908000324101710f43c216800c081108003510400c004010550440322074100f02107100c903455101c9449200040041600d50720080190a0000401c41040303404103500404038000c60f43c682c640c800038698488540103500000741000321324952540402c0d094400d80c0030000c4000d00241c0c2c08082da50100d488011181401c840c0307940141400d01c1041030b04070195031184100c200d61403000385869010039061408450b0521918190040d580035a442182102c040310340100c0b080c0105080000c04100070000900c1d202a440c2c900f0800c0801044103000700d850006085a15605040059400400852026140103041c0c031071f10381030203003507110516045200c041c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 458598237 1250 458596987 458597017
    0x306050a090201081807090b3007060302040317070c150e011403060d0321060b03070f0c0503040b16050709050f01170d0c15052409060a090c14 63
    0x140d00c005004888085c5c000d480320559450f5032441070000062440c2110f111754004108121490045480c01855460100141420000e0740c40c8485c03500d180c606041088d2030807143c40c66554882141240140d000050020f0030103170303000c021400440090b0503150f000d40008114141c2d5401e03c5064105540d407403502081c2040c24006241d0b03001115500b04041c4007001500d180b0341a00001d07400062010b00805004c3e100001000c2c1728400040d003101d0001070242041110b84402d1002c1c981d400071500040090894140809d4941c071030080804c195030301500a500742410102002c519801c0351108a020103803155403000842c004100d070a000f800460400256814220100004031805800804d1581c4a120017000c0300400000c00e02040c000514011511150500d0503840e01c20362440f266800070b01740024000000c11421076001c8980c004202e40c940b19440c1c100780604010200c1d00e2981c0030484080c00c03c00e507611740d00710088000c5685011102c0c40314501c401c1015400c03900d071079a02c1a0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 458599487 1250 458598237 458598251
    0x12110d030606030606091d0c0d0507020604020f060a09051e13050a0b0a080304090b1c030e190e04061d070612140610120b03121c06050a03110a0306050a 67
    0x3e80504c1110090300c07052411a244138180021501503030407680e4020011410301e00000c080c0581041a81c4000c0140c0506000740d09049400a659440a440982c85544071802d80003441c500441103c510840c1503c85084444c0f0b054200091300d02c0800c5220303625090540030450661b41c880184c446000c0c48440001e65080c8416854101e03041c0c50442e034096a400d945c20301c0444000007c0d42d04844a004c03011078080881e001144030310260305202e80e504103d04642c07404045d007004809000010642e1103541c410b504c032080f0380140c1618424950f801c8002c8000c01c0104041303070048500c0c0c203c2500c1d40180c41c1e00000c10306142040650000c0e00140e0840400c00340042a8050f94446081d40c001c6944241004000940510003011009041c001c0d980080e000707102490f0415010000c2c020240d440c40e000440b41d1040c0350780a41400b0030340145540244801804030320400041d07d00113071404183c1c508640d10302e0382031500f42403100c0e803080100c0030000014a4034051a07214209815002c030340ea0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 458600737 1250 458599487 458599499
    0x7140714120906030f060d0b0109021b03190c02061b0601081510120f050303011409011e061110150302010e22021602060f070201020f0a020d12110d0306 67
    0x5507460707165510010001100103664242c01d9a4009003000c85050203622102d00269440710075000040201c0e102c4000010986915809460b0300781e501c070000d00600c100c0740505a01d03481001130029560031402e040e20245841903d0740303154a48040d00f114035004120001448081032100001210750200c0014442c525050040301c104200101134a91182019031112001e12030500600c4515007000076034105010030294500c00b5190030000f03482c1e90396120043c2840d08002c200000380604030f901c0c0006043c5050031511445040c20312400000181402400c6031850b8011480300f840f8450b600d404d11840106215103c00030460001c6e40c003407607113103200160092056800081c071645e0034900380b03600c40081000300d514800800c040103079501130b905040c1440f08085980650042d0300403908070040c9140300c00404d80d46001b6000c46442042081980f9611010a81d000b0b4006100354501c0340021034204800c000328130581040e110080b410410030303181840b280c41c2500041d4a40c0410041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 458601987 1250 458600737 458600743
    0x15050307090f091a01150809030301051309020d030201051b070507030f21080420090703110c01140603010506030f0a061d1501030b0c0a05040b1602130c030c03020a080a0507140714 79
    0xb01d03401b0346c209011940340803059203450340014482c0038080c0c0c0038102c485000503c190b200307410f40e0b54020585906144203040090003480120341c4000d041c2c10f94182c03008490480d9007901d08480c0d20400401c501e60650341d41842c50002a9400c03200f00b0a180302055008201c1051494042d400e41c0d9001400d00e014180703620000c030721898110140c5448040701141c1d031566001642d114a5500f000b06182203204036204840c403c403641c0101a5191820740d180a0300c46299035070007040300718000c0c0440d4031114101a160401c0004461141e4092030360400054000e800650b00c0039200b8000e6031140b030011450509041c46018982a130554041c014403c1003090a2032a401242d810380980c01c010314100080d12600c81d038083e1003406900403500e01416003036100103640e066809800c00040841c03600302040906000e0810344042801e2050460090384240b00303848036104641d950301d01c0c9450f00032400e8010b0002401c2c0604000303d41124101a039514002400128461b4424000076060744640500b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 458603237 1250 458601987 458602019
    0x1302190509030c0423180d021b030f0a060b06070b040311011a010f0c151107030305130c0b0c012a020f0708030f0c0708100209030115050307090f091a01 67
    0x88618038051010311243c0c804170f0841401205010811543e0300d40791002c02070103510410b200400d125102c9018051940440c0c100401c00e10801c03c07003903548203c0c040540b912a040d42418450b803281c00d2990120b21a030b040822056000340410f031034a199603d910014840c205ca00390040340c00c4c41d120003030a0909116040d00c484542c074501102c090040002042d024006802c1400c02200298100a000c4480d080d00c64503802d00204000c04010071803825100d803c4610309030040380c5070900040d44102151205100290b010001411380e500303002681842d500100d41c004407541d42e804440300c6600013030030182200850b405007090b00c60003014000785030240e208100201d0741c100407402c000c4254000242ea10401001d0410381d1070f07080d124250340c908903050b4481c1c0a03600c5641c80d8030700c010794154010142d43e44240c2c028403101c1103031000d29000c2c420611446030140d001c4102041f8043d001c0d0301203e0704680c100c90120350000317503031545882100d4403000c0040c1140e400004109010018031110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 458604487 1250 458603237 458603239
    0xd0f0314131e03090909140a0c050102121c09050c090109021e0c15040f0503040e0103060b09070c140705150406080916050f0f10021e0a111302190509030c 68
    0x74105602070760f0000c102184600c111004a030f1600b01c50030800c4220303040c4100c291040707000c0700d4240080f42803245c1d02450f02d02c50903000d8041c0340200104004110200d40e245004410800b0650208501080040c808084181c440340540d000c50540399884000c050300030b000d40e1801603101c0c4048407a034200c2e810302e0303c00035005100400c050f030b000c0c500c04a07180018482d1a91003051a40c2c81e828440a05d03080404010114000014003103038031111020514140c0740184c00030060301f5084d1040c42200c2d201520100c000c1200103119200088481c100c0503620100c000555861569940101c1c414101013039102581000c0800c041c001207600504c440d9200c0004401060680940c82140400414078003030140240c003c135884030300e82c4d00c0302d18641d00c12104c0505a80301c0c4041c0040000d40b00c00b0f8152201c1a580c0c0c0b01a40b4800407040003401040c000c1e040020f2114140c0700030108010701580da2000401150240040404100842e0b41d0300184a00c40d00c41541d202c0000040506100c02c82d0015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 458605737 1250 458604487 458604533
    0x8130c090c2a0c031403160303020d23040b1801111c02040303050304080d0b091807060e0109060305130804060906032307080702010b060412140106080d0f031413 71
    0x64000c01c03000c1d0300040450760400301c054801c0c5d082003501070031481400c000c2841d07800c2400c5082c0070103506600400e18181c109904004005040030420b4100c40c20a01c003c0040b500342010a0200d07035085402a000f403903c0900034840000000d015003950307401c802000030300001007130304404880c5152400a401180000443c5010f0641d40e0241c014040500080c0c1a10004681034013411419400303c0c038a140010000400742ca0218075040355955000d881d04080e0040c104001100b40c0030b05450103903c00d050f11914540c0e030501d10120020500101580ba00d28000e030640c501040090300148064100d81e5100c01d910b03400c240c40076060328400384036081c50f400d111107030300358034211350904a400c40d642d46010107040d12a03207001c03800f61030016045980319100090000d103400010604079210b074400c030004008064210750141c01c030342e400d200e2640c140c0c12542c1d41c800083d100740c9650f00b907907116040c0003442d24003101442c2e0104904503400302c03840b0040f20340c0d02c040c4075a070030103940003640001e20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 458606987 1250 458605737 458605817
    0xc0512040503070b0c01110d0608010b031c050904060317071b0803070b130b010e01050f042c150408090103060b070f08030a1413021c0308130c090c 65
    0x480c2c1d440f0443e11070a21402000b045151240740c0a402141c1e481e500f400601c2e894800e101041b00040c0032a10404485610308080107906040101d40440b84c0520540c0b140780840c0b040000750384030fa00414007660710503903034a00031000400a114900185250340403803500d421680c07421251a9142101e0900001200705c002c00500c0c00000459141c00e902c40c0d0050000d803550301509402c01c80100000380f5512482001265000c462800503048400440c4d152051645400030f1004030b890f0020132411580c024034100482d80c41081180380591140c000302c0f01d0210346d20f94038450b068801d4500b02d40c0ba40c40001c11021070741c1d160013010b000c0c0500c0258145004916920806102d811001c01001203e000c8001408510700c1e900850900514000c46421031810340340c80303a20014003000481c85600340d80c203038160a16401c0080100e8031303415114042c00d9100d080030301d01c10742c0d00b86100716101e014940340850007510030f00442848040907201c0c0e11001844000740c80070b5034000b1200e02005544c403c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 458608237 1250 458606987 458606989
    0x21020609030307030f39050f120408070b070e0a0b03060d060e0c06070c0e0f160e03120a02010506010e01031a2209081804060303170601020c030d0c05120405 69
    0x2c4036041642c5050016030900800703030b1070010301020b000620f8242070f2100480613098040440d003c0f02500c0001c0d210111921180c1a00d16005412000748003107011b1100c01e040551707003000c164000c4e005020450038a00705548001a406080f180c0e100085c2c0e030b0030b003052258103100101e013014142000c045410341c5880b00c0031800102204c0d0025000700d4880b040f0002201003071120404451010304441e582c1e040d50705141160300c10318460030041e0700100000803011500451074034092540e404068225808101c01140c03110b62566a0942c035000d100343c0909070303c01020003844210002d80000c01c0e64640000054215400800024180745c140440300b01e4802d01c0300700c5902d50900490b85500142c8444040303100c034240d4182d9424100b4a0503407050b0900900328050540b1742e24401446914200e5202408299a010301c0700601240b50f0820041112454038661030b03000e0300600c12900250b00d00800a8500743c0c0030300b2000c7c0820030130005441400418841c440c3c4882007001860b2030249024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 458609487 1250 458608237 458608243
    0x1060b0c070824130b130b0a0203164e0c0e011d03070303230f041a091e01120b031203040305040f06020309011704240605030a21020609 60
    0x3c1088078508000107044040015414903c1900032a82040074a05585092294400c0c014141c480c0e22140d80003801a0800f03000f01c1b48540d200d0245121019036482056a003c10b500c400c098900007101d004003440d64003100d5428003805116001c0e50706281d4484440c50703242e405a0041d40711414061502c1c01aa00180c1d100c0902400f8a0300060200110401c4024407000649040d41b502502500006142c1d000c80e1041c107200310801d807188001c18042c58805144182802409414020701040102501c5c00d8400c1484541c0d070790500780380440080010300d1044524108020059021101d52042d5078041850122015600002c011152500e0002903848564103091200e50782c00000080c20035200e1029500184000701c140c28502313440d00340207901c1c6c0d081020b540c0d00250003506201c174201d5151264a000d6a0811102400d020741d202da814803048000d41030907003046d1604000102900c00300407041842d80644112000c0e0821240c00008580aa03c4a40c0441d80f061040c080114004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 458610737 1250 458609487 458609533
    0x1b0d0e0f03030a2102091f1103030f0406020d0e03130305012f09030c030a060b0306070801180507020712050c0906090601050322060903050d110c07030602130801060b0c0708 76
    0x4000c031089061840c0b840350000c1d1151280d06d0350040403600201000d84440b94031900c1e021607075203c7c008045c80071001e680c0d0ba4041112590074402c6a0004240420f07087c1d0b004101440a602c1e000c515220f90760801d51955108031400e1210000401c03080090001c20f220f034080b20b002d4503109508101d091100c039a402c580581d07000c83c0d01000010000910359003007103000300103840075059400808050030258020402404054000d01450000030a00d0344030b40401816240d040c2801c42c7c020041c9015400104801894581544501c0c540850300d41610002159054481c100412204c051601400000d5801070221800f9580140c184022607800c075060302d9009003008401031100c101c604025241000c0100003500e81443d102342d050174142c0c02401030401500b00003091240060210b8000c0d0f452054420f003242c55000601d040c030004a4a070020409203803485a90452261219aa071b0300310f80007030340003011000e800100c101c01e5020070700000300244640805001141c009800f0402c9402c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 458611987 1250 458610737 458610767
    0x102011a01030e0a060e0604060b06030403050304031b0209010807061412010e0a0b09070c02040b0f0f010507020d060c02030415140301030305090415032904110103021b0d0e0f03030a 80
    0x940d00f451074040c030b0030010a5030f07558014005105110401c030380f458440c0c2c02620107a0b002401d0030318001482c2011402c582c05203a01d607071060303c4c545d11518111207510310792148075480400c402102026940c0e0b541018045d09a070405800e01600d000b50107084050804041070b000003050006039408100d0111240c1151494442d81d0110741c0c424a81500400e1400e0540380c0c044050814460f01c50303401043c001441d40300340c8040045c11049000c00c09868034000100d940a410b4071404480c41d440b40c0060615244041c1800b50484540c0d0340300b1040d070f0660502900143c1c0b0200b81040303145154550000800b0090030050311004454003180c0c0789100500003c0c0074802e00241144042c2c480764802006008142c94040703203140c603450468418003000159104d400d1381da8203512416a88450220302031035214070728000704031140005502940002d0f603c800e02c0c40100a181500001c180804440e084956460003501c1c4140d900704081340000c9011240241c1c4184180249280c0200a0700385a000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 458613237 1250 458611987 458611991
    0x130f05060f0a020f07090203270c0f060c1005062701060e060705060f190e1c2d020601060e090415180308190b01080f1b070f110102011a0103 62
    0x80c1d07040c2c01c2c0e103000d0011442c181140b0501500252544080d07016501580c0c01d05000d08110540030310640c00d00050003104121038001d850000481c0c034121840400c4a6000380c4294180800c80c0482401c104100301a02d04d204d0710b0f001001114a820b11280200c411003080c02503074030b0714214003a40d90190501600e8140034051507603114035a1100280e40c0303c241d0020444400307107804071510100c4101694007402038002922a84410170042c0110303912511100010b01d401071600c0b0b1030500c0306020410340ca040c01070b202440d884c111400007540b020448490540818203068480003031800d001640b11100b004801941300d101c940d2005419504550040f8a818080482c4540c0c9001020003410200c0441c0202124204142c1c100809511440221207100100c014443c1401c0c01e0300c151260342400202e0501c00114600c003588511900301321980c030301e80a00090038640c03881c981e02952003990301c10340a51a90701001000b9030700c002c0c281030a200900040e400c00c2e40c20144d001104141505040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 458614487 1250 458613237 458613247
    0x3035f09070306020f1305060a05090405042d05060606191211161e0b0112110604030305030f100f05040c020f07060e030f0c0105030c071511130f05060f 67
    0x22008201c010041c40d0020401c41d0b803400d5200fa0700d0402e503c4411070104441c0001c000180c240703000000d40e13484603155100d0602e89460541004001e0400600481700c15503038881801101c1e00c1880b112001d854030002c0d0b800c0410090030f0803490440300408052042c1780402060701c81c0782c420307103c141440c1061301f0828060061401800080d04400c1c1c0c0c0030320a801e004c81d460403c004160103180c07549008502400070b12090022050100380c4c5550003400d284400d90040000002003109585502d014403844004110f048000402c00d51041d48190700041010003480340c44414030110343e400094940c500b03403403285010842c0401c0100313881107030702c2165280c0469107154000d005681c000d901060a4810041e100d40000e0f080c2c5c10948001d600920403820743c0c404100300001d800301c4003e0161501c9003941c1d6500202e0700c0c581e01030f5071708588684051030700c45540031181c000d10020451203990162144080c84d002d02004a0982c031501021440d4482004940c41e0030702118840c0c14201241035a42e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 458615737 1250 458614487 458614501
    0x702010902030a0320010515060703110105090304051f0f030209131e0e0f1903050403200405060d08070605180a050d030f0501080d0c03035f 62
    0x4151201000e0b41500540515404055014040b8450441c0f080c022412815040c10401d00321102103400c00340311202e1200c0f40c0038600d400000b500503035100340303004280a0202c0404500307440007034441c10200c0d400800c0c240543c1c58100e00c1d12034108a0308090101511105800034160343c0e00b4503080c0305050380001d07440078640710011101c041c010468400d000024846408903c01986003440141c4146000703417010048401107005018107000400a088180001e0200011800d0b90041101400004c0100100081d6a545000040c40180b080041c91251040a2000b51000140384034802c840d442400000102030300140c2d00241d800c440001410b41d5003010100c3e242008044c204d14074401e4022140411000090448985800750f500303100580c40007480c002907603070038000c03100944c200e003500c0034500d8480c060184c80d95000740b402040b140201905c20440740031301c0959800f040e24080000c07a02039008809200e1820324003040c100d10f0070010211700fa58072411050140380050003c00720346d00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 458616987 1250 458615737 458615741
    0x809010c1b0605070b0c07020d120c0b1609080c220b041e200403060e07090c020c0a0b030f010308033c070903021e010311130501180b040905070201 65
    0x407405407551681c8110b48070b440181c501d4022480031148048171131700041c1c000d000b04e021303516243ea021b8220010340c207903652078000240308502e80e80c00b002644642d620200e03500340101d0b40114206c500710300b200742503000700502540b0345400c00c600da5400010012a9030705c4044004850041d6081d00403003000007038407004050300000070074590042c100014600d05100080d55580070714800001084a5008500300d00025615482d42c0e00e552602031104001190242d0000010309041c074040e543c079191241120070444085007042c0300164018010800079042011224016080c903444282c2140391103030384602d20b003005000040071650003001050410090078060f40458901c0c000300321090200071886a1880c102c0700003001854404008900074900590b41c0c00180e81e0058500a641340800300340c40d5010000f42d80d054105075842c82400100e210340405171218003400319109400a281c04001840c080040703100c2588241d05290400c0107041000440301110380400c008261540c0f00300044e40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 458618237 1250 458616987 458617013
    0x31e1508060907050a090b01020606040e010f0912030e06060a050607080409020a05031006111e0f03030412030605220908160501090c0b07030207140319030504050103180809010c 78
    0x2005104410074000a103001080000a685040d03c400d03040b150303500441e20941f00c82911590158120310007061450819812480020040c01e0006c43c03120401190002102c0346c00c0b2080e206030016030044112654940507a44011148100900d47d608003807000403500a401c1c131446114241c0040c882c0c04005c1c01c1410b503001031000103030071900d601c1c1000001e4039030703401100c001003450707a043c0b030102d005402501c5800c1034107030000043c103500d00d002e204620040c6140551a54511072440e91440081c0204000e500c180e20840521a81815254000d1300703640d0030340c001038031404000a880c505e4440d4000c0c03a030030380c00030848003150480f07950070b2442c01c62003400d20005101d504141c0550520105400490416200d81c00240c2e6059031009100c2480c05446401401a0400f400801c500202654001c1590b40300605450303100b1100044010762000e82401140880c00101c2d0401807980c05108134948246948031010011001e075030345a540e0f1040132111814130952a80017010b00c109202c1d880 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 458619487 1250 458618237 458618249
    0x60a080f010c0f09061b050304090221060301060b1608040f080a0209011a04090b061908091c09030605070207150c110f0a1205030705030301090603020f01031e15 71
    0x400d44042032032414080c0450010007030224251400010ba0188605801c900b03d070480d50762003a030188440383c004207084014006690500c002d201c042410749180c030040c4188020b0100e040050b07103000c82c412751003400c0208164800d0b450428204203901400702151301d10000502101c4242055280c59070403402039810043e080e81c2500400700d200007000801c4044107000321071070f4500380e0340c49009986804039812040928030301400b082012410710741160035100c1c4010113490130000d03504503480e4400b01c0b41300d207200000c2141082c00307400c1200f4460310159950b802c0005425040d02d000180c0300300f0b0244001030a00e1369410000308114400d010002c083c00481181001130b00303c61a006185903800042520032444c0b6081e60516458074819a406c1150042c19402900b85030070804d9007101000001611340b4001084801d000680c14002540606040440011028258018001d02c08800c504982c18541f508000e0036140204d101240141449040d000c00c000da201d402024a0040b140e1180c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 458620737 1250 458619487 458619493
    0x6130803101e0e150303090f030a0f0f0c060e0904020f0d050601150e01110d0c0f0b010308070605070c02181302030604050102030a0c02030f030126060a05160207080c09060a08 77
    0x42c8079103100d801801d034221001181c5680c09a140e1890500074209105502641a8000c20603046282011541440e1050005050b54070f86100e90b11000c880320011305044900b41b0700190300504100700c282e072060150005242a0040c600d01d1400708441c500081d2000e03218084a80c0b00541c035070380700160a0201c070383c03000584d242541d640c070400d040c124081b240840402d0492442c0c04032035108400000d030210402c4000c01962440c072005860640107404141d40e00101a0442800b242050804da802148181003155a90a650502804481000d0508030401081d038041e400540d0b50340310004014507880300341d40d0441d141c684130001c0b4051802d00003900341c043c4404000c24441c040d805548600e600c1c0d2070500010301098000c036240d104140300e01e0303a80b10040c40140043d2403010305000581c0d80102100d81d00750080c94642c0d203400000c55050076801d0312602005801808042d00398482201c60005010560812100c940c40e034030169406405648007000048150382c8403410030006203150016 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 458621987 1250 458620737 458620769
    0x310030201030f47130c02030c0313090f14040219150512010806060a03120210180204140105030d050f19020d17070e061c0e010213080613080310 64
    0x41011a41c4810301c00108001d5042c4c1000c20b080c814540070100d10340000c0c0f001d00c0d0010346142080080c54403040303640c00c40c072007404800c24600c0100010240c10321020281d54043d4039005404040d501034420400300681461004e001c088000450650000e81c115112510f90008540005052091303601090412082c5020202180c7e040002008030f4182c01d4020f068980c1c90700401e9075075880584041c0d412003005841080800d0010b002c90748865410b20690380160304400406017a21035008040e030380030003404203040441c582480382010705003000d25602c6c2d4561522001031f0725250b0b01c404582c14844001134160b841521601202c0c95419139a40d2005106031f240b00007950380c0300d40491000070950030030620710090749071801035105a6035a9a810b60b00c0d0026420700555401c030500c0fa21030503061030826000c0ca03216008440b04203041c0400140c8131401c0380c010f0f50032202c40794000c1140307401403414801c401030150308032410b143d005140f80b40c1d0f036240e41c2891642108a45d112100c5081d481071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 458623237 1250 458621987 458622041
    0x1909080a110601050307030503091e030d0908010c08040302071a04031a01060f1b0f08070b0a051f030c030f0c0f060c060c03050702060f0601120f0504030f050310030201030f 76
    0x881810260710040807100b2682c0c940d011701d940e41020b0f02014201d030303000b4046824a841d10200101c207998401034071a5070900860301082ca00f0b040c2c01401070100b071080505010f54030092080c00d040c0c090b6890f05841030b0070305440280d21808036000c1c000c8081159600400c1660f008001c650080d0740c00114034284030302d01420f03090940300a0181c00006011815101c10040c480d4400300225505900b40220301c400f01d40e90a01d0b512112003040343d11920a0041e07001244020600c00c1c494026a28045170601d04070721000514040301c1c0055a5120a118040c0089003451041e002540e501c1003400c04e0249060a003003e21070034a0388070b05802c281003200825100e51200c0440001807190348240556980520180e0584400b280c0d03030f000680c44000054081c42c08000704981100c0103042c040340c0588170300462000c3c0d42512410100075501e0f00305100801d5440203644503a06c606203001421410b040007140818009448060f04054032512403903409a000c0c1d001da200d003030030b0300301070256801004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 458624487 1250 458623237 458623247
    0x20a0e12010b010908030a1205060a05041401030201020c030d120e0106030c03030903020a0504020f0904270c1e0e07180510080a060e0114040207050a02090f16090605031909080a 78
    0x1c05990300044c80c1d0b18000940c00d1001040c1d8001c22115143c511100c2524204034004007402018185d2000c5004000a0207440d00c0c480c0d00343c1e44e6184a07503625150304600019142190011540f80660710281310000c40640c0001103036090110030401107012081d40c1c2505024000940024002404e111000410160400300382c0c0e003101d1003038980550890f82d4800b000100d004070003200b030551500304551115454640c1c44017094402144d850301103104a0000601c000d1611801201c8800c1c10741c0c018010001032084e01c0385188880101f40c0c2c926810009421a2910050240b0040c0055480d80c20319144002070002c000c7c000c0603025224481002c0740c0200340340004c5e0744c6c03444050b2622501040589035000054180c41c901b80c4055441c10120742880003d600448060741c1034002c01c03981c08010794507455440d0191290080c0700c00c4504168468039810b850013240b080602c0400803081004a4012055a50000000102c00c4071070a941c45428003811003081c1c02042100005070340d0190319001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 458625737 1250 458624487 458624501
    0x30f030a022a060c07030c090618050618090a02090a050f090a0b0c0906040b04090506131a01050f0d060b0a0311090f060c190807110414010603020a0e1201 68
    0x41e070856101c00e4052007000041c0c11041d0b65001101d1082e6940659410000000c20000702c10108850505940351038082c1c1500007504280d581580f03480040241c43c029403202d54050000c03440c1003001e41801800107150b4240e02c03400c04254400701001903000c980030b01c805801681c0203003a90441d40f40400500006110450340c0042c0c6810b4540440c2d141040050b803100c881d54008a075954a403110346171911150841220254400001c200200310000c28034080c00003440315203808149400d00c00c3c20400321441000700c0d1107407540350401e00c200c0b4030302007044010202400e09006a90740d0b50903000b10710702c1c030035040d801200a007004000140d0040281c000d1842c51901e6400300031040c0010b401d8501c40c403415864075848406420341301c00c80e00d000f20007050b035822080215240002040881000408602d01c2556045c0d404070b10f180500c071405d4144595640c040302e04004010340e903820503454501c107004500c20035902050410301c4034080da02c0c465031601c00410905903c00c030a06264060130035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 458626987 1250 458625737 458625757
    0x503070501050a0509030a020a0b0916080606030105070c0b06100507020402030403020d0e060c0705121c0807141204030f0306050d0c0906060e0d0f0c1505031f08100911030f03 77
    0x14144c002000c02c403000c8180d4011560a078060000701d0030a0311407410742c41000d0500c0c01c0031300404210251548004210500400c550405031066182c04d00400d821207134018056001d0111503020400011070000301d0943c00f0100b215007908400e4095000c03955400340503402034100d4070000600c8141a0001120210807a0aa83c0c03110100c9104c01400000d000e24044890580e0001c441400982f13450b050070f030341c440c294008440c500c80340c03c460070148041005c0034802044160051021072603001c0707061070800c5044010340703140c241e9410f40c144c024900104007400b0030400202d00c0e00d01d00d10a82099004000c002c04154580096090403045111180301e800704251a10b440003540ca800381c4151921800d00501e01446007484c1d072503042400d100f00350129404540500086891000012071102c241c045a072400e03100e1030482c092052403a00385520400d07441090904010a03400028240b403016108400460301c141c0e02d00c2d0841a00500c0400c9641c140550200c540c0c1a40d4000050018250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 458628237 1250 458626987 458626991
    0x207060509120a0e09041407061205010503070b040302010c0f0230010c08010509100f0e0402042f09180c120709060e011413031410180f0206070503070501050a 70
    0x111800c440614402da402034004a10f02e840e90050030310b0040c03140d0b90f105002e80c14001000350607407c0e190801001e03401074000f103054500540048501841000e000d064190000e16900382030a110b28543d008900c0024108030001ca0880c0800400d011510a9103a01520814034400b6030644111441100b100c9050b1f40c1c1030b520072040d0305210500640685980c142c464003590790900b01400002400140003000c00304804100140032514106c4120081c2034503030b40074660b828607204000c08e50340b050080c00045c0030402810541d4544920125441464208026658092100c0130444481c1d00d090480c00181108080000c0720041600a103810382c5040491304041d6551b82042da18402d13507010700320019485120009195000340c0302448040100b5042c182403210300d42c00c5108008030390f00101e9000d20200074500d0803200400c40d940091001d030b442480468000e085580340721014820151120a60094a8003951115000c5a48540e000700030b50340e03150381038180a8080e103801e80c0d28030701c114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 458629487 1250 458628237 458628253
    0x51e0d02030d1d0105030f0403080c16050a0201080903070b060f011202040305010204030b0105090f0a0504020d0f0f03141612030b090c120a060503100e011d0a12020313060302030a0f0207060509 85
    0x4d0320510440c0d20850200c412030744107840c1c03600d00b12008c00d00100384445000c000c0242054403da0700003054074103882603000300401c03040c520005009400240000d0880d60080c0b2501c000110302020b0799621400594403170700307103452a10040702e00c01108881c58280f03a100260100510006400410a0302d01407a03181d44d00b640d80304e0501106100886050700c14003c803502190406e541c035000a40c00a000030700d840400703074154956085000149004440190b20070350828201034002080201100a030f40d01c180c01d1090265040314440d4911000504005400c038007d901540264003103d003484000d080480b042c075000f4a40c0f8030031360044230a03003d80b08100c40000c241c808107000d440252280036000e001c0c5403180942c40009084d0142c1030412030354032034225030b042200f00348482140c03100b200000d01c02d4006a04004d641c2d81c0d1240384004c2103400400080800e015803480c0a0200e81381484c0050303407a51500e4800d07004020070580030050a0001a415050100503004180a01c480c030080d43c5000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 458630737 1250 458629487 458629489
    0x70302010b031e0316031809020a1106070c23011b12061a090a0801020d02070c090c05030c0c010204210203060610270305030c071a04051e0d02030d1d 66
    0x110f003164000d0ba090742c010450b0f103c501c030311030001e4000640f007400d14484000c1c2802600b61004000d07000b04501c50340c081124180113034040743c010442000003010f00414200041c004003054400321002c0c1c20720f91400035070070041d4005404200960320304002000340d5510b640349040250304150422000403050161004d81602c0c0788201002c03104c2840c1300b2010707800d4410610105801020400364402040b400000c0c840c1d100b03000a00202200400050b0384420524100b9500c21650f0000d0603034030710b45049210a0754001341140d80207202c0800c00c070f4440302130029082c06442035400040b100d514000340280303445144001d00e1001403089081d41d1080e65440140103083c8900c1e20f00800203020a03000940d410800714103106401c882e1010f0031300e0951030f500d9480c40c41d44007000c05c0666034000101005609180c0c80c0441a40c186450620724051a240018050348549102e024142c244520305503801d59928014030003007a0702606807107260000200c041d09a2002c000501e540b403064404000351 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 458631987 1250 458630737 458630773
    0x3020111060910050402131a040e01020906070204020714070305070e07020f060c0c10060b07060c02060106080429090f060c0c07031103031204080702030c0409020d14030f070302010b03 81
    0x10444003070b0001c09a44240c0d10241e0003601020304207070707041034000404a940c180c0034010030110b6038003030075080c0511241c201804125a01e00e1000c0c00c0350b034818005c200b030923030b901c5d4200c07140c1e00d4044a000d61661041d040c050500345820340714501611450300d00004100000c1100c000300c8440003212a100da5880300181e85505012000f0001d0b500898006240406000702070542209800304403001c021003401070380c080300e41c02d0f004008444000314144007000200c3c01180d81c0c3c1c88045c40500307115450003001408541d00988000c1000e400307485440741d01a180c18074400c0d0200107020342c4c10782e414851101c40e100c05914131550318038006c1000080381d80032144119004c200c0500002d120642c0746440c1c42801e84001300e13110f54140420046480300140d205000d0f03016a010b0210705580d8041407041510341064006558081c80c01d104a6001692303a114900c407040307420294030101613081108142c21440380784460010400e000c50300f0400c0c15415805405585170660072511810040420419 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 458633093 1106 458631987 458631991
    0x21060f0e0109060909021008130b0c032e0612060506131e0506041202120f0a031704210c0c030b040201020607031e0e0f0102030109060302011106 64
    0x1020042d1442200014045030700104414200d076804170322001100700410082c03080040024200d8520038881c0038440e40d003e42c1103c1145001680300c0c04a406c15540c20b1080c22a4411000c80d04ccc1501d07000d4142c2010924214013954a071030001c50300c03200402c624541c400c2c1c584070006295160440606244411928904004c90410f824000c1803149006210010341050b50200b01c903803900412181640d599038000c0040c0c001034004140030000490300c0070850303c1b980704a00540030002c10600d8029120303645a000d401c041e096403d10710b40c0182d4014000b10703075034080800540c84c1241000411210303410701404a589a465184e141c42e416030041e103118004001300800c56a0510540354452010306041060071010761400d010b0030211440403002035510440e0b25400714080029440310003d400080d590b968440c0401d01c0a04514442280412038514206100c42d2006c12114 = true := by decide +kernel

theorem cover : BRFrame.Cov 458453237 458633093 := by
  have h0 := BRFrame.cov_init 458453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 458453237 ≤ n) (h2 : n < 458633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
