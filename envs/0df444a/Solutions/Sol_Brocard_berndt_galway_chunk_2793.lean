-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2793
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:45:27.815718+00:00
-- url     : https://prove2.me/submissions/f93fdc43-eb5b-4c37-9674-668c1662bbda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 502158273 ≤ n < 502338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 502159523 1250 502158273 502158281
    0x5150441011d0d17070b0708060904110d020a080c1212030c0309030403052a04050f0a0b0315130b010b0f03040813080d090312020a0f02091008060f0a0b04 68
    0x14890001c0c1c490b207800b803030109100e003841c559650090824075005103d44c0d00d0142142d60382100b015100c80105040c0c041100c50003a540d445811441c02d8183c90030300e40040341c1d000700e0281c002495100c003041c030713107081d42c41d0841c5107101d264000b4000030304c00d43d482000c5074644811060795405903000484030a148500000e01c0503400b403044c90000c2c030b583e440780209461508040c10149142c0820800000032484c200720f007402c00000c00039925044907a14a11601082203100070b41e001c0e5003450208103234401201411a80000c2032400462544811000241000c48482c80120881c0c9000c06020002c003501d01030410a42c440c050071840303030f621071030014130034007440741405010700003000090005100600940003114000503140c04054507040c20b0750411001501090026210b05810000c1c041070000195120380030703002900c000c52440d125402400814807019004049000108400740c5542c80b680008000a030b058a1103820010b02d105100e523000d03104084503e0030000c1c01000c0b85450300c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 502160773 1250 502159523 502159649
    0xe0135090c03122706070b070306090905060f0712090602040e0f01150e030304030804060305092b0e03070b0c0d23030403030f0b0303030705040905150a051504 70
    0x40060500040d46005542a0065000200f0031518050138440e00c0d03c814003d0701d80c0903c192614200d03403601c2e041c0141151010380c8091151170405000101280b808240385400424024840c90541e807000d809a800400c1d00c00c4140a507880e0140d004281700080d805003054030010340715102d554941c5000546d000d1420b0003103200d04441c0300039400e4181d0052041d2440800c1c06015241015071b00c0d140c2c4141398101d580301c00e0100c0c1e203c000300300c48030f1414080100918684070001104200100b40305100034480c078010300034040182034004403a41c003000910001d101c840040da40d200182c64800792184440c03c248400300310b032140c40c2d07003026500c03544902c150102c2000b41400c0d542c690f24104e014180401c01204180c0d40e4524501094509100a61299032161161951640352807541012100010a200d04242c4591180b100d90350759500141d04407401141d40d490580c404050b008c02e00d00c920740c4421200b0845104070310500000c03054840c19041d0140500319400c40d00d000071002000114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 502162023 1250 502160773 502160803
    0xe2e02060a090809010804061404030306151e0e0a050a09062303030a1b0b10080f030c0d20010c0c0606080c0d021201060b03040804030615060e0135090c03 68
    0xc007104c1220752041c0412130b406400740340003060345e1848403c4000c1c030f41c0c0c003520164001b9441d1001440000301c4055200880c1c016460301d2400d03940504804102880d00c1000c6104104c2e041004001c0340d604c016010b009040001c1c9100469a85c0d0070340000100285d22844260a41400c40003001e40041042d02100010280140d441c02040f03150403100003426040542001099407003880c0454074400c2d046102d840c40c0600c80d0285410010600d1401910000809181e0310410110380c50002c04121460544404d040080e0340745100e001e60b074204a129502d1119944c44e100d01c1c1007145a200b00600501e50081c40200005074403456015100c07401c0d03424441c4c102c0c5184014030011705203400a001c0d01d5402000000b00c9513100d40700302c0380c03d61041d40c0a4510500c0410144107000c640e1090002c05d1182100307202c241132501c000a007895003c0b100443c188943e40300301c1420721203503400e00380703520f04500d490820b02201445c03040040c420a95a60046100303043d81001c19040025028803454160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 502163273 1250 502162023 502162027
    0x10e0c0901050a0f060e130c0f020f0304050f0f0414070e0411070b1b0d020d05040c090b01091a0f040b0a02071a070b060d021801030b160f0e2e02060a0908 68
    0x240650304521107200441d00100707c1e0003801420001d901c00e04101010669032202d01040021000789000c1041c034240855130400c1100308202e0f55011210000e00e10181c400801c1c071002c03000024000c1a840300004602e44081040004c0c803980541d0220305c007001100c040107003134410300b9000d0207400f41c004000c1082075a600030030071310003419107400b40c002d01741300d40f491400f031030341c040301060360480c1c490072202c26101c1c0240010000c484002a0285c40030840c20040b0b00055400203080c1610b5201d00078210007001c4589002e510f0301400c941d2280d940d150783c56595990380c594442039600c034061450044c050000702090046c00c0d98041b0030101000c035422424a41030f6203c04c0b004040282505034007140c02251038006860b0b00100e0304c00800d8080b0018101d600d10300308103060f850300824a44080040d0042c181d0f005400030310303040080c500c0e40781c001c840060680101e0301010549801d111400e58045095003a80c03003801d01d070359002529030f00b80c44440c0c03101102030702030b10700141004241c4602 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 502164523 1250 502163273 502163279
    0x70608041109041401020a051c11030408071509082805040b090a09050a050610030b1008062101050117070b070201080705160602031006020c1f050408010e0c0901050a0f 74
    0x2c00c42c0d07015000b9008014405061201414060880c0c2c4a88408004200c003c41c10b03050f42c00801510801c0214680e00500511052003403151407484020001440d20501089074414407000e00322200e491840034108102101d00d0b820061295040008c4082904089c03104060107424401610151880241c903418103190500c01da01d28103800503200141c2042e04040c00141807581740c00b44a0240100002c001081c0c1415000e00c0390007108088910300b41130500f585000326481d258100c969910840c50301d20082d89451000603038041c1c004219000100d0400000f020019040d4480e40c121010310b00038011140d0fa0310031060b10b401d6039124000131080280105009540150072013a4407000516020b031800728800c0c8140c4200300641429103190380c3c0442040b420044590810016100740e0009040444021001400300c01c021000d4000000c042e82c0c44500c240d020340e0a54015185000083c000d200741e01c45c61079640d440945060788212a44400010b480c00c01341d850030143c0c0e0130180f03120480c1d81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 502165773 1250 502164523 502164529
    0x6030a02010c03050a0210061827061a210c030c03060c030c040803030403030f0f060b180406231503090a0303052a070501060603020306220f060312020706080411 71
    0x101050175001d502030b00300500030207003d902c02c48018250482c42c041c00186422404c03c200d440d000c901c0c0d0b41c80d00e088070035441e01482c02861012603a030300075800b24641c03486002860020070409172040d0840c4640081d10a00c40d4080441c9000e400c0c051308850f843c4281c82d04065a603032092582c0c0b030301908034401091140042200650f80101065403462410795100c40443c41e5502c1110140c000039540d181e1064007000700d004060b008000100705000b05170411106c881c05103c3c2c08440000007840c03d4815013151280d41203032000302007191a107041d125618058100710050021418031035032007012500c80d00040c0fa0180ca01400441d4000c0000040940c7d0030350013820003821640d003009402500032240e091121160451a1b0200781c10b9442d54650301c4d00701e0a64401e60042420b050041c0100851525840060309009203a521792119080c803907181c250043c202c2c2078800d58020705095022090160303c5141c807041002d40d03400c031407100d0f959000845401c0c1c0d00340e40040c4409516a164501d0349 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 502167023 1250 502165773 502165777
    0x304020402070203070605040e010b0a1220031504060e01080a02060714030a031b0206010305030910090512030901020d0206190c12090b060a060c1e170d021206030a02010c0305 77
    0x188090030051904000f500003d28103c02984820000f640c00502802045514000a03004244845c202401d210500001410000740901d920052035076031504134085400ca803081c000c0031090090019030740d0501003c0404a51030b0102d800c1c2c051801e105000920134002580325040303c0b641005410700c0400b6a08004007980000029201300030300c09034023000c592090004100d04500c50b1000600d5590458011802c800007990302c4080d13400040c0100301268020088448881c001c540380c103034113952001c0694817100303260813664001e000065080e44c0c1c510004001c0034180400d23007c071800341031903010032a0307a00400c80d140e20000c10f01803204003103030039513070404110b0359440d04090302034041c80079141003240c0d0345a0054400c0d812039020f0000600306041000301520061a01c5000c1c00c009495035141e0b025003003482150604c0001041050022242e2141260214128007958805007001a007000c0d42091988080e0f902101011a0044c500001c038200041c0c0c0c180c58a82e5080c1c4a61001e451035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 502168273 1250 502167023 502167031
    0x23a0e0d03140c060702030a17040f03030c02150a02040504050c0708070b0a0207021f08010b0a08010e07200102030603060a09020319060f061e050303130b0901050f161a13020603 78
    0x144800d000b000ca540c2014400c0900c5145c0300e80c0290380320b05440800403e9500084503080300102a80103210106618240340e00440c1d40604011804450f0380000b02d02d810318108411100310f544506000c0d03400d01c290020000c45404540922a40e02c030880454824420b429000f4020602080340400144241e581c6a6000216400060402d80c068005c26080048202c0a081c1c4651101c058490a40c200f4031a41c098403884052504003d003415010f003c1450600849400c1d204110000309514864010200d9200843c400103c0e105031248805020790020780d009031203401a0400500058542c0c401d403031030250010010008100384d50480100c84034408016a4401d403540f0101030320000c140181401088200d2500382a900c510036400c80641c5950400352107074004200b00700140380d0803d244c01c1a6000f404045031398240c484010b8840b481010501000700740c0100d805201c28a115460322615030007800c03d0002c980c4c038000da001101204a840c1c4804216245001c805070030280051030340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 502169523 1250 502168273 502168307
    0x90c05031005250e090a05180705010203070305070c0b120a061e03030c050705061602130e0c012a0c0e07090509130807150501081c0e0d03023a0e0d03 66
    0x14929044017107500703850304a810800b219280c1c2d0030300c4007100040500801c181c1d8031201070031030107040c00c00003034030b078821100e0182c00c2040104d051018068004007201c028550b8191050b0b40d0854044419141541181c14100180c5801000100c0305560b4111000e8120401501c0c1051810b5980a403400030002c4010344051040705400300d215102c043c0201444040c3c01c2030680c501c6030510401c0a4644035041c260380c020b04103a80800c0000000030707468030100003400c203408004480102d480482c070303100e42c0b22a000240131030b510041c410020344800503a5680001401d003541d03021401d1f20341c0c100342e01c107251f00943c070000041c0e081c91300380703d4420003244204000f80c0f80100716102d00946c04210364154401542e5000100104031041001c0d100b90b50144092085c0304900000103400c0020300301c8042d0080c1c548641c003008251081c0301e00d50344a0391000d41c0c220a0006c900e094960b40e080e10060000045880c1c1002101d00d001b086d070140501d900425001d0b1a0700680c0d82295134004000d03d06d41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 502170773 1250 502169523 502169537
    0x207090509010f050a061701060b090409032309041a0d030f0c0c1401090608090a08160b0a0c1413051e030a0302060a14010305030901110c04090c0503100525 69
    0x4090f80c3c46025103030080843e503801041c62400e081481d9102e89005038904066071520404000546880c030549010380d0040320001110451424281c4801807446044c10044882d440c101003e1031500001e41a03d40c0b084d101000b07038003114062085a58080010154071280c0c071000080001d101c1d1038035072400178141c40d10f81201650382c1c0c1d0340c2e2082c8003103130001509885004080c203100d59100200c68000c0601e0b1810440c1410541440ca8690002c6c3c1000703004618006404550881d601e20303a0030a00d58480302240e9a807610f0b00f1000000c1030015a440005581640c41c0d034441c0c1da000050b01d961010100c00901d40c2441c1c602080035940e101101e5000b0484002c1c0d907005a030303801388400007044d030003500580349078941031554004884400c1c02c3c2c076115044010050001c10400000c0d111030344420708180d40d4200681d05610301e0001c0310324a10354410300b0b04d54a28200b0041c003c000781110000d408031880d0200095031441504c104940342c1e15000318004489100190300306000d44000d4030341c14040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 502172023 1250 502170773 502170791
    0x2061b010e0d03020c0118030f080a02090d05010207030206010605090a05010c020d0209040b09060108030a0906120605151804052505070507121e020f060c0c060c0a03020607020a03020709050901 85
    0x1410144442e48400c0400e6000c900c110305201d0a0141454906074210118400c40c174903a000340c03082e101c8240250410010100040610310194101e814040005280d6040000180761a6020354801d5004400500480000190403402001600c24602c001003421224500341401110404031121040e070b480003161107d4000750f112001e1213800350340a002680c9013845d040344158540076040e40506550341c0100010070f0304641c841c0c2c7c020261680c925150084070b0002c1801c20241159400081d4814080754084d040440d04000400c000c07034000e40d210b0041307e0b003181004111482102c2c3c58a10040710f5000d168044442e0446540d0308038681483c0d4103000c03a907199145403003400d401958200203481418424840a01a10004404c00c0d000c1d24184455550100c3c0c0e4082000034107500801c00072036039100088041c00491412031000d4503c548600c010154250b4030b0107680010b40c09070140d00f000c98207441c80443d0300c44a80d40c00da002403a201c0d25000510005150081209600d55a584584 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 502173273 1250 502172023 502172051
    0x1031502130b03090d1403090618103e03070e060708040602160504050403120c09031703010f0f0e0411040219110706230f090a181802061b01 62
    0x3d5400f4860610061542c1c118808000e00250102d109400e01c6090500400c8658000065a01d5000c503440b000d07200c20796041842c240c60122015200403485090040451840c40c0150000c000050040040c189050007000c00156107101d400c4051705205081002400c0315000301302e0100030b0b50003e03120b586814001e49074100650040e4101d40c0040e00107815801c214101c2e01c4202000c1d050441e401c024034106a038000d001e41d24500302144800751100700c21114103005248070801503800400c1403c400442901d1b0398002d034001d0148414a0454100c04500c0540000545007a110705c49290101c54455803110b8003040001d140d016030050302085540c01500020348441d10100325502da20403c100301060503402c02c1072581102040142039900c1e05518000f11a84501418a00f56371568a02c0c10003071005082c4074074130503117801402c1007600180301c03e520b91000308400361200701040750b80341005441d808580000c00180d03114405011040103030a180040c528203101d50400000e0780b031010116 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 502174523 1250 502173273 502173277
    0xe03121003080c0606130e0a02090c040b1305090702011e051b0705010902040c260c0f0309100c05030105010e010806210d030e010504020d080f0906030a2301031502130b 74
    0x2a840c204e4110030280b1046041c14810401081130b8088140161840f03400c1c1c0641d50071003808043d00c5020792501044c85914240100c4020b086108849071f80c0d800d60004811440b65944581409055038900040c001c600c1131144000307404101044200c1d2082c1d001801000e8507000e0484501c4c0518101c80081c0030309940b0040c40564810000030070100c400f401000210b4a0300c03030300074080c411140700c00c2040c20400000182d0748081c14102d02103a0300c0c1c071100095540129031240d610b03410000301b030109068000a00078804810300350305201c44d034101c80d0200d5903400284a041e0115000315042007507917000388445541300d030f009041a164460602154900380c01e0740c540411540c0c00c84511007030300355071600811000310000070003031200e828035a0208030700c1c0b14004805428001c001c01d0001030004043c0456003503c0000f0b03c0c0759140e040072100300000300351000c1c5000c3c2443c0800381ca003407580994200581240e402c2a040381d82456840081000b0b0f6001000c2100c545010340380114289440b040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 502175773 1250 502174523 502174537
    0x103080f090d0b010603050a0510050d0302010209030106090b190b0d02070203010e0d03200712080603030706230a0c080406020c0307020301060f150c1e02220504030f030e0312100308 80
    0xf0207945526180015040341c001a01c20f00040707080200704820b405040107040704550b02a29911403404450808900a0280300000c5515508049002946c0e45040d008004000c0045801050f06c0d03c0a070a80301d4825000d11510709050014400030074030103200c1c0c5c05004003038000360010a60b4200d002d10f280c281209580c000d800300365101070340e611010400c0d0100404c009003040e01858124075813030311208042100007034010041c08200040454500b0b009481c0180c3d4843d41c280200c410301c3d00b120704124000036031003014140400000d80380303a03128000c0d1031040301280c81d4a107103900c80d602c0e194080c2d80600c0320110a03110411554005803002d1151800808255400403031407801d003189440388020500003001008000352044011982082c43c036a001214811503504119091000c0703680d00b100e41c00e40c44074400b280b11203080f50321112342101e0321440c8280e0300d800710041e0480b0190200c8a8120710850203600920208840140c50780380e00d40c12420320110040307003940d6507071107200170342c002c1c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 502177023 1250 502175773 502175783
    0x30703020d020d030603240608120c0c010f08130318081f0519091a0f0906060901080307030c050705100203130503010203010b0306061308010507030e150702060103080f090d 76
    0x41040754255040c407040200391910310303060164500c0c40d12050740008051400c0c000d21407103090101c03540d40342c2c0e91290006001d070005440d0040310380c1b504103807039802c51110074595001303d40160b001507200b40e10726404040700307468018043c0c5800e01100c100d1b180000c4114288126064640310754121803440100805008005103401c0104a142100648000032410182410402445004400c080c0441d868014034100000d542e04c240c108a9138248180682d8003841201000340111840c4200b9002e200e180361380200e82d0191284400d010500c0400d1189907031503081440607100080c8640d601c5a111070240d4121100c1981300c00014920180c03d80d0400d01680c40010300f4030101072254035180041008500071820342d807615100c01920b00c00242541c1c85880c00141c21401003c0d07080c900005000001c000304000c0c940b03448060010002c292900119201e2003d00c0310090070340c7c8403154411109940a8985a4a5503854051a4000003ea601907050603c48011030307413603242425450398011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 502178273 1250 502177023 502177033
    0xb0c150108071e0b0901050d0b040204090902041b0801061809110301032f0f040f0f3804181514070516031107180207020f09070e0f0d020303070302 65
    0x4540d00c0d103038003a0f005540d043c41e03d0b4a03050402000d0050801d980f84034034207007403242e640d522041c01c6100616000b817407194400d20200b000328020046034041d11610b07109480410151003680d61180051890701e4031100003801031801401a64840c00d104100e0fa0f8400c040c4e0324040f80c80e04890401e94800d500b883c10031410100c010401c0c450f401d00c900350b202010800031458103081500c20300303a0b000450700041c0142201e4031411070f00e44465208400740ca41542c020003080d03144200c5203020f1b009610940800c90940044800d004d0301b5800d103800c159a00c40b000710907141c03401007448041c2001544004d210320507607400001161440e800c001d950318880c0800100180c03500340e05007440b000a0000c4007042028070916800e40340c030b20000c550240d01801c201401c4652036481d5071405a25030400b02d1a400c1c1c00100790006e0b06103801800e00139108603441c030500c2c801e0740c00340482224100c40d03450010300704003508560313420801c2c1540303e0404060080e0740c2208403034000c44c0c9181c0c04104c0490042c4c1c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 502179523 1250 502178273 502178279
    0x2040e0a030f0f090e060105190809120f04030b10030803040803070906030b0315150a03081209030909040b190513030305060609061c0e0d051e0f040b0c15010807 71
    0x4412440e807803480c054100310380603100f080401088140d030390248201181449000c120a070f03000748250b812414026030719004a108800b001005004240c0f10a0468420b4055003800d0861b89416601e000d42518240d5041c540385880d15142c04001070701120354034486c0c41004c004030304220f004502c00c502800840f542e0303041c8a2001405080698800c00400d03181c903035109c0d031998010400c100040286003150102c0d031100104401200000108280e110181c420004100100c800140c02c00e00760002c040ba61540d9403c4181d40c40388504081146d01c10b003440005400106da0032409a044001d21b112101040d803500d90b504102c070405d54650f40d00f5600c01c10944101541130103070740d500141c250740c0075040081180206200e4012801c50b250f00c04101e90b000c1000c03803c1e81c0c0c014042c0c03901841c110b81c85038100b4007010f8059405610258034034014000503818110b0355404a0304135041c548626880c180c40c245640350241c01c4410162481d002d01201e50200d21001070480340a4080d502c080c194541ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 502180773 1250 502179523 502179527
    0x207081308030a0813030306170c0310020c0c100c0206040e01050301050907060203270d1b080a0804090b060d05101d06180c0403060203040501050109060801021801051602040e0a03 79
    0x806030301c900c11550080000e220125071112600c0e801c02c00581c02ca20001d5842e18041c1c0c0a82055002502c05582801c000002c501d4001203403850b407913064007521041410781c80f4139401d03031040300c105500310b030301c40000c40b00942084207020000b42c7c05031902d82c100800c0cbd0b5001401da54801e0740080300030503075440103001d50b1400788111030304408210700400c2d4542c602038000e500ca0041691880020b016924950800c0c0030f112007040140800a2840e014082c2e1b03442d10740f107a084d030800f00c400d07075103410b040c045866007002640c00102e80e00b02c410241401d14199154025107013540980ea00500d0901085083c0d01940c06160301650814000c124258140344410685030b00814649000211403014401c050700e9920b00c0700000c092030311980300103584108a841081c0b2450380018010380c40041044184541940602d05032141074005001003540c40c022b213030a070300801d00040300310040c5503140c3d50f083d80260000c150305d1400030300c12a20340209800007000c0321b81800206003290402c2c82450101a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 502182023 1250 502180773 502180807
    0x22b060f020a0206070806060403151a01080903040b1c0203130b06010e011e020307120512070e010f080702120412022b06050421030b0306070503011d0a0609020708 72
    0x40d003000800c500789050808000e554030340c041c214005004d0100f020451544407042118090742d000020041e00b4112010450014201080c200201e074000310070b040425032081e5940c0f4000c1188800942c2440d050103004412580045024200100840c0308203200340d40c01e001071841100341e0400070282c448241004070b04504020146410003111102c040140d0781c1002e51030a0700d662110801781031500c0d030001a40b4510a1445c0a04030303d92501030450301d50342c400002e0090801c401e28004070342e218403805689103046191481c0c0030822503400415403500c98100240c1c081041d00c1290210110107010201583c000d0f0400300b155640b1844c12015400c005001001e0b8654240c4040b07019035405c80041e0340e0703a01c8000002c209a0329000410240182c40c4894504a0b118009841201c002c0d00000307002030260b0502c85000340905400500c1d0140a0350680c1c1c100e610404111005944045d00500c480500803c0c2c2310300b09a03200c1011440003003038030107040e20341d00c01c080076650354071002000b1700b80d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 502183273 1250 502182023 502182041
    0xd0c0509011713150902030118050705031c03050915070c060b0f06121b030a140a0c050409090302120d05061203040320040b130614040504021507022b06 67
    0x101420500c0f04401079100034010540c0c1020201444000c41d04400c4043d001c1e002d0042e61540c04d10303590043d4100080400c0203001d01c00d0b021603425a50700e2003415250750040b28000900c180c0c020310018a240640c010b01e500404040a83e400140c5108130304410703540503210300c4001030a2508050410440d44190120140111005134072034096100291240c40740c401c165494012410115141402d002d01564201c128a250a5200d28202e01e03134a00902a10780c1190f10b2152910108055400b188646030700c01031207035103252525007419a06c1003c0c20084508404611600051070801a007003005002d11981e240030200c0c03642400b000f0440310792485000c01040e5003041004000190419130748051401280224911038110f08000800030004845e515402014a00c2c05010b00b5000d9032007541520171035540c0ea44c0d0041e018042c1300848a08460003900194032103c010401c0207008083e1491610040c580002001482c007a083d040e01c07480d1030f0034070546501509800300540c0303004008034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 502184523 1250 502183273 502183307
    0x21611011d0f010507050f0a150c171f05030a0b0a060f0e190e0d170c07020312031b040305070501090b03070f0e0a0b1c0e070b040e0c0d0c050901 64
    0x40c4030240e600146240b104903504905101000425070104101031101126160f015016034040551608290010802c000d00c00804c0300d1600c0780c009090303030041240d89103141e940400c003034840c5e90380c1c80d5209680000007001c101c224400301000901c0e80d0204a484241c520030302d40b848050603ca0903040c1a902d1503000321000d5074181c0700c18410395603810341c800d40c05203850f140c0c407000300700c1f604100b0010140c4c500312040a0050f412081c52036900502644000d0301c0300c41c50303070505940705540a60b8034020b030180294180c0140008080078125440616003140c0000f605030319445a031700010859134010307401262150010031007080f0541c0c124260000400c122a6507620350b1608620040c076019007511000c0c1401507090702c141c0e035230b181c02d52010302904101002d107aa8031120041d11002c2000c030281080340702d08200016101d10404988841121041400d0a040c01d0901005090000740200b400580b00001e0040c091401000d00452401e8006900d45070f0741d640c5000c00040c0925000d0a03071800e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 502185773 1250 502184523 502184567
    0x10605061606020a030b0a090507080901150509041e150b090f070309051002030106050d0b0301020909010303081909060212061212090604080609060108070f03021804050102161101 79
    0x7444000c940c00c940c469500407001640d074030401d4402d80040c03880c0c140d4250440c80d18080444e240d5001c0d81704c01d00a0700207458180707450703072982500c0742682c0c0e07082c41100400711254000c01541c102080210f42262195078a5060160300d0410b80d801d81e0005003050301d40f911944a280b001441d10b1080d440b582c030081e02c2c030b43e14610308100194030103100900010101503841e4541c07000e01c1300620250b182c40109190030b540d80d5950b040c004005801c0750b00c20069445c43c000404801f4a030502c01c44004083c00780c0703000d0480e032031514240c42e80007000305011941440b00f0001c95030f00415101e5028200e01c501001611160010903a242c054030040007907005980e5202c0b00c0c141c00030001643e2083d00c3d0f0a8074090307650414040404c800b030080b03070b10500b481c1c410354090003050200401d016040c1c840c4501191081c0d90380c3e0b01e001844c3c00c81d5120294100440143d0115507443c405c808076403080c000d030005031070b01c80404200221800d030038000fa03440c4610400c40480c19070780301d818159244001c0119039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 502187023 1250 502185773 502185787
    0x90806070504051302070b04030f1115010e06030a14010903080c1c18050f0a0b090a150b0f090f180c211e030304060c1713111302090301060506 63
    0x503040748194050948692a030544070725601382190100c3e080e4942c05044010141420301d4060600300f4042d0101003c601c56207900e1850100000303c0c0102100d00c0741e510440d903441e002e01001020350141c03030700d078042c024040303220041100103403c0651038070301500004039a542030500808041000e050640114000c0101c200802c000b9007407038084030158400001c5481c0980c0e0405001818070000400c82e004944484040d00070101c1d40e0380704140140b00781500da07070f240407030241c45001c0881e00401401178902aa611980d03154061441d0410240510309080c2d403940000d00c1c0d20f0000c95a20341c40002040800480d0020103911075510191540180b82d00c4081d140000d102c0300c444508100350242c080d035a1140410700301310096031084c0d540428610903800074407050312940122800e85043e400c01a1004049200c0c10030100072205030020705c040d42d241e00c0031080d02c150380ca480c01c0d986164400118009a41d45030405244810b40d18001030392201500113250130749101d0b900c1a4401d080900200d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 502188273 1250 502187023 502187027
    0xb271203150d030f1103091206010806090a02030303160e09010315060b0c10020313020604060801030611030f060d0317090f1b010e061605120a0e040c0905010311041806030309080607 80
    0x20114135006401d05203011340300044154a1400361010041d440030058003500386100303020600505850181040d07441654403400051b130b48940206000750180d0042002569428803000c04501d540c08628198482d5a120300000350003c800b071b0019500d24034209000800d4050f540718a40080031103050603414000700340b81980d25000e03203c850381685500040018101c90303000182148055000704100c1c1c0340e41c0c484000521000c0709000803512585044603c80400c0484825a40b16494003003e5400b5681d80500780180b400d06142c08405015140760304030502e05481c0f060902c03400300d040046c40009401002c4a19001401c00c0398a183e00300c0f49203050480c9d078084020820004150b40c2152749440700f11045c55010305480c0701a00c28003940300070740c1082d00500024180c01c01c0d2a45c03002c505c11320400411003180c00c640c09400108181c08410441c550003500218000a045d03240103080940d0786510300c913648002d10046c0040c65652009004054020001102510100d00104204d1400f0000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 502189523 1250 502188273 502188287
    0x120d0501150f1d04020903030d140112021c030507060623090c0306090726040303050a150504110d0e0a03020f0712060b0a080a06050105120a0b271203150d03 69
    0x212a41c0d0303181643c400030031911035404031040c0100240c01c41ea03070760314095085001008105070840880429100000704c070480700058071100d54000b4600c0c1d482e0b1100074200044480e03040802c80034400248414008255544510301c01031a940c154401d07403107000d42d042110200903040c1c003481410560305000840e0400300582c2c0d8001815150300800d85c44001d0b0a07100010f245c80040051080c00740301c003019000011406004620a803410310840e1070f82040441961040409a003400e4a115400c00007444c050304092241d172581c0300b00c035141020021505098450380b400d10342d40e56000c500d001b0209503040041d0743e5840441030180c40392a04041079900082240a406402c071901c0354545440c65850243c4000213143c01340484801002611b01103025000c244203180c40b441c4224101c0d080e42034041501d60303001c0c0e80441d4240c41ca581790000213a46d4002540d003135582c6d800c0e4181108980c1c908200300324801007940c0c40a1344a28010380340c030310001076800c1064091003c020307100000941101d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 502190773 1250 502189523 502189547
    0x6050109051207090e1c0201142401030f1e05040506090c100c020103060f090c0f0905060a05250b09190803040227010b07261b120d0501150f 62
    0x21001c45e00f800e29800040c81d01d00301301d441e04402c184519030030003015015884022112000c4d01610b1441d560302c1441008102c42c603660707500306400507201d0040b661080e0300c51191340040e40d00c00900400c0080c1c900007106c08448844103410b40c2c0d4001d0005204003000690350281090000302094181d140128030600300d40740d5042c0a21100303440c15030840e8000d030884009040100d0007440c00079901d60140001c0e06900b110310010030640c41450701e00612401c080b406a40300900040d00e0180e080c142103400344c4c0800c3c80302d001f002c8110141c42000380c0c0c80d80c0c0e01c03c80c1401140700b48030718140b00241c0c50030441001d0407454280708003480c0d80009100c3c0303825282d005030111205503050041825050041340107070b6000c1f8000844400119019144a0151a40e10302481002407510401d00c005512090404c021b1414884203001c0d40d03138040401403142440c10140010b0318101c03e07038030300e40040540002c00d00c40002a103c000510914841d0b40c0c00b1014445246041400c046803a40d0140041d904c80c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 502192023 1250 502190773 502190789
    0xf12053007060504020906040c0f0e0d0204050a021201080a020d030f0c0609081e09030c06070f1a1602060411061305180906060a0b0a030506040f090606050109051207 73
    0x115120594100305104110103410a00541e03600c00d003514140b402000119022481480401d003c200b046c140b0b882540400c000700d03100c046507810640c1d021340e034000a846c8190392000c507061610300181c0f00c0e40201c2d0702808401402603101c00c21030010403100340058001070103e0f441144003102580d1604102c0d10510b400d400c1603582283c0f2403204031101d040c20440039180500b00f030511002c11003240001c1c1420308402444120021a002820141e0303c00c42440540c10f41c0710803013401c4140340c400004d140007840303040300c0f2500b03050550380d40c1e07001e0007031905001d501752101080050f400c0c84940e140012442c81c1c0301601180c900b558a585a00c07002c607036080e014002c00707d01d6a42c11988800c020000d2b02000f800d0786555440c5100c140100c01040350850b21500421001c198a800c11442c0707401524456055503003018120705040b0010040146119449034568001381c401c044184618000c0340d000d05004035143e820803001400044250740840c0c0140005040840c1c03001d0041111800c0c0e0300b1034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 502193273 1250 502192023 502192063
    0x52406030c040e1003030311040602070509180d05031e061c02040f020408060619031e031b030509040e06060a03020904021807090609060e010503041e0c080102040f1205 74
    0x2248404070790050b600800751801010062142c0c1c1c07004d4204d4001103d110381d40900c404144452401c1c114000c0f445604c015a002c01414402445c0480300b113980070844140750300d444220380c031000d03161803511031204000c03d01c00001c2c8007003605080b015281041d4002c80c481d142e400c0c40c401142e98000742d808000034000303030100715800315507c5400103082d0044001041d03440f00e440b40001030b100c813800c0d1801889401d1410340444d88001603203915040f2500940340100300403030f02050601041c0004022810406c0d9090b44030b11000034915010300070341c042d664968644002e0b806000031501081c00c140a1640b210b8200f208030340d981360032181540d6050f5410701080d1558404180d5400711115522205404417041120895001202c8802c07203e403a40d485551796a00d9000743c0341c1a64610b0b602c4d0004604000280c00b00394084505100554601012075042c582a2a224031900f016040401d00d030350005020081c60382c1d05048080900b500026148201446075142035942c2c0480101900c10910 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 502194523 1250 502193273 502193281
    0x6142101061e2f12130504090f0f050a0c060c03021605061e0d0203040305090a0f031e0317010b0d1103060a03140712060c0f030209010207090e0313150305240603 71
    0xc2160001010b200f004450f85040d401c0700018030f03a00082d958034840e2101400006952406004a80d4010307009a4503080c6941c00d80c4802051082c1c4007003d907502c1c400d16607082c00140301122030100a029540d60009441c21901d4000c2c240705003610318850078445010180240d9864100301c0c1c1590301d40c03149400900c10b0070001042103016280c030f81040c05202004000516410000410040804868400c10750f501c4440d40300484540f40006804142100035800d035040040d0200d40344d1601a06003c51850189200c0b0b00c1d020324241c1004c0c0401d0400b0a0304020a000c5004a1f05c611900c546414118a800c0c0c0115000c00a18880a00b44001c9040681c40b2180b00780300c031902602c3c04081c2411018090308064010780b0500d5204400a4800040000c0c40e5210b4400d44400c010143d01401a039860401c045025001c00d090a000a0000304410032844a0101443d00100151803003000d401c0d4006201804881d001046242000c14030854161824616400070001982c200d40d61038681d15 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 502195773 1250 502194523 502194587
    0x2120307120509040618051e0c03191103240a1a0d180302010c020709050f18070918050c010212030a020d0f0f020c010b0f03030406142101061e 63
    0x7100c0c2d40040b805003051229001c40a40c00e41000d845940f2240c123607009041001800c0280f00c00484418044003010700200d01c201441103c07510740d07a00620b201290002d00303414200c01a50081d01c80c20100c4001c007582c0540303a00d840c80003800040080b02d110040714030b07102016012120400614590b10000602c0c01e4490100350700c6503441c40b90b0891540022410f42c0b401074002c040440d01400036100da8000010944c07560f0007202d100f44086c80e1440c14a44980381c03101140306250006030050f00030042d000c2080c01580c440d485c1840b0704041900a0444070b400e02d00d081c0280440ca00f811504400040b03440000382404890704030424100050b554840b503403201d402040480310f0480b00a08000c011141007044d6000f900142d80c1e420001c015442000c010803640f0a0f00b40d4504c0d400d40c10a120130403201d030050480c840c640501d002c40615200c4a0303516410140c000e9140c566641e1f408100500816601603580c020b00c851103082000f209418040103050242d41209803d2a00714450001385c41003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 502197023 1250 502195773 502195781
    0x50708160515040c09050c04180e030a0e150a170414030403150f0603170f04090f06060212030f1810140105150915090a120503070212030712050904 65
    0x1074001c0c054403001c05000c140c00308040c1e800c0e50141c4103400040008180b4810b2440ba99008107900312480f49051300d4101554020070000b01411042030707403501c201141301020b02c001d00d1034004540d17605041056803010040d420142c0816440d940d0424801e42c160180c00521090b10804203501001c150364885c5003c00c9888002040302c08940030200c2c00000708100705050070f80c0c0c17000b06501030080b952044040821602e1510000e40150300240d03040c1004942d80c1e00a194441302c06449904e425102c40c219026100052050880965208000c0000c1603040c0080016400d0000f1080e1450400346443c0004c042d02521080082e902402429405001003103613440860890205010760380e282100000840024411a400750505c118044d980085070811195441e02c0200b6141d040c502905840700690054803d190b081400d00b40c0104003101d007070b258440c000e80300380300031030355920184148000000a801e6440c26079000340041c60016040310000740d030b881c0803448c0c1941c40d10300381400103000d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 502198273 1250 502197023 502197067
    0x905130537050610080601030203070e1e0907051206060d06030209071218150c02010b0d0b060301110c030306090601022811010207060519020102040b0a02010f0b03060601050708 78
    0x14598001c085000034442064602440600c08800c20a0741e95110601c07003a03084840000f0300003181d180000b4510340c080c0e400303035800862610b00542c8480b240e6000c90328030a05800c41e410800c444d010001060b1500305026130340b24140385812802c042200c1c001c5206074401501c000d103c0c0401040d0b00d96aa012a1701c150010750300107214540d103040107400503043d001222102030780d042c1001c0003036850180c0d047c209940180c0c050300d80325028140e86058401007144c0c1781800c0071035407111807520140da2030151212031b03039000301e0b0300e0801c82c02d01300e08242c2114411603040c00381400501a07002c0c0b10030b010090b0307503020348140c0d00040203a44d8400100e0421081c0b50542205a22840203521940c3e9040b441a80c11841851444a42d4120000680c3d80e41c25074420940000d80c108905000322070764401c0c2e05080e0301180009810541c441c0351020080d00150342080040c0e64070200254408800d01448035211007c1d8058246400c001c00000c060348075031440584400340001d0390703c1c444d620707100e020108 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 502199523 1250 502198273 502198321
    0x92709060b12030c0d030b1206040b22030905100c140a0b0c03090601290d0e010f09020a150c0203030d0506100e01080f04140d0e010f09051305 63
    0x40a0800d14240000340180580203010700e02c40491000350072000411110f809010740001c1c805500e941604401402810f04805c3d0010030f402e80d9618545010403807107004500c1801c022120b864040e030842000c40001c500d940e454074811034160f010a0700010b03103e065640c29500103c0c48011102d0a48030000801402403104414200034071120402050724112240304a800e501c1c1a00d581c4031902c0c8a00082d0781c0c0f48500e030051801003103540303407201d040030900b451003074502900a50b080342e0306010740041440d2145291244550680f0460078030800120603681c1004100702300898003c28408a120b01541c5940148a00c098003964002c50460407007550080c110790759410100d5160001c0e2500340d03602c43c01246a100781a103481d0044414070701c54038040e5500700b01541c810401c01e84025020304156a804091340b8a181c104005000c440032035090780e03e9084200c00c00d000010680481e012802040240c240381c14409a40d407080480c010116000b000705150b207480f60346520280030700c01c04100c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 502200773 1250 502199523 502199531
    0x3050613050d020f1009020a0305060c09032b140c1c12021201090b28050a12051b01031116030206010506071e080f0c01050106120204140d0302011e06090b040903020c21070803030f07030c0927 84
    0x103003011980030b52c143e60040f5541c3c100c2c4220140000030f003030307000b0b0032514580c1c2040000103019581e0141e00552200800500e1101520340c140250010001205501001c40d00344072424001402c1040344d200c010006150400d00c403407101d0f202c50341c40310446200c5c560300203450420310300f150384250020b40070400c40e01019583d40702c1480c0450341032080003038201c001d80a642d00028007490503200703503101e15400c8404009420780558111903c101d003580102e40d003500911010280c43c4d03503034014040c98501c00000140c10350412502514607100f03030810100040c0104024445404070a41041d5a40d20694101c1c03200301c050f14059014201d056125036034845030365444001c8a505400020840381b00740e0301040b64050840c01d0105590460714050050380c00b00f00a0107445c1055110074020151a01e101d4103424601c0c08031504000b100e0388500500d610200c00d102840000c55440d039048105400c0c01c00c030700061071070013070300420003032045001580703414500c022010324050402421491a05c0200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 502202023 1250 502200773 502200793
    0xc1a091005042105130e010602120a0c17030402090a05070f030509150f0a0b01030207031b0f0501180302010b060301050319050703050613050d020f1009020a0305060c09032b140c 78
    0xc045030807500c282540d005e116a4009946201560758038140d95803640900610480703404031001c2540051140c0c1c00304002c1d82582004a40d1400c803074000800d80c04410713680c07801c7c07a004020b41100003415003c10640b516051003403154004428001c1c2080c2030502007915a1501011410320212610080345140c0180c01c1107c00c4100c0e8003120f1286240100c10001c10102400440490054890050108800c03d4444250002441030b00c2035441c0300310008081540d160340c9080c00d40b007081c00c3c181026417042e0245010181c080c012031566550a07526281590325160000755181c0011016415500640d400a4240002800380801a40d0000115441c1d4100f140c001204400d0040e01275400d80148440e1030f00c1d1074400301718104241c0e04100100319250340800448000d00000c04200d90041d400700340000000c5062000c1c43c8a02c26503c46561200e0044040c035043c41c180303100c002e41c000c81d5000c0c00202d0150f00c091000d0040d034945018802802417555408a510a800429182e071041c05005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 502203273 1250 502202023 502202027
    0x1615050c010c020a170307080a05060d06060801021801030e0c0111030c2512151113030b01050a0e10030303020f0919090f02090a050f010c080a0c1a0910050421 70
    0x404ca026100e0f07050450a001c0480100a9030f000030b071400070000700e00c034000c9101d041d89a0007d90304070301d004060b5460a8041d030342e0740c41150310951020f0017a03500852100700703031484040b440f000044282028802c2215105000d03032601c0128141906000c6810241200f0640030401e40348450050000c0704c110a46401440b00074508228111100104c45240420010002070344508140d43c44002c1c44032180e08485a880901912880d1a034800f00a111405081030b10a0290008501a200d03401aa505040c24006400c007103400ca030200e0f401c16800e02400200c081000f1084135018500162102c01e608038044880c45000032456000c80340c00c01c08003008011540300001c0f14000c04080040308101843d5200313a0040e40407a40e44500524020003581c10300d0188007150840c1490007408207006a030301c4d90550b42040300da5a00098000c0f007000c0402900e00007004542c4101014034555280c0624100d507501c07940c03402002035544480100e02000880d540380a01c110030f0202195036501c41c4280 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 502204523 1250 502203273 502203283
    0x80705100c0e03151b210a0b03060f04021c0818100c030c06020408010c260610030f110307020a021e01050a0503070905030304090c0807021615050c010c02 68
    0x80c905024640a024039480c1d0145004500284015000d000041040c068524013114000c040d01058020b04e600d8840800115004202014003212400241c2c142590000440a00141004c640c1840c0622110700d50340d0000f50315910844415141803203541d5403012403968402c0300d030160180c601c4032022004211030781c2c01810511054441f10402064010100400600c0c59683c1c1070100f442d0f035a9120100f0703c40c0e2440032400d030042a0140c03401d80c1c5c0303003032007401c54140c860f00f50001110000d40d8100d00403000c40034055480940e000c4c00b800e04010000914000001008506140d540c80e15140440c03500d420411a62010039003c44d120b02d85003201079200e8130121000c07480380d80940250920030f0760842d9030180c00201030703542608004188605035010307800a44002c06006940d0300005240d0341c1000280040c21004a010404070605030b4007403d0528098004030654004c0004c00f124030080e4580c02003180c0c0c8419801c40b008801000039540751085400b14081b650030701121205250700011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 502205773 1250 502204523 502204543
    0x70e030106060e1e0f1003021b0717070e061c02030a0821010b070803090709060f05041b02060415091506030b06091e100e0405070e0a0603150513080705 67
    0x107480005941040300d13540b807031a002d00c240c6038000090328041c145410301ba18160005075140c14011b240420312050b03400f50020000d514001580001e905100d00d080b6181c00c1e00803004102d00900540303050440c18a40321600508441c05030700008070b09080030161140b082440740e00541901c8003160503052540c05075118120440b5601d804005500580c04561040c1c0d0403104c0c8143d6042c2400b8135035890840642c00a0043d100358400c480003c00d92200c0c43c81480c00a03d000004481c04904d020288010345030310080301071011924840342021160040f4403240d005031301c1103078010401340e08130700003000340010103000c1c0c002501c040c3c4c10040030300303203900900c2034a00030019040700303903215030402542d140106e0340301402d0b04a061342004038441040256400004c10309003800c8054885506480c07902040f503003030b1942c2d8410403041040b41582d4a0f42500700825038024000207007161901079509121031113030300c400c03581c0e03100294608c25091078125400d5440940c040d60341849040841e03850042c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 502207023 1250 502205773 502205779
    0x90103050c04030812180f100207020d020a060e04050606070b04020919020a0923030339010902120609032706160c0603061809030e0907032406080c03070e030106060e 73
    0x1b00e25269400d000030f45198088108000b40800000c901c84d0304041c2d04a584220b800030000c107100380044e940c140902010f0b00060780d500d810011408104000c0c0d420162969011b10020000400801c18450b521035010b42c05482c0c00c00180c56054415218910780071310455450301c041118503101c0e034014056000c880081c401e85507a01e44d0441e00c40105462040c00c1a0b166108001c3d0040d80b140c52102d803480c60500454007100c13503200d110402031041c0c050480120300e0f55100d11030320031498400080204501c48030014001c44c174009240d240e8902c5403180849800a8180e2065129110810518035050300a090280c0741c554a14000780400c00c0e0350001c03503d140003424040f40c02813091040c10300321171100a00318000c88850300c00800400d94000281c0c2048a000d40e0f2007a142c41c0c0300301c900e0107001d0503a4005092041c65000d08804011405555601411030604000c0c235170b4440d4403aa080014028000e50f2500c42d040c00340c1e4002070582007c1c1c0c242d4200000000c0498110002c4101d681c0b040e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 502208273 1250 502207023 502207051
    0x20c130b01110f0312090705030703060209180108060a020d020c0d020708060c1207050d0f051f0b0424020f10021201050f0a06050a020a0605010305060711030f090103050c04030812 79
    0xb068503075119000c051483e103580d8414003100c2040c400088802d904464420145c83e096900c500c0840d08180d01e0703402c00d4503082e0b000144c07070b195801d243c940300d5120303100100849825410914025114003000e800260090340100c0c44d0548410b0035412244e1540540c0215180c840c02e001001e502d85141c0c3c8554900303809120b00094105543d00d00b155914401500214803e999103001619160485660204540e40e101c411441072021841080d01820078020340c00005040d1662600386030116422166111000b444100000848402040c1411144c90b026504143c01003404030701d000500c2510051521607071484915921075075005108041c014850200b0300c3c0e880d0b07024481c9091000c0c400759001492a001000364501c01c0025006000c801e2040d80d0b50500f16171a100d00307591081c0c1051380d190300701806014015070000401c400110301d000146090481602904000340500d0f40b1281c1415115400036142090f900704540103594420002030300c0d60034004500070b40c02021181c640382c0c0012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 502209523 1250 502208273 502208297
    0x60108011508060c0a2105180304030b04020f0409050307030c0614070f1805040207050c030709060b0d0b030a1e02091b0403110f031c0305071806030b01020c130b01 72
    0xd01400781c000d07507000000410b03244d220030031402c000e9030240718041e04020350320344007600c0c500350554200000e030765000c03000c41e1a040c605458480038103820a21610b650041004100007400300a0707140e0300c02d8040b03803a440b04400f0b80d400705024095008004145000c001403840030940c1288a0406550103007500300807503c4c200240f240002410f54005000c903c034804040300d5188a01070081076030b030039661050481d1b6030b10000300382641c101e08000c40d0742c0d412000801ea0302e41010000c0380003e00001d4800d010a40c500388031503042c0e00c901020403c200f43c1b1a020010992003c201000c0c070258801c15400c0780701d5084031003103001d10000c1000c9128140c80000b04028014600e5440700494500c1c40350340ca01031131580c4010440002607907480c0c21203407003050204039903001d2102111428001d200804200200c440003402c0340c40042202084c4482041610b44071800440510b0a658140c01c0000d040104000141c0c9000244420301754000403000101070704840030f41007000c2c17020382a2628041021 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 502210773 1250 502209523 502209551
    0xa030809120301030209061f0f113408060703020304060507020705030c12070e0c13060f020309150714071412190f12020616030b011403150303030906010801 69
    0x100a101c609900c58244010700152074005582e030b400c41e40041c9144201c56004041c44031070202c80d9404000300d100c0000c9409241e800001000d1003003080b0003d04a0316030304074401550840c000344099032008040e000d113600ba44000c40410054040b817800c4501a10b0145002006503104071021105603081c06c003c2030340503000288140c1030b01c0c0c000300a0b00c0d1030080f03c8180a03940c0c015101c07280403441030200c0010120101030b102c6010340360b5900b8441e5501d400f07901d80448109641e01060820255001c4454400d90100641790100022180132456070b000111145d541d004128011305007401c00c1001c034900c0c80700042c030f40048480b0608185e02e02c0d60101c0811110000343e2040e0482c0707800c041c074030f00452904801a106180e01c51440c5850b4108541c54243e05010b0080c00e080c0035904c85003d04c81d4220030218180d03071018103441d00780030005680000800f402003034807042c512500040b02250607010008001c1c04442e4000d03003200d44034946080184d58500081c410f108141d481c100c100102c1d44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 502212023 1250 502210773 502210783
    0x27020c061b0c0d030f0b060c0c030c0d081218060a0c02060c04121205160b0121051005190c0302120714120402010e040504140c010206091504020d0c0303020a030809 72
    0x4101c2e10007620214054903019000b0340039600c0311043d040c0e81c400588080d6038a0394040d0040394100c000034465038640318145071401d1080d41c1da0074411082e034105000001d011104072464440c002795031206c640c480314020b141c460340d1aa44407ca50081204004440c4010750000c0c8001c443c0b035007141c002e61100c10201185100b540640c26200c1800075070400407621100d1689045581c80c0341540c58180c02116001030302411130021a110408440100255903a1480a20101c40c2d10a5282074003140c40e51000d580c2c1151421038840f0075142d0b00010a00785407000032440700d810030071090018201c600b4004000394440401c1d1807084841d900484c00080c030400740103103100da50000143c80d203044032120307076520030b03000b04100d041081c10401500640c580c2e02546014074880d002d18000c02d000d00c407404d4104071541e049036046600c00410000c1c022000640080c0740070304103909c0c9009032900c0c0081942070300820b20151049807441c10000416600190662501d070103030340d8104030354455107107464840d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 502213273 1250 502212023 502212037
    0x6020403020a0e0916230a0306020a0504090f02032401020c030d050c06010e0108070302090a091a04031e02060105120a0602071208090102041202010806040207020915040c030207050727020c061b 85
    0x3d030320020361a04910b581b0f01603c05110700500d403407080d50740e954034a0261380c06150004006100030800304084400c2d4080c016490b000701b0800c0d03046161030b4882808121b030100d800f81c42402d203480343c0040c40c1d000340494446c0c0c40c406020f527501140d039540098007d138040f4034500072a101c0d602c0001002c01440e0240e6042c0c4502a001e04102c03443c50b0204808603401070b207100310380d5a0b034607801c50000300f150400b801c810403e40203849043c90903040141c2103200c100c1c1e42250480036144c014040742d5021581c5410344000326000034081ca078511050380381000100000300b00f00d200069000900c49041108110000c580d95139035205da8900c0701241c2030740510302c41c003c819080c85402c1c00056004001595100030050001030504850380c00113042c0f01800c1da001654043e0300140b080d42800c19018501c0c900d00705040a520301040d564419544d20b01521400d2040151013460b12072943ca01e0501100d59841a04255100c44906400c282c40b507d05680d01030940d80c1a050740301c25100c0c164180d03104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 502214523 1250 502213273 502213289
    0x3051e09070b0c0f030705101404230717150702120304120c02040f0605090c12130812070e1309080a0806061605010911030a12030906020403020a0e0916 67
    0xc002d242040400d2a600040104040c50050070504141d40b20100064101c480c0540d008048000d0703199141070403143c043c0c2002c40034100b0f00c0d0421011a1017100c40c0c1140f084c2ea5800d0311151031400d6049420300740c058001483c0c2c2c111383d2600c10168100003e0314040307410111001e980d2a01c800744280d9032207006410303e48080c0024000180071030300c1d16400346800b16003424604c0f80201e1070f60008044a240012412440e0ba03200d00a100c0c0d070a0141609a001d00c40b02c450720300d841100403170700c00c0d01c130802060590a42c040d0340d6160104030170341040e0f6083c00600c203590106424004800f50000001130440303402075150712801162000c407070140c4110b45400c820300038581072102908840c21940100129000fa0017088104400b81c1c600d07100c42e0380d960013039000144031401450064410084014181d2180c0c1c4010100400728000d0121540b440d202810000ba14116624082010b809260700281d4464000d0710001034040d030201403d07119002050984104007204031420301c94244500411038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 502215773 1250 502214523 502214533
    0x1a03060d062a0201020c010516020304031704091811060711010c0507030221160f12170406030b120105040b0c0c030d02031312020a0210140909010603051e09 69
    0xc140682d121124007040c212019000420809004007048800d641910051307600080c00c0200040070310489030407858865408100000e0560020340d070b402940405002404410f4565241d246561f007110014049240203101410a81c18000c014883c0d8030015200814400400d481a1409404942c040c1e6440002c0c59481c0096900441701580c102c2011034252280c10404005a541d107002406070b80800c0c0b48490310038208608550404140d090101c44c144170401c0300b4010f180419190710165150340128924211a9041050300440c1000c05d04000035070006010409940c9a042100300d81030035a00031030382d0003030105100d080700c00417079016140d075a41d04040f03190500100014501d0031080e04c100c90500c11a0a03d5400b03d034015104a140c0e04030410340c2c1800c04c2201d91640304203042c03a00241c4440c000c0754000c1180d544005080104110300204071514407035065081d10400400503001d03081660b15050b020340181020b980950903070f50803200c0320142494813019a4425404000130740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 502217023 1250 502215773 502215799
    0x303230708030601020f011508010612020619020a080c03090103180209010b090409020315180d1d010c06020310030c05040b01140f1e04030614010e060d030302090604030b011a0306 79
    0x740580c01c0988035a0440c003c1c60180c40350035009005800e030010400324050981840c04811900316040da40c07100c7d1000c8094002000503a42e604151000090ba180c81c810103841600e5040381000314100c0001e02043c00440d8004002c036002014140309402030700e0030010341d0394100504c40c01a07408000250703c2620302c0c00503c0b407503181c8406000030500280020494841c1c90740000e0822100c803210700c070700a10840c10044070f0600820260004084030300640294000004010080d1010350381458441e0100034100d402644201242801c454014404540301c2c02d040b101c4101c100300710311040c1c0c0c03210030282c008602440e00c0c0c8202d01072010161918055117540c40010307120b50304106081445070341d0901005420a070011070500e4250b0051600c40d41d95803c40c50400b0446800c0344120f040c4910010040c4150080385070369070b0300404115242e0340d600001c1e1504030064400c801050307401c850041000000c00541108d26810707070303588400048500e08520b031025141d010445189510840005d901317 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 502218273 1250 502217023 502217033
    0x2031909150c020709060b030906010509090a1412030103030e0406050613030308041707030909240302060912010612050f030304050c060304060212010617100e0601050d2403032307 79
    0x200b850b40c2e03490040e106140d989000000448000d50301200c0d041d4000020012070841c00c0c0a8980940001c4a0300c07101c905100004641e204440b00e8020202215140080c038510740c01c026401c114051120201d0340c0b5038582c98020040b00014020343c7c01903091400125440c40d12405803a01410000240a011441e545045417070f2640903106803040f840034081003c030130007050028a00c0c1d0340207403030302203082c2c1c604510b89080390f120b5040300b44001c5003035514240c3e03518800490703411241c04480481c0c80d0021040003a000d0000c21020b6000c962822310009a100390202d04040518010001e9681e25012040b82c980c5034802210000c1a68100e10f80c860f030140351000195800074020f0400504240900001d1501c94800b80c112030b001c603040400901d5010108011154019118103084e81050700d0154001c1e410b46010301050b041c0304010800e848801829440400b11401c2d040c00b00003c1b10414948031400040c5010a030001541b4015100204a03216007030000308031030740d90091600805440b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 502219523 1250 502218273 502218281
    0x2090d0f331806060b040513060b030a02090103020d0c02250b031315050a0506090114030705060c0f16091d0304060c030c05032817041401060f090203190915 69
    0x2400302c03100511a20600420102d2091602500d10130003c90303696800c210400419203541c443d205402c504040040c00040690011b4039000700c11148050707101c0b00d000300181c029000b4403c21700080d0780f81c140d008075010f90000b801074000fa845080c1c2c0741c1c10110300401d00d5141c00e09000326105070400f0000b1503d2040d40c0d4291803000d90043c4005c14100c0110450b40c001e50f00d0544002c8841c1e07841c0c1c800e1091914240f9112401084400c00f581200d1500034086611000c551284134800c4001140c0c1e0741c101c0c0c80038070040002403001d01c1664640c0d05d0a2a054602807000c2c040c00801034034082d14040c2203509000d031500e0017800c100065045c185419012031b0104010702c0700300c0c00c02c0b081e50100c4000a01c20009040c84a41c0540b080e11410340800b5001d403503884507001c62b010001c540d480d000103084200e4513180c10a400000c011104c0701410015409001e5030307404866170030f460080000b02038180750f026600a00703110300c81250780b900b510f04d03041c00c0d100c6c602c4c4082d0201910040c07401000070b071640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 502220773 1250 502219523 502219541
    0x1a030705120708030301060207140a180b0f03010f020409110310030b100e0a1b140735070c080724030b04020406050c100c051c02090d0f33 61
    0x30031521020f840f4210681990001e138001800340e030201c80140400b40580030762009002c0140d800042c040e2400d11503001d02071004880105481d0340360b00381c80c00d98590b540030a24411001d030081c45800c41c0340090744000d50161252000c130750301d0b14954201552031001100e018044801014680c01c0c1540c07181c219003131000e08040098501404001020482400001d2081c00c00180024410400b1003007800301061802500c1e00700006102d440e104102204151010160800000d10070243c0c901c0300c13000ca004001d201d42c0c854441841c0d02c103020078400801000000d1260042102c7c04d0358440c1d10541c0c90360b01e4003a14030608801300360030020780d090800982c0c00225610b404100e0a01b40c9003c40c040317900a81044002520004072144500c904104426806503100c40c1004204400580140240144400c8100040c034040030b0071402d894a8050b104c188100605201da8910b0a16108420b0020008200d8030202c0c005c024a6898010000b0801d40c400c0c0044002000100c400102c001003444807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 502222023 1250 502220773 502220809
    0x81503120a17072706050a0509041806150b03060a03060209041b0f022406010e03101e05130302060601080717042a140609040902120705041a030705 65
    0x2035041182c0b1584074030050084400e40c82d00c244400248507104900d15031004400f0303020205040820a1680c0002101c01c078603a2840d0060700c60b011080000c01030b14034050706240b02c0000d01c98a0082c00701c2036100404d0410f103a0703180d088095a0303d441c030341140412114030b40c3c44a02c0e558104041b07181d40d0010040c0c150b005100003001c164402d40b855400e03644401d030200140121f0682102c25404001c0a01011400c0285a40512040c0d103c1e6028000003031010741080040d14a099003a1001c20021030100290703142400321505040003501c0d0301031400c0c00904014103100220b5607525011842c81a03503a059405010fa9603100320040d2011040541008100400d06e01d10404203421601154019440348104146144230821807048031603840300585040030360880d081151007042440c0320a411003d540c0340317494079130800024005200c3d0390300c003a4204003180755a11100e00c000c10480c0a5a008860030810103003260103440081c00003a01b00b94056014443c20300c424580310300111200c000034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 502223273 1250 502222023 502222037
    0x10e12040612022104020301050a2007030513090207030e090603100e1f150509010609060c1a0903090a080c13050a060b0714010b090633130303081503120a 68
    0x2104502a1010030165a032004c40352038424442185020f02a26800504c40d00c6e0503ca9502544d500700c460302291001104101e00000e41c071400c05001d42c081c1c0d41c1002295503d41c10748c0380ea4204410181d8440101280001d4200d01d1840442c54020300c0d0354001d400c060000d107a8008501c585200810054241c0c0c0001d00c6038a0101e150050b80c1c20030800113101d60103010410084c2a804403244543e20f801062046c50400018003549900411440854266160401c00001141040d1402903181315090752080e82c503a04000d1041c800200030010f10354207032400d00019690300c0c40992600d0780b100c4810ba0050a00c40600740540e00b90b0042a0001806080000d80d80c0e42d45e11781c1940c0c0e0b881590111009595100710341c801c0c3d5020300c1007407030100c0c003521300c6840d51030440005941ca4005104140c0240340b500d443d480c502841c00c004014140207800283d42d00c01d140e010304280c6010381d10044001651880000704842ca070480e640b451030001038000d100c80c0159019110540e0801c40b100b41c104229 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 502224523 1250 502223273 502223287
    0xb04050603091c02030a0e0303071a18010501060906110d1e110105070e091312050a0201140103050106090e120a0813320a02030601030b270c03010e1204061202 70
    0x10308040c040b43c001c0c180c0045955039000d2001500b00303030400c1e4039503200746c2090280e803010272002e03200003c41d02c040b9042259190344400e50800341c00c4080880c000c441d032034400041079050b04010041e027900d0722a22039803e280d00c0c0c401041e80d0b134203001040000043d04146501429151300200e1030308152241004d41041034051151809c60300202c034500c0000304400000e213058241018229001408080e000300000d12603224000362506030140031080000000c9c0c0940300754400e50200001c940d20200d0041704e969281000d030f000e080307940920002c9601c0c106030955032400000f94070740c14580d07200b00341d800c000290380c041c1d4041000419909801003822640c800007807000c2080d8030320003401540700750310494900480b0610b01c000100c11486521100345000580e50000d040ba0449500c09054051950758502491003081c0403040508207061007540501054004100c0800819064000300084000e010f070155480500700385060192200300004c2c00401e101c0c3c3c840459207048001d002d17181540e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 502225773 1250 502224523 502224553
    0x1014041113260a020919092301090f080a09081906060b120f04020f0310020301140f061210121b0b0310052106010f1a040b0405060309 59
    0x448004184110000303800188141c500c2d0003140030340741407a22100c115205081440c641d8070224500003a01c60003002001844601070201807641ca844e201c0c4043c414440a4a49110240e040d03505098503070b0381203c21442079041c14425641ca05070082070002c191074040d100c154080c0d1003a400142000007089001c51035030010040201402c1e0441c0000c0040515818000304607620b80d000f421900904020318088080040c480c1c0d60423002c1461080b900762142e200081b940101140c03010b40500030308445407843c04840e4055412a095000d01d0364041d08044200040f2201c90030445901c036505108440c107004400c089681d200f400400c25641c50340d1150f40b0281203605001d0100d17554003115000640d16802c004002c801064010310306c60071802d210700d201c00b0083c031768058140924a4214018075210150754955031552164081e60001e58460b09540b14006090040107000d5070f032200c0440f02d0300400401c44046138203060003542020f0038807040129541c40500044c41c1441207190341e00c0c8000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 502227023 1250 502225773 502225777
    0x5030109120f030c0e01120608120705070806160c061e050a0b0f0f040c09030c1e0803070507030314070b070e0a05011b170d020406020307030e060310140411 69
    0x34060580750241030768112000740880d682d000803100b00740c10a00003000450300070200100360f07a03090810685a8070034011120003021b40c3da01014480c824001c40300c2c2c007910324000a0a11a01580a0726405030b2101c0358140d40c0e00080d0380642c6d00340300700c04401d8036243c4120310b60320b01a4840d080c081212200c03d030415800720070250040e044540e0b16400d20241248522441040d080e0989002ea0040181070006191620400c4a2809103481ea1540d110030743c89115507c0103141c1c07251a80740c4290721002d120307460002c642900000030955010104882c00000182d403000c2d9407007002400024110b540c200d0340c152a546150390755400030305c4070100140d41e00400f144220020b9440c40d00b03509010040004410b000e42c4164140301c2c000c0002c010f41034485000c60401c50b04414080c0c558145081d48101a04c01d0981c41071456101003400f02d40907501100505065000b0b680e01c1c5030401248040210030300c006d65540803e81d41c001d00030000d0020b0310000c040c140200400c0080c01003c2141082402c2d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 502228273 1250 502227023 502227041
    0xc06050c03070c2402010e061f1707060221030406110f03130b061009090510050d06050a060603020c060a0e0f10270308071b02120312060907090308070c050301 70
    0x100e80b10482c1503210138901c100c019100641071009010700300b0050f140c5d070b0703c924002c4c007085400500409003070071485100e8403010041085200720020400000341e819111031050207450018001e80a038402100d9210400950307010036241c41c903103151241e0343e494004241304407880f111010240100c0000a5509001e10300c81e8225039110120303c016031410001907580103082e184107050b005030900215911954100c1912034105001489071150340c20b1200507056648156404100e035a0034508002c09a04200c0c0111400142442450780354003044d026401a00d0139985e055200301c002886400d19a00210001c1c020300d0291020042d69000c15414001d0700030360443c0071030f01c1c1c400108d01c11103046151130401000341e0303003010b16180c107030790003050000080d040808004801c0848002490356412031903019500400c0d44501d1051a424591240c20000b44054030031810400a444e07402c12044151098030035030340364031904c0e003182d4680201c1e801c1a041500c0054201c0c00c04102a1000d100316058 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 502229523 1250 502228273 502228289
    0x6020309150c281a070203071b15020a03142106010909020415090503010509031b25091508061306020705191401020a090e0405160906060215040c06050c03070c 70
    0x250380060402a012030644134207250442d03220b40410103000d03404010b031559180d03c0000c20040020801309011012001d03002080090103115042c5241034001568011451190f1a042401c02003003904c800300d0f004106030301201c14003c45544a04503a20360200ba0f0207501410300f1035055890720030700f00803038001307070041040d4520b44028181280d0b007000d00b8400038402103000340410b29003100c0c00758980c09445003843d00021a02200b0482c81002d101049250642901081d6940380a840f002c402c41d2583c42000d10701480c022000845c50b01d0400036100f902c4840d030080c8100d4a41c81d44989018108200a03140c03143d00340042c0001800501103820505000701c07262151320b07030b82d00300500c145441c04000c0c500c7e60710402a20a107650080e903820100e40390704d818507485030b40d00e003442802c20303c90b044001908808502c01240700100e95004509641686d82100e0b8801c03088142c24030480000d5501601c90199030404204e07007403045006081c0361040070103403410009242c0c1d030800c140b8069004140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 502230773 1250 502229523 502229593
    0x90c071401050a1a030106050d24050709050a050909060711010b1504030b010e010e060103020306010e13050726060607030c21080c04060e0904050c031b03010606020309150c 76
    0x10100e81d01807100340d13918201301e00810420b0701c1d003400039880d0b00712402e005010b0446541001c5030742032034814214000e15114401c2c441880e1841000f000c005980c064140b01e82620355000c222800e206040c144038040800042c02c0c1612055025034499a1082003005150340303400c00843c10781c5070200c0e21144601014400ca80715070079850020542d1505030000365800300d140004102d00e0b441884160382180302030a00680d00d8a0790f60040710500381580e941901304d80861001282190030764086031190701c150b6180b61000305c221504071596014a881c80072060588004074050385418402031009078400d0914107100d0419654a1018035031100c00300108130601d401c405025a081021180c0c803000090302e0901c2c26003450006081607280300085c078003035180000040c5c00c1200c200610a0720040080480746d00750210301802c540607c24200040c001e508090f00002c0c00c80c00003003655440741c0010003204100d6403d4942c40440d8000d203640c000913203e5a00318458030742140a0f003452414030214000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 502232023 1250 502230773 502230791
    0xf0a09060e0109020a120903121823210d060b0301090e070308070303020307030e03030a1a1915090e0a05060f01090e01180b1203030601020708010b090c071401050a 72
    0x19001d030050788030000345801006402e661503480440d0000394882e1807030000d10510705060840b100c0e010302c3c1580f4040d80c0f40940030b401c40d03070540852040705071240025689640c0b44081c4104900342c0e102c45600aa400361030011003540c181c080b9180d14201004003d401c0c4032101c5540c0042c0c694a0388882c505182c004014410f951550282d0388080c50818010a0001e165682d043c04602c0303000c101074100369000c0082030b02c480c860b802c00cbc4084040d0800302e07516420462064001082a01c005115103044a0884030560a060f5003407518056401e082440140c1342131410070183c0c0c4d07640c10030f0042140142d004200c000c01d202c58240105800c000004052038032100b80082c03004001c0d49c072030500003030701c0341080010680c5044a0640300954a420030041600c0e6000e40a41520610940e00400700c01c03c4180200f40040034502c1004240e084561940d5140c022071700f01c500c004295500290028000ba40c00d081480c02000d00301d00c920f003502c04404a40c024142126000c1e03810600d15501d1340c00b05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 502233273 1250 502232023 502232039
    0x3090303091a04140105130906180b092d070807090603090c050f0d0501060e100b0c030702060a120c02101b020705040e03120705090306011d04110f0a0906 68
    0x8540604148840c0030184590701695500c0360240c3d10910303642c1044c0d4903000100d0391141c415600e1041494440005090319074070310f00003404141c0140f5001d40811050000c48140602903006130070f101410328031880d02c41d50b60454a1080d40070a0484007200e1142c1c002c2140030300400c0718850941c40e80d03003041c50305082c40006c00340c9040758040020581010942800f14680b950580102e0b01c080ba0701c030b41310129080101e81400080000501194640200040c42c2c3ca03c642006100d0848442143c0c2c1107612000109854021810f00c003e40340d10501c140c05c01400c000000f070040300480e080000c0190b608003100000c0d511580031480050308805043c91003060300e07016010810f001103404019108803200700955070403403807203030520654541048d001058810b00444a0b80b84030491069158500384802802d2548400c0809009201e4100001295500514407100a0313809040010a40d01c594072910050a010900f403a440800c500360402150b48116029008242110012900b02c0c509111 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 502234523 1250 502233273 502233287
    0x206160215030103150f0207030203030732030a060914010b0307200c01030b040515130207060507091814150301060801020c0a141b060c03040f23010c021e040b040903090303 76
    0x4060101b42c01031080d100003980100640754060070a240103081c40a069400c040900061818011019040c2c0f41307001c3c0d02c400b001e008521031410700324280300700d681e2203515400b02c0d4500071490303d61041e450014841c500f01d240c000c54202c561841c2c10030481b24031070b420b10003840406901001c1988402c1c00c0c2c401558040c02015241c9008650410140c41c1850880350380c0441c0545041c451203980c105804c9a5603d5810f4603403284e0845010081c91400b54405400c003140c60149000c00089500181112006401082c038400061002080c80343c5580a59000150100c810240d255481d0200803c440710700340b015100038540765000305550788440c01d000314072181c0385104003441e03044410a0100209091000300810006503005039072002c2840380281140140e41000c4180a007101300000c00202d0726114204500e104a0100580882c080040d2050030000710001d40001c0680c40f0104203500c100114010400d0140001c10200b00a80008044a9802e0000c4000c991604818014191712142c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 502235773 1250 502234523 502234541
    0x30c031204020102010f051504020a050705010218120f0d03050402010e03010e011d01020702030d111504030507020a1409040311030c07090203010f080703030e09060414131b03020616021503010315 86
    0xc100148d06150f604178041031459281c56008540001c0c2c409c81c030305c1c481c1f4121782920b81c000c00215140d0010142400305424948401845003650840b0680b9220010410400c82c1c0150300040425020404081d0080c00c0028416418400340000003440754034280528220141000000240700ba420450031000040d600014030503684148000001a10b001030b50100340174480c203090741ea50407031642040c40c009040e07410800390450346091104050b001005004442d208032402c004803525440303d4403403501c00305805a440030604001c1030200f0700400f041040c0350380300c1c82683c1c0360800f40c135032484c42e01115a00c16400260b00000400c03c404c1c038400c500c0c0c080c2c020314018114140c07540d14000c0c00c0100c402401d5106120070008103125507119400442102c0540d102180e180c41c001c84113800218140340244e0b0020044c51403814482544103090080d25030080846081c02e64980301441001101075040f40c101c800d0407803034244000c2085c003440c001d40c820b0100f8001d4008a04d915030036204100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 502237023 1250 502235773 502235801
    0x6190c0512060d0c030203030a020105010e0a0209100c03052502030705180c030a060f0e0702100522061404120207080c2d0613030303060806010521030c03120402010201 74
    0x1c40400c49010340c680c1c8042d0004800c591803000f40c2c10700e0828840350000f660000398140703c0010b03101409030b010340109040360266812044036665203040201684948a410740d408000c400403800020701401100c10b0040c00707031038803505161203891071140e45880702e4001c0340e04055036039512045190800075071f805860152200074034207103215090003942ca03010780310b000c0da9480030000894070110750f4008401012050045c1c8c00c12599001003510780c60003650141c00602035031881d24400c4d075607405054062600743d160900e07051031020741044800d240c96003c980b880e403503c4030403030354810701044180254003c0c840b6841c0441400400b900c0e0a00342c3d0301090003170700b0150540d50380d9951022000c1c11551660000900c501d0301c5400f900340504006010395202c540469800500340c0302c9480641580c5c42074030104515900d6a0b145070b0b0303920091045951250200380f0f28400005210100e1100342100401c0302c0c1030003094000700e42544c0101c4008851204600200415580e0901400c40014840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 502238273 1250 502237023 502237027
    0x3041d060d05060105061c140720031611041a13271e140c0901080d350f060409260708070606090501172a0306190c05 52
    0x140d502e494582c141441040d12560740400d0300b1071201100c00582c0c0358560104010428002c0e07600149003a020f00343d81d424001081c4030010030003031a0041c00d010700740aa0760300440c03c0c129018078280302c4211000089403509030a41c1051a59181e6001c0c0620f171048040e108500004002d00b07010081c040c01d15900416424120002c68400c1c0030f51800702c54500805030004070841c203040c0089000400d003150f8019105103c524000d02000d804440e401c60f40307640c191290b45440004104044600380030f052103a030003603001c07100a103001d0307203034092403010300702d91912803007040402d0583c1c88407540c0103c25294654801c10524200702d0b019541d1000c01180c0411920713241d515950750b10140c05018140c5942903d1a001894142c1c1068812261344818110303950201c6240c0000980420700c2140083c904000021038010000600c1005400640006020b41241003001c00e030301c80d028051001c401d01c00d0a0000c41c550f00c00f800500d205910000c0749048400c03210f48800105c07908000b0307d008100302 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 502239523 1250 502238273 502238299
    0x609021503041101140f191b0201080f060a05031e070e011202040e0f120415020a03082404020c0c0108090f07090e10020705061005010801030b01030f030c0503041d06 73
    0x6600300c1020002842d05450080c4c030702141201750b21840f08001d8a0201c00300309404008043c1b03510700000c00ba00c2e55107070350346c841881c4041300901c5441c00c020b0200741c01600007940c40b1714010f49a40d010728014644402c1a9595012904105410384026962280542400c0e40300344100020001040c001e102c8501641c50032407401c402a51440e0001d20a544030b81c03160450701000c0081842e03943c201000d4564440300507415013007942c480e10030505461840304004030800c0c001328001c02c107540c00d074664510303a40c0d42c0204091106910001494801c165210b88041d41e00c03148003a00f407400980c1c00914101a82200141020310001d000340e244d50301803110300700e24101c003181c964206c45144101207880051000320f80d00307080c1d0b1140c0ba11b10441c40414000c00344040040d00500030943c00700038034041030302c8400446030a1804d001c0a018000e210004000084d01c200007002001d000380740c8824070342c5050350780c03500f11b5101d64845036024984540e00010103c200c50001e401440c21901440301d094 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 502240773 1250 502239523 502239533
    0x90e010317070312060f0e091b2e080f1311010c0309120c03030f0302090102030a0507082a071e1707080a03031a01020307150b1903060902150304 64
    0xc0d480d41001a0728401050260803d4001c1824190050281e1018490b090700d46208540c2c41d0241e100d05018002172401182c8080c81c04101024034260058610710b50a021101f401041544001ca20b414101064180440720100e00e9603a1003032681983c5102d03540c10160402000d444000c2c0042c07100c02c44540c034a20001d1107100384240f040500317080c1452031304002c0c1400d03075903125654001030381c440b03050000d403003004900c0d40c16000340c1c0c3c0310707443c1c84000c0d0381c0000e000c408074001c00c1d41050269004210a040b0700d80070354003070040c5070320031038290f460890010112201102500020280394205002c03000d60081c0c2404150081c4c4000c4000f070f5130140c0d40c00288800260176125080f4018100440ba1071a02014000c01001e00141000c0301c01807462440e00400800d610045100d1380765441ca0b00b10340c0b075803002c421034211640100b800d10b460070300003041d00014106209900d034411101c1c1c29208003c02d40060705401140900c000142d0341120340140510841c103030412a815000030410080021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 502242023 1250 502240773 502240793
    0x6120c0f010e060706050c070606150e060f0c1e0709020f090f03120c0d031508100c0306150810050d0b07050d0b0904120e0a082a0603040c0303090e0103 67
    0x920303080c02e0350b204080109000c0e120f940e038007604060528041050300d00c1c00a00030301800c0d104140400106a51b052000041c00c1c00303442c0400040c13560100d0150f50b00d070080107852664040c4554130b1500752520220f074030740901c1c41c0c41240141032018a1031900030041c0906001031400501c03d600e81514070704900784902c64076001034407c410f00707041107426440420032526545441d046540da217100703052445d990707001d10400c0c9000283c20450300389403004407503104104403030380f41c4000c109401078074000c500541011207504080581d641070010703c20000d101c042d540486542c8582e0700c103080010b110240310b0459080740d0f000b4906000ca01d80020300d296001644880d00c0e1a10503110305200140740e010300649542709500045800c10300050004810780e407042c0c5c034290380f121110318003440144082416188624411034001c1003103000c601030800c0103111500d83e68107071641c03003a20880c00241705400c01e49043d1040045a02c05100309a0840b16140c0a020ac800451400e9031456a03000b00003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 502243273 1250 502242023 502242049
    0x209270c040b0f0f040e040305030406111c0b0103090210030e070906060c020121110c010e0604050c041a030114010e09121606091722120201050306061b010506120c 72
    0x200300001450213a1504107425200600303a001c840c1c15060030036013402825a0011b54040e6a01480c0642498040070014126075110562820120040500020410040900a032050306064a50401100594505441c100010881d0f20b000850b00e80e915071b880c1c1b03031940541100d40c006241034002e00144e40c00602040286030309282200107480050208554400700003d01c40045050803072201c2d450211001410800c0c406074020801c6007145121790756289029a80a417403a04100300c1c1000324241138103c1000c0f800758140c9850000f001e800420300b11400ea8882c4070400400c0001481a84060342603203401900800040c6a008503031032f00c603070702403180c40d0010355003941d90003000c01001440d410401d00341e50448501c90050f0744880e440b000552004c40404442400e002e01c4ac0402c52040d65140241e412a41c84c00c44807030305a9005487d1540041d09150380003401744030f200428141003280071395482d0500004106401e00301c042c0000701d00b44854407050740d009010011b03510f03210203400341a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 502244523 1250 502243273 502243297
    0x1c110d2306060f1b0c0f0409210e150304050105090f0d03050601110a03090618030c090b011b0f0506070519030504020f030307110a120308190209270c040b 68
    0xd111590207406983d4410950300400011104200000015020070710300b110034403e807025110608440200300454200a00042000903d064045e03109042c0d040c400f02049190b01740743c104e841420b400544402d1603030140c4071100600000708400c2190a001e2540c00c000703908010003409101001d0300c3c0d141d01c003040145082540d82d60014407603a2290310b00c0b0f00620120820307034007003194500b00200141081e008020204a06099041000140518030401c44e900010419449410908118007030302c4011280341c104100c04000310004200800381820b0a881041001e46605e9641741603420208014a118107114050003004c00e082500c01007a24140841d24001489076118800200c41000d071a51480d0548408142001002a19802074920003070450300c1900c501d83c0c584407840c1c5100781c510003d00040013040820a44100d04850315400500c40307001600742030b00000810716006034000212840351103000c01040e090000510142c011902080e442c1ca41820030000701103030f109031141c04003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 502245773 1250 502244523 502244527
    0x50f010204060c031b0b0f0906090d090528120b061c0209090a0602030c0a08180309060a0e0405250f0801050d02040e031b0d170c1c110d230606 63
    0x1915140c0108845c00a55000310031041908013600c00d00002442211082c0346846441c0116001040c005034280c04203ea550310000d0080c102410f2101c0050603042e48600480514180c040840001408102030400742400c01e07070701c25640c00c1c90100c0030f20103009140500705400040c0c20140d2410f00c0d001c18190140d450345003d4480ca01c0302072a0074513202016105034030202c28890f05440d40300041400300704603502c00c000d5441e44801001d80030520041040164020004c1c001a0300700503000e0b22002845d03062100c0e2480c030607000f060070340b081214000c0e03094400400802e6a940182c81500c44803a0615103414a1344c198140500740742c4040c007500e031040c8581c0c07407618110364031a0490b60500403900181e90f140c00403200f2808488200c0811010980100713200103601c98828159a0500700a140664006841c1c0211000182c0c1c40b40c2c4005d40440c003003075401e0200991500803501d410071804001c5035181011480c1008581402d403120801824290b4100c980c1700c40c454115820501c1121480c0e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 502247023 1250 502245773 502245797
    0x15030c030a020c150703020301060e0f0618030f0d0f0314091f0e0a06091403070309050402130b1306030b06040308040b031806010b0c010c080105010f2a0f050f010204060c03 76
    0x60300d0090103c0c0c2201c413045240c02000340c00c640c0b54000e581201c01c1e58a03070303018000107041040286030507080c0d2280c00240601901d0003a00109203251122100a4140c450b8a0704d8890044c0c10700711007189240200d404601d40c008000c0d494441c074095100780e103880344000d040c00d410054440c0034216038000800c0c0040340951a81c1d20550082c0c0d80340e0800310403101885a2440e154010308100107080c0c4e2109450800f40c424134401000302c408a0350316a40d58070015062504020003508084c90310040c0080590002c2880c802d454000c0600d80301441448008078a081d6000b403d40307420b84640b81c010f0700e00b84010400076544030b0a42d000d0f40c0c00565015141e5880003503c4012a0103092440900e00c90b5400016041b0b4015000344000c0306250000d000c02c50384124103581e0b0850038490a800114448070701e0040c54885d90342d0301640a0b83c0b17585810110300c003001600c2916100c0310241c2d801c54440346c0303503401c00004000c101c601043c500c00079410700d0301d8400083d110b00303010b4070054240300d28a5848 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 502248273 1250 502247023 502247047
    0x8040804120b0103060c0f0206040f0c182a02030702280605030906092406040e100605120105280204030204050412031d1c090e04030e15030c030a02 65
    0x51000750950600c5441021558100321207044000e1009a5205180c801280f442c98031845e14030020b240603070020184c40c0c80c0c56444043c03004e030003d000e4511543c03054020a1580c1104948229002d4100c0c010903110341380d5010480790b44034120300000c101003003001007410703a4006c0240d0b6005501101e54501072101c44200001781e9070400c4900070f003100070b03100100710507801401450181160f20308842d100e41d40c01c48003075a110324210040d60710087d141d440402110b60042280c0d40b01c2d6000c0e0021031501c0f088904a4604001104c0181c500340c3c55010500040c11b082a52507a11094680240450b040c000c0e0074403400003182c2c403201d03400304528004000c0b201040e01268019980070308100294038090070465010170421008400190070000110b1145c50301580c40404205e1000150168400c3d038902c803440c08140d40c0d0f5403818400081d000040c070001410342603100710301036211a500d0f2012201081a059154598001c0500040c01030110306003a1505880d400381f14400b0069a6503890300300d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 502249523 1250 502248273 502248277
    0xe041a07081807151d0406030b01080d0e06030a022104120f090e0a050717010f050f091605030603010b090408210f0103021011031b070504060506251202030307090501030b10080408 79
    0x7031b0300581400400410401c081e00828100c0f4085002d80b9180e0014070401c5440c102e04241995000e04180302044110708154000c04c41d020001ca46000b5400340c8003009500040220350561b2941103c0d0b050003444c540005181100c0c240a207800c040c201d042540c16042884050f2200700c41e1a542c0c0c0004650ba4044c0c1245002119100c101070400c0d85e40390901300e13030342d40c1ca4003489004100c491405d100c903003071080820b4002e80c08145158681a14840102d0710368200520080d85076403680710490344c6440303400c00300d40210700900b50f45954a9940010054402011101c203104c90800d01c108030910b11074000042c150313581240c0c40d09000a071a5021601802c5610740032003940400101040495941d440d844030080c1020309030b071051940c40d4104411250036206664100208114240d0704048520070346a400c40100c034450213808850311032a1126441a0410015074400410700408540060140c4002c150920b01480043e85840104080f420861b8945060000480c042000c102c42441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 502250773 1250 502249523 502249577
    0xf030f090a0f050c0102010606110c010c02010513090605090903031003030f031d0d090b0903070311060d020a020a060501051e0108091f1d070308040e041a0708180715 73
    0x1d1020391481d8144242c4801141c904680950310702000007031098064900d0036072b03440b600305c0a40001c2c40ca8000554007804480c00072810840d08004429409968000000103440190030004d415400c15091003400c880103032042d82190f20074010020844204034036030f02580d07494079229420302650641900507043c01a204134800d580041180701d50b04001032188202c075074135070719020440c2d50744d42c0303511091140040c041d41503048400140042043c3e14074109000001520041c40c040da0607001c40102c2c0c01800d4241c00507084014040d081c800140942e0303000d0041216501c03400642c50b1140561104142c0c10706040c403066000080c2844c3c0c00b48003900e040d40e00314140a05440320078480000504407803079403203100c60f0036410030310400c0070015000d001d50798090b220900d02400d03c3c11941700030000510440c0c1226400008025844003103080c2400740030aa00c030403950b414070480784008a580076800c20070607480440100220010300301d6803200342c45141040704508440060041554890311 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 502252023 1250 502250773 502250783
    0x5010335040e1f03170f040506031617070e04050606070f1209230607170430120807030b030a050a0506091204030209070903200f01050f030f090a 64
    0x108000482e0101400d03003c0c07083d0282410391000064071004100d1501a40c0005400008410031000f080c18010005150002e2184242d90034280d075980001e00b940c1c401c443d440c0038031903501c1201492079000203034841821342c030281102081c80c04040092180c8062186140300340c1d00c0e28003041c510f80b10ba80450303401580002e101a02c0058130b0901e00c202488e65154075000407000400012103001800000c0088188070010080c0b42401d0420460380f50440c0005680c51142894440c01c0031940702c00810081102a204882c00d4400002949404141c030186401400c82048404c0c006002d080034180040d02034103240301e41c2c1d03c940da012801880d0202107103800d4400c1041300390030310400003803220003207204500b29106a070f1036151a90315490b44014144140c0c009010500051034061100baa0005851500e185d24a0340c03a11130080c104030406020710b410045624641845c03c01030000c41c041082820040d01e41034240d0417403151488010300c074040915203100890310040e000e100741400300b5000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 502253273 1250 502252023 502252027
    0x4020a150305011a070201020604020906220e0c100e1912050105060906180103170d09030c0204050a020310030204020708040504021c05101212091a0705010f05010335 73
    0x280c0000d00241020302402c5500c919906683d40c1180302c040c02c40b41111342c180e014101c503031035030f509108821501034002c80d404203100c1c4e418071801d20085004211080c2020010070700364682d40e816400c1182d1b11400d00e0190509600810181d9004540e03010440300070f4801c910f006800145a207101407068200000c1e060340c07007454006112054000d14080c171406ca0300a00151600740401c018800400b051841c4040c60400400c0482c0d502c0c0c02e00000c1000120005103441c40c0712440310200e5441580c1140807400c00f40e402419410b1034800d0396809080040c0840c030751f09004854030f9a03a0752621009219980019020b410400e00720305072801400050010b6464540c0c9148130b2005200004450011b2407074040001d042e801d01c98455000c56034010300b080d00d0f000c116140c808240c0841206101840100440028200220315050501e00c15202901d51201103903d811404d4030b981200184102d8100300c010300100700c002d0440490400b500000a920410550030740210f2111011001402c440c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 502254523 1250 502253273 502253309
    0xf06010e04091514090705090c07060b19030312110405061605030f190807050d0e01180503040602151501210203090a020f0301181403090607061a2704020a 68
    0x16030402c0b961340410710007004084d41c48540c1c0c0b6540340d00b140b0590340d1115080c408a680070242e280180040c60040300080768221017440401c034040d0881d002c0d62080030549800b0028540e12000035040c48002c450144645219003c8560507402207019240c49400000b40c0c0000490542c045400c207150b00c40150307502c8000c0c103c0c40e81c3e550b400078904901d0007a0780507444082c5c60303c5800304922070741d01074072040c1c10601c800381524000c1c00ca6103603280b815961000700300d00c401f40c0c0020400c10244618019542d680c100b01d4020306150294601d4100d003c42081071000c0340c1c0942c55014451070003842d1010714030000e00032048400e958900d4200407240300006204004402144142e100ca00a543d09c0c1c02c1e11007600c05041c02c81b4503801745500c00d404110326032000140d08a040000c2480e155080300e090100200001e181580039201c1110410369840c2405240c40303846814031940b6104455448456002c0c510f44038018842e03100300c503038145d0010001421035440020305409006ca003c010b17001c001c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 502255773 1250 502254523 502254563
    0x20705190e0c131505040b0d141602070812040b0d1107050d03110a081f17160e0103020915150a11070b16031b0206220b030f06010e0409 60
    0x404400c0302200000b403d48007240751050201307900c2000006942e20b500d01403614162103030303a0f00a081507400058031a250498000000d08119008403003a81010002a02298019180c100240e10079007041e04083e0307071795007002844402da80444282092442d80c60041480b800c0081c00b000c502900c0840780411190300340200040c2c0c02a00b650b040c1c5003081116010700300d17a1602e0040070188000540000b0000b002e0309401c880d0040001c41c0b00b440c1d0103090b61250900c0500d05116180d08001d0752200b4014050020f0701ea029000a1100000c66103040d415900820708400c4001d02042c2819008158488162640c0d00302d241c06140484415403110700c500c1009003074a6418404a0252050070301c003080801a0b03608560341c2030710002d036510313400300556020340d813502c04064010030b144582c04001c805a2501802092440c0c48002d00540060b540107034845440029001f0098091080c41080303c101150b03c07407160800401d0a00c3ea10310340e190310000d0050300018070024496030b00c950100070014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 502257023 1250 502255773 502255777
    0x6031f051f06020d11030316030e0a0b071101180317040f2f0406141002010228110a022103090307060e0a05060c06010902030c12040c0504051501020705190e0c 70
    0x4c505039035251140515414030700e039640416108122882460070385c00c20400e01aa00081c01e02c44150181c80d0342c141213803902440b00004450200100c2c1d80c121090300c120400780300e100d03922000003085c1c40010f811514020300310100a0004101858043e020606004c00d2a9902c000a5444074240d0742d803414401c5000801c010807171169000781380b0101544414031306030290b8400c0c0c4400303800b10b103000c0061008019691707100803a120706555081060a8081c01030181c0000c41c0054a1b40c00b03400c00321a000c3c0280301814580c4850040c0c3c106a002100581e51074003040e620010008110260741201d104081c00c5204255040380d0500c54420000b5403540c01c0714120034010400c0310381c4041c01742d85a0500c812442408030041994120350014000c0c820030382c0c040c54001c0f8000e003101e400e01d0086540100c18034416901902e180102d0304080240340343c54064540c3c801090061006c2030055000041d6983c07016024007441a0b40481c500081c141c215482c42c0010030780705242212604005001d01c00d0744d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 502258273 1250 502257023 502257043
    0x30c0d0c030f020a050a06050a15081b0108011d0403030209061209010c0f0203030f0a0b0d0c050328061e0f05011502030c071205010f0608030d0506031f051f0602 71
    0x100703041461590806002180a40040313170490090318103400c0681d00d9200524008041c8039199aa510b00380314215103400c0c60340050112070008044c0441c44101000c0e8100100d51014100120f0200503c6100072011100c3c400041c2c00d240e40400d603c030703850305030007a01412074195041000450640601c04403801305501801d0540c0080041417880c20303007164114042020103026030f000300049856080d1108009520103040796000516a145c08000341a4207225101901c01609004060085140600030260500081444807080645410920011803000300e00503005644e038240d9203500d407031032006030040c01d0360540c0200f03d00318031001c0040013040d00703004552070380140c0c610b10100140000b003100c0f02c1150700e0000300281443d06203e8202e480c1009411038280d5200c40c0c080d00750040fd0300a0001808001c009151106e8904400c141281c2d0000c20491083d440901348042d81c40c4004004c1440003d1460b01080980c1e4468040e8200001c04d1200381c80b000c803400f4009248c2d40e01103141011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 502259523 1250 502258273 502258277
    0x2a05160f081b1902090a230a1506122d02130b07390303050c0c0f0f011b050f030a0f030207050d110109140303011404060305070512030c0d0c03 63
    0x1911404169500c018000340d1400c030407078514010004d4503110420076400510400b01281c082080c070100740b07100d544da039407012040140300309205105490380070700d031402c60740c0c0e00900d0201442c1010051405e44480040d00c51150b8440e000b8900e900b104441c80b1724203c0200c00b0001c827650701d0a11400a5001c00c40140580c1c14200001c1a820005403c8440c55600300310804030700d079113003402c0c50444200580c07600d01100d1a001c840c41032410030810040158001d4460a480d0300703040d5140c03400e2a104914040c0303c2c1d0400c60403000543c2c5c0f42c44600564810a103051a030f054020355070480340b0302d1f05d6080078109120345468020b0140002008045222055503011203907160584164240d00031100010001d40020b910300c030b6914412592081d04801c110b0001c40c050001d500c8203e501402c0b15507006080c0c100100622041a0740800080700316015101003082130304e1074507220b840300c026002e502c2c0710b1091645500130200c020020340d11a40b40750760a07039041401085c4060402d4107144c0302100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 502260773 1250 502259523 502259557
    0x13230408041a0f030408250b040605070f0903060b010203040302130b041d07030605060f0d0b060a06020d171803041517061e0102010e0f0a02042a05160f08 68
    0x82c500d50400280d81c2e40854480109040d5202d955402569030445250400001594802c3d04c040411106003481030b6401440c41000600b010705041e001e48600411100c1031000c4111103146569000e581e060450340c1111001444580280040b410b5100d5940069400002d941c40407000e240907074424121420110380401040030fa20015508070884451011b035a904140420400706a42da0000c55000030010600c801c01c1c0c2605001519441d01413405941010908040000328280a8a01d01c06080c190004081c110a0880e0017400030f030307a20f41000c1c44076108602144140c400204065a8400000c058945413034441007102e602e154461380c108001160b00b120840240c1031140b20718003400c0b001d0b095081800c3c082c0c2030062840420004541190350311116031000c0c800902c11145070301002009049030807098010001a00d000418a018246280728a80488656440b500542c03c606042403510741580484007140700300040400b4002c510200c18050402010b50b0080c1402e03002084105 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 502262023 1250 502260773 502260809
    0xe150901140603100915180b0a110a0c0c0506070311160f0308090d02030f010902030c060c0a1b0306050a0608210f090f040c080603070806061323040804 67
    0x1070180c1030654001d42c15070840e50380d401c000600f030340010030b03140c3c01074215100e942d45001e14001140d54503070038244140c84110350502082040341d0841e0b00700004040500c5401503100c214a00c91055681c00380522955030103440030401d000b0703480c800a010052000b6207410140c00e01a05101c08a02200518028001a0200030380007130040000c1d00e049003005a10380382181d03a4071003da0300c8000d00c203074400e8100e811000140d508000c00d00c502259000081503003403243c4107152600400e00b80b198428071041c024100f4200380000d0b0f0800440e04480e04103e0f01855038056140301c1c0c3c81b82c01c00f406940c20141003009022880d0880b600300c84c10f8200b101c0750194180760021601c40c1705d5044c010007001c1000519514021800a010140300c001c0800a0418212001404603000501803e021408100800002d850180102c100400c1c098002e440d49203002400180100c00d8004216001e907034a8180c90706170034070110789060302000440c849156060600300015160064801e100d0405200c01070740d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 502263273 1250 502262023 502262051
    0x2030408031f0605030106030e0c030703050d090603050f060f01120203040b040308010b03100e06130510090b09010602150403031b0e0a0602030a0c02060703052b050709080303060d03030e150901 85
    0x1c81d00711140f59907202d0640e420118101d01404050001c004e140c8540e1100c2001660700b400901e00551044c4010072015a0410300540100d8241d400300d411b1614250411031103c00000303005501190403611001b00700518001a60316000b00c12003011503a10100c100010011902800d038001e078003039140c455007681d035100200c5440c801150b0801c801d8690300760030000321451203102500f04000822031402d481c4404001021107200312074641c40355441d040c040000b14805c1c81841c14522f8240c0c0c0d10039441d810131310302a668603920300402e240704900000180606128ae407060b008881001c03800103018001d00d800500c0304940380b00c114460b5420356000640140000111074803025642c03208038601801d82c08110064010020517000d00c0320401c5100519541003008180d800a1199000d035072448010200701100c1000703051000703000303113a0020702091500005499008104840d40c5800c01e10314078044025040300c41410242d4442c0500c2e5030701c044001ea0845102e10240c80082012078560611 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 502264523 1250 502263273 502263331
    0x8070203210310050d020f090c09060c07140613061202040302060d0516260c0d0c05030a0e0a0816230c03060604090209010e0a0e030f07030f08060108010b0c0f010203040803 76
    0x95101c2811047d219a0381090f07019958030021000103e130500071050003040d46075004070f0b000400d5400404051210418910b481201030400341c40301400d100114070b140c40465000c0c0241c10500c41c08401c2a800680d45404940146a024210544501000d0345400250000f9102080000e80700c2084c0c4594130721650000940c188484407d0021501411144280c00e20140050740310010400440c05221080e020f40101d211565440681d285480c41a220842e000038107003403801e0f040080303505d0128944a090324032a42004a4081604940e0301d02500d207503c0c01c1791484811200d0300d070210394614012921881c2c110701903083d103459a44010400c0216880560001c0d88020004014021107481360329035544529480d90018201410030803052440d00180c007241e40500000841e8001c059100e480d1440b03058542c00c2620741414000006091a18140107030024400049803240d0000700801810f000000510001c544d241001d0030410000d50049071f005502e413444440d08084c181009032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 502265773 1250 502264523 502264549
    0x90c05040513050d050a051b1608010e07150309020306072102030103080301030f0c080a0c06090e1b090102010902180108070509151e06160606060f0207030807020321031005 76
    0x130f8520001101c0302610a40c001c13201410030840140301884000b10420490700c0d121940200400c1c0341e1030403000f07681c140da915070424102039042400700842890002803401c161075015440950090305804214000c0111141c0a981446118180502d10350082c420400340101030686410b4260141550001c1c0d00c02840b0041c1160300400041000c940354404042025100b2150700720215660206240707088842d0a0a440207a00c0741c0c3c00b00302c00d82c1c02c00c4100e0001d1500307212203440c80c980070210100c0792a40d800c0859070341c40d000910740030340c1c0e10079071200c017481d0360042c40c1001000c00e07130140a41d5600240101e500324803138904003080364030f00f81141c1441030350a441c4e19015034080303400703002031001e40d40c1d4064800c6025816040c07450350381d4400b0344040c220f4030542d0561440b0f10305005c0300303840c0c003540188140a41c414050112690118140d001c1d00d400c00345440d502c81403440440d00c1c001d40e03145c1446248141c001103685440c01c58004501400545200c01c9107a51903a00b0024011490301d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 502267023 1250 502265773 502265783
    0x114060d02180d050609061e041401020d020f0d0f090c030f050a060204030f06050a0b150f12131203050114102007030201202a04090c05040513 63
    0x1010340c0c01041900d400400070500d15200104082031000041140492021030460b40c03034002c101041060320003000315541c00111000031510340c05034049140103d0501802c00780c4803e601d01451a00d0010035012a55030100e81c81045546442004c81004150442c0c41e1400301e00781071050280c4049114018200c0036900003030798950a504d182e8841032000105241100e0501822032200d01085c2e8a00c06030000b18000d0940104e00c00b414641207084802c02003025480501e468010800e9899071941005142d01d01801569030350340c80c10201c103560043c8009110014240010002410320b60007980081c54841d800c14448090511300507030036181c0c240207401d80e0507005418410146400d001010250700359003015419028111002910382018030710400305035106200400031035902141c1c1c40340e040c4000b0440d40410128200194681e12060400d0680d0b030005402403108c0e04000310920000c0c84010001c201400d03443c500013041c00c50501c5528030461070413000501c01e1001e8500d0b085165404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 502268273 1250 502267023 502267027
    0x3030a0e06071109070f03050f070f052d04050a0801050105060f0702040b0409060e12031306050601110a0c06030f0b030703020402030c09040f14520e09011406 70
    0xe40d050144a400c40d001c25680c0c1d008a50400b89542c4500d03034602c3c000d03a0709541e0500c42400801004e4150390026110005116203442048040c66000003500c21003c09450090740e03601e409400400c0001c441800c00d0b40c00394140544a4402080400401c11076106940619030155100501c608859091181940000c41084802204d000c044010124240700900008194204a011a0440311074030811108683c0e500300200811800700420840c402c51004540d00d14500b042c80e400402c0d4000c14000c292035180c10218000ba0b003e00200b5440a8248080740c1c0d0404089c1080100d101a51140c0d40c00b01303251100c0328000055500400d81e05140140090100740d10f10f5090200a5000904404000500744071580c03095031a40100250028000380c003289212081c0050b01264401604404c10741207900c400c24000c9021161780c07a50440e41800300510520f44400051100c1003240d0310845030000184125a04c640010b8007484003402514545096038a4040b52032292a107180129800301003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 502269523 1250 502268273 502268297
    0xf09040e15090616050a1101141807050a1a091c0c0f0302010e0904030210090f200d0f0c031514010509310c060f0806040908160512040f1403030a 64
    0x43c00090507480c0740c1f40f03000406031009221107421036050700c11f81c0b2500f08903801404140210619405440c000b5a40a4004649040d000848050b180e115400c44111040c410f14841c507020000d4450424020b003032008501c034104041c1e0001da0180008641c00c000c00d05001c10800ba08080410599a041e1140c00e030001c4081c08100c000140200101c086115a601c5402801c005002d602074203842a250081d600c43c10785010308140c1d03a400300380c0c030f0510600324160070741c0e5032801c281e03038905900304e44000366110140c1881c20041e005600007400011100600340030308002036201040c11581c007c1448034590f02d903020030482000c240c40d580d2a1001d542c0340c003200d0b10050f01c1180d240304a04440c4110441356580d03058040b521691191700030852000c0781281480c7c1008400d40d01c00821917040000d02207036503540e000d901070040704044100b03130b0350351103020401c04101003840f844e449490b840d11950340e100094070070305040c0110001901c0482e21038000341000003e44d10001855111545200d031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 502270773 1250 502269523 502269527
    0x14010903121e1805250510050c0601030b011503060602100f0b0901031a0c07020303072009090c03070909020f1504120b0106111b060f09040e15090616 66
    0x7a107032040b640782d64241c1c031642442407058403240c0c000080454150075041c1042802c02e690128100d0080c02c00d0320190b90450344851400042c2c0703008480710621454051030071985ca00514842ca8618400d079400401441125400941202d41c102c000214401c442d42085007943d42074070501d80568011550301020307003140d402900703554071803507030014025040380c1c002405903c0a03401583c041c1440c3e140d15603500440c1c80155400355030110300520300782007980400d58920074580003500c43c5404400000682860072801c6201640080c00f20364142000802e482d01c0d40d00c413081c12031082c070400100141180b200d00a40700e05e40c2d001880c50700464050020701a54180320003442e00001d01c1080f000c11a42040c0286150050040662400641c10003070090404000000c840400d0382c047c0800380003070f01201d128a4042d62041c0d80700d6440e0154442450b0290003007550b40b6074000d05000c01c3c0c982e100000140728030802c000c048417401e151111074209480302c206884540c2d0380310031980090703400b44c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 502272023 1250 502270773 502270781
    0x2030c12090d02060412060b09160f030228031a0a0b07170c03030703050c040509180c0315041b0b040e04051c1d01050a09060c06060f030f1401090312 66
    0x1207070240800b030680c80583e000070110303030050b0001c115561421181501380441c5224565004205982d68030302404c20114030761760007210700881c00030050058101c1c80306e203202e60141c5a10120550b26007180004514014420407049641d00001a103024603000e14515504420401d520001d04140f01403401e007900c203840c5074015903042d00c64058500000320840040e0005241400e812009183c40e810050070040594101a0070740c40410b41c10300050040d65650415240c008c000103c510144e05200d4089604020407980420303814002e6082c030881d4510104801ca01c201d21400e049217556803101445107200d00c07180180c40840300103100600041c131007402aa40c009000c1c900b12064003211400c808900b94040754030038001903401070308284003003413071041038010b00d82401d0032402c11520303a00c003c000c0040d45c852041009014250141030003d0f41d40498083c25054004400c02e5842c0c0c1001c801345611071000315014034400891540421040c0f05175035001c1d9066039900c081c1e141c04187e10001c1c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 502273273 1250 502272023 502272037
    0x14030f090d17041206050c0304080a031d0f0714120c130b090a0c030c110d0e0d060e0309030d02150a09022d030d02012c0307120c020a0602030c12 64
    0x2104101d100681070103420800382c00200700c00c1380745401c443d0144c6808015104043c2011901ca0414007d1000145840060303035020310480c0780000d101d000c1c40090030707806803441e0341c254058000c01681c0301c0040400f25021050b1400d0850042c59140c0d9102032244903000c180204c00c182c0c010511040283c03818440b00d03075041074800d502094034000c0100243c1c0019003542c3d00300c003469440d800406000d8042c000c01580f1005405d1036210407060184040c2c4501403030f01c2e00003c02204184085c440e607a101c3c000d00130b0b20341160040050f4245500c00c5540c0f40c3c04924624800d10a4107680100a880011650000c40d4034541c910034545400901401a0805010887c0d01075550584200148500000543d070450406020131074451494203050426104034005021a4106040305c00c5c08181a14864440e43c01d0303008101100103012a9241180a9290000e11424840340403400c4a0360120140c213449000b1182c15182941c1c924080e1b03507902c5803109002040e00116180040948290040c3c501c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 502274523 1250 502273273 502273283
    0x100e07030b0109110f0f09040e0307020d0204020a09030b090f0609070b04060e010e120c0913020303190309021008010e070c030f0809100c05071a0103051023040f14030f090d 76
    0x1410902101c007107086c1c1204e8290703854000085140052460103014070001024160046d620b0312a554000c20f21000c0c04440c064000d640004c1c80310035451051912200443d0003c1c0311405900b0f0045a083e100c00070b2034000407003840341602107500040003241d00e070300b100d404050f054641032516005507251401e83e42c16606000420900940b07540701d00d81c3d000503005140002e031000c400f1640402c4000c6402400c0c0500d440e40300a025001070710000101e42048803041d04010a104605100720058078010328001d401c07841502e0b0004c0c07015000b40a2506941c400100e00040d9a200c82c0304480c80918010b0140004042c00c90001c0260b004200d40d58000461505039800303d90885c1d03002e0305884042c40048005180001d50009202144e9803030181030411400410031035255032580b03a511914104194a000d81d1401c552004190f035500310705800250320114003980c505401e1419840e030b001502581c100701400c0500c01004004003c41d0300d12030b0080010b500307000241c420b0000d8403540ca102160 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 502275773 1250 502274523 502274527
    0x901140a240315050f090a0f0206130b070c0803090604170f1b010206100311060a0c121d030a02090106110106090e060603101103010506031f08100e07030b010911 71
    0x640300100340c0184000e503009241c03c01e040301c1c0d011811001c440e4024120b505000380c1c8003d01c50281e0f00402c01e800c10303076001140e41904c2d82c41400000c0380d911845c1281c00030310300c10100011780020071401070310039a40a06450241c1a07500c205403522072091240c05030303001c4805c10003807088419841400c0100c5002c0070031501109044030b0032034030f170500344112041029403860b100101581e0420a25500003201c0520041140c0740d599680c1f561603403d560b1500c0380c1c60100e600905144940d00c46804980c00c0b407011808083e0109000d030190086e90404d0340500725580c814203583c02e000030000c400ba64041c0c0700302e215070704e05482260b00082c1c040d13084109540700c0000107914207050040c1c8a990b80c421010308aa0309040342058505201d03104400340175070418503040c1e580003050054a04581b404d41d0700c180d680d43c80da0030b04400301c1111803001d02c040f81c40380c03004604944009501c8030a0072820008000404600030820354030034040c84020a030040c11001405880c8982d00600d03424008003203418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 502277023 1250 502275773 502275821
    0x2070614070e15250c3308071202070807030f03021e0307110a3002061b09031f0609060e0a0b030114070804050709020405240c01060902070b0901140a 66
    0x103120710100310f400d0350b00d81020368060217401c0c0f500c2006e010013620b41d48002010360f5140080302900051020300310034001c0c11000202c42900450b28a190051600c40441d0746030340d589400003184d000032005400050b000e0000e262444c3c040d02c202c83d2014900d8918507405912100e1190b0305501c0100b410041050a000144420008010300a81c140c42810a40f22140005026031404404940302c200202c1c002088106483d4012502c41e402c100414400b21008645a102e03008505c143d81d003807505441036200c04500d070007030f0b2a00444120403900050210710740e2003402c48103071640b501406490030707100804510011682d41c0150b00103003001c1c00202d6141400b140380500d106044500350081481c0314100401c0000c01d000071401307003007030300021400d040c10b107800b041c08103160081000302e00e80340020420000d03072440142d88001e07001c07034000d0040680f540703d48006500802000c80e0b500c000300e00400d05094060040408420307510483c2840c0380e54001c00e40020300075071800030b00072680000c815 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 502278273 1250 502277023 502277077
    0x10e0106122705010207060b0f060a030b03030702060406020c0108090c030309192402190b0610030608070b0414090106020a0213020f0d0b090a0902030303010b0a090902070614070e15 80
    0xd80c160b030302600006844100d0350400c0000d894100080c14415104500902581d541d00b109235081d001203032800041c454407401c007082c607500c00ea0030060351220b00030034000360a035070020f0380b404000000c0e605c1d240c0d962200c1400d1030365210034400391581a0801c1c01001150700f00700344050241c00c075220319400301039940c484503648440308115440503054140004512036404008151403101888103544e0000300d1900c1c1c1b5880282c000d007030180304441d8450520030581c8680c00040140c5450402c0e50034080d40e86254031100e40c040e02c9209440d90780303548205c0b9186080992181280c000341c01904082c050381c0d0811151805d21043e45130655824800c440481e8403d074040d1011895468000444241010410540c0000182400348181c00c180000c40180c03000f0042d01d04480a01c0c4280b41c454858040036140342c00d0079006208030070b10200d0200180206074101e040310800f0030041080d181c030f540208483c01801c043c0800c0d0045166400010040305a03002003c07070444010320b1400040d04440c40e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 502279523 1250 502278273 502278341
    0x6050d0618060e01061106220b01090b030c010c2303070c090c0305010b1c050601021912080c0427090506070c060f0204031a0402010c020a0b12010e010612 68
    0x541c03120350b48030402c1c80001c600c070700000d014092504101010300800705e14140d64010041900601903031681743c2c3c2c0c0343c00203000b081401341d44d03201c5848007082d80c590b04180d0090003d02c060724424401c01440780c6155018481d400440c3c0c0e0814050031010000000b00c3d05111603062031040030344070400901c1e0104000c03d442c08081c1074680400324401a44800c000c0a0f1481a00314001e0390700100b10722208480e4085c004290b0750100c07000450f03503940740310045c0c0c00e0440743c00c1011001c181d0012136004000220742c800030a404661524500c03501d5174130541c55640a14028410010a030540c41c50080342c8255221202d24260f0802288036002035450074106802901c5100101d015840c0c000104155030003201210511980b0450409103152902c50422401c01c2422a60561000c08503081d644540c0d414640c00741c01030301c00c240e41940d88086103000c0e80109011100503110300c0002c141c00c440c50035064121541e03640d96114041e03024500c0c00082c20550070405044413080050440c034031807202 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 502280773 1250 502279523 502279559
    0x110318120c0c03070501030605010e040f1b0203092112030c19020c011d01020a0f06061a070b130209280509070915030b04141002070b04050f150106050d06 68
    0xc0500050b01c801c0060501d056410340020341410304142042c0680d903404090f440030034800300c0c1c000c40d5009090b20b41c2002460208080c01d03440c000c001c0e44007800b5030004020300108000ba104000705400411028000000d07a0324140f281c0d0700640311040c0e07404d0480300555003220920010b2803a004103a89410850140b8520400150704404003c0e0f6080d030f08038420074003010b0384100306240e060302c0000003501c5a0840d0300003801030b0035803440380f800e2090030f501200c00340c01918218049003030443d4444002d030700b000c1011230b0740002d104000b03480410360101c09808664003401c071114a0301d99101003900c2141303083c0c0f540e041c080c9231624404d0003080c1d4003440c0c0c040c00710130001d854035604191510381564008010482407002c17448040001074040380e44141e209401c1040c0110b2030110755149810007103814141e1401034000700d4150240b05c02100201c0c0a14401c40403104c0350104c801030962909840000880704140342c00041220704e020758010401c40c2e00044001850940307440b01c103a80410050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 502282023 1250 502280773 502280797
    0x8180d030902030d020a0308070c050c0909210a02031c151e09021e0a09092903060f04060c140708070614040c030809040f020304110406060311031812 66
    0x304001c003075041c1803090345598026032000c0c0c0032611254038090140e0702c002c2c10b400300700030030034551a0078400240100700c00050002e02e804058240002405e0356062080000240051031002104001c49200211401d0480c681c0281d420542c1d100e441550308880d0001e01200c0a4544c0072041d842044200143d010745030f102e11000503c103c10310000725024a035003261441c1c520420940021501031401c4600045041841d140d0360b078074814080303481d43c7d0503031301000019040c03803540d0580070030380c05801001d0288298417030030206404080555409080c0d40d0917492103060030128001c1605038100310b123f2601130401c0316050072040c00241203907012010540c0c07041c0001c1740300c40c10803800307000340301c00720034034058409160406455002c404070052100501d81302c1e0002c0d1704c0030340d51269007000004480c104011074076031525017054091400c0b200041482203152a0000c1180786c02031050340030140440c540c05046a41b41600840f083d400b0442000d26441520310f08000b5a074040e00402c4844409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 502283273 1250 502282023 502282031
    0x70506040302010b0301270807140c0114160f020f03150f01050103091a1015050c06070801060e0405060f030d020a0c1d070503131203090506060f060a08180d03 70
    0x7814000c3c215030303104480b240300b40d05040c4807401041020b02061901c4ca50150b581782c42c04410b151404040c0706844004100320343d008026a4060f1000c5460b0003c82020b0300c0e1010710340d4061361600d1031480340351840900d000c070301180000032a07041c8c0d440c2d55140d44050402901080703e00006490300180c100b4000b09604070000300040140c10b01c0e0654010b00086c00c2c103018045c4540c0d80c11120b03a5140d030340d210095210310006904242d55451030002000d5070388801c80b200c04401d000a00d55401080c0514503072050030301160f2071170310402030141200c0300c81c0e1f2007101a0801408200c05000003608681d40300051300500c00e55030f901840448411170441e00280056405850720104e540301c41da0185140b03030101500741000000b01c26800780c0c04600c502d01190380390b403022882d010301d40d1100c50103080f5440059154252a030940d0080090314003c90880700c255a9002c100711980b014a40e949800038400e0080781465802500c1140d003015041408030410624240c400b4a0301c001c00003004006034031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 502284523 1250 502283273 502283281
    0xe072c040f06030201020604080a180e0915010608150d0c09060510050307050f0a1107060206091006050d060c05041a031905060307051c0203030c070614070b2a070506 73
    0x1803185501c0354a40751418030049141d0380001c0d44442000340054102e000000e041c840d103500ca82d43c01340c1503011040171400816141d0702024503101c021a4168414401c2e020049408011440c3c0f96040b0b0300c042c3d40e403440030b940703061059017501130040102d13411000003010b240004400e204042c1c05841065000242c43e0316210820030404c040000c84001e0202c00c10910030700c581c0c002c0456240803400a03131166a20344200046481c10000511300324240600280810610313800b080c5680244c00107001c68204280100040003124002e110361a4030821500c07242c1c00240054008000400e880c0c200242416079801040e0031078054922074281c1c5810010400c004040301c460721b00780e141c040e541e04000f14034081b804650399400d5802418803507048140e024290410b0100d8a4420030790103030643c0c0c6c484c038100300104c0e9030704880d001c1c1401213103020022032000c1c540c481c1a2035040d82c001c40070341035944403596001403042d000c80d401d81e5200c42c0c01d444100d40d001040c4c010003400e44200000c08041c07074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 502285773 1250 502284523 502284529
    0x1202030717180901060f0503100302030a0302010902030601090e0a021912050106060210090b0a0504061e0212091609020904090f0b1f050315060d0f1b0e010b040e072c 73
    0xc41c48145a101c0c43c00b060042c0400f503440200f0381810001c50800d16030360748aa050110301c084440c3d00013507051181100101c101a41034000746500c2d40f082e402c9a1107a40c0380d0089900780c0d0040400d440d020b52080c035040004d40780003030302e1000c940c9421101c840340c161a21900821030b04105010b60f41c03a91900b40420846504003e0040d01610000c410844001c0130740c1c0b1524182c00c0036050441003074071140864107001080c0d000e87c0c1101881034400700b8100784981a1006500103400c03048011499000084800c60301103100c414000103030900d2001030707041c1409000203401c850030351500709541b4540803000500300d0b0480702060307003e0760f400d5a00d0302d2309110810058641324000b17461a000e0060812440d1070024402c1500a503448101e42c00d51f403000082207010340c000c003000d8668a00d0040740d40c140811240200d00c441c041c6000203100a8440030400e440120030320071810201003c000410000803401c00c81e0b90080341900d80008114001e080d4407242c4485035041039054050800342048a02d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 502287023 1250 502285773 502285807
    0x61305061e0403180513060e0604020c030a0507050a020a0f03060507031506260a0c0906140304170910080106180f030b04230606011b0f1202030717 65
    0x2030311190741007209080e6250400000001400040031300421041d4282c800c00c640440c4406003c0203031400d00b084030686000d0025080c648160a0402c0c540b80108425040a00845035202542c000541ca042c0402104481c01c0c0e100c00c1050311680641170340000181d8a010142008141890035803113001e0560030700704201c4c0d102800f01014903281c1005410300c404024020710807940a810300b604d0301701c80c900c603546104840f001c4c00311600c03a000c010011106140e5005014001d00d079517616440ba0303103e640a6800c003545808a00c00c0590a02c0004d00290100d082c081d0b215200c2d683c100d040120301401314103410350a1104801040010005000307440d0301030601303941c801000da07000e6111890041001c080e2000d500000c0c250b0540e240014061040f42c8240c80b042c0380310968540900e4000f00702c5a521040143c56450000300b03400b202c2e10801c1401031101e00e0042e04a4100408101345a8400d01c031400481c3c7e0840039800103001504c0130582420b00d00ca100c9492860803941c51208584800d054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 502288273 1250 502287023 502287031
    0x10218040c09030204110903031308190b0c07020a0504021801020105130f17040f180606030e0c04051510090812030c0d020702041e020912030a0e041d06130506 70
    0x55181c03030303012a04964002c941c50100d0f6010345c0e00160418519209028620810f504140c02d4803001982c648a8019210000202e0f081c410954014a540ba14041e1180c02141130180500c0d070310030003162001c1c106038000e240c4140b00405081186a0b00c4010900782c0e000030415108501101541d000c440d40c080c000c1c00d074440244801d0b08000314455450514445481da40a801500c124000d82c501400d120105d40c0034082c640b00a506030341d680c101ca2a51101000c90300701119090000010703000d80240144441d88450201520080085e802400000d00004040300020240c414000b146600d07048045240c0e94800c2e0780d80c40e409401d06102a282410082090140700405c1003001010001001600c01007442d4600c0903076201d4650001801034166402c0c1c101e107800300b50f00441980500c95008103042c102c02c1d84c40180c1020102c9403552a401441542400f1468400d803842c042d20749a8880d50384040d5100c00d404840d46941c84451900b48122880144404101503a006004003001000c1e44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 502289523 1250 502288273 502288279
    0x415030602030f10080d0e040e070f2103090b1e0f07050c06130618050306010b030a2901030b040906020a030e061f06050901170f06010e010c081204051e010218 70
    0x2601d1408a62651b1544030900071000c0046440600c0c00035039030360f0014007404046804695034607441c1e075292440c1d22842d12070741c4248076010101040a82140702c800b45100d8164445480103460b082e0724021a40c807540d000d4074044020241544030403078130409040d940e03100e4a10592903090601e4410324182001c0300c124440d0805101d40d5030800070300709803039003550301c1c030319286106a8144501482641003504019854081c0030700110340aa683c1c0051485000e00d6402480403480d0319404024541c0b03800b8407012070fa0740411b1069142d5020750000341e01d00070003401c00204442d131604d0740812604802c40c4e40000948036200424042800c001d09508100c02c5e81d2440490f86170010f041e40007810500c203040c180900451110502e81c05841d00301c812102d903815095042c500080f0907403c0c2002190802d000c1403030072070585450b502c600d5a444403298844c058620b84440c45c04000882c0e54024001c03981403050082d0509650740b400020f1808854910016032100030100c035105103895003551440c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 502290773 1250 502289523 502289551
    0x110303040b0a0b0a1a070c12051507210609060b04080606090c0903030a09060f05040b040b030402030a120206010e13030e0405090c0a120c08030f07110415030602030f 73
    0x428803100440d5001540d0402c00a0302c0c034218030200e1a090640c0d401480704071120495031010088a200402d1650b20520040e55129110041001d03e00400c078405400e41d405060301e403600c00007140c80c994200d200360500400e0100d00482007040c05035280040c84200e034070707404104012203160140d90045c014012610b81441d040515465862200030a014800c08440b004a0386410505048030411440901501d46d141e0300000c1c00b9081c0c00c650704c2542c1c0021400d0460603070191148080d942900c00c0001428030f054a4140c00b611140c102074000d0340e043c007600315030000082810220b8501c46103240c0240009600d4003010145c6010010044150f090003540300c800000d512035a00303018140200e40c0041d4544481000c80d25000c500a03555800c103500c003501081c04400c040c1e010310035511443c0004a03141d11500115228003c2910302d034a102d405021050019540c140180400c60018200003100010041080e41850150303005030746069002046c008100042220a40e0054581c2c1c0810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 502292023 1250 502290773 502290781
    0x1103040323010e0a200414060f04020f04030303090c0f17010e011503080d060e130219030c0e0a020d02030109020403060c031e0f09210f020c0105030c0a020c030f03040501110303 78
    0x50b107800316800c00401c20f00c081c0724070307001403008500171056206014008200c1daa9142d280c3c225801400d0319114440d0346444a03e40b40751425000321b0b020711110036541810a46550340c10340203003031144030881d03081e0030145002c106080c08411020042a14040059018070000313806800c40d00ca2480501240c0d040c910707901600d9142001d100c0440743d02203e4155070b0301030b818500c0000e00194026400200c1074005000103810b0390b00f13070880c1c82c60084580540da03107607200038124200b95511000f400d000c000e450401c4028103188a699010840b0000986409080c492140481c0d00980100d10040c0c0d0218050060201740e104038406e410705411304206480f0100160307143c42801084011600b911000b0300c0e281412076030040740c600769000103514442d180c0c1600110381945e80e142442e00140d6004801c110803440010100010340341a1110340c95601d9007108401c2e5907001c1000c040542c810303040c0003c45034404018412000e05030340c0255498070304200004008201d80e001d1f40489901c00d10900c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 502293273 1250 502292023 502292051
    0xf0b0403180f17010e0708010e2416140a091d07080f09010e030d14100303080604090804030b0906270c060d09020a0611060c040e04060c110304032301 66
    0x10030b040e6110306444600c200e20a03a081c501501c055a10100c080c0212000000d03030b02015044003500c888800301751400850f007210500c80ca00041700c5a108442c1c1d041d808100e0b01c040d112201d00c054141480c090010300e600d10340c035281c0c550280340908005803480b101088010740780000e050420041810b41e003214242010002e200190107400b0040000b0050080b48510000b50301c0003030003000b114243c0ea1241100e40e01c00c001070003c211241115180039002841c212810348108040d280d041e00e442209444480600004000a20088504100c10031020001c5501031910f203100e0007030440103060034a01b40100c0d03014030382040500159004110f90070140103d000c0740800c031021054400c50f4441c030600c8144405043c100402a40250741e001002c1001e503401102401402243d504482c0c40361214109010341c5d01c00c0744101015910083c0115002a0072074005c2014010245400a10304003030750100380c19640184d00c100c980203541604c0c0c1700309801005210012400c4100208400d00c4110f9034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 502294523 1250 502293273 502293299
    0xb01020d27031a0901020f042115020a3f0908030f0109060806061302070213111c2a090b04180e0c0609120a0f0b040318 53
    0x2503402841041c10306603505801c00c00040502071001030500550070341c0c9052194641a208150403e51038440000981c2c40c00e050080358002100d40e40c0c22490300e4038000c081d5a85804884201d042c150b005500d26000c90f4551446242c0c12080160040c0d4030050030201810390b99260381d015001e40c030400100b10300a040c859040f03100080f00743c0c0218030020401d83c0350004044000002342486004424000070680102500341a2030280c58100f042c992070345881c81d03980030222410760307103e40c022200c91048082034000e4200144003030702e244405040d0b200d03601d060314440e58000c00c2c044400300306002c406946240007d40281c00c914100100840c91040984048100c2940762290086034500c126230b500c1001c0c54801041c110075074640f2240c9030070290303401624103030210356820b0401e40d0500b074212000c01c5801c1445002440d10b440d00303090034140159090092074020450241c581040d01064441c049080c281780301d401d958460707103042d240260401c1468001c00e0044041c00600303004076504013072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 502295773 1250 502294523 502294543
    0x20a1d031e0f01020a09170109051c030e070602012306030303160210061806080c030c100201090204060e100e0c030f060409080705011b0e0102030f1e0c07030201020607030b0102 78
    0x141801840101c1103840385400203041000000d9840090060745a40d440352811007a0394110340d500d20141840c4c0050741c00d960f074a01010704190010019855028520003500021041c2c0b400e001ca503600d0341070f443c1400c00096522041c00760b5120146440603c000f03208284810b10301d038900451a040500100340d8a010044c080309984e401c0500d06024a80200401d41340090a0b0350309000b001d803101640043c0c40c00440c03035594400d00703080011a4200000c281c0d14140900a4028102147d4944c2080079203104c012946095541c0c8030800000b42c0c840d0b01880c1c01801546ca042401424100c4a0b0b01c500f1070903a01448500705440c05012440399100100d030f802012010301c49843c0d407502e00009000380103980c0018565040003801004000c41900b007158800c01d2550300662040800f1002d50306002c0d94072003a4010f80040048100d084090400b500c0d20404407032580e81c0d0500300c002c001817140c1c4002c00000d8180d0100c0d070100110f42e0f0411050b0742c01001440d0034000302c1d0060300041c1d41c890141e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 502297023 1250 502295773 502295803
    0x140c0a0e090645010501020a02210d1d060a0909020309030d02030702150108070b0405040203040830060105040303170612100b01032f0309031c020a1d03 67
    0xc5402d9566044462080b007000d801d0a980621144075542003009201c3c81c00781c1a2200804032440484809504504890041c0c01070000151240d00700440240b00c941d281c540f04008504503400745104028540010b50305480381c50322064110303408103460f41d0700d82002e4801c2804111454995038024044000c0710034100001da00c0e030325101e101d00e003140a103445c1840a14404001c00240c0d690008400300700c0100801e56011698071400c3e010340380ea4044c001d4580c17204c0204400c125030304280d07004552040c0610070250600f401440d40680c00f50b03030000b41141110703599100e0b1101f0b050105101ea0072400c2400c00c0d330721b05460750760060031080c0642c0ca40d102070505940007600343e4440c40c0c01c1e107008100000c283c0301c0c01141c45612500801801141c00d0000346000c01002c1a02c60702d00c0c01c083e00002c0300c54036100703076848281c0d41740d0a070f8002800000130b030209100f00c2342c2c5044040038400b20310441c45809600c504003240c0040c44074099031044010701000341050400d585000c181c014240c2901 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 502298273 1250 502297023 502297039
    0xc040b0a09030f0830070c0212011505011d130e0c0a0924140d02030a0b250c0c0b0a09030f0c0305060c03100e070e090901140c0a0e 58
    0xe1401a1100c0695520150464600200307410401400300f00030704200003400c0340ba402850f200e04d05030419180c4007060081c030700110750100f82000d01a5101758916440240940f80c8094410b50070340c00c0d00c4842074500008034980106110719a040390301c4006865210070b04080d0f40b1070040002d280e041c9584003d20326183c0c0e8640000510340b00740202060118003415683c002c030b035035500c018010281d00108080850003402c40c0d0030001d040c1c0c0e03901c4048501040880c00303601454010040e4480d24214100c0e4135110743c00c4030000040081c044a40300308400840545041d4030004203282400704004507508006400102e01c000900b4031400c07406860b07a00c489a034030b41c0d031821001e6844010940018100c4407805ca009010003500160b807600b0307a4490002e460180e04e80c01900d504500080c0c0304005154100031051111014142149500440a207004903050b032124010400040080e9400c10881c1d44400320072405052014480b50080c501180551030210101c030020310301807001c18401d1282c072035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 502299523 1250 502298273 502298287
    0xc0f06070f0c210908010c0912080f1303050a0507060327050c0a0801150501090302061603020a0b160f0f0507320307050106060806090609070c06050106260c040b 71
    0xa01c00800c3c40c0c07420b101c1c02e6141010035070348000d07000034102e10401c5810760815601c964100d2084446504803040f0079032aa0103120345507a0104560046102e02500b60805d02c0300f072503d80349001d00b00d00290b001d2005815515807a040060070510319800007000e041c10000c81c4440703102c102010180b402c00c520010301d4440c131546801410426110541540a002100301148046066001011450180304000e0242d60748100542d40c8030806d01c0041d50003417007440092004d5541e5100030244510074810383c1c0586d01a84d43d100c3c2202d1098900c0d0010a007c05c407113004507a04481900170802c05402d0000d03070300d03044c00d000030080d21442c90014031991200fa820501a545400d254810a0130281605084130300d412120f5501d0708165420744066080c17100000c0e04500640b10705008083c080d01d0400d2541c0c0348400c4c0102e00740c0103001d440c2048150601030000c24114441c040c0a0105070340d981494400c698140103401d101c04680900f03036402c21082c4410b021001c0c04a40071100c80c0d692254a03031719 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 502300773 1250 502299523 502299533
    0xc070c0b12070f0225050915030d050a090e04110f0109031e02040b12010c2c0402030411090103081c1b08040302070b0d06170f0a03050912010603080c0f06070f0c 71
    0x4165005203601c24000c00903105c080c1450700000080d29016a8035000da03980d044c40c694050b6170800c03a0590140c1102401c407031002c0c41540105a10551800d010741040da541c10020541d501c1160709548250300d1740d58000c540d02c0d00100540180c50f0918207142e00f1815a2119081800d00710703541c140450000003640300b1915980c00c43c00ea070070340041481c0a01e003084001103000c3c0070711011a50000325030344005481030b110404e1031a91300101206500f140702001e030901000703600c0034005441d441c2c40165811002d9850004150107184900082525a40a00c140a85042d003030440078141c603081200600c1243c428400030400c01926140c00303100c41d103450606905140b81a0801c4032201000036000e54440744582000c0221002c000489140f03021000e00c1984810800004845a0b0441070545021910030005000354000081001d86c44d0b1a684249a0031904194021170f003600300442c24284100e1309110320201400420090500b614280078002d0820200300c0c10030050214840380ba0f01840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 502302023 1250 502300773 502300783
    0x14160803100b0a0c2013200c010c0e01080103150207080d0c0c0506070504032001090e040503070c0501050a0507060b011404082d0d030e28050c300307020402030c070c0b12070f02 78
    0x1400e1f1707101d5911442c054034203010348820108000411b05c8003045128552240303082030b040340d030020b0500e01182c080d106420065800381e40300381c60204082c403075094000350900c02da00000996071101444900300e803400d10b043c03050080007a42807040500040000c10960031f200140704114490880e443c9070b01c0750040c0c81c2ca40f19a0031080c144100f0300100400c200b00000100741c01406460110074a0742e440004403902c0c0b2810458030700065090000c1c2000896940050343c40700c01c1410200c03140710340c2e0340001000f608258801801030384000c07a07188000c01c64060b01411500c080e5400180315543c00209540e844040c2d50200401d40c0d5000d010408201c24408a00300300f031140240340c40051110294400707021015800d03299030180040d5840e03070b861704584642449101c0b071004c0c0a035001480030290075003001840c45c0050300007084050700680c2d0b148011441175418509490b11a01d183c10441c00d40710080d00000200901085180c20094800040e1540043d15141407c92204490804c900708 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 502303273 1250 502302023 502302071
    0x70816030b13180b0a0603110103050a060312020d120c05040e070203040e0109061409040b06040e19030320250807060509030a14160803100b0a0c2013 66
    0x9610340864200000001802d41d04560b0091a07404001c0c1c903581c05d90f00450700948401030240f49036007412034084d4000d41220754003020090001030b00f143c0d00e840340c600000801000c080140c121002c82d801140c1c2100031410340e60302000040001c404108006881072155014070032079145504001103100d03108000704c5000e4076008041c10200d50356244d10308043e0459003d454040d514040040b003682c204800c4080c812600000f0f900d00a80711441444003e041e0743c1c0c2103850394042d1400c030703c08141c205641021203510a9500080080400c088000442c0780400e404a07a407070304024a840d00c0480065865100a250303178002203c00c42868280b01603c6081c0e8003c4c0f0440c105810014071074000310103454514034585460201d2030110311056050300c101e00000fa800d034200012140803038070b00006140c1c08413a0304804c480c10f0fa01c90303001c480c0a4004080c00c200040c0c1e54a080c1d810040081020002e60006406800d0020b04030400585410442d4081d45109036136030b4022507501b005280a1661 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 502304523 1250 502303273 502303309
    0x903090a0609030803060603191b0806040c09140d1a0610050304030207090c21050417071736182a09060408060f06190603180c0e040b070816030b 64
    0x2a02d400c42c030b03c0d0085245c1c010000d000320780b2f644001001c07800c2034058036561440b11b545a52040e03040001074003480c400c80040a800521112a0b2000215210b1400710000b40810b281651442e1020410900e05000c800d00001c0220900c01c3c440025000910300040d030b1003401d808901c1105115003207520700f0342d0f084040d10141d622050041d5180f102d6000c540113500482c406100c0c1741c8400d040406c148a00701c8001c125074803000303620740040304440281852450340105900c401405414070725040e19102d07641c281c0c400700c4040c0140d491400440340340b405501d00425100c94030300500c00c0d0401d1049003c0e4081545c0c181c009080102d1252021078442c81c2005141035111070715480080c0d610501110792900203044003002c03404c945081407104801416084200310720714204a011805808088440a49107504c2c00303001c0001102682c0450140c602004403555510f0070341050844002c000c0c24440a001841c4148000440c14801e01d0b04440818100456203c0c0042e022400041c100d0340d559070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 502305773 1250 502304523 502304531
    0x10804140c130c02010b09010630050405101a100f0909020406020c0405060a0e1f05030712030f08101502120c0102041502030c030711030a06050903090a060903080306060319 76
    0x102c4410282e02424190000d82d0013000b0034004242070009030300c2c082c0107a40c003040340011119144d5806260031000a0142c20b40420310300e601c04240f1040d00c20a603000c0b251604150510000143d0300d1144014a09040640080000f140804070710005089506901040740f1a018440d015004004101c02001810b00465403150b40b41c01c001e444140d0303030014510a0741408003107000c92421a8042d809d840c01210501d0789900c0b8205205d49805112031a0312858030404ca0002e29a0780a209600c0182038001c3c184240c01d030b42e8600107140e044c19060140502c42c2c0381b010300410071649495002550301c0024941011340c01303d00c01b0381c5040f4040f80a44510700700003c0d080b40303000040d00600110341c00c204001011500c04030003a610703030040d001e003922990300074410f80021490349662402000c0029068507040182610b418040c0c407400c489040c040d03440040c0c580d0329410306004c54030041c01d40d480c081900e20700b180e4915800c0e10010b440548039900c00700104a2510451032400030701100510108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 502307023 1250 502305773 502305799
    0x20d03030c0e060f03160c05070303050405151e090f040603050f16060806042007050601051905090412030e0601080a0204060608061f020f011505040501060e010804140c 74
    0x240a040d44500503000905042c801c0012400c0c4101581d0140c1012194681541c3d02d60103400701095200e0300c042e040201102c41407011510038030141b0301443c040d55a0a036500e04280c10300c0b030f0801c4403801c003642a0301b0402c01e09c03c10440742030101c0d042c0c0c44aa4100b65440c40c01e180024a40d2602c0d0024661041c500b05000003045400541682c2c12403880055501080a004036148540100c0c460740c401f08070803800084482c64254080c4442d500e14072488480000005448010742c1c02030442107039541d22050042c001450700303100d070b054210100d8680c1c41409082401250540802410040074aa000320342a034900740603402c11952044118200c130b00710340c0c0d140071507035598200b003800340e015910780b01011442a1240c00d0712403051601a20001903401000200da90611100da07030035046015000b116414100203000d00314442990928202c000790030001040304455043e07005406011120001d00314030b0b41c001c5040d6600039040820814840d61901c41da6050513000d6078515880190a4200c3d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 502308273 1250 502307023 502307027
    0x112020f0a091422120f051e0913062306090d050d080c03061f03060b0f0a030609020309071814040b1608040c05120c0303041706160815030a020d03 65
    0xf142c4103400c104448400f401070301c40002c00200302ca0740003820b0742c05402d503410101401010b0200803429540341c07451426552994141c0d008884012512104000007004401e038900303180c00b54240150302c0c07400c2105a15104a801100a80113007900d199043e001c00d8442c203036a01c2080e00d00141010381203400100081c50117a4030f407060311400b00c0c086109180810614600502964403450740031f0f01056031070381c00f03403040200c02904034a943c1c105a1140d00214a8092100c00780c1310070600c40c069151a1002d00c44060706540d4250401428240b045c070800c1041003000aa940407585040850b41006061450b40c0024202e40b07502660701d11540c1c011f00c0200840700441c0b0344201e640e03101d5100d2a44c43d80804a40fa520141c4015148440481042c0b09601d0100030794006c040001d02111104030044000c81d00b160015070200d501003407803440c104078a20003070041ca58009041c400482646203ca40003401c4d50302c014050140725121482d81030300c5624200075420308140c0051455203c420035242c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 502309523 1250 502308273 502308311
    0x20a080708060106050304050a03050c011d011a120601090207081201080709180b010504050c1e030412020f03070f0f060f0501050a0911160f0b0705030403020c06030112020f0a09 78
    0x29428861050b2800000e02c40c1c41401524000e591110207400c1001183d00e04a41d81c1e0070001c490203040d565503164000d886000c0440f140c200c00703c0c07400070074501c452071406140075041c25001c6006142001031000f11441c003240746030549809060040e01d030641400e107918a4014000003840307036455440007091a090010306001156a84007082c0400003c6410601c8500380c81680109030048030f0006000324a0560002c540c400003004c846400e0096884041c508603074030521144400b0000014003046c441d184001102c0352001c1c0c002040c02110400d0b040c0d076079118048014101110305060b2408000b020291400038942181060180e5850726507100000c01c2c080c4100c0d4420420100b0006019a885c000c1180500301403201c40d060030148805054401001041154203108000d43c074070000c0c1140d201980149600c0c0c0c0d90b191203141525000c0d01c2c00700081c103d5445488103000401c10049581d1125a0710303641558494201141200030468201268220722429410408a03101104020b20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 502310773 1250 502309523 502309529
    0x5070c0e010f09110a2109030909050a0903080115020a06050c0306130e150901021204031d04090803010302010f1106090a0c0f0311060309071e032a060f0903020a0807 73
    0x10301c2d030304a41e502c0300c0180880350005088026007000b80012a00700d4050168502844400b1225000f0340c8151b0180104071007404d00704070701140120400f8045103400e8840e203544080038500404c0012501c0e01c01070800401441a4180040381c9022a178001e442071106555440d84040180700c0c5051409034230740f242d0802c0318050300400024104c81d80401c00c81c05000540b49449000d80744e03541860f655500c04400051139207411350340070410051189800c0b03a11602c654001d1351000c05a208100b9035004824451038454425800c01d004038000c100c1e004106c0341101d5090070074880c50ba101e10400d54654020b001501c080d802040200881030030b001c540d04822a200da061007030071a40343e002580310b05544d0f000240030868801010300080c107010b40256001144102103070081359842001d0b0720381ea55060500c0031001c810203410010000f134000d25001940500118011400c4c080311300f203420414900c1060208118450034420b128040c441a40185401400c00a40c45856110080d5680d4482c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 502312023 1250 502310773 502310789
    0x20c10060e0610091a0705030a0306030201091205120702010e0301050709050a080319050f13120209090604051c031e050f1f050103020d02161406060607020d0204090305070c0e01 78
    0x30300080c0d1a860303c0e412001401185460707043d03059003440fa01e0b0401d40e08180d10055460030030000300000c204100064480c42a56a4000c54030604510006202c1c080545c4002064207803542d4910000d480401c1d0380f8400454030b030000c1d0712201c1d01c1c0012904000040c80c0035804d546040705001070b007940594100d003920003c1d00d50354141039490403225aa4490660101c0c03c4541c500140c00c178141c414401444294000240541450360680d20b44c81d20142c00c0e44a00c8146028080290840c01c040d198650b000384403034054100c1e8906901c4982e100d001c60129454060410160f00100728080d920550b00080c030240f9100c11282121044402030506480c090000640e00300041c843c2042110200c040311a04950781d450649400010760194000380e02030020503409100c00c0340400c510412481d40c5501030300c00e04640794a000100341c1040405098103014000c10050b80c80540c60360300010240315415140003550003d030381002c5680e40541d010050120101050005890350401c0c1624141c602d41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 502313273 1250 502312023 502312049
    0x1806070317062e020a0c0602240108061503072126071203060e130218060a1a0c030a05040611070303081f080f031e03040c05060d020c1006 61
    0x3440801001c46032002551a291526000040c3d002c240d240410030301128600440303c80742016a43c503c052205600200010790000341d00340d6503081407810580f1276020188298240b94105014540c07a240c005001d00003070012004599441c2c0c90400c0100010000e150418100e07820b16180c000c0908003001c015500c02d0314000404e010200c484900440046a50a145207048043c0d650700000c030440101c1c10701803556640002400d082c402c407400340b00342484843c04000c1419841004900c3d1440310044a01401c00130802100d510381c5017405040e11910607260135a40c2401e0b02000040c0300b4400940d4050102140410495030020701505c10b981c2c2c1e03a210700c81126203a17100251348801030701c806800511070802040b0000b043e809510301c1c0104001038441010740311300046107882c400002151640d807000a01c0c030001e444103601000a107011008040c503500307054907032030300b411005d020745441078400040f00c0c540001140d049032107241c0200240d50861015001e540000c3c41544150300f801002c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 502314523 1250 502313273 502313281
    0x60501031a01170703180b0a1401061b05010905070b03010f08011103040305161b06110a021e13050406021306021501141c060e0d09060f03021806070317 67
    0x80005101803082060b5a0b005800600465003e18180f001d0050f40905540324241010990220100b122017801000000c645041000c000c0702240e03090003410352038001200040c019958801b01c18041601502d480d1850080141400c500402003500010014441d050f000544a03400310080c5040b80e140e000344620703155846400301c0c00d03100041e15190240400b0070010300000d000d50041d200f5415030700c0c5003070001c6a155480b548114039000d800001c03508402800c100d442e901910140078141d180014100c0381215501061514950300000c9242000004880042da250540c4031a40001410400e10175401c283c02e205000b0340c4005583c1c2d44007a000c030004201c0038000940003400251651844901da0f181008050403c14021b10030b83d07111240e05001098041c041c240c2d1004d0f2801403000240003074100051514007a008405401400200001000000e0304101500c40d402e11032300300980d84070410784621103500480300d14540c0c001000b0850701e00b416840803065180c2290061072500381e0315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 502315773 1250 502314523 502314551
    0x30303010b03070c11060d0e060604140a0c030e0a0f17070809040903110307060b03070501020c01020d03050c042115150b16050d08040302060c030c0d05100e07020106050103 76
    0x110074007a0920840041001c40c0790184100184052180030f00300413003d1585010005017581d10500800040340d4a4924010452406203c0b0340d411210440b41040030801147c644481c48200811044003d952035051420f03607401380c0c0146042c800480d00395404807615192044005980d041d050341c080445682a00741c0c07000040c101e0f000c0a82003401c1c03078104070b04141003102606100c1d40480401c070340001d440140c010104054040c82e8072803d00426500f5101c01814030b02000c50740220b0455000d81d02410140e6000b0640f01c040306041e180c041505d980e030310450000c42c8180d40c024840144100903410f0090000c200c161541445443c0e40c00c403c2c441030f00044192542280c2900b041160381204000c00c152560041c4284125214142103600b21501c1d1681001800702e5400c01060040003000101070741072000941c0001c3c00301c000f0341142000c110840c428050a44440103d03552a00402d01400744490340d41c00078400396101c030a05241c2880003e000e00300794414107002c0781c1045c0b8902c2c2c0040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 502317023 1250 502315773 502315777
    0x5030d08062407031d0607020f0d050601060504030501110a080402130b030607050d051005010207060e1804050d090602030a05161103010f0c02100605090a05132907051603231201050a050303 83
    0x1400060101d82001002c0d02044a20103a4815054ac03204480b4250800108103110040c000e00568494944a5181d41005420b6074489204490440d501b0000c2d1070f1074070b40009009030401e406580e81c1542205403001c031001805040c2e0301070b90500c200ca0800c007145600c04010f122142200c04180404d071141c0340085500009401031a0150b0062802448081d100390441c0d182c0f20f0b0001e0101c1202c10f118544000d180c50281c4040d84c3c81c2e0080a5204070864202002000602d25440110302d00300c0c4480e401000e41c05065444800d08402094000920041e0340090345d05140003002003200c100c1c1000e45070010000603103007801501030f0131000c001b10602885044200e880c040c02030902c80e590440b130318009200c02886035640001c00005a004554403043d040380600f654085520500801016600000c0009201108200b41044907041c9081c03440c08000c0d456606080441c420368500300d1156400c071f502028819603103008214841440b1040f800b8904036242600e5041e0003d860b04240354482c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 502318273 1250 502317023 502317077
    0x601031b140f01050d020913060303020105060d0b0112030e030d080103050105011d0a15172503050312180f06010302090609010b0a0e03030702100e010e0a05030d0806240703 76
    0x242c030034140240a5029100030143c00412010042ca40461940069005403010760307400c01a5a85850038000c141c1c0900c19260898030840325071184c7d0311256160307103010005000e403980c045111110700c010140249205151304074004c4c15a80314000480004204074824072003a00c1540c20280005803100c822045419400003d81d5001034a9854078201d0001d0820b0b400f0b40c0c48030901c3d8220009007500760f0050580301c562450b0252a0039804014942c0400d032030149010162181cbc980d081000460000031a1070b2800d401000815a50710604007660f210050302c0c00600501030b440001c490342401041d003034140d9100303c550103002e480c1c900600010090034020220800800c01c030500c00c150150644101002d8000c0442e0f242c0042d95000c81c0304104604491004515090303801c940d90360b04900f0460b0441801d550000403280b400300000da0f41c003007495a1205020060000c40c2407502e0343c2c4c16070340c07403010701c0030704410510900118204103510400c8281c0c0041c00c415100342c8039241d0211441d0b05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 502319523 1250 502318273 502318279
    0x60f0204060509150a0e040504020d020901030b0708070504060c020409060f020c0709050c070b0105121c08090f0111090411040806130b09030c1506030a05073f0f080c0601031b14 78
    0x4100c01b200c080c88014400507006176809404600e15400507501c44070114065031080e0000b03145c6c1d0610a102514904000c0c01c0507062184c18401480135550180e1044001034044902003400381e02030800e4401030401410784c0004a0001941115104000660381e08542200b002003010f070740c2d0b02280d98198050014001c3c06200c11000402c0185000b080c401c651100341000d403223075141107403008045030700b800d100080401c0d0f051003040201002400354802c12280c000083c080b05c1a1b036403205070144100441031344503a40d90080310001c9a01c80d400da03806041410100c032070500b03080e006000017007045103040b1402d1803c000004c1c04128080195400783d880e4000814140b5031745607550440d03100080c490380d018481c0e6441200804c2c1d003000180c000784a141800420070400175480540807002280c680010340198110503503a1003c1d080d20940c40e80c1010594080d50701a2422a401e4490202c150016200b000008800d2005050181c46605080301c44400c41c55a201c411280018126065682c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 502320773 1250 502319523 502319537
    0x9010905010203091305090f010e060402181614040306020c030405190315020306060702030a030e0a08010e07050616170306040b040606080a090305090d0f020312190309060f0204060509150a 83
    0x162071131254104507004501f0307900750b48642d007500c0695400c440d40c00d40b401020798480b070309000030350a0100c0c0103d044051622414110324080074010300c5003007004000400c01201d6103400c1100911241900c01650740305405550781d401c22000b41e6074940090040078440da00451161001450041c0740d402102e6000d41c2d0307114100d6440e50b0f00002900024192500701c84200031802c0142d40034442c1281c4207110742ca50a40d0740e4280810700c40b416201e904201940e81c940552913501e20390000d11442205c030116002039580c070f03c0c00001074504100c4c0600500899000281c014041c03560009503104075800d45040283c0e5030201d0402082c2d9415218440c0400e40c51004140e841140b504643c40c06402820880c1c5000401c80110b40418141c00c1c058070f100c1c035400c42150031441e0901a338040d01030340b181e41a00f010000d0b824a0903480c1003004617814141d40f280c2420030400b603a04080c0902e8042d20301151074a40c1d0705806030969000604480c414047d00420422031400241a1512260301b81d880354 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 502322023 1250 502320773 502320799
    0x405070806270102070606090c0201052202090c040e1e06010903030e1c050f010f11070c1502100204060c030f0c11010c0f021003020a110f0a08030c130303050901090501020309 77
    0xa015034410b9072400740700755000c00c42c000200d4014007400c40205101c1c2c50000b21111041d00007421144060403070410480c0d91440501d141c100311010782c0140c0c0e0121203d140c40d49540000350528810703903000042900c01c07501041035614a4024485081104494800042c0da9284c01180c021440340401008202c085081400909140c00054902d10203128a0740c00c1c680c083d12680d20704011048140c903640e4441508031042c200e40e02070000e9454014007440e0601c929956081c2c04544c48d40100c1c9900e612079018101294420025200c20400e04601150f58075140c001c000c2c00000c400c0f80c1580801d0380c20301010006803203508010b00a03904030b45011402d031201c100464015490110650f01e44412071070080151f919148ca041030300d68151001070780c80107140d8001c0c09400c0702c404140e4072900580842c40c80d450b404a185105183d11095075a036071707902d903e031903061400303410010344d24101c0702c060200400da00000102211802600c9842c41ca5940b140121703501d115140410750441441002030f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 502323273 1250 502322023 502322071
    0x1608060c03070309140d091212050a02190b04120f0e0f0a03060e01050727030b040c0e070e422203020f0a0501051b070506040602060405070806 63
    0xd5a00500c0a1402080104154413440005604175452651a0b0400010010740d540c200030703120000d10140032811426082171700c5841a00c41001d10a0b814840d000038840100303442030208c1103030002010384040204900382442200c880e0200d40469208908542032140180500c03000c2000c41100c0d03880024801c000c5040c0100641041a400e4100c011901c0110004051b40180d05880b10380c6000081d80d0701c0c10f203c000789a0040d90846500c0c00340ba200c0403a40c191481c52a00e0292600410508240e49440c42c203405a08065400303900c02d40d2101041c0003880394054001d518a0400312040c01207040707481d21010107200e0000400b90b190f01480c020380002c442186021207000300c035162079420202c202509860b480072000f00c031810591010414400c615055030300040340074050b60544902400d00001034964844e6980c142c07140002d580324288031040400144006e0b06001c1c2c138107a00e6680d07965001c2d59a0805540440b00c90051100125408400180842c415205001020582d220032012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 502324523 1250 502323273 502323277
    0x2070b0a0b0a120515070504050102070306020913140f0601020c0307290406050316030212070318020402210f070e12010b04060b121605030a0b0103061509081608060c 73
    0x156a00b1588500e000122510000d9a050540f40100003a0101da50148044580c03200c00501c12001d0000502c81030217140d0380000c0d25400ea0791f22070001640e4207107410009100d0415501142c41c0c542c2009058032080405d0b4210383d00034504403c2d01501503c070540166180d6000e120b0181d0141c0c040001000001444440360503201540394144031030f00488960b40072a0361281c2c104201203800001070101001503014035030440c03005403804504055000702c0d000c40c2c0300006021a0300300340c4c03600003040c19450304c90030308911664010000c5541c0c0c10060002c0e6069040c0183c03001c1150300388000078580289440c1d5807803240f40b00f6950181c14031070715400c1000002040008500f1596980503000300c60f220380c81620b0292088a44d03441e291512480340c0c55102c00d00070300941c04000d0351180103413000e42120603607410121070900440d030a1821401280100b800e0b0b400200003402280c030311069503800246400c181c0f000b42c000da8281226071100780e95407007842e1203840d0b825070004002801803600707140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 502325773 1250 502324523 502324541
    0x61809061f0c030309020d11130509060106140d051f051f051b010e150c0c0d120b06030408043219081c0906111506030705190501080a02070b0a 63
    0x60004481c401500421500c408403002120b62480640b03c580d4107180c003c00c180d480f040403c00032b120341c0c5480c02c56540c603804180f14410500240d00000c03124142448151a50a00380e068108150f00e0544612a185800d80d40005448200c1007404500c5060428040ba25810300100442880700b4a05d022941d551142c000c400044880c41420b00815a003801642100040540105041c1040303500e40da04100c4064140c0c60041001c11030314010034000310b03155080081c82e062900c40c0c8119214848040d01840c03001039400b000000411081089176009801510400d42c1d55802d10305c50b122014880d90b2100c03142181c0030001c0505074050349462801d0741c890706850040201c48650780c0401070316005c0444c065000d43c812a807030540726a80d015004078003d0600345040c28081d213084202c103480318104210210804140b10009509490812154005010141001c14141d0003000c43c0b00c840c40703060203618001054031000c01d0580c070b02030017612411500184c16800c07a8a60580a00003420998 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 502327023 1250 502325773 502325777
    0x5011b151a03240c1207020a06150e070809121201080c09040305070f02030304120f1101020c06090114091203040303110114010e0a0605060309010b01080f0c031b0405061809061f0c03 80
    0x884110310600c526460046e0300030380041100c11128940f074020b8907090303101c011900c07030322031020400f5201c008040358002c01c0c9810b212040341c1b60441820700f0448103c00001031072500040300c141040c0d0b4100c10341d041720000c5094074580f00f1040c040050f07056044c1c4004d400180d0900160012550b4402d80c40c40c9139100404030313450030351303100c804440c50f14051320251403008100c28460103010f802005e52014503c244094031600c0c417210002422802860446030420228034903400303d045021081318180c581c0104120318469512851582d0b03948a070000304c00003907954041100f152014003074145510f1043c1c030842056802c184900307103604801401c44004507280e05002a40342c444034015406020843c0011655800100000d0100d0001401803901d80c81c486040045001c580c0c01981d8200d1814034bc0036a11013034032a071000f0f85004641207540d12890020b115000d5048a50400900703180a403007008a90355400c003000300800c0c4211111041000d103d50400c0c0d900e200d00030258800703120b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 502328273 1250 502327023 502327027
    0x80f07020f0106090b01170601081902121003050d030608030409020f070609062717130e0705180d0c14060d09060f1107080405011b151a03240c 63
    0x510300c01c9081d11a0360303010070840c541d90302d155400d03964840108000b240d40551843c2050a14100003003010030001d00000d42035111348060516080c013a011560040000310300c01d521802c00110070151110144000c80c2c05205040340d071004580207010704001c603012603018605040c60940054060341c40240d54503055241000b10341c0014680b80300d103141c2103000e60030005400c2c04c074032508501141c03074a4010504070202c160b42d10005100010310180503440720a1507884080f2900c261103840c41e40e4000c4881e00702c0c6541084410340e030000213030041142c4083c045010810030340c01d00070b0000c1d42e400042c0050444d441d040c492018075252003115020701500e80c914103001031019604490f003514040b602c094940f40d110b00f42050501a013060890403e003003c1ca098103c0d92090610b01c1288580c9041c0078050710211020858401e11a8600380c20903508a08400e80b944100010104802501494065142c000c0d86600f00000c50307034101e410301c003841400250010300d241c400342d40040265240b8002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 502329523 1250 502328273 502328293
    0x3011509140f011e021e0f0a06020903030f0a0309020f0103090f0209041103011e0b090c07060c05160501051b0307120b040e030a02150c07020d120210150303090506040303080f0702 79
    0x26081c20303c00c0e01307031554050310100122201000601444900000c00369003c04014806085d002c00d9810308564040070050b52a811107001c2801c45c069500281a80b00000c41c0d00c3c40b2494054204c00c0d4258821074440e484d280014005500301e4101d4080501030b00c04440c1920010700300031100c60b40042c0070300d10200017507003560002401e40311143d41d50307603040000a0810020003101d006004060b0000c0b509010070f07103800d4400054601440130007038211f0352210100b450260140d0304503035460400112428007480d29080490282006a50000b203006000ca08102d00c1701020041c5c90040006a640504440004451201801004103403d9115613283e600ca1403500b410030051080e00d03000e030054400c040c8180152540b003c030041c02140c40a80401c5144010394400741440d420580c4603410303000c0c05030328200c203d14022042480d04c0d84103161a040d000c2400c401d80c2c212045910a07560392509545a4050140c0e5008a220050125900c1c1000c10180c48049014a6200c9410301c115514650 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 502330773 1250 502329523 502329557
    0xa030203240907120b13170c0609063d170d0305061c03020f0303091c0306050315070513030606051516060b130f0f1815050601030b04020304050303011509140f01 71
    0x4074208081a09001170910f14408c82800344990221801014103454500700440e81c021a6201a89190008240802d6600b41c13007040b003007607801e0390140740c1041c555440b441c048110030005a60080981304003101d00701c026202e809030621a1402420322503511221560501580d819214101e0541c0200d03c0c2d03800002ca000c2014621172a0350f0b2005002400d0700a4902940200282030a01014203100d018400e80d07c1c0091000301081198441080998807503c046409004184001d804c42103c08400000d00515401c030900f07070707001100d101c080354110b81c2214015220314401c94001d012460b40c00c6011495a07484803040a0001d400c9865030244c01c0c01c040100c510210103a5121541c890007144100740d0f03440f030003400c621521001074880c8501e45510071405080c2c0d40c0101c44588560000380541d100b42c100b52114100034105649a00300351800d182c40790424003458885c12141051040613600c10722030541140c0c4001119204810030006000c410401817824034140700c00e00402c000c04036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 502332023 1250 502330773 502330793
    0xb1e070b040204050f10031205090909010b031002040608132303030106203403050307050607031803030b210a0b0a021c0207020a030203240907120b13 66
    0x6106904480e190318140c810403003200c801030404180d143c0d8030402c1158182c600c054007000e482d002010419040d10603881260745108240d4815004024002404581c4005410400074510124141d4500c6200442c403c0128040c6120b400001501e15010402c03034800e800908050f6030286a01000c050800b011981c0c9402c2e203102203103800e07413002004000d29a0b128440e0300e840507809944a6101c41c24440c4c0c0d690300c4030348240d0b5506c403401d4a080f10103c040d081d0003200d04030381d614551455007903030303810095203d801c1040300352000e00800d000104010720a00c1402c28801d0034402c80c5a503510551030440040c00103c254036000401400c45a01000e140e5500340742c0006214014020070196182c1001d0418000d0490b640c0f03e4010301004040b01002800c0c070725002d4400e00300503155102ca00018200e02c080307500194040c054141c940b2514090501c00e21401421000e003d013403901c07184000d9a8484e03d500c1401c84014035101c0c6600005c10b4007548541164483c0300c1614441041d8461400c3c0d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 502333273 1250 502332023 502332037
    0x1e03030409091419110603181617060106020a03050c030906040e190b030714030c04090b010501081b0904092901050f030703021507020d080a0207060e030a0201090b1e 73
    0x8828034403c010241030204900000c4512900c1501204041581ca403540300e082614003500c204008000079800041003542c60154031070b400100c400b0f8118030702c0580300c03080d203e010300404030b0036007401d0104809001030b03018100c58007a40100417000543c1c0301241e5a0704040881d0085010420070100300e0b984410180026000201e5100205d04140b40080c64550b11a28668a150700f0907841040c25607002c00d0030707011188808010304148034030400003410106a030070707400c0c2d001c0d180c1011141070040b039120607816a0700a03220f0b18400c0c1c5a0080c5001d02c0c10b03600c4082c040080303041054400320b007016040040e260f4407402c10380b50b442440c2b0030190580c540300b0b864803a09112032001041b051908001b0f884039001c099018050712400e640200340300440d0003840d40d80080c2c0c006a02c1007113407546100d86100d40c1d080028103441e0070803144d0082d114806449207074000784001000100c00d1034041542455a507050311200001454140759103000d070001902038001c9030980703d4541c00800303414012710710 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 502334523 1250 502333273 502333283
    0x6030c0c150c040609080604330504060c081008280f0506070e010302091c1103190317090c090601051b0a0615030f030c0206091002060a05151e0303040909 68
    0x160b0f4149a4024010981503012210702e5029101323210104440c041e5000d40b1110002c110304a0071240072030100d800e1580020303000c41c41e15003030400051244c00c0c3d01200301d0410564581310981c03170712408120000e03100d024100c86038101c100b5506103c43c0760b00c4108030540b030440c0c00705400c840e41d88890f00560040a0242c40c50381081c4104000780703901030409812400c00742400c40c00c06424401041c6200152030007038400d805008000c03402c1c02450151200030280041c11504a00c0850284000e81c0d41608411004610745200c0d1f2100d4911404d05240300300c60110042400c0d16070f400801c200c525014028a041c0a010885411940d000f00200c0c2081c00210008100c90405d07480c1020480714001000c0310042042c5400b0b20000351900001d007600c640510745a4901c442c03034000a24280700326103100d40d11201c0c00e03044200305900803c11501c00c202d0b540c03080107503540d101e840300000880c031040203038011040000d41c000074000490b8851249000360440c0d080caa2229000d40846190003004c1c0c1d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 502335773 1250 502334523 502334527
    0x81b07030c0b09030406090308070c090204081b04020a050a031814010222030206090112060f181a0f19090e01020c190c030b0604090c171b06030c0c150c 67
    0x400d21141c44891604043d0b64802103152501d0440d00078418070160100521031a4000b030390300300b80700302c0c0d00700f200140240200440d0707155541c401059580c650440c06100d0512281d0081d13070186428401d0314040c401c00d494440c5000520a8120010003851100784d0402114122007004140d010b80c45020040300f05000607515550000143e50049059401a51024100744144016180c11046d240e0a4000b804c000001003440c016400181850350032038101854941e50001c1d04a19040b00f00e110546441c000300184c52202d0008400d0454249a558001c0080e40c030754521420b00800c0186009107641007209031940707410554041d10500d0359121420707034000c02d000304040d4003403085810400291450791040030b202e130b80b902c19920365171001070080440d0500007141a22580c100e0f019269210200c04001340d1a104c2d0071190403c0c4440c904040d1150041c0c040920f1260801200f02500052400d811a5200a489925540101c051441302e000341d20481900f40c4015680500a0b01d204800d96 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 502337023 1250 502335773 502335797
    0xb16051902030a09080a021003050c0415020303151915020a0209040f02151c020f0f0a12060902070203060415061e180c0f0309060b03030d05060a0e090d081b0703 71
    0x705105051740040c00c1e250081c24400005a80b000e00c003035860121820003050507624803000d09480d01a640c080b00361014520509040c2a602000a5103c1c88030b41d140303042810007000c20300c450b03801c45810040f40160700c0041442000d040700d0700c051058043d44100c2d1001c04440d80400c002c440c00391012500003072201091070071842c00c0c240c200b40403038030b10480b0303420f1200601d00b50482820348503e501005034005200e0059264a0085401d0000c8000d051a5100185a801021001428008a261494028042040b140500858503140d400800411840d107803034036140201030341401031010b070507900c040001d0320b03610b03090780a01002d01440c103d401c0940340180d01c680c02d48001034003100d45841d03c10300b070090a07000744018441c2c0a540c940020203000c00e01c1c100005201c1103031001d42c035120114885407402d5076904118462002551504e940035030ba03052030500400c00f88d441d85069044059202030040c412200c00c3d40c064414030720007120769404007403096907030b1141c1d6061700083c148844503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 502338129 1106 502337023 502337027
    0xc170408040e010305061009110a18030501062d051c0f06050c130e090601050d0507031a0901050708010302130c02030c070f051801030b16051902030a 66
    0x440700f5616410501d55401c011107060410f6a808100400e5030300311400b50140c629030241e032a50500e4140d040698488601c01c0c0e04140c00c100c1018000302144090142d4401130090040c4150a0052001d03510400d61608280300c2d1805a9910100455100d070145a8401014940501c01d2a6018a45038189260145001e80810708200501548002c1c91004015101c0b440c41078100e503513583d018a00014030115100a01e940005004010300d092a070f41601c0820320902c25110640d840b5035900001d09a17880c1c550582074510010000040000d114442d088881c5013846019585140c0c0042e001b50300d20202c030300c5459145c0500d60041030007007050711050343c0310806075030b440c6844101c00f2070303107070780e10701c00c1c40d2107400d00b405210f03001f804098596050300d820018001440e5106051403030200b0085052204002c1c0c1048552001d290b032480d41c1c80c59401c0750780030f50752307904000c200 = true := by decide +kernel

theorem cover : BRFrame.Cov 502158273 502338129 := by
  have h0 := BRFrame.cov_init 502158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 502158273 ≤ n) (h2 : n < 502338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
