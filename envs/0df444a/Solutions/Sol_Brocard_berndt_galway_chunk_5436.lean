-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5436
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:51:50.58618+00:00
-- url     : https://prove2.me/submissions/81ae20ef-f955-4ade-93af-92a61ff8ccab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 977517985 ≤ n < 977697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 977519235 1250 977517985 977518019
    0x30307140f03120a20030f1003022215050f1c060606080103031112120a0b1509121618020903030a110d0e010e150403150207140a0507 59
    0xd80503000c4000703511981803000d0018503000c100303101c51910703000030300d0710444000c03c4440c22012051090710b5104880030040d642c1c002d20703c44a111080d19880520034039041039030300007503000302d0300099140080100c80301c09114601070712041c00519141001103a0410b8907008450b040ba2140300c000079a03140c506c1141c101c9460400d18040700500584803002076800705e4101d503000c2401e01c0010410103a201c51384500e0b4602d41000b40c08601c2c600d04400c8414410102001c40000c1c0010110742c1400d0940c0c01050000c10007071680c103a103c0003111015254126846451045026801d040d4800c2c0c00811145c5040850141c000406030507e592210004001610319400f654244600209524100001e0000c42139031345512140040c0349007054a031200076000d0400300101c2e40300485603a41c0001c0d5036485038604460840032a81c4d03090314103001d03000b9a407000c0c0000c903280160359140b00e1258014411180110303031201c00b4a103103000d0180c1c0d46012000c01071050b0300007841003100c00d50318804101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 977520485 1250 977519235 977519273
    0x41101050a030902040f09020109080601060203030f0910060810150e0604020f0d05280b010806010f0309050724020a111e0d0311100902010c15090b040b06040515030307 74
    0x43d01030f400e5000700703049804003400001c1c090380d175620400543d030708013040c0b0f0020825074009200d29814480700a46038007010b81b43c40071640075500803030900001408445204c80d01c00b00200103040e99580ea00c0d90b191200b0f80703001d00851522414080b000310b4101d9100c26901c2a851990041d1113040c10700c00290700418810201c50001d0100103c0e0300300070f0007028060313101c00c6210f801540000100382c04a06103840d0b4696001e142084502076a600940c0103640003d0900b807401390352030401401d50180c010311000500ca402100c101103141d000251320703507510f036201100c044c0740301c401984180d80d11301d0b0380340d030117400740d402a80c49141510b440b0400c00340227005202000c002145d44804102840c0d54501c003280807030b032a00c0d840000c40c071040002d900c810021410902c181c4031560000703485042c0d4030328040c006018038100c080c020041c0c1e400191030682d0220101c240741c0751a050100301540142c641c03501c900c1c2007101140e180f60708101c1040308100001c0c06180303040819510700c00c20b01b1100c42d80170 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 977521735 1250 977520485 977520491
    0x11a13110d06050f01091203202d0c06070f020d2009060123030405030909041211030301051503070e10020304030c0b03040b1618030804031a041101050a03 68
    0x555044900e0014200c80d0070740d00004140036080a0422040c0001441540c2c1040300d00d800c10404041c4e81d6115201039600f6061200c002c0c00f100702e9042811000b042d0801032441100c450200b216600fa001c00b4030540003030b40c080e02014048401548500411940c5907110100f401a03402096007400d1008a1038801454160030500564504c1008005e0b007020203030076560b0003088503d6003043c5000325403150003460200000401c45c29a094150801c0018404c10341c000300002e81048002c000301c3d128010003d00072662441d01340b405140076140001100001041d00d400641c0c8801700005507416981d0041c140501041c52103540d28982d04000c0015041210b000c40040b6161035004050f4260110340d8040d580c1d450031414070a0030100d495105640c01c5908000300004200003003012504041c421034603160f085030680003251186500c0704190f6040090010000c2040581d10080084a12a41150100c4d8258200c0e000310040e0484001d40005040071000d070240d032107440104500344440c1000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 977522985 1250 977521735 977521751
    0x70c02190b09120c15040611060919050114040f03020d0306080705151c0509070e0c190c05030c0a0b0705090d02090606071e0b010b0f040504090c181b02011a13 70
    0xf1801030317011340850750038034001a080c09040c3c0d2108441200250080044c04107040021100350b480c511400e81c441094000400c0c4020030400303400801401b46815885043e41c1054207140305a038100040490151103040703c081d0816000f40189000c455020f406004402e01d01004d11550100340401030075014010080303071810405002d0444122800c05d1000a124070305425290b14080941c2c015482da0071200042100c00315400d07003180c040000900006101d0200340405a0760344d000c0c000000c00754000451104000c44001610700c0d0098001e0f0101101c903214020141e42038880d0000c056005505218000e001d070608514039900402c1c082c124a02d0040192600c0403100c0442809a102d010b40740b600e40c082c041c92000380ba015201c180e00c41d91404001d120303441c0c4103214900c603090140e503e0302e03203030400e0006505500008000308440c0b0080300c03d511010900502118640ca00b10000003510410a02d10501c1800001c81e043c040100a1024400400805108154198181a844c0d61070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 977524235 1250 977522985 977522989
    0x41709010c21020c03010605150c0106050d03020a1a070e0d03050409060b041403060c030a0f1805010c20070e25020d080615250b070c02190b09120c 65
    0x1c1040c80640141c0303114151440c20b0080c03e0111404206100e6810725405010300e41da5000d45040316041394040d10b80d50226411450701410159001c44c0d80b040304002580141900840c60140c01403141c13141d0603400200d0400155130240aa40304070005a001100000074140500541a244d00a0030440c0c10103030b50359290301c195031745908498103610012030108401c200c1008003035900d200c2140601100d00e80308000c03070703402d002c0142010000d036200c00d0800000103185e0321110b40e03074900d5006500003034001d08005004c1c0110180c0580042c400402c110b20541410451a205000c20406411024505015480c030300c840582440c600a11400b07100c2c001078502d1101020140c21034001d000c1b0110002c9000c3c02c0902c006000c02d0141c1c4e4050303150705540e22000300719800042c043c01c0d903001e159441d00c4402c0306001c04480c000c20091640e003d01c0811034000701051826482290b02400030407600501101030310b82d9228103103004a060014920610740141b03a4442e036a0101c08030341c062540040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 977525485 1250 977524235 977524253
    0x110409140f030a09080601121e0611191110020904060810090302070603020c07170a0c080c121c0c15020a030b21101a030312060103050708041709010c 66
    0x10624456510010f0855a81500800380d07900a1403141c01602c80d07580340080781c00e44495055001080c20704040b143d07129020b0220700c5984c84a411031000c110940d043c202504243d80b2100c00d0154140015503501e428a00c10f501c10f072076101200000e030a228107001d0803180a9002040a25442500d0b443c0100302c5c00c00400c8180d59400780100007142a0415003406814a41a0341201b0205801002041030700000080c10004545c03d14105d2290412040a203604040c94a41b00400d2000c900754002032180001420320405482250207411484501071740660b10041014000705515450500c0c485050003800200d010b82d00900316400c2504180009404aa0109041034040382d0f68170b0003152503062504840320706540031031009610340300024038150b0f00c0c070310560070320f0000d038903903041c4011010085100108510f0140499407100000903040051718001c84990780040d18140005803803500c520380c801c0c0510340055a4000c0514007511440d1030354891007a003410f002440d0005400114000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 977526735 1250 977525485 977525503
    0x6110a0f020f060f0c0a021008040b04030f0e121606020d090b0a090810052505030a0c030b0a420c03020a0803070e030c101d12010e1f0911040914 64
    0x11001c6c02c5030000034410040c1a400308800802084442001c100008019503100e582094140c24a881d4010405d1000c803800c650602100d60404136191101c81c404800107807078940c401400440b49072894540740b040f43d658004022480c0010800b02040009003403800c000c11043c1c83d0b5140070303200951102e00d564a03150101c40c0074100e2030b94450820001d55010a17603090b06000000c0c405103031003403240d0000c00500000c0e0041036017540e0b44209a4210340641e100c0d41c9542409811004481c1d03503405840e000c40550001d19070304000541e0030300116844240031049400326122a030490f1401210200c440c0300d50760b1400c03829442411000c1d4080740c461005180b2601c0144c1c0c03244a02c09610040c0340c2040c0e0340c1041c0304d008a104154020031280c00c0598049450b060a06401000200e400000c8281003043e0034021103520b000000990003401242c0050401c0b813031580105403040403174100301141c403516400380c00e8413110b0b80f4000180c5800c0d0000058580511540b12a070009810900e041203590 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 977527985 1250 977526735 977526757
    0x90606080405010c02150f0a0b151201080102040614030c07020d08070203011b0e0f01050d0507080601081506120a0b09010e06121c050318010e060106110a0f020f060f 73
    0x1403010401040b909002e25800100700e40b01509200d82d110320200041c980c041e00c1c41400e40c52038000100480455030013482454801809820700201c4400d030341e010740e440801903600b52807082002082c0b2800c14000c440c00c03101c017a6518481da01060a000442d500084c001d00c07542c11041000ad40960394030408184001c3c00f9100403680e03002a44101401c4a041c6901d06a140ca9030031700310010507070401c9204440c0c00c0c003500d600111045040c012901c40c41410023103940c452030641808041603020601500c141002c2c1c0b520b40c09038460a107614500004050400e40c0710004111211746095000d4180790400c00610000c03030b80c0c116a400158807041c098100c0c10150b00d044041204a140c90303000c0084c59a00302000d0098030440c000407101d445104046441400780c0000414158040400303c0c00706840c181f4020000ba0290340351141e1503040030b110701800100022140b9081001c0461070401a6900400d4058000016800d0226018442d80040e500442c140100d075902e5031500c00818051542c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 977529235 1250 977527985 977527997
    0x80a061509151409070c02040e0f030d150b040b041e05180601080a09080306040b01211406040e0d0e1903050a170304050d0e03280204050a0b030705010302070606090606 74
    0x40480f40c80e001180212101d1003240c10200b404030044e0019207a84005030150340214000c00c50081b118170300200d654241c807007440001170072464034405600142810364615800058566140041c1803540924080c0c1c901c0030200304010800c0c485a5001c0c3d0380001055140075030003030b98501c00a0000303035185000d520010500b808120b525030740175003030320341c0070201e55001c0055041c0c0d511142031300e00008202c10f01842d5a401682c01e560301407404c06100403900300140c074104403155243c5d0b01401c41207154100c00d1241c0307030100e40300b8a014019040201d440c2402480c00450b1420704403410b001564071075801480b51501c084001c03481c81c150001441c0180000c0c840003c8c6403070303c0f031806800c10400324010344060090000080d000b0842074a00105450880750303d68401d00064180144a070481454200f034020794241c0c01d08101d107491400b8001c403800c001d159109a44c1e0070903170300b040c81c46a516421980090045600a034080d0040d00d00400c000959039803941ca00200311940c0c2e80195000c81c1c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 977530485 1250 977529235 977529239
    0x60f092c070b03270714090613090f0506060105090d06091b0603021b0304080a0305030717070c05151510090905090106030210090510121812021006080a06150915 71
    0x301642025444160200910903030740703030000360118143d070440014130508400011400a81e1030500e0101268901c000422801c00c842ca40a21111903408007200c540c0101400903140358014411c0d01e40c084c1014101c64199252a59180014440501c0403504103480030303c203c5590300518081e00103002503403801aa01d01288150402e640c814000b501301d550320030003080c002d41c2800304920392407036410f0416544980b10b5102c01e54049010070f003207442d5280340208000d943d6038050103400c151401030041e141c41c1018001d02c0d0307010101c129200b01c000d0480740465102400d001e40c400c3d0001049242c92100f054540500506645c1c0030b82d554083e585d1150f405206502d8850341346006280103003003101c8464689400304159a00311121541032200f440050f83c00320380607400a541069a48085007007401103880c20140d245502260030340140303e81000f1000f200300500c075007000d880800d0b00404d0300109030360390040544020840b0600c1c01d10402c01c00510742a46000b8520410314840f2403042d024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 977531735 1250 977530485 977530531
    0x40201120504120e031903030525050a14190806031603050c181e07050919061b0f08070807021e030105150603061e13060f092c070b03 59
    0x1801c0240f0a21030b1b01b0000c8010070f07004888180d400c2039030341400c000c60140c1d1140000c03008410840c048003a988030380540d00c004541d01c1401000c5c0c1c0d82042d203400d10b03203d580b00e0040009014000013194a00d1a110901c4041c602034007016900c058001e044031006189000ea00144c2641d60380212079540c030114803090b0720700e072000119240c060b07d25801c0380140352102c8003805d01c00d41d1040030f0301002043e10114120030721400403125142000360241815a03a10a4204400c0c80103206400010704200c401122480400302d07211216900041749405208080d100c1d100350b43c0c043e01040720b004104005020068881c94212211440d00e500940c2c017847c41a01814251034000300031410146620241d0356840da20b8005480d000181528041601e0b02401c840500c00700290f0380d45580100c010b041080e00f0800b41d0421130549032545a04182c0540d900241001e44120019210403e58150400f0403540d0900507000400d00540045841440e500ca5210b50194070a803565507981e141d89070220380003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 977532985 1250 977531735 977531747
    0x2090618030d080412030c02030706090503031005031603150e120403030e0303070c0e0613021812030c030f030c0403170a1e09170c03070617010e0c04050904020112050412 75
    0xb690071400d103c25249002d070f803184000200b40b0740103410f155445030310303d260601c20000e49031803e0b030003441000542d100381001640c1c1c1c0c004445102074070450120110311420302042b0000c052003003156070a1418210380d540c80c1800c40d8101d030f1101007952101440c2d100070b81084480c0d980c15940703d2140da130b5407c5040041100210386840d138043da10403c174481c0040c044ea0000001c40d84d003030065103440e0f115040012366610008990041c510b0000c100784040808400f0b41080d000c201300c85908502d1020a00c1545901032842250080e030001e00c040030304010804011540012815005841c103500d0f9035450700c8503050240c0800392100b01080000c003a070b82028000001103809a01c0c07400c03007004d0b100002d10500050145201304039502c50b00c40d004c050100126010520700071f0903200301548400d0000c080c00002008280040b10200000401100b6020054000d81c040c0c0100c52505042c0001c0c850a514040c104a04000402414142549980c0b24250086105e04114a20b051100f0001084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 977534235 1250 977532985 977533003
    0x190f05100605060d0509030d05090706020c0307030803010e09070e0403080a06090e1c09081b0103050f090604020d02011713110303042315070503190519120209061803 73
    0x401450004144115503d5100b07031202c2c40f00d0b0301e401041c01c0d80d5403121642035028108030b640d0050b0410b410300070f0516021400c5c5041e0380d01a401c941010140e103003055690005440090100c21b070070401400880c00046000ba400f150440c21240142d40da18807003100301c90100c505a0000e00c07070320184041301d40240a000c00410075a01c05002c03d83c3c104600f19110010a080c8981d545410020000c004d80900038910045c44090706540001c65003000c038426403890800c2290000389071500159008002d032083c2802a04014010192a5169802d00c0800d80d075541050b410701c80a414882c8041d0001d030110f920401c0d40044502040c03206223881e030310f1400390840751807003074005104c01d011a010f00ca4151407088030b2400c103c0010034895010903a000c170300d844c0002020320006013001c1072180020041010fd02003110600d000d01c00480129100d0203425041030384041d80c1112100f050f0300c5900104d1000600d4400140b0781500c800005050f94002c002074030084004020141040c80c061103d400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 977535485 1250 977534235 977534263
    0x8130c081b010e040c020309010c02040b0612060415081c1e23090d060209060712020303040b0609010302010f05032701090605060303032505122430190f05 68
    0x100c5050540070181d200e018034412350f810003000486c0c600540d40c60390410034a00360064a00c9688440045001424070811144680101e041000403000c0d1030501e00c8030000c551160029001c0740c84600003112807103034000d040700b04200c0422540c1c000441e01c509a01c1e1411403076254816000005800c9403080e5410103040b20280005120703070002502d800d01c482c80210350001d00140d0f12090040010340e2409280d01c0a0002400410b4141070150004001d5000314011020352100f0340d1034804201600c1c0007400001c3c001201155a4146d4038094805160004054071081200741d41005420a4501c1c03440180d10403691076411107014801c262155582100003500075515600e429404038502d0721200311a00422031035145901c240e01e10610640d1881054000e0a502900345564400d14151444a040744103031248105000c06150001b9500918003d500030505109611480600c00f200608800e540790702411810003442c1c806035065284241c400c40e03800440b4005170400d0361400d070080398261 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 977536735 1250 977535485 977535491
    0x1b070210030e0f0f060106140d0c0f1707020c0103020306010507061406130e03030c1605061e0a02070525050d0f03030e210307030f2c030a08130c081b010e04 69
    0x2c801c1d130b400304609045d1422818406e0054001c260110f01620820154014541c0b4143c0d844103c6035121480144001c11599034000341c042480d601034440e0402e4410801603804418002c1c40381d40643c019607403268050504a007001003e45448096411591004841507045d0f020410301d464205010946049000400c01010100342062a034910000c0c0081060352800304070200030000401c003d48800d030344001520600c0c2800d8140c100c907000d080004c0020341c940c10000901e0118544242e588254220006140c0c80d1351050306038000300e080070303200303c3d40704044100412941c84014141c90124454182c40e4007845043c10028129a9101d00f516429001818080c1c0b08109030210342021070038010159031780745c5614600760020207840140210041c14001006440b59840304262940307a60b04400c1c01c05154450400c607103d00c9509003410201c1c1c8090040340030080400a40c01209100f02c401e12040354840134498034007420f240c0e204040c08203071340305a041035902541c02c103114042aa824 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 977537985 1250 977536735 977536753
    0xd0c021f092408010506030606070c090f0c0e1e0a0b0a0203070506130c0b0f0d091a0a050106052d1b2b0e03070f06120b0a08061b070210030e0f 63
    0x5081a0045c80b40e41e110b014088085400c9984110450f010309900002c0d0800441c2c0c0c6030200006880315241c0004e951b40740c40703210440140a00041009030900501c1c80800c00201c0850000925400c8559900011141800704d84161440014922000250025911040503140003840c201c4010041c1c1040030912003050300150708920f8000550b03804101c01e41e150500486800c0c201d0041418007000c0d5401c0c10303100c50500c00407070045180c645030b40c01d80352003581d543e000070000c1d9003080c4201000280100171500c070a070b02c480c00d0303840302c550109156004000308001d480e00d1078018a01040a20034590400400801c08000c155070f500c00460016140d8502c1100a4150707129030401c0f08140440c1c0d0000140d580e40c02c2c84090050118803081d02d00498480c0401040c0700741d000c0b24100001c0c50f003007060301c2a14001ca200070460b00188020911559036402c61643d10001520b84c424000043c02480010383d114032040740e0b82c2c811690b0010b24440d03004900c5141668100010071150406805 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 977539235 1250 977537985 977537987
    0x10b09190e0c030a0e16150201051b0906041517070c11090405160b04080d0903121b06090f0b061905011b020406090c030b060c0d0c021f0924 62
    0x14981d11403050702e41c140d1a40d4030782e05044003404008092a0060144841c544d10741c1203190310340703420359180d41c12541c1d07031181040069003200c03810748003148162801101680700c1c7c800c440060043c00805004c00e420103a64990781d50740c05040e01802004550f820002403406000d00c01550f500c28081e00d04012592103545811104504000c11180200101400a01403081c104140c5207500302c036040000d0788031b0ba0f45c0c541c4101500311b801841c06500910b0400002c561156904c0b006a03500842ca40001c1000f00d00196400100c101c90412164004010b0001281261240201c418000c0e00d403d4181462031030002d01c4410000c3c00f0a210b82c0824820187c92020580240705444080c240818a0301d110a5115402c140140d0000d51041c00c0c0000400c1d1704465400c110000384203a1030a00c0040c01410411403140a425050080350b4440888224602d00c900d042405450000c1d140d0b4080c004141d01030790120890141002c0440e200b01e80801078016540c040341c00305911030044004081c03480328 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 977540485 1250 977539235 977539259
    0x30e030f211b0d06050306041b12031b1e0507060e0d030509040b060c100f1407050d0c120f0915060b040302121005090d0f020303100e13020603010b0919 67
    0x41e40505451000c0307407521000f5601e41c05007026240040445000d468603140180844020185141c0c0c0d07641c2c2800c0c0010356080b00401d000c4120b501d51101420110072189082a00120b00c1c800c0d1000e0780000e9918071110002000c0c08036241c00340b009444c1c00d40c14100081c00c546040c5603218003800c3c40d500c01d040841d034080c003070f508801401ca41c04604030480b039000a02d9405941031500701401004080a00144c3d603500208000442c00801d005400c010f40c000c0d042c0c10803c490105c04034004001c001d505014640c000029424075060480f5008031030404001151090003002c0305440d51190200309100c12420010010300c0c41d48001d101090a003040d030aa1805103100c003e0007031007203c4402e40e0402061003842909541e805080001e0f103800300841d82d4035407480d11000d0101300d80041d0041c0b028800310844c0c0c811030484040c1050719140416148520400409607144000034658900050781d41400031030090a003680d03070700c0e255244981001780303070070064422180119445000f005030307000b01d00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 977541735 1250 977540485 977540521
    0xf0f030809010c1203020d052203080a090c0e273f0405120a02010801120f0b0c030a0b0a030209010614070b0403080a0e0105060a030210030e030f21 65
    0x8000300e403030380040c0d401600c645600441c020021500c400c4610800b691641c058421040c0290b8240f100d44c88413007440103180110101500c10003522007405000c00d0180e026070780c120300041000a21004c0700d031207085000d40b850700041e0f8206650401c1c46103294054060300d0340031948400101009004211040e950095058005e00090048520800c0c0c0c00c090400454010240c804c1e81c150788218000b00a0f49a00034000c40c1c1c880c11168140c13034184d074000160000c020713034180c4801d2201c0e400c2c0729801002e14150402103909010504042e070019030b242e400706005020b5800169182d0600d40003a000b80c0703404070501402004190310410150391101c1400d411521642040500761212400c00c5809101d581d1000d41040b076801c0c1400105a84484c4a80c0302c2c805000342007104181d8110030900380c44060311100e0381300f0f505100500240c9401c6800d003200610034100050b4080184a00e07038115007128102d04d02c10b4034041a402003103030380d0102e04044407401e42240c081c10f140402685026038400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 977542985 1250 977541735 977541743
    0x120c06061e0a1e1a040e0f130803040f1b03020109061701300b0901060605160308150a03030207140901060f0320030109020a0e0a0609030803040804031a0702070f0f03 73
    0x7052043e4291041e1074128400382202a011825816048214905551191180c0b004804140000540e5640a541002d02400c0500c031090100402900c2d0100d254001070800d4400200042d5050006800b042c2000701d000500e404547c0030a2540c00054480442c66100b501407040c40c03008c07403d5800d1046035460541703a0102e04009040c100004580c42c002c8018000003c1210301d6110000744052105c0c0d0310701c140c0c803280080c00541d0304c800086495000f001210401b4050801403240001d004030a403542c81031614440390910b0501900040c1d00c000d503a03000742e001d604074000a10124002c1c0340402c83d02002030300d0791800c0b07507d0315600401000604641c9020076075595201000459103080b407640070a46841c2998981d61104180e0000b54800641103000c29a120400c3d07001c5d0030000b0500c0219070143d11001002032650700c0304040b5a200a004842c1001c0800000c0700241c2c1000004100000d40c0385148500d151140c40640f41c5515034000044e0f61809030030412001c4a03481000f400d4a43c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 977544235 1250 977542985 977543009
    0xa0501050120120f07060506030109080418090c15020f12120408040506121f05031002090d05030706020405120105040b04020f1f02010c030c03050c070b09120c06061e0a 74
    0x1594582d040c200d903e10000c10300400090f80e6404035460304060310039180181020420368455104041c200c410b0355030700a141000900c410401410300260059600050071404601048146d60340f80c02045075400981d000700d0100380c0c80e125150304203c1e0381c403940300c41c000424214520044000d8030707001d01a9003000c41031800700090208116441030728002c2902418141d100c01445540d14600c9808031080c2c2c0d040321842000c1000c1c1e2241c503100340201c4001a0282000e041c0315981400a540700700e0b51650020600840b07900001e504000400120340a140c0041c3c0716030034403040004002d80b01d018002c407a0b0400d001e00000c14090000d290b005076040301d20300b20110482c0c000c6503803c0c800c200f0041c48200c0328000c00510342d40640007402d40c10722070394003042446d80710b138029401c0351401d540c00c2a1503034042c80020001108070903125088079494007118184c0c030303c400078414164000080400b06402a0b001c0c8800c90600c2c1803500d50903502034030590147c4080c0c00200f0701c803e00c00d115034000f02074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 977545485 1250 977544235 977544287
    0xf0102040614090d020909071a070201031b090b1b07030501140f011508040618031d03030f040b09030f0303040303060f0e0105010f0f1b260a0c0f02040b0a0603140a05010501 76
    0x141044501c000b4243c101c2038127000360051040440d82d82000d40c0a901080c01c1600c11407401c0708500c24041044c0c0c140d198120203a09100d900d80d920380001a42004110145c0306009440c43c04005c01c00046216000104050701013030580409504003902c50405080003038018054004803041924a17208645850a0b0079076039030078080060183c030074480c050200344000358018141d002d054a058001d14000b00b1035205140310a06035684903442e0f5015002d031003071005210a414882c024614190024111560180d25628480c1035a005460850100e0f45c1c40070300300039080e461b0400400404100861120300d6151900180c01c0d100c400c0401401c00425401d4450854095101011021400142e0482803000c07440d04400f0401c0c8881e85401c00c2c031a409040682d03502d4007044640056096441020800b1360f0b56401102005801c03040342d105840e240225903586405446c1c3e8000e02140d40c0101e288024961510341d030003000351040269609020042c401039811400c0c1c1845d00d00810031000c0302d49 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 977546735 1250 977545485 977545501
    0x7090e0319170c070c0506033715140109301b03050f03070515090307081201140a1a071a04061b091202120f0f0102040614090d0209 58
    0x8004080c0082d0581a0304050040c0b0340076240c05050f030544601040403040e82c68404200280c04100d030303201d641d0505081c1c0c41950000c000c40d10380c840104030444002d45010b0021542c1a03c031101030800c120541940704200d05403014440c40903e01e42800c00107445400d1035000c82541080d1804c0f000714568103162040d19402c1d40c10112085e5400c4010340c401c84c0c49a44560304404c90320700c800e0b2401e1180c040e000d04101008821a070296a0080c02002210550006205d162a005016607800d002c00c0c0640d10201d64804000c0030001c8070005480e0181d030501404645244101c01c02038000c010406050040c010519200f403d042803031003e10743c49848a140c580ba40d12407400e00342e0a10000f05003480100105c0b90805401414403400d24070010341c0245007260848001e00c101c1c4138140003202d251016042510f0490a264050030960720341c0250005d040346070600c40884d004441c0e43c0014104001036200720040c140f0f0108961103841c1489440014528036001c1c400039104802c0040401c03c40c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 977547985 1250 977546735 977546747
    0x1109150a080a0b1212092701030f050a05010c03090209160e060d090501020f0d06120503030a0c1b0b0a06060905010507080c0c18010306050106030b060d0b03070506040e01030507090e0319 82
    0x303020f1400c120b4041e41c0e8080403000140d040740441d64054001070f10000303000920141e01050108251400c0700c0680e12710745603a81c0c02d203a1000c090325a400b803828011702041c0d0a0090000a045544000c10095090b1050120110004011404000c075224842601da6031142c0803440410f0b0486000e0b46031690f890801c0c006020800000340290b10024540c4a0f18056902801c401d889000c0d04006141da101420a40840100e0000b0206d130400c20000d40c58803c3c1d070b03000110140d46440c1841c4035020300c6240000c7d52a01c0082070b561081c2041c20407000e41e03150301031100078003040c0c50840c145600c6c0c0f50000c0c240340a0000000c1c41c800c0042035011065208205c00684100c0040810320821701c50100035245013401c0c04260f5020b4207120000c14054000e00072900d107044094203880c9002d07111150b0030000d040640405a0500520000240030b0b65484098006413a544586103c0c651541ca041c502e001042d0703000e402194100444803580104c0481900c52401040004189030140b0103400c4400c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 977549235 1250 977547985 977548009
    0x100f0612322e0f0605090105062d0d0c0e0f030115060804080c0d111005010b03010506070512180307140d02060f0c0a081c06050616050a02041109150a080a0b 69
    0x9043c030388000c0020742401500800225002500c2c6a41c0a9880340c0600141b4410102c036854105403004075040c10071219210700382d02c12405074200d4240803605030020140c0d4034100e118000100d8400301c0302c415207004a42c076414400c00700d008010b200c0303450441c2c241581d060300c41d010900140c1000641070048602c101c50310a43c1c4241a142801d03880c21002d01001000c42880086202c0c030512042072440d10700c1a40d050710742d11808a4110380c40d00c401c200582d807000c8001c1700c40303009415442001e58040b2006e810350140d014252520324146005052528000386c0c03003100c0d60142ea18a03c0c4c0640c80d143d284080d640c0d0107449031035959042d500405014801c10b102017441d80b02d0340b0349034007e00c10088054070b601c502c00c0c00d052000c2600c0c1c0300340d4016129540501d03640303c80108001010300d00f241c41641e20342071103034081c3d541100791a00003600312410007641181a0400260092882c5001c0c0d40041203540380000351400e1070a1660300900200c00142255040c90340c881c403400c900d580d20000026 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 977550485 1250 977549235 977549323
    0x60705091f0201060e0702010c051803100504060b040f0b06030103020405090a0b01080a14030306092205030711031203070c0f0c1503140c0408100f061232 68
    0x1501c1c1900000f07008005900c81c00074803c4402d00803c00c0c152045c018a0601c5101c0d0f5901d80c01d02d104c842c26024403010048405d43d1502c100d00c0f02c03000b1003040d030040520540c0582e0000448a03503d00a000680d1074821030703900800d01d0b0104008141d92180c003500e0550350103030340c0003400340c4d100b070284d500e0a80000c102801c2900140f000003604000000c01c0803445220780c10364142c0401c0f01041d00e640f400103460050340a80e80000044203d8440d18404210b04220003404100e6807261701d1305130544d80190801d44a0390702c102c0f00c094440c1001c200c00003a030072074110b0b02855460010303001040120070640c002c26866030b46040e50b0034081c6c061a000003600a041d011842d480d600413026000704940c809010351030401d90001400908804180d0f011908104050401c44402c0d44003900141600203d8a0380d0640d00d031800b24080404041c28280f86100d00080310311380c801d403130100c0c0255180d5941c007100001041e03c0d0100d84030f40454141c1d1703580d481b40040717450b44030050031001d10034612a0b1540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 977551735 1250 977550485 977550529
    0xf05031206030d033e041707060203040807030b0910020301140a0f18050c0c0d0203041404050421020c0405070f031a06031803041a120f010806070509 66
    0x8100c03035920420a500400d8100c00711240b0302000b140540548140016282c2d41d802808544010220020403141c0c203810000001450020f1700c1c1402150b68100344c201e854078400701300540104480810140e00a48201c0c001181058903001016960b0303240c1b07000c0248030000c04008240311540802c100c1080ca400d01c5020764803036850301c0c070040301070300321130381c0306105480010f40040c91802801810782a01c0f207404904a0001c0c449941030044c0401070510080344804101d84801c4c1002402400358910380c6a01035070b0794920f0040c09180201c4418616840345140c0002c0c400040c0383c00e03014001640c00781c001070320810141a000d90038852128200764029003004100464581d01035818240001071f502c0c1080a04402e12070000c02910381050145c20090070004106511440c003a50340c94412003400b05c80c503003901d4501440403208a55449034803030802040c1042000c0380b152669520581c13214a0301c4141d852710340c4d01552220054401c13424481c0c0000c04c198181c03100f00c0001c4841c0040c00140d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 977552985 1250 977551735 977551747
    0x1413111e18070815010909090302030c010603050604030215060120010b100e0406210201031d0a06061701050402031002130b03090d0e0d030e090c0c0f06070206090d0c06090f0503 78
    0x81456804200d600340c0003d90749200103600400c030300043c94541d56040e59060059030034a4128030081c000ba10040d82540700070710542d2800d480034050a0083c5d40b040d800b400041c1804d00d070107482d200c0b0b110246c5245c0c00195003000500c3e42e01810180c4000703840245044258189000b0030f00420001c80c0c00c98101507184071520b00141c00c4510100d64010982c0d04200c05a80c2e06030100d40c182c80403206442c01401c074403440c40036600c01d0b00496020140c2d0108c48030000382e05d004140c90304945500403244580c031780e1020484480c0d5108944440d48400c4002c0c001440d05500103512481860000079500b0381c080390700400384020f43c13000e102400004208995a0606525403a500e1410031000800503840d02d840142c64104108080c1400d81d16480c2c5205002d5400104003805000521540030030000740064551680100035224500c100500030b09090b0a00760340007814144010002105036004114401e00d15900c000100041a00040c0000f401045860031080781401484050910320002c01c0d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 977554235 1250 977552985 977553019
    0x60a050702041a03060601050424271a0a020307060b0402040e01120c1502030304060e010b10020a12180e04021302070f020315070c140304081c080f040b06130b131413111e 75
    0x151000740d4810704183c1c884c03440f030300c44201c0d000d1040c107241d40d0040c1c0007407101c180000e2854100c41c03006c80004001500757140d00c036031904030400d4003684001e00803000f014230785003401800c40c500000742c404000000044460850040d6981c880908001c11140e035841101d44420805e40c04161401c400411000103034812080c02961040f0149041e1041010807204505507030142c00c0342201c0915080400007414905148261761300300c018401e90b00881529154500c0b500648001c02c0703454403500440c155001580141854101c1038001e61840700859014808169001045104a140c0c4021103541e54680c500000b07045008541c0078403a0ba101d08080c00440d45080261240040c2d4903a03600d03031443e82e45541c1480c2d40c0c1e07400d640103020403014001144d00c0e410660b2074254804001100840d034035a4034030100766540440c2d5045110107130f0711040c03004280400c2280380d030040b400f06101c00000c00941c42d109100003070100040d114118045c460301110580061402050788001e01d440c02d40d00780c1c940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 977555485 1250 977554235 977554307
    0x7140a2a080f0c12010e070f090b0409080913090f0b07021204030809131e0b1002060c250b0103030e011101020c0705060a050702041a03060601050424 66
    0x25000c1010a1246404100d6460001d200040c0914220040800564280c20720542c10321140300300000e5500c41c40040800d01d0100140c0d0f000b00380c10301001c0302c2e007031400a41e0011150a8400a44503e05042d240c00224080c602910b8181c0d004482d010402d042c4484403200808080074020710192042c0c1610003031101f415205842401280c0948910fa801c40005803107521550200800c0014140a0025681420071000403e02501000001c12100da500700002d00c072512000040881d85900c0405c03904d08105440b201428540d000402150500d80101354481c081d00f80c04407000f0b070910302481100103014558203011900924405100e507102d003001000303c18050491400304500b04984000144144211101c1c0391101024041860400381004001c2e071000700e5500412200340481001b41e03540b4454405210008207107407140c903102c0d005060902400800890510400788010005580541c002c00212881c161665503062030f02c0605803005001d201403801d030084e08132070610600f80045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 977556735 1250 977555485 977555543
    0xc0b01030803181212060a0602121b030c010b1c1a0403030902100c0515010509070e27040506100f0614120103110310020f04090b0a0302060f03010e0606040b07140a 72
    0xd00342052980d41390700340407c031445441400010b0b40490315000c64802d422010304101e1401405400386407400f0301c42945980c1041030340d6029079550b00c1e0031140d5450075992410f40c40d040c00420760494061a02d480002d00ca040700300d4226040c00740c0000303040600c40e610407a13640341c1c01010800e01d0326074060000c1600208203c11140c5215918131484034801c001c3c0e141d0704a50000748000072503520000115280b0440c44c1c01d55821103180030b82004c85c43d210303620301d100c0925580790701051854142012441e101024101d807031031403940d0205000304100340340031300151441c0d403d041e010f1041d4000d00c80302c14462113140101804102c00040b0400c9240f000c00000c00724124211500740700201c100508a204070080d042900d2410001000940200c3c1c11148201c42c009045401240c4d43c0e4011071030550000c000c09960030800001445903a964200e1180c00c60300c1560300a040a080402403803c0e0711a030788010300107401e601c04010480030100404484954010920300d030111400c00d07500c003049211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 977557985 1250 977556735 977556757
    0x30103110102060c0307320a09050a06050405100210050a02030103051b061812010228030612060216061104061412010303110703050316120c0b010308031812 69
    0x2500c00d80c030039031000480394001d41c204640e03a80f460b25440000d4500500c000540e024460302d00401406002041d920306101c3c040315480f07203650b0489100020b0a50000d40c10240c8101442c0105100c92a171000c1070345c0607244182e42442c0c1103000404140e1800d00c00e03407100c0c06858241010000c2c1100c1c0303038019504a0384a60122480307013142300c00b0b900307444680b2054990803000c00d120006115803849240340300d49401400f4000c07288216040d890990b44541400242440c41a04142000c070100c15440d2582420b480c0c200002403c00b002049511103808018141c260041110544040d20f10000c889095001e401080002d00300700312013180390810b109d1240421140741c41c541c1003441c2c8808440001c40e1013224141140e0a507681510714582c40b032601140c6205d02c2d540400040c034108001c105801d107100081d00302c42114a4515002100c00b503e8000b0000700c0400040080d0840c2c0e1118103596101071020740325625000212014200081301d11170a101e103060342104246411700034611007000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 977559235 1250 977557985 977558003
    0x10c0e030c13050a020f2205030f1c030b0414040605100518070201020f0a02060610030603110d05190614011406041e030c0e330112090204050c030103 66
    0x28240405032125198096940c100c42042e400d00d80034082c0e54485a80001e919100505026401d410501c081e000309030740700d01c003500340b5500ba1b0200c2e0301900e400c40101000c070010b02445072aa07003803d03141c4060180307081003140340e6030454280700c0c007907045904074440141040011245421101085007015a41501e09501e44804106119000c0100c41d0a0742d0001c4c1968001110b5a0100803c81d90018000821554244001140584440003c010321946e1b6402080380b410b0013404c0155004140ba240418985404010000a01302007c0503403050230841c4c1240640b801810540d003441c0300c21170070403840311200e480752007080025072185940013000b1103030708003981e2502158419000c0204c0c00b181c0c442e2091004014240210045400e40e142e100061415250b81c0c1d902c8140e000f101350051102208544100007480300484151140c0f407400d01c800880503e030360300e28503960030f803e5181c080c10850102c6c020449207986400c0710340744550181c420007141c074000c031030811250400c4c0821145910 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 977560485 1250 977559235 977559257
    0x120604120201290d0204021b0f0303101205250e010b0408072d170f0a02151303080a0306061704080d0218030a1101170903031b1308010c 60
    0x220502c00e541c5140032018901c0102c18030040c2040c100544084810b0b800f44c0f4500703800c00142ca0300d00181810323040004503603030070843d090001401c0080441000c4c0b0b80c1e5105000b0025690b00c1c80068404403001500806108807587c20b000341042a40c1d40300084904404800c0c146850101c16208211101c0340014ac0c4566200c0c0803c03115886103104021060380842814801c0100540250001955941c0206080c3c03101d800101c1c28038020798403c2c0540f015000355640780140070b102081c400260720b0090080c51003a0707800140001364480c61050807001c041480c210800b010318110014540040a143d260000d040006010342201e0085400080150b41d52220144444003100c3c047c0d903006808a0401c400e2003a0300303000350410a448840a21442003e881c01c2e1010301c8072031150b82c000c00c910101025044c00150841501c444050708600b425010018031036404001e803500a00c00c860001c80c110068818015940507000c4c49840300d460441000404160548c050095802030792683c1d0700d020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 977561735 1250 977560485 977560487
    0x7060e01110d06081507051b010e0303060406120203150714040e01050f060703081906030206220b160212030712080702070e0c0d0c090f1806141c1112060412 69
    0x4403000c504170312002020804525400c0c0144040d29848010211440003411440e0030316003500d14140c0b070303c00c03a42c000000303015032420f01e401600e01516596001c242041e01d9a40465515a031750320b00c0c81e26840c028008078401a2003000106800d40328207041549950300c0d0311108003807a000384180341c13080003014030482417410010142c640782501134070b03028441d80da07401c103418074040068050118203549810200050b55050041c098240c02104558401400024803888003000c54004584800c02400700400400d5589003030070781140d040d140d001d054035140350010301c1c600661340000c01d0403501e8664001803690003140c242c815403160342111034032940c501c44081c00450994020161207000c22240388130a10f81d030082075141c43d45242c2a030340607a4410048142c015560000a072880b10319207400c0001e0028081c4101501e1000d000c22034204002002858141080c052541440503240d05042442181040e0902c649009002e850030005030b0030304140c075004201c03411900e91201041180c0f0392 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 977562985 1250 977561735 977561743
    0x110a080106080d081e0903070210030f050121080d020708190e09011401050c1606020304030510060501020a022106161209031b0c05040e0102120108030702060301090207060e01110d0608 81
    0x101c017800c044114842d103c100d0b8070741e03141004008000902c02041200d00503110300124540c044102d41c0c00248280d01c81050400b40c800c180e04c0f914201c0500340c40c090002c03918203a00e2040640c40b0303c0700307690380d51a0031541029016004000e1700c1c041000c120b101074111102d0002400815594030749111551076403c01403a85400e021384240003000d58510301495014100a000b0b000c14030088650071410b038088502a020f40e90802001a00003082c00c004004080094014002d043c460a02034a414000002c0d039411030064003030702ca11004d00100768110b101d00351030803a40340c0c03041c1514614502900d80b03111003154182100b00082c03c0ca507420f645030b4000c0c4184c22046906a8444405045e05e000b00c41070140210030582d1880f141c0318000403140d07624442c0504e4002c070600091707191354818880c2c03980084164410705054004104000c0141d0f0f90604030380c199090044016181c0400b4109240101600134050600f90728199202802d0048403014110200b0340060600606840b03075180d40e00c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 977564235 1250 977562985 977562991
    0x20312030c070303020a11070f0807062d0909050705131e090c020f06010f0e0f01060207030f060b040c18080c0117071107030803010f0e09030901030504110a080106080d08 75
    0x8000700b4428100001e10940080007800c0071890150039000d0005000c604000c0f09034131485000c10060780c1002804403e0015000810140c140080c034040595009164000c0380d0b98440b00440d04029039154141c06146600013500410320100030f24601100054000e62126894036418031030300c240050344034000149403406d80da52600740d400d46441d11000c01c0103800d01103450415030141d8000c80102e2001000305500828841d0400c4075181e29010004024080103428052400714490050141c0c0b9000520f103000c80341c2c01036800c5406043c500340540100380d00458503500904260700f03c104980c3c81009e0180c1034802300f078041c0301903560f80b1005940346041440203011440d410205050800c1220030341d42c0c0000603003440d651a043d480195400d040b41c50f0402c42d4207280c0400140211400c1041d503901401c180302c0654202c0c00d00e041030715500e024911046041541300e10014003081201e928a00242c4d402030001d0070700c1c5444019050180800e030190a0580c404c0b0641d840050317100d0125240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 977565485 1250 977564235 977564251
    0x1e0a05100f050d0213020d150302040b010504030515040609170a030b0102030c121c02210106020a020108040f1104020a0207140603010e130303060e0c0705011a1f0306051c02031203 79
    0x500380015800c0c040f021140031701c205403c84d424040c031001c10405000c0ca140c51154035090718015415481007000f00c451000b0a6810800c00740020300002d200000e840c43c400c1c405040c8010b0659444c60050003411501d0401408001c2c4140c000c03481d120008080c1c4080e25980c0c4051041d01380b150b004a03541d02842700d0803551a4008120716000261800081c2800320f0020b99807002c5409042c131b420180d900514114401124001070038040144104000f405003006101405009050781c00090131104043d00141041003813000749000c00c0b000590380c0034143e0b000382055498000781e0301c02030340b40c0c4220b02c107a0840ca12881d035404028030700703402100c0c141c401c03c1040c681d80792aa880390110001c150a021020f00d40d50341c0c00410715440050ba402d128081d42c0c250142d49000c6840c1075800d46081419120306000e95166040c0c695440c2d5841e00d86044040d000242d40b603000100c2100505803e92116800002e00b85015000c0c400e09118620620300a03400c850041d1a140d0b10303030b08184401c5a070b00c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 977566735 1250 977565485 977565499
    0xe010f0f030b010c02100203031801111b1c050c1002040b07240906050105130b1503060109030b040b0f1b040b0a030906020c010c12110405091e0a05100f05 68
    0x140d0414003aa0010040c80418035041058082c07035070208111070540d858480150b4404410441d00c00c8000b60380403082011103000744002c0d005081149154064003003500b0704030646000a43c0030138010132490006682c00890540b241e80e8a15019005a125014a083d103004070080e100b203800703850007101c04032f4030580401881c1151584418140b081f003c0c4402c4280d03050048480040c07a0240500308003a4007428000a4a5243c80104040142d00d407010481560070011840c0c155506c0ca00450500c1c07541014260340c3c0c0d42e42100481e10071840da0001006908618140402c1c881100d00712840f480145881601c561188241c001031140c1205260b048080c042005106c0240228080c00c0400c0780d504021501011b00e5841c8002d07604410300209050703565040f1124802d40c00120707665802005001000b883c01400d8104480384554000c46d0302800c822804251030344198501c540102d4040044041c0c0b505100030b0403000342109a03035000b01d42c0c40301d010101d0942a8044040110341c401820ba03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 977567985 1250 977566735 977566757
    0x10e1e0f060409121d0a060c30020c130e1905010f09060b1e0a030b040503120709030c0506090a03230304060909110906070f061b0f0e010f 61
    0x32001420001c10030703508903440381e4104000445805940e85250314070b4503080d001a1840d0a600c00208441d403905101c3d00215030200016900450b8145105401003442d4903600d1000c044060710078891525140000000469189a1035010603001143c00040b2191070041058011b00020b6412181c1e640c4543c0c0c1000122034031003840012100a2a0b20901c0082000d543e40100881240c106613015100786444d240791821a141140b84111988003015804a00c4042c220119a01c0c6900e4000207104601c0b160120342031040400c02c0c1d44809480c0c03019481c25241c40c1c070303000304142e0a500c0102c032526001e884c003103a585050000c2e600e0b0500e01074150300c82c2c6d41c81c58441e01242107010003480540700070035285e0000c1000500052015041c29100c014040340380400d02e0f422586000a00c21503d0303424007910040750384d5001101d042507040340c004050201103090000003401901400c0300075a07441d02d100d080b1190000400000d030b886030344a00440c04103030401036507100c50007003807030000800720b0b614 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 977569235 1250 977567985 977568001
    0x51509010e060c0129030f0d02060a2304110a0608010806070c030c17040609120203192409030e01050703080105220608060907120503030a0f09020315010e1e 69
    0x5003d00c004000000300f80c5d01c40c050740b14074110481082810030b00c11a0305050340315044c01c21050310a50003080c000c00c1540c00c0720000a4581c0b0b005480903100036268105c00451a04015030042c4840c500f88070020a0b003414130700080500440f03074005014414000d000203555008900040c100e52110016207840e5072442c10455006409540890902c890382d079441c00030601c84c0e400504401c01c04003205036102d04040c4003500c07810302a402000c00d81da100820000503100800d130300341420500c600301d03034004d4054a0003030450310502e00070f000342041851f440011302c2203d8026480c510300a40714a409000340c0c400454a0303214071200030340855290f40041206051804c101a0f441c002c03101c0b40304e56000c0c0300c0035203c01d45485511107080c0360f10a4040c07040403201440824000c01c2a1142c01690955070b984003601e90200500c803684456560031800109030300b0b6003280381440c0d07004060b185c43c40040400110341d03000030b02a001c22000284000f030218a074242028480300d40c0010060b92554961070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 977570485 1250 977569235 977569237
    0x6010f0302060322030e040e0a1703091e0c0108070503010e150303040b0c0105040c0f030b040305090a030c030605070906090803040e15030f210307050a12110a09051509010e06 77
    0x42d030048048400e10030f102009903c2c1c4c0600c0014032980e00c034010040e46100f0071041d5103444a03000c586400041400e0700181e0585400c010000301194102c2c1c0740d640d01d800c45c9082002a103206072100345040002010b410700481e0310040c01d40e003600c0750030840d100e10000320f60a0009015801544008501090310201051000b00382c544000301100e16041d00e4240c501500c0d0090156200c0790fa440d40c003484100443c412800c001390250303102c3c1c8540303646143c03101c51034010301902c00f03030034800b00182050392521007810f000040c513003100079103403010740e03a01d041d000a100440e1000000b45010f4030100700c0900c140d0f01c03a812204043c008605150520071059003020b401b81c0f0710a81854425204452510b0520000c611103200902a0003c1da8145401c104140e150001180c1c000780c3c10003c00021513008008c0c0c880440d920318108a51041d945d0a400c0180400000d0381f510740c4000c552000d6a80e400000d007401e80c0e00666402c002d41902030b5024015004014200b40803035120750f104c0c030160a00c40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 977571735 1250 977570485 977570491
    0x9010f060e041e050d05120108011a01080a0b030610090b0a080d030b010215090a0308090a0206041203020a0f060e070902071a040206040b0f0909250819050a060305010e06010f03020603 81
    0x80b82c10742c101e4095650750f91601180380901d1000c202c0c007154031004147c0030b140007401400c43e072000303004802d0010710720010030070302104d03035030520800d40c000c9607188109601c402d90102003d0219030b403604103404c0c42c440380c0d04140f0499410a051100d10b984a00340f1740781d084216124130340100444810307400158081c00c5645032090441c0700d03403800100d005503030060250090304000040d10310708100e8140109442d000401018090740300f4000e140060300c6e071004450403104c985440c5503020700d040c03a04a0910007a1813010740035010740820f0b80c0500510f40c0c465000881d420b03046540342c50762140b03001c00341d0240380405484d00d014040711061202d28403400c285d110307200034440c61919840340441c40c0540c000b249207052001c4089001036441c140303061403680102007080000303400304a000e010940b0b10750200301b410030407403004080b07280314030b080710007598441d9108001d01c01481c00040000c000c1000b0711003034460750308007500780500c0f1b04041900d50617540d90070319412205003140c0034014143e0001d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 977572985 1250 977571735 977571773
    0x51614030c04050912030c0a0f09060c1112010903021b0d080d1d030d0c02011107080904200705060f070329060708120f0603030f0406030e030702030f030309010f060e04 74
    0x4840c5d403449400303a0001754450805603030b0280d03c90410070001400b40180c0450303601407060070300d010721040750400d90040310582e0000d01200d50680240c00304d54000e1804807010907075800c1c00700070313000c254022480020302d02062251507610110b503410406104003400c000741c4540c0d130400007001620081e0f00491540030090300c04011080290050901d1540803841c0c0c101100c0d40d54800010566081c040c26254034440790b8924180031030303512036095a20901441a00c12661020111f8518007060b0042200007100503c072031f2a0130300707802c006841e544110b0303800c1440580303003001484460180c40343d030000c456072000001700048402080c800c0c05841c41e031103580c41500cd104030380000744020014022400d803110000a0390400304165010b41c507002d40740d54400e4100744041c8141d90007140c1542c003110307941d15001c82c00810f071140d40340c20340c03007501000b9400d4001c09445105010300040210300a103020b4000f0414124002c000760219031075801803114020190700410040360305403c25682010b41c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 977574235 1250 977572985 977572993
    0x12030412060209040e03031320060d02220b04060915080612030d050a020408010e070608060f04090204050f0912040501090509070519022a13090519051614030c040509 73
    0xb025101a241d60412101e00328083c0b19003078080b0800450100d90030548404911924946271440b00041c19809604c1042890a40c00b054100308100701101300707007815203244080010152100d802d40c01983c003030300859001c501d40110016840360040d00082306080c0d10781d100c0c41103441c1c0c00c0c01c1002050500d6880c00440c8428850b0400f1036201384240c6d8011104690700581d10741c07030b0030240e038250780c03d0001c1144a80c200803810003d00350040344807a03020404030341d03102d00e140c0000009401401e142c2c00103500113252008000d179024444d0803c3e4011500d81003164440c02c0041d40d10381d1a0300c600d0060b00d0004103103080401040c06c10b040c5842d0088040d04005062000c1d14009102c0140d0201c81c0c00c0060303120300c9000e602140030543e400710703081d6440404840d41c1080700101e030110b000080c40108060351740650105000c414000000300e0640302c2c2a607554400142422980c4060204054042c1030300d02d50001403200442c032440b0b94000c03016014084060504080000034200117101d80c2090007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 977575485 1250 977574235 977574251
    0x30602091f0f0e10020703032109120314010b040501030207032705090106021204170f03030115080115080f0405010b211006060c1506180203061203041206020904 71
    0x2844859a081641070b40d1202c80940c40d114004140d481d840c854240514000004201034aa0100324401a240c05040000c9840c1010902404100e4000c1d60205c001e441d0200f80c8041081c0e034440042003a605a5040c090030340c18039a60706040c4c50070b118201c06000d08010401a070b50094014055080c001e05010ba04000c00340940c10240310030107864440400c5000c810304c850b1170b03d00d01030741c0540414401440340200c00440691b03203105038041c403403100424040b5950012030030044c980320300c44541c099035100e5035110000301c01c00e100168180301089a0500104013104c5104244840c00c0e41079407958590745910708168400f04000d081910f0381e540368101d4544640f14440c0c03441c44041c1040c211f480848960813a2410b016400400b4a1a00d007004000c02c40c05070b000f00c444103640e4005c0504090b031400c50440340000c1c842540907658509030050109648e0565502071880b411055a2030341184c200400c00039280d03c1079000310130a4601110958020903039950291007205409080024018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 977576735 1250 977575485 977575519
    0xe0a0f0905040c1406040303030b0604081f0e0318012001061701150e01031b091a03100b090c1309052d1314011d071a070c03060209 58
    0x20015401030044240c603102404200485281c070007008101148501d40301c0000c038000280349105502c405010940c440703000a04030741c5c03940700b20340c002d002c0032040b101065000c0050a051541c2c002141c821030780b03800e425404401020084400401c41c100c0d03000d4503849010700542d082060300071042501d000c03800321044c0c00e14003407080b20068030301d034407904440216201e25142501c02010750880a1144090108a07004014140c80c1c15641d10148105643e01c104034131940c0c00509030b116408603801c0c07050040501c4050302c400c074204007068003641d0380a0000a0721206941a10b10150b800c16030000014403a00c1c007000c0905018a40801445803466036040d0b84001c0e140705581c103030042e4100c40e03034181740c1c08441411540440c0340a401c10896140490941d55421090500502400055200c41c0b6000c0c40039801680128011460340080c00110f0070726a0380c803225030141c1ea1200e0030741e094112507051700700c003030f240d40a62018040b550b80342169213800103500320003aa142c02102171800c0030410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 977577985 1250 977576735 977576759
    0x1021f021b010f29010f02030c150411102a02030f01060e06370e1302010305180703060f02090a0e150a0e040b100f060c12140403030e0a 60
    0x606038800000c24030b40c440e2980c0004480301c1003413504000500790b0241e40b00c1012402c000b1103031402400e04054080096105904600c2180c00042040c0501c400841000f2082a0f041e03004500134240303510b00600d1007003803125003948080b02d40702080b0004846070841c60400c14012003880070380820040502103030b0220346070013160510004565150fa1051040311034041074503522130000c481d69900d1455501c0c510749521032507107122001c0c4607007010001c008085107640000501d00000c2500d203600e8036101030310211888220490010741004049890005407403140c0b02014440d40160615900c2e65503098000d180f090460000309400f802901815075480420a000300021245031a0f0780c5004540e0034004e507541d29240e40705c4ca00e815400e22105103109a8a41c0c019480500b150f01c0303403680c80d05948151401e13802000400e500d1080400c02a500c0f445c2c040404d4030903c190031808a09400964581d40000f2114000660500c03042002c03c0c400c01d840c81010070702400301501d43e902d40c0165105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 977579235 1250 977577985 977578027
    0x6111011130f0510050a050304150b1002010e0c01391703180a08030c1305040f02090310060b0f0f0c07091407031e0c05090303190f08010501021f02 65
    0x500c0b40da00344200610b05003440c1e00c0700f021000b80f80051401040c0a0003504c1400f004d00b020340f05d101009000301c0d50f0344403a40f010305d440c00000c00d01240d42c1403049000f0b02a0050800902c880d0180f0b0400302119401030300c910760481c0e455040e1056880d000a094841801ca0950b00d101e404030b10580400440d10314a407a0904ca2108c0021030354915140320f2121011184828000131076100c3c0c404c6e00b011034903c805498000d00b215060381e5036640d04049000c20b108841e0061540f003860308607200c000c501a0307030051034440d00c1502612a00d4480300f0551085902d00d01c900000090100030310105069054001d01040c88100a024141201d410b0401d2404c00f40c1d800c4490102e5842c0c1c1c103246460040400c44d94400420700d41885120b82c01d0211172112aa16070000984545618400100034011f03826180e03c4d21000d4100c82d11313100b030030b0342c03500300030708101007580200381c1c18411585140d1190000350b05803401a001404115410094004a038404a4001c01090307428007110050081c03c0d01e003200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 977580485 1250 977579235 977579249
    0x804060e0d0804060509060d050a0501170a110114070b0a0213091407080c070c08160b0a0f0e0409021507060c090b09210a030206010f050102010b010e091b070c0f0611101113 76
    0x1c0d10740c1454144000c020106030885d3760b81e848550200c0010b04228000091400c082c80d00c1c21000780c6c1c100ca035138030320b0244c0d0340f0041004901c0340070041850f000e0b5028014460440744958089a500c03004841258021400700340441c002000041c103081c01103103040d402c14490b0003c0e610303001c01c1d07807101c2024940036045024150001003140080c0e014001941c0090018041014508a241803024140c10035400c0e000043c402290203800d441d54590b40440e000c10707005083c0b50036071403d210b501c803011f07400b03240708039404c03494107582c26842442003000000b40c5165905107450316648904100c80752181c4d0b4601800c504110404000c406014042a105d0b1807081d00102040c0d41480044482d600d6182c001e0707411a8501004030300140c1c0e001480700c1c16150141ea08a81035140c250b0020304180e0103403560000004006001420009017408030000c0710315148400c0c41264039890200d80004441e044640d29602585840c031034220310b98040015902190b41591800143d000010780000084e07004c41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 977581735 1250 977580485 977580491
    0xa09051603020313031101060b0d0e0115081203250e0a05031b0915121f18020906030c03011805010b060a0207030803130f0804060e0d0804060509060d050a 68
    0x841404000000c844840680703060039400c6160071054031201d0221103001408102d08401c0c84d2031040000c0d0f100d803024100c200d80740b9588081c2108210007030290941c60611a601e02092851640380506012056880b000c0140848505802582d1210b03000680f800e038020b610400e200354144240140c46484c2ca0a94441c603010302c0304c10301007008039071072a401140a5008151442031051464034600400d1004485000c2c1c0c40d100d4080301c00e0b800070a0204c0d6600301034000910a100d80c070000381c070340c001c0f030016562052207000411604180d0305007440c1945106038402100c0d0041c43c040c00c4640d80300786d000c1c1c102d880d440004030000342540d020f01500c1d95086c02400650307041c00030a008808403102c080d11021701e481c1800400951359000c520020707102650200200310940e9520500300c04141d0070211264102d403150504c40c100364003030301c503c001007a00c1d000030f5001c40c14158501064903812907115810316142c40000d44042d4400c0002980c04981005010719001040c85454000c00e4540000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 977582985 1250 977581735 977581741
    0x1416030c02042306060f0403020301061d071103070809040f05010e15040513030c0521030f060f031510030206070c0512060c030412050f03040b250e090709050a0905 72
    0x101c4100c86602c0d415900c0d1503500c841110038032103a02400c0d504004c060f40e1003642c1c1c9000d000d00009a00480c5c0000f903041d401c0c8407002803503601096040ba62205000300d46607250300c0e01c1e001550301e03901b40740e24580340360414000d200114030500301500c24624088c001295405015502100722076090300000c2d8600390030802d120180c40e2603c1003100c030380700540d410000750504c110340ca120300329032890040c10840026a42410840705001d040c41e09103005001c0310740c800010542c0805900219485055405404001995071521000c10692032101401502d0725a5400c6110301d81201c0c0200344500e00450340303100100507100d202c002d058a030300030028440118101400c10240d81d030302c12019541030303000000703124241c240d110450390000e50014403035881002e1000d0990b40ca0180c1c01020130110004410002031140740d001e114410500f6601b100c5119001c0c0002c000d02507100700706240060442c402404950806c44035180d0030640744d00f0310444d650341d900002203004d00ca5401c842e44040c2c070f550034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 977584235 1250 977582985 977582989
    0x10507030c0201060506040b0903010e030c031c060510080c16030e0a05010e0105040909050712080a080c031605031003122c0609040b0409021c1505161416030c02 71
    0x5150070858103100900401d0300d09800100180034600501c0f006c0580090401000d0390b007507002c00b40c40e00c4982c0070b994032580900d18464036074000b8080d10080001118010450481500c14101981e00080034651440801541151b42d9100280440700144041110158484001443d07065091190703880030030303190828051000b940e4540c1d00440c140044601044610307a04542940e0a42d9080c1b103001030030016038184140b030511207030b08c400c005482d1020302400307000072a030003040a06074644841805880b40415914980b0080750304035078469414018640483c459002150402d1810304801c08042c0c0302e8441622284400720607402085000c0e80401c03010f45400b00509440c004025010021444000803441e14402d045030f403441a5559800503640f0f546950014107090340260400d000d4091807200d400c2c2103c80b0103015a0340440c0e0f4882001155558000c540c450800c0c2070321791740c100001c030009460214039468180c1d016041800100003240e4460091845603000350b035036690345071041c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 977585485 1250 977584235 977584241
    0x2010e1207080111090303071b0f0303050904051006020c040b0301110d152103050a0c1704062d230a05030f0c1201140a12050c040b030d0e010c06020d050901050703 72
    0xa01351075424090108840564000c008d0b07a441541180c01b880307020000b03618541628460b03130017010445050314008814141d0020103080f04980c141d5003080315450301c801004031031886104040059216000a6600e814aa0000780700c41001034004203450314041000051030f0000744410140603540c40c049001e07030900e021210010070f042851042050b002e041c840c100c423080000041c0c00d00100142060b50148141c15030010560040d07170114240c0c00d00c0c0c423642110391107407040000091294903034035542d500c003490841c0210040c000760010803a919074103a4029100000741c0b00c8068400c01210814141c9900816000d1120303507410341e80e8030300b50f140f40e055440301900707074000c50b8001e00103410020003034940241521481c0042143c140000c2d0001003604030b1540045000480326040c8004004001800c0c007030505007141c06000300403040060541e00d1402010b01303800203813000c41c0d008040d4003400300d5019644c000d503809407070400c84d00101816154155803140700c43c2e41d500c0800c02a568584 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 977586735 1250 977585485 977585501
    0x5031c0c080411151204030c030905042304020a0b070606030209181e010f020418050a0e0d0e010c0b0403020f1e03040b030a09050a0c0612050c04030f02010e12070801 73
    0x41401e00e403504150b01c0707440c1d041c20b103502100d0042d003080ea10010a446400c0c00c1d02e25511061002c0a0140703010310b001020441c010400b28042204540007103810b25080c01041982203800d040c01d107104040910008202c10013602c26030304000e030680041084c03260b040c018030705280140d40103d4011b1452042c40075a030401480c81400d1091508501490300000c41d003407520000101041a025101c8071048d0b00511100169090080c40010006400c20301c84000885060400d60204000d40c0c4410300b11041c6c2d14175659020541d0801060480700764040e030769503141c818041c900703444502d48a5540030f030a81402c2e0b50036030160b0710007400002d601b502001691038007100303481105580d44264182c107980e40507501864900d80400700006101c560103034000c910143d080b400300d420a503000d04111121003518010100001e000400c0081d44546600405029030003040c0300074506131658680014050b0348040c224100710009005480340d40d03e40c24141040903842d00500034031072401d59280e0031600f540f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 977587985 1250 977586735 977586737
    0xb0c1209010615030207020a051c0605060619120612080910110c011b020904060b0916080609040f0f0302012309070303083403060503010203101a0705031c0c 69
    0x1807000d0003071690030840d0300418842411301507150503841c40000d80c00141d58010680140344490141c41f50340c11034078840400390140104000a4803103809005291141345148090f40821908000c0100d11070348407640103006080c000180030f5211081130b00065805c24050f82c01520204450902e071501591400c00304107035092503203484034221103054680030540381d41810701100207165044980340c0c4402c500c3c11130707008140b14450303c0d0601d00140101141b210450182c608880001c54200800c12404001145600e03110120303a11b550422010080040007200c0d5030700114031040c005040b0807082021644a03400200d1845031798144100301180002e1008030000c01401030007286071022685200762500b61418080d150354515007404919a032030340d900941007204a1310305018000003071a0613805050358090103070319030b07074401c140c00e0f8001641d81a5071019850320803c14203003408480415000030040c0203040842031340b156400e6030045190300401d241d0302540301c1c0004015208911001c2c0312 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 977589235 1250 977587985 977587991
    0x5040e090c1305060312120901060e070804060b0604050316140627010e030a03020c0315011401030e160602010b0f0415140f120a02010f05040605250b0c120901 70
    0x9a000282d94440702c202c0385004595100089069030700d0a001c0303450001d808120b6165503181c030145944075640100e0700006154600800860b6252028200c18020440d83e99100c0c101c0d284c0b03484805c0240075410400d0b034051810080051140c40a11076a80030800051044d96285d2400e50440c10414008c110548284000c02521224480f0712803d0f50052402140e44d080c2000302d080140d90300c103c0408216454402d12003604101580040d080c0c01a0406805583c41c0c5000e11a0341d2004500038003480780d1701c40d0009010045035120760300c10b4002000f0324040300c0a01007401448401c401d0940c00080042c2d444502444035410407445c0c1400400050b6420041003d034210a00041c02540c0100201e02030000c00b000182d40d1034031106089020020029022034460b8120305a403400140d500301d000c07401e01c0c4102d000407030140c0d040d207040b03901135202c0e54a01107540c03c007030284090406040044a61071000710001c9601003651500c50355500105c81da540303020301c051181686e8014100c10250381 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 977590485 1250 977589235 977589253
    0x2060f30072a080304080d06030c03110906130e0a0b100602011802011403041a1303081311060904020c030c01091505010f12110d150f140105060c10020a05040e09 71
    0x42100e00c0741d1899904505041e481791030340d00c0e2130005407290450406015041c0380e008424050300e441070400300d0b8460401c0c020340200c01424802088030071038807643d0000b090395140d070f2408c02c035070807440c0114001c10560307403040799542d200401d48c1030655618141c01034000c414040070ba0244516103030b84041801d10141105a640024140700400c01a00c802c07110100100b42001710341d210115000c81160030081c00381c07070680129a0740c8090f044095001400e03120100c5c00b4000b0b050500c020309a00704a9a080c0441100240103050f0700115001d074125508000fa01d61100d81030004e40304100b101000400d200c0e855003482c5521041c5044501029441e142c010002204542c1e011400c5841550141c1506440340c01d1030030b100c480111440e80c0040204698000b00107040000f00604c541c20481002035480c2200340e00c4c2160340400340070b651150400014082e40c90440040d101c088140c8049415404e152096141641c1180008001040020500b48070b201307070f1b03410f080760b100f14018000c6c90540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 977591735 1250 977590485 977590547
    0x9150e0f010e071527080c100507020f1c02090a0b1009060f032007030f090801060f0e091e030304170909161115061201050402060f3007 60
    0x1400041c808402d002001e0310b80e9446400340c17080181e07403122100c6a09001071341c4000d070300d0b2a02640480e080c0b00380760446d8051041401841903c1c03d20b45c0241c80003409034940018031083d07181e68074440f441e01c0310b00b01d8902c1c01607481c030100500c0382889010208000c000c160501c4410001070b400a400d00c03509100600100e030707014185500704081480d010a09030100b1000d01860705200e070741d503090241c0020341d81c02407603085081030004031010344d9040e0005944004007801c03580e8a010b0303201c11000000c01000350314050f05c40035401c0301040c4140ca102c40c0748141c00304622803c002c103448668001104000034481c03900171003008000400c428502d80707907001000070b520090042200344144510080c0310b201c64814211905042e25690840c0d80e00b504080d0601c0c001c1c0821a90141b003800b11100d907070140d41041c0030301800f80d507003d0250340c10304000200050b590b800000c06a0051181d400c86104503c0e03032030032100504500400030036250306207024001e042c150901c01c00000d49100140e1043e4134 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 977592985 1250 977591735 977591759
    0x90a090209040b060f0405010b1315020a0807110306070815030303040210051c1a04240e04060b0d06020a0f020a020a15020114091f1e09150e0f010e07 66
    0x3041d4040501c80c01a501d1900003103821000403211794111345801c0012402d42c0c842001800e0161100740340c480c1c00380d5241e0020b8011911510601c0042e0406c0c0840c000150002003d0070340c082c030a0080030544203841c2c011074a030000488213240000c03804814028040c0801d42c8102c815901a0302840c07952406801064454581103001d40803c1000129600c08000c5100c80400045003120280100e003003051129003070001141c10140315610304040040410b04c2c5418415a90201d2080c0941040c9403605054a103140140165860fa40b00d120410150b030f11240b602e103840c0d04c00c0c1d1006032542c0c0100c100404482e0042d0b02801558040001c0801695071002c1d10400c0320a08840700d80300e000d0301e4004030301500b46044422a000d69060a2004001011035411030000c203100c444e00f5280c20000005040c0e62841c010082c40082c2991414074940d0650020f406c0c0134020000d5107100101c240c030200c100c402c04d480007003d541250003000750a40080c01003400c1410180b00030100c143c01e04880c0d00381 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 977594235 1250 977592985 977592991
    0x81905070c0e13061b26060906060d0e010504030e090f0f090f01060312020d210b1c060501030b102303070b0a26042609040e0309090a090209 62
    0x341a03079800211440943c421030418242d106000b4441d0041035007400c0f50035644081c56030301080d0b8012400d80c0240880c0130320031804114803040300450321002d05205030460051300b1709820480810401c5680a01809844c151443d807400000701c43c034013130138010a00d0540d4148c0b24400c1002005001c5010755207242a90080d0400c980c0b03900540382c003103100e13140c000120f550f0f098035402d16800106002c0001220318510f0b6064007529100d501c8034004031904030092400001840e2011810003902c48103500070070b412f44000e0105018840c08208003003140e0180001141d60a48800c018000c01c00c03017910a40d00f02d0580c00500300c85504180d491032a04d4908002c19281c04c0c1c2c64003440b4155a0200828030007800b02f9410a90388442d0004000d00e480000ea1801c0b480300021240990600036510385248141e40020340d108601180e000b100c001c1c480c540f440c40c0706061050000e5181940d0701d2103045062040b01d80159030710000329046c4551203200501c0c054110745000240000360b122000c80c1750f4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 977595485 1250 977594235 977594249
    0x301050a05040b061e04051302070615060804030f0507060e0307020f0618121509151b040e07110f1e011116080706020a030b18010602031c1107081905070c 68
    0x170030129803034045045014990180d94041da0f080314800450191707500800b03845d8040e0006118292140000003842112841400001891703c000038000c02d2044014134911800d46c541140780620300e0300c0303420558880c40307103c03a003036000081c1c03031011803a100c1d812014008050b030740c170380c2060401481c04400740d03261043c55000e410640c0c0c483c51740900a11517003602e03020700644002d980c1030002641d60b91782002e0454000764980c840c0450080c3c12403800710311040f00c3d500c111170f207040c0c20541d0a08180d440034000405001240881559014090040d40a1580a070000740403411100d11004c0e40e50f404080100150b0349000f02c0c201114120741d08a400380441c000c000071144c299031230425054030034114054100b51000c00c0c040c1245a16401101a001c011110007030103100c5c1e07090442e00e0070b20038400c10005d44e1040201401e280003440c03031911213040000000420b601252115005035100000441d0501000a42c0703d008003070180128a600b9482e01c1c00500340741c00780c0c0e644c500002c118041d1030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 977596735 1250 977595485 977595517
    0xb0a14280e0304030605070c14120d020702030f0a14121c111207030609050f0609040605100e040606090612120c080405120606010806010f09090b060f0c030301050a05040b06 76
    0x1c40c0d52010070850f0029684102c0c2001a03182c0744200800d100b0322054100d0310700d0244005007020700c100045030341981c6c000c1e84600c0d1418000010980c001d501c0858100d030180643d81d03da076107101e0180b01c5100c1050089044e8a50404e8400c407203402c02004410100a41900b4890080580680c4084100d604010040025202c0d010031040d40c1c2c50144010541c1010000c80410510b95410b4000e10100c5840c00b0307091160740c85221645039a003030112491a0031241c0e000004011440b2034100c3c9810003460481550394075245d1004403101d060440e0700f920015110320f1300704040080c5201e204000c11062859124100e0199110100221041c2c43e01c0200500600e07080c0c2840900c01c110703401000e0082c610102c8150341003007203882d048210ba14074041883c05001503c0303940030305035506000c1d405aa0742191203042c49035075001010b81d403460a4201406000b0080103440103401400c040301403030002d43e22589007108104000c8119044540550700386080c06c0b0043e1074180c10f44000903840080d407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 977597985 1250 977596735 977596751
    0x92806080613081b01230402010507030e27040c0602060925050d05010b10031e0203040f120c0c060903020105030f06030a02150a180e220b0a1428 64
    0x1041160060800810008800130500095010151310408100070400c2c0c58600090002142c0324800004940c0a40824410400e6100013803080c80810580b05000788680103402000b07010f440100764040035625012111401c1c8028851680a404020905d174801098249040c50f9103a44032100c0300008001034072903200d81540d0080301070080c405001e014001c03855602031760810902808909149134002c0c8902180b1104980c8240200c0841c00c2e41c103100400503000b030b14203150080d88014000e482c045141c0c0c00800016484403010350140302030b81c1da0501221030070300b00b41241c220b55500150034002a0a0b00300010b0741c0003030940e98403841c0c2c6d1000c8203841d55074001081c1060444d8000030b40c4541801d205c42d01d2103410401510508056668055400084041601031701340c2501400c00503505c1c090014005e001942201c3c0c8108000300c1a1581404ca19550707812140ea003540e0700184a51510360706005007980c046a10340c4840300e80303041031100041c846d491085441c3c914040c41d21540340c80c1c103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 977599235 1250 977597985 977597993
    0x4030912030c320d05091003020f04061710031109060d0b0c0307121e0b0a24080c12181204080714010c05030901081005092806080613 59
    0x54886800d4000214441c504601071440007408042c0f401c01c051407008100905100800040c2d8002881e01611510724110190007040743c010240c000c3c100416800f002041c4c0d01ca40e82c0000740000b400d0584804240d042151101160000c00416080294038080c8013040440c500d007404a450650946002c1020348941012609413011110702030200807040c414094540f032200015032141c0c00507615140d4401086014805444401810321445044420005008255603200a01010000f00380701b0a280d0344038015504112040140110a0303121507c1c1d940541c0c1040849910044591005141a240d0480e10005403030141030b21000e41c031401c02801c01c10408020b8a0a01c80341e40303007842d40300c0303036181589a036035050f90044010b8002d044031095869400b41403052080c66116000e5810141500c00440349842d004152480713101c100300d00000c3d191954091903008042004820201560003101c2d05032201d0041c0d803080c1050302d01103080290802c04101950000394402080ca01d105603410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 977600485 1250 977599235 977599247
    0x301090b060a020a03180e07110607020a03121d2530050102091527031522140601051c0609021305130b060334270b06030403091203 58
    0x1030324510411030502940580203c26184a84016000c030345e0240d4be000412601e0f41e00c4184010049107501201c0d18910f4a160040c0d002015540307401c21801c00c865a22514048201803181e9985286240d1051650b442181d03040c0a01080001d0f10104886031040100307000da004418520300b0020500401080001e404941402d20008e1141101b0032030a84100b03111360089072040d102d50114410002448140c1c0e03a600114103009029083d10420141894000c0500406080e40078404408410010904808450000e4018264000710382c11490407035141c4407068214601c2500c516103459444d84409055204580d80a8004507142d1290f00c01306800b048009004950a0304000402c08001a030802002c8024060319a0407019200d600034103807200014008039008405580c0c10621030079001c980c0200d001d400c0b900304640d15681d4005031045150528861a40da0340c12659487c560255010303081c0d64202c110b9406155080c2640c0c0a084c60001d4411084601c9840c8010b20505000d80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 977601735 1250 977600485 977600489
    0x1060f0201090c170c092502070e0708010819051b1903080a080c36030a060519060e0a0c12060308030712020733110301090b060a020a0318 61
    0x22004844940c8030004c120030585500641c100c94407030480e0203401c91401c1d0950a0050540030165071141c1310040401d0b01c0c0d9200c12400c00c05610030342c040082c1618a180c0f030035100d034442e5030b41c0580365410041d420707081200900e04041035407403809070100820004030321203203400301058507001c4280c5a240400c0101280c0380800c4e8681104030800000d00031003a00038116061950383d002e00540c0e4079240700320300e8080da0746200c03200c46800c00e07016019070740714060010805d50360f525040740d03400d40310000313240a106420446000e03840384c06100040031a00441008054400e00900c001130a14108650b600401818103942507210104030300d5083c0a6441c0545048901c403080c400f40740c580c00c1001140d0700c01e50f002d8001640481031100301008600c00d403082c1a504c43c108a04540d02c15103c03c07500c0000d9000e03203000e82c00100d0b008920003640d2144800c41003140c0c0c0708545030b41c5420712810403a19012074a9004450070400c041e0a2940403c03c02d58950b81030604000083e080200c14065054503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 977602985 1250 977601735 977601743
    0x50603150405060102160509130501020a030c08010510080c0901030204120c05090705032202030309030f0c0f010903033203040b060f100e150d06120302070e010b0301060f020109 78
    0x4140140310014440da03840300351081c0c900b4407007030b2039000c012079441c02040c800b41d16a6015070001d21441c030b0000c6415400c0082d1562682506d4041e4403140d00726071162980e9070100307070784880d14131285400840140c010001242c6107501c42d001c81c43c0123090550004c141600da6180000c1d00305140e800381d41514058040c0c200c08081c260749919010501c2210350244501c40c0300c001001542040c4140205d03880307002c8901e0141e0503854800511507030041d03034181c1282e26000078010001c0039102001001c00c001c14010090031050440d10520400a0f200c039038190400c68003d200303001080d04030265030354a40000724028802803c42c0c1d42560002c05500c0d0100081c44000184400d0000b1140318034003e1b80c0440e441aa041041800c104000b603200c13000e00c0c08120100103c1d01d0602c0c000c4150070380062154000d525150400e014001100c4040e04a90902a1054074280031f150f03040007410b02514109040b000c02c1e504010407010070b400140300c1c10041000d8900f064000324401c1d005000182d0384 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 977604235 1250 977602985 977602987
    0x90603060d1e0c090213060c0c171609090803010e071205040b060306100e0712020c010501060207030b0c03100e1320152d07050d0507151a1002070506 66
    0x822250482c840410103419a90070002c00d2021548640520889011140550955074580c1c64030005803104090a05c0965400d16071010008003161349103c001240e0078400040e2420114102c80d0b21310031100c0341c10150a81c0d1908a404000503da003003102d043d101c4408071030340c250356105021610f85c0c03030095003041254100030500c41005480c013101c1e80070359400c42c00c1e112155070b83c85040040b580c03180f02d0001d0340d62540300461100703401003842ca00000c80020000d8501040c104065007074460a0f440180140d02082003002402109007040d038101c000e5a1465256040c0084030304175040b9107024210b441c4840501281802c0001e01035549800d5000112619140c0030109100200c4056083d080c00b424400b002601008912001c4940400140702c115200ca240041d445002d00c18004070003480d40e60801101b80841e0b4200301c00054070400d40d8460f6540c21176840e11100c02c43c124580b42e02c0c03041c1420540c0400e20008040f08511030419910741e48280c0d007030f06040341b034080c65602c51a08100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 977605485 1250 977604235 977604263
    0x2060c0a0515010e1e04080d09140703020f1207090f021b0c011202120c0a020c0d0641060f100905040e030f0f071115031515090603060d 60
    0x22400c007054100c0341c004c009550a030356408191041c0710066085029030750b40c4d1000040005400601038000785004010000b1400308903640c08801c12400051003100c2e0388159400c004520303080808040c00d6605072400c0c1c00c0d0503500034403103941d80454010344042a4030741f04080910f5820358190382400f50601188040d850103945881d444001d2024510f0000315140d0b15809044240e008039080ca08494201620300c0c0d41e0030700e0080340741d00110100340850003102282041d6544d103100700310a66004010024808501040901c91540007107004000f1001c800d10040041c2010410000394240c01e040c9240780750380305400500e40c8038070580300c1a4446d2100303803080031b42070307018010b0ba0541e070045c0c5040000a1382465207644d80c1c0580301340420a0722041010100c2c41e1140e401508940d44140141183c0c48045d100007680f0b15020740903001006400b100304441900c40d45c00d100c0011409460400d0701c51456020f401c4280300700e43c0300500901000000c100c1603141d00301c08104054011580c801451 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 977606735 1250 977605485 977605513
    0x9040f0207050607020c010507020405100e100608091507080619080703051002070210050a121a03010c0c0816080c0109061d0f030403140c12070920030402060c0a05 72
    0x2401041c400c0d00c0d544a10b000041e01d0b01c0c00001c0d55800c50905840f16420803100d07908010107810018051000012044000518000c00747c203258001c201c0b00d0b001d0040c1f01d0602c2d81c000e0400e0380c0101040f08990024541a6400048101c030a4100041b071074010b07041c0e070300e40011526610900c41014000b500491000a241e0b0020401105482c41351050b5000d4a21041030034082e4000d919001e03501420380b401c40b9284500403402442144203e040c144030300c8014800341e408036040c4c0704200c18842da8001d9401c0082c0b40038410203100106d0350408141c800e00d99121088076004114400410300e01006410050000d84420f40f81405003a100078040d802ca18a4170380091302030502ca0300450441c3c03041811054801041341c408102d4514001d40c10070303180da210540780402070002000c0324010a202c05a143e02c84904c48007022343d2001c02060132a241c81c60f004121183d80304009803068a11540c40042d4942e2412039400c660100c0d00a9214a0555841410000808402000d612440074101101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 977607985 1250 977606735 977606737
    0x509160806091b090f040f0c03060b010e09150411041a070c0803070b07030b04022703060106031116050118060906060e0105012019151a03030706020f09040f02 70
    0x6044400243c0f8401035109002c0b011030a1001e0030243d00500c4000016000300a54010303a6009000d08400c4014031a192200d40d1a0714098005036942c2c3d44070b0540c02215600704a0b02c2c4154802a64031030303038902d08034080b1a900c402c0c1c0c01c0a10b03c52900c03a680c000b1144c2105090358060715103800000c2c111020115000c00710351002404407221075070b0307140c000f409040100030340352250380040700f11005940da40c404400401c65070a00780d41c880d80c24002007001155444852007030441c0482d00031480300d00c520416142140581c0068101418000924111140c920a139104d080391904140043c800c240f410314050b1000800511040789508088001e114240c1c1012095a00418040001c10784948004545030000d020b420b0100d0844910301c0c4a880c008003ea0824941074400d6039050682d00c0700016025004e140152240c60302d00e284401c0824941c46140340c00101d141c0344440c15600071740400c1e01c030f0168000242c106640170070042007201c50007084131050000104104014010038080f00c0003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 977609235 1250 977607985 977607991
    0xa02070801150501080121083001050a0e10080102300105060708183f0d21020406030207050d140906070f0203060708010303110d120509160806 63
    0x180390708100e00032100c82e012070394400a4407410b03569404960f080c160380020f00c0c6008502182805c0040c10b005000ca203c940142c043c0018802c1024030300038007071224000343c0b40d20a0780c90f00011401c2c401044682d880ca00c0d2541120b442000c490b11598440880c00000d03021341d030199155500001b201151130580c05850300e10f402c0b100300754201d8051200b54101c58004240122600507000300004804941808040d107900c104c2840001d07070400500340860802d42c0c1c00d64150440702000200201d6201c804006c11050840c415200c5500c5003020803825a80d100802071001800444c0050844158114564090024220f1001d42d6140d5403088028002d610242040e40c80703008031034403415210b1103110344644890069038410b040036469002c210740c0380d00c403000442d03001200b6141d4500580b030a00c0894400c00483d12601825855410702416544503a0505681600003065180c1c1f40390b084603800d11080b0160300c0003e000c1e5141c0c07022a183c641c001e541e4042107058050b000030b46d10703000078481f48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 977610485 1250 977609235 977609249
    0x7030f02121f08032a0c031005150405090d0e0a080703030f0f02030921010207060f1a0303070b0c030a0e0f010e010b0102010e0c1002070302090f220218100b0a0207 72
    0x407507503030f0b4100740c4e450b030250304005428051591942d115412954075040a20b1015800752a1211010b6000034074064509280d490b03c41d4880040162031a204403014100310005d40f01400103141c4141e00c07640b2140780b40c00c11800d000100d10009a561500401240a0010b4900710f88045490341030190003d031003110444000f46000c1d24646c246407006c000d4941040c00a4980c8803246000c0d01102d40328044640039130740c01d6600b448080c0c08242c042c041c4003110340080900107030004100501d09541e401040040c0e001e544100407400c0040c00c0c51409031760259036103840c1e0392642c07135026454010b07006a10750001184140002e20882040661181c04081c0710413000b0014481702400690a0341c0340d8819800440c1c00000484c8118104801040c0d500039042c0706842c0555140ea000424516082d1410064000309608102c10000b0341400c01400061109030740e45410265800250b000208640d5040d1490030100466004140d07051080d010344820f640450321100008402541d501c114440c0c0d103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 977611735 1250 977610485 977610541
    0x60f021924020915091f03021908060a080303090a03030506030a021201020a11060108071208090a06050a080c0906070f0c031502070b010b28050f040603140f06030607030f0212 77
    0x11311014200c0100d40650101910711010b0b20f600c1d02000e820b50442c0c1c1c006900b0b05408012030341600501c42c1600040410300e840d000d2090070f02c94244500c1f00e200b50000b03080c560081003400440e90001078424000b9a1525020640d551745401082c24083e004900a4101c050050a5401c065042d009408901001d0b80c0d1502c60800100701503554070001c0c460001140c0018806010215100111080e43c6004081152800300d40801059520300b9680c000c900090010400c0a081984030344000c0e00209100c4050742804040000200c8900c103040c4000c19000e031000c04501001103070b0902c80003e54004c4034442400e5a0900402c01a40c09075400b200c00014540010440da2454020354464410717031000034484806540100021810840ca48020700c00c3c1807004902c25841031008001070049960040745400c03803580310000c001009013044211309442c20800110b80c031300140d07a5621060a00c2c003c541030387c244a10800034031400c0700d4a0140c0d21b40310200516444503581c00e81c0071003060030b0340c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 977612985 1250 977611735 977611759
    0xa171005220e0604170c012301030209070302090109260610080f060c070212072d0902030412051804060b0909091b010e1c0b060406060f0219240209 65
    0x100d80f40e400884009042050009800d00d000c0007904c090000005007500014240200d42c603809861560101c26950b03142c0e801c0010302c11810700030304441c2c10000500301581010640800a0519a040d0140100704010380c65107000f044081c0d6116100655504181c4400303003000c45c0500750741200c1e8025103200e4807554002001240d400070350725120b0f082d400a0b450a003d815400c01c0820503900120030014840c540010801d0142c82c40750707100c03101f100650700d00001e81e244544581c034034080d800b041c141803040c0701b0000130075030422548162400e146401580c0c1c5c421810b00443c4011600115034005d89403080102d00400500c0c002c0458a07402c5464070b840f40e0380c91446c16601c0b004004c10600b41c00001c0030f41070300c030350203103054180d40640107012001d06a40800c22800c2e800b5246400e441d505010808d02240e41010b1050344085c09080c43c2c1000b501c1c1e0b4803071003c2e585030b49508440403404000c4005200b4408240c60703036101b0b55449040504500d91041d031420194105808007841840300c4106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 977614235 1250 977612985 977613011
    0x603061104080703141218030105060f130507030e01230609040305070f0804051c12080105011709010912050d0609050411010e030a0c120b01050301020a17100522 71
    0x7034404440e010801030032502c0c29980c4202c2d030080522442c0c0d003d48030714000e04464040b03580160421210500340301c104640710504150a5403800350800e4060006035410700110744440c00d803000104c1c008035003c40d00d41c452040443c010120048291860f52a0116081e0340056040c5a06802d17034810007820000e8a582040040e48030b003c3d00c000b40031840c100258000901d0390985528003e0040c040642059a607201003106040b00c122980480906034056108202e40c180884200742003d161000d100d40c10a00082c1c0b980c0441b840d2004245150300010b900b04000b5041052251790000b864070405541c0070010b0030b6604241100c40029060070404a08501c080c07180034072070340d08000c2c0c10341050300d6000152082454130010a800d80100c0b030140c004a903040d840900144100c10707040c140d948441c1000014004103803c01c1c3e109900400c15038410990186440c0007050351071008035190389030042c0010701d600300f980c8403a4018864030540b49001e802e10000c010700250101c03041c8200c5109581c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 977615485 1250 977614235 977614237
    0xa081c020714010923060f0408150408090409050f07031b080a1a0a1811100305060d0201032d0c08060f031c0504031704051206090601051003061806030611 68
    0x5150f0002d89400020000c025041c2040001210b81c910141c02007180c150205010354811100345039001e90005081101c0c1004114a007481d50059008500e5400c10b42d4501400d40700d54181c440c442d586404d0344405010341440282280740e1202c08980c0c241d030b81c0b0314081501c40c44035040c484085a100600188805007c07618141480c1e000d4200340d02c00c844208070b0b05848001400e640403440e650344421404003100e99082a41c580104000c20850700408108600410304012400070181000d00f8030103e5115032407034980c041e50908020a4a2403a80d04646400341d0a1510800e0044049020b130840e40c3c03285d0100512031100d60780c131645503030b46038184518100480100d54045d48495038800030107503202c80303070154030b0098a00756180c00e507261600d0030350f29840b81b10300c884400c001400304a80d18049044400a1160300054812490019040e54070b80c58144526406110a9040d80c41041d100381d012601400f0310055540c4142d030790908050007014540011a41145010444d04900c48008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 977616735 1250 977615485 977615519
    0xb030a03080106050f04080a03110c0d350d0e0d0e0907030f06090e0106260601030308070507060207060e06060a140105070c08011b03050a06050a0608060a081c0207 72
    0x18a078010a40d10f8001c040300c055100d01c1003400419400c1c08045000303d0107200240642e806943c40344200300b441c5078402c3c20f28114280311032041d510078007000c00107016145088822200031601c2c0c00d030380d28035102a0f02d01181183c80d1000c0f4000000d18a220b4215591020b03a02001d040102d41808030021400c3e03924201c01002103034400444000241c1e080e100fa00b10482000d226140880c2c0b2994849008050303901c180482006a51680e0041c06042042c07201d07440340ca520756075a41101c0000d0041c41d500c07440103000260030000c128001840c0180500300715032010b41e00c80d20455844000707040000090000c1c2a400400d80181000700b003061501118840030345060038101a8841c085200555496000c04030440754079150f071600003003191081c42440002c0d06001840082c80203114001402c8882c01009820031074a0018140902d4441c014680c0c191042e41c1400c3c2c0c003c0d12014000341095401742c1c0030840740c2c41500d0202c0070004016100c0e010f10031060302201c040a84829214203546808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 977617985 1250 977616735 977616737
    0xd031e0914010522060c140c01020a080f0c04030f03030b0612090c040c02060a09170d0b030610081c05121008011a0913021f051c150b0904060506040e0601030b030a03 73
    0x26440c2d101040c4e1a9011070050704840c205864501109400e80d0408d4104215040790f0365030208103039440b103420044e1f030390b070048540d59071161a03d020542c880c014003417800040d124503840c0e4900010503000c1e901882034150003c3c003107600c0d451456010a203003442110300306d0740c6000e501307501c0c000c60034680501e1a0010454000e0300b01682e91075101c40c000c102c07100303080d5014803080c241c1e00c0e5941c0307104008104c4a0302e601c501140d419801030a0602d0038401505203171425480c0c800412922001294400106804e100c5556208003400c070111524001d420003004061910418801061780346202602102c0b200802440091008029400740320180b055942d0081d608070006103c10054503014022144001c0000c0251517a040c41e0101c03c0788400c0301580030410000b07030000482141554203280001c0a0300c00e000801d4000c003035100c00352042c030923050b80000200f000c21680d903031a0810b0010300f401400054466070344400300c88001c0c409441d801c3c082807420f160285181404519011040c3e01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 977619235 1250 977617985 977618041
    0x192102030703080105300618030f0304060f1d0f010b040b1804061d300a030c030b15220803180105120702060a051501020d031e09140105 60
    0x6444203100303076548445122980b607020103007204c1c450300410062480c5000170200800091034000f900c083e08c4000050143c02e145d000380990303240590f1010480b644a50302000214101c011076045201030f000c0681001c40440d800020040c1e8050000349200d0f038211454000e0213505510400e103c00c8444071580a90444911134032050302900784482150010700c180c20000d40e103002820201d0700080912482022504001c81007640040080b440d41c003005e40122161501d03600d480610301c5144690300c1040e041c191030f1442e0308903d43c001c1d0b104000c02103019003201032110307000440da1581e600030080300748031000602d104c854a0b4255038008048d620084010343c41c0c6205030001c85030184e1407050490410000704017030a04119041c820300e0040c1e9140c1c00401d0b160500e000d5103003e64030001c04002c41088d20350b50124150b0b90015600d035000341241000130702c4000c01092064a958000d080200460902c03d02c1d4003003000748042c010400381100004c005070340700d07003c00000c0749407082031444d0141e030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 977620485 1250 977619235 977619239
    0x5011406090609311107060518010606050c1002040f061d060712030b031b0f061201060507200d08160209010b0306030d1107030b091921020307030801 66
    0x20000c0c010405180c0041145007402e6080700080d40103c2c030014001d00b01c80c840d84070810f141000a00c803010712016048184503203200b01c0640141d900510304003800e1151038401060883c0c82c07040144011a065200034010643c0b0340700d002c0c01d41d40c06074103410043c0c4261100f201d2184010310a903070a84400c58403801c4100c0c42c0160481e8060b50703458039800c5140259443e002581d40b040c005040151040011080c01010388001800b00c4005010a60094001070341c820008200d48a005518900c00c07164440b45092040100c1c080d8056484070b030042c030681030f00201f82c0c2e54102014015191055841c1d1a0310103d405101d819038400e03d00154008000110180c00600600050403400458000300180340040c0c0e000200c18010030380c44161a0300002040c844e0508007445880e01700103407414042500b84403602c0c015583e074500d21018110180c0200030070311b0070006000380c40c89079004079000b11650000b401d02c1164104183d40650034412208504500c8030f0000c4161152250140c41c1c40025078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 977621735 1250 977620485 977620489
    0x305040b0630010c020c030c18091e0c0109091803030e0a050105130203120a14071703070f0801140102030f090105071a070f0813060c02012403050c032b1b03030509010f050114 77
    0x83e0000c1e015902070300502cbc014000d07070b2010071105e50304000ca0400510b4020a030740005450880c071904100d45140c2050602c88000c5544d20041c4842a03040c0740004503030707e80e01e0115081104241c001440c650074007052194072180c2c1c5200d444001e008506403484070700710401c0b010052007400300140109001550511142d0190307809405014000d0701040d40e00c1c0380c000711504803503104848c0000403804440385030406c10340c0203150ba805400903462a541c100c54020000c2d6403802030342c10609802a00046610030360741716106441c41e16a005e494090300440c110044600042d08070341110010340e501c001a45110701c21815a03014821503aa001c1c00351f125501c03240d015040d0318411000b59034807140130b81e40d081ca1481042e001ca1594510600d450741c00c1d894000e05103500103150321b1080c4d006d241038441074884100501e2042d81044401c2c40a03480030881580c0041c3c0c40c10310760b100c2d208420000402d042c0c041c0c00240c0b041a030003000f005000848e003100d03400c50700c0c203025074440710b00914a960440c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 977622985 1250 977621735 977621779
    0x40b01150504030f06020c070b040b0403150f06060206160801030308040f020d14030c0c03010203040b0601051809070c05100509250504091109070305040b0630010c020c030c 76
    0x2400561600078a0b0a80b0307511000140781d00e20354116101c0b0390010b840d1008070f9042c80b2035070150041d5040589028a0019160032501582c0405001404101003d80b03080600c1c4d40b1080c0130f5201d80d4418003d496817603a003e5280c80c0202c43d1282c501f17020300141c1000b24462440c0034140d035450740381c6035090340b01c640b104195100078490482e0082c0001c039042010820340d4034400c1800400c070008580d103a401c07031415400d244400c11600d000b81e0050040c00b00094440382000d500042c286000c41e103440c410941851044480c0c60840d41000844003405400f40e41300c003c00c0303466800760045503903c00000d0058001c9410480d2100e440380c002040e42001103c521040c5001007030540313942c0b414035403540000740844842c440100c034007031203406080c403180c20b20020700ba5104104c0d003410082c920341516a0780e01040001c0400d03201360400c900354041c1e0107d9220503801c03098108900c100300182106414002d00c429407000015110321a0007440618001690700e09540000e402100b010788101518996 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 977624235 1250 977622985 977623019
    0x3011b320904020c011d12120105040e123f01090507020313080312090d08011206020d020313140106180b18042d05031207030f240608040b01 62
    0x4815004c1203000e2801c4001d01616001c45140350610032810b0720031b07070858a44100709100b85c1c0c402c507051210011503041031100030304648042c0c4d0b02240c00c00c3e08565030f60402002503001040503e0200c1ea118882401070b1000ca2004400360f00300d40d032400c42c81c00754103182000401016810a0a038010710039581c0d50f41295800000d80d00440703060032020700c1021001c03010b940000400e81c1c404985083e40c0d02c1c0c64610180c0052400d809003444807811070004221210500a44044005a01040c0100903082d4104c0f4024401c4074000c40d100c5c10452100d000100d0504001d0b140400c56400700881444d061052034103c03095160024084c55200f0904005044402400d0303512080030380740400444000b040030351065119081c080c8100d0144100c500080b0306c1112032840c80c1003c0382c030130300004400008884800d114800c0c06c1e5041e95801034114090090302d00513030490741c101008a0000c135440811265000054004180a19100d001c200c07042d130012240a440304522100400c805184000c800c18 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 977625485 1250 977624235 977624239
    0x512160908150a050c070201173607082e020706091208010806071205040c0b34081e221d07020d050903030903011b3209 53
    0x420641c0da2181c0c40e0608050314044074102c0701e100c080001181c003078460b103980104901c0c1d1715400d14000c2e0700020682000b000110020260072004110060140b908042203800300a400c080c0180c1010220f824034041d90524000610070144003051071070000c541c2400200050710035002d5080001c1710038018102d44100d06104a600b04005004a903a500460b10010302404200c0d0118200d01c40003084110b0580c00742840d60080014014496071010350489106c4a160000c40e59858600701094000090361026054040005480b400c8410b403000303040044c81d01c41c0c28485001d20000d0305010703441c080000108001e00030003951100c1d40510354141036030046404298102103400800e90711482c0140004030054548031810042804400707501d6109020000302960503003048503019650308030300d030001000c2c020045007401007510704001fa1018500010700900103940c012440401d18024811302e0307000650403100f68000c02206030314912094540c60320880100070305550500c10343e0000b20b4500c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 977626735 1250 977625485 977625497
    0x10b2505030c150f06030a03080a1d0606040e06010b040b0c071517010503010b010e28170c010203070507060c03032d0605010c15091a0f010f06051216 66
    0x501154040024182c1110b160004002000074a0107810781d02c000142a03c0888207201d040208548010410104072945400c003064140c82d08800c0c40081c2c09000d04842c0252207900094414a0002480d0390041409450820140034090001925150300b402034180000040104104400d030700401804000c9180c01030f502c0e416124821b110451209980c1c0b800007559807070444a5850b6040101401410120002c02010440e41c0002e0002c00c0d081290b02c5c442c02a4001680850010340301203086000708040100351a519007004a18194044100401610900c400043c20354000001c4030b02242c1c02c0801400d420f454050101d8020101440c101d041545420b40000c3c81c0e052404007518102800c1b86500c036006800000204030340b5154040350400400415200c0418071a0b0024054081070800115120550341442c41d00507600700701604641501d9030800c004c0c000070b01d070354a060b500035248658049907182c43c00c450340d0003030704203c1014460800210381c902105500d040950580e9040c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 977627985 1250 977626735 977626807
    0x51509031201080303101409180c0315091b0901030602070305090a0b1b030a0c110f0904210203090112200c01020a090b12010302090a02120a060311030105010b 70
    0x62000079400ba844104941c1c008400d0000c1c014515081c40d000d403c0424101c0309542d0f200300000d1a02501414940383d8000101c140c0101c49804c3c84801c03002c0030080c0c00c03500c140c1c0d1050450b5080c44003c4030440345c1c40c0039544466a0006c07a0084103c280c10740240040038503425511000000d500000013103091080403c40403450b51181c03102e1100034041160050b0300e50044107203282d419402d12081001a4108000b40e69500c3d800600c1d4400942d0090780000212503980081100e51003551101307940030b40e002080204101d120b801d28541d00034030105031100da40f40d0150a0b03941e4020010100e0108880150446640070154031030700b01e880441c0b9080401d009501189200d9620021114040365000514446283e41041160004289000d0268680f840a4102102c0c906040c000281f18070840000b00b613048090f03805807500d8940d00041c820580c00d0805c00c039801449503202c100c45c40140c2e0780826442d0b20b07040c403a050403a02d121648500d4840b484039080050000f01c0d00c0418040008014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 977629235 1250 977627985 977628007
    0x10c02100c0f0b041401061a0702040f0f0e1b0108181c26090d0828090606151d0a1205070f1a1602040207210f020a05150903 55
    0x6031030700d54083e88040312507043ca03060030b4401078220114031007968107045040186008e00c424030142c010b0300410305ca841d1180352001078064411440d141d01e0080c2403550078440d084155000004a40e003900880c0d5517660108280c0000e071009552960100d002d01000a440c225041d00803604584880240d501c480081c40c070342000d0751141101200001c009c48201e1020041a0718000e840032010030030084c0f00e25010b200030ba034840701100c134402002500700100b050030507500d0132081c03442d000400201e000580030382204004e101c5020f0540c0c043c0c0c1070400c00135400044400c100c0c4041400c2d80da52030000001e0304503401480d507141056401c8051283c9c00034044c1e02c40406e107400c0034450740107840500d24145c2da15040b000360350810040c0700c081c1282084415035002c1114103844c0218110280c50489000140003809000409003080c0658244098028030100b40b0707200001c01504c0700c900c12070340b10304101d0780d034800351b0030040550740302d0303400c0340750304000c2c6409154402e030003104403032a029000385 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 977630485 1250 977629235 977629253
    0x2a020405280e0706030603050304050d170d02090316030218060a09020703021510060504060e010201060510230301180207060b031507091a0307031d010c121505010c02100c 75
    0x4201000c06559607101c1401c01ca0a1000400130f064078a42440400c0c150b480e0a0b0300d038419480f50511442000452908021400540107580b581c3c802c0f0513511098181c820344080c1d844142c10341c3c0f00703006140c5201c1008103044424026aa005424036101e03901c425514240725001034a459488141e800002a0440c460b0000305244d034800c2d070180144046004054450382c0c00500301d46000c0481c100301340a40e551240584044405078500380c20030b4849600183d0042000307401240d00407299900040d85d950704154050303200c08400c54003150200e180b401c5125540000c0c0102c80b4070b842d240d8040c4090700400d0300900906c5014000000e0703004000c80c000791810042581c00d8048071400401c205006411102c5e40c002800440d5548441d182c0c6c0300044031007440300500c55814555500e069800103000d80112840703041055000700660407500034080c00c04504071144c01c100c0c0f4200403070114110f0b01010310300d00710b030010b8480c054681c04503800c000d29000c1c207480ca0800c1007803040310b04021402080f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 977631735 1250 977630485 977630551
    0xe0c04060b09090a020301120b1806010902040312020c030c060903030f161401140703050c070c0f090605060f0a03090f050a030804110117070e030709020d0605012a020405 75
    0x40c0c89680c8403031000501020343e60051038540c8035403044c4010084540b10b03081a0320722aa020804001c01ea80d604108040134512070b061084074418240042544405a0700410a80780540021545040790100807a510140c1390103075601030f000b2401e1070712941041800344c02c603803200a003039a050044034662050581c0101205405540c0c1040224050010001c40d201440c1040740003400f070707100040c00c1c0080707581c005400c400806d5034071000140c1d4400074100365030320a030f8400c60010003103a46080144c03000c2400c3c02901041890031000050520f0170078200c3e044501e40003446030600c80c0740c0c10240c0c000e042d060815520305101c66150b000091040c001d00483d14425205d41c051401c003030a0510030b480c0300444c0b0906101981c400b144409142482040d40200c144c034028001e0101d82003c41c0c1000050b078081c2901500200310b01e50b011001d41c0100c000c0d514280e80320304401029141d0009500501545071030300600f40503605015061580060b82d011468002c0c15003031001d40a4038600d140c000c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 977632985 1250 977631735 977631749
    0x606091a060a1418010f1d0f060408060420030a020a090e0f0f03030f0606030103050c04110c0f01090506090a080a050a032a0815030d1d030708060a2d0e0c0406 70
    0x81d80c0d405030190b81140c40a00c41030304c035180a42d4682071420b0b07c048081000104a0f2181c0f02c11401103a09668040450b00542005420344006040c907160401c400144000a4110444200c41d110060b050010741c51114a4004086040d00f03441e15091500601039480e009036180030300c08246000000130000c142c030000d094001140e0324070b00306803c0c03c40a440075000b0b41c4120810401000481e10003d00108900c208442c002001c100c1110751080d035100703000030440d09000d0080c42040d0403c065018409540c0103100740c403825541c0c02c0701c1c070340c4407040b0040040c2003020500c10031040c288182c010308500c205500f000180301050000c040103820784403114a154038240c41000d007060b0382c8100240c0c0c2010152140304c50310303076090000a859031512200c040401a804003803000c022114407502c580d0020240554510790345800e50580c9400044558010050519202c1c0c540461055149090350801141c0d2001811010303072904040d000d000707a06a643e128072412001196541d100740f000034070706 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 977634235 1250 977632985 977633017
    0x60206040605090304030f0213060f0f0509060f0d1b081f0c2d0c06112208060c03090f01050f1608011202090606250606091a060a14 58
    0x107403804105855009182e40a507800034401003000446094466010315070494030f61805022015410005065aa00a08415141d040b00041124a0300040019038a080c1c810780a81e543d50800e000210300442c101c0c94021803400401d03130116410041030200c4c003a00d982c1c98212643d48166891512610407081c50517860300e03000032051051188200c24020f01301c0c0c10103011700080d010700c0c4042c8001030460100703a440f8130056498414071840207503501907032003082000711540204042d10a03070854009000d150304007000b540116040806078004888641c401001266240c0c0c0c0341c1542070704089d200350068480c00001070003041082c004d00344900d8860720f800d00c40303140c00c03580100004a805094410312041380300601070100246e2004ca4842d40580d2030380f0b490388904010070500d01c41e20b45210704030402d0102c5d586061700c500c05000785242c01020203005a5861724109402c84000c451822000b1171041c0354403c1504095000e0400042d486c1455401e4003c504500b8045034482c10030b00c650b404c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 977635485 1250 977634235 977634241
    0x60a0b160b04050c180610080a020c100c021915230901090215041d0411030604030e0103151d070302041a070c080708030a110304260609190305031b04060206 69
    0x20284c15030342201800c5c0080b03514508014010034807041407015800c0400450030005541c6800c2d0390100c0d4008c0c3c10352811282c1042d1050f81c814001c4c02d0b8072f000036005010743d681100b46024486107044c0500d80150203800c101402d2501e18006028400f0100d606600c51000f021000c02c801007074501c00c8404900100351110144100140c0050482d900d0400c42806d020901600329605500c56045a04290031121078440f070030103010718103400d09030715032510070041044100f6622030b0061101303c00a0320144401d880e4200310394555849805104408200103054484042d0f225081c1c1e0b404c21003d007401854a500e4a0043d00341146415001040341c200044990030401c102140000604000b0041d046171410301619546030320803900100100101c200e0030f607942e0311060088070010840c44017014a503d00c0300042040421150001c800140030344000100c1201002c910010540010f149000c0b032a05103550a40e055080640010444d916170007000c04905c2c02080200041e102e02d4006040d58a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 977636735 1250 977635485 977635489
    0x5100b0a1b08030a0f0c0f21290604050906060d0e0f010c0e0303130b0703090e0109091a091e070503030d0504020a060207031106031905011503060e060a0b160b04050c 73
    0x1200c1c49a480b50071407500b0b0507848807030380c04071441107c5c18161034000f030507000c5100400301c8400c8000d09609800d1070300c2c0710088510403500842c2507100c042c0a0110302c4108050800500d400307580716640d005400c0c10002800b034a000e1004168444805500140e1030700078402851403c034010642c208140e5440e0a25200c1d01d070041805000102c00320b0007103103011011142c030703100041070b0f01c00c404a900d80401c0820403d4042c4d8590030180800030b0710600250f9503140c068018040c681c03800d0f240c011291112048000b55000d250f480707140b8400c01000c495000d0254400c0300350641e50160710600803507201055554090006120306034601c1400315650506004209501c84194004020366200010400c002238240a20801590040f01c40d0342c0c50780d84110700200d0305243d103171081ca0842d1070400040303246620302800304c503002c0c095503041003502c0d20f071200d0600304001074520540c0040c920b40108230a000d0072000b048000b410b5505c600c080800c03a0f842d104008020b507001c4402c0d0f0018130b00da420078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 977637985 1250 977636735 977636741
    0xa06090c0503011820130e060708070f0e060306040f050f1e130803150d0317160e040b060f03040b0a152105072c01060305100b0a1b08030a 61
    0x40794154004800101d05542d4010903451600c858004620180c003605100d60b1040c4880500440c41d406c14007220710050707184d5458000031034104020800210105141074032586038221061700d5a00c2c1c1c42e1100e011202000101d40000b40020317030081d2a82045a561046030081074001c0c40d10b00021039042c200303000514240e00b0701c88188a00c501c08030302009003400c64800c421a410780c00c0050a0365a40320103861110300c00b208c3d810745030854116803810f020558052400403203221040700e000019100c0e980030b0100d840b64040c1840004a04c038518070081d00d096440b03c400d0590044c1420b02d464496841e0031000d410841d01510500144e0003004240c201e81c0c01181d1036100800c109031140c0d420481d003006407000007002c9915408280e029001041000c1094001a00e0510314080921041d2b4000e40c00c40850f00c1502040d4010071000020a030b402401654007602c2c0c0d072186800c0250501414010903000310f44500204502d0213015461071027042039110f801806026403a80e646050104c0b2400c3e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 977639235 1250 977637985 977638001
    0x6090c0c030c011431030e060a02060411060903070501050309010608070b1308010603020a0b090f1e211f1404060c0219031b0f05010c02010204080d050720030a06090c050301 76
    0x141c074100808804074a007009500c5c07600014881305003002c03050141012104c0401e0220126040880064420202130300051520f00c204e10600110071f0075201e6070f003402100c0c06141d65a81e05071788014014403456009a02441c0e2110081c00000381056513046480d1411a603903101401340c0c0b60000c2c05412403d9070052950242c000f00c002884502d00e994081607030702c0518819051a41c1010400307074540d541e1748075200c4064030010b0010713a075200c510845a500c110b24045291080000d826030341d040ea582400c49228241200c6c003e85a008584001c1c804d240188604001060f590b41c000b03002510812065035015500411380000d00110b146e0000e4a007030100321040700a200c11404003400203620803c644803c0b00030b0710840152404501d4291500817800b50020115420050b20b0040c496055010303004454018044400032040203c1c140d80070310646e40090801414003c040318051440c0c2c090030155a000313400c564032162591180000c40d03c4085041f100406400c00c100118542400b410003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 977640485 1250 977639235 977639251
    0x4060611120c03030c09040b090a020912064c15030b030a020f04060e0f0a1808030a090c0305061312050a09050f0a0509041a180606090c0c030c0114 65
    0xc80c00c0070b100b010b03683c1c90000800c81c00a40074000f034020b80984454101c0360311007134080c05d1003001e418035034400303030203504200d503010b000c0c0d0703c0210600d81c203240000310140600a0003d40504010748084440d0710105a034221182d100c008090302c8124021450907100c0210303000c0c4c4202030040c104100d2141401040c55584101070400b00c80e40c90302d80d07000c10304400c11541200d0f032a1038540c2d4900854081c1003241d0180701c0c03009860080203000e0841407030b041e1003040380c2c6030100b001420b00d6080c0d50702015071260180c030b00c0078184000340307181e11154010001c4901564005150303e40d2a40c89924106003100e440c10759490039050711080004151000c405000704d4142581884031701c0f0070082100c4c0c9140300d114401c010a05080000d0744582c1038240142c03a0141118003d0325207814815000441c0c22100d240f044202000070b81c441c103840514042c0074520b20b001d054262074075401c010401c4409484d4400d980000c00500e03032654070810003084411619000403038088150b92003100380f00c0000349422 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 977641735 1250 977640485 977640487
    0x402060f12041b03050607200d0c051002030709030308040c21060c0908030a0302030a1103010b04060905030c010c060203041103100e060612062206111c060b03010b07020f0406061112 80
    0x4c0002800450029404206441c4c01a0346000344804c44c035903a121034261340351030301682d8075007800d50b039005089085180c095001c41d0964107030500008102d100880c0e6000c0080c8803103500b0700000e44030b2250250068024210083c1403916406034460103c00545002a81022103821204100c0ca600500141d0b00d400d040050b603951070803018a84a1150121200070982e000000884c1d0400940c0a4000c05a00b0f4000740c0d00e943e119603c03084035a11901034000401e040680c001140d2800040d2404440c5040c0c1d05c400715000d003651a180070f07400c0500115501130411102e8000750702c041201e0740d070161a1000103c0c500304840266410500c01a040e81d01a5400c1e603031002888200045841d042803803048101010308200c5501150010440d5000f0b06407070411202e00c5100c01c0c14809851030f6203901d50304c0d120341000c48030b000d400c9840910620312040428401000601044405406142e0018100182803800c640008048a41d2904080b01181c400031034061054070402c02e004d0907000c40c4040c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 977642985 1250 977641735 977641739
    0x5120301050f0307050f01030e1e0304081b060406050912160f06030912080615160b070503040f1506051801170607090510140a031e150308030402060f12041b 69
    0x7044006c00710a81e4a8185a1151100090b00c8402c108001048000c0c102146030803c414400e903440c2c0c1c2c404c6c0304608441c800d0500944890881c104690800c10000b0411850246000c0d0182d0b400d402c0078401d41e0380a002c2c0300308a000050240056000032001d8500000000c0c20841c0c1003040e02c1e4290818030800d4549220800011000350390341d4101d45840c20f040120780d48100000d02004900740316480f4444001c038000d03400030440d200701c500c82d81c803a00d411078160f903403000c0c2295a0f010403100138004c0e00c40202d46201080c0c0c4102c5074402950300410106040e034403800822150941d11070402d1049080000402c050048001c910221030300b00000381206041c00d29004000d00c100b8086c480c440c07030300c54513600a01406603c0d0f403103080902e02d98182d150060100083c0080c0317a04550b4140140207003a10b4078003021984507200c014581c07440d13520600d0341107403a4030210b9003000780201d070000000c10104c500c3d0300c28440a0400403484025100b9989030601e4061030404610700306000c9441d0003c41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 977644235 1250 977642985 977642989
    0x30a0b120a05060c09210a03120c0c0b1902131505130902130905090f1b013e030406090b07020f06160b09071d010f0509090a05120301050f030705 64
    0x81c0030740001641e1a130030340311200a000203408441d02d0b041d000f40c0c501e00045c2111800d5010900c0c80585010341c4400205001e4402c42d0020350f07050400e402d000551045120b00012441c02986800c549684d04070803080c80301c4c0e14154203d0380150050401d01e02402c2e030030003000081017401c4401503ca860020b0400101c85104031100003607019009480d5004a032810b45014001c04c030b6170061803036641c14000c03818201c0c4159121f541e232035401c900c140949840014002000c039018402d150044c0d595081050321030110700c00d06513000b2501c03945048441e143d4803900485540c401560b50340c1102860b6101d02d07081c0064491113450307201d558000b5082c40550007603031340c1c1d120031100980e050769540d9030f60424042d186801881c000000300180070203c2801203002c0b0014208054841030030780410598440d000c4081008824401d852031703866031400c14011405d1621103e504051518103c0d0500c810b540d50f05d03420075409070020150428003000402507071400c0d036070b10030040000743c01030700c902820000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 977645485 1250 977644235 977644243
    0x2150a0c020607170d140708090c010c0f0f03081e090705040b0301020702040f0209040b01030902030a03031d0d0f0914030703110a0902040902120f091b15030a0b120a05 74
    0x1038452900400c0c01024044242c0c0180c00384420343d800c44d9994440260241c004064800201d00f40d014141c000890480c000c4c41094000e141040080c1111003043c0d00442e0303001c44204c81200d581800106240008044290220545119885170802d0345864006003c82103420b40090b02c0080e90706c001c0c020303035074004039400f010b03901c054401203403410300d40020034064402e541000350040d180c07401c00c800d4030a6070f60140440c044103c5040c0400070542004400382c5802d50001ba5058008604030400603000c0c0d40000901c0400e510b42d20b40c1892441c0d10b0314144000c8680401c00300354189600e040315a44038038040054501c200f020414070810740d001c02c0d034034011400b0041c03190302c50121070007560740c1d1254801f00401d180c60040d9980c030780b03400781c0c100650082d101002d4020940c50108160700100c51301c003842085002d004100d0f09007400d2107603103000411043c054001640540f502c80391680319000394031821140c1800304840348000184400040075002c0c0c100940c0180e071900000440c041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 977646735 1250 977645485 977645507
    0xb03150703150806090d02010e0c0603130303060b0a0207060f1e14091c02030d030b3105010e04030e1905040209030f03070516050612010306020a020a170702150a 71
    0x49000034600d0b40b1100c4940150782c440c0c10459003032045a041002118001821801c0d0082c1c2c0d034000d10800f050800010394a0000b4031145038841400e000080c60001003000b103000090280c82c001c50380740d40d241142480f41d03018410510058109400900009400041192500280d80b030140e084265401c5104842d1040860650402102d440c14400c4103c0303d40031780d0f00d00c42001300100074a58a004101d1403d011081042b8040d0040c4005480c49900a2054102918001d8054494001d4225009481d801801c43e464074240c0104001c200882540c42000c0c007130541124030152a0415040c007500d40c012080300a07110f9100305080540c0d801074030b022001240ea0507240540c85454490000342000c112a00240c0d42d0b00c03001c500340d410f0020001e5401c807540c50b02d00015040d05c1d1a08140012481020b0315286010180c0f001000007502981c000c15038410a4411b645440380c260781c5500c5e090b02448400b000707440000c16241d055107440100384060305440e4183c249011041100900040a61 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 977647985 1250 977646735 977646737
    0xc1908012301020c03120c0708010b0102330103060209030c040c12090c0504110a271a090306070e01030b04090f0f020607320604020121230702010b031507 68
    0x203101c00c0c01a0b81d00800204410450040a440202490490515490708040c00c41111803045060016540e04188200c940a50060313002d403424004003111184285103200f28041d940c018400d070385600249110246010b54420030307026950700c500300c2c1050700d01103004500c40c2c822807400304a820441c5c6c004e0a2a890018030400100b030145140c1060f20841c24150300251b0050b0401a5110450510f8002084240125201c0c01881107103815050030400c540d203084148004451000e1101c00c286848403e48800382d0503d183ca009a4034000c60304000054070305c5404a05c8a200103401d56070103001e440c404a80c20b4808001d00200c50312620210740c2c00c42400380200440b80030000c20b42d1540c1085404581c2c100389054a0108888410040c64a0304501f04080384842150041d0400020844501540d0142d43e00e8500000b600c0e007241401c12000c012000d90380c2e59469640f080ca0f0100c141e061a05140d0480b020249840800642980c5c1a980e400744287c1041c400d80c8000e034401d0700004e4006003a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 977649235 1250 977647985 977648039
    0x615090e0a02160c06090b0f18040609090b10060c0507050f01020f0d0e0108060405041a060a050d0302010f0b1c060e07172b09090218090c190801 64
    0x40107a00c500921910035401483e035503100c0c072001400110341060003140c0c40c44e503c010740580d80b005003501c0390040e1103800028090400c800c1b1a07040c00c11100c4051104000c2002a17030381e40c1c40841408460388468205d420000302010880030300000d103420380041c5244c2c1018110344000741e603410f45402003405140c1c03040500014440b5076900c03c000c400207805000084582d500c1c60b0601c098001c4607051003190002c1d101c0c0c0c0000300c0501b814001c080c040c560042d01d8520901d44441d0140058174014039154100304202e200241c960303103003038898544074000d4000003010050350071040151015050101c0c010018407217184005800310030f902c1b000603004040028410119080182040d41d035600105e50f543d5001c060341700e202d8002ca424041c0b041458000700007100340b840c0441c0c454151640140104140318003c001107409500140106a801e003115401050940000307161044140c078504c00e11100071507111558654480e003580130103414100b06001e51700d0080f228007680a501e0390412003800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 977650485 1250 977649235 977649241
    0x109060e0c21070b040f14010203070c05010c050a12030b040605030106030c06080c0f0414031501060815010908060a15060e031b0f0405070513060306050303070308090f0105070201020406030615090e 87
    0x14050110f0005000000343d03145d9900d50b0341007141e1940d000b40c0504000d92414400701601c56000004640c00c5030b50107113806040514240043d1090b0082c014107032590b0107221340d10320000d50700000d031f04010501900e00040301e650207824881128400c2e0003040c040c0c0c1c074003074061020401c11651070707084510038a480300c000d07919016000341c58022486071441c0c540f008900418124132411440c48030040c142c00704c0e03840083c100080d08500d4000c0c8a0030001c01c10303d5003c20f0610800c1c00541408034018100405000d544280d82d40c90018102e850800541d038483d03143c2040580d14403220001c00c01031500c0380e0401d501800203511803800d10f100c5100c0340080026545c003500c44140c019070000006208110614150201a1060b03010300803045613a440c026001c100d01c1e000e8460201903d6002d8000c504083c8290b400b82c3d07124031b0141c108501c62142d55400c03400314600b40200ca125002580c005621685080300c00340584240d0f82202000c0130180e8482c121042e4807070340341d00c00c032412010310441e070762 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 977651735 1250 977650485 977650549
    0x90d0c17090d0c030305030f070c021e04090c1e1a090906040e0d0c03200304030b061206070e040c09050f150f0a09030c05010c080a050304230109060e0c 67
    0x10b40d00d00100400c0088000205164218019501c121002e50b035000003580c9400d0210b92100c45402c00a41c02004081d05007502984a004109048406400040c80f28825101c400740c00c1d202d0f520806604100071011102205400d80d5103000b0714100a0f04c5801d0342e030b540c0d0b03600c0c02c6000e07030302d10039014108641c001074141d80c5607048403204035007850a4882c0200c2405009080c0c0e000d071a03007500030407030032841c40d803505004400f4100c00d400303c800518101821030380c991000c3c8401074459540035100e1a2100c20a1b80140700290007008142c95081546501c42d09100070307510510a003030b0501c010010104400c1d1140710000405a1003212006912480710302d00b03050310701401c0310711444a0004120031106030380088460050b00d0044521451050340e40004442050007144000c00201d024058a44c440b4042d0000c0d5422900c281011000c00d403042691406204030300041815683d100d49403942840400c1c41049100d00c10440a040b072101d003003010500001d50200c0500c074003030300080120020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 977652985 1250 977651735 977651749
    0x2071a04080412050c151801030207021302190305060931150e12040f1e12032c01140d0609020a0f09150c0602090103140906090d0c1709 60
    0x6480c0d2000800c25110b8907080ca0f40c0d403a84255841c0e030080081c41b0a9a919190b0350055845a0500c1705107010418202401180607400c06401240c200b02c0d45108401c0280450000e001c1007001014003500c94103c0d108000e040d640081c0507680101e2007881480780d800c00c56a10302030001c500041400d40c0e10740000310a009c0110814015022121030304144140c001a0341140a0850961049a82103020045800041d10a51142c50a0000510000c000340d8903e20480b050b00c0c2100b10302c0c0f0ba034103940c8200304000e40000ca070f42100050074119046401103481034484e400160002d211407511001100040c0c440000c040f04487c0300341c2d012680300d03010380c1c06d9000403024095050056484801000700078100d0102c220b03039031002c240c407080082003240d814402040e1003595a951000b120307400d62030302002503210310030080c109905d40750030380f01105012822a0044007420f006013010325080c42000d0500600c19201000c00c030002600e04041400303580c4070340c2e03405015031209540e010407038001444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 977654235 1250 977652985 977652989
    0x1081305060a1b090b0d110408010609051b03310219091103090304061d1e1302090310020a0306030b130510180f0305040911030105040f02071a040804 66
    0x2a4030400040100e0052a41c00c4540b50001480030010401c070f10f26801c1c1c40801c21400b0303202c40365500b0b002d1058810380607040941c480080d8000315140940700e030390300c03401e5038040e40146607200d803984203000c1c811145800c81010700004951f41415403c040401b4032100900060b00c0c0c006807550b00780c00009e07a016400840282da07004001e13030380e250006800341300e400043c2e1054441c00c07450b001910310b52900b0901240d1086031142c0c0034600c1e103070908200352020b0521030041c0000c4140e031114003109407541440751601d80c10641d40c5c250801c00c0303c82003007400500c480c10300380e1280c0184002c1c060350302c000451184407036100300f0150312500284400c50083c5003130f600240c10070400e1002d1005080d8155083c0060602400a84500889a400103000c0e90001044807920040c685000008900400d0390003600c14480e02d880762619564190403402c1d5400030f017901c800c4000020041005180503c0340d0300080d01444400e50600801e41c8401800814150a0340e8400c02d0010004080044040442e40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 977655485 1250 977654235 977654243
    0x11090c041509080d0c02011b05100e0318010e010e0f0301020d05010e0a050108190807060e1b090a050f010b1c020d050a0b0916050a260702070f1202010813 68
    0x441c20315040d000b4019021449880414010440380000e01032040c400c0811503501a1115401602c051280085114007a07205454074014102443d02c0d191450142c01e1147d0074100046454000d46101d41001030b4114203901c3c107105200704259100d903001184403a0081c012503103031580c9940d4a010a02900c41c406121800502c4c080c00410300c0804029100d0180d8130203001088980e0b01c6020a50b41c80d0f00b030f0f003881c201d54450703041c101c400140c0b000000c1c42e0485c40ba50011845842d424422803404c103140c0700100c0074803908015032001c1c4c140300d1211030740524003081c140400d042c10641801840e4040c020003011540001d200f6649138160414001c4107030050300c0441d9904d4502c8007010040009840c4190410300301030f2042150700c0c14951721070143c030780400b08043d000002a0140e8680e40310403014018403611145009240d08403140307010704000300d804e2140321881e06c000d0007414003106400c503050381803944005001e04016150720031210b55084c2001159502c0300c0c020b90013202d000c444024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 977656735 1250 977655485 977655509
    0x1401111905010603020d0614090d021e0c09011502011410050105250c05130209090c03070903020a03051006151b151b020606030102340c090516090311090c04 69
    0x9040042e203a01223020840c09107003030102130320380d964410307181e40c0c081c8546401070380003d09140010b07900602400348081079030211000d03850305002142002100341c1c0290746001f40b9078104a44d0640a000f84815104045c0000c01549010480c000008a16000e4075040101c00310302054106020ba030040801c810440c2d11518000030307440c0400314501240181c3c0c4c02107040b0701000d06064070074025900221001005208182c1c0c98250400254000a124404100d40c0500000240c2c495507107610145002c0c1c4080e00000d1380c001c18110599002d42d02c4500b600c0031120034222081c2e40a6900c0c1d624030511040320202400c01e040c0040c41400313540028101602d810200b8500300341c2d640311181c0c070081a40950300280c5c1d80c1400c041c207e00034460900800030b01d10400d80c4140080706442c20184000c0c214944000c40941c4a6950384415504080e01c00c540c1c90b4207100b046400c000c200940c05060340740080d20242181c1c1e44808540b01250f807103001c1d0f441c003008074503003e41035030a031005024005055 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 977657985 1250 977656735 977656759
    0x90515180f0a0201020c06090f04050c160f060b150d020d0f1d011505060702040b0a0305010203040503070611041a16210e0a050303041203180609140111190501060302 73
    0x1c162544560941240544540c048140702424148141c03008078000808200600c0300300000d0101422b0024040d0381c916608100442030601180c01c1402c049000303c003c1403880c01c4070b1400004590344544c0891150582d005045482d400c44021035100c054000c3d00561502c40314a00c0d400a00002c051000c182c90420300d01c204540300780840c114046010314020b218212040b440d100003a1440e00840d41c0140d000c1001e03034090b003032136000526a988060070030030b41540d8075140c0d903003280c000b5075045415420004001090000740d026801c3e2491070303148503d141510b081c041500034400c84074003074002c841c081a608560803840e0741801c0100d802003080340043c0a00310140c12044410381d506408130b855240d00000600340420014280c4201500a620f1321b1f003051010703070074240e54400440c200b0422201064000401d0008039001b8429600e0b4500104e091612081c01b8086851083d81000154941c2d220000d0000030380000b5103090202c0040d51000900f421809421182c0001e90015100300c0c0c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 977659235 1250 977657985 977658013
    0x706020d111c06051021020f1909120201030507021603061509050606040506031f08010204060f0309050c120a170c0606010203040305060f1503010c1e0309051518 71
    0xe01990b45540350204040c241e00c0d01041c00c492403401880c2e0070000700051802c905001d41545440140d0b1403841c0c15a124202d0021816a40041d2090001045c0800d080c1d440c0c4e00c01d000e1021203411f040c1400c03000d560401540198520751010060f040545541c08128600e000b800001c0b10302c01d206500c40321694032030801001901265400195031101c0c400002000c0201e0300c0b60030301441c401002185454541810040550000740c8110709000502c1300200136011035086400080050400150b02e580c42c0040c09081c581e50a4070100506090040c102c00117003010070303604240c0c08101c804007401040c400c1020b00d4810860401800004041036130200d606040e0058a80c031181501200d00c84c0e901e9100490716801a4071004159903c1766011640340e40300e8805c0d8030340c41422405d500320448001d4000a0a41d8092102c100100342407810628a034000a4078100100c0701c54141032000030000d946080d6641c0701c810750328400c4950540030900813a4540709420000c41c9040865480d071580c0c1c02c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 977660485 1250 977659235 977659237
    0xd030203100b16051c090302060a05090307030c08330a020904020a030204080607020703020d030302090103110f1e0f0d090204180b1617150a21171306050706020d11 72
    0xa094416219174200d80c900c102100c800140701004954074030002074610760900045400c95522201402000d010f8204561000c00001c00103600403510b040d0364900c8c1158007403d098003294906800d100010002000002d0290150ba410700040c900d07400981d9401102c000a015003203034568024000a81042c4440d8140c001d001526003860a0329174035100d1607410b0783d0b00c000d10302c0002e4020b18415800c2c004a4004d40c054841402e040c10041115001c074440580c5a5000d0302e000313035607454080f45c41c044c04030215000b0a03906c0e0032181d1081c60900e42414a90f0503024030a66891035a80f038102010443d2103c0e0040c20400c030803807c182d44603800603e4040228032088401d1500001d0b100c0140310310b280f0545405d0101c0003007640c400c0442e250b19000360039026258420a0f0070a00c04180062500514403514024501018209040d41c03403600d88201840500c0107204400340d0b003800344144486400070400211100e42c03c05603592082d901d0030310302030b010b060885450b442c5800d402c060a5580d440c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 977661735 1250 977660485 977660527
    0xb0a03060e010b1b0304050102060c0d09170307110f1905070306110901080a090c12050f070e1009061d07120e0705040b0433030510021e0307020d030203100b 69
    0x513450302c1c120100a0700d150365a0040e131203640d00581c400d4020a91aa60314002060303110007494000c01e44102644850210071042d02203100b80400010401840c1d40d031003030743e03902a122540c0141c000700c48064201a0f8407221800407840646940c100c4104012007046084000d680c055800d02c5110004032001c100c0d6080307a03001c41e0109480d42c00141400060b07200d450740705030b480700411446a0410150360020504110708075070343d00c20300346440004041001260b00905c0e089000e02c1062800e000300903c141001c0e48070074149414198207020302244984000303140001341c05140c0041c0d0340d00804540c0180c84c1030b40d011030b091a00da40d10820703480100c4e00c0300941340107036014400b8610420500040f100005540d40d05100070095824081c1070b1154400c4072000600e0300c980046860703803a03039810900c0070401030314820b5001030910100c181c1c03040440e00480718049038074158607268801a41b0340385c4007a02c400416500000107002c0031130301195040070700160311403140c0b070308400000741101015903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 977662985 1250 977661735 977661757
    0x10803070611071e0602040e0411040b0a0e0a0b060403140a02030c010e030a060f0209040204060c050712051902010c08030c030f0a02030628030b040f06140708010b0a03060e010b 78
    0x1c405081d00360920002140c030b440d680101d0502c4603564443c8072480204031303110112511502004002486514a06400e0185016a11a42080008404120856111580c0140a0320f8282400c0000c0803901c1e000a070b120069100200c0c0b00e5100f100010b54031310840d00b00a14101c064401035040300b8001801c11211442a8100c50340229540015a0307003413010024941e040c1e100c070b0314160016075940c115565088003020098203048020000506a030001d030843c80002d0b0503000f20740f084c081c0420901c0003c00205915076034061460f11041e4845c4015407004110004104448045901c15a00e408d85150031101140e00c0f07040200141c2c15960007903070542c0d541840400840d116412074403c6078003421008008040c2d1003841029540705680e100e84008031588600c1300000820710a0714440c1c40f6611a8000e90720405040c6482d0046507615120300600e10104030800a10540001080d0b0540d45c804030119114a0300c2c07030044010300f5103a04000c50560000c00002007407080d00300a482002e2030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 977664235 1250 977662985 977662991
    0xa1d2a06030403390312060513091502070b160e040f02030114150913060e04030305060111030306090c0702040906140601021b0607240603050d030606030e0d080903120108030706 78
    0x102c0c0321000d01c00341111844c6111100034490400190080c2e04414124100600c0031031441c0d42c0f800000c0000c2103a07a40c0c0d40c0c0103600c5920010400510098025640c080a10114142801d50721440e4211800405446d03401011000046010b8000c4025880c80040100180700c0c0d0307070042000030040e400a1280d0041058030188514040ca020001e070607a80d42840001820502d84508024680207a02c0f0001d1090390345513008108104c6c1000605d02c41c9000762004110343c01d00b100010b09001c507400780404a60404d00c03d21211707540e02d9080f10741207131004410503190061400000c0c01800c182e24001c0003d032034403250004802c0d0603620b05109501c01d800380e1342050003441c11031800c05401e401c030700d500c800100030140001c0e070030040b02958801c0e5805040451525404c0c01021900c054005950550041c0f80175041c1c1c41e807502070300c1c01500a80c83d06010140c46002c0c0030f0340c6c60207410f501c1c6040c0f040d4140010b8414100b081075030320785000303c00024000c1d40e43e110001d80300d0f8000401580c000741 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 977665485 1250 977664235 977664287
    0x61e141c0501050408092704350a020c15040b03040303110309070305070501030218060318070e060415030b060f01120c050c06150303030109090c09020a080a1d2a06030403 75
    0x20607d0a9064030014a25051342c1c00e170340319920341c1c07074800c01c01101c0c601c0c0013101c5440c01c0041249030800c0d2003200300001151758407074070494017a1921440d02001445400401d0002039401901402c1c1c80840340c002d0fa0154507901e6a00d030a4007d400000f403800c42500c8040b0810103200c00c001485c0c41100d000750262540b0301d44460044082c0d2141d469070031102c204ca01009000350400400441c0d01a1814046102d100c9019018078284219a80040031043c00c003424001245440d125051071900c40000f903002c00c0780b65035500c00800d0380050540d40710308814150744d07040fa4081c040c500c03c462002ca07410000c107803a80750f02400d150400ca0f1081103d100c1d9100040004132624034070200403100900450842e072030000d40300c018101c0084200c80e980d81c1054000340e8207496002410781d645054842c1a154608402038001b114048450251001109050314400c030401160000b1416007007101c3c5288031803021f8402d6000020342021715040300000080109050340509d141c80e020303c1d0600c5401c0d1000b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 977666735 1250 977665485 977665519
    0x801080609030a0e0321042c15150d0207050f1b190e0a0902100816030b040b09040326040506131103010609061e141c050105040809 58
    0x2503000c444000c50303a031040041007211406110341900e00240241215108a2403986000041081c1d18203654844c13408602804840102038241c0c0082c0c9616001400c4054030302040100c0d90400303011742c1c915141b5a00505003580381c411201c024000340000865548159100500c000c1d8010345003a03840c2c0c01132100101d16040d004c80d140c242c1251b0341c3e80d10514803030100200603400e0703015007007000184441c2c0000144580c0d072050300c40c400c6503407035000202c0d0803050040c401d688104841c1c5804104040080090200d1041c20b00d400d43c000d03078a0700080c40b44900c07000c90020400826003a5200d100e88080004169000e0482e94185960030081c040d48c502042d22845441000c0e90018261b80104001a24510405c0100d0018a000d05892100c82d103610021a085403031175003107840381c90380700c00b014400c5036400380c4e00c0c032a429040d089004001e442c4c103121078104803407514003c1c4a090541c04080d1101c200340400b80016400c48001c0001d400c041c81c0180c0d0303591248200d54010125812200d0105d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 977667985 1250 977666735 977666743
    0x61a040c1806110c100c140c120102270315010909030e15090f011e08070921110a0e150a0b0a0c021003110c0304230d03050d0209060f0a080108 63
    0x8a0000c00140744ca40c44034410020003c1c1c0e08803c0c40f041100360031000c80816107504485451000000c080c00c00d11010f4410311a04061013821500da60b030040003c1c3c2d4582098414410090b440b0301d0455641100300c000080c249049051819850001c001c0040b40300c0215600292400380300c0d031115504060810140304100301000c119170b03403200007032104a009041038400c50581a04c14540300301d43c1140200300104038900512040300241c540701c1040302040d084660300003d440c442103e00362103421300c2940c1c07031900f01c0c031440100041000c02c9a44115102c00341688084d201c01c450100051501080403450390450740c1d80203102e8900c1810000d1601d00c5503046a078203400903510021403085980900598034142c040110415588800c0c580d5100b071000302505500e42c0500195503124a418604003070b08070642c0380034050708410507070808503564491010100592600b4042c0c5c64102480ca990003c1c0540e2400c140c00110000310701c04810000b000074003061805445080d44d40c1d0f280c0c1240c1d0781e2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 977669235 1250 977667985 977668007
    0x15030b040c03140727230303090319060207060c051804063804061d040b0306240613030209150a090f06091d0607050304030507061a040c1806 62
    0xb00a0496000c5041e0724800c1c5400b030008003031014241c410030161403d040095031701340e000001c07074030b0b100400c801a0048400c4840f240101100111300340b4480000194686a14003c92900c3d040800c07004070401c03504c1d8040e50b844035080b10342080400c406500103480366102240f030601c051142544020240303080d1080000b134911400300399240b19035070301c90340160fa040000200080c000c1e543c804000018483c1c003c0003c0c003801e83d62203203114404e0f821801b09440035448a80f0580c1012204085c0d51400502c055000500310030354540c001c4000b00d60f1132134031140c6091607002200007030201c0e0203100d07292281c01264401d46110741d040d901d80b06102021103800d604180d004000d401b041140b9034954020031041450044005440c6641300e058004403034480101804a0b5140454401e4200d000d12486a001d100ca082503460342c90b1a40c4c3c010300031300c10524001d20950b035510406001e848090b40c00c400d41f01001c1e00c100015140040c0c0541040050007401c09041501540440d42e10712411300300c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 977670485 1250 977669235 977669261
    0x1090b030f072102040b040f0b0103060503030403050a0206130e07020703120305060d020402090604051c0605090a080706150b0c1e070503030409020f0f13090b06092815030b040c03 79
    0x4100c3c00c1080a0000c84803800f200f640d125450380044a51a56203204501140c1c1d2014030024000152000142c00c0d42c1860380315500c02c0d04280002c0010440210700413607410343c11195555502002006510364580a4014130607401240381000251500083e44506407406080c0071030100c00420b804805035030341141c405401484241010b070040c01c0c039401904080300c0041681d410203480e0408a4071aa001c90740c44e103d1001c010040d181170129502c90070350450030410240000d06429140c0641500c10150000c0401d9a15600404a005181081c8000d480482400c40d510032100c3d00c0d031035441002064031030404400045d29016640001120022070f01c024024500785860181184001c4d0046004201901e03420002c410040700824018021629166201005142030030b040c24200c03015505118003868040182d8100b80e03880410b28106055003c8007a000840440e00003810705a05510900f019004600000c0e203182e010342007114001400c0e03904015903d001c00c0d01310705451640f50024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 977671735 1250 977670485 977670509
    0xb042102030d1808011e0b06030c2b05070203090a051f0305100b1c0e0c0a030f0501140709031106030c07350c0c0f03060a0216020901090b030f07 64
    0x2440e214002d0180018116080400040040d9990004e07400d48442c0640082020b101c10000302900049115668698200355116811032034070401c802c0c594444e010411801140d900d9035400030b100071581820f4012130004050103103080c0100d01a6481e0082440c1c1841401c42c25070104c1c0605080640408102c4440a5030030440c1c5910b000382c004001c060024640c18950301c80c04240400c2000c0140b420300180b00c540d42d030b000c401856040449801c0d4040c5462074011400103007080e0b488034034a1003960340143c842111800e280c43d00303500618280c80c0e5201000900403c0104598000410741c04680c004c407400010b0203050400c10946103c216101d5050400c240031085c04200e088644680204000d21218101c4004403085034824090401c1d150030300b100000c0d407100042051050203c15941560440e01d52840100000e888030300040841110550215031701402601a0036000440e540150a8944958452004801401254620038000d200d04580001e07018400260351040b00c1581c40341d0303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 977672985 1250 977671735 977671753
    0xa0c111503010b18032d01060e0114011115060f030c090f071701030f1103061017030f040807091b021b011116060801060e010c020f040608070b04210203 67
    0x80a01d42e009814071a04d411020414840301c0d07102040309501400c2d00700c65000b4161940381540d0740d0180c4c0c81310300b0181c50341801c5042015014612640d41074443c10002913032000c20030001291503210482010300244162040840403010030280d142c06540c05071002007410040c0b0041c0743d40e4641e41710609401140620000e1840c189610003943c0003903442c038110030404822100000a000d00b82c01c19681e42c1030802c081410844145100b060700034044d40688200e20b0031103d00b11100d20248108041c036081c80c442052845000d000719480c2517405503031180c8440c1c441703062603904d55580c011040680d00e4044103c14040b042c2c50394500c81c0140d0785c01840e09601100c149440c900112800c241801041c0644103c0360009000c100701920340d80c000c00071070a10b4504000e04012060740400240928494400c6041e640120b045200b190143c44c1c00948841d04000314005200d254400e03940b502800c100130030340444a0b4020000c0352420301044441440b0b40c0c80b0750414103040c05000394168412005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 977674235 1250 977672985 977672999
    0xc0f130216021504290f120a141603050711070303030e0d080c0f070f02090c03041a24031002161b14010f034805040501080a0609020a0c11150301 64
    0x215142c5d94200503600c034181403513030300c100e5403641200414015642440040080791003071840b8a809200501072140410b003011a0100e02100800c28004101600c440000302c005003da440c003206da040210844001c02ea407820018000d18000c070285a640c014280584041d40c401c03034403940a000701d17106141c07821440c1c4050020382d0b0b001980c111441e041000615001d60b03500006144506410705003103503686403a140481954040ca1044c05001c00c22034203000c000a0030000c080b85455010810300ca0045000002900c1d010090324403040d030031300000b81d04503243d150010703240e2020322461291515a031102076580d00c107036140c09040c114005402c030f800d480703600c101c0ca00130704803000e406c0018055040b510403002c1406105603c0b03125059144501e0300441d59035049038514108604441040160110000d295104034030a1030704001019000c64a800101ea001c94020b054002e021035071000751180181c043e4000d281d069600c01c10b40303c011001c5040c00c3c0c1c09103607200d2454800614507800c083d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 977675485 1250 977674235 977674289
    0x8190201120606091e0306020a1d03072105010b1005130b030103020d200a090b12030c030313030522050918060606181309020415080c0f130216021504 66
    0xf21417920680298400800f040302840180041e07003c03a9681c00310660090b01000e000e2071543c88171402503022101c1003000042d070404054100c0310251140602d00d082d42002c9000d0f010305010564082140761514100d19007020041410354000740300c9010b03840d40c6a0340c00c1c1c15030000b444007940280901c50004000b40840072846003190790404880c050f81c2d000804188080701c1c5400c902e820581c0c5500600a40c58a450a01010410b042c001e5240400280a09859020140498549082d0080404100b60166099400d01884141c1c1110800f484a8801d00822040e01c2102d0141e0703032810101d070103000304000810303011040f070000308070380d0300c070b0b1030501c000c56022021b8040303081e1800a6841282d41c5070521440a001e141c40c001ca07141d0180c0c010001140e01802c035000c1010f40308007080091a2003c1104c5100c401c0c111903003c807030520382e40441c0d1600305031014200c2491000507581ca4240c0859207181d003c41c003c0e18042003000d1817020004461103580580280640741c280c03a0000300420403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 977676735 1250 977675485 977675519
    0x2060a05040801090f020a050d081204030c020d0308071b0203030307121b0206090105060909060f190207060507120509120d0e030c0a06110427060819020112060609 72
    0x1180c014905962112103d003142c0c1c0d465001c441c0d020100040c075007945031034040b10b0040c0c03034100c0e25042064895500c03d14035124400c0c24203400c0c031480001500f818004d02c01c900d803e1381c0107819440c0800b680d240041643c5011594400407400c00304240c4201c1201c2d01524601c80e0b409001107103181c903290400da60700340326804214000307a1241c0d5901600181c1c44042c44800289800400d1707103080260b255800e44034000c4c4042e015510240803c5241c2d9400106130350020714580d4080310588071408174541c5e0441143c00e02406c90f000003032180422413598003040c85070354a42d894003599645008004207494007502c0e40032882d40040b40020414402d507005015500001200145111001076050f00703603003080c01d5002058020318181002c0c003060f805040151107900c6100d83c58241030942034040c54801c241d02c0c0000e81c85000032080d1920047c2c0c890409400b13008101d603203034aa00104030000c95040c0e40d0890009036200d2240d0442030050041c981075410030b45404029901303000700d100d201c203c50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 977677985 1250 977676735 977676737
    0x1716051008090f0d0201060e090a03020a020607030c0807081206090402011e1b03050a020d0311071e060f05010501030f020403111207090e0606010f05180f0301060306020c0c21070302060a 82
    0x3500b203d00301180c0400c0740718030081154001180061808010038069200148034a40c2070300217030075220010380c2c04202003540d564115401911414681811900ca1020305801410740c000080c100d424004104041c201d81005803c1150071581e0320400d1040d240000d481c02800f04d111340c000000c2190510465001c040030f1898a9118081081c81c50050710000003003e4022400024800420982c188945414003440741814004051407081d0b00a6510500d40050041c4403101020840710700e12095510308640c0080d000e11901c0980d01c201d00007400d023031040a02080c500032203408540000d009072403c0f01d4000034000b0041c04000309000e40c6600d266107281c47c41c0200a070101d00403007030348034105c0006104c0e8010310307051a01d0000580300000e081000b109020003071058010440700b40044c0100f484003910004541c1034030038040b07400340150b1340000300a1400464800d006820001d203445d01600112151483c0e001441c1240c3c013100004c100000380d640150f0400d20242c10144024002c0a9403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 977679235 1250 977677985 977677993
    0xa021c0e0c04050a02040302120307240b030f0105100f0b0702210303090703030912051c140c0a0c1703030403030b0f09090d1e020304060e0409020a171605100809 71
    0x18407000404030781089540800c5a5801b240070702c01c1d82480480c01c1c6c07410084200452909609031180c425042c541403480089540c034421121145000c1c0e004000030020140840e8015100d28810a0282c1011100424040c0d010703000080c081038100e0001c8112000e031103009d49881d40e0f035020b008050002800804c000b01a0340303d06031510340d0410080d40b0402c4801c1c00340174050f0651a001f440303070300c0681c0700810100703104002401040010601c0c41204164030107048101020b20401d40355484941c0807400e41c80400b1501c0103811401140c44009184140311425425441301720000385021403080500042d4000d1001030000303400b952003003d107440003e0440b640d002600b40000c07100c0104a0b04800c07550002280400c10503008051502e00c107070012009864040d072610029901e009034843c640401161405005103511a5070100c14800d8001c2c00014a0548610681e0107080041980041c14803a01c04841c168610740c00b00f034010b880c00140b10784c02c1c0750300f41082240e0405015008881c0d50103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 977680485 1250 977679235 977679253
    0x3080a0305040b0907230a0e010b040e01050d32010507050c010b1804020108070c02060403080405180906060d06110415120b130b130c021c0201050c0a0c05070b03040503120a021c0e 79
    0x1508c43d2054005c0c2994880c4907a0303036080c410044201030060340712502415100032490000b90205480b5845400103606071a007507426528181300c002e02071001112300b0751a00040c000c26540c003000500c148001c0c10028018203040b04184442004844100d01e5411002d5003c140198451400c1c039030005c800d031801c2c40b1500030310b40000d84968400d50080718901c83c0080d0810041c1012004151802c00c040c10020303140ca0b144010755290350009080310700c20740a11203403c0800c0841e82c0003203003101038a07072055216920741040310b00a040c000c40842c04560810703181d0800140718050301380c40c03c5e0081d020010041e00b92420102400c03100c0b070010380c06801e1a0351090a00b00380e1250462640943e4000d00c0e11411254000350780d03000c0040c40000316410320040000c5951a1412200ca8610301d15040000000754108141007c240781c000d000001000000d0205100000018004000d80d058080200f900c501d12401c0880c444d41070f04100c040340c01c4800e0381103101950b018102d4214040161600c1d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 977681735 1250 977680485 977680499
    0xf07060212010e07080405070e0a0e070906030318060914041b03060603180209270d050307120e100903050d0609020c0c03010209010212090a03080a0305040b0907230a 73
    0xe042070003008004120000100f101800c10700c185500b00b505414541105d0900b40c40c0c03030752030b480c090040c3e001e41c01041c40403910f03401701070740003140c40d42c41c1c6010780700307000d44038001c40e0058840d5100a50029400380040304650118443c0700301214001e880e1060610b03e0040d0b0401c1444540000c80e512641d10032840b510000210b0900325840c100740d40001c2c0031400d1850103400c5607450b9041c00395402420018000503250120419001080184031080400c164452001380b481c4030295166075004810341230110580003005903014460503101c080c0c840c90300c001d0b004d084588030f0705105030692203001580446451030340000611800703481c0241c602030007406154180c6010364852450070703074001001c024040051180a002c1003013200207618120b44800001e41d6800340d5090000f0201c4001240340b03e0f561019601002198400f45032034030703096004006001420110b400f0b598402076840010b105000c003003480019165182001000105003132508644480d00b8084641c000e80c2ca1030b0081200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 977682985 1250 977681735 977681737
    0x7060606020c100908030702190f03051c05120103140109060516030b0a03021008090106050d080d05071106012715170c060d020f2106030114090706050f070602 70
    0xd8421038000304124044035050001d04a0000085820026000300c00e0055005c0030040b18000d40e01200c0c03004040004a826a041c1400340d880060400c403426400002c02a0100e0b041c401e42c105c080f2a42a400d0300d1b07440654603031144c8180082070301c00c0c1500600000d9080844100708a68490000801002550302c0e2030450780d05032608190b54268904c0182140d07814003c0c02940c45040e9000c07554907140d0b42c081062840100d00784014010402c000400c01482584010000c000090800b01c0250b820300b4404425800500786030401803c060000d10a540184c00c00c60300a04031200401c4140c2c40d1500605c402040318a900001403141401141009800d0044081145920750200080c9152502c0103007414041c00c1030320029000004804000c0d524403064640d6092107510150b42e4903c003048200c158451000034200410b240d4981c03224580748501c6c1503105040550003041f004010206403042c490044030003a10315400079406100f401d10500180000481110015051001540d100c3e416 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 977684235 1250 977682985 977682989
    0x40305070614150f1828110715150e0a090c03080405091e011a091818030f1b010615052101050d060b19080a120806010813030203070606 60
    0x7001c03032103000c500d00b01d01d81191240300500013144c205000c0c10580b2118070103980300518039140c1d950710240e0345d0751b001508105007119140e0070f03408002e0b40141045003200b03500202003c1d6103215400600c5010481d292044c0c0b0518408040c4221106244c8070081e5661200105402041c40d100d082c1c020014050007100320145100d00f05030707510b5500300307401e110510100902c090301c400d1141d60311201030810b820f00d01d415520100402c2d00003020048060485102d042c116a4104c0089607400c00c04460090089000f601d40c842d04810181039000341658070b00a040004001c0c02c001c100c28500b9040c101240403000c02c5103000441c0141d91040080d08050640380b61001151000400514007590b039140c4000c6070000b90322560040d4105004203004119240005140b980c0e00c220088856444500f8031741022800851220f40b80d45603060349484a1001c2d0301250a401c001300d81c089c00700e003d041401d100d00010b9407941005d903122544c50b40201102d0707070164294082044041c011407070764010380340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 977685485 1250 977684235 977684251
    0x161b030509060723030310030b09011118010e010e150c12040b030a06060903030e060319020c07090513030e06030a0b061206030d090b030a020c1c020601031703010b03040305070614 79
    0xa20341e48801e82c00d13213550a140d589414560010401c105040c008001d0b248241c03074000400305400d80c4c4207035400303004007946969881504d50105a15038086200320599240070802c0e0b8506011002074001587c0b0140a92600c2e42e02c00d940300d0041c8020090100078003081480e85080f15900b0740c506c0030b840195401358005030ad5450000080010105090003608018051850210605495a20b004010141d211481442504000080344400041080c3c406c405e03002c14904560340c2c128810700e1555040184101d4001c2d508100000c0c3c080d40820100f80f040c0ba803d901c9903040e906904040100f258030040038070446640d14a1059030f107845100c00f420441d2510340e10701c0035900380f0b030f800c2600d800d040b0303c502c0e01004510b031001c3c4441502c01e82902d4110139090390151301c5018102d9124180b001403103400d204400c00000f039980d00c5070f000458604980c000e2205c0203c0c101501406e41d100e1000b40603a00b00103000b0030114002034403410081c4030f140c1c040e40300056850840e40241d15082c0003528517103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 977686735 1250 977685485 977685503
    0x4030201020304021207260a1a0a1406060a0f050706020403060617030c0d05130302060d1d0d05091c080d050415020c060103110a0b0a02070608161b0305090607 70
    0x30845c1001101654080503040041c03440615185421640401c805e5401c22044002038a10803901010040611368541c0280c900c90309ea0b14101c50204014411105a88000e04200c0c080850042c40b1807018003070760703014050a10309000e240c1c09690317041d003102e29001005030811206011589920240c00074601c42d000101d4040e1030a8140c1c0711031440081000c413a40c10401101d100741e000003d45000082041c105251141400b1020035034503155a4400b0390004030020386203003049066401416485143c00d0049460b43d985002240d0b0360740c4000380c48d00030a000b0012a170641c50003206c412055000c92014071480d820780d5a4290454010300044040b59848906101c01c101c1c1d182d80000b100c5080b10b078110b0601118101c1607075240410720000d004040d481e181035109845e0100d02c50054890b9428042c2d65880a000095a03103541e0311030782d00094900d0020510506a0003001d0004241980da21020082da00c1100c00462100d080118180718040001890039210f000241c59083e008030410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 977687985 1250 977686735 977686741
    0x8070804180207030f140306041a0d11030118020303040b0309101805070e13020411190504031e0f080309010b150a17040c060807020a020604140f1504090f14040302010203 75
    0xa4102e0121707240041c14070450f01c0d016041741217264196640084220313070110ba901a401c2000c0381c4e08c1000c41d00150846074014040042c043d030500341c10800042540204448095401600f2400f498001c00a6054204110400c20b19881e0703405190410400c4054072510b1900041c4101103480074011440848032a10641c0e0071f000c0280424401840340307407203150403498501280c0041e000a0700d1700a11a56440f00d04c00c05001d81d0105035840500309858100c401120710001803d41c0e003013480111000b9888142c40391910420140c1c20340030755032129418400041960b101315168100a00682c883d641e1412000c00c0f6644145014081c00e02403c10300e50349003030f42000149041c442d43c81c1c0c010017030a600244400200c550190808aa03c503250660158468490883c109035081d04061740c80240410003088880c07200b204401d0b025403ca0340302241e02000c005204540005e820304d000000411310017004461380a402001d0000c01e1500006403002180343c10102c210002e84003500107070f41c04810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 977689235 1250 977687985 977687987
    0x7030807121d160f150207031a010305070603021204080304140a080d0c02070f1406120103080322030906030b031009050303150307030c12020105190c150207050a0807080418020703 79
    0x1142c4903025070f01c10100e18050401e4001c54042e079940c8290508038a044c8802c495561003444003502442d44010086101c040284805114840a001c00d8406020755040010418024401c03500343c4034543c01a0482d95449844501c8ad40c2c00040050b22405044455200201810322440c115207104590380d5031207800f003440103001c844070360300907006551080c4814007001610401440884410804041403041102d0128030749000752100200ea4010394070021040102510155114030f600e01466824030500e22841100e099420f81c3c050040b56152800b0f002d800c1c1301e900100300e111000b0b01156441c201c414200c504031005480c064034190400b0091087c90600c0c3c0c50707500d4051600700e005000441c1962196400b0119900c03d0f520321446020000c81164000c5050f9503030000800d10b158411100420040c00104941c2821514507a0303150111a8100b600d00c20b442085800000030004101c6680e200b0340070307500400050f1246041804006542c07124800303608070100d2488030268a503640740c54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 977690485 1250 977689235 977689243
    0x14031209010e011a04020315060d06151718031b03090907050301061403060f040905010f050a02040f03030e060f0c07150206150103090c0b0c0c01120203060607030807121d 75
    0x71803242e0b40d034107101d5120340c0c0110001c41107030000d004580060b5a9258144500504800384080d25000100442d0781e40c10101a0341c0310328110303640184403180e03003041400101c0355070b04a881016840030f11840428500d601e050000030a01c50781e072003101d1400b51404100505580e80c060091180d5000140c512028149051407542008440c1800343c119410040003502c000b02000d9400780b08000030001032980e030303038140d6110454a07002d00104100341c0107090041c080c014a0b03501008550a100108148039143d01c00c440481e0a440034004155046680494603507000c101407942c0600c05114000042030104001c1c2081c001d114000d0050629005e00e9120500703411146030706542240c0d08010f901c412030b00c642d910414007403030001001ca1962800b800c00a0780780d0010740001c840800c10101d803085c00030f2180501c55003600c40c1c0918000103107034441a8031048406940104080c451a0002801404000d07044843ca00303000c86610008080c2404482c040d004802c2260401c54100d500c021040c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 977691735 1250 977690485 977690501
    0x501110c070f21050a1a0a0c2307171809070f02100e0322051e0a0905071b05100513121b2312040e131403120901 50
    0x3441000590f072901600d4850b00c2c0c00c020f101101055040c03414404c00205000d54503405078040400f81a1203480407074120500070454203040a00d1400b5000c20106000e008005603035403a540c107920b0710240e540c155134099000047c0c100c035902640c548403150218100d002e80a400c090451003113070f40c52060104419407001510f0340c824050301c010750000c810340c0491074566030685410b01084002414100b507140d407041400358845038002082041640822242900c22100200d49032950054034907003214200030800342c80380e400700351201c041082145a0700a5640494141449010050300c0321500326400300151080ba0150840700103c0c1c1004035a1244c01e82000d104060810388480c141da50844240c05288080180400c0c0303c3d05480c4212000c0c40d18400550220801c0601700c2c80b6820004a90203080c0d4806150145503034001401a2070800d6408131102103100a000d911212100e03662070003c0503003560300050301d6001840c1088100000d142c3d0402151051200d45040d490701030071103c0305 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 977692985 1250 977691735 977691749
    0x11070309050922030c05010f0b0918060406050705071b080709141302030f0d031401051504180209040203070c0218090c01260c032e06030b0307030501110c07 69
    0x40c1030004140b900b071401c0203003c1560390300000220043c18203035070440b40c1038001000e86d0709000175404000308513084525415804e48042d00a07844d20790b03280034455084480c44503a40d01410000f004200140c1000d90441c24900b40289010811b86950038a00d40b682d1302001c0c8088003140030004a18100500c4002f01242078040200d03160b1004041003d210140c6840005102c62070000c00750f68060001350480d05030003080301c19201520342c01902600f5840c0c10095640e2030000006800d040042004a01ca2800f4030f85520382400c0400501e20010b50400000c8002e600b03000c000c0c0d013505d0724801140035401c6522952104000ca20401448105420f480005d840494041c012107002c001030440c030440003404c280c11200c1e441c1f081c0403d041480e4003104054040042840100e03101c030f0000710f000798088107103004e00c040c40c10b400a120008000c1c1c108819141482d080003821b04c6940603041c0444000d040d10300b01e0795251102030949210300c1d04032220301e00c0091440340100c0200f00040040000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 977694235 1250 977692985 977692999
    0x608070f0905060a030f061e090b03031e040b27191a0c0102030c04060f170f091e0d091e090e07030b0901051005010e10030e0f011107030905 62
    0x1a241008125502511034540200c4002c03075004030721303406134201403008001c21170104107170b0340e50394091084803060807646051860340800108002d0190300a91106103006801913180003403581216800f051071410b0031001c15010300000c60b07182802e0000380380b10f8030801441002003511801d00090301c40c103400418410201c024100355048024644d41c400c5403244858289a403201040c162268030403503824084c81d51000041003040c4088201034004d480f6555103100300c00c006034409454001c05030710300400e26081f003400540ba05000c0400c00364001d00c41c800f601c044241d054020310481140c400400003a40026200c180e69030b501000090050803100c1c42502044401c0c00004643d00f524042d0141094444034020520710007008510000c55024682c0749540c98580280d40c000c1100f515000b520000c101000921580700305108920000002d05524101400507415001008001200760702c0c2d014401540c800f007035080c400c0302000e00c480014039540301640d1800034030000c4160080703885091 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 977695485 1250 977694235 977694257
    0x705210f100203150d0c0e070302040b04090e07120c12110409060903020f030f0d0906020f1303060506061810031b0c0c060315060c0201031512020f0f0f37060807 71
    0x400c039011b4108850841303030444441d4440c10f408401911464004480e00100050300064051142c2d000d11400020303902680d5040341ca80e000302114280c1c1d05000303858460b8060082c490351510f0341c86800c2c01c912400d800d00109118002150030380b90910350551700381e41d40b41c1c0001d05144c0c041c801e060b1180d80b690301452a064909002e10f0160084240200000b940c0c2c1c0381d49410804190304907008581c0510880c3d48aa5400b8180b0685000c41c0c082120f5960414010407403500b01481581d03034141005440f1580091601c041c000341501d6401c50204054032515401030380e041020b044805041c89596040c0b001c1c8181c1400703e482c04466100800701071511081890000c8008540e4095406516049000030990b00048000d00322103200c0b08600d800030000000d0301c41c04d0b0440320030b0a0b8800e81c1d000c1300c100491010003440c00c4090115542105106030344403020700c2c0c510090100012003e16104035000021110006c80301c625041e01c104d9000031405024407600b069115610154078505145418 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 977696735 1250 977695485 977695493
    0x140613170c1f0e15031609060903020d11150c012909010b3004050c030a0809011209290a050601050409020a031404050c01030e0705210f100203150d 65
    0x1035860194682000402104401c05a5441d06069000702d1150544d5450303041c1510355920039080800c03d040422105000019014050862402100c0c4c00030207031860a00c6a843d07402e8004440540780da402842305400c090842144400390543d00d00f00000028080088a1011007100c0300ea03a04045042c0c0300e500c655155070302c10b44a14151241310030003d40754114140d11440c4800d8152200c0310801903a903041140e40880b07001148958060002c580d000d02038882071540790102081c025080400070002c202403035004511514034908191400501c2040d90b4551034801061440e2030710307001c0c1d240c0f014030101690801495410510484003000581022000030306284200e2042e4602c2ca900800c8407101603000e036200004003071601c3c00900c070341d03e403d140881d02d5450f0402e036180841e18111031002e0706100066002c080d03c0c0090b052943c9041031307882c100900100b192100c12540300c1d18041c0102c2000178409800b0800043c0c0002d40c0b00c0c148100302d02803426241d92294095031010710303604042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 977697841 1106 977696735 977696779
    0x20703020d0f05120c0a0905030a0b04060e070b032d0f18010b03100f0b030d1e0c0503030411011b08071a040507140613170c 55
    0x4003600e00003d40d4503028607913040e007203407841400003120704503600001e00d8a140c2e90700b8004074a0f9901c0700000e15213181d04c5800c03030704403022400740000c0040c02e001d940f03210b81c0520302a2400605041c94410540801090310029001d441188400c40d16025604c040e03000790006843d8181c80e0460030400000400e560001440c4d05c2250440301d4003a041c0710305240813000602404c00301c000400c4010160800f500322404141c0d882015400980e810130010b00001b10584940402c0801202c01405079440d903042c1e070091001520801001a02c04400c0342d41c0507910154005c9901100340048034a480d19007807090300031548064802c03d200400b070180546c01d129000284a0702c281e1581c4500340102a100101180d21502c801c1c044960000c0514022080c0a4006c1d03080681102d0f04680c07003001a4080040154102c58440c1c800c03e003800891100c4006503900c0c2c0c44051070360719680711 = true := by decide +kernel

theorem cover : BRFrame.Cov 977517985 977697841 := by
  have h0 := BRFrame.cov_init 977517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 977517985 ≤ n) (h2 : n < 977697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
