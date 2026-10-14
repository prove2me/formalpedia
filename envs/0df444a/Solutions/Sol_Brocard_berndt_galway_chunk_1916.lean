-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1916
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:08:40.243598+00:00
-- url     : https://prove2.me/submissions/0e4ea55f-3c3e-48fc-a56d-ec75edbd685c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 344424460 ≤ n < 344604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 344425710 1250 344424460 344424463
    0x80301090e0c032d060606031501360b120c0a110d03050f0f040525031b051c050c06030a0603050604030c0b150108150a03150b030706030b0f01030c02 66
    0x4261401c010210b0b078004e07440c00000c00f4485080d240c0f9400340005031203012200c2d03101003455441520b001303202c5810765071848450ba00482440c43e466041101c1e885a0351420019400380180e075006851303605581c4d0700030302104003c50450350058070b5241c40034020050441500c014941d404a044085c690320b0790780005090340d03000443e60071101d03640104408030819540c907910441c8140d0b100b14400405480341d08007048141c1003914090010b030460310169a50441c602110419070300500341d0060004d9a0f500e80110200c0081c60750903036203920b04410801440c00d9040309011645202001c5036540a0390f0b02c0a85c0c0d881400b0b4001e0040c5004800541c540400b45d00280086800009441843c600740c0750080c030982141900312518400f0038040b0390001103001203401c11542c1a12081d4039030300c40c0c40300780c2c0300c0170308481038a80d00c5025410007000117142c1c42103d0740c541c1d007241c1c004075200024200b05030401c45990480c4040501c0c01542e4501a996402040d100c010282000520760074245400c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 344426960 1250 344425710 344425723
    0x609280809030114240f0612060604080d030e0c04060b0a08070306030204111903061202090c0d060b0408070603020901170603010b0301020418061502120a03020405090403111504080301090e 83
    0x26295540041000f103080c0744085e445c400c3e040b0780060301c0825030402c0100000081000c100541020042c4490030b1030680d040e21054226000920043c1026958a82e4519000320f000c00000042e40310103000250b540100f260b8600f40d41c0882e4140003907401d002c0002c03654010700e0303c0b0f50f08004c0d803c408a900c01d40241d000c0030195801400034016101d55142c41e010542c0140320005250701c1c0c10600042d0340740700b88202c500b51030b41052036240b15216602081511003000d0082c0c07a941a0400c02121405034074480c1d800148203d41a6a40f0327289404000d5040c5090303548036506040c01084100c20aa900c041e00100c1035110907080941c0d0344503400400e004150001c0300a40541c80001d020404004181c101030314030650303a40034003545480e000003500010b07144030301c000036038041500e000c030f030520702d4010307107036808503460010f06266440000405e08402a0b40c1540880c0681c407244035100010302c40308008060840b0020b9032820103a58010091005129079034007140c1d281c000301100d50052119 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 344428210 1250 344426960 344426981
    0xc031615081b071109070c0503030a0903050f040f26100504060b0307030312061d0127060311040e061006030c05090301091506080a1a06010e03060906092808090301 72
    0x320343ca0b4501c91030000101c00845480c00e21511450000500003481002541642d40e4072402442c295125602c080d006044c40400403000c0c01818000c031188040c2e40340160004206c201030304540503150400502600d8007205001c480910a07007410000c0c07017000035545210070070662000440c0d42d100e080c0072004100d140c0c003d5905000d00034002046c540e02014280809061070002c024203a80c031701159050b0180c41030140408070800700100007a1042160200c3c1d540428802200f102c240062164200e900310707041125468806180e900c1141000e114a00031a000440101291b0400d0078140b00c00248030b04c54a420503841705c800100303a91013a8241c0d001401d026000348500c416525082c4030540d6421581c80c0b889103018030000740030b01c0c0025411001904803410384143c0b178440540c20f01d1104003c3c541414402007980d80c01041d10108510b03449443c004002e000182020781a850408800001d200c00c015404803d01c0f224807004034001608907070000750595252554000319014000c0c0c000c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 344429460 1250 344428210 344428261
    0x1101050d02120117011a2b080c06060a050d0b09010f060f1a0301051003022a01050a050610020d030e121c0c0203030112060504060608010e0c03161508 66
    0x44032901d000c04501c010b4142c8141c11070107503002d405000e81e0b83c01c80b0034142d0344c8100208503403509a101d06000d8a4800400c080d4640d0b403031200103041c420f2880d0000301f40c04444c2100700190f501c00c10700052009070340000017150382c0f00c52280b41070000b071f03c0c86000c2c00f0007802194a140214501003000d42c884518a4201002404811f9a980c036041392600c043c402c400765607032507100401d240030304c210890341aa0802055001c0c6030341500400c600941000781c0b1907904ac0c2c8000031840c0c500031003c0c5da1501c89105030300041042d1401005180c01d86030085d000c10b008481c02840074074100c1e0085000801e103503035441c00150510003200c10b9441c10740710b07006103c2400c400240408001848401800440c94640d406010040e50840c0172a52488244148034048402030701c560000390480e00940e030014010b600221350581c4444125003111140e01c5c101640d40e03c80e0058011904007809001600320800d641a01141d1900d5910a1429000401d000810405000042c0c0810080d048401a03500c400c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 344430710 1250 344429460 344429467
    0x10806120d030b030c0405160507060917091e031e19080a090f060903020409060207061118040203010305030f030709030804032415050906030c121006050d08071101050d02 75
    0xc2002e002402a240458020b0142802c80442d504190107101d01400030741c0030700c03106024008002c582a4000b41822074099032210185404280701e907500c500c1e03ca000c0c1501c3c41d66039003040c0400011031050082d0040000c2d02803801c401d2940c0114900aa280d50b107441801d501220714012030600042c1003884e0000111035801030240322151300a08000403840e250180d9a50701c0e2102100811018800c05000640c8000d052005003040e402c6045480d01c111030140c1855174075645c1c14203480311050101e80700072010842079110b0b12032051540e00d883d01034404610b15410768070764a0712441548031450041000102240500c1d210b9a664030055401001654441e81c60340b0b01100303010440c2102081c0141450003200310b41301d051080656100c0058880e000c0c4a25000510031900c5005111a50500410001c240702d61508051111804084405401001d100b0812101240c40c1e0b0f8006900907075190302200005040242268041364001d03035192410200c14004881c1e501c95911305400490010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 344431960 1250 344430710 344430733
    0x30204020f04150206010f060e0109080d0e0a050625050a0f06050a0501050406060f0c05010204080111070b070203090d0627290c0f1b07030b07270501080612 69
    0x7800a0020b551910400c02c4203c036000318100d0380c81c1da003030090280a4940306020030045008445440005d10181480110f05aa40d1078090900744d4444090700482c444c11090541407603c040c9010240008846481c24903000c2800250285020f28400c00d401207022407901c140441046100c0300c1c1d6600098081108541d45401c3d009443c1c00c0d108040316505203400454503241034086c0d50240c41c80c1c4d9444040006100100f121b07090710345030041e1401e5508102c0412091001e010b0035443d0512000d00310750318080d5184c00f034103042004000004640090026040542d214244a82e4042d040800401e6100d00f450f5810100704170040c0400141c0c0e04e04891001300311185030050746101000f00c0030082c0c540c0038904a00340e41b008a640d5a900d440820020038400091001340031461984900d1540300390304070440d00d00c0c2c003110350070594400b4600020444660b46c0069115003810310b1310703000d212380781d280080c0301d061400c140140c5052205210001d0125241c40074994410f00c8900c013203803036441c4030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 344433210 1250 344431960 344431987
    0x6270f030320010603030c0204020a0306090515150414060a120507091409090c0d0c050a0b131e0902070525140f06191b080d0606020c030604061503020402 68
    0x11000900185400096410b10840103114078801c8942544917408000d06e00d40c05c00c0005c2d40956442001c1c16510400881c4602081c49500c0c80b940c5010020400c2c02c1c64802000140072024107a5031801e074042000380f1901c20090440740c09424141c440648802d00c1d10000e8404989103040502824a01000c104034241e0180460084441c0031a91a2070b2080c103e0034442c8a003811949800603600c42c503155081c0b42084e8070301c0204980607008840440d40c85000040b000082075005a44a507000f08044140255540010700109054a21111381c0c040740000d9032035007a05482040600390380806d00b00700340310080c4511100c1e4142d50115800460710310081e103030001c4c40c2d4050320182c0c1045c0054200103051541d01d0042509004003c1800d20703030310040d51444602c0c102850b00400078400302c40e42604442441c205100c92040b41003a4550002c500c60303004548003035000804543c0015100031080c2c40118100750070a0b00100c0114450350422032800100344ad950009420038400034240107444003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 344434460 1250 344433210 344433227
    0x114061317070303110303040507030803060a050411090405060d0312050c1c060608070c0c03020405130b0c19080c0d0510080d02010902211b1518090a020406270f0303 73
    0x204e41c950110040a10a11668a0004541c002c0060384044010300229038000051580800e00502d220509904c51001c18144e481c02044500d2480f004215044076203820b0145541c4004252a140030140c1d040e28010701d8158900441005035a035880030401c003001c000d089514010802c100700d6181800c40c1d520700d000300003601c20351001416110101d06040c1c0320f56124101c843c0c003c0c265a2980782180c080000a10003d0440700c40f0724103c040b02c0b400903810010103032156412a02041d11688501c40b8141d45154103c3c0280820402c5001c012000304004e0542d0000e15414074005010f6541b007162605601d40791b080304a0500c56100c960001c1340d07054000f41c40d850310903a894906144030610403060320745416080b50258203ca1079030074000d54160b02c031505601000b00400000c043c403419903a0a9889000040416501f4140e0000e540c185148000d40000300140114903040c90090000c11040c151119039270006041c0704950f8400c25120040310140c0f2a54084590960703591901410846 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 344435710 1250 344434460 344434463
    0x20d030503071709030f0c0a050607050409150b0a0f030b03101a0f0d0201050310120b04030809060613150911041a040609050f0402070c150e040501140613170703 71
    0x89080e02c50061100c01591001e0150781380384d00960520a401c0401016500502c17001800ca00c00c1d1402c21010620400401c1e005018036100c80b9030740c0d81010380400650700c074001e07540c0184004031800c00000784542c1c01c0b6000f840007403400c9007000321590022000340c10f42ca4442c80d030500c243c086c001048402d070341c0203200307458101c180c1078000c660030b00c280650004552500c640c40882c10600d04055402400299032144850301c0d05a040c6440305180b0b4424401e00f40191a0240701e482000101904000519084a0008000c0809283c1440060300d402c04000c4c518100b1919140c1350700c40410344207a00720150a050707000348083c24580c00690b80a8000e4441e402c0c2d04801c0d039004c8254090400200e5081e9103150b17480c810001e0812040c05000940000f0041e000f650030400c100104c0c9161400710083c082100080e004a034510340000c2103100406000d900c203600d400d004205840d614411000019400e40e405511500000b51040e101da07410340c80000c51541c0044003402140001c100a01500d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 344436960 1250 344435710 344435717
    0x160303020d050d1503031e08090601062708011d1b040b010c140f0c010503102106020c0a0c0b16060b0111060f0712090b15043206031c030506030109020d03050307 71
    0x8000c07c0d0b00071103072620103841c0c149258201d2401402164420131111188400001065142d11100060401c0c8181103070320038030b503030b035501c03e00c0d0240d4100700d16100c0c03045000d55006042070340c103800c842555010002c50440c410350f070fa50445145030b409220704d4104203030071074038041783d01c40503800680c0c1702c0382c0c00b8003c400113010300d8039880c1c1070b503002c0c00035603004039040c3e50f61812060800c5100c02c189203140340300d5030300c18218141200008105000400b070b080001c1004d4640030f082032814401c201030319080020076140c1401808201e80c044902c80100a41040001c102c1f4030007000162800d82510309072240038000c0000b000803030944040007074040d11407541c400f03113044285c044000c11114140001042015048045001101d0010040b0012100204001021140401c1014a07080441d004800d1400d42c2c00c0f0400c410f1100c0340c800355224900f507000d4050075040c100e070502c4813801c8030041000d0541d80c00c0031526030384003540300d11200c542c01350070080c0040755800c010304660001c94502001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 344438210 1250 344436960 344437007
    0xe131b03020903070f060503040618140d030b0603090a020d081e0403030212030f040f15063b0601050a0c060c090e090a030e0d031103030708010305160303020d050d150303 75
    0x105d425110035a02140d030240d0740d080c1551102c1d614030001e8400020449100c46030040c00d4004956103010b4040c585444400800c48146c42c0c07040034090715100e10106100c3c00301402003044130040443c001c0e6103958121150800d11440303141800050269400984c00881320820300c2000c00030070001001a42d0094088031520520054104007600c01280c3e84000d44802ca40460300044001c0e440d100094030070a4101088442c000400d4100ca07180d6008410415011204038030310b503450a0a28140c048a210711030702d400403400d018a20380f41c09000141005400204280814070a01e413400c2c0066029505000c11450fa040040443e03103d8002d044002400308003080c0d2401c400520314001d140d054a521710b584445c802000014404404285d0621503000112036031008244000e6104848645481e00d1550440c1040c0c1e1804174004405030411880c0002800800e80006202030701c04118504543c0c5d401c110000720700940411000c1560f00301c003500d800b01c101500031801c06c04c120007407401c46c0c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 344439460 1250 344438210 344438219
    0x50a020c10020a0c0f02130f0507030b010e03060f061210020409060902160602030c21090606030a08030606030402040b31060521030c0d020d09150e131b0302090307 72
    0x40b0f104051200300480e44040c0c01d2400074a1024640b40703498001400f04a0722424250001c00366040c5591403108103950b88200850705030584681c041000c020300e0040c940c0b81820002c43c0e941e65010700360104a80c2e0001c000780b0640d035042d210140a0f408502601d00b081001e00040b40650814001c600c181400d040b00403418296504c01d58505c0c8100b01030300c0080190a48400e4001d610140a2441d60381c0700300a1000f40651020190b5181610060b042c2c1d46440c0000302c0d00e0410501a00c0c0d00c0c0309810330107860012402500035a600580200c1716030365680c40d6803002800030440400c129400001d10380c0f501900c6540c0c0085005070000c00000c10050700003410040040710124015180d0040502110381c40c2c00c80c0a000034145284c44900f01c901e0519032031501860885000e11810043e0300c90040c1d066240c0e0f02c144003500400da0f900300710b41e410760a0741000e000701015400c1240a03c1d014400044600c3c03c41d003084044103c0d259821003134040406008020394082604240a031203005400130303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 344440710 1250 344439460 344439493
    0x3051203101406090405060307050a030b010f0605160b070c150510051219141920090112030309060227090402101b0b0c030609070e03210d050a020c 65
    0x2810007000a103c3c2c0d241610840810009100203815950503200e41c00010030345460b1581c1c02409107004580b014242e600d000c1c00c00c0041010350700034008201052249051103602204241c03801644910804455070718a8801c480b64941c031540540961a145400d170340c001947d9200c40d0003001030303071020252706803520203000c8050038060070301d00c08d50f00940002130000d42426808814a110f2000312411a032000c8082e860a00603482000740264202010010031408012010650003c1c9407004504100040084e6a0840c1441041c1d8180080c0882c00b0030184070707a10509026500050454407400031040001032040703e03c5107030500a031401e030500e05c030745881e5400500c1140e00a040c90f841482c95030049601d0800c96242c848012080100d107000242030102c0c1912612861803800d40780d2030800100170400c03001500040501c0030603450101203072000300f10b03c184034407031440c0b01104013019440d50a803486004c03030003500e20345080d0a03c03995241d20340041c440026180219241500401170701c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 344441960 1250 344440710 344440739
    0xc0903051f0209030708250509160203070c060e1801140d03090f1211060a08060f0d0606030b01030c060207080706030c09080109061d190f0204060305120310 69
    0x30308580d00c004810160400786081418555081c0d81d005400c007078441c00440d1400c1c50b50381100800b81c129030625074a1043c090882c0c035a44009150b81c04003079140c040400d441100260840b18000902e681907d2041d008004481015900541c0061560750b240c100605a40c15500d480748580d0320340c036502d0080500310a505040c4c40f076041880403050400e008211210035402c0044040c42913454000134241c401d409140d004042c20215001d4189103407601d1941090b01e141520b1103141e051100c19407059100540f01d511901c2911441c900240c0d60002078698000400e0003001142001404801c00200d072044038102c03031041d02800915070310755100b41d0b00c9600c940210581c9501c042c408020741e51003500220504511400c040611980b594001400d480300003000742c880e5900d5015581d031421280600480340401e2002501e9245015801c0d41c02084000402618000d8401c011000b9035490b54802c2000b160b002c0210b94107500d040300f19a80700c5c0c004480f441400700f80000c1c0040c2000380304001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 344443210 1250 344441960 344441963
    0x5060412020c0a12030c0c0b0a0306060c0b070e060f070f060509010204030b0f1e0c070309050f01120209040e07060f1704020a0e040501061e3f17030c030a0c0903 71
    0x11010402d041c114030700c0c03131a402e906081d030030003400300401c0e07011903402c4a501c4081c0a51040041d0380340b0100e070018064440c285d00030130812200a006202084804030b00e547c019042d482d240354009500d40009280e4040e903400c00d80c20090009150301004040c44424103180e2040d04180a1030352170660b854200d018503c40a0003007045080000d020700c4481040c00c1c1c1c01300042840d0381c0459100d502d105070001c01110200e5480c640014800c1c14944c10040001c02403c049890198019030700b0b00013032200268180044805401040520300c541d0340341c000d1150b0301c0401c01285d2540740d49100041c009050300d18020042029000b00d11680f03840100c070f46101d66006414500c140d031604441c0ca000c2c900040003500e01d950307560030100d60340006244c252100103600650302070080c100382610400c2d4840003603806c007050800302c2001021501000400424420001c1000f100d042420924409007007126110610320f00041040082242c0c540618003c41d40707010200484460007109a4500195000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 344444460 1250 344443210 344443219
    0x30516050303040b03040303090b0a0e0c040e07120203030c06100617070203040b1c0c050306030d05121f030506041511120f1308030405070602010e031c0b0a1205060412020c 76
    0x414813842803080003d42c1c12a03c80d280024840c3d003640c80380750050400340c0e14481d626480342084034913a10100f02600364804201d504014004028045907a20121841105200400001000290358080c41503406e03140152082d56203620340800c11110031080d80c055074000c03c8000d19040e045290207a4003501c10400c5400030351415040103842880d41d00880480140d8003205140c901d06400030340504502c00000c0e07203400781c40e811f280c020507050140200d03d45003081030501030342001203083c414031030300f03c01054181698450300038a000c1c40c1446e260806001403040c00180300401005030200100b08104100800010710610f000c00403e00c140d003400c0c0c545459030000f14410160650b092508070b81358120306881d1b40d41c0f035035a030005a00125000e03101038100c000200603203602800303891890801c210103140740c03940e000c2c0c030849034000c0350203420784481d42d41d4040d82e419120320f00400050603a0054215408440b460300650310a011076003140d10340750840d41005400d00028481031303c890001c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 344445710 1250 344444460 344444467
    0xc0d0e0313091d0123090a0201081b0708030711070b04030818030709091103010c080118020f090405090c180c09090603010f02070308010611030415120e0f0106030516050303 76
    0xc0310000500701e80c0102581e5450400c3d500400e55000f403180341102c88207403200750100b51040076100d01501000b07241840d0b42d0070003aa0000180e034401c6260b82d010220a000440d14694000350001601925000400044000007440880c0b034100750041c0d4a41200d108803612140c84100c040c00d58055440021315092052007171030005e00c2039240c224900540138040b51200d41daa5414002a504001c0040d112608010503841c00d0782400e000c2c203003c0000509100c44594500030450b0302003032400d00002c460799808070b18107020200607070440e5080e50000f001840281080a00c0035145c41450714900d1041e42c4000842c0d42c81c8880d070950b2882045895401c6042c07040240a2004030b010060440d0b07895581da43c80142000200e1000c0d0071018041d5807660080e60509601410b900d02d0881594040c0d0700520041200440384480928004401d1800d0340301002ca0311140000380c41b240f52641031600514040c812103400550207801100d000d541103842462464603440f030450841e00074560150000c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 344446960 1250 344445710 344445719
    0xa06030b0a020a210c080112020f011101090c06080f07020d050d0b0402120a360f110312270a03060e151005040b0303160201140903060c0d0e0313 64
    0x40e07000c0d1000446904003610305071312821030190030310b0f1a1812100515076505042102550044541d800741400914401c0c1c004e50031b0300010780a05265150904105108500d4100001d00f034000814160748419240c04040d00c540001c0c0c02c0d8841110714042090a400000e441d16100003021007403442030742c0311146890790b8904940090f050f14104143c0003a020411000031501c1070940300e00c220100d0f50005201400c81e24038404805402155101201c09540d1604224040e07a010545183d4001e5844000810b10310700b190502032204001e0f54540500c0d29a03000380c140d00001804162004440a02d1092000903a0b4010700030080041d500610707603400c14000104aa8420304408100c01d04480900c90314010450f5035400c1100c60000f004812001000ba908103401071074881c03e0220082c1d810b02c1c84910b802c05140c10b4842020341004070144003040c50101d10303c200da03039000005c4c00303540c000e1610784120301823580b0a0200f02101403521700340c030f01803440120581e02e030352408000c0e08a40301e262 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 344448210 1250 344446960 344446981
    0x20a03021522061e0206150d0f0302010b04050709120204050403030e250605030708130201090b0c0318090f010902091512072003090d140d020a0b0a06030b 68
    0x101905034560240030440c9603440c02d0740e00c9441c403149182c050084042410010014095155032034401075018001c4220044680c02050350385e40030100b501c01c40c2e1344042c5200010781c1e48243c00c0d40604580e5010b9858018998190409040558240c0d014041c80c0c0f103000048030ae81170340384207102c01960181302803001440d0a07001190080e01a00c2c01007003111001c5841030501c444000342040403c0e180f118207040241e01001f010080c480b50a102d4151301e03048001400300e00000340720101c10188000514210380c002c00c46013014201d16030a164460107410304a564a03804650350980542204502080500d46807440610450303120030316155503440d145d900c10294004915450b401140007201041c5802e01da00685140c01c03d109500105080519014003480d0602040e9506011305005107a070b082d40001c21240318290544075901764035403904062440410810003940d5a0180c410100300c0c0f02d81c00200c1d04041d50040c0c40b501c2903915240d404404540c0c851000420203100d03440011100b501b07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 344449460 1250 344448210 344448229
    0x7140903010603060c11010606020105011212230d0b03030a020c1201091203060905130201090b0705031605060f07020d0207060c0305070606030503041403030c0a0219090e0601090c0c020a0302 84
    0x40035001295164603652920166480b2113240c800044000e54000c0080c0030900035a030041485000822040d4184400c40700028000c8001404103800c240c1c01140303161141650301c1c407900044101c55020140600100c0303c65000e503503101e005030b0400d205000341e840e0100440d40c40082c26001450112200030600400d40704000c0c110311555a1102070303501203034001d0842424225640d42c0019101c1c00d00032204c0403207201500780031402614001480060340c1100c00c11003a0340b86201c96588420b81c9140252840c0700740c40031510010803000c49401040000626203002d1000310011052503500d0701000c0381d90345d02000391140180d2010104101d0603008071482d0000c3c0b8080d11b0803502d041c1041d290360b415104aa8000c89042d413002a081011007401c602a01c04410100c014524000c1c020407255980c0700c082c2c40283c4a0a41e0045a5181c03203030705400c480c01049654000e00c044e6981c944640e488020034400c2c0e550041c100b02c05401e1b002e1050f45d5514200c0d40c020f0a0040184c01c6809003c503101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 344450710 1250 344449460 344449477
    0x6010e0c0409050903070c080c01120510080f0a12020312041514130c0503070f031707170715050105030a3e0a0e090712060b0907020c01030506090714 66
    0x1003101144442c4140900c034401c4110900450ba41c2060b8076047d0140c41031580201c580d600b0981c1481826a4401103414015036043d070049250384a81d03200b22410701c0a41d0041d03450f0710500601c052690404200803010740d001e120726030071800341c0f100d060340c03644a4014a501c04525000000780011003503031000400c0e00901c00005181c841c01c50080315800c00c180c1d251501c1341000d0760280c6c01c020090013440040c0000b0b5010300155454180402d0401c5080c0c00020000c0d04a120086030310104241a210300310f80181c250303c03c0b00045c0c032003140551300901065403a41071081191034555081d00485040f11005402420800e1442d12424407030340801225105655070302d02c45e185041940c09982c60100d168408070305a0608607010000095050f0344050021075200e010018107642c08103100044034000320040e2007410b120328201c401414103144481d44048140e0a1100391507000031240a440b4003070303d0802c4152250002c001c02c500c021a943c1001450881e41c030901c0c000048050710244 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 344451960 1250 344450710 344450731
    0xb010804080f0904091a07050a0f0509040e1911090c0403060c020a06020c0304180504020f0d03050405060a121d061314030301080a020102061003030816051c0b2106010e 74
    0x100f8483d00040940301801d80c00d0704d0790850707450000c1c1c5022028208a800100c0c60500d1031030301d1002940500b0218100802c81c06201c1701160500c0b04c0c1c0c807190003000310401000c003500c1084000380000c04010518580549060781c40907449029820065010b60162800004050600c5e1030b56882102030030f48174605404502400d00341c43d000513024006060284030040c041c43d2100c0c00c01607000c103440c2e40400080c0c021350500003032001584034003826420f4482d05480700c000072819400e040d1603610840d800310b60050000540c500095a03c581801030f84541d406050141d681c10000c4007090b0850030100551079080780307010800f01d072280d01941c1c00280c810000382d00c1e641e007084111411500240d004041581200203e0310031981d040c80219030203800540c14025a9055840080501034000c1051800d11381ca0b00420251a00440565403003060714003d150005100c0c01e4560082c5c0341d20084580070b8181e002040400020003590300c40b4060510004200710b030300c0c1040d207881d0090b004d020035010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 344453210 1250 344451960 344451967
    0x9080708030313051e0c030c0105070f080a020f1605010f02160e180106120b180705010311070f060915020a08061903021509012c300a150b010804080f 66
    0x80345c00c00d0507070710102c4e640101820a11101c0700c141414140c590003443d04111081014400080da4900b224000f81d81041e12651905400d00050b071404141d0b400451003441401820010100e26801100a6a20030b81c0c40c40440300030003005036650b40c11141c151a02a40b0500c0c10300a0940c10300100b41e001c2d500542c441650344801100c113007141c01c03c0e049056220702d60011502442000d10710b42c0e4020b003807441c51100c4139202207034440d00c600da28080d850405031561850f203c00701d803500a032040c058008040d030382140c1052419800802c0040c5044458581400301800409031500c00e8411829071500d0361100f079503500d010042101001c040c50102070952500102c0544c0b6165000402807030010226030b0f4446032540003400c0d01841c2281c200c00150034040000d1804c2c0410b0148400450682c0c0c03c0090540703000341205803100500032101034110a0b0b04002a00e8000542c0f02c4100d0301a4913505170b07103100480000700780d038031006c5e0741401301d1901804100058100e2005203288100240d66500f07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 344454460 1250 344453210 344453233
    0x18150902041d03180a0f060809070308040b07030807021f051f0e010608010b07080d0c030605090709061107030b0f19051003050f0a150b041409030a0908070803031305 73
    0x8100b038001401c01c1550b0000c10486032048440318180000001150550340140c5484903c120903001402003070100080031001c160a00400c005840c040e55010303810320303100c80e191040b011960304007107000d4002034403400105200302d00100d6044104241d201d901c90505040b04031070005004003824000840c0664601c074198201c106286001414858600100a500d02a4010b0810906803c5600d620904000382400990003c0441d008081c0c2680089460141c8001c20f4000b82120707031045812100301c000b04483c09500c400d40c1801d40c2c13040d072115607500840007141940d400e0b00b8080140b01454410110310b000ca0300152983c0d00c082c400d0004000c2c401450040c00648206854646c207100030b80c002841046014008952101c10b040002d0080131390a407184000820b010585850450f0307a103000300c0b602e40b9650408a094142d41c0140001400d0012040340d40f680030f0841400003030341451000c907844a02141c2d403c2162252401141151241610b00800c2d07034417028211128401ca403110103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 344455710 1250 344454460 344454491
    0x30510140d0b07030603202b020d03091806031203021e0c01060314060906010e06060f071b0e01060e100302070204090b07090617011e050a0e06041815090204 69
    0x34440c001135079012505034510328060006803050301c1e11030100d0f0b401000031003098452146511070030442141c1040180c220200c07086200d03c07030120203504104041050814036420100800c1201c04850f0205c014400c9102c04004503062804010511160311400c4d8001034425005040204180d00003048114280781c0001d8283e13000070408040c6035141c203020000d100110501440d0918104040c000318600b124805803106d005014141c07244140c0d001160040c0c4401c0c040d150840e00101c0f10561740c403c1d0f41007421046880c4590007a401c1903100f80443d04216102d80507040358142d40f2040c80c00c001000c1040000c11560301010100365084c00010701603901d9002d103000d500c1c02201e8aa881e03042046008080003d0703600014144402803400300e040010903020356046a0946440c0d40c1c2448440080b5411200d881c1c0c001540480320b4103000c00c60412248045020300000c403001c000f0300a80302a00d0f00090705100024110030141d0805e04180d140c2504044d030321900c020000540c50300380c2d80108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 344456960 1250 344455710 344455733
    0x90402040f0909020f040b062a0f0601090506010215070f1803080d0e010b0f010c02131401140d1109090a06111b120316030e030a0519030510140d 64
    0x1c610b00340c48503403540c29801d1903100c85030600c0c1c0c144e03403c2c0706078014000031403400e1151303500c0e03144443da4200002c0c1003a810300203540b10300300411050b07501c442d05074044160303185020301803100083e18000215451b036000203106021039203905460703402c9580f000c405032041d03030001038580240803464108602c1080b0382c41d900030155200e661020b84640d64020101c0488418070010b1000368905014141d140d034400301d0700c05001c0b9007440c0103034aa04140c80490304103807507074442205032030034041550741e00744000900a040e2a40c06c46108102065001081041010500090906030061941d1001814000c031610f82c040111412100300a031035035a040d003110685003240140c00d84c08141d0780c2c8020581044031203001070070402440fa0000d05404514184009000112070760551155100e915019402c40b180822603002a03e4a60740700f035101501c1940203038131a4110088103101440030750f000c5e2046a005108500001828074106160380003071b80b01012009921032b000c43c0030b1200140d10900003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 344458210 1250 344456960 344456969
    0x5030912040b07031211090f010c02040507020c01110102040303090501031a0d05070f08010504050d110a06050c09100807020c12010915020d1107030f0804030e030322060201090203070506090402040f 87
    0x16943c12140c01c00404141d804494481064200019010712600c1041a901c6902e8200c4050300400c4031140140c40d0003a403100000e41080c140020000500e030003040c030446254080e2500c20086555101c1036080784610301005001c160080420300941d4401d52020062031601c0444182c0422418005500b0107402d900031a00c0f03522560b4140404664030181000400100c0700910080c01c0a130744090b115901f010808003045015511807081c0d40d000c02c000326006401c08410041d500301808802600c0e44a01101405441c8080b024032809104141141c0321303075140c1d03014241c41120841000307038170072884282c0100d0790740350440f62010032540c14240303107400060303800160384144014000c410390324507601510311100d040c4240b5002c250000351003081219946001c604a540f1440c00350341c0101c1c1280003540510012400900140307400e03a11620a134240e1075901d1016685520803070070307140201402174243c1c01c1034104000034244003000d170645003002030001d410181c660060b04842c14150b4003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 344459460 1250 344458210 344458229
    0x270d090608040309051e0102120a121532011b0f1b06020a0512070201170604061802030906102105150c1c050403050403020f130c090e1e070503091204 66
    0x501036041e48e01000118a10501c070080d150605901c0140075003105a42ca00c4000225100e07200542c241c01c081c00ea01e00079100d0801e04070b458084160607500c00c41c540300c07500388192055103801c095560080f02e000f0105c03c8041403010882031141e40314003a006810404450700b28160181404410483d0092405410710f0340c001c0c8a00885800d2151800d2505c0000d060502c004001c1800540d910245900315140804441d11040d250300c4045401044c041d404421503c545014080d0300901a800440c000c005200c111203141e281c0c07a080e03520301103440c442d508000d4203411181c07022201c0340c00040346e440d000e58180c2e0f0911031001000303042807404642c2e502da082d03030028041d1145888105000161550040b01304540c1c6056640a4500d01c035034007000c0c1c451040303005031512642d01e807020070000c030384004014000d02d040e20602400c100c0c80c500440d103508804c0400516270400d02d118003800d15000c0308080c0c0d0240c0385c1040c2540c1c194005082107042d40202000424008581b90060000b41b4040304d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 344460710 1250 344459460 344459509
    0xd02030330090601060f0c050712300f020a0b040309080d050c100e01021e09030c0f0303090d1b0e07031113030b130209270d09060804030905 62
    0x200322a0420409110709007841d00c0101404240c030030024074541500d02a017407200507201181800d0310070340c0c01300c01d0003882071241e000081100f00e007000408902d40e209500641012041a8142d8034603203840b8100e0351009152040d4541640c4180050b254600003401621804007040d2511014158102c8003900499501282080311090070880418503610510f0700606051040b9905900c80c815071098403042e0361034241c1408055000c2d4115805100e40603c01016200710196400054102c040d40d14800e0141c0345e070303a241d81e003841c42c04090240300c000c019501e404c5058041150803d0020802e070394006560321a4505580400c0c105009008100e0b030840c680d1502c030300000c0645c3c4204000d1130018800344000098056030192400980358050074900159550320800000340181c0f0801030340c043d00d25030600400b5a410f0782d10468040c2404240c040082c0300c2070f409540e8486190603280051814003007044600d20401d03045400501c02d01d001a2050742c1c450029030100b81c0010008200706804 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 344461960 1250 344460710 344460757
    0xc0f170d06080c150a08010e042907030b010504050a090f0b09090c1c0210080a27060c02070b0708090a031410050105010e240d1401290a0e0d020303 65
    0x5240500100d44c03000b1469150003101c502c0104180018824529419003150129003001000d11000c10720b2802c4250b85080c40300c0074420a900c245058811101082ca4001480d003107502c504101c5003503c1003e4000d1100c1403401d01e8840041444d0380c20707814070680e83c071603412090f900c0412650042c40d811008180080c0f505c810041d004454072142c0901c6a1101c1c406401a2542c2c00704c1d42c0b8200380c90400400e00c3d41c0c0c0e01c0c40f80f0301a001c140b00c0364400015050280b03130005444104444118040d480030400c8a00c42d0005070390710085402803a00045052105070300045e0f0303800041200180240c07080e20300d29a255500c3c20440018074080b44150480d498840c810b007128866140141001d1800d03036110340311400072034105415102040c155841841855004e50107000844030300b00e0303082c8000c00001082249065003c1800e020340314442c6845600202aa4112106400c0008110100c00e00c0c15810010079500041c0885049070001c0c9403500e03c0015a40a002418602c1801da10048041c40c08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 344463210 1250 344461960 344461969
    0x41b020a170901080105010503062404032901170a020901030b15010e0f0d051903020d02060a020a0e04050604140a02030709090905060121050601030c0f060c0f170d06080c 75
    0x2000014071111005004826283e0b901c20b5445045801c00e00341247e584d101c220204004440d6880c035043c504190001d07141d8450182c0d00100201c1e03015110b5001034120f00081d03465680840000c44000128100c01030090168901c4803100201c42a001c840f942401ca03800300d502490300b43e10541e85400e00404005840890f940b15107810082440c000004035812800918140303001c94100380210001c508803010010100041c04404a43e2200100440060301d0020f507180c443c155000014003030320000c02d1091200d0b00964030b00e00c0c0143c40b800000d42080f03090100401005000543c011345550540c000e03440000c50290246482e98809640c0780b40110002c1c103440c0d5503038002485549008210b84c045880403030114152156282e007d010480803200781d58002d506483c2c044e10724011032000004020070440b000b400c51f2007131021903d03690b40d50784081c0d81e001c24025000e407180003220800800151100e10700d80c001c298846482c0e042c8a1075800090442d400f80e04009459071101407891001c0c81e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 344464460 1250 344463210 344463233
    0x30519020306010929030a240e06150412050a0516050d0b070324081c021b060d11090301062103030903121817131202041b020a 56
    0x1690681503166060040c0001e2200555203e00c14106415912050f03c43c03406038111900c0b04240701205880782031810300000140036007104c804100c840034402e001c8205406c55284200d4510f12461000c55031f0342001d01070001d03503a800420072500304001c08207000c042c1c03444221100340103000401a04403541b800034a02086500e200084500c03030042088075136154a5100c95250340054507070203540311548240c014207015448441c02c518080080c038a036540314a403000446000744103c41260440b100f2403000b403174071180b00c00b005800050030a18485c100803405e2a00d40d20280006190401d1058240200c1c0d101800c54540400c000500141070b160900900000d043c00a4046160603100b14004d540d0f21140e80d00142815150b42449091500400d080c42403135101000902c8559400c02c1c1e030711103040c04004200e88800f8200021004255160250740608102d03906c0340744180c1c10901e48258103100003204a92041c3c584414800f040c5900702203c20316020780e001070001a0702c0740b82c690305006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 344465710 1250 344464460 344464501
    0x402100305010f060e0406050315090d090308030c090a0e01090e07080706050403022812060e0d0e1e0d11010813020607060b040b030a210c050a11031005070305 70
    0x18101001400000d559060310f500320341d044d04007020783c41940c4000c20090305056220b10313031601603200e100e00c4581000201910030781080c0e099400f0040c582c2e40503242c54009010180018500340001043c2382006d40061110300e130020640322449550700361080c0046802d800c840b01c45030300c40305195880341082000802401604001c3c100e03441c2080c2008217036001c1c62002a20800c01d4800010810103181381e050000c2c41e20305c440c038903841d8441d20a01e1901c20818000c0f201d2a24151f404210f003035020494403042744081c0e58a07042d10080004025550020a070040d095004211581d01299a4054001e40e03984c0700707510180a40b00500c002400c5040001d02e80e080341901b035490b00c8016550a030480380b240e6400803001500481e50000b142c01040610f00b4541c15100f140c0c00305041c0181a072080100202002920316240040c4030308031070034802c480000301070740e001c11000000500d002200c0320394a000a0f080b03802402018440a0644000703464090100b55958103000400c1d02d1010114440b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 344466960 1250 344465710 344465717
    0x3050406150306022122140307230c01210209120c090f130b070915020a1e02030a02040f09080406030903140c2e06140a0f064103040210 60
    0x2d20708120f0105d1600605043c03045201b005d110b2843c1008540010729424130550011651a58154980a80e1581c01e80c00020000c141041a41d540c4980000d181080140e069640305442c074a6000c941710303040c070310f00b0310020401d4003400500708503200c81c5020303c22800c20a005000700c6244c0401d00c030054401501c01404010b89008110600705c81c0c1c00254200780c3c0c80386c01002c032950b910f403084408005641008894600384818180b0881d070000380000e01c84e0107150092401103242c41c0f8600b200a00610007901508241040e402500e0103130b002181320128024041800041940d0b1314a85c1c0d80241c20500c086036440103050145644505044049240148100e2404083c45650b81c0e0f11006080143d1503000140c941041000003048490700c4120004000e2012607118180c203081c0810404285000345840d140010381480c5c0c1a035507030100c429a803200d18a50f4a9842c03040d6410a1011402c0c00600da240922040162402c0003420484c00385c0720b0082d01ca0401c0e10410501e00c42d84444507040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 344468210 1250 344466960 344467027
    0x100207060902100804200a0b0f0c0d02010204050109030605090c27061c022e05090306090c0d0b04030504030807060614190506220902030402240a0305040615030602 72
    0x1410301e141a1580031b81200c0840440389662000504021a54000b200887c1e008601511140c101801800018042c2800c0d117003d82c1d91640301b213080b40118801c5500041e188542000851100ea00076074001e02e808090f030f64049241004504c0407a50994a200c2c40c0c410901000c1040c07846104050f04664119400c0001c4510f041140c02ca80000d0b840191103030a409030008481c5441d80c0c03449012032202028041c44201944c405040e03508191152802405240005040c808021821069070200140b156a4610795500c4055410384014001c5042c800d04000100218400d000513040716885101c0c0440d00e50306050708403000c004051b03000d07800b511302d8042c9000400241c00c5004181c4400b500c1c100d80b151207102044d000701600864443e0b01b424401400706205556400640c07065000340c0d00da003c400d0000501212948858040c03090b800820301000c48000c2c03007500010303089802100d000c00c21722001021110300c10081e91080302c92680c0020489071040c01e640101345450040c0420700d41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 344469460 1250 344468210 344468213
    0x3150c0304151805010b0a050607120f02030d0905161e0611010f020c0a1202070303170c0702040203071d03070315090f050a0507060306170307060e100207060902100804 74
    0x40c0c080980001c090200da01c40748104581164891040e100a08040060380b800e20708180e402425444805801280520705c00f250311308001c805c960700541c0c041c003d00111310074a03c0c1210340c21404242c460841c0410040700d22402e04038020b0790b92482c000d50181685a07219800100742181560200350400d035840c54020b508810344401c03400b25005030616000d140c10f60140b940c010401000410b80e030a10120756045488000141c500c8410311038035603010010f54001084c1c4c2d541c3c5140c440180043c1d14918030f401060080c040880d08004491b1019042c601c03154006403d83e002101d80c0e10010301c0c142007003c168503501c90507080d4008240e0203411031a040d03881d40c26481118002031288a0388821170681040703c07000507011080e800c83d0948001d9031603403820944800042c442c140000b41044004102210050b8001002c01d08a800851030310b64160b440d4400b5040800b15510342d801550140d201250144c0010043d082c8192400030751489284100084810501c0d400381c00c000d420002c110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 344470710 1250 344469460 344469481
    0x6050108070603061d09070504060e1e060d11130204090e120a1b150c0c03141201030b04020d060c020307140601060c0312110a0e030d021c030c030e1b0315 68
    0x301d82c041d8005c00a103465443c80301d42460142c59a103d82c0c2c00c680703400b80010b03d1454806040d0b0046280d600c1a00403903080004d10305042c6019119280d2000c00c0000301c01c00a0042d209011009101030141e46071150106044e004a82041e80102116511886c12a40c84101441400c0c10403044c855080d0804002000003407801740d0a000e00c195114840244206106100e402d422007000c24040030f0240031622480245802c141d9003048000c5040080c00d805014111415181c142c400c1c04092201a071a688820324203900103003041e40c0007032b48040001c0109046000d9051100055001103540c4e00c4240f40140146000d014142c1007a04004018400d85500421754100c0076094948050443e5580440708001c10701000114040d200014040043c242c000c8084400400304406444011000d01000e9031203c42040d20301400208680b00818418001e91000054591a02d0000340c1040c1c0d1b08059450501e07a05050003c1980d0201c082510b0300d401c000d20320701c1901101601055040550920 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 344471960 1250 344470710 344470739
    0x1020a03080a0e07031407150302120c160b4f05071e050a051804120e04110c010518070902090d150509010507050f0d020309190605010807060306 64
    0x2000c90f122007031184803060410030030010307542007035030800c25a224400066030740c44280f02340015100d25100b1040c01600034402d039090740d21500140d0001c0d5031030305440d0a056100700f03054000c1c0d41031005000d021506400086108008003030484254400201c040d40c0281140c8020358101518031442500d640c101702c10f0592060b40100b80a0b44500c6d26141ca1404c00004e90450b0306400c1030b48a03002000c8500d8034121040703540580b40100061b8a41d41031000d9900c0f403a24407040303016203901041c00250408081400605a0304e04810440503100c0041c056540140505808080100e401c4400100070310a55800103200c01c1c01e8100c8110360b6a015480d854240b09150a099005c503200d005912060300000c0002e5124580c0130104000340111402018260394581443d0718103000151041c3c0568100c4100d0503a0551301400c040464100391f010b544001c21400c000d0080700c040c0d0113180d140c802d0480d0103e11450022403d0340c1081f40e00c40ca44810b5910000405003010002c10060410701c60b072 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 344473210 1250 344471960 344471971
    0x60b03150109080f1506180403051305100f2f1b06070f03050a2d1404120b1009020f0a170601171503120c1006030816140604030f0e01020a0308 63
    0x31031046c0c0d1030000240b80c10850300703001c03043c0c1102c010410041541c4030b002010480304c4642e8209405407a40184040038681c1c480c0140801c0f8005004602940680012962a40032030884101844e030325203e8047d4a80e808100c290503030002246003803135000c0d842240c01001e025107145050924580700d104407074a0343c0c4005804e01c2000103140012512500045441441410403c8064040b04900f1418613403031115400005013001c0d407107007419128400715401c44d516043c560041900d50307110034204500180161006010304003001450311014005004000c41e48059203444070071040001c0c01c00d9946580c9074010002c40d00821000744e801c04030605001056823600900e5a40d1241801c500182a0500513454860111a00d8030003a560004041403080c0c081030300c40ca45003042030442070713442d14003000700584070612800c40c80b41c4c000c54804030503a01421910180e50071b4294810708160090750240c0019441c98400354500c1c2c1c1006580300c0c4040280b000340a503c1590301c00034070107d8003510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 344474460 1250 344473210 344473243
    0x3040c0302100203160c030302190321061203091d012301020f0a2604050a030f050a080406080f091507031d15041208090a02090a060b03150109080f 65
    0x11802c0b8503c200f055800d08200c6940d001030042c2142170007202c02d901c0380300c118018800c1c00068014210b991100c10301051307050f1105002c0100401052340030320507000007a0125a581c0c01c0004a06140c0c54100d60b842d030003600c41c0c8681307508111030344007005200d481c041c00b0b03074222100400038503107404003010001a8250702c0d00d005c065030030f00407401c2000f0600e401c4114414a196030050081030045080b813211107182c00c0c90a0000c0c02c1e0010043d010fa031164550000524100700041003034002c5450326107204105075590132200c0e40e203c070f400d40c215402c484005420102040a40c80190194507040380852000b0a0244605c900700407911030000c020700c08040e00c07111044008102c03851181100a6000240c8154600760711448015103030407201034070103244641200810b5400399010901076007080c4098041c0196580900c040b09002610351103080765221000500c4241150146000305c1c94064181c0030807640000040081e403903030704040075030740190343c0e0041e598000160702c458100c207209 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 344475710 1250 344474460 344474479
    0xd02070504050a0b0d1101030e0d020604080307020a051f1104030503030615040f240e0303160c1503090b01060509061e070602070f0b1e180a1212060b03040c0302 71
    0x244450082c0665040e44d036002100d040c4d181c1c04000303c0c500140d5100c4801e903000c0001c40411440159511800803400c00560001c03c0840c000c5030403540190350249882c0120340380958540d454516112200d10500d001c0e100d88506106220300d1801200700d40340240c81801e05203421500c03435039105d03c005005e0601c0780b80044165006102514144d60041502a0600c035071256101150382e180907000b1001040f103420206000302040c010880c1500c20702c03000c2e00035800c3c10b4054151480041d2820410350355620005400200c0c0600901100c02c503404955003c1000c1c0305525220061a0701a08214240706c0b05200c5010380303446800a640d0f04c0d4005801c041c402002c412401030ba503202d5040003810141c00003034003105100241020310b40700c610484d441e043c13664a0700d00400080b25203c070b810000c1e1410001250200701c9140c50794440c0c0d420b031415120b0702601962100d01c903128890041c00400e00d008a003095400492080900600041000030300c1d40c03920b50340350315003071a05010080c460902d0b00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 344476960 1250 344475710 344475721
    0x40e0a0f02030a0b040b060403030e01050f0408120c0d0807020c04020f0c0a060603050d05090916110f07150804020303070803040317040812060607150b0f0d0605010501110d0207050405 81
    0x103030003244200628290840d6030782007000011015109041c2d84600580c14440d4802c001d0508070100d07000c5a03015a0b074001c00001400044810381d00c21070b1000003842c010b200c0405d05000c240562405030303040000c0b0556511803203601f5800d004207810001c052002500402ca69180c001c0b640c00a035900c12180103035034003036030b1b0202c41c0e59000b42c180d124010310486000360204519a030015058038025030890315543d0f0b5403003041b5a64482c0300d24081d0881400700100e41101d02c01541c44088107014101a00c1c00e483c0c0305560bd28000c160440f4200c140d200071000c1281c0f41c029802026200c50340d00c0c207000c443c40c254002c65506d10540800810405000000409142c4507071290a400b141d1041a684c06003442d081c90341854009111040c41024040003149980c906007003103036505075020801c90850b1031003040301d5004110840b03c068200084004481450342d03800201c8403d588502c0c000101343d41024001014519641e54220080c2d202c084400000d540004001d03048803001c64000c03a02ea50789 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 344478210 1250 344476960 344476981
    0x807270f14041b0537031b0309080405060d060509160206011d040609060e010c05070606270b040b1e190b1b1c08010e060d0305040e 58
    0x25404016000402040459425940d09206081c02000c840c02e00c6030905608400d0001201d8100500100300b0800035450038040c00200c81000d0f4813003840e07080915100c1d00e04028020f003542e00c0c100001b41d452a49a0084401d41e66080e009551458100b01c12082d6541c2c0300d034544100c0c000e0078410b09000c078050821001d9504a6005010042c0503105103041c00815180748062070416403004d0700692001154606c00280c48544e1504000e000c2a601d850703a0f01d0352001020380c180203603015074443c41d403460180700900030b0403082083c641d140d99071824a03061020480701540c000745006074449891044082844500c18454004020700198a84807000007800a11802401c583c00405c8200c4001d00341d0b1611404212081050b90200c464a2000400d80c03400030040c0a4201c0c6510148402d81d0304010100003130b01c1111103d012280050a9940341d00c017044d441d4803ca04c00180220f00500402c110765648540003c01070340c5103400f107040d940d4040c001d1300460107020902e248110018200590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 344479460 1250 344478210 344478287
    0x7081504091a1e130605250f11030f0a05070606050303030c0403050f010506030d0521040c0e090610060f0e060f0c19020102030a031e11030901060f031a13150614010807 74
    0x605110340c5010407d40380d00030303000b940704903403181c04107512844482e110740000c001c0b60903400c9404c0655240c404c0484098540740c01c08001540c10350790751b55000c519a101000110f020310321034118103880e00e14500c0c003641303400c24594103103a660341080d05100040e100000d5490242c041800d007280c0345e08001501080f10344408203400506034203402408240244104d02406840b81100c03001d420f40c0d9164200355481e0402e40384226206e9402070208046072082d00c401c10340303440d03500c1d041c0c542411035030016005810112084042030b034000b0702c3c0710b40b551041050b0b885169000c0e43c1c003a810540c50300040d48a00800e0409814103854040d0301c00c1c0a429184000c01b52581b2440c20054520100b480300702c5504101d503581001c1d840c011007c50040140e580c214220f940c0034007103076902d800600510344001c00141800400f44118031106000030048400c07840000c601150010302149440d00803013070211401422418000c044050101c5243e21003060300c104020301d40040300340c500c0c1070381002801c0d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 344480710 1250 344479460 344479501
    0x120307050d050304140d080408180402190f090e0c0a031404050a02030c0109180b0406030f1406060603011d220308180607081504091a1e130605 63
    0x140705040003480381c0000145008901414800304c29030350000c441691000c55110314004141100c00180028290744028944200f40c40d051010303e00c41b280209003a0f03041422000c585000c124500600f10390702a0351140c0602191a01e006403c0c5011140d0389040c04c06091000c90000c000b6542c40e906009400840c20b105085e42c0214140c5418100541c403095100e000324403d018000c603009003984695a20000d07204425071249146d0100e0700601c0080260140c0b090f0041d4844200002044e00442c148810078001c00300e841ea00504214a2803d00d20000c00e02446864140010700c090b40c0c2c11a40c812a91202404805003a21404d40310201000312110200040c203201c0c0062040540c000c0849002d010324447e000306884610364030701d8540307004445103070000c1c1c624000550550031002074001e02c404041e100040e0540303030b92112000210940155001e0965030030501c00d4000700000700f880b41c2c10301c4003890000350410003200700c8d0403080c1201c05051300b0b8880c004500c21551400c0c1000d0081c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 344481960 1250 344480710 344480713
    0x30a0c0201020f07030e1306052805090f010f0614090103050709090f06050307050d1a2d06010806031c121509061d010501170a090507090e010f020c06010512030705 72
    0x706014a8010400c0d40300c4188140102500c2541c4502e1f01b8460040c00240c482c01000080751a0400f08400840403002e04070865a0000c808000303841d80790107071a14042c41c1e80040f4141d082d070400708905980003076a8012402c0102e051100351000141d84107545040c81c09180c04100c2e9201d080301162071049a0b0004030f90b85251140c03034404c40840f64001021600d0560951f401283d036030040140ca142c00a1020f03016003144284546c500044154160f8071206004c2c04400121003041c10501e100882d180c4407a400c61034a042c02055038000301c0b0740d076102104030001c110365818290b1440c023280400c22500244580303002840c09002d40b98014a86501d02801402c100030387c0c0b200e5240c040c105505c9031044203510344a20307031580301d01c00347c41074162001a1254110007a0005140694410041091280d00d6944001700c00080c02030101c10003c0c035000d100442ca10f941800500d086940905843c40d00c24030420000c0160600030a016044540c12601200c001d00150300702800c1d0b00c070341c0b08018003e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 344483210 1250 344481960 344481967
    0x110115090b040605011d0d0804030b0403020604061d1002300a0513080307050a050d05041b0501030204141c05060a020403150b0f092a1c020f030a0c0201020f 69
    0x194100e5000030750032502290280308a580e502c4c010355000f5035580c50990403030800d015041d858200190300d0109203200b0041c81c2e1038156a5240c5180a01040d101280140c01100501c0113000361030081c84072030440c3c048031403019070341750000030391f18101011200406500481e00c0b10300f80e244500284034504840c0c1c0c04c00400003400042c070108882c204d800a10316403802c0041140f00b24608400058280d0180d0742c6891034544003c169065080704046804009040002062030081c034090140943c2c03140d0f0350a0100071072144281e0b02000386400650405105100c1000304034214040c1c24210304003a542c1010340700a4019204a04801140c0070b401c070f219260901500079007030380c000c1c401c07280030340c40ea4000115050103010036a036034000d85a03406030b280e140c100f81d01c0c50b040b04072681140d11404614040541002090301d0740184500c03148054501050350303201d0404840e552184d1100ba064210300c3c142c24001c11071924000036003001d000c00d60b13a000000c41c2500035411500b82c03401c8080700948 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 344484460 1250 344483210 344483219
    0x815190b01201c050406051b0a150504030e040209060405042309070f05030106050a143609010504030f080c040902030c2203050607051c0e030903070f05010e01110115 73
    0xda40c03d00000214a9103a03680b0340205441c4a002940c040d1082c90b542c031440c241003c0801d4115007041c100c0d01001f03000e038801150014081d29880c00c1b41803540703840420a881c00d400c014185441c2042e00ca0300071401001030b03c030650f0fa48000c803002c1e230b08100c40014540c0070840e00c10200c84030413060446201e40c0c5500b40600041c00003440001c0715100a5401407890b2a04181400c0c0e8034a44281600012050f2092180880081900c0d83e00340000d04029804131043c0d00070151082c602403094042455050310842b0030314405c5006a210004500138402801c03da40e0051415003039074444c0e0100111030003c40c0d00e140300d0908640040030010815500c2e8141341c6151171103a80050411180e0b621601030300fa4048070424446030490742c200001c1c14090b81d80040541d0164013406c680442041d035201e10f54032024061049071110481c5000440c2c0b039000100c2410318101c0341d82c12402111030340c8203003001180c0e03106441c020412001c1c42c2000b00c2e42071000501e0b016100c4403a0f08140341007001c5c40402d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 344485710 1250 344484460 344484463
    0x62d0b12061e031f0e1b0420031305120c01150801090c0501110114040c050414091c031415010f090e040215070503030a05010815190b0120 61
    0x5008000884201d156002d4600d054030300d0001414226825801c1107010804660442c01007580c000b440e0000801e03103003044100c0030b0a00d90414108125158102c2e070311440d505191042c17040049074010b0309030250794810b55095007800020508071004404a00356030401030103201c407601071601c0c02c00141d216a120f01041e40a01005a860810b0118445001854030ba0501683d034655407c01c0320101d4403410f0200440d8524501285002103648486101d103200e0210030180d8407860094511808060814080106848005031282c40d19502c14052120300040818602c03c40405208540060701c4a03c00941c00f070440003107803010190070300003000382c0000c032400700c0314010200742d031003140e01d007a01038051301e400c1510b010b4101080140c0300048c0041c100311032003464a050740345505042c6a070703a0361294a1a4012901d03100741c82d450350010440d404080049050000e003400c40781000d8504280e09c0119043c3c402022456541c44007500a01d5034025211401d070f50150105a42ca490081490f65 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 344486960 1250 344485710 344485747
    0x204050607080c010f02160f030207050a0801020c0717060a0b01180b1902010218370303021c0f08060d050616080906010f12030e04020a030f05060103062d0b 69
    0x3c1c61035400c00e03035625600d8038588200d84d208640c1d02904031145090380c4800000d642403100c00c40661280c250046119950241c41400801c502c500250303070381180c406107a05088850f8031103030012061403034240c070b0f0340c070301180080c4e12640d5140002018915540100c541c000d65400d001405214800c010408035909801480c10000d01801c0c0d00c1207100b414000c900301d1181c0161603005282505030201140b405a0340b000e02c10303a081e044c4419900319001d21004002c58241c0d02240003042c8102041015010702c8512052100e2184800c40e43d00c010700040c10200340b004400302040300d01d81c00540c486e41d030201809615a004002c442c0140b40180f0032504052540d03001c1c02c040f610034030018511250028002e4182e0781042101252949412417900d940b54040d181101400f15139416540c1303944a038806440000115603002c40d40c0c0118410410072178001400b200e04060070a0700038400c218000040440d0f0080c2d01039440e050b0848040c090290190307981108481c0000003a11000a0b5043c01b400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 344488210 1250 344486960 344486977
    0x3130204020a0e010e09060a1404020d061d0106050c1002032a041706040c0b030c12151e0d170d0603080301030b10120303090c05090906010905160903020d06020405060708 75
    0x10381101c1c61107801001b22160701155078544c0100340c28014020a9812602c1a2900b07034050005030410142c1c0040c10700707030342607904842c031000300c4150160744a1208110301c1d03004101c0c1c0d0810b503140620558100f6124010100c190b5911900003000c2034190051880c040b1440302c481280c030b070320058050b00c1894180c0c414440c141d0500d4000728685082000425024040c42e40640c4100300241f42c00c240c00c8840d0401084112014020700000c48084944980d40d84210f4040f000200c0e440c1004c8108813240ca200000e410b240000d5803880032042e103a4205400740e031500900250303010352245042c0340241c4220700c041c0041c9803c1500001c00c101d052000745050f01d200c0c0c661041c5642c0c0c2e8044030181250f0a01c59000910b81028131140400d001e41d01c62016507000e5070310706840315210001f1459480090300c0c00000307a44144010000344180303228060b0040f581c3c20303441d1031405001c80010300d10405400042c0c41110309110980411079a581140c2c01400041d0007951144d1041c100340e0900d400103004c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 344489460 1250 344488210 344488217
    0x20a0f02010608010c050d0c0c080309070905070504031208250c1713030b0901060509150405060306060d03030f0b03060403110f0703020604090e010e01051009060e09070b03130204020a0e01 83
    0x2000c501ca420601484180d603c4646d6900d0800d0b4200c1c407d00080c041d003645d800c1c1444201350300309000c0394110f0000e62140c11044014210240b8140c0300380c0840e440103001b85c00700b0609010600000d0b000c0d10101444607050310b41001107442e03005040c44038241482140d001d0f1003100c04007542c0b554001440112441c0161400400c214540740780d84014443d5040851043d46240c1c400d00014800d0424076802c00451400050740c2070700d030400728441c84416540720f41c0350350449000308014601801216809201035000d4800b41c2405404100e2500102d1401070505071941d691181c01c2d680c2d680f12841404008045910b1410070707060182c6900310396182803903240242c1c03006401c1e40b0000990202240d501815051402c0e24002d101c2d00100320103890320540755218041040340c0e078024065203008284100649441714544501b44085885c0b0b81d0148a56840d800104448500c0103c0c0800440c0c0035424015500d80e20242d0400150702d54501c002d500a01c0420340d40b240c940d118a0510314901d0a89 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 344490710 1250 344489460 344489471
    0xa06030b0604060b03061207080a0b0a0e0c060f07050c030109030e0a080105010b1c0902040504030302090f09061f0c0c0308040312020a020f01050c030f040305341509030204020a0f0201 81
    0x30b02054030000c0c01604111802000030032a00d0070401152a0481202420f40703a12a444000f03403401d002c103503032051b150108003209000c501c0f00948112100581254028098481d8034808201175002d000341002102201094006c203011040c041d50081c840c00a00822a519003441e0142c4609031a099403802021010030224a8800c144a1035040e554140d10f040c1c18081c22042024110f40460302c50051251160f0710300c4010303140d0b0b02501d0701542c801d88001da11016220140718a006040c451036108228440074841c141e2102e4200c0c42042458001100e50203455403001d86081542860090885400c0c0d44000300780800383c3d0103002a64401c6150312110b4031031200c100d98690301504003030342c8070b150000300010b01d40c0580000c161644201094034100586600a807900d600580d000fa01c030b80c0c11540b0701207d0038485000201802c8040750048c4103440c0002e51070400e0440310700459000c038404000445020b40940011002958001d206640da001118802443e007911032865002540c02c4c00d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 344491960 1250 344490710 344490721
    0x40b070b0f040b01290c060a0e1506090405012901090501030e1903090f03060b03060a1404150f09060903030501140d08030606070c06091509050d020d0302150a06030b 73
    0xd40ea882c0642e40050600e0300303036400c0500b10050030129408040c0d1500d08000e401182e0200b00002e0070340b08540710064405440c0a8441c4015504100440340c2160030052100200c0302d4042021078003c0020349420038559962300d442401003010340da00c8001e50044c9105115000c1c5607144250360300c0801e81c0c03802115a40d0344015070640e02d141102c502c05403c5400714603100c603482c0043c0030300c080c060310b800c400003035907038201e68480c3d0300d9500292840c6840c0c41c0d505005003004c00c04150450038a00b410801b8100181194005080203000204541c041000044000707915400c902007000401104002408062610100400b109003045021a05000001903000b01d088808038800c9005052004450fa50355580c3c48298001800c49030302c80c406016181c089200c0405d0b00024003416155615030b04c0c01c19403c3c600803807101c803254040080c2040180655141c40c0549141c1550568500f101301c91703245820b900708601d540c2c224101e503240c2020030511310303c0c42e00700104490161240080b640c03640c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 344493210 1250 344491960 344491981
    0xb07120e0613120c0f08030d110412032001020a0903060b0906030c010f020f070314061f03112205060a0e0906040f030c2103050705070302150c0c03040b070b 69
    0x181c22402041140102c4100403849088038080710706440b502d0104c807120b0b2140340e00d250703100d070540080c0003d52001c07800715007484880c0310300007180d1700718110036003010300d000c9403000c501d0414007009003085401030960882042020350f506110a004009544418010300c1c014401c48492005441c02403c0850300d031228103101d14503a01500000d4042d08050401c800150360084007060002c1c118411460007120402e0144150700c040c611030340700414601d403400301ea41c0c54594090150030049840030303061800b8000c81020359085039801301c4c4048a0044020025424440c04075a9900d01d000b00410038160103250342c4400d02c280b200320340083c00c160b1501031050b0000822101c803981c660026000c80c000c00c500d0702e4044122842468281034041d080e564240582110703103904031528240ba00341d070310b00d203401d4000c0a5102551703240040c240328554030b000f503666110300800d0840c0760130603000c0780d84031880300c040b9803860f01840b00316a550396030344070420220b0b0321061b41a101da0a810020810450741d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 344494460 1250 344493210 344493217
    0x12110d0b01050105031008031b0c09070207091a030105070e0301060f060e0d14030d0b040b0907020a0b18070611010b0612010e3103091710050a060b07120e06 69
    0x10055101803290b03007808010354280d800a070880305007a41c42d01d0f0010b40c01404000070b081e40c6c40d131b810101d05d81e0881e507200301d482c102c901c3c1c4549214075042d07010000c2090b80005d60f582200d000d4a030200e00d1206020344252040c010b910225055401c140410401035000b440c10041c0308025002007103804d5944659011035281c41c040c0720000344d48119130500078034010718900310150180b0310701024080c2007403c0510b5903000716446007030705031101c00d44641d92406100c0c0307243d055425155015146408800251a600ca20388000c0c405c250503000301d80f5030481d2560101d0030a80c840103e80384a030301e0380ca0240c000f980800e10141507609201c20400d607803c0c04d0094a40d00b075514001521a41d00301240031021a100600e04c1c4071840e400c0d074003507210414004950400103420180d03111609480d080050800d111038000304180078140b03c0d161700511000410b1045207006070000206900c50042e17000250000741d010380001c14004c1030020134000107581800c06280203071160100d00c6001e43c1070148500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 344495710 1250 344494460 344494463
    0x809360c0a0e0f040e1504110307121e050d05040e011a0f0f2b0c02012a090905010e010509100e040602070f021e0f04152c0112110d 58
    0xc1001d007100009040c002c0c08a43d0716030000340045450340001c08040c3c40d22846a2954900d00b007080240f20602980e44800141000190007030b102c294142440c1c210600c0407140300500900720900c0d1682e112914188420b00c0680c1704054840a00d01103100400030781007400781540003503003107000080b04844400503030210f0710422501401e0007421020718034550407901040200304000c000700d01030a5500d80c130070b068403407101c0c20800f0780290150319034048910b5101d441d800c3da071600c0001510390401c1d0403143c4040d000411180a0303450f0940c806c8401110030341c004c4c400b0504240012841642100e0f110f4161103096880440680c0c4d5109940741e640c05502c2101c504c1c03034410011a0200e0715a40003000018020502d400c200005540416a680d016240c00500c03072525542d40c07a00c500e408100706400c200110b60034416905055115541d03810b00780f0407041d06d02030001842080580c020200c1d03503050484880241150380d6003c4102010764100c0c0100ca42c4407140d0000008c40ca0051002030702035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 344496960 1250 344495710 344495717
    0x1401030f02060307021501120618150e03040506190e0109150e01051603030c1202040b0d0b01020c030303090705090703020a080a09021203130509010e04050a0809360c0a 74
    0xd8140d6000d0144590000d40f48408501400310b0428243c002c0b006014000d0070ba41243c1d844003400c03802c00108441c0132007000009040000d000d100490104c60702c40900c5075540c880015545160182203145206981c0325a0700100b02260095590186400d400c6003041e461b103500c10000d60307800044690340718074000c030303000700311782d024241e100910031400040c01c0d81c0306043c12031806000c50001140c0a00d14281140003d0b107945014000c540d221410800c0500740203030542c10a810100c0c440e10b41c0c0507082421410ba651400e181d4590781c402c00c903104100380d02070103980e07603414078020641e154081801800d02442805c030114048601c40d1080703c0038511107a94003d07581e1150f03400780c3c000d003841504c1682c1c840d5035003012652030f0b24184000c4c03410601c2041646540703480c00c5e040c410741c100164410007004402a0400020410200d03560018660141c01c441c0d07150300f00c400007040450441c2c0449441c000740d4004400c0400030100100c1d2055900420b058175075103e1001480741e00c290820700d4000f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 344498210 1250 344496960 344496983
    0x80702100c0f080306180a0c0e0418021507020a0f03120e0d06051f0807050a08030403050c010f0306030602030f0609061030050c031602030304110d111203030a140103 73
    0x105070010040c1d600140000d18816501c030b41441d440441d00002e58221010b030b941d03a003080d0300b42500540f00fa42740c48005d80d07086c40092208542c281d66806901e0019000b130380f240306140b60412031a4101d45001e07500500310120981c41780300b0303120410391328007048481d000120160a0380343d020f42403411104a004000c140c86002c07580c0c54230080e00300648061300011400300d4102d03c01e044542d19a01034a56000241b2100b0301d001c04100000685500480d15504108414000315001240ba02c1d0000420709001c040c000d040c0f10300b100280f119510150520b440070061003d203004a94055004000c21160641681c440724204000700c04040c41c031001195106000175400d40d10389803c041400c0c2001c404502c0d030910b14009005031a000c4801c07140341c0400204111043c0405000d4074200d100903c001c605504c0c0a98580b40e0280e0b00c81007107445008200e5078101004000c85080300c0c10301002d001e420b81d0329104044555203420541d903840307500b81400d8500a500d074200b0f40c0743d4126500500c4e034620707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 344499460 1250 344498210 344498213
    0xa06051e031006171015050702041109011704080f0a02030417010203161707030f0e1005220c050103090f05011505040b1212030601020f0a0f06050a1107031812080702100c0f 76
    0x342c1c10710894a2080c084240302442c0580d07928460030bd10281d528840701c0d6500f1042000420744240501030625140d031030340a10011980c0b00701560100c01e1012407080d43c983c8080310907846c500130b5a00200d040003c411011178101c1c0b040d00a140120143d1940c2c0860724281d00050703811699034000c41e0324640351100042c40f80d511a810680c01218070907030004a092955002c07904000d034220545010702d4440c018099400004403110180c1c0c210356441040c0e85140ea66607100c849094840e1504241d03d40840c83c0c00e015070401c0041c0c01039401802041001c19001110060311918032071188614074210070070500e41450340c00300d48000705100c0034054414180c0e005d001341c2c0e04041c05071811840b03003250810017501c01f0803208101c40c3c010700410440d01c0d40b914000041d01c5c070043c0032119180c20911040c5114469405482d034895042c18501031000c51b0105072000b01c4947d50011040d10b004514000030310051800400045000780c86011a55a014106032502c001c1000002c2a61007540200c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 344500710 1250 344499460 344499479
    0x10608010f0605010e130204050d0803010f050f1c291008011e09210504090c0302040f260105130203010b0301020c030702090a0207060204060e010206090601050a06051e0310061710 79
    0x25034102600c6c01800d282d111808944445064802103c0a86002005000c0d082071803a41c0d60040c03104035000075045000e80041600c00a140c03800030b00d00342011148908210609154503901d800354003040012542d038402092241d0800d842100200c18441c901140c40c05040c02002c46444c3c1003110740c080d0b2180f51102d440108142c55040e524101c01028042070807807145547c0020921a42d902034480d41050010340850305083d44040034984100010440140f43d1030070355044a44002610700d0184e41103003010881d0240d055012903d500e844101300c0d41c40d08034203102d448039009a0003005a40c00038002e041c204d10843c0f01c13000b02603100780044001460818034480d48191003130f0002d401c14245580e000c059821940080b00814540181c0d182c0350351f4104442d650144000700140b289514040c089034861286010b154100074000610280fa10030210080d00e81110701d040f030035940d290040440039070391150700374140000e0b104241d8148061800450f207000780c20907512045880d250840c540c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 344501960 1250 344500710 344500729
    0x6030c020604120e1309030207150507110108070309050f06070e0301140f060a09180204140f0402090901140103080415140f09120d030f0501050103061406160503070302010608010f0605010e 83
    0xf01d91200ca100c2c51784046011718081d03020396a120790004e0480d2400e0944030301821002c6011441008000c2c492800455051a804c0081a07420300300100b6076210b040e400c50192140c910040d20340d01c540801021884c400050031445210a0b6540d6001e44501d50f08050986481609119195200300080f8040e0215810019004840144102d0101d551590b0740402d03074046c000e040d00b190300148000d8095081601a010420410134501c3c1d43d80c0c40c0008002400320300c058130180c0202c040b000040c2c03041c00c0940c040e43d5104040d4002400640e502e01e0002d005078882d000b4040c1900808000c18104e0740101c0d114400d040c005890b031401d05003060100051a0054400706901c040a80c08405049009001c0840b000c0c90554012407000d004010950950310183d011504043c03400100704003030300d80900e250702d680100319034441d5100000300107001d01803a0480d02030043e0000044040405405500040c21145038500a1103099840b840b048101c41517442f405020985000c02c1e075407603150101c1e40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 344503210 1250 344501960 344501987
    0x3060b0a0e010602060907120302190606080a061e0c020a03111608030a030e0309130509030903011b0206010e060a03260a020106050f0312040e0c04051906030c02060412 74
    0x41864003981d4502072460040280e0100025811003000c3c0120f2403410321051010b009a41d8000d010700c0800d0b64001d43c0c80080c00d00d6502030074402c2c5070b14002c000440c1c209500520310314085074022151400c0c610001d00d0707141072401e02d0641060000c1186140f03402030154142c41030b0082d0807001c0d550348055522040d0b8062000c418050140424200342c6c030003041e8400b030700c550030003141c5408110101030100c03260001040455070007440009490b40d074030101003048811004000c04c0f1901d0326a80a8518041d491203190306500b400306181a10b09884440c4900010725401c1340c5071640d80365a60507071040240c42d0113400004405050002ca00c0000d101181ea0b00b00300c248140c03031050300048848503003100c880800181d44401c002c1299240041180003514003c602526402d101800145240e02c900c0c85400c102d000284c00213203444003040281c0c4d000313020151411000e9002812640000007141c01001d0110740b41000340c0b03020910004141d8440c44e407102144800c050000001c1d200400b05212 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 344504460 1250 344503210 344503219
    0x80a0b0414030a08090d030608030d09030e040c0c03090f080604030804020126060a0b0f04141201150f0e040308070e0a0302270105060304050a08091315090501080d080103060b 77
    0x301c141e01420001060b40500543d151200d03410903000c401d0604411555010406040c10303c107000c0c241001c0b04803890051b00e00710010f045022881c2c1651901c0c504c1100c0e65000340781c1030b10b1081054114107444641c3e4443c3d601c5941d11a01d505940345407000728041d0002d141c0c0501c0000300040c0c06100303000c1d082401410403006002c03d9148404070240254141031840341d40100b8003a450030403c0507100034080c07e4000c0c038200741c0711a182d4002d0b030049100d00c1e203990030b50b00c1030600300c2d03150480b40700c1804070168020302c0301d8880720350a401c0c1c440300784c070500595031708108001a16044804c6428000c0d030745a55140c0450303d5855040700c8501010604a81c089074004000005940300d410785050400c02c5d140d0403500d41048c1c1c0302d403802460164080b60188400300104000500e02042d105011903000c100940c03201c1d001004640c01080c58260403180300d14124040e130341526180c3c0003208131201500284032681e2694079180c0c4800c0000c00c4100851000303001807000030300380e40108100e03904c080c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 344505710 1250 344504460 344504483
    0x624070f02090709180603020f060d020f0a08071e02031c0618140106030e0a03140f030c18010e01050403080c030d0207230d0503011701090606060f090e01080a0b04 72
    0x1000a103002e0025514403000c181c007010108480040b8800a200071182d03940104a210b103075801241c40e000050480d0f6118542c0015801c14841440e8150b03010001c0e00498941c5810b114800074001440507180c1c8804215a62034020300b090800e24a00040c6003280d005d14140107150b0a881c00c284007100c4800c03403c90b02c40201203008425451400010300400764040b41d601c10700c50311055441c1060708081c00305801d02100c554200800030700c50710400c1d03051610000760044180c406e0214014a1042c00740040001300b44018508218050240021001201e009a9000d4401951500e00c8080c0c1c9034085a000d21040006c00c0424010380103c00340e00742664546503100c1e00100882c0d00202e0100c828401c095a240714000c122a01c4480401c492801400303541240300b0042e00901051051074559144c0c0a100407285000713421440308194003400c24486c1c0e54803448007908003406243c8100c00111401720000c2d4851127007100078100d0f080e1101510030700e1115202c0c410444c00090080e50980d9420 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 344506960 1250 344505710 344505713
    0x60603210703031103100611010c0c0f06060807030c0302040f1401090b0d02040f05090f0a031b060b030f0105070e010207051e060f071506050405060907030c0c0c1d0624070f 76
    0x44010340c490341640c15070241d01c6d4201070700681043c400030b900c401c0d141e150203203103075819802070300c503002047d00b00100064110092400320060900d94002d8005401480c6c1c0000c1001501d8000030b050b070748200c405103c1c003c0780001c8442100c002410301106100c5140042140012552108100c11070140100421885c81e4000c10140d82c3c1c414848000c1590781c0c4c0801807007003800c0c000d080d80f10655001a2034a52241d8900500350041d920552182c200f01045101c20400554060128003402038150f41d1b0145010035032074001c10044403c0c001186a00d080d9206030740c40401d10a09407a002003050580c2c0e9a41000500d50211a40c00303503800510400401c01030700c040c4000362602c14030901720f01801201803d983e100350fa4007940704600441c05c0c5010b00200f039a03a03409182c1d10809c103180014800981e501c08888081181e10081d03d50a042c00f030124846054101080f0701410a01000e1400e450b400d05000c18010448424030070344000003011160310000788024900c46003d9400d1101d1400b16 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 344508210 1250 344506960 344506991
    0x140901090b2d03040507060503040b0f0613090b07090f0503061603020c1f0c2d02010609020d23010303050403060209010207050402042306040b070f050312100806060321070303 77
    0x48205662250030b0120421080080820425001d49444d241403411410a0341d80c00070445000b50414401400c001d00040147c0c03640412595038106001061140c030003d810203042c0f4100c1543c0c490300284002c1c0012038800f90000c00700c41200c402500801d00b0f80d403002401d2a0501400f900d840170075800304003980c4031010404c1003100d1858850340d0045651001c12944044626041800c0e003406010001404021125031840701d034584040344000103c0411101240107005a0f0002212241f001c515100c80c0411030f885000140c200042c00140003c4040ba0f42044100900c0002c00050b400c010500c006802500a090400701c18012120565280c400281c1641c00c16082138445000e01c0421000102186209031004482a6100ca01c0c26003001c0c00c41e074180c46120710203000d940c03c240000341000340c02c0003102c101810300741c0380300c01c141410700c020002d14820707108070341140c81600c1c04145585000311751100f407880c90044000ea41602209082480e8001c4002503080c9944c452801416030305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 344509460 1250 344508210 344508277
    0x160c0f12050c101811181005030127021207030b01030303020c0c0109060f030b060417010b13050c03041112010c052a06010e0414010c080601140901090b 67
    0xc162512521031000c200500e00e46400706510ba4402c5007001041c2c140c0181e11605102070980000014001d0f011030000700394604025960742d040ca1542408100321128105100e405031780e803c500034005c3d1f0707592042101100d15210038450380703a075040780900014079109a45080b404618029140107035036940740d2408400003680141c020a800181201404005000a4607050000d080c03040d1884d0038175400802045400c1805014543e4443c0d01220704e0b555602610010000c0d052120b550142c00240c0c0350103001d0114905000700600142520b00b01481e0180c0791048090391250350070342d81e55031030f20014a1000260650094411142090580801e00482c0d04600c0c00c1e845081c0c0d10003030303502d2080030b00720340c648860201c00d90002c440070301810200d161411a0401240c44c003550f00da505200102c0141c0c040d140c0f09079031030140d15410003500419070510403a07007601c0e10140b0140303144e01b503002403090308007a50005040c0b50044c00310b01801d80150a0450a041051030084403024048502d1403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 344510710 1250 344509460 344509493
    0xb0903030601030609150b0a020717030a020d080c0f0a0306080303040f20010203030a0e0f0a0c03060b310f14160203070302060109020f2503080c03160c0f 68
    0x10400001c101e03281d6014001c40d801013103808000c010080c030307400104403081803e0140b882407020004401264501c00c0008c0c2002c0d010f0406424442003041120590300d41c058160170004d4011142020340c19801010294441c2d000c2c04007851405400e150511121303482001003606159841c4408a0b50303201c05c202031485644540103d05220398a814180006a28140200644120300c81d0032070459a021007582d4002e0042c1c00007180402c890b0107228200036580045089a215503c514030620000f4001002186e0042d5403c011018101c02401000404400c1c41075460700d2101140707046801a081c000c802100700320000440b07070981d170501d0b0196842100c800c810004c3ca04140002003401007020200c9800c18001145004201c0e50040d49510301403248032031480e07003c00e4a803d01c1181d0811100c100c0c690f0420001c08036561300041600d01c0c841c80041d40007034031020000e00c80083ca001100d000d4000b80030b1036103100005042c115801000410304640003030f1202c0f030910000f4008410882d00b107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 344511960 1250 344510710 344510713
    0x9060608130c030807140105090304081e010912020d09050d170a0c02060f040609050d03270902120f09120904090303150305010902120105060108270706030f0f02040f050904050a0b09 80
    0x3007402118070700303488c03021303144495980003003000300300c0101d000850910f442005984040405900c0140500403c42928040c1440710291440d40783c0030360128240340b07080340e1038550030a12a196001d100303003d0840c1030024000c0c1e1684100703065146c4800080c1086a1403403800c0d8105401d158003051094100300c040310300608011030280700107504a038803c0c000c0c1106035080c1311f440406480c010441d00c4d00303508203400b450311f0440b0500603c0c955080c8801a000b09041955a10400d42d12130340003090444900720010000c4000c0741080d40041016494101502c2c0c400381400c410500b048020724510004038245039503020405040c07403c2c114a40003c6005000005004481c2d0050001002000c800c182c05a40b400d010440181e070440900c9400600d101030b4034211150341440206801510010400c2c1440f0f42c060009003640e06400c80c1c0c054020304042440311402209100050703002d18054400085401c04060201c0c0c103010042c41d41c464000d2040740c500c0000d40d2140b0540749c80030788003000706 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 344513210 1250 344511960 344511983
    0x31306090810050f04140307171206030a0312020a0c02180603010c09030b0c070f0218090727050703020f0304060c1e0f0e04060503120c0709060608130c030807 70
    0x101c00c2c070802a149100d00800d000138500440043d4030740c200104018a00c9000355841062000100196540c0d2a480350701402d503048030320305685044e0401445c40b0210300780c0c1c000050283c10085a070350041949900d40c076043c0d4000400000194000407824000c01260404e840d0240c0e0710050003a00708000f0580c440114109442070600b981c805503d00002d0100b038010030000144000c000035440400c3c0780c500c0f0345510755846d00081190f0b56003006584402403020344207860101c02c6600b8082c00c007110880b406250b660401c0b40ca40c511420901c0224168548601c2c000c5240ba00f01c258001d0051400510340161203004000b9074200303032030944810303580c0da25017400d154000612185503a1022080c440800080328001d00703c0c1e81c010600420865840c07151070341902c45030071039000342078000d00365810340c4100d60316005150040502a0400e105a1000003504c000700d10030300040d1852a0741e0307009903548003141d14480f80c6050000301c1d0040c9102100002149002001e4104540325583e203016 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 344514460 1250 344513210 344513219
    0x903060601110c1c0506090607090e040503120a15060809030a0c020a0510021c05090603042a181d06040b0711100c0e0a1412010f020c011506170a020c03130609 70
    0x190034002400340c40f03154231a5007030144450b00030300300c07404a4480c00750140842c4e850f494403034118010300c000840c44040e541c0034404203030419002103280241c52a05000c0903640d540d000c03101d5550954002030140c0040204521051050340805000350010f00303d006010380c1c450200d14940c807200309100040c0c204024080c103100088003021038160b03040c64294140040070000907014440980010f06914940076020001e201d018403a205107010700485100503903a075410314040c06c0c101b402d46c0123582d10b4503600904032080749840740407018181d4001c002c4c540d11903640003100c11000d0800030502c0500499005590740400040c004e040c5442070204d100c040b00000a040550005990ba2060850400602212a50814111845004484811000d444220001e00401a004045400500008034140441d005421540340030100102080302595584001c85078142240048030400001c04d02291407140c1a402516480b29110300396450a4004120390060101c036070302405c040750040e01c0410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 344515710 1250 344514460 344514463
    0x3020c0a060c0203060106030c121d011503052e02041d01090525030b15130b0307020303161205070f09080c011e03090803040605010302090c0903060601110c1c05 71
    0x240204054248010761400303c2d800a43c484105008080400d56280400000036100309800781006030a85d4040080c0c45101c1117144003d107a60780c0c1040950b0a110040304880d869035281000c40ea000005420381400c02031942c40e21040c54180141d80e8568030400e844c0c00c05040c070040005041800b1200b1440071510601c20030444140e0203112a9032509040100c0c82040c1e01203101208808440c0048405048100360300400c851001c058100e0410340002c00d00d0700f00701c002000032070071488110f1300c0559034400c0c074445440115100070050f0414004100407074047e0007440f10008460400c02d000c030758024080d0f4210341c8120707100000240900080103003640c0105180028021740005030852055100000e44001900244004804401416521907034401d84c080e814041d4020107aaa60781010b0070400e018140a0100742e00c961200d6002ca500d008510040325603001000c0d01510455440030015103e155003040c410059004d008401d0080340d0345d2030610280e80010758081c9500307828070704045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 344516960 1250 344515710 344515729
    0xd02030405070e04023a03170a0204050109060c020f04090b0411060415080c1225020715030902030106051002030a08060d0218090115150e09010501090b0a020304050d03020c 76
    0x181d200510f440920003d41c0b2064814000115041c0081945007000300200300944103c07105001d80c1224058108101684503203c14062440194071414980358000d102d0b089100318030800c0d0210311004030410845008141c81c0a03c10b0000341050065540c06010900365201c007103044031040650390410007040402d0242d240fa80900351010382c01c040c24002da030091001040c03003110030300107041d00042c1c0402c0740c5022120040f0b0150041102800d02414503807110b9076419002c1503100c8010302c4080068070015800c42210f041500420301c0518001c0e040c1c0c02090300f480c00381e030035540320580480d198588072104000704455500641d504d5600340c0c0001d000940180540d0701c81e09400400901680d0743c3c0d1550302c0707034880e00c0c50003042c6c1c7e8a40402507801421102c1103000080100440051409040120074815a42a40303134545204449000c00c01c29407000d004260115030482006d105406582c8c0151100102a00460385402d480d070780041d60190081c0401c40042e8060040b0185904103501e60 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 344518210 1250 344516960 344516969
    0x1618050619030e3910031802040c03090c09090b16020a06050705040914010e0f0709031e061103060d0312110d050402040606021b06180904030807020f030708160201020c060d0203040507 81
    0x560400c0f081000103d1521032000c2070001c01da2100c500c4c0c98040781f03401c4c07415030440d8018030801042465100140250404010907940c070300b40900002001d01ca035004190181f603001244e40825518140d50302c982a0040d8843c10461040c000c24400080c1548503c4e4080c0d09591141d5480358a04441c00342681e0303001e08820940500c180c0101701a111081c01c99800052410b01b04e800c80e541d104044489070102d40c80504803140607000c0038421050301d2010711145003e48001d00c61140c500203211041c0c071060f1003550300100302c10900c0c40032921804d005071404501801c0405e52443c00c0b080403025800c001c0c96600d03136a644030305120461509100d400010b051900242c032030070741446d07036103a00001e114448600031070380041d02d120390141d441c0216520300002000b1903040e05040c18001d00c2500c04440e040050310a1000c408008035000051b9001264804070b483c2c0b4060844032942210100c01d03c04031b056129800203000c0e0360313a5000c007900f10302c0802040141c6a16107400c141b8589002d9070711 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 344519460 1250 344518210 344518303
    0x9050306090a08030a0504210903060f050f060f150a0521060a0308030a090f030e090f0603101d190507050402040605030a05040510051618050619030e 66
    0x10428000f40f0003d007620703808980c01700d0020725135889050801002a11656a039006011400c0003034100d5040f480c080c06803801210100252110300c40c3d1501200d40c140d07280a441e40c0a10005409803500780506101008050246400201e6200c3c0d00b02581d0446515240480c10114404008040500c0900114240b50940010600f80b03180483c0381c000c040c1c003002c0d00e070907800000950590302c0784e04a00259907100003012416209402c3c0101741c071000c1c0e00c000c1e03c6181f1900c007261451030001a0b131401414020044d20101c00d032580690020030516045a103050342c5401c000c00c0410003031002d00801e101082914040c03c4240c5801c07420075001e508802c0c4502d00c140401c0c00300603800b2007529440901c10a0004981e00d49041c40c91412104030403601c42c02c0d0502c0c007004505001e524440ba140307212501c07602c01c5080c1c441040c0720100c0c03460040d47d4200c0c40601044045502483c45040000301c40e040028045064a50050402c1410750301181040055440a1903183e080c0100d8101100c4806 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 344520710 1250 344519460 344519473
    0x1819051e0a0504030509090c13030f1e0c050609030c04111b0118020d020433050d050c0603070c1a0403113906040311030d02030a08060103051003120905030609 70
    0xa44c040c1141c010181914000e12014000800440b0303800212241d10709444000411070303a032840d100500070202941150501078460b00c92034401c040035803040f100c40c1e203d1001025682004107000c440d270000c201c1c0d05d91522403070f6001801e64885204200c0b4100340d400340555542e0b140200f082d01500031000c40390031703030303142a00c21800d101c4003080809000707604031107441c01035a150000a01904080d80b0000c1c940c100f100c020240307190710031038135804101d21125800310031b40e841c0708000c040601e03544054029081080d40ea4100d00e00f40c0010b40e80310907141005403c000b011b460710402811002d6522400c080e10100340014160004a0008005072000041c003c0100a001202203803941c543c4100d83c06009080300387c01000380607806580d42c1c03000380403d911242d4074108040102a000081c500030b005241c4810105440803084507c821a02e440c4c611700d5455a10044000300b200078201000320b1841c1001100149030010200340302c001c0d82e075540341500d052404050074a00013500c0790905a00c10f8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 344521960 1250 344520710 344520713
    0x8060c0408150402010311030f010f0b131806030c1205010b0d1203110d0c050d0f060302210c150c0c09090a17070f03020a0510020304021819051e0a0504 67
    0x40c0207065a0710741d04100702d9a01c4038401030300500602580d006a0f900c0210070080406140040541241d080380c100b4285c46680755440783d0184900300642e403442c41026000d01038620b0728612001140c1803042c0c00140940d42c0c5e1107280c110b8080360880702100c03042aa151040c00000d00510001110803140f800c1d403608143c1d01c525440e074012040b141416140d807100c1e12551002001c0d070b8500c140e4181c080c0820789045500070310316171128042c07a0b1702c10302c0e02c2c07801c04284000d0b101d5201038039805411310021468100608000800d03071a03060046108040304030b900c035210880101c00c0c031254480060703200c4000222041c1000d110341c41301400381d074018040004e07400c1c1c00502003c035184c100c100c880d007101c030b000801368640c8a800ca001e001d403d0300504000801d82d00041a17100c4a0040c01076845940c00d0131401003e84c4025100a5404856410b501401102d10201c9503000001030780c450840707a404003952019202c007100c0c1280c6842d5454660580380416211240e40501202e00400003458607 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 344523210 1250 344521960 344521963
    0x6040b03040201031d16030317100308070c090204030c05041d030913060e09151005360103050d1b0f0b040c0b0c010c2601180b1908060c0408 62
    0x40010f4101615030302c8409600c0c40c40800d284d0805d0518058907454020580ca54682041511003100001d040e00f04410102c00751004c214010410310f02c2e4001624a107840760380c003541003540140e031181115800001c81c1c0342d007840104001c51203420201146490301c01004215510900c81c5130701d11405000c2c0308201d0602008581c005241250b002d0544140900100001c02b20340d0044288410841c2c207000135a800010030f01c015610403000c00a00f0740e0b98050390520104a403244a8120202c42c0b1000c1c00c5008a80780e0f410030081c800451070000580908145802c1d0080c0e100341c0320b0b50000400d1140701540098201881c0e100000c542110402e6507036091a42a08030002411907451140440d08000b0308441500091503440301a54884510700c03545c074001c02425016501282e480482d001f0010140710100c0c103410a0b030400301d0b480b40e10304484c480c6d1404848207400391590f6914001c1e6070329a1034a0a159240022003005406141840040351808401034655543c1890500c02004241030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 344524460 1250 344523210 344523217
    0x311010504081006240e190302030a06050a2004030201050a031e06140a06081801110f0405040b1503180c0d05010b13200a050909070e01140c070b07020a09060b120606040b 75
    0x181950f0b50304407c0c4400940c10714019154000a6060040d202e60750140f092503013016026060b10300b0b00f0009420320140d603200c190041c1c40c0505030201d0034001000990301500142441d034500341030115400044819003100c2100e00d90300d8442c1d160b030380d210a1121220501e10180210416104010782604002000c0d000807002404000000015801440c0c00c01080d00b00550030018003800980f500107500c04058503420500502c0d001c0c0d03117000d00d81d504902d00036107110350111980541038070f5603c032184030f00e044803516080320300148941e001d603003c40d44034500440101070080000040d282d9010f000c0085102005510b490590b0420725507070030f4108010a4407803000ca508812650741d5100704001c4c0c41602611011540c0f01079440b08110341e4640040301c616014509070790b40c101152040e00d040046008207845030b00b55070b02200b001c0c00300149010040020b42e0000304429a455907440c3c041060383d5854000c80030300600400e200c035100d610180c010381c1003c000c0302c4490410f81041c281000070301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 344525710 1250 344524460 344524487
    0x7110309130207060b0901170d090b120403091a0d1505210a0b0c07060506011409103509010e03070b071106013c031101050408100624 59
    0xd0340081c01d0b00420102d0303440751742e42c204003a126124560b510b036001d071080004440090b00d075005501181040341c2c4540052000d68000307090550078001c055650400155008000324240011024041881c02c0b403d0032a0203090035508195a60380c916100f100700b51584441c504040a89102d000e1150b543c40042000303908005085415642507041801483c043d448203014005600010500021640307002c020102c150107407400344000d80300e02c1c004484e0060310600c00146800c041c0034800350340c50405045680c0200303918006490143c1480b151061004102500307040c000c243c002004407813201030800354028541c07002000241b101e2982c00d62244a00d010042004e500d110000340b0f41c900910061b5104500041118029030310b030985000803804903000c988880e04080303005104050b8500d01c1010304c00081c8002c160a03859540c5441b2452546030b07146d418030030103100100d4000b0f810061250b4107801d1800c0070904c1c0c0d18002f001c151554500010031035550743c681c8580c4403150040c510400c40d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 344526960 1250 344525710 344525749
    0xc030a0213050c13030302030d0e03120f07050c0102030916050a030c0e07051c0b0306010b04031a06010e030a03020607140406020c121608011a0f130902040b090106050307110309 78
    0x2991030800e50f01941c0700b40c4600f4403442e9440400030007459800800b4224028000004011040c11101015500d01480d1001005243c0c8480003807510140c10310010303041b50440c2005810040c4440b011400d9801c100c41c1c00d015940a090460000031440c070907180200300558503840f0890654955008060b0540108820201c071040441c1f2084c1c800c030212400004102c3c18003222840c9500131070060604074800d83c0c03003407103410f0000c5840f82d8041c1c102e030304a0f54401030303643c9010b14007940b442c80110300428403810b00a0361103181d13500e614184504040613200ba800340989241c120380c09441d15207507030f00c4042180d50512062042540004002c02041001c07590701c03030120006000a45000060504281a41d03030403040000c2100e07054000e944c25080d07421140002001c1c0c102800ba07060400760a0952000030b660761205011100c0d404010011300182010510b926803101107000c28a0030323404000000e000004100c822948000160700d04254a0043c1d46092011400510741124245a00242 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 344528210 1250 344526960 344526971
    0x110406240c1a040b0f0f24030a0b010e0103050f122a0318010201050627070e03010204060801030302150403081f1706011701050702100e030d06170c030a0213 69
    0x2440481005200ca481d001110b0901da07241c1031400550411094030341602e69160071000c28803040300c90407014481c00142450003e0b41100480c0c1c0c240c20b80c000d1144039010b01409103508045034080090902a0002542c0e00405500d1803500910300f50b070302d0b40c401500da04148420850003890008032550710f62209948500d0071114201c01a4403510001000c42d05d2000281301542075040e401030081c0604241c008010341e40c4c4d44018410402c000030a003580c600c0d80003110440c0001e1036080c00e50400041d06c1c1c00c1c078040814501103400c9901c150050f502148250b0010810142d04012032a450068401014241d080030383d4040c1840b40c000c3c0011a021420030134500140c114a02104000c049990200c0c4401c40e9800300540c40b02405c0c06400810403254001d07001000c0140500d5004602d29801450400041004c3e1001040034086014030381c0420005c02d480305401d405804003400e14880d01c1c010604a041e2007518000c0d150300319600075001118420090b0761600450201c403000c108c00440c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 344529460 1250 344528210 344528213
    0x60103020c10050a060e0108031e0403080a050304020901060c0b0c250b010f0501080c0d11040b0c07060305090a0c0306050604060806090a060c1409012703110406240c 73
    0x107405000c0c180641031040d07196001425901d07401550140004444c1000926110030300024280f0090040c0d81080d0300401c00314072103010040b0500030441e4460111400c0079201d65401010740e1018003860006880401170105500d805807030113005014604248410100c0b03990b80c180d070790300000d00c0d045c50b005002c2112100441d83c800c445110f11800164a2140682171070300101c2c040080c024561040c002c0b038008181c55021700106030040c5c442842460603c03902c030b00948080c0190319910310a10301c05000010341c0485010103410031050a801504a05081090040c00c46900800600c010b40c0080f4038000440c1c2c03034000f0007040da50410404501560b442000c0303400f270560f980c064a0b05119020401150004c046440b6216921400003889034003840b80040f54881d1114548841201080041c11030542c01110f144c40030400e4541001c2850781100102541d0300702c0d40d801075035403e00381d44c607454061416101e04800340201090054207040d07415040d00f01230030501007001c144203142e4020700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 344530710 1250 344529460 344529467
    0x70315080d0c11150d0f020c03030a090503090d0501200a090e1b070309030308090105011a07020a0b0a020c0a09020301080307030804050a02030a080909070804080327030c0c280b030601 81
    0x160110f82c090103c40c03841a002150711060b41c401e60360340510502d0040c51307895411480c022110f811403104c00560a40c1c03104103d120007410a24021560b43c07000f0070540310b158448055000b05c2034000c0000050f260b8924404880805e071880c900103100360104140794070140c00c841c040f421b50f810300304480c0d61075a0301c0812080204002400f07410444011a0340810594820300440949110703030354000c6283c640072183c0d801e9503001c0c00b43c0c44a02500c03403c1404180c003039401400ea071a0005054240203070391aa010384540e8800c8402c1c0300147c0082800110070b0030808028001480e40d0b44c0b00f146198075028610307840c0d004014006003008130540101d002e0040401c1040070300381c1c00074103681c03a200301e03881e0060740c96008040c4c40d030050b00c4600000d1031041c0140c110610807504402161f1665640f0344c09101420f030b000301e00262602684003034104418080015100011201c0020090000d06004010352011920440c0011184841d2052580a050314043e401c0710128a1640d0b01c94a603840141c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 344531960 1250 344530710 344530733
    0x30b07050a030f060b0918010503070902070303150e090f0f120a020307050d030f050105030f1c050d15030204050121060f021210050901050402090f10110d0305070315080d0c 76
    0xf104007410014007003807003141c000003081030510880d5991480301c440b4000300c400403024130510354107811407401040261500c0c1c009008291091500284002003c10303503138210111508504075100c19401003190320101000301810412000d0020078581240b10a081c0e036030348102c0d900006940f000305d41050700b03a0080098640840e4040c080e5000c50019080080080c40d0305000c0ea141281000c00000322420b020a18440340c040381d0300a0100c0008901020700c20891070244035042080401c5048480780980c031503281c000d2602102480b1151440c0104420740c0c82c180c0140c0f09038125075100440452242d5002d4000590180e404241e684034540e01c50028041d0b29112080308094034200301032080114803c0058940464140c403141c0d803510184812400742c584450f0700301801c03071009201c5182c07070b06c1ca5510960766840c0248c125824480c000e81000c04150203040800e0700c840c14844441c0d0540142400d4120903e06942c00f549004105903075866032403001824400006800e10502c094a00716 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 344533210 1250 344531960 344531981
    0x2a0809010b033301062111070215090301060f180e15092d0d020705010e0f03100615030c0c030f030914010c020d02070911040513060305011b0810030b07050a03 70
    0x4003096a45032000703848140c0c0c401d0070034401244440303038414124987c41881050801d107040039081a1242d0300340200b031100d04140600002080c402c8030079996007401040301520b421300d81c0c600c1e400e14200381d08030300c0140c02c4104466182049008440350034002802149030400313a440104c0ba4892030f080d50304080110312903411440720182041c02c81440c03040111488034410084500700380b10745001300e0302d41e000c6d03010f11400202d403541c220302c0e41d01e41038055041001c0002c0503110040c2d4420220412905642e001e4002119030000c501583d039014400c2a80709041400c0c001d0803041280e0b4014034014212a01109140d51035007414103002000c03031000b6048034028020030410540760b0010b940c0f070200c00b424000601c00e101c4082a442d03c94011400000b0b0341c151802d040c10b00381020042718001840d03444113265070703e0170000007042d000d004419070500054408800302c480e444000703014840052440e49510400f10b000c1000441c8030064030780c0701c040c519245d5240e2480c400c088000d00b107600003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 344534460 1250 344533210 344533303
    0x160302071a04020f090c0a051c0501080a1b030305030c0d021b0c0307171c020a05030a080f010806060d02010f0c050a0b100e1302010309062a0809010b03 67
    0x2981c510000700290030034012802103446400d07110b030071410810405001c030303640304001c0c006204c6a00b070705001e40c0140624030f080d080d001d5043c0005540210403240246d02c103854a52280306182d040c400c00e0301345407800c88501042048051700b1030b01c0c00f41032840003130110388031750500060f032142c1444e00350b040e1000681042c074280c900d0510310025a43e9000701c040703035270712030b00458200155009074042503444484090b006040d041114000402150540c14104803d50007100005000990248000c01c500802c544586405d410411040f0f020810140c00c055415400402400741941c0c1ea0745042d40200d40c2441c040c8040300c5884412110701c1342e042c0b001002885043d548408008120000c60320034030391182501441551401d1400401d1070603a083c5d0340046200b6072100141d4440e802c07210a00b809040c7c04103003462690a4043c0d0102ca001040248020260a0300016540030004507040890f41e0024011004187d0010303842c0c2d801da8101081c02c0307000303850421000c5904842030300e00e80344001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 344535710 1250 344534460 344534483
    0x292505030a02010b010305060604051e0109031e0507050901230a1206091e0209011a130605070309050108100905061f0c060e0a0c0e06010309061a03210316030207 71
    0x1e5019020740400400b031030109050000280c5141428402c1d0780480321300030403105c250f0b181c140849561070f24101d2001d040041071600403000c220131481d07905a40760126100e013100c05090800505201443c1c000c14841c00b000d80040283d01e01c9002008040304080295003a03076550303540010440f10aa60240c0c802a0401c0001d03010b1041952254420f140a0000321805c200310340c0744608144040c074402503011042d0703030040c03000040002250780c0b0031507250249850645003205e41596030086602580000740c00146d803c04166000c1d40d000000e10003800c01d0710341810008000c500b5007040f070048003071381a030b00c0000405565a09a0707054804d55440900407a50b11405002010034081c0d10040d2005030070b207440417a00b4100000d41e20100d45d0400211060740341010f61705040710f88082d000c1c504040c0c8840711030000c00c00911428401c6001c0302011038110307a440703080c141001208554800e1040394806024000b52586c01181c0d882014009010b000307034030b4000150001c2c0111540940802e140d030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 344536960 1250 344535710 344535727
    0x30308060108130204150e150d0b1302040504150e01060501080c090a150302041d0405030f0a180e0907050a14010516060e0318040203060d0210050c06090729250503 72
    0x580c00803007903400c4036203400744923036a40201e03140822030044d8040c0c01c03149070011800403c1c0302441d0590031214140200b62040c02c0d680000d0309035103003984c0130f40761125001d100d07010107402403184400004002000340b011618000010301017900040c81032860003c00500c074201e0ba03940b141340c80044c00c20080c811074244000074006009412500412102ea52420340600e0202c0294022912455021004501e01041c540800c01e503500944074900c00e01015240d4003250040581c80c2d40041d00d0000c130509101e00e0300e042051b2803e07200b54400c030b000343c0f04003a040c02090001c1103480f407004400c0c2080d590b87c04ca2140c800700e15080e000800b0f0050707450b14110a0b15400040010620300440da50031030b68440d09c4038100802c0b44001c1c0d440e16400010403291800504220030303503400086160500794107104034501b0042c02d018086400c0b01d2590880e0b0030521070100403013550803000c030569004210140022621070305510840c02e084a401c45014540d039259810000c00f032440701da1000030b4075182d0150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 344538210 1250 344536960 344536991
    0x30e09060f18070201090c080321100504020d0f0207060e010b10020a0f11100203070b0604020a050706050c19030906050106050702060a08250f020c0405090c010806130c020f070609030308060108130204 88
    0x9400411400315546042404d464101128ac1d80223004070062800140d00d031404120083d44041405140b55840703155482182d9070300c0c40a0446a406048082034a9500e420f0b02e0b42100c444090aa102d4078614074400303904c580c00210107401c50792110b0b0039540c2114a041003054003c5002c5a698403d0901941d2218185e010014203205441005240c0f400c2c2c550004000690140c12440c0000801c28001c0001040c6290011a00843d1482e10149409102c003200a0102503281c094000706e42c452400104200b864401c041c01000039280450808100e54000b840a102d001610800c022148000c244001b200c011194501584245400040307000204041e040424214407640076002e404035210031402c03d80200d5208a032184041e0115001c0c034030042d2a4040050a040e8000c0d05100110001209a116480220080c1e4006100d00b65450011b103282c074030550098010050500340400010341c200921540180007400c0820b40c90b0b54152090300e080103402400f0f0350081c03c115a0a4804070f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 344539460 1250 344538210 344538217
    0x1202032205010f1d010c0305160e0a05060d0b0906030105091c020705061b0c0103110d09030905090f1b070201080f070c0507090501060207091b051b0703030e09060f18070201090c0803 80
    0x144d600034004144184c10690445d0002c4406402c400d0450080e109814404e0000050842c0010306c00308046460f0000320f0108e40040000348501c0b9030703a001c46010f51400120640d40580c0450007805285043c2d6601ca0b107074203004042010a22020a00c2d00e0003500903c00f00000d4900546015241d80c1c26401051048001c1c00c40601d0368050006071503c0e551103030250980c20038800010500c0c03c101c400c2c1c64802005c515106404000714404040345644ea1507034400d000d08401150352046040c551204580844005415070b000c400800400c80140d07000403280e13501030018a080296030740e43d0101030350a64a00280240355002e8014085140e9505510050590b0850b81c01c0340c2040740c455a02008a4000c1d0207100c40d04050105203801d50b40c8241d00070b002c6822000f03071030801403481c1701c1005d280541035041100401e40103903400206081c080c40540d800a01101c280a40c07000c050302203041c48a6803d4024411010320300002d903914001d400251341594414405000c00c1d65800d5450f480c1d42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 344540710 1250 344539460 344539511
    0xe0f01140a0b0103090209061504050a030503041508071b0c2706140315070903050f0f011a091305011b020a050c03030705100b03070504060e06011202032205010f 71
    0x70314180c0c015071254130070304c900e01c010390340640386a1007034a41c001000006041c00c032542d41c148404000c082201d0b1500070084d030041d4401d000a41e116414010740c0030300c1c2e4901c0305001c400c10002904000085c0e500800d002180e00c0341403100e5011050070700703001c25041d40703903000f680480b9001c8000030b04d8007011030b40d000d805c50782841c000c21555440300d43c0c2c11900414400030a1f815440322102002c40010100c070160482d04901742420915030700e5a401d4200814901042d00d150070070000da0790070b03200a009031010551918400e00080040100080522002400e0014140c0d00043c610040090941c0076114486124501c00c8051000301002940c86000d200c1c12500d0380904000300441341000000c0d1260181e1250150040c400c02d0000d01005000c40c0075042d030315110300705001030143c64a11a22010300562460600d940c0360440c005000b00180b500c1088025204004200020200e041140704a40320101d15450711071590038510701421a010103800d9503842d00e0050411f854a5041042000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 344541960 1250 344540710 344540731
    0xc1a1314030d020403230309010c0209090a020d03050d060b2b0b060409020403020a050904050c0909032a010506031b04022d040303180f060e0301020d0c031e1e0e0f0114 74
    0x90b001d0781b1209840740150840c00c0d022500c8005d0000045c074015840b560b028080380c044030b0b58500303150000b030326103040180c094010680000740403003081c0145c000c280c05024240c000916000c400c40c1884038071440e5503407040e041c0a003003102d00030b0502039400500b90290001d1850fa22541c6800c5100c0095001d444203d2045014581c00152414410319440c0f140380c105020305000e41086080c040682c40c02440804180810450a04400000c0e070f0b03003031500c601c2040251b22000b00344038a282101c40281806200c0e0740003006460340411103100c03402d01882c0c262005038580d006c0d00e030000c04407107102e201c3c5090243c001b1203101000c0307084c00c0a401100e000b0b6032030400904ad00200070f0b4452105004041e8401c0b000a4140080380c044c0035203010110029000500c0d2150122900040b207101007005000a0b80300d042054172060101018415050384002c00c0040416510381d6031240741e03a01001c0c5100780e49a60000d100e038501481118841c1410100a00c07800f07005400341c0c04049012242d26416 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 344543210 1250 344541960 344542013
    0x4090c05120a0c030f170a0906090b070506150f04020f121b0304021011010203090f0d051c090318030609021c08030708250c1a1314030d020403 63
    0x101c003000960303200c00743e412004001455095483c3c2e918028210141079480c80d9a1651000766811144020041e290840e030b501203000741440320052406141d54807203040c8441c280405400320700c0114000f03810469500400000898071008104600a441c031507a900610111b2103400c942440e038000d200c155000340010a140c0d07150000b80c0190700840c0320f10050f010b0248005001400c20a4004244000070300f044850068100307420390a83c0e004441031442c68220b40890010240c08000d4008002c2041c10102c3c10301e1858150b81d02c00007402503415021940718084030f0180750050025210200040c01c0c0d100d09107407281441c07000340203c15402c902a03407006078942d0000d00c82c0c1000074100b6a0184281e80f41d916444012100e45001400b43c0176850500103c112a25800030700da0041060b4079115007071200c017207040c045d0b1104501400c0721035908100d003c2003000944200b0800025a01078448400d01c00c0745003129186018014107c00c00c5403002034040b040c03003442c1000242e07040b10401c074600c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 344544460 1250 344543210 344543239
    0x280204151101150603090c17120702010507061a18072c06070b101a030105061b2a030f070302060703050d1401230907030e120301030809180105011205070e04090c05 72
    0x8154240104500b450b00701022500c27112101200908200e80145022030400100d40c581d403007198101c03001c08030500c0c11103500c2106410302550f0400501402c0702d004540346030000c009050321074100003080304031484050159001c40d20810590842c0701c00303014240c1310a81d80c50442c03184141501d0301207001e1940f49000070b0302c810107011400700c200400361441c11a46007406221882e082800c598070705038a25480030055100812a603804c0d624942c10710751451410301040d08841d507003c040740740a508129080b2842500015460049a50540c3d0040d5502d81500701210309004200441c20320f04e050250800707003170403c5c2400b94142c8007400d600b40354000b00210980000300324544140d410501c500c0004803d50300035408100d90714000b0f400d40d1202107400402c0343c01e65009800468920700d000ca10012107051040e10346058034840c00f80000b2a504040029007138501621503541080e071210001240c5502c01e00741411140c0c4050f00500240040341f40043d56640359009860050300c030f880701c900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 344545710 1250 344544460 344544479
    0x20a1509020123032502070603020a110d0201150f0305121e04080105040c090516030203060d0c15031d0303130201090503010504030e090c0a050906090406030b280204151101150603090c 81
    0x8812081342c6c004160407450040c0c16030194110100250501802d2014045001414031105d4034026041e0f00000b515654008042d1280d82646c122071014074600d44107100145000580c1076442140744502511401c40c0c180303420101801080c11050f0386c80103d00083d12100c1500710601541c482c5100403003847d00c1c0da120381c0032070b01c0c111415400106040c0714445c10030f010740e00460b00f2010141c5000b0741036000c1e440d003018640301d03640160941c0d4608007694174640d90500c07410b5440070031810444032180e4030050740c80c0e6900010f45102c41c0310320313800032103811a0700904a110080c01e02900030b101e01d14150a010303084400400c0c085000d42d81d4540014072020009007160000c12080e142c850400e180c0e9420301c14650488c03120305800c40c0d0350b15000f2000c940b1513400075110340f10071841c1032030340641d9003100703001c1c120015031001d500350061005011180c24480081c060480701c0c64120026640c1c454101c1c050f11000c01d19202c0c440c8a5a0049a056410b800520b10903020320f004241c0c640e0f9806849 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 344546960 1250 344545710 344545771
    0x403050d0302090310150515120108010b01050a1817010912020106061710030519030e010206010b03010603091b06170618270714030d020a150902012303 67
    0xd6040c1c10811455030242e45c2940000001c824200c150080581c58602151001034002031000b09524081040020403248141c03145c09081c20304000d00c075000c22003001030214021b6801100612050404090303004e05240c106500401d221a54101c070385101064084c0200700d505400e03213a025400388a0744415005002d010210b565550740e1004072142c04410346800c0300c0182a24038000604540040403071010003401030f0b240900d00c00400a1020752801510070302170251194159082040101301180310803040e42d0444509040202d941e45031132803c501d060300c04a420300c2a4601110001c200e4550001c444642131018914844468070303550208010302c03801c00031000c42c0d17078ec0c030200003006003d4948500004001c007480303000500303c103040201c4c1404000d42024240000c2549020a1840d04101080121010740060310700402140c907001400381e00c1d2103107010015140c1c0044001c5910036070002e81c0482851304d0001e50380c650085d0705202a403081e12071005445000700220030071568107101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 344548210 1250 344546960 344546977
    0x2040617011d1e1c1e0807080606070501020705010509060a060506120402041104030f08090a090c1e11010501030807020f01050a020a0f1e050601031b08030d0e0102130b0403050d0302 80
    0x2481c802c00c410841c2c0c80781c581400c2004106000d04804d190310450510003405000105131030b14003410200140c0151040080e200c203500f000a0f01050000c03054202400540040003641c040d55268001c2c204180644104c02c2c00801540c03910042040b04980814031340d000710651201400754607030f22000c010050107007512400041003210f000c0340c0180f40c00d60081c40032110b502c10b064201550398458600380140040d00750703a850b00000700c101141c07410340301010180c82141c20810180d646c4a00c0103185805102c1000c20740c1e040d40d0100754802d4011001140c40300404002840590307101d1500301c080760000c620480c014442d50720201c030a580540141c5d0030748034040d0b000b0000d000321a20749018541c0503210595600811141e008152810401803401d014002d00080109515501e03200c124400240780a9002c06240001401015008405c8a420f2024504041205080000d15900a100b8800c41c039a075004156000581040c44801800031a4000c00c26254040c442d41400e50681c81001507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 344549460 1250 344548210 344548213
    0x5090901090213020702010c020a0608040203061303020a0f03030623120604050a0f06020f0307020c0f0312040b132402010f02040b041211040e01060918020105040b0c0a02040617011d 80
    0x403510f500700554080c12056005141c100310709100d42c0c0104200f00401e80088000945000403c030641c2000c1080f02d4111550040d698041c42c500c1d18000d4a85911030740007060f4195052881040c0f522a42045000d0b01500030f41320f01a420140e010801d00261450359402800b0030703c0c40c8485094041101442540c200001c1d182040300e0340da41d02e11001c564030040711407581c00d10181000e2224034021318450f02040e0024414186050b04204a042c1c6050800d4400c1e80310711140d28051168070165401c03560010481e9071a000405040003080075941c2180c0e00048002b004045242c0e500f40c88002e607007003141c000300903401e10f41c80040c00340d110728011006040d41c10801008804a221804032402c4d0040b100c07114001030180005054425240605140340c0d110300c014003101c07201e441076500ca00010030254103080300e135a00180c0140079134868201d0103d804101440c80074070500000340595130041c03081003c5500c58820000c05803800702008815881d00720b071800c0310110106001e090303000900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 344550710 1250 344549460 344549479
    0x1050c04060804080408010204140103051b18030712230706080114010c0507171506030c040902180702030711120705130213140f030d0c0b2e050909010902 68
    0x2201950b031040e01a1044034940030402000580d000288043d1001d04000c040440070300c00540001810342d070001c1c0c44100c8082245200f60441d12218040b40d00d508400d400540c99003440d4000242800322aa000f49110207038865100200011210034600100d5100100001560501d103143d9881401d8060ba101003070b010b030010f201141c510f04840342c000d00c0c140340ca85001c1001c0d90307c0909012265000e000c804100d01000b028240b410b0003c607103c0415005c0034109882c1c494002580e0f1107244400368003030342c0d03a000d01e0019919101a2400f103400c0c05c0000c0d1a4905145100035640e50021a003555104440c40b690601c600d4505c5102c1401c107a45402010b000b400c1c50104803a22071203281418400d40c0c2008000020441100d80b00000d01200c10341144400f00707201030010543c1d091001600c00e41104521041c419003002c00442d1042d041801c0c01c41031764807480c008a40080c07991800303803c1d00da03940809042d102c1d8051144140d400c2a503400c0c09035101c1140c81c030300307850321050001d40c40302002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 344551960 1250 344550710 344550719
    0x16031106090406031b060210090305040515040b0403080a0207090501080c010807090503010c0c0203060105010c02360c0c010e0d05071407050d200607020a090b0d0b1501020f01050c04 80
    0x10380a01450304008000240959407640c0341203120344038200308801c122488200700066501070001e0b03200801c10440a010b40607040e9001003151059018640c810f184103150141c84e08040416600504140e81c1029607840e142e040c100f034540c00c03a5030490014810f50401007000440e50003954122a6000300810720760900000540315000020900350800c1554900007401d03540902421103034071215121584034501c03a00506080940c140c02441c14000074084460060b00e0311942210407410240c0b03a480c5000014044012240361982803550b43c0c0800400d000606140400410b07035808400020410b207a60f001e84103454544400e010400309a083c000640401c0c0340300d0f19082d5a000c07043c1914003698568001a80400940a00fa540d180700140b140400342151101024603800c222002800e20405070700180e0300c4d00d818051001c119842d19604421501c4039130040c94070b02d512641e601c40500c0d16100d006403000842085500500c2942c610160114040c86040e0181204000c00341ca4141007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 344553210 1250 344551960 344551969
    0x705090403030906091b082505010516050106090b12070513020a0306050a0608070f0206130f08070605040501050709050603040218040203120708030a0c0314060f1c0501050702160311 80
    0x25a010b4881c141c480c55078400040b01415000d034560346c000581e05c907090514100518108031856049500701c60b00fa00c00c10340b01d13030700d50742e2104035002440d2081da0745c81000030310369101140250007000c4c0d608000c804900743c592a00102c0c941c1c1c4050760f091a01b6101003400c07564800107440b9a07500030000c50800d0064031390382d4006114074141824041003103581c44003c03581d490196840740c0d00041030031040c001c1d5aa4800c44000202000388018074941c248a240040c98181c00b80300141640c1e0341015607403c00038083e0070384a5564004104000314940741c01c1c0140602003c8407203500159002c24086030b036103001c000b624003c43c1c020b800d210b007028582d00000c1d01140081d000380c4e031602c2005080080854440d009050b0184160078058807030406100390401d4070b40c8000d5410526082200f40380c080003030242c032554441011240444198a0400418400c0e180380c102c2c038040300306d46001001404015048107004603881e600f11a00e01030440c204143c40305850000502c014140c113040c900c180b41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 344554460 1250 344553210 344553221
    0x2130b01090519030f0506090c01090b0d090312020a0c030207120312090c030203100c0806010e010f120e0312040b0109020903060a051e040b040210051e0c010207050708150603070509040303 83
    0x6000403001d00380c4ca0ba190811540c3d5002011075182d8462030811582c003030144428010400c085c01d02043e99410308402c0c20321401a0344694003010741d10501c030014940b01d001d00803c11000f00c1000c5507500d81d0100c00601d54140507a040d8054070803e0400640314120307000082d0a2500f41d075a003075414070314142000103415600c1d400d4600c0c00110a011025a50a011607542e4489600000031030300100c1001800f290001072100c2e050040c0386600c24001d0341c02168000007201c0740e00e400c801c80c11032038424500801100c1d600351114803000c2040e41d1040d40803400076006502600701004580c0e80e82042c081a0b11030380c2100d03074141e0040c402041d4101e916402060300061070200b81c190f102c003510384c25442c0301d41c00c0768165140d91450040c80300354100b102003800803101d207103030403490300202404400e20750540304281141108001040c031548038007941503810f15a40007050300c11550781c40d48255581c01100903000c0d085405c4d84003195080c40c1c0001c3d02c501b03e80c40503103088400e43d11030700e05030300910 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 344555710 1250 344554460 344554489
    0x602030711060d11040e090a0308070e1f030c02070803041d1b1314040902010207060c02030f0a030806090c0c0c13180501061503021602060a090e1302130b010905 71
    0x982444020f034207000b140642d803e800840c12003d6241e51400399046c0680780d018081c10400c0d000070314a240480d6000e48407641c0640c00e4107261003068001c402203030030484181092807040300c4101c0c10525080e072540005c1c524184035403c4441c040c0e00d481005442c1c0c8524401d20300314507010074a031000e070907038907642c40ea21250090346603030400345a9115640c01d41c00342209000c1ca0388401d070144403010500881d004040f400741d8040194400380e9002030741c0d440650280780144803a4030351070011540c00300b0003404030320114000d440809102c0c2c50040c201e04019101741e0301c509480030004510803601000d4414000341b1f040140541c409500a00101d09942401d404480e82c40b100b0610b60f500e4010313410b05207144603100009801d031800c680c40c212228440c58502c1010300420080f2062410041d12580c80354040780d01550b0380017650800d80d507042159012002102c140004c000c1d41c0d440c010046032000e4001e0b03c190501c66004d034072203012203131050002404246021420b200504040345401102e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 344556960 1250 344555710 344555719
    0xc09010e1b0f040f050907030b01090902090a0b19110a0803070320070c0303090b0c0a02120123010501020705061c0c020c120703020f04051608040303320c03010602030711 75
    0x480b0300c84002081d5001e07400c8824001d8894008106606100540c075600580b0362a00300100703100c45000030020b05252040310300c0c840d0041420300d9030341c1c0d840707030385800800c0140c2d00d4550300d42d900803400e01000300200302240400c0407040d0241741c0300c40116644881c00c2c1c0c0842024910b585412043d4028942d4410420101d03d80ca030812500040c04401400403900503541c0413007403451490000e002402a41107010b8407001030200420821340000d140030003c1d4100c401014455034600403900500c00c9942c0e801d8041001c4206c4805c450401220030305894003a030946230b120751500280101445890107041e00781d500c0300318a42d006116a8420f18005c1010b206031403001040c0000141e5800800b03940203419001454100304501d0320300341c0d4074001e40c416101407102c0e240c21000158400301da0140c035020701072407500040c201442680f00300494907440e11a001401c60b8821000032a214580c442c01e02e009108000c030b10792b66400c07415a030480700313568000c0d45410b1719070b81c68091481e160480250071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 344558210 1250 344556960 344556967
    0x71101090b01060216060203090a1206020909010b07032601050918011e05011205030708030703060b041404151a070f060f05070f031b0c0f14010e0c09010e1b 69
    0x1400c041d00d214002d0005a00600e040c002108004901c810182c0c000c20a55104020195494803410050021101c0704000d0004500080c185040170703200d44030703d00758003032143d000114802014601a0900e1802a601c180007007006040074140d42021100c01594640401c0040100e4686448607641c8a80c0c4c020311010480004902d003800d40e4841840034560b2a90b5160030319540d02244181d500501494103e8100a8120388545c1e442e44202100980700080c0040011041d500076007002c0024900f078080c0c070b6a20741d80d83e40f2079030b0842203101c8030910650421002c03019051080704904140c900750820a07105801c40801c1c040d1651000c00121080b04550302c20790041140b91146090b03068051001149920341060000c20a489410001d802d2602c2c1454001d003408102c2591583c031134a506052905d000c1300d06062034000701e0343e00b000f803107120341030f98015440c0c0e419003020140c181c00c43c04842d000f80d01c050030006911001d000e007625403401c0310001480e50f0b07840070ac10000341c031308020090318 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 344559460 1250 344558210 344558213
    0xf150f130c0306080d020610140109080f031c051b1c050414060105121506011403090c120706140706060e092a03030306040c09150810140907110109 65
    0x540d1510070881d80402d80d07410081249a90a00509030241d41500c09404549421141d14000d401240600c0d03882404001c0001d070583d000c0d01a820142040c00c04230b8016030403101066a07240e0280e000c0780803c8603020301d10510110704c0c1c080d407409400d101600f00ca0581c40c43c4001e2034250031040c400752014042d201628000c403060712409018a000c1ea010880e40002480c03000d1501d8070680c00f00e40110100c0d501c503c500b900c042094003c100d0801d040b407800b034541c0c400403a1138000f80b415401d05003034000b092202c01240001c0c0740b80d140300180d55200700300d00b4160313085c1d40301c500c20b10506001c114510303003501c074016401c1c0003048064401d03040040d2030354560281c204500001c440d100303195445200d200481c208158480382c014042d02140d18240200080403a469000181155004644034170341451306030700400c00301d40900840c1407081000c05c00d24000030000319080d51540302c9401e43d00000310303860700140384490014001914003003031512104c0003140c3d040540700e40084c8955807a1800b40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 344560710 1250 344559460 344559499
    0x9010e0112020d020c06161107030b04020102031902011d030405060409110705060702100f05061e0a080102030c0904060b09010903020603041401020304030806040e0705010905060a1b03090e0f150f 86
    0x413118043c05c0101420316222102ca004034983c01013040900c00031000c0b102c03407104001241816294000003000584d1641e1006030318501594146201d62200b564100130a1a4154062030200042c10031340b11134504200301c4a81c4a10940c000c254002d0420401400303825401d80043d9081000070602e1454030f102c40e1541401c001040e10300c2401600943c01c0801c0c8a051070081000007410f20108000d1401e0020001c0c2009071106181101001460000c444580e11a04501e000303011103802035540b86484902c1d0f15960344408038051003203180c8400811180d4210040e290351a40c10784981a02c070b411a005c201c500e0b04000c0007294101600c0f40088031118081c0080c501980c8241c80d5501141041c900300000e2310f4550f40702c401558010001080350703030713403202010040715801d17a000c5654003205042100d0740011000da4190b000e088543c05410140c0c0002e0b04e0084940082c480302441d1107d140c241c0103910151646540c03501c040c080b50540d46003121182c4a0548001c0c540b8030109a000d8085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 344561960 1250 344560710 344560717
    0xa020c0c0a1403060a0e07060818101b090b09060f0c0a06062303211b1e0609030703030c051c2406021209031e070305100209010e0112020d02 62
    0x100403504111142a1041c1070421055403c040e840400340001e60034500d0007587e9a41512400b02002503820214030f000c28034100c0c0102d5207880c1c80903070300300a1034480000041c209140d074002401090101441300903110b4506802580d020103203991a191704a420024560000c0802d0102e5120411150507280d20030408144191700c6180049200361415101f0304c2141810b2078500005008060002410b59001c00c8205104001001040100e04100d405240c0c6000b03503d114008180015150820b0300400280240012001492132420f0b41c107288a0580301d070000c0e00e40c0050350384144085400031b130090b046014002100d01d412801e240c410b424a1400302c0d80598841080c90b43d038440c00716005030301d00e1040c5010000b540181d81030f502d8418000d554412038480045401400b04042800d99410301a00324618454100c51500d0700c242411161140300910084070a84504402c440c940f5529000b55280240705855442080020800566002c580702c18001c202c20f9080103050300048852000d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 344563210 1250 344561960 344561969
    0x2010090503090d0b0106020c041a1e040906020301030b0c2104034d0307030503131a0f1f060305180f0a031b0c1205150c12060d08030a020c0c0a 63
    0x13003640c103515110001c0c0c2040b0380c0102c454019030034070701400304101050386500200403042d100e80000c42c4408000c40d0501e10a11000f030344c82800c02c00690148801900034605a9010301800d41e141d4a6021145903107108100015074050b02c0d000002c401d21200d40302c4503a0050090900c02c5a0074a10460b44449140c244011041d21135816078450740c0414280301700007007490b054612035911490040c002d03600d014287c4010308100300000003900c60101016030079403070341c2e1188000038100750001c44103a03104c1c011202130741c5008111000a005082210700d03030886001600d840960369041c040c6c110b025090080c0801d1300c1716038140c0400c50711101004130000c2c4a80e207201402035a221454000c10110010110f410608500810940864641c40c8030350b04481a8000c45228014a46003c07810f00303400301403840c4140328403010450750303001c0c0900a00b40301425410404042c3d60300420041d0045500d100036020200600004e000440c05a00400d4091640400c880040c0c00003000900000025000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 344564460 1250 344563210 344563223
    0x302090604090e060f04051c0905090a021c180b06030109051b030d140409090f0516090c0203030f041101090816060206060901140d020f04021305012010090503090d 72
    0x54580900074069503404c48002d03024010f81d4202a1200e070f548410f100301f484c010000c0351141c23040ba18000c20400707006140281c0b0300106d910f00040582e000703411007145001000c1034144015124405441034100c580c000e1911400d001b012030700e40b0000b01c540200300c10b80666860b0540e0300442c10400142140c9604420300c10055000d800a25042c20070684950042c8662101047c0c8004000c400f0369090f82d00071040025005840c0c240b11a110b50441005803050003084140700b4a88a60301d015410b0321314008040c00f14a6000c1750407a40c0e44011214003448604500200300003414440e03102c1d10100d014900820000e032184185406e107003809840f0030804000ea4800c02800d42c05004199100600b00d03042800e9614080084d400c04036090415441102d0200010b070865441007401243d84002a10071501c4c0c1d042c81c0d50203900c256090140301d0104400660b00342d402074240202c0c81e03032841003101130050f207001800c202c0007501c21340348112500e00050103008261388599001c84640c4e4083c5031b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 344565710 1250 344564460 344564471
    0x1b030c0213140a0f18080a05130e0109060605040803122505090f12120f2505010f11041205030403020d050303040b070806011706030a0c09090b06090906010510030209060409 76
    0x3c2c2c420100e0302c0441c81c00c11014208401c01d1040d02450f07010050682d0043c0080d80d5a05013071a0484080c860301880c0d4800b4048250702140c13409800c09481d06a03000e03200e04200543d100c042c16034150003148a120115402000410340d400e4040615982041c291402e40219070760340701240f141d01000108420000c1c40114041040c0e1401800c00480f01000b940d0481d035203184d00349019116000380ca000c1032aa00c0004032442c42512078012240c005200046402601d40085503629562500500503500340d8240090000310945030b20414038008060400341c1d1906160a2604100304074842c02580c990000f4800000961103003000e000440e44108040d40d9285820300c1d040002c205e011348600c040180800030040c2591300a18205207071440320a2007000e55981b45e0000b440c1541009004004035200c44000903449030b10b420442800c0d04c60360361002d0540e40c160601c56403a8003190071200c0395110a00400040c02c000024076402915403402610306002d00c000b1a009902c241c2c00b4036401542d50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 344566960 1250 344565710 344565721
    0x90810150b0a0f050a05090a0f05010215060a1403010213090501030507060302040e0a0e0a020a032001030513020d02061201120b0105030c0a0303081314070608071b030c021314 77
    0x20020280602000c0703581041c11800000300007400c0d4071203c0083c0000003c100c0320345130058040d0303244210014003400ca074540b44c000300f91000c0a940f04150140c40f601c0750b0f0704100300c0100c202900c601c01c00760200c2c1d0721034070308450484184801e00705543c15550030440e034000004840c0d01c0c0c601070203a21038045101c1d491460107600d00360055000100b010300c18030080c031200121400c0b4a0300f004203600e02080c8101591000c900701405110025400b02e0546030000800101c401c070701d121040c444119480721130024005405583c1c1c100c03020044100040c080d0001841c00920030720119001901032070800800c21900c54840c00c0a0b04610300070300c5040b80080c1001960b40005003d082c040e006400d04406010215211801c103000044c1840b64240000e10301d06081100441e000c2d8215111210511140b40400e84403074850040100141c8410700240764903003e904180740d511844176000b1450041520102c034031051106080340e00000d0342e007a00b80311050300c0c000d0104000700c40c4000302207070506 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 344568210 1250 344566960 344566991
    0xe10110c0a0219090e0102210702030301030807231b040908030402090c16032102070807020d02060913020904060e010608040303020306011b060b180c0d0216060507110f011b0c0201090810 82
    0x200095600004c0000809c00155408016a81100d0340000a6911411145020900c114146690003440c048a90442c44c0001c400255500039000c2c2260003107e2000c01000e12058031000750003d4000a410004200141869264a903020340d0781000c0c1c900b00702044100a04290b049101603000480d02101c00d00321041d60810a070702d08402080c21071901205a80301801402039800107841a00d5441c010010354a82c1c0c3d08032440c03000300070302c0440403018220455009401c440c04080c00b981c80d01c0710209150802c50140740c103807807841d200c0c00140e5a13142e504501070742c802030100741080581d004011400410703804072100c2c46d01ca100045181c6048a0501c50705540780d528002d510944502484100c00c80d040071503009104001001da038600403403040381031421032800020451071501007000811648500b04240c00c03e442d5081c3c860320303004503410701d0a9908140403180c100b90044c8030b031307400340d401004140c00d42c91046c180700c929195502a018189400d005080480c182c59002780300f4400e20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 344569460 1250 344568210 344568247
    0xb01060203030f01061b0204150503010513050606040b0d0b0a090c0314101b110c0a09020c060c03040206190e040c090501020c010908030a0513090e10110c0a0219090e0102 75
    0x41349002082c288800c90a1b81c080070382c80c00041d0145541f03a0003090041c0c0d0101140e005800c0c0038000b4807507402e1004001e0403c402800c0183d416009150101c1c01c0f5107814018801008801400010038914944618028501c0540480000d944e01d030015400a002601c00000031800b48541d00c2c00c52010207169820041f022074124043d03031400c0d035445016003982455072421403003407030101014088855100d1905800c17500c1c043c2d000180400000b00d0071340325002041170070815410b071901611006880f1a40d0300003a68000d40c407260521607081c1c1082040d20b107606080341c524000b56071140500100d004c94920140d050002000d0100920495070104100f6a82070f50a281248940e8034100e0415160700030b01d1006004c0040c0042d071100034280340c2c0041409010301c54420840550b220280903518040c1a01c1004050f00f400d01040359107101d401507801403c843d0018203004410766081240c100340921100100803150400401c040000788075041149551200059440c0034001c0c82500e00303070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 344570710 1250 344569460 344569469
    0x80d050a0f030504150c0318050d141201050d0305070209070305040302010b0a0e0114040608150121080706090228030b0901050106050a1409040c030207030306090606020c011b0b01060203030f01 85
    0x43c03c02e01030000003800115120f2075aa60f0304000151030b607090200f140074003900342d0000c41030740481c1c0080d01031160200307018466040f1915010542e000d2481444524050311404059291a800c010407490625100148046100346029490441168001004801e090718180c00099540e810003041503024401d84100138030403101d8032140362608604200d003842c14001c05054080d030002035610360300e80f6044000542041000c0e26452a4031034080025540c00f441864000e100c4210048203e2400340c040b40c24581d04000068038001e003946820000d40020f50342260410284560845a1010006422120720120704000210342c914140705c21520300142c40e001090345014010051240c0001c1280c2c2c007100c0d03900f0306880010a90707101510070300540f0300d1560441c0c10303c482c4000c036507803580c003e00030b06129803010480c058449147d5011542c844c007810002d40e10244040c0800d46c0500c40001c0d2001240d00309103840d810a590f6103501c14802c2e841a009a8808400d000751548410303111030141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 344571960 1250 344570710 344570717
    0xb03070513092f031902130305060f0411190b0702010207090f0e06060621090c100504080625030209060706060306020703110c0901060e18010e0106141e13080d050a0f 73
    0x1801d2003142c40c5c4451801410001d02540d00180000c0c41c940c541d554040115000780580f80945000700d044900d4036821038040b50080042052100a4580b44804c00bc0c00781038814414a0b040c24200c00703000b03d60040d04242c0c107520803014002a000c941d401005c1c15003d83e9000030032420844000e181c0740c490b018000034802d004c1480705e20854048801c0401e00100e2103034040d0f51030380343c003950076091000e2400156000440ba0035034440c0c66410130010710485810704101d07402a03850080c05c0710743c0003041c0d07024003001ca0901640e05d4950f2082d0064902101c000381000c2c074008182c0d440204852407648112001600400c507041410307000030b207540e04200558083d00400418030001001000705018071028030501003038144403a21106469885c0038500e41054049503110500ea8004400c00d204040000721424000511780d410502580c1a044150100d0325100d207071243e0710107c541141c2c800c001c5580100200082c0c450040045510052080e01c83c55a5400ca01000034001c05081e4064000d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 344573210 1250 344571960 344571967
    0x7080d09050d170706050906060135060a050415030c0b0c0a08030a09061a03061806010b0307031b080403140309060609060f030a03270b03070513092f 66
    0x1140c46041018600d00d0f030081a041c440f644a40e1058200c1c0200d000181805240504100010000140c51405407809881326040202003011502000780d805c858540e16110202c0c00e510302e44848861103412110081081e955903413150041812500314100c6150f103c1a4150100280100702c41c02ca00038044001c0f49034076028600264903600c2000e40001060f0190020004061001540c0030102c0d03150310410030300c6641c03031010000842c41240c0000780d10a01480011607507a101000021000c2e000c0c1501030034050b86001d880c1006a0001410007040c5612007401c1141e290503201844104041e0f41c669032800c2c201400c0050050302c545010360400341c8100148841c1010002d07140c1d40c4a00e0481300c0c03146a41c1c032032022035912004100695007510902611800b090b42049412020080312449500801e400b030401110300350440c82420901c410810104140500c50001441d00c0d00b8403170000314072503036240c500e48111140194001512401094400c0c841c60b41c51800c0b00742400d204400504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 344574460 1250 344573210 344573219
    0x2030906160606090f0e01050a0221090f0102040608090f03070201082d10081002090108010e041b1212020601151d030a0f0506090f030a030905031b07080d09 69
    0x2280c072030891010601101c02644504100e0150448000741070f000005101450b2000f814802600e00c01041d103526500b00800201c07070388250700c2039409444201a151007010344445419590300005041f041c12401200b0a00c00440000d00081c0010000780c0c0d00c030300603403070b20aa00605002c203565001403c0d42003080040d004d0f0ba0701030791540d044080c110344201d213005050f03c00d082d120a4040030300e9020180d41e0802200074a0f0602a008440140040e1018640c039440700604922517182d010340422881001030003d09250142240d10034400d50091440c0c0038000050411460503a10510303a80f1140103000301041aa0f00754081d4042d0390740000c22041d414041c8030b1103040e142c40b9981c2c0070000c05410305d00e40c100662a4020a2100c0507042d0703044030801c1d08002e04080e60b980b83c245d81c00d124076030102e41d05402c001403100440700c25101a60030300e030041e441280a45440e01d800d130384a20040c403124140407e1324102c40c401488400081240c42d240c4004e123820320800701704038414032042200c00c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 344575710 1250 344574460 344574469
    0x70309030221060f07020c181e010e0a0b0d060f052d01090e07030212101506020307021915080f090f070306240306020c161d0406110c06010312020309 66
    0x181c1019042a0040d5155201701040346010b0142d00310983c42501e90359041280d03d0700708480c40c0078052000c0d403d0001310b010340c034030001007100780b2480f03d01c803900000054115030385038002c0d04042002016000c4029098482405842c1100514012103560b04240614400c954000c0b41ca00440c4581040c02c00782c00030f0b00002544014401c1e84540e503100c4805070500700040c4038400203158004d012180f051480480d155a0f01f0000c0f10074114580343c199625124002034141000701d4840303034000d501e00041a8207000720304124403100c03108101e82100100324501c07003100b00080c2c01e91320f5030b4400d1149000d1030a400e2150004e0807103403e90300007149017070402d030000c0f45c2c0c4019030360040c03c0458100c1f159a1004a001001007000f28a440d00400100030420150002d1680322401c100321200b001032040c0700a040c900c00c5c8140824a007800340d8940207501c03440c09540d44280244c40c00220000d0000002046d0390108000440540200005000704810034610b401d80440f03d1008500781748241c00801c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 344576960 1250 344575710 344575723
    0xc0304030806030709020a05030609090f0d0e060d020c06092802010c0c030501020a080115081003111f18090b0603040212010608030a050a1e08010b0f0f070309030221 73
    0x501008070700000200c2caa101004000b0050080c410115950251203200800710741054071a41d10032440700d00403c0300f2b4880003819103800c0106102a0080c1030002c2010354400710b07148030080e001401030012011192240c4050990850020046c1860745001140c070741c2031800f4201d20918003080000c0c00c0459000007040750502960a090800b640b40f614142050340091a50000309250300001d412840964040062030480301120310707002c064412002c080d120380c40100c0c1c1c6e03400e40120070318080011450040d40410f10704000360070341d0b036180d1685400c00c0c4074004090318200414016a400d040302c8011001d8040140610394040080b456000d0010b03103107200251001c2c0c032440840180707241011081d0f1015008000030000c0b25510652071034064016005400c040010030850900d0000c1c05001c04203000201e41940d03a04030ba00d80c203000c41d071900c40e0005810840301c080305220b00d4900c154010000c000d0240291180354503d4954810031440b0108036008040002c60702c40009140000003a49 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 344578210 1250 344576960 344576963
    0x60b010306180b01020109020904030e0a06030e12180907030b0a050d0c1a0c0109150c3b060f030105040b0a0b09100c15060e1308250c0e06090604050c0304 68
    0x86003d91101c1d004034090520101c0180d403020b05a0140020190858400d148007401900c408641503550704080d021a400e41c0c1d03a01210360032000842002d01a0b150050141c41f1031084162041112000407440702c0c102103a0410100c2d03900c070400c1c81e841c0ba283c04484001c00045400c108452580d940702d88840503180304060303c1421810441c0c442541a030144e03240034032560004c004074001800c0801013811a03002c450107007842d25855a8030103204500590030003081042031900b410712907411038030b800d00c6581036281c40003a0b00d1541403a580d8040c010600707031a94019054036541040d0801003125032808003240302c1c44080344200301c100c001c9401e48800d036500300c0f114503944060080a9903030550080c0001d10b00a0241c4007508040300551005083e20180c1d050b54410b591964104e5640040e200740c0a48800000d10100c485001e220090f005a1446031890f20310300c03a440e51f95440405000d0300301c042c2200b60780081200d40d05000c074401d944200c017114240700780d091511584400c0d2001400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 344579460 1250 344578210 344578259
    0x1b08150601030e0d0912020a0b13061701060f0807020f030a020619090308040609020a05041407120b0105070206130b041503050903030103081207020a0b0c04030b090f06010e2203030207060b010306 86
    0x1c246e4199541c44090500501400c44110f0b502c200303180780082143c41900815001c120050442541d803440041d040d0b041e101030780ca07031a6840120031400e49019900600580842c405c03554205040c4605102404400c5161780003050b0328200302c25001200161300c100c1c4000f16181080e0503000c00d80c000e03c42508903802007400030f250402400401d41c282e8041d00301310740050511124030110303001101071621600b420b503130301002d250030f10340d4070825110385904050025030305101c0000945811001007140d0b40204101d181c0031681c441100805401c81e07030100007180e000344807998000760107000c1c05a000f110f0300061880c640c195a210000da00030080f42e4808940d100300040ca000d4003c100d4030408513000807070303e803552070101d011010640c858001100d076901440c000c900700d030f076002620982006401015020036070030440210700d0343e50000e00520b01030f8046a03000f144180c907021490400d5009681c05680c0d41c4181c00e00384141e81000641c1ca04062408004105040183c812108405500709 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 344580710 1250 344579460 344579489
    0x90a1a070c050d080a050f10061214010b03010f150206010306021c061e05040506030c370e2a090315010e090105070503090a1b08150601030e0d09 64
    0x3030119034503040454014502c0c800d481024107070740c0e00026018429110600180140d40d25421440b800c42d40176120703011720310036402d000d04c031040c081c0c2c56918801022003000645095a50840c1d505035600fa4801e403844c0c0c40c000018841c8158000c048000b812000010b8007a160001c13000941c0d50005120107044c0c907034042000e2544081f1414045610211041e081c0f008684802c0b8100003501d04851142d00009031010008a5041a02800d44110345c002c02078140c0b92400402d2203c030f800c1080507440c02d041300c0f01c00c84001910780c3d110300e0007003170704d1501924440d800c0c4000f40400c0000603003d40256140000140782c009503007401c5914030882d0222807900c0b100c51102003441c120081d41420b420400c0d82c1c00100300e000a004102e8482d42083e40244515200e921040d661031200b41d4009070b2540100c140d000101e40d21000701d1404000e1291001c18690b55500301505203410b01044051148891080c000b242d0380c1409241810208072025000803540e0b00700181c50112180f1400e00d144100c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 344581960 1250 344580710 344580721
    0x50607051308010f0b010f02010b0d11040e030a020d0806150901030f0b030a0807020a0e10091a0402030a020d1a010c14190b010306050a02042303010e0321090a1a 71
    0x300071070001802110300034469030011100031806440135035041c074000b8089411900d00c05205024032039a000c0041c00c2800f04002c280c840395001c910404c40150000e0b01c0e10602e00c40040c00300000c0081c500c10764080c180d20800c24800400c450000341220303120b03800342e9803043d40c021004c6003103d0341a0000d08001030ba00f0074080c40c0c100541050511242d040c042c40c50346c00c0a0005180c001c022451080740e64100d4581c80c0c01c05c3d007041da041554550040e1000320000e01c84a045036000c03034950a211082500420ba800d8001010f9030300448000f035121380c0200c0c240e400010300b405020201b888032255003002242c0400024415550721102521009100844e400441e000f4805446c0307401a10420342d03040142c0e4100204181030070301c0103e548500d001c0004540c080e4910991741921900d0f03031800c458902100ba90448101210107081e415565035500806140f420001441c2a032451243c0300728800341c10000c0990140001c261004c60b030071440401d00051400c0350b80c0b954500d89045003032043c0e103d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 344583210 1250 344581960 344581987
    0xe060105061204050a12020c0a0f0e040f1505040f0203010e0a0206030a020d0908040f170a02031e03090409240b0a1505071410050c0a1d040b0d0f1e05060705 69
    0x110001606c40707070110042800147d4040340901c07290798251009075660f03030780d0785081c2041400c0b4440e8100600b1410081800661800500381030036003e402d01005004980328403e04540341505d00b1a5054100798403041141020b026172003d03201000b02501e0300784626008a0f140f8032000b81000200780d40000e01c4040701032550711001509400400e02521651134640142c00c05c02980a1004004d603050040d81c00010300041c01e492855000d409069051000102c010500c6595042800d040c00203024008042d1100e1141c54407560041d0b1200700565000740200f0720072003a0400301800e06003040140016501d49a05400803541c400c1e01482c1080c14001084070a8000c491000703280b0b4001c44803000c2929000030305c0340c0110742d01c004100104c0d02c4d4400100d40b07601c03900c48108003050341e8107041c0e4610403000c46100a0350501034800308180e21000001050900546c0741100c1c00310b80001c0070810301901d224041c1c2c8600c0c6403c1306107038000ca2900d03071550b6008010703d510104600041d808201052 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 344584460 1250 344583210 344583223
    0x20403050f0d0305100f0b0a112b090b04050d050a02061206030c010f082e060503040c06030b0a1203020a060218100f0e06030a02040b120a0e06010506120405 69
    0xc10809072041441c08000858680c1001011180024203010100c4c40c0c0302c24580b24601143d0600d030340c00046034540704074540a50420141c0f0383c00d002c1d100496090707d810500c850007603440341440d01039102c1140d0711244880400c51100d5400c001c95031105200c2c4116840407202600e0040302e5042e907640f41840c29500d0b1020304070b00250010b10228200d03802038041c6ea1180c0c09000102e0540d107800d81c40000440d0044458001940050305030f40208040d000804040390b454200c90802109031110940c1c04120071000381c3c850800514000204024000c010a034000a00140d240a0040121050001e0b400c1100b0340500001111210003090805008001000766a9802030342507407a00366183d0703c040c8491181640c2402010354140d0704da001ea11800203150781c0e101c1900c4a11114004c80706120031600300030b20003404540d00b04004100c11581e40003411501c2d910000d0142c141c68850482020b640070070700110815030103030300140800d641d01c0041c0c4400c0d074100030300c001d030a55960410910300340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 344585710 1250 344584460 344584463
    0xf280204020a09091a09160903240f02040f170307021e0f0907050d0c0c0b0103060b010f02010207050d0f0509210c0307050a150c060c020a021c020f06030a020403 71
    0x91001405480154000c6400401c9601c0001304004800840412028604158000390b80c0030000b0800581250742844025030a10405d28000e00e22070348030b54ae80c4801a20b840c13402d0203152001c180912111403180507800304400300c420298142840d080310300760351107118050f200e180783d201ca1509a00c41800c01c10b851100707400134030301010401103101e400c42280031104021300541040004c186035003420000240038951540d10545810300142c0341c0c40c020918130045d031081102c1205900041011405068040e5005040016010f8480c070005004030142c042d403903041d640140300703d00c0882c00c04a407144200040b420046903072080c80c88115040c2c0301c0d080701160300c400c0071002024544800b505114401d0101011110f840c0105420540d482e0413510550341d10802c910420303c000c4c43c40341e03c009145411030034491440915030384d400043e106482c0e51007006900510300001036240100d04c840b054017810500300c2084c001034010441d0003000710250f50040c0d6001002c5032001c1c880d5412030340190b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 344586960 1250 344585710 344585719
    0x80304020d05030f22060509090f060a030218160903080d1508101b051305150c1e060601030203010326090a03060204051801080307060b18010b1201080f2802 69
    0x415211780b860350b10008a10000525203020321000c1001401002100d94040c00240b03045100d559003052100e070b10100414040d041400e0440000068072100c4403659192800d14070300070b045c0b800c1c40c0c207a4460305620301f600c010013030f001e10104003080159088030407080300341c240490b40300d550140e04000e0002a40c00808948070f58a88910b075800b0350350045008180b00303a800311161194040449aa019056144260700b6251100304810300c1c103404060540c0d60307807003443d50411100c61055420300500544000c44c0780801ca134490291501444410b034004800d080c21400e55065484410402c45600c01d40d00c40a029044646d80310403a4a0540b05c4c1c0c008001d02c4483c2c003a84078540340010350424820310b401002c100300b0045000e110012443e0507145143c000303506082d000e444150280052090085c3c1150150b1401001d009200103418040c1c01d40100d55039a890046d04084000740f0160701801c103075000b40c83c15540710080482c60011229031211035842c01c281d40c0d80d1b070030030705090084003d520 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 344588210 1250 344586960 344586967
    0x3050c241602060c101104060f0503060307091e05011a03070e0d0c0803040501031a030a020d080d0c0503150f010e0f060c010f0605030708010b0102030d0e0f01050a02030603010f09080304020d05030f 87
    0x22000005080d8504a8014800740304035000c80c280300006018501421000c04c00340c01c190401e9038442d5002cbc5a108500504071803585940e000b1000c100d450310340d5410a5800c62969405001d80d09020b11401802a41c03892103041c7c2c803400101d4280e0002078088820464101c04003d80d540d194842644600c1e0000b400718900360b40c4041e2682d03664440c1c031446000c03038245a202c003c4d480c40e00c54504140c607030240c0600018291582080b02c442c550303100482d070182041c4222181440c0c240b094019480c840e8903066620300302035103400c0301d220004803500e204414400c1c2c20760030380e64025400e81c03500c50184e49810f0b21418040c0090024014589410303041d620303114200040112031f070444412504c058090301d00450b11020402d00340d0b01b403044807501580c010010404ae00c80594810401940d55800b03590740040741017290f03070a48009650b840c0105402005000e06498207100b44901c0200da0303841003000b84059aa041102e0000030000781c8608c1e41c007100401440400c5c8110382900210454441c0e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 344589460 1250 344588210 344588227
    0xd09031e1202100c1103030106080c190c20030d030b0d20090c19050a110307030804020411090a090f180b040b0a0b0d1b050d0b0103050c24160206 64
    0x15240841400340101c18181281c244443e40a4032046850f910040051b45c5903a08280003520340110103000404d44000411414400c50014000c4c0003100703155a42d182c81c454400d06200400c60890710100f0083ca202d206003144c1613400141d591b650038907505010403d00140d100241403510290006080307080c004e61003000d100c44120504a5004044403051110344031807008200310301503014911000d40c00302108400945c021809854120760300d1511547c1034002c0c2d40c41b075045412014044001c60b405906200840c5440e00130760910b00f500c090b4041c20308500c1c000140301e00c4154071600d821666208480741420b1103e230015000c1d800e40c07040c189908281850704001610003254142c0300c1c2c80700c0704041071080b4814000c4502e407040040c0613520b041203d4840c585072902405402c00c9810403000005516111150040403450042e0380c14442e96240d410414146210409610304c42d00241d2400031524181c00b002042e0140c050842c151180990700703880380300c0401c00e40041d62003500420780340c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 344590710 1250 344589460 344589463
    0x1030c0905091f0b131401121511070f080310080c03070b03040c081504030f050a08060907120f0903020712021513030b190b010201060506032a0304050a0209090d09031e1202 76
    0x5444c46806c2000001680d0b038040844212200a10051420a51f030300301c00c4142d4156080801605c0e901180140b4140c2c817941d58039040a464007044810b01d801000f0064000080a10030300140343c00d40c0584942001d04001a8980400d805248c114590200c00b040c01e00c00c510481001500f03000c4111801081000782442070300c00300315804c034001801103003240c056900c03a42c1910002001034890040c1602d946080000d01c0000815010400160b02d03440d214182842c0564541105488800520800395080c02424100190040500c40c0705d86c0c520000107841ea901030111030426010a6030b05c400904090041c040080d41c00904100299000e00500c0000280009200100729208000307480c918001a400d0f94198810141e01c58800e000290000404c2d0010240042c000307001c1044440c01400080b03401e030400e0f50266019400380038010308600701036840c1600812040020300111442d8603000740440b8080c040148004c80b8080707000382808211001e40340c03c1c0d502c81003406d000708000038001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 344591960 1250 344590710 344590721
    0xf10121a040e030316090302090a050a151512110301091806020d1a030604030801050411041e0614031306020915030406050901150503060402270405030301030c0905091f0b13 76
    0xa8030017a004420031031054098000d070310850713a02804260309642c5400c0c82500500000380003900e4039440b04c1e0740405910003804240003400340c0f40e0900c260041c000701c004240007c031940d41c0140324a4454045440d440100a580c1118102400410419003812000c4840300504030010140360001c034125035070b00050b802c84041c1d01a025800b0282c3c0800b101015038805040d14050040b61b550001408541429003011001101130110036240903a104003440103600c02507054100d00c08450400e10003a40e024240c0f128040c1d00f06d6580c0e00318244145080407510b00400002e0601d0750024460f252a12181d0316032540283c101121340d140c1c80c042c2440009413400311081e0070154a0250484190345c56a6540b206640d009001422242c1e80c95017400700f440c404c0ca28604401110801100c0807000c80d0036041e20552013100915140c4d40f442c0750048200d02a90005030b07009040c54108100000006100c0c0c0032901c040c0c08086440607440061001000304048080c2c0241c1118290f15551110b034100e0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 344593210 1250 344591960 344591971
    0x240405180a0b0a030201050304380a14100e0603011e0510080f030403060513080a020a1202010507170403030b1009030b0603030a050304080304110301020a030b0f10121a040e0303 78
    0x1848106090380400c00c50383e12501000b4049035041c40490042048018409100d1a140c0c04492002d00c1c0c40d860802d0f00c003d40703854070800a004000300705010789a130244071480b004081e09100c0c0d90410b000f036046000c0160141c1d201070b4801800040f0b10b42e03003d42001c4003801c048019090a801c0c11101c94029141c1164914070a00000d0000100368400041c0b04e127070481880055414030341169a010003515010300015501200c0410b0704004c650000004e012301c0200307800512032100986009a01594a44002000d6902d400100814140c12000040002c10411441d00b0141d95074542034008001c2c405d070041d0042c40240314404050b400250301003d50380248840074040c2ea560b0f040582c0c03842822000c0000900500100700025008800355404c1840765512a2048883e40042400c84e0408070011000a403545502d28450524181c485882201a2814000c440b003010703003d0917612201c88850b602940d550318100071b203800781030000500c1e107004000b4440035030086801aa03035082942c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 344594460 1250 344593210 344593231
    0x150e060603091501030b070806010c1205070501020417150c030c070210020f0a0b010f08010b030d0c0c0801020a03020706060909051c0e0303030109022101060f0503040611070f06061424040518 84
    0x9c50301d2580a060410b812640c8569000000b4886050445040d0042c5004407201d6400b03000100d05984011242c0425440c024000c2c540701560301d40d801c104c0d0f8805442003408aa0801c140b001101040c8203d440300f03070701658842c034405110303030040785400d001100000b900c0c0900200705c42005000381015040b42d5110754800e03402920341001d01d0884860680d407641c035911607004482e001d40149050508103006007210103e056031a000d0704d003aa403100300302c200000e42c009255000c00c0101d210303160250406403c20031039440581c2d6031550707400c03a8480300304844d516142400d400c80e124400c507139070082018080e2034807543e6405004000c0d4100d006200300c402069098450a40040c2000354100c510541c3c070030071810295801900d00b944060000d0300c40fa515898141e01807800003008000503840303044496901c0040382031900031a20107802079410305004403110f803003513034540300082100201540741d0100081d0005003250184120b600603500300d914084c13510400012a092244070781801007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 344595710 1250 344594460 344594477
    0xd050403110d022d03130602030c07060e10030b0312040b030a1b051b0c0a031a06030714060c0c040507110616050a050d0902120304060201150e060603091501030b07 72
    0x1003030780c81d584e40001c0000780719901411541c90600050391090080c44420580e440c005020740144080d0b42c2540220700075134400240058200010081e050041c6a5450615404500740e000907000740caa13000032004264984860700e003169418809400300c071404032030301036886540e14003120380c0340c2007150f0342c8902d00c0c0b400303a440f10b0f28104107a94440180459076010710707141c001d1212116455001580080307506c2012449410307a140c00e503060000d18042d05095100e816156403410b10003c00078a01030098015000400006044c003101140b0020120350ba6034654409242140c6010429441c069000b810a814000300315001501c2c0341d40c84520741e0035290b05980b0416a25848452440c4800c0050001c12103000c4051040c00a40f424060040010901c8030407a00082c2d40352400a0500c01c00f600005030401010360244510384911203d0604d15605616183d041c02101c2401060180a0040000000c41196050010f91400e2603503180f980d006503100d05101480c0c5400b11007160100e5940b6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 344596960 1250 344595710 344595733
    0x60c0114072a05060f0a06050a1202130c050405040e120d1e0612020d0320030415080105060d05040c0f030813091e0c2d09150206040206030402060d05040311 69
    0x3004981d16a0880001d000130b44039005c4080c482e81c03000700301c84c880325660030000c80c15070f589000c840c1c020f01d02d0200c4039035010880d004009000d51a05c4128481600c0c141112407601c2d0042e0503102121021600003404c0700450050300c4c10895150b203855069070780040c040b80320702c40b00e41c0248822980300710f0f404152010f022140d4121010740c002c3c6040c919420f08808010729004030307061100d43c03003803502400d03000100c204100700100881c60101c1c0c641010400b441403000300606400c039150070b0f14040e031130303541747c03102088103403013400b80700491141c40f4800582880000610b4000800c00d2002d10a01c2c1c59403400d0410940c4c12031681021808510320380010014614010345010180340400c404401189525810042500c0d081002c14030508080c0444a2100100c0080c81214840c8261000319410003006000c440e040c0c114048500e1403000c0c0c400402e9000800ca80c0c420342c180c400c241e403600c9900004032603029140200d00954240404c2000f01584502a207041c021080102d410b2341868 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 344598210 1250 344596960 344597027
    0x51f05010507080d11041706040201020c15030103022e170a020403020120010b060f091f020a03050c19060f0b091504050a0f020406080709051e060c011407 68
    0x105034010300005030030b22038804c9064a552050255800307484800f4076080d40c48000d1403041c00b50200544554203c202000199601840300449548044400c03151082c49091810514003060001a008445079603a1446d510242860402e002c0f8890800003814085854014000d0765030280c89000342d0000c6010411510311381c000c0e0b40689034161107010f10303c0e0f042c0d952000d50b81103121380038400b50b490b119403002d1502c50000412003900e00f185030650340c03050342c0180002201261911400c1d00254040d80602c95070109050720380b00e48c03528100b60703952900101e40303283c0310368940c03c941040c400350400c20070000568000240303d00c50003c140250351400c8100128a4812100c44480d40341204020380e007464946d005590040c0322100c00161000030f907030041c00f241c1081d086040845c291005200215400480e1100200804c40d5010042455140410007a01d03209030042d02400c030200b4007031001d40007034000140c080c0390400d10705000c3c13614000c020005c0c0164805402c81101038400354140b00c0c1d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 344599460 1250 344598210 344598217
    0x702180106090b1e09010e0a060306030c0b0301060507033006030614060f0d1b030804030311031809072105060418080a0e01050403050708011a011106010e19051f050105 74
    0x2013010090420704c2c81c1010302c2d40700300c5005040100046001d1055a1228034183c082d203c00d50b0700140740c03401d40c600143c2821440d001655a8441800104025548030044800969261500c1d50180781045454000e00007071512443c0c110001c0c12548061220366400542140d000c2d00090000a0160204504068050301c2407608a4240030800340e95040030040d1101d141c2c8180d41e03c0701e80408e10929440c2c0c4140c0c41d002101c1c80b1400240400074194400c0107260840e00400146103460215102c80210800441c400c5004803104170000c0c1c5002c3c003914148880707441c45909120780c3ca207c650800d00400003210b03950320480c0b600d040c030001710701c0c001070a000c0303151f110003180d02c0c00008101c1981d40380b82213100369042101c104000301c0041c4091041c60001c00b2560000b1451011551140c40d5080d04898001d0410110b000ba181304403200143d02811142155041206903c803001c2d10f8041d40220b1606540c154105424400003004502903407500a164140800503031303443d40c004480510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 344600710 1250 344599460 344599477
    0x30403080d1406010f050c07050303130815010e043221070203071806170615061602010309061b02060603060c03040507090506040f0c02160f120f0203030702180106090b 74
    0x1c3c1a0300402c1c005c1e50054004100d048400800c450a269954000038a150300510070140c590b4a4010200480a820130003050900020842c2c0000d644c1480c0120403e1031b0300501c0a407032180d040000d243c0c1a62040c1c80c50201c10404a581c0602c07418007402e00786c3d1040c10786811603c44440081081fa10408001a66100ca60003405044664600310036081040c1c52100201c3d80a41d0780c800008940908800d10021101410060265803421845416001008140c881d00914007004079401d00c0981040f929036841e42404c0000c0e01304520b0600c2c000510403107580e4184822600400543d5036000200c00e031054004074200c41c0c40380c3d200c45080d010303800251402000f50784045400c1c0417070362454210540c8018003030400203020100d2034035241030f204014200c10240e0081c10141400e1012561030201420400c1c04070400c161a001d00d8031025503042d08050002c0d80315610480031541c00740101d48840f81c008005404088c507030400d03001e41003003e1040501145001d0800501004841e05681c03060707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 344601960 1250 344600710 344600717
    0x90306090d0f05030907050d0302070e0c0a0c0642080a020d0b07020a020901090f0f11030720030c010c18210515160f0302070c1a0408030403080d140601 67
    0x380e92000d480c650005131105d03200b401040004141c4c2c0c6c40c1c03840c9588505000380e00800301546442050074450310041c14034003c10004106090603590405180803480d9808074000030b071403240c01c5200350745904001640311405032424244001515410000c41d1421201c0707040d40c2e100703a9400c1c540e651915400e030000e4214103020791030804121300d24a0346512102e07e00680d8000321031035002503c5184260030914446544012180580d803051054034034003980c01c203040181c408105808041400000e10360301c100018102c402c02c081700e0400d10b0300106242c210407640c4400c0010b030141d01a041c0a0700010000300390414610a00480920403401c484100004c44001c1315074241c40c400c8407020321802d481600c00d5008080f03080404d1000d40d80f082e200409119040203078031070020304444940b1412801c0500501c04400890006070440086800341442d450b008050420b0020050241d588510310502001c5400418004048010055441c961740200314050b9482e540904502081e500310b07000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 344603210 1250 344601960 344601977
    0x2010f240503161a04030f03030f24180b180f060613090203040204020c0a030201090309080a0c0b070f0b040c030606050a03030e01030c0509210d020712062d02090306090d 75
    0x1110040d0313040404807036140590300d217400d0302c81c0c42c0d081d0a01a22181140001e5480b01e000c08008014480c40c2d02034840c0b403c500910317041a2907091a01c46490040c1ca444075903110020041000c5a40102100c020161081e0184038100d43e0b1081149030480e840440c40c954000051741c2032924074101c1728210159114030b00305a0134410861700a40004004a07041503081107440b000202c104201848030f4070070760012400c07035101e01c7c0c001c04881140c3c1c003080c0c5c590304c80345081c000152a089070780191010000640c0e21a002410b000711003c7d4482c42c080d01140c615000d10091000c00034500c425a401410244502130343c0d03005001c6102518400035001940d002c404031903662082d0040083d99805242c0281403403103010003e5109440c2101107241c0d1950105513407000700c404d00c1001214405400640741d02d40c544003104010304400c101c003d202c523959410300380392940e44840100c0002c03a1006002004100f040d003c100951025517014071a10519002414103100001c0c06481e0042a66540c4070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 344604316 1106 344603210 344603219
    0xf1f1415040801020d360c0e0108030a02070803090d06020a030b1302040501030b0402030f1305010213061218021c08071505240312070302010f24050316 67
    0x1150348060001414005c0001c5d01d00c0005135803070f68110041d500d242c071f41c0713030852503401c84102c00c042c0708004550f980c8008090f06007076110b82c0840704225102c3c0c100c83d40e04e00402d40380d11741c00780403484020001209034002c3c1480305a41d00300819a42001d0303000500c04c0d04410401c504170b81c0d0100e41000a036926000c2d43d102c0c04001d680461460420071104001100c0003000c241301962201162020804258112481401c210507450751130798072040d0060203880d138102200c25140c200401d015000403219000b220700c039401042c503030b0414610b05036103082c0070a072041a12194020300c03018000c9541008030011596024274000740030710748a602558035528004680c6500b00154030201c0300750710001400011107100703141c1d09449244030318040f8050158000c0000140b410400300000390010710800d015100b801c603003004011501c030418160741e5044200b4007403444400103410003 = true := by decide +kernel

theorem cover : BRFrame.Cov 344424460 344604316 := by
  have h0 := BRFrame.cov_init 344424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 344424460 ≤ n) (h2 : n < 344604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
