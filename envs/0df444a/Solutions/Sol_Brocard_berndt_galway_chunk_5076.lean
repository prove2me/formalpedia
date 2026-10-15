-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:39:52.000849+00:00
-- url     : https://prove2.me/submissions/f28bc645-a1dd-41f0-984b-52b5a117887f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 912769784 ≤ n < 912949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 912771034 1250 912769784 912769801
    0x1b0c120703030906121d07050f03010908030f0c1e21060a0b030705040f030c0e0c040b0d090303020c01050f160207060503011205070812031009020405090a0f15031415 73
    0x3d82c811035016040010090046140f03420050010749040f0740880305140d8444422440410004161901250304018842208080c182250409100141624020008510b500031100f10890348141c0c00c0c0c0001e40f4003043d5007105049198140c1c64122a45001f0a42c01d0400003199a0749911865201c9030482600d0501c00041c0380f0000c510607100c03030000020100c1c80e1103208404680c058001c8100c02204259a490020400d41d02d40c8035090303041024102007550f0a200d60216012039030404c0000d4100f24200104000a10900c84100c042c1a400c101070f444d02c5c0400c0c06004e102c0e0303001c000c500002d0300c5d104c0b00030488914444425001c6400010082c40b0003074000090303e064582c0c001c12042e9003207161030440d15112842c0c101000620444445590000c80c040046105102820780e5401e001d80d5401c04809078000c40c010745510070395180c00a01c112295500c09640c000e403450300810b80c05d495100e103240003800e5410588014042c03880321900200100308505031149582c19803401031900e07030380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 912772284 1250 912771034 912771047
    0x2151e12040b1b07050601090608011104090b040b0d1b05042309071703030114060406080103080a0e1203090301051510050c0f030f0306100201060305100902061b0c12070303 76
    0x20010070005011980c01c03d05000d10803900e081c00702c503455460041d8148680d0380c001c2403080b20482824004040f81d00390042c0510401004020041800d041c240015600038101a00600760415034440500885544159103a20150301646081c3c0c031001010346851030405c0e282e00244e00a07800c0c50f00c0614041c03c12219801081c40034565007006031900034045041c440c1c43d40c0310280034060005c8000c3c3c0150080019812144136044c1000b00760082028804036010310710401021500280041010a00000040000d8469464860302c0368105200103901d050000103030091075400070030300065a040c01d11440d6003050319075080003c2e4030610000a0011071690440400b00b090100c1c0c525041c4501300403030781b40b11180406903915034a0368004c81040d900101c5001c2d00c1113091001403400d1704d00602c0740c54140d0760004043d0290361002c901d02c10180c54038039000c0760071000800100701002444122121002c0a50018211800c644000c00c550140050092200c58004070070410020f50401d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 912773534 1250 912772284 912772291
    0x26060402150a090b0d06080f07350f070510090b03071437030e06060118080118060509030307170703090501090c03030f051815040302151e12 62
    0x1080e255540101e03050844283c40264498000260701103030054220300c0503084130003030310700600840f4000000320480b20342c0c3d802e0074400e5441031907140b0840c0302561980998074101140e078001111100c14010442880c01c1d10080c01c0d11030303075001001c2c02d000c030b4600303882a070b031800c807517031410800c2c984c24908414410702c0080d0140040c4038600f501a044040b2403415203176602c4500004d5006407410f41c501589845001e20b030440000e03409580411400c2c064411010031a00081c01800c1d44c0d51824010341c1e174a5000d809801c042240c00d0303400928000d01f4020121003280c030001c3c210603020145800310503614080c0c2000c0e8203400605c10407115075844042d0521344c3ccd40307001c41d40455494a0200b54001e1540850281041d424400000b043c0850140403d00716882036680681241016200b10b0710f6010300bc400e81d03503040c0300240090140c6000184400024a00080e041c42c0a54035400a0451801c00e060b291701c2d044041410103000c0103889490984401580780b8901d404c0c000d646c6c48180d1407006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 912774784 1250 912773534 912773569
    0x42d0903083d030f0b01030b0c18010315050607080d18080d0c09090e1b0102070f03030c0c0b03101509030f0f0f02040509010b0307080106050906091f26060402 70
    0x4903442c0300d2121000b09000841d04042d0540140b0720504001d201074000b40000d81d80c000000c03021400c1c5000e410102d0310b0002c95142d03024250000c100c01100a4100700780070307800c81d0040520100b1580c1d9414001c00b4000e10032102c0035070785c80c4284290030903903041c102d522a80c81101c0c10240007152046044854400764503030006a20190040180c1e241c120ba5080b940300740f440c00542d20095030000998004100c2003240c03100e4010b00f00001266910014000c0c1c500f10881c0a0003000004c4c0a41100c04095114400c40300c00340c0d84a81140a0b250001c80d81034080c440c000c1d0041202d044007509802e941c6409141c10100e543c155201e13982d035070744c54160081c040500c51708d108040c402c102482800c3c1c1640107005001508000f91680d01811a04030645d210f8000c42000080e850360504c10581154000380000d00c0316a00c0b0000c20000000060030401e429a40002c1185000d40300441c05000d828004600c0165007030205100d402016100f0702056254004410301001d0780c2c6110082805046a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 912776034 1250 912774784 912774871
    0xc11060105061b010e03160218010f060e030a0b04050a0209011e0b0c01091203050a060e0108120a090e0408030a0c0509010804080a1803061406091302042d090308 71
    0x3d0407403460060600b881e084049000c00f2820190f41d2840500c1c008440d402100d0b007031014807003c0050ba01165083c8290300b4010080c5108001181c01a22000303051440242034600c0f024041e111010200e004a4048411748c200180c080114079044046a000d00081c074500e214803640881c0c20200881035001c0c403a507800c00414500e480c010250000c0e080158480000144d0300100140030340907003030960f50010f01030704024010074031003040c1c3d420604807241c40005006d082c1000d601c074a0154070000020040040381000400d90000d2982001d015521503000b040c0c0e00d250680207201110801110b00c1708120b4100306040705130382c0c800c1e01160823980021245507180b01c443d078280c2d0324804c1418000c1c0c07806000a0300000b0b214a6501081010801d4108141c8558820307040000040c811a105071040310031101600c00344c28164800052820155880843e1094200024801207000b510303503500b16454007105d20402d62700040c2c1d03e401c441d48890200c4014403101010001030105e14032100c0c007050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 912777284 1250 912776034 912776077
    0xa0b04020120011a0109050d0b0a180816050c010302030f18011b0c11060304200f130c1205090a0f15051806070f080114040605040f0c1106010506 64
    0x90340c0941c41c0b0b24490701d0007001980c0749100400e0b850750f00188054003054400c500002c080c10800d40c0c0b505440d5001004c03444c9c82c0e9900c4002c40090203444036500603a00494a0355001801c0540181810040d9101002d1404420319180b072502c0b42800c0030504140c010300034014114401840380d07800c0b00d60383e50704102034480303261924014401d010b02c1c03090b87c61903010004407003134101d0342c1e0f8207445000da502c0b0000c0c013a000302804010321055400814000182c6448003c000343c0b440c4120540300d0061580c1034621230380b00084c4000c0e0072418960f8099989040607412103420103030411280c10800d60a005a10b00106000e40300c416108000d00403c3c0e24042c2030042105403030617002501048602086241400b81c0c0031151001d5171a1240f59038840c54000c119428094070103408220701664607807243c2da0030450f0302c49904078140030340d40d0881c1c1c6641000c04d0540d0380d03000c2c03103480300804e150024910940c1d02c030080041c642d0b820002c40c00e802610050000c0e4844078103e55003288103044201444c0d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 912778534 1250 912777284 912777317
    0x708070f1a18010e030712170a0e060309030c010912031a010504090902130525090e010501031833050c2508040b030a06050910030201030c05040f030b180a0b040201 72
    0x80d2080c1d113540c540161100825402d1102003d5411180600461b040701030380644480c1180c03003813104140201d07003402a81743c00c0d031400000943e4844c04550540303043c2044800032900b911142d0408455945220740234075207141d814030425824203a504007890414940c6400078200303120314000c0e092255115142e00b001d54844803404000341d01604001c0199240c50440604401403080003802d00c5809164400e0301070f485801c202007a10014140d10980364640401907008100b45880131101c01812007280700824482607450786500340d024041000d1070425524000201d0003c0300d1180381a02d03040a1007244086001a41d8008242c0002914403001c08a03c002d00707031800c2030300101811800500456000340c80302c080c60140c0402e02060100d5034540c81040f0055034200c520311304580b000304081015620a4002e41040c105504159182a85070034580c8000f8403035070000c1d07400c000e5000a00c00844484900021103500c0d04000e800c400c00280c2c0c0f00c000344080500082d0402c40e0300d000c0140c409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 912779784 1250 912778534 912778547
    0x10e0405180a1104050708090c0f0a150f091e1406090607030f020d030902060706051504060915050a0303212d2d050a0e0708070f1a1801 60
    0x901001c412a00c0900042c0b800d401c51082c0502ca2502650404012415650041180c1c0e80215041009090780740c80803400d200b00e0311841203180c0d5205281c031400043e03c0c0d51b0300301442d034a0340683d5a0461081082c08010f0f1a11186034403560741c00c1e61141b80c4452510486e122001615003081070045850407500020744070740245031585500c6580010440308254006021120008180c0c0a580300d40202e414190200c030307848540a500503804020b11800694142c2c0041d5000e54042c032140030388041407003c0707011607500d608800540c0366200046590b041d401310300070000b0030003100c80e581200c0c110740d001440c42c0702d5010316511107017601c90004403105664020103016080c40c010b0000b60fa51680800c050a16003405a601091529244c0302920141100640b8010400401800b200416022400003842d0040001c03540703030745c1d4007288051301c01c040c02108018003041c0c0c001d1119904008003002880c24035071041b51281c031813503140c080e103803c1682560080c0c403070040d441d258400c80c180180c519 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 912781034 1250 912779784 912779821
    0x1b1503020f040b2a0a0b06101701080c0316080a1b12150c0c1e060e0a080a0f08190903020c0a08030a030608160306200c060a05070c02010e0405 63
    0x18004045901c0f818444404802074a50b134480c03d4460700100b04034000e540350160301380050240d072030341d000080c84c4e41806210212143c80c14648041d0002c80070354503a002e00000c3e0032421040e0000c0400c0c1c540c03842e003001602c503800c01180d0a01071161504507001d17039504070500010f100c44c5500b2011a190411030341290001d000d648003022081c1c01c1c078030b0100b01116403101b02521603446d001292424070300c180c80414403a640840d204002c00d50811084129242e0900c040703031310603182e4502110849080c081c0080091090409a86401210314058003010080040c00100710000c81080380080034002003465007590f0745000940c006040c1412401c2040030385a050304500140c2000490241c00001004252440d5800b0411a520303038141c00e8a440c03004128080040c600401440410020350148400c403a65011410f071401900c144040c4540021381c860086410140c00c02100020034081ca0b6070000c04e0f840c00e00a1f004666001925a007204026280a030750b99400050203070380f0f8030310b00c06034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 912782284 1250 912781034 912781049
    0x10091511030c0f06060a0e1b0d0902030a0f020a060c0b040f0c090e1b040b18091c02060708160c030f21020304050d11030a0c110a060c1b1503020f04 65
    0x882107401d42506a07074402c00d07680755001d682d0141c00087c1caa10503018180c0201c60050700d5444c0d040380302814984a400c2440b00c003a03220754070194000103076001c0000703030070392403148040d2400a4010700400c410503e02c2d0b4400300c10720202d40110400640140c000f0b40e4000e40c000c60001000c00e990600101c040ba2a030030002d215860440c06442680d0005807030100502d03827080b1a0640c41a0006103c29903810f8111140c102204000c0108450000d034490b50707211490804a07800b85a64404c0710044400410510001d80c0000d401e120010741c0c05420306a10200b992403003800d52a03044401060100c950b0405020010100030f440a81071003201d91049240315044028001c1c031250307841030025482920219024403c00310b80e150034a00644002c00020340c80d0020b10f06010300d504040d102841e0805044a020740404460540d55449a0390300c8042c01c01c035a213103202038100f40342260103100791882d180117400340c1c50810024078203011010072038480030745000750b29009148000403442c01107400868 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 912783534 1250 912782284 912782293
    0x3120f0207060e15070219020409060f150801180f030309020f100201020c060f06010c0f050c220506040912140913050601080a0606050d020a05121510091511030c 71
    0x42030200002c0e41411105400c50740d030010740ca030b118061f039a0383c1d210f10844045040c402c1c02c000140c0b42c150321610f03182d4010540070440841c026101c4c4200c3e01585183c4250700070f048801d0040003000d00c96100088412800020001281d0f141c2c20040d01100b00300a0416444055003001c54485098401d803d100c050140f074030305241d140001c0e010b1b4000340783c1d0044a01c121800607000404249a03180640410717114100b20035134944525071421040e500503540351107204654071681d2601ca09601c0c1c5190301030f0381c02d402c103009912a00152803002c0c09451046007000184404208504059100d0000342e007003099840350765201070382d114024201c003d07900c84007040c0c113030303c10700c0c120b800103031240e0343c2680c03101429940c0c46c1000080b0b0381e5901a94002420a200d04112a40c11780c1c0186401c900c181816802c1905071004000c2354070b0200d80141c001e10a405407002507082450340b50326840c0960804000702801e0030007030707c000744001050504219040c298800240000e008640c101104401902c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 912784784 1250 912783534 912783551
    0x30f0c08160f02150c0d1b0212070b1305090901090209010b03090a021201020c070806070c060b010504121203060b040503190618140c010f08070c030210140a060f0303120f020706 78
    0x80130030ba082068000e402e801240c00b4191803a101e912650004060b281c0d40f420400c1d16030b001d0101003818440c001544d407045400101e840c28141c4068a05d24040d21811400d103810b01050250759000908960503aa0410000700c00503600c6003801e5054807008211145c8a40c0d42400e554a02001c0c0c1e00082e4121412650003104043e040d0010101807007210100d4414941c3c0d80e540580d21401115001c0000300c1d010359242c00900703150802040070314145042400c107602d54a15551044000314101d070721000854240c9a8941c250084400800c400c0c590b0f2400c040ca0080440e80314010f8040d10480c1d5a03440040b42c041244a42c00038400105400c50302002e08103506d44140107000181451040d07102e0f200304404207600c10450a55500000c1d500c2c0592512030000070384441030341d498228158000c0305681c164068840c814030741c0404c852125020f19080c12865402242e10680210b0a030100588050010a4002c07504958200c4007400c00103d0f0b000042c02d9400034022540020300181c140000c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 912786034 1250 912784784 912784819
    0x2090402041d010f031e06200a11031801030e010f02070507141e0907090e070207051e0303070b1003240b011d0609030109060c0804030f0c08160f02 65
    0x31400b60200b46a4041490742c89804c000743d0384e1001c2c40300a00a90556a000000d50320718014050040d02c101e10102e81c903000c03010300110501c803990420107a01404140300008aa20118018294003080051403074600c1c1c010502081200854000c1c3c1410f440300c442c484926401d600140c082c5003464030854650901c4e190450300d400241c407030780c0036564001520f1850361425100800203100d811028600711001041402400d0800034115802e11010010000d079203031015045500c40e0034982d0190400c1402d040400a40c1c0b42c58400781d41a40381d40514680300e9031000821184015006405000980c0d0b0b490030303200e50f9820b00c0e00020b041322140c1c551500c0c840b080301034496120030010000c0c030034074411a00440315000046240e82e100b800121029055007402c00090503d0704015002244210141d2900340545002103a075030002146c07001004103042e0301c481e060300c0d41031903854114a5001c0c55207903054640a100f00c1d500d448e031101c0003082c0030455030301c0107205c4041e4080d115000c9014102d25 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 912787284 1250 912786034 912786059
    0x7210203040f12030507050301090e0c041103070201060e010e0127020a02030a08070810052206030c0323100b010c0b100f05101b0201020102070b0c09180601120f0209040204 76
    0xb007102c44070710070709101032098041d00a06115408036525103085a10302900c02c0c2c040c1c5003079409001c880c01014041402d41d00c440c0600c01101c044012407903541c0c00c25441c000e08588035584504017807141d6400500c028010440c145044407907041494403100c0c2d030400e0880100c9031701002e515200748001910269650080f01a14811a454035480312070b5490180c142c68a48003141d007a900c88801c50010700451501d5001d00408603c401c040142c8010001801001c40301c00390000e1300c107070a201c0700401c00c20500c503440d0701008038010400c1c8084a4030044280c0d1300c80d41e10003100e003810f0326001c0d489150b900c903102241003690840302040c4030b42802504061155500c0c01504203841100c440860181804441140e4072516952440c07810b00d0f005040751070340130400710300728110754003044910003190504e000710380100d25195000340c6d40c1655008102d10031420400041c4241d40344c904002480c5e0b00289408002180c0600110f981034203826158000d00c104030201c0e9000c0d2003c40c0c0480c00594285 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 912788534 1250 912787284 912787313
    0x60203091504200a080c010f03020d020f03011a1207030504020f060304030f1409032503020904030203031905040b0103080304032706090e060603060d0f0501110306011e080721020304 80
    0x1004100c402e86004d01002d208039010740151039122455465155104420581d590311183c5401814500000c841a0a0b0381c80b10140c54014000400180150004106c03401540007804890f41d150000180c02d1401010006014105050b60f440000d42951500310b148018150010310301544e038581481c025120b1f46507044c2d02000104161000c0044860410886100d00001070081c605014954030764164449000050002c83d001d4035400401611480d8410b80181d02c40d4018507200c0c908060392702122205040145441c500344400d00c40840d60380c00020341500d400420159485d90f0300c0c1001e82e10320004914021000d000c0025400b051141664204180c0c2d5407a035810018135620308504042c500e040c1d84169216000f040400c40343e2828050f0540e00307a01c6840304018404c0940c03501402c55803071800c8465440800010031030150703884445e03c00b242c441c14141249441c20010018a803801c010a201d0a010813046490711203151403100540e03c44ca1300e10300303544e607103050310703210b40401c00d1328 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 912789784 1250 912788534 912788573
    0x6090c09030b100503100c030e010e070e130f021c1406060a05030105040b0a05131209050108060d0f0618061e14070507020f1c110906040e0a060203091504 68
    0x2c8000ca440e00b520b8424030001c0340c0005001b4107006c0680080c50005064600d00641403650703417240d0303082411080c081c0380481003080c0040d25200d80303012104150301600400003014940880f078004001041c03103c00802140c0c054425001c82c002c01c8114504208103408040c1c194502c00c46400a803000000d03034644a544240c5002d11000d55440501d070aa07002600c0003004400002c00280c4400880c2c2e124070b900c850000c6041c02c00c0b000617110844200ea801c142280020080e07032091261756000039034282c0040c030949807015406840e4981e0b480541013000c2c010840364842191403003211903001201c0240d80c20020030810420000003881000d804458014a000d00348440d01c580e0050165405101c0c660070344581c0d00e4403180b6400c0182802d0740e0b100c481e5009803401d0301142074856240040c84618818078140044c50118810410040c4008080900c1a03081140101c207070080840e05050031030740510050384a46401c604139045c0902c0064440500c107100c0d08000c2400312440e00c500070404074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 912791034 1250 912789784 912789803
    0x21090612063a0302030f0304050d0e0d0222020906040b03041b0f03030c030302120a020a120e19050102280801060e0a0620160e010803090d020603040606090c0903 71
    0x405204071880e502001011000c2c6042c60140e1180c1200302c891041082d129205681c40c0c45e18016107450304c0d4209131800e07149540841c0c2650381d00d80e0000b42d8849080c0044a1448024110f035000800180c0050701d07808200c070584901900700070660b01603449440c0c000f4a42c0d40c0302d5407030304040e20b1140c00498040d11032900d11050800b15082040000081d5043c07001d4801e0b09900710f8800751707280340409904a04042e801c00414452440507d400d50041500c2c41c0c0245c0e0311440100001d00ca140158038440c034851901005444c010030025042840c007500c40c6001072400c910307041440c024022042c038511920070703d00540c040d00203031005040b611401d54540003200d90700c2e480126803000078a0007950300701200483c01e00005010303500300c0e10300c1d860004001c1002d64007103801c00d00b44892218480301e511136800c024400069981d02c1203014109900003181400f00450028050502011000e8010200000410107100d1160004030140c106107a0034400c0c8035189074001d189000700e1000751317440c182 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 912792284 1250 912791034 912791059
    0xc031d0d03030e211201170a1403070501020a210c02061f030203150402091608150402161b06050c06160c05150a050601030c020c1e210c0307082109061206 68
    0x1450396102d0603040c1100401da542d0700d030350300e5408001c0c04c400d941002b031100b4400f19000030424001080b84441d103695591783c0e00703540c520641200740f0035042d030200780342081d604460081d80001c280d544948003050642000301d294441c1041005150401303505409603002c54030401c81080c8080340118820303126917583e50b07180058003a941e23101c0c9000d580005c0c0c2c410b01003180000c14100415009000810051034001c040e0b5012040740d80820086808040f40c213284010b15010420030802003c250902d24640400d117900c0c240c44103001000400d0409017506691440d80c031a01018141d40d0348001110100e00020401d1643c405044644100d510b0804000515a501c40e0161000003440b5400405a03048450100580c60040801741c0c807803141001c81e052030700c1d580c0844040030b000c00d0080c0f800320940d0700320360030741400c1161042c0e0f40a0b510400040004920009203003428007400c1c100002400c04620100c40c003072180465899124101040c03c21a0700134400b0403d000c4e0384112000307a241503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 912793534 1250 912792284 912792299
    0x9090f15100807080a0b0d0b0a0c0201150302060f0408070906050f12100b04180b090f0d05120a021605010f0507090b0702040b130c0c031d0d03030e211201 68
    0x110019600c0c80001c2c0c07030030003003180540201c0b0100e0f04419651390105504014202203100701c0d040c084182c50741c00010b818032003118501d00c245003020a0520083c404203034214080305241c0207521001b401900300003000c50041034007009480c05000c20030141d4144581d6547e41c0c5003d44a1402200c0c0300300036180701c0c10310a140003a05100c280210002070310307082d1003400c264001007188140c4150050307200d01107600004541c46244900c0c0e1f00c2150f054140b810415502031400d651000201d100780e000800156105800c541560785000501c1c010000d41e03a40c07100c4180183c010b020907803c50740c1c40140100104541900400380f00300c411001041660340e10002107070004014402d030500818100488009420107400403051010050410b19611200e030303444d0001c440011760032000240da50802c5408156103c442032000407505030160045401e440002070300c103034810100505050340c510040807100014495070880000404020402050400308400030b0382c81030254204901102e0004510071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 912794784 1250 912793534 912793549
    0x110307150e180126010c0203130b0301030503071e1b06110c090c07020307030218041202010203061c0201021c0503010f0603060b0406140d060f030c0803121b09090f15 73
    0x5808501e02c03160030b6440e00400c86540b001c1c254001400c19100004200c55039401d0240041021056005681d40d40c04504543d810082a8100d10f0740c0d60300c00c100410224500205a94001c0d8000d0740000300e214004025603030141c42c0e88c10060011086a240c02c4401580007a200c0803180643c607101188544080300a864600350340416910200503004104102c01c1398018100a40c03028045500094480c0c0000d80603242c08120041000b803a0b204010800c181503001d220744c5030140c00290301f181440c0000503140f4520203105510f440300030b2484c074203582c0308000b801030301c401e507505682d8603080020b4000c040d03910034080d0030300c000c01250300040d140e80309200d401d045405800380c29003024100341c0c08860740c0103d400d0240c5030100c140000c0180303000c0c1e846800018035402c0781d5000d01d5440d61606d4000c0c01c3c0542d10599032074000340010990050350b8010071354060b000110b160240c58100c035802e00c01c1d009405499403c80401030030856120401c0340c600340100c91500081c10782255007005c01603003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 912796034 1250 912794784 912794809
    0x30f05101b0c14011116111002060601122306030c100c1203020c100b0a0e1e09100f1d07050102071509051e011403060d0f110307150e 59
    0x842d08280440814200c000010041c1895000032601d2003042d00300300c0c240c0e00701c2c0c40040d2103c101c0d84510305c05c2102c210300040c085581961280e000c00e96403403000e1348855000380464180303c032004060b030140c0c4582e0300c055095040c00c0b00350211504200518410444100c40c110700920130310003d000c84c5e00c0c016002c18290280c556070340d40a24004e40e07800199102038180d40051540a01102507c0c001c1071103080b805803100300c0d0002d03c2c140d4941c20081405110f50000d06884007120074040d040c0b044200c030007801015010610342c04d40750f45a0461910464808a01c03034145401440e0400e040d0640080e00002500c903012100a0100c420a40d142d1449120311405a0b22100707003040030225100504a00b40080d0030080405036aa0001c50080148a07a42821040040003001c1e250740c0c00000c12070000c0300c03a10109040d8900000802d9442c0c891401c05000203a02154040801c600c03c0416100300304d0180545810a5441c0015103103004003140401c041000c0c0390b0407220398104001e02424 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 912797284 1250 912796034 912796037
    0xa09090216110307170a1a0f06040b010207050a09200a020307200a0906080f07032d1b0602060c03100501031d150a0605190306020f04030f05101b 64
    0x45003000e90355048403004208094503058000c07401e000660719110390303001004820f110085c041202c0e080c600300810b9010300e4001f00501f81c043c8140141d171048942810b80c412415100060b00300c0040740140c0c604107080c1d1041c2d91080b0016400716024002d600b080100c4122540c0e1101c41900d180404011400380e01e01040041e4014002013000c0350200c103008403050070400205d811100b80b400451a0306140d900a1207015844990810a45030704218036450000f140001d08070103811507840151040c1e040c040000156a440c0800d4901c0410030084404594001c0112808050072030700014103103003903c07414004d070140100184203c030750075084920410704071085c4241c0c1401e0a006400511080d581c494001602e08800032828500700051400b0065540306c51500349000c0c0114002c0c0c0725190410703400340202c000071105002006103020b050b01d41c8084003580714506111a8107641c0166031020741018021110710301800804103040c40500408281485042c4802c2e034134144041c0340500b82c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 912798534 1250 912797284 912797317
    0xc020106140613180b0a090b010e093d05010c0312020a0e090a090b0702030903060a0f0e070f030b0a020c0d030504031b1109011a0406030e01110c030a090902 69
    0x524602d0400001e0040f6103030340484410403600d41c803c815080a001d0348181d25103603100b40d0b5a03030920341281d181e0004e0600354010b02080c50050002481c540e0b20303601203805058400003040290301850701c9100c0e4088040403241d4840106a020318810000d9410102d642104900c0440d095105421020802c0c2e0540c841c1d5080100c110300c03d20003035100c08000342c10410365940e80b101a550b03090100e4000e60101d640402c9100b201e091460781c4020203008801954810444400c0507180401c0c0d880c5d100504030000034a0301c50b4000c0c620054510011684481c5c040c500004c0344080c0202c02d910305a90041c451902e2075a114103081c0c080f40304804032100c09502024100c1c40551003508490340c4503201c1d10b020028840d55804611511851400841d54056503010010311410074400c060f0042a09041d0799201c04140f541026141c0715030300490040507141c83c441d001803042508406096004242132701c9e80c804e44130310b0032a10390300081c3e102000546080720000351444140283c5000f01810328400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 912799784 1250 912798534 912798569
    0x303070c0c1214010b0f01140d060f06050a03380a0f090b18071b030c1a090606040608070603090219090203010806160f0807170109020903010c020106 66
    0xc0d1004406010300721119000d108011820603240c0741005107051190040c3c11800042e82d07049801e50364044030460040074851360050751603901410403512000c1540c0340590300c010310400a0094207a07a0040c18a00426403000514540d101000308801026664100110380b00c601050407140f61030803030614851710a6481d40d0f102c21020070024000c0c00018005004179548445c0114a080241e22045410f65a1b410b1000603043c6410000c1d41004a4442c060302e51802c00c0780a0b1045213032201041d4411003464642c4101805200350140543d0406c81c114803549100307840380f000c107000700d8903403607180074041c0440c000c0e050038025502a40c40c41000b4001d00742c200b101c118000d00340100180e0340001c046124401d80748051040030f0103003c1a000250703403036040200042c40c05c04003800c0d841c0c0c681d82c0f081030140d68030351103040c041031407105203088c1d22280c40c1d008045498505d4a05403030b210b820410000150f101240d802008441c105400902204440400c240d0890350948910342d1a5001410030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 912801034 1250 912799784 912799787
    0x15070b090a08030a02031e04050f0f010212130218090c120a0f1101030603020d06060302040b010927020f030f010e0705071106031317040302040b1c0b090106150c0b1602030307 77
    0x10b154000075514031400026001c55047c0ca14100540301034541e6007240e43ca03165103031014400e040003160401c0096280c111501c4500b82d10303810081c0400d120f001e02903d038000710b40d540e40b4988001c9802000a040c00c1c144145070603183c00d50802e40610601101800800090002c01c5003104180c000c0245102d40300c0b140c580e40341803402c03490021704060740d8140100060707a030f082003d940540113000010750581140305010480d840e8003001414049480380c1008910f1290705a5041d50000c0340002121b03001c0100020003034060400384e8482d40030080100702c0383e0200300c6052812107503075550312889038950b001e050303400c0d115803040a000482d2610010006080000040d138201e60100420401c055141c1c0b202c42508000d400649001c480014040056207014012820f44c8a0100c4484401c00307404c1604001c2d0301100c1070000d01000c03031000040d4651000307501000c020004200a84004001c4040080054440e95812202810b616002c110102261110440500c019400035465915040e20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 912802284 1250 912801034 912801037
    0x2010512040204330806010506160c030609050f1b010f08100503060117010506030d08070806040908040b0418020301030b13061116050d030516030b0301090215070b090a08030a02 78
    0x106a03041030311100410044005811504c00c14021000d62000d841c0900f8801640d5111560007080150b100c040180280d507203130001c490851000d1101c9000d0b079611460700301c5058080d40e00107082d0501d030081d0b41d0180a401701e403410000d00f40005075001c04110b02e114078a01c0c88280d001500007102c010480324414010f41c08540c005145480e01003d00382d4a82c0080c1c82c0c1402604a050f00e40150011502040750900816030010301c224042d240703441148100520321034004240b001001a920086821626076900c40204e803a040f03651950303120303201c4409543c1a405803084409a41081142c210f2410142c402c1c1c9041e02d030f020369280240d4607036a10079002604459001d0b5440c40e0348035805a8034081d1a40186100d46034110181d85205880c02d189080481c1500d906c4c00b03143c1040100142d054403a00f0040d2a03201500b030019103a11030b40040382c010403034084000d40010701c004510032400e0040015018151043c0443c100b66074a00c81e0298642100d014010410031041c00481c140d0500c940 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 912803534 1250 912802284 912802291
    0x4110d11030f031317060c0f0c0a0305090117061302070203150103030216080a210207080105010e040c080a171605011802090c0a0c080703050f030c220302010512 71
    0x89411150310a8000081c00d1040011002c041a40001424101007111034500c00041862000d51a1003481212100d0f03101c4000901d44d503010000002c04000545061090380c00c0d501d001c008036841c5241510300503002d540710301d001501042e60304090007103404a640c9018400e4001030148821040140c0d40c01c006508071400499140c003070710b11002c1070840703440c81d40c6001b94003a500500d011840c132141d500e543e001c550005034180d00300c11b0510010070680038090703612050840c05840c609000c800708a0a181c40d0740c0003400715508110000031041403404415014a0085102c6501aa0358224581da212581a0010b1005016214101c040e2411901030540c40001e040c1c61401d6130302541d50282140e04040324400f40104c4466104258141184826070041442000501c1c01c1d48156015103000c000d100300401050000aa400415110784159030048528615580d1603003440400c88021f500072640c2d5400721101ca540c0454a04160b803c51800c480c0c068541a21f4900324643c00b001150004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 912804784 1250 912803534 912803543
    0x60e090703020702121b0904020d030e01110a0302211303030503150d12110f1f0603080316030b1c02060c150a0c1b03140c01180f0b060904110d 63
    0x3c1c000c11025840790082c01805228400240c00005401d000e42401e48081100310f81c0944820f10030000162200b001c0922000e4050410340c40140f84000100d50050306810300c2160340c025280800c080613000140708c2c6801007104103044140d50b2a0300801030a002c1c049205104291391201000400d005030011500180c0a010016081000700c0c04900081500001180d07640c120840f101491940440100300201040c00545404118219040d649003001d49441c6000c10840625103c851250782c4458000c55000040c00e03120710340301c58980c045c000c0c854400800710b41894180345052810f40161420180f642c0329040442c3e9643d02403100343c3d009010800d4591040f001208508103100c1c06452203005188008140c04114402c001d00b160f5082c26030008400e0384042403800641c01202014040343e0000382c407901c620a03140c0583c01f51008404042080750980500300500c07692035040c000f843d0050841440310344400c414010f9440044401505808d40702c03083c46040d01d00010010b07a940c0c010f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 912806034 1250 912804784 912804787
    0x40305031b0406081603050405030a050d0e010e15100b0313060e010603050601051203090307060c0819050306040509031c0b18011805010e09060c2a06011e060e09070302 74
    0xc1e00646410394402c0d00000089003d003010400d054090400c800d03000e42582c5001d01036800c065846c00da803801098201024030002080d030b031100c04610350040001c20075010083c041d558803003070543c0c0c981c1c0c010051444003103010000518110341a030b9120086804000b030301490340c0d4880a19482012140804070f80082e1a106019098942401040701550041001d0030003549002e0030000d00e900014078020841d001405812550b580104400d001c55016050400743e0024a01d40700d143d0b4414401600f03082c0e1500086010203c3d40680694030514040d42c00704166254040111340e280580c80c04800c00120b401b803d0081400300b50040c416411000d40194814003d2001607405a08240c0000200e00500358040d0b098191600034180100714001c800c842500b0414216512040010521301440342b0003e204aa410303140342d803400110b450140780d88000c11a9400c0d998035140d0a208044000c07219000402d0080c0700310454100720350103500c0e1400c0602c840418000c041000412140034141d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 912807284 1250 912806034 912806071
    0x2072606100e090a0305071b051002010b011214041101022109040b0105070305040303050f07021c06060f1401120e0a0c2d0e0402040609110702041a0904030503 70
    0x6040005901800d0052022640c1c07608200d00d001e200000200340048580c00700600e0700100740c02900b10340e4100d40098a1102c0d800181d98040c01640040d80092707041440440011b80c4e682d8194002000701d9000d84c0c40301070200c040d001d403000703a8003d640e00340c503c140840040340002c4e035070503c55110840180151058208103403806c43c0c6054140c05800060100007400303002c1031070184901c0e02c0031a0b003401e2585c14110144c03401007440c056404024140b00300054880c00ca00c44010580f13580c2e80d402050b01007062000c100d81c042502a034002100c0c0241070000216010b0000d99100c82501c12103441c031868840132100446501481141000c182a500c0c400f043c0d141302c0a0086403080c50040c10551101481c01400560310f201c0c040190b00038803004031a034202080d110081c0c0c4200e4034207629a000a031102e00004000300030f07a42c80002d1907450040d00c0040503000c030002c1c0c4121402100e0401ca903000d000a0100424242c0139101e40c4414854001f400007402900656003100000c00c915002c0701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 912808534 1250 912807284 912807359
    0x1a03010b0f2a010e1009081207051c060e06030a02031218030601060c0203070602030f0a050a021f0e0705120604020603040f080a090e06031f1e0615080f070207 70
    0x20800c141d00d02c2607945035018001201810003114425904c080c01c00c110b0500c003038940e8500c030300600303807440c454461a502040010f0b1048050b074241003031040e0504040303005901c0080007442540700c1c00110482503c006803142c940400c07040905078020f0060542c0106060b006401030f0300005005c12400b10300202440d80d80c6040100d0382c00b0300391984480800203298010546842c0455000d20115402000100b100580c11420342d280780764241404c81e11800a00016130402a218261760785481d0800740f6021092030036000321625040703d00958803e580ca45060108041880c100700c0800d84c0a00042001414088000c5034407500aa030030b801c40107841d541c0c41204c3c1c0c1c8260310038000592210410700540170342090322034120300c084004050401780e07107520741e41e44809118590030b42682c960300500301240c47c8040f4410020765010811407141c40325602c04100e5048280040003070448000914501a101c100b00c1c0100980d40040c09201d00e400040100c0000400344044500c058402215092 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 912809784 1250 912808534 912808597
    0xe130803042604080d080604140709090c0203040b041806030203031603081005030604150e2b020d1e0504210215031e090102040815011a03010b0f 64
    0x40d445540016000c0300580c2010802a000310804082d2580400040095600000741c2c03908514160800303c80a03a81c24000030028900c101400d0618441141002880383d4400c0828040d1864000700304602c071030440c002c80e40e90246003e40b00e19041e08000910802c62036146e00f04240580c03000102d5499260b0303002c41d0840e0841c40809003004110300e000300c201904207801561111a000c130060343c092410b030000c2d945074400361014000010700c80040b6080301580c1c011010300310b07402c002c4842e084044685520f01e580e15090000c0c0451030348040032121807000c1000519600ba60341c50401a001d8842c1d0a50341001c40c00b0004240181000001400a81940c100c01150403540d5040d080000c103005202c0300c02d4800e441c40c401da400800c20040b21408c4c5c0b603002c1050007403c4218981b02ea86860804c1d0080c440c039040480e80348540d950820031580c852035494140c44070ba8425510980409040c0c40d0a80001c1c0a80c41008206102c5102c89420f2500941251403d4541c40b01980140420300e03c5032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 912811034 1250 912809784 912809791
    0x90209060d022a061006032f1215090415061d0105092802180a090204082a0616020a03080901020c030c0d30080720070e130803 56
    0x102c0c0860b240102c0d501c40e21100f01c0305800e9441000d0949071418958000d9003a0060095400345903480099151441004490b1417251050810065900c11504034000c1241c12207100e11456002e034600061504030402401140a4800351a682241d00d603507407000100c00442c180b0040b0f10f079541300005151124500120f45440b40c2e044441c100354100004c2c007841d044004c181c0c40c6000d94044020301c50407056a044003641c68048030040c0c45121012000c91240032903a01941d118007404004110610700d98003d0044840707420494140519464a24211180c4501220018841c004548046042c41002001d5450324614042154111540001d84891554000751001c03000030403c81095601007008592120b8128001d1540b02054400a50185a0000020045a6088124403030440000a00600030144010600720b841e04850010601d510407990f07030000501d681012001143d5001010100b01100c6000e0084103060a550500d502e002030413800003580c019400c040461034a0016600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 912812284 1250 912811034 912811057
    0x219050f0f0d290901050114130806090708060108060601120b04020d0b01020607030b0d1e05030a050d140c18030c0d031e0512130501020d090609120206090304090209060d02 76
    0x298044000003002c981c0d0883d0520f01c459000d6220241c10b603070760701c426103411100d003440e00301a24118040629420b005e8102400c01e05e609080001c036071203c000c50081e00c1400008103d400440c0d81c0c41c00309a03584000c1c8540c8016410504c045207055200c3c11200b5010940200041640d40019003c2000c0b0383c07142d42e034161840c0d59042012019030381071041d60b4001c5450714043c8000000c1c500010002c40c0c02c600003c1c48000700c01c10716020b0108841c40c10207016004000d4079100c50152202406540c04103031555030051030164100d002d040807800b240e0098500d0400c040c182a00ea0301d030341d40700000c075210065041c41160b250510b6540e0744002d40760110700c00c2d40c1e000034500800041841c28049107110030280003003400a03001d643c0030407054560000b05405a12100110b504281d40240301d800d0f080d01650307080483d400140003154006000c035038401c511810461000070012600c5080699941034950001c01040140c56980d80251000c51030041c07289241c50030b000d180004076400010101c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 912813534 1250 912812284 912812291
    0x120c061801020a210801060216090f0e0a0f060b0d35030c0409050f0c0a230f0c0f0a030e1905060a200307110907180608090c040219050f0f0d 62
    0xe2060342c01178101340140610b00052180d148081740e080168185030059107441595442507181c0d60300b15070070440d80509480c040e00d08041645c10a19480c03035010400792030083c10088502d0301800c201c03d0811034a0340102020b58040c912071018207400c2c020410301c1810311455844d28841c801540f0045000d4480c0e00301440d60740d4030303100e414019910001c4c100b000c00b202c50001c100051940c0030031101014604d1404080d060708152210180385a060321800d0f4010022920506003520000103100100c864000ca0323004c641c00807542d690310b00802c1070040018899034003110190400404a06150782d08506a0812603180c4000c540960005007641c40002c000e0400388030314070080081000032170300d010040c600d0a001c54603152490500300c5c01c414001e9035200c0000e84058402ca11441d510159420b1081e2907a9890500500144007502d02c1324a6014411500c2c400349058405c0340da05403a508070400a002100703600340d030907400801c1400d00040c400c124038690500c000c0000d02d5085900c4170000b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 912814784 1250 912813534 912813593
    0x18030c01050a150e060a050607030923120d120f090602310b0301140f120c090105061303060203040812042001110312040c050a0b0405120c061801020a 66
    0x85544a040e4000c0202403045010311049440e86ca0340741e81582c005a41c101c0e0b845102d854111040c0032107902c645404203102c00c00c8010b9450b0b850076150203000c22505641240d404260b40743c2c4414001103014045001c901807140310721a2a0481070001c5400c83d80090808c402c0c0d03c6000c2681d01843d040790b0300c041d014884801d46003110f0494100c00300d40d01d1040d0025420f05800ea01e1034841802a210729107400d8000c0d4030035941e14260300041040c081c2c4054606050280c0b02070341e5201e0441098071401c80300c0000300702d6050090a5600441804c040d0080092558886800961028100340c0e801c003020081403001d2150300301524025807140c100208150845c080d848828080e01020f2410001d410038504c00c1980004213981024000352807000f426220380c540b2081850003a441142c01c144150800a2170320302880c0608121101a40da4003403114814800076142c1254415056003d041803140c08942c90a2138190100040c0600450b0013080c1c4a2311070540c3d8480f82103084030510443d0720300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 912816034 1250 912814784 912814811
    0xa09051216060e0609060705070c1a070c050906010c020105090310060f0e09010908090f0d060c02011406040e120d0609060902070302010f0e0d0f090b040f290318030c01050a 76
    0x114814182008050901800c1080b40c01e40c03580c030b011f0407010030080701240000501c500328a0640052401f40c00d060703090107003444500342e180c0100b18143c6400102520014590a20b840c1e80c1c0d00c51401613555440da46507503401502d103508102d00c0c050300742c46400e405843c01149442508040c00b1000d400b48185440c05440a00491009000c0c001c50b9040c4401345001580c00400c3e90141402202c03140b0b00c5003031900c081030617140c0007980507001c1402d20302804440b0750103510903200c5038420705044515698000c144800d45003008542000c60381301d526044900130994000d802c041180101c0881c1190355160160203662981e0000074045600148100030150240704030249900180020b0200c203411403000e81d00c2d207000402d40030500510213800e40045115001031809000911002501c41da00d8410316a502c11503805108400e0304034410f481c650200c2d05036003614410725410030914560390010b4084c18102e0101e00100c680c4000d0000d0015040203010306481103501d501d0009421405010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 912817284 1250 912816034 912816041
    0x906021b0f0615090103060b010203120f06010e010207030f030f09030804081b0d0c0b0904020c07081c080103330203090109111801050f0f0a06021c080f0a0905121606 73
    0x109040382043c00520482903140c03c0c58440c1100e07000f0500103004048040181d08502c51071072040c44d088044410401300c040b0b801580c5010f904207984100f00c40009100590b0380c1c032010b000240418100711161000a440303500ea04000d08007511304400c1a036134a0781c902c00c60703401c580c111110725000f41e00b04c41406600e01c00760740302d05101110290341d40400c0ea1291600300c2c403103024011034450300040d01c1416807600e404448075100040200ca4041350380380c00e01781d240d07101d496802c42d000e29010403814800d44111741c0c040c1a660401071036070780020001c0890440b10004001d0f119070f03400d41c03240000001168800b03140314410040c004500802286003000c00403503030002c80703881418500707003031008203441001850650f001541c030074010503c14000242d505646681d020307400421a0000700d426540071410001c42d0004640b90f803803400d00420240c89580040307a55124800040c0c2c00540c124245d1741041d00c1e031a000340182c41e040c8041880030201039000d4a50141a0980324441c981000514403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 912818534 1250 912817284 912817291
    0xa0b0901140c070b0705160c03020a05060705100c12050103110424050105030a090804060c031e2703080a03020417070806070c14060106120b010807120906021b0f06 72
    0x40d41c4000c1c640300345108110300a546000d03041072660700024403400d009004940382000507810209040015140c482c500341c4140c04101d005048852001405007408030135100080e0380a005020411040803401c0010990103504804028510300e54014080c034600c00c2d20702840c018942c2c40d010151410602c420351310001020100e0f6112810002d40d04600c3da40310700c00303488007441c1507656501c0c0d000c1541c01418104c500540010700004000419507003000000c80413038442d40b00d04204d05a0764110100c0508401c0c0f10102017089203103940701e0045e03a08814503440c81510413003880340d03480ea1110500c43c1c00c581e1344134020940c00641408907824440b40310440d9a0240c0042c95040e003014512520380304090260018070084400c010100924002450340107902d0b00304807441036a4401d0007d1030a01752110101c4c40030301e07205e032098070ba512888034548140348a4803141da40210b41c5000c03c005084180701503414035401d002c2c0318140291541c000107044030310303401091b620304080b46aa0402c54040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 912819784 1250 912818534 912818561
    0x3030c0c08043f03091406190201091a071b1e030c05120a031a01021e0705040905071d10031104140a061a09130b120a0b0901 55
    0x81440058002402c035800c1c0c500034604092034150148107111003c03411450089070f80301050740701c80c80e40800360305001d05034000d5031084d0026507665201e5686004107180c503500144c041054140c411158082e0900d0391041d4030001075906c840380c45516160b042865100e4000301c6c117000344100305502c0341c03000f46542001010504d08140a036650700300e82c006104c0341c004080e400740c4400207040c021410402034541003000c0e20700e00f02c88410500140c0d4030061000c0003203131800500070202d8105a0f01a40e803001c040c0c005007030b0f0f00304000070104c5460b9180081340c82c6104042011420391100e000b107981e001c3c4964003e100d41130811809141c0c0c000400c2912074401e07100801c0043c0f01480325600011a6008a070000324200303d40c01103405010081107078031b401c0030710310203100c180d50b03d540c480b4080340c640e40c0f660500d4580380b05290300e00744160541d40394480035801100080203e250311006101200074400c4070305048114032142042c0e1115000d480ca07101e900c08200c4d0390380080c0100800388000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 912821034 1250 912819784 912819797
    0x1e010f052119140a0e03040b0309010f06060f0e130f062303010c0c0312090c12020f040b0607080c0a020901060512090a02101d1201021308010c051204060f050a060303030c 75
    0x2600f071100383c6400b00800d0300e11800d4a40240400d10030060046801404002003c281c1d01d29000231164045c04034448803030025890700100040d4580708008041020f03140340e550404840022041143c0311070007198444080340e0b02c240740070f40300f00c440c0300e03400c020501c42c00e0410030650046005650710b048200103c0c085c0e410200960029a8403d080042c5076600d41860305d5440b407200700b944010604803030300914a8895500128003d00d4104090780392a1081b10951047c2c500c1c1c00c240001e6070365007401d40344c0000d4140010000907a43d5406410000e500f135080316103104281d0001104501e080c1d0085000c2080040d405603000c00c124401503000d02d1030350060140c0035032a804550303524103210400c030811215400b1a100240d4110308042420310040c58000ca0743c010043ca54002d500c84031409040300d00301440010301440c180502001540542c49040c01c200282161406004005104945940d9501e20082c080c02c09803181d180510202c0388006a500c0c11032070013500712000b0701d80d820140100d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 912822284 1250 912821034 912821051
    0x507110304090f240b1b0a1109130b0601031107020306072607093c082e0e150f0103140c0d080c0a150903020c1e010f052119 55
    0x910541c460308a82d8060017940d0740300502481c00444500c9501c1250150240310f500c0000d00141001420340a001112075605580300c1d403002c001107031507262008000d103e5400c0040c600e98007070b5009031850080d2120540c50840075900090a14404481440c040303804003c4980e804c0815030461074594603a4085d804081c282514044c04c501034621a40070403120340a2004030343c1a1400340d9422203c1207120300907060742441d2000b030f5581c289000c1d00a00e8441d24403103007000c800c40802c0b44628400d10741070b4003e061955000e04058400005180c90911802503041c0110f030004101620030b5941c84042074103075040d40340c81600f206400e5046006a400780d9401703d015911803070040046603000d0085a0340d503008202040c100030403041c000e000c1200c4820341040d110065040152018403940c00d40c0d00d044610710801805004055040150744810300c20b1002a50280444880c00421800e01078109551084426110303041c190109240c960703d20b0502007086100d0405142e0507234882d60a108180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 912823534 1250 912822284 912822341
    0x804030b16170c0a030e0f100b040b24040f060804120804050d110c03010204030506060f0a03050d030c0e0604080a06140c09090a11070804081203010b0d0507110304090f 74
    0x102e02510b500303106980040c0b07000724a030103640444410105042554004003500f24880e484401c03c800d60b0750102e052a410700c5840c68240301d6400014001482c03070116102d1760f18200a40d02c407001400840003410400460302c0c2e54640121001400e140c1d5481c0d426292500e000c400c2501842440c1c000d200302002400005400401c03809090b01103840d1a00d4001240d001341ca02c1c10780d16881d8183c040d40700180c0030007030140101c0d155204803401d603002d40d148000c0e0400c2c844034840d51302c00600300c2c0c1c1094610504082c8280c100c41c12550240c64401085003544001030722603030040e031088455600402c40f040070803010b070058490131048051000c0c80f502e03041d2400b214a100d07602c1c0e903510840c045800284980307041c0d40301c1404080c9259900b92a031100b4074010751503034050f004004080c4911b000b40404a108402228169500c12904074101019160030b00040c1002401740010b01051801070075030110104080e10041c03001c2000070034100308202b569030440705800000100703242d04410414090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 912824784 1250 912823534 912823577
    0xf0d05040e040f061a040b0d050c090a02070b0112060e07050906120115030602040e13051203070e22061e0303050c25091d0a0b0601020a0804030b16 65
    0x1a9018501105981e590b8584036031000140f8200500316854503a400c58100c460301c6403101c80c0f2000303440401050884004000c2003000584004210750f001c5124460107091400c10150000d00340340000d8204800317556045081c2c00e090b081800d010013008a411300b0b000302c502a846001043c0d0010384942030030b1001003004900c0c01440d6500400003034a0704860b0040c250701000b0050880183d008005880345024800b071747c494455021400c3c8080046104901803103c49000aa8080000c1c8011604480c200b91a50401030041c6e060180d10842015141c171040c0c20889144058100302c840c0c4035440441008607501d40c2c00447d100401500040702c1101d03072038900d030306903501410b0450312095195100c62404100a50a4190004120505503005480e11814080c2c0344401340a00544c0450250310303103090310056010b4443d6100c0e000031408180141c4550741c0002040c07042c2d40b9860740644442c0d030198030503842200d400070b03074808121813513031603c29400310b210161030040718407000165000302d80c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 912826034 1250 912824784 912824789
    0x60f1807050c03070c0902041706070c03080c09100c02090a27050c0a06090504060504110d0507110a0f050c0906030d0e2103090109090b060706180602070b090f0d0504 73
    0x6004000914006000b02042030b82c200715840001216226110b0300640701a400038414248061860687d00c0c64440011030980c1c8240510350f900c240309040d586084032440005030507130058060800c043c0600ba2074440b8001d0041e000754954416240482c8188842c01c60020015038040e07240c550322004108030941080b0100401d180340d05068072190a0041c00c00768005131140c0e0103c2c00c5940080d807550015406421100129000c100b21507684d4107110a503812040c2810002104208880d84d086003644041c4e0408002e00d4400781141d103549070b092800c40a0041510100540288441000410080d0040c07040c8140c0e0320303042508154000c02d035210212032030b4a09100c070b402d40c450016150707040300642da01403484102d91201600d00040e0346a9010700c004500044000c0c9010130304410714014030b00410740262505140121a80362400109405110003848241a4201c5004507215001a00c103244c029a0765100034100341d0781080c6041005102d40086030403070801041c4442d04882902c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 912827284 1250 912826034 912826037
    0x105030d0c02120106060c0b01090c08040609032a1e1101050a11030708031e1b181201020909090a03050901110c030709050a0c0212093303060f1807 65
    0x100d408203480022810021100b9601c03042d0311741070000802c00e81c1300780300148150060900c0e59540e621119100152490980307150041070708000414000342513a07228056460113854040100c02c3c2d0898840c003010641100240003200d0107194005000f540c2900f0820b500085032001c80d0740c10144d032034145845203160650f060000c0802d5550400e8002e50481d04d10721207600685c1e5a442c4140f801444903001621400074280802d0b02c01031031808480741850148400c0b107006020b0119101c54030070244d0100c42c01d443d10080654070b241c0c841d25880d070b00100c0310801c0c1d8002351b12459088140b100c64a0010642c501a82c0a0301007000425080022075001c2c10702868030b40865005030000c103162441e0070311000d030036119103000082c1218880d031250740114440d04050042c00203900040b03a0301e0302c0d0782c3c2c0180d862500400840101e850100e85100c001200514017a641d1645004072101e02600c1d98014003020000004000c00d0b460111414001203000312141d040700b00e101e02124403013a07001800e580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 912828534 1250 912827284 912827297
    0xc04080114240a030c0305060708060d0c09020f040f090c0f051c0b0406031e201f1e02030301290a030e010e03342d020d0302010b090a050105030d 64
    0x22480d02c807080f0b508050754000300c0d549120380c1d60746021903541208036100c00000e129000482c005140c5510301e2070b030117a00b00701c044042c2800c04003032800139400134100d003c0c040030401000075808003140d891b60007401c1e070303020010349051290006028034103072505240c2000b40410940b000900c6440007898060000900001d0b42400d54010900910721900080d0910f40321250300518013041d0000c0c003610f0740c403804130301d1065001249035512046d4442603542c0d00c2190034620340101030301c10204030307040c0c0c1c0a85042c1c400385040d5803580714603d40001e882e90046c0c10020040c00411012030000c403c0010111103950582010003000040f0301807400568201500d072800048104025004602111000001d69644002592500340d4180714012801c0d9015801203591812750300410708540295041096140911a02c0301c1c11088810030b103c0c035400000da1341440c3e0016865a140c4074640750711a13000007400320704a6040080c6003030000c09140d011401c24006100c9500d010801015000103800d080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 912829784 1250 912828534 912828601
    0x6080a0e031e0c0106060e030c131103011d0106051603050307030b0a2306031005010809030403120503091908090144220209090102120c04080114 64
    0x18250301c40c91041220442c481c100e80b6600414041c020045070401c00000c03c86103030356000a54100c2060495942e064000e41d00c18003542c01d0040d4060901c1e81100c0e400140750622581254854100785c011480d010410034201054004940400740504400e092507414054080c082201003048950020704105011000c0760310503000b600700c01400701c00104141e40213038484600b020b46490754a204d41d00071506142ea282c4030b04051044901441c0d002596a00d064103140041d5100c0038045c260a0061104000000201d500c9095880b80d2152907030f62541e81e0300b080c524103072030b102c9180402020250b9030900080020300c05030841d843c480c0203007401c2c80c0500d821500348240340304070340c0703510f0301200d03404001200303804114001101c9009aa0141c080b503119039011015420401c2c80e9022070000d031001c03d901600e4005400343e400464100098070300310403c6035401418105540102c40c803840802e091000312020b00030080785522040001c0c2c0c140c0f43ca401d40d225801c0c141c000743c81089401c51201c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 912831034 1250 912829784 912829811
    0x91011060a18060e1903050d060914041103120d150506090108011404060b0c0601150908060135060114010f0203030a05040203030423010e040902012102130e0405060c030106080a 78
    0x1e0340d941c22008172820010190305010b0f1140d40403001611310704e4589100442c280c0500e114440900c405158085003a41e20780d528a03501b04604010241d05218401c040c6000d0f411030001007200300d004800100e14003681001d070f030b00300c1003150b0000d6100c0c000602000c041a47c2c081c1000d41118052001079480b04003e00100d0000c0c0401e4201c1e02d68040e000582c5551400300003103081c103e07039240018060030070000ca0121001d502d5405548442d4000340c0c010070203400760b01903041c1c408030080041180042a1b54015404440003070380710f0b40c6608040c004000039109011481000d40d800c1c00c11400300ca22600c0020348034070008125803015588c81000c00d00b551410416107003d41803000c1e40071501580c9840b140780c0038001c40341050010354108199201824a07000303110500d581a150380c101c4007034807405510b020f015039901c03500a9230300b032103040400101c2e805940001c1c24142c15500880c1004e08240d1304141c401002c10540c1c1500300010010142d1041d0526401014070800103010f00d1503214 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 912832284 1250 912831034 912831043
    0x2060a0b010e06070c080705100504030f02011202041203030c1b03031e38090403030f090b0c04060206090307051f020c0106060e011205100b0708091011060a18060e 72
    0x3900501c1c0132440100708207040668030141c600200884d00f02c030b50b81d08200186c4001c00e03051800003810500003080000c000102e8084c0d104c0c4141040030114141030b40b9001240c200b544200400034035100100c09168140c41944024a81e41c90200c81503070704002c140c14204159400101019034034091300c01e40820700024000c0d03d00c10044140240203d5880c01800d51440f07400181e1049510382034501c080c41036890501c00036501070201049541c647c4c40a40003003030007005078035100d0340720450040060784107500144150243d0909940b128140400245008401010065254030411040d0041280081d40001c0c082d020500d07465005d01d041d1380900a03000740107602c0001d44c00c0440202d08950020220380c0d5200d0207a1716425100c85403080141604d030705031940b03c044140e0003820300840704070f0001449642c3c080c08045151000d0b160115079051021120480040c2e203844503595104800c0c0001504520b00043c144081c601a9442e03000004520038000e011030b640307403044c02d2407240910 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 912833534 1250 912832284 912832307
    0xf01050910090e0c0301030c1818060507020c0607020d061805060a0902103212010f090e0d05040605160609030905210a1104060f0306091b0602060a0b01 67
    0x7000c105030712030099000b500d210150300402d840c0f10b0b0814002100c26400206490407242c20810f088a00c0c3c1c43d112580782c101c003c2480c0600225120b80c00216481c0d040c070380170041d15201e40b100140c1c918103000000c2c1030a2529007040d10404082000c0d20150b950041e80b2074666410140004524544811800081043c09001460ba005203000c2121081c01c9078481d4108078000d8079070714021100c3d040c040702d030403000140c814052900b446109004c1204145000c03600110100c040b807420440200300500340d9001d80c0b01e1005c200d841007040c00f80c1001800703020440854003005015180110b8800750a500071806800104440031600300399008041a003c0b8407250003481c03c02c0080e10904000303101c40c0f914080c3d03e000b0039201028028045802100088964840f0054020429240e59404084620101840d80646c8680e00464001d04410850009501c03c0d08001a040028a130040400ba035400f8407661035120410100038441d004504264072104102c800039a0503030742d100580304904d221 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 912834784 1250 912833534 912833539
    0xa0803071104200415050a0f0804030e0d0606080118080f090d020604030f0b072c0a090c020a12030908031f0b04060c14060114060c03040819110405060f0f010509 71
    0x41085003603c0ca6000040c0181c4894041c06502c102c0e07110010b42e020300c1120b0544d40000c0c00442130440142c032a9254540042c42840c04107840078910001500d9420b80b42c905a503c00c0c0d8070101006982424884e000d1017001d44010104c09403425140c107000b500070704000b03c0c011040002d8041c585c1e9640640340900c0b6500078461521561241040a5940c0c0000421100352001001107509140501c3d0001291103221041000e0b145c11000810500d4100c039100c5034004201c1c50002c034030410503001c0c1099000340c0e5401058a484603050601c0c41803480307820401070510344442d14010034001c0b411a903000c2402002034a1801094801900000d40d590041c03a0380040450041071603684407440381c00650088049503211f814001c07080703807541c03801c0c81642c229410080e90317010703181400030240400c1c20410003524102641e0710f6400d810541484980038800e407603808941d040000c1c1422038040403506a40821075032030300401191040707841c103a40c2441030b10220581a07490384950212420351602 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 912836034 1250 912834784 912834821
    0x80d080910060e07301e09030c02090a02070809210109150b040608060103020d151a040e06090c0105090a03020a090608060702190602450a0803071104 66
    0x10388681c515201c0083d84c513000045c1c0030f041300140300d10030f10042c0c071142d01020a040d003169000500000003082d00043c0c0c845000041610402d00d4285031103500a0f4601949130482050310030702c1000742c2e09000401242d00d5900c10300000300480c0303402040c0c601c44581605c0000c4490303800381100b00704038995000d200c0d6960170301c0404410060814103d103d511a9102b0501218521004110030b6407094002d008159104074010009480d0130070909040d140a801240c030700c0903800040030f00b41d50a000c00010710440c0002401a6820540714450000d08007401078010750920b43e143c50f0310b40e241075242034104000820950790030740e0b4030400075004640c01080f582900d5600d40c407101c05008148034101081c0100800540e42a001041a2000005000421542c036195a58083c02500192030001c0400750465103054400c0f0300c503030101216082a441c012200803920f0340d1980082021581500a00890b00c0c00c2001e140008156006943d10501290b081403002c2c000c0303030040442d42107886040c6503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 912837284 1250 912836034 912836039
    0x608062e0806151009080615010c021009080c0d050a030e0102010204211205070b071202040b0d0209091510083402100504150c140f0d0501050a080d08091006 69
    0xd424814244821042c0c4e4100074002907504240c401d00c1540c07186003004d0704158002901c80c10034110329808560141021441c07e0350a4000c070702c10002c00b801083c00700d080c400090002620400090019500c00c5542c940d41c06c03004e03650b254494241c0c080007414003c00700002030060b8000c0d01035801501c000c0c0551b860089105001c02d122030340000c400d80e14121900380300f001681c815412180051b422650301c0b81a91070300281110110996410303200f05941c2403001180101c0b800d0000c00c0c03064100500942c0f1072000360104404064054142e1442400684031000c0b02c0e00e03007a0203546100350340e0900e07640c1e83e0f603200410858080b0310f40110b0041c00a905003500c07401140c4140c0d443c1540346608451804c03c40150031011070b1420303600a812848400c1c4408403041c0b041c4c2050384004110b241c00040c1d62890210100036411102128145000c08a0726280c002300074400c403401444100c84203442c0d00c0c980000b0603242c0c481003004900308800480012200d15040000c8a0f1031414407034100050b69 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 912838534 1250 912837284 912837301
    0xc0501050a0b1c0b060d24050a0b0d0c0b0702060c06010806091b01200f07030809030c04090240150509150112090b01080a02040608062e0806 62
    0x14402d1580c078402d40b461003d0100c40a249400d484403181e226020050a80f203100811003148410302d02256010700340d411203180d003c4140900b030721ba100740200104143c104640311100f5100c2c402641c5000d966524005c1010524100e00750b01114403134500349030b6600d814004501d02d4805c00403440c02a2161900010721184005040b510420642044d00c02d01c3c440301700e480c1c5c03141d10039000950000c0d0601da100403010300e40d00a01000304405400711340001801c242c07a64180020381e44140c8540b42c0101e92440d86083c14013103000b01c20303021601000901e403181e0004000354005844076800102c0f02411180c00e40100705072112403050344440d44011501691800d01602042550107020381442c50000fa090400d803803018050fa030b5400c61358006a62030001104e201c45010003030340146440d004080081012651014060883d80010309460031250050200391511035010907002d80c032500c20410b0300c0300d01d5007a403688070780d014141e138004176500041845645c1c22901700350030f00d004e89004e200a0b403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 912839784 1250 912838534 912838541
    0x30605040c0302100801080a0221060708070f0c02010c0620070b0627072703080409181a0403020705040e0a050f0601050a170304090c09060e040b0a030b070c0501050a 73
    0xca10850300d285070310f4021310084813221820300c03e0aa00e80d01100d00280140780540740e008000840c0703550711400e041e410242518000083c1ca80101154401040c00062503001001d00c00c02205400c0025108185038002490301082c040094800c660f240407480c1c003407020782034a207011000c0b0814251102980d007002200c1c80000e44080c6d2042ca15441d81c0000300c2e46626a45443e1200311503c20496a111681600c2c11013407607110060103004400f00100b41e09044140300c0240d4042c04c1d1054a4504084036001154261241c81207103c0075520b0070800240405400000c0c90901c4000300300ca40c555284c141c0c5004202c2c2c0100741d2003400c040b81030845085c00140130403894010021220440d01e00b00310203883d0700b402e014094020742c10800a0014128840c4d4070001155460304403407505a07036207440001c8070300f4180340038009100c4d40010060150300455420030a8070444080007900480c10028902c15074900c0000c00b240b034418009115203000e104107031070058014000780f005141001480009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 912841034 1250 912839784 912839789
    0x908070203060c0a080f0c0304030309020d170703180b041e030611030a0b0f030d0e0a0302030307030c050f011b030504030e1f0201200d1107080a0818010216060510030605040c 77
    0x200500e00140600d2158805c01f070041001c60342803480e540b21761700d00310090100c9030380698000e50071081d5500029100500c0c2d64188820800481c1c40d0303a5940340003024103412950084942051080c1881810105002c8600304c0c0c00d086d141c070201b2040f4841903a80301d0400d6001400d114600210110001d0920005600c039001c200d03c108204500401000140141d510070030350903600030900702c812217009001e5401403400041206080c5a43c03580040d24550000408500150355040e5200800ca0104142c19484503440f00074003401c88130002488202542c444101c04054070360380807030281401120803c0003002c014000c11803c0140380810a042c0480c2e0b01342400541c0303841c030103402ca2500c40f0401504070413800300c01490040740000b81e101620f400c90b40c900907014100301c1000015074500040c25a1081910741d01018070306000d028400c004496034038400e40e4010001c0050014204203484510703684180700081d9038440210302d00207100c1c103400c02060746190100b0701040c051500444404c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 912842284 1250 912841034 912841037
    0x20910210f05060411120604020f130306020c0d09150807170a290a0b131806230924040e01021e1615020906161416090908070203060c0a 60
    0x350800d000c06800725104000c06c4016408190012403a03030320305078000f81241d0481c9411181844101140c40d01c0c0c2c040c1c298801c031078aa50006119140380c1060025905000c901d0520078601c501c1c0c01c2d000c00c0a0b581c5a481c0000b041107010000d55028015411185c40c0e0086000c688018940488a40020170340c0030000d44443c4260300031441031665000500d91981c60251043c0d004034038100100003a90001868880301d9483d00c1c0380802c909a0411400081c26000100811a507103851845201d0700d030350030f84900c880f00c0720000300c1c2c1080e21180b49942c0c1200c6a00b90b115402d000303910180700031181800e190b580c803a0401c95100b507134200540140403c402c2c42000c0b54045a0000c0031722455200302004c0c215159003051910303000c210005442607030303020141d40c00761030a4481c000003815641b001c0890022801042144c0041c030a12103403442100034420018030041c0c2281207020701e50341c8680308030025151103c01400800c0092025126240d038003400b15406820003600c1205240c114041110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 912843534 1250 912842284 912842291
    0x90e1302030f0d0c061802030102070305040e09071a0a1e09091107020102150403020c0406180e28020f130605030d020a110405070509031506040f020910210f050604 72
    0x1502c500401c6418225649485000c0f0b41026076407020090006c4400500d20801c0f407202440c09600d0a00060152078400e030740c2d00c1e950710f040008403501e1500c0030b4006262984814414000e4050b00a041541140880309094603a120050101d56440403140780080010846204403161508441c0c4031090341c410900500680c146256659468010060040d00690041010002006101181680250091040d1a600702001002c2001c0c3c0e0601d034001000d2494082c585411000345114400b0725020748006410a0100d42085420036541e514110700340351941d40890b0215030f115400d0190326600600540500d0941d00064070041006100316800f0707024a0882e001001d201103140104940d1181d0403009050203842804000c2400801403030611404110840030782ea420824190700315100c0041c000d46181c080180800e031041e10308003d0075a4010301800140e603950308002c0001d0b80392071900c0380b49059000001840c8505100107c49014545206109144a960825803084000b600c050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 912844784 1250 912843534 912843553
    0x1c0207200f09090607080414010504200306070c060b030708010e060406180c0306020d0b04140406060501050403080304020909120a0f2006130203010605040c0201021804020a0210020901090e130203 86
    0x8855450222110340e20f5030046400183c003940250140b80d0854000c9a03008138209810303203040e003155401c0d034044d103451243e00c526126420255100001a5400f940901024181114060038280b100d000061040d0b480701c01c81000c6860130003041c00288078100081c0201d0509002c40f54a4220546003a980b29060981c40c070b101e030107102e03841e001490b801441490708a185440d4a40250401c50307071905e6064468403584d1560341c0d20302820a00c0a010450070b490760034507141c1203040b941e1580c846814031106102c2040030030020340949034002c0d010744010000383d0390f4107032940c00d04101401c0728000c80404901c1d40f080943c0301c643c101000b40252950386201c5d0041c120517801d14528140000260300000000e03203c4d00041107052074252010700041940c644860008082da0420014500142c0d80841c1c800304000e01582c040096402c252070031840c001109070029110322010700032209039500041c282a1030303441442000010030203422600c0e410300342044006641002440c06a11034070445648 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 912846034 1250 912844784 912844789
    0x9032409030304020603150307050d050d0207090626010204030b1f050d020a03030c0203120301080c1327080c06101502010e0d0c02010216060e1c03051c0207200f 71
    0x880340291340041620f03055580e005034051300c0d000202e40660300360140c420b001030705071942070001c001548580301401e040e20112000900c0d1902036032100340c459041030810009048006c1d841c6a81c1c2010550f66001201440800303406881160301c010705140d140400c018805950280303040c1d06070065a071084515940b07004002004580d1031029500521240017080064000c070b104a81c103601c0a003d4580c0c040d01051301000f56007090303001050541000380040a585050900c05032076000410b020000c0840c2d9907a0250a051030302e1003040c442c07410f0024141889407031426034035640c10301e0003280d19a1034001c41d240c1c001c5a030741c41049a02410080ca280e651030043c000c0b56010f100c10300003826600b100b194200d84480b0f650005a055002c0c4032048100f482c94a0b42c01006070a090300c0b4002040011401e210b0503085070780803000c2044525400301c0000b03a005080300c4080c0030070b0000350200c00928400d040244a0000010f00c028100202140c3c20200c2810002c0d45e400d041b0756207149052071109 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 912847284 1250 912846034 912846037
    0x3090e070f1202030402040b030a030914010206040b0f13060903050d1a0f040b04110c010c09050919020f09091611031e0a020109020a0305100f0c051902030903240903 73
    0xc0800301c0d496048082909602e54095980540001d001180464071700000c28102440c0b841c094000860444007848401c3d5625225030f101ca0080c8000c00481ca450b0300c0d2041c113080090f000480450030140030604030002500600c82460b00010200210030f001d20b400b8101e540703c11601503c15040c40c03443c030700309034541c41410111400602401004aa26010000244144d41b500d641c400d5503040c400d2031f425580c00191801d95904000040c82c1d1140b4030300070305032403000c1e40001d200c0c0c10520204030b200c04103000d00561890a0440140e1101407a100351901c60241c04907103904130607068204440c50050325104045542c9640b901c26a20070300d1400315807a0f00c80c00c4450f0307294203204298038030b0320001c0360024004000d852000103a03030030080d400507403c40c500c0d5109444540c40380c00100c0c01c2580031700c03c2c14620304c4910401c01040190300c002500900850300344900323608041d200340400030f0083c400c803801e030000101640c0b0f00c00e44c041c118807800044206002604101c2c4400140c14810010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 912848534 1250 912847284 912847307
    0xa0506010504050105060d0f02040b163008090304030f150e07060509091f15030b01030204050d021311030c0c010f0225080705061503060609191a0d03090e07 69
    0x45c00c86e458030034100b001f18083c0a520100c0c3e041c040e401c200001d00c04c00084094190045050588954080d0a0801d02c40840b815400e440d030076602c0f05502000307682000185004043c01e410841a83e039260b649850950049a00260041341c1c601042e070b00f00280d00c1440d6144400e20001045000702c4a01c3d100c0d92414180610f03400b1403800c0046000d240303000d1100513840755401d040707044000045001c8042600c0d460740700800b101038007410258165010f0007242120403080c6021401c042c80c14000410000c288003001c0c1c0a4031602d801c5440c0c40300703240c000c3d00c0001032403801160303a420600c1340c440340ca9210703445821722035103804031214107602e0a00840d1a0900c01100c1010030100001e1141d00c0c140209204076424002004001c3c0010028060a8480c1055181c0a4060b41140045c5801c000f07004218521900750320b4100a202403480c0b00741010388464000c0000c1d582d0180c4014841401000d030380f968080040c40c5503600705680f080750241034411401000c50701344c86400f003e444410091 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 912849784 1250 912848534 912848539
    0xf090e01061404030f05010608061503030318031201140a05010507050c061308060c0702011b02150d0212091606110c1c02090f06040e0703051207030e03030c0a0506010504050105 78
    0x850040025500c9400000700080e601ea81c9546807903035980c0d602d0001811050119402c3c5d4444004120002d41401302c01d034840c0c7d001940c044807084142c0000c2d106c0c403008204005646102011000e207110400c251258490918843d80140d41c40d01e54441c031358000741101c584900b00243c40412954412401d844025910600914a00c801d546c1005469044203000b100961070510000403040300c10454940103662041c401e1341d440703100f8000100307a01c048030b526980b480e0301520303980c0058951014500d0300031002514140c0346c4043c21b00d260b01901c28481c61041542c06882070058005000c01c90504e070994142403480d50507920382d01540c00c4200701c0011901138118280d00a03007400d0041d0400885a201d030130f081c03090f512581c00240903003010f0740c084956004d00c000700a81030405104480007446210014810580380d56500e0b9501c80229840669241021030f03040e04042c0601c42c0301c80e2a0b41c000b01500c0d03c501c02040c1c0913a441e50035950a039103038402c03071000054504117442118181c0d10702 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 912851034 1250 912849784 912849809
    0x603011a0319080903030f0a18060f5901021c0302040f0b1306082208040504050c030f100e060d1b06020a02130c0903020909010e0a030504060f09 64
    0x140c050b0072003078031004101501c881c2c004204041655805000070092000d0b9000c6580c4ca92107940ca0013010800145015040c1e00d203155814803c458010040107010000c0b840c0c281c000050384080d40200103400042030040e55102c4402030705a4100842c201c85000f0712480b03031540340581940306d85d20070800c003240d5409a000f140c4040341804035842c2100007460a41405890583d0300c0131100030490b499809510030a00c08212500d140c841c0300b15140041c1070340d01e00707290f03142000065060700ca2070405c01c800321442c2840200c030070051a0010b4038003c0c01300420411240c43c0c030182d1460340f613200b00d5034a4a503006480004100f8030070f03904010141c07811155010b045984440600511526084041d912184540c084680b080d2600400ca4003403d03060340a404061528414085540e100c108920300b942d040492070340d4a90340c0848018112078048400002940b1038264540c0184075948c2e0040907802042c1c9000d00703144e0003030024012038049503a40c080d6030b42e40030001c460108040c0201c070703d090742 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 912852284 1250 912851034 912851053
    0xb030709410c0c0a080301090509060f010b030c2a01020301050a080601060e040218030105070504090f0b0303070f1502130510030216021311040e0a150311090406230603011a03 77
    0x1c80301601d40d40303d0180448051071507a4850400d50b41003640141d1215444408209103031800b03124060b00b07c9803c100b07035130141d41024980941030000a003000381c824008502e05810810f40c044d401d070070000400d643d030401c030905072200340070f035100b405a02c0c0644500400010281c000050190407502c003a80c070000030300d150b1030810019602c81c0c0c80c44910b060340d10703070300d55035a035070030721a00d40600303034584400355035614004450068070304c080380c410004d034071307218040100d520003008580180740e0041d0640b2094501e0300c0c20359000f00d03465180f294041d10104103113500c0c1c4601d414110981e04100d070308524034042c1042c101c00307078480d41104018521545219400601300700f10307031641c02e401c0d809000c0f5401c0e000155542080d0403540c00900b103c0700304030034000c500c0c081e4403650142081220000305042d05544403a5840c803a1280c155006040c080c000405010f550390001141040c034000c003900038440c0312010500d40710140c950360700c01c0d480c000e80d06800c1c0c02511103805c90520082c01030403072100e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 912853534 1250 912852284 912852301
    0x201080604020c010216232104031703061903080a0c02220209092a13090c0e0916140c031e04150912060b03070941 51
    0x184098511500140c00f0700020011050a00152044501428403901c50300c41a041200788119040c452107c0c5004402d410030042002007a0783e40c00e800c0340d09a02e4018401c0c24840c2540c0d10443c1e10160a1808040e10043c403440d17504011800781e41c046489045200220049400b442c2142c400145940b00411400da4018000c8094013a020b0008250319203101803007085400e040c0d848180c202000d40c3c00504840c6d240b52280001381c029072420b541e8408022258010001e07a903c5040e08925440045076000b06030480d401d0100c098020b144007842550b001e0030000d840c408e11012100c1c403d400000001e0721201d4807a000301101c8005907070b8900c0c4042901141003555101c942c01c40d1442c00704000c20071842900c003080c000c0c00440840c00d550b44916001000010303042407504d6000b0000c96070710821444030300c0b8001220b40342c2c1000300002c1c81541407002a14000d040d911002680741816004540b0036036054029100038409031540f4910b9a5840f40c4034001c8402c041010702010444c1e011401d0718 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 912854784 1250 912853534 912853547
    0x807171005041505130c080a05060f060304210c03110c03030a1b020a0e04050601060c03080f091507120c02030f04090506210304150e030c270406020406180605070201 73
    0x40f41c0c2103d151010b9480d80302164a20602410f060001d94980da00059010791003120079a014070308010801590070300c04000351003102c403c00e00d64171030103010010a061200715442d400310301c004407983d50b541c1d4080c010042c183c20300314541900030904130a00d0000c0302801042150030741c03000030060741c0b0f00441d40b803054400012800c0c49101d074151007004180180c49030b40c2c00402074a050041702d40a454a454910b1803d01d050300404100400303503204100080c0c000c1c0c515908241019004038450303607580e400a00e008030101543c0c030740011003802e0104882d04650445c5010172541000e0180d4601c911090741d0324418048141d031032010420003000054480d50080d80c101d0402002848107010f04109550501c1d056003890006403c00207082000d244002c00d10680b546081c240400000c0d01140040d484000c15020f02e4007410040580c0341d00065025103480d0880a035480c3e550a506260070000000d4015000d620042403807003850101c0004200900821200075544584c5803008583c011a5007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 912856034 1250 912854784 912854801
    0x912030703060e0c03101707180902031504030806040b1f14030c0d1a090f070201020c0a0302030c011505150c0a0c0e07080f01051c11040507080717100504 68
    0x4160782d039500480c94614449003c0d0148010a00254990400303e02ca94075681c0381d81c1c80910705030203240c428440d6100c0450f290084030400010705000d01662038568014045402001394180207207140740038240c0d0405800e07400b960180d07030b1f80340441d946c00c428401211039007031509a02c48450700d0365140c02c2110019800e80c060035440c2c8000c1c9041c41c07000320900c5801c2a560304103980c03001305007000b00300c00340d01c10044654910494000d40503050804154503040141c8680180880d07240018540c034002d404030740018165004484203c149400d00070340f03941100a1800942d401c1c000b21102e12000004004181c1c0c50045c03019500c00c00310422204540d100c14070044050241311102c40200d00c258201c14002c5c0091844c00c001e5140c100c10003401100010002e0140001c05401480191100562101070612114100c080c0107400e0410225080700c0764551a8001e0a050400038200d50205110b8010002c0ea00c03101d515009a00f8480088541203880301148091030300304010902e03154010000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 912857284 1250 912856034 912856037
    0x220f060e09150a03121716230d230c1603020c090a020307110601140f060d1d0f01021c1128020f0f06040b06150a12050c0309120307 58
    0x6198803510103d035440e00700d607005407101020000c0b1550010303081501518920020003640800c0d1411181000703880d01c03510700d000c3c10409001340d203040b040f864045054440744034610650f11620702c00d5a0402a1195840181402544804150382140b41c5c21545000d00360300700c00f031802e240c6284203004104814041c182e0862080060703289207500c41d0311609021b000e80c0980942d50346450b0b0400342c43c0d50600c04002c540d40d442840100503902d0803428482c2600790482d0070360880461080021442d0080012035034003589480c1014081d4058103000303151101c2c2e280151030403400303201c12007800c038044c1e0422038201d203c0c0799600560100450b4840a0b201e8281c0008500300b5a03c1e400e020258013540c1186050306c0400c8844002c2c3d00e40400c40c0c401e991601c0001400070340c500f02030040d1507140151005211f80c03105000f107102e503a10a224280707826481d8000903210303010408014190801c400300001e204c1d1405000c60841c282c0101100e00c01c004207001000380c1c40e0038514112a6a02c004c1c240e10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 912858534 1250 912857284 912857311
    0x206090d0b07120c0f0906030509011e0c0201051b04090213080604030210050105031207080306041e0504150207110d111009080d0503070915030b0402220f060e09 71
    0x441ca00340d05030080b50340d961640400c6040c070308030f0000c0f641949505010320a81c4172215a010b5072150105003030301c04520340480d5507201c480c6010302400f02a83c1c054a040000d10f158800b44a4541c4800318504032580248016210403240c4000012140f20b000044c1500300401c0c0b2002003076400910f182207814a89660403503480f056607081c0780e03044d2021001604070030b1060440c241d8600405000d004110050a056000c1142c041801d2103410002030640c5004400190180e4940d48050b0b0310b001251081841c68005042e880001e1404079411101c1010700c41c0c004160400a100b03880d41181e00903d8030440150bc0c404124028001c080100c2d010705e140380400c1c4283d1200407040c41502501e883d00448242002c140030b007410f0101085008010741401000b24041d40803865034101d400701d00c00155000c01c0c0780400c40c06801c01c010715a0b0404c0c0001000300040d21035001c8141307110201180880c01c40e861f00c441c1c5002081c07520400c000140e40342c042c049103243c1851241e40001900a404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 912859784 1250 912858534 912858559
    0x30507170f0702041505100806040612080406090f03110904050c130c090905060901120f020607030806040b0102070302010f1413030302070501021009053310180e0703020609 76
    0x80640d03020502031030803a00046440000c40c2000d0158100360080254a40704460074040032510b003054a0008104000006c8c010a000f40c58a82c41240540517483d03006006140074248040154020711a0000040c85000b000518401c851410383c02d880d03114110300014420319040280294002d841a1400c3c00780540b111701e82e550b5201c000000d91100c200c0031035000242c0002034881c000b02c5e800200054108400c21180e41c5c2e81109480c1520200c80c107109011034a410602c43c844030501c0029004100054884241500281228800c0c81c04440612a4044142c01280c507000c41c1d110090208056102d2038802e140600c0ca02c2e9004030b03140514078140016091400090000c079070094001d0303040004140070031b50f4180000c0d4a05102c0c2c0c0801c2c0064509a40d441da5a01840c0d030700d4180c0304000f08088034040c070410721056040410700c3c991480c542011807004207522340038402c8104180b00300d90301e650714800358000d08143c40030030409032055134036540034000554802d40d070040c1e2012001110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 912861034 1250 912859784 912859823
    0xa0b0405090c030f1b041808030a09063903020d111806070809060f071a060102061812090312030703020d060b040b07060f020423031006050d030507 65
    0x202440752000300001d0505030410014182000002d42e80b1000c6500020a4000c44450390b9504904050060303400290302c0340002c00c00c0003140802e400050084900100f8003400c0c101a4000710111401000c081047c1b904034402112038529008a000c0d82d44140b00300c81080590a2005109400e490b0074050301e00036a410003001120701e201c0c0e60b40c40c0040041444040b200d03000c2e5050511703004c2582c00d6403400c1125280e54245000b03010210b03100b810300040c43e040021890703040c3c501d0140e10000042c2a41c2c400500e400b06038000b15040ca006200f0f007000914500c90300d9807060542c10b40c50f8003401d08420301c07090400c540d13840900c5107a014800d00100c801500800c01c0118821707900da60300140c49410801c4110b007a1143d542c84091040400d10090014003414012942600c0d40624005001280c00300e5801c00b9000315400b543c002108005060701100482090301146007080301a100e40340e601c01100f8045660074001c194120f2840c40341100003901500041000502803052801d0301c1d0881040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 912862284 1250 912861034 912861041
    0xd0c0b0601032408030d1107051b01030f051303020c040c0c0b0c16030216080102040506030a020d06080d0201020d0e010510060c051c03230c1c09050d030504020102060112050c01080a0b04 82
    0x2030300e40d40f0015811b202a18503200e407050340d004465855203040c100e0b85400da658804840000030f0320340d00c1c20200c41143e001350301850080b00c0c4c194042c8030600d0048071100c40024101d1080d009405800400402464036104040c1200240d454040d55000d894071011040358004000d5588544200907500c2081004880c0b101034511960040401c2010801d000c000c802c0e440c0e000d8803190380140414041c0f590b49100703580d44902c1590340143ca90f4002044072000c0c0107a43d002c0351003405001c500c0d41c80309034103400800344103040340010700203a080000101e088820403a003511450441c00c0052201502c9100aa80007a00800454104074810310340c030861a002980e000002c283da81820001044c1440365001124901c0c0c0c00b50003081c40c042500b03000610030850092200c284220320815010313810b80c4420b28a9030484201c0d0b421240103079000d0020502070b1000d0b40540301d802c00000d4584441d61007020450f13840780103084a802d0440040d0b409401c050300200d00b0350340700c10100a15440b20322 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 912863534 1250 912862284 912862289
    0x60f0c03071e020306240a0305060a06120b0103020603070c051b0114030709060e13140f060d030c080a0e03010c020715020d0203090d0825050d0c0b06010324 69
    0x1540d51902545803640d101c2c41002010351180d1040012500980d8001c83d002e540080501c095044c680081d286180c4400f507030308080341c4d00504114022007480800035041c0c0c403c3e83c82c02410000d098403002c0d03c1c2c5181e0b401440c020070030014a4014801400c0400c00380d6044201828904000c10b070740da40e81c40c100440104240c40303244071140d0280b00c03036034070103500c1052148801085143d07040118004155110900403038043c003081d80740300c1049841c1d2a000041c0303410350040800c055210940040704150f82540c03d04400003085001c19403e00d800e0120002555042d1a89180d490b810798070361000b500400400803d00280ca4510704281d00c00780944280d50710035901a0500c2810460401c20311640e45006404561103020148039440e0000103c80ea8107104940c2e0302224074640c601101580300303007403030301c400c40e8240c20a40707903480441c1c41c8090030180303d0360a0f2009a61501000c441d083c0007100041d05051001000c01c0c80c80d40603520103240020150060040c0ca240c4d112a140400103d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 912864784 1250 912863534 912863557
    0x120b031f180b040f0b0a1b0e03031e03100f050a0312031b021f0204060c080f0d0608060106020705090c0d0b0a17030c16060e12010b100f020610050a090209060f 70
    0x200d00740100066400b05c25404009868100858000c7c008030114003400300e0030070030a2101c0c41d0b260b06c41643c0c0801c20303904421088000c2c08407541a101d10700d01107030400d999051010005081c08900802c80079500c2003501c101800b2420301c20301c1d60715000803410048006405250f51402c0d14280c1d11024034500001248640041000c90701e5821803085c1d82400c488a12905803040c0809d1204d1544480310000c600d030410b4119490709003601c480304262180084801c0800e00c0e002000800c560b002c16124122070344c580940368507560b01c00031700803200341c01c0b140c030b00410030304010040e450f511a5028a0b043c0e64040c10740c40b42c442e124840900102690000141158004540792040d500208002c00b0b03200001e083c181000d0303240c50800f42030102c0010f1028410b0092020611003a13509501107034800c0c400a240d04443e001c03142000d408074000c0c40e9810010302441c00066001e11a4106400481d9400392050365001c0c54038403074600070740000082c3d5a02410400c08003030141c0340300015045400c0c14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 912866034 1250 912864784 912864803
    0xd0212031914090c18190b04090605011503090809041a09070518191502190804050a0605120106030e010b0604091a09010b0a051e0a120b031f180b04 65
    0x410786189040c03040c2e0780c80da220740c00b05207285c40c0789002c0304040c40e0000810100f50544401da80c0c0940c020b00038529800c0d4100785400c03241c2040c46400c2c1c01c11070403100c001039412507442ca400c40460070b94401c0d00018188100c100315100560038694048803585450071039070b01100c0d000388000b40d040310301a2034403400903801044001403500d100c16100300741a001ca800a0000d1030140000c6069059807288040700c2c7c0700125500e8042d40248200300070011120745a588003410703840c01005503005030203a240901c03440480031601c0d502800440380b000d0003d141000ca982c0c6003a908501410716079240001315501e0f9150002c0039103510028001605801c580822003034070300c00162108002134600d051244a2038070040182d00d071000c1c11120b5400040c40e08a03074a440001c040d40307000780391040c4100d4100b80003800383c03405940417164003094200284144000744513a010990f8030b640060621007040345480c0f200b40040701d9584250007000f8a500054580082138807451800c0b07404481c1511981c60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 912867284 1250 912866034 912866041
    0xc0a1e140105010513090b010308160b1003030e0f1c150212010504200711040b0a060e011e1b170c0d08010801020f090415030203011a0a080d0212031914 67
    0x1440200b030b010303901c4030717040401280b562601d401c0c02224040c84050612807000a40d46800310804003030446080d0040d031404028100b40d40b0721220690325100c15000507290210303803405442d20340f0f011080100010b082962a00307a02e40c407180c0c103001083e0308540c1400003e002c84038070a5140054034100e609400010595890701042c0410ba401700d4803a03140b07000d0001e03c8448003042c02000c0c0d07140683c00291400710800c1c2070012500800c4000300c080d60080b80f02c000068150391100085201c2c000a80e84e58007012103001a405900d01000c1500000c5203125190715410a0b400d242042200e01a0007010a18a1194030300181e5a00030350301188035400c90000d80100d02d0b08002ca403801171250f500210720740742d1030281c0c8000a0040002c0c8500c21900c8030350b0002c241500311103d02c081c0d034005008101e150200c0f2403900c00c20f548803200300d004800303c0c140044e84c4080800c00ca82244941c4c3c000d400b41048070009200a54001000d409411910010340403000000e445025480306601014515506 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 912868534 1250 912867284 912867289
    0xe0a1d07030b16170705090916110607050a030f020909091c0e030a060902010c05060c040f1d04030513080f01021e0c0706180e0c0702010e03030c0a1e1401050105 71
    0x2c40051100c8408400c030721141040da07511401100500001580403203c54071680002c46061240c6c3d503c49a00c40707000c0090040c4044244c04180103039009443daa00c10400704000141c0300e1000f1141c000210714184511a4400c1c000e41054400d510b0201700149840b80f1500050012002594603074025409016465030040138000000c1103900103080c0030810300080d0b03001030b6a0fa040031078000c00290310b07480f10b8002c59005540b040110341e80700c0d06540461424500101054002d0711030042000c4200b00c0000b11000440060f03465070ba00c034210b1500d65901d545003a201036002d00e4a0032490181c0300c2c0d000400400c18089410411a03d0300056581c080790a02c083d0140401300040510800800508104000001c1c44804a90180c1000408544120020860a49103500c402c42c030708460400c0001d282e01e804001e003c602e200340c03104400004404141a680d0169500412080e40611903803008240d0030842801840b6001c0b8008000c41c6099803040070040c880720300503000d0782d101d80040c002031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 912869784 1250 912868534 912868553
    0x638070203033001030b01060c08040e16030c0504181a06041409060109261f060f0b070206070b2701020307031a061c0204030c12060506190e0a1d0703 66
    0x48410203c14070307504580300c40c5010b06041c4582018401c580001c08100700548043e9002448034030a00c1115240942112030581240c03600400060f140841d2002c50724000c100f524181d072218160443c40500c1180c48100501d030440306043e4600000c04541015070311140108013406014108040b001c00e6401400113040000c0d0856041c0101c61074240128119840c0e41c4940b00518804c00c80c10a0b100d401c2d190600740301500b5805200c0481c200754028940325000b82c41143c508981102c0041d42d1038000c26118064180000e5001400b04204008108100043c0c0d81022110410541200380c11000e0315917103041b0f600c40520b603500130042020094051058220840e0035070510125032811070b002903d10300c203802c1100101c040300d2500c07242c0161a0360503070340615400303080506160303201c2284401103e00d90b00c08840140c10320002034080d04020b200c03400134944007031003480d90300d0608004540e1a132001f00041c41d440c0e590301d150051140c011902c1114001000b0180501c50b055040c20550f4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 912871034 1250 912869784 912869857
    0x2030c1e100507260c0706150f080309190501210e15060f120c190305060406060305160305030712180b04060f03020711190906090b04063807020303 65
    0x1c0300b44d0303001c108843c1a0f000480c0e84044d0b00440c00618802d00d4001062030001a401c0815510b89a600220740005c3c000020300303030034508032582c01c4110420141da00f40e042090081a00107401011a1351440d018240856203070840d07000701040d588603030000c0c0b074074180c200190b00d2040c074466810300681d400d20002c00c00c55a10140e85090043c1b0030710011035030311160100014010001c0c10310000303140d038140c56081c0245501c45e06440ba6414142008806840e990205076150b0140d1000c4104a0030ada40e0488122503019028504051498442c8408100c4407003108003448410400c4070041402da60055000c0c0c1058103507903494500b0820001c0041034100204001d1510400c008c501040e4580c0800803405000c03594210310981441140c001300d0303049c1c2e1140e1340c0c1c54140040494a1501a00100080902640c0030050b060b500c40d014244100020705100146e02c0800441ca00c0c5442c42d40070b2504140c0302c0d07425600c0c00c529039011900c0c50b80011000ca00703220100c6502c038100803000c0003032000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 912872284 1250 912871034 912871097
    0x11b1e021e0d1502070f0f050106081c050d020d18050f160302090411120105150913030806010201020c030f0909150a0909151b08010602030c1e100507 66
    0x3244003510002c0307808866501800b901c0000340c08031074076030001903070110307000c0c43c2e07021803201d411901514200e00c4003402000201e5980d42040c0300450010000140307001c01c82c21f1029002100c0c0e20608082c2d980d540328071035200342182c003003102d81444040ba0054185d002201420b42e08901c1c1141890780c284103000c564002540c100920741041130040c81c0401050300d80454140000b80c0711403070920103075409100c1594215400880c3d8030079020040d488240710f0450340011040c000c088404000c0c481c6800c4484001200c001ea003600042446074404941c8020b06000051420406500c1a40b442d0010800d0140220000801e4240c3e0704000c44041c1c0c0107410300444001c00100070340001c500e80307018040c181078640e42d50340510900c15412110708461802000800c500800c4982c10140c0c10708000040001c00c07030701000080d00303a00c00421964040444d0300944600d2900c106c40050f5080c10200c4080705c0e220303507411950107819510400303000c1c044a45039550940d203504210240510131811000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 912873534 1250 912872284 912872329
    0x1e0c0207051323012303060c030c0307020106030209180106080102040b070f06060911040509161e090302040c03021b0304060c03080415110301050f0d020a05011b1e02 73
    0x41d2140c1e18011640794040002040600b001d0302400f8521144a4011503040c100d10300010726002400d159001400b407810040100004540915a903040181c40d001a500d40400008100300c60000203950004120310004c00c4079981ea170000340800c00d01380c80038080035030030703003030070800c0301070900c206d1f0010200c0314001d6040c14074002c0034032000d0041000203041203c5110884080100c1e6a04c441d01420740c102d4100004e40b200310456240390014000c190051200402149a440710740c1c00b91450b0503180d6640803061200d012540307030000c0c40c06211a040c810500302c00b10060344d07a03010307035459400e8035680107881e50340c21103540011400b40f610700d89854100b00810300c01d880d4000c032000341944e054100b10086440b50f01d040204c0302500083c03542458940b180c00f012212041d401141211011610303051055805810071588080c0c0206c029030182000400b0001940101440d5682c980110034003200c0d000d460321141c034803110b030a141d00840055522010114613101340841c2c1c840b91020a1030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 912874784 1250 912873534 912873539
    0x30b1804080f0705280308152b061d06180307230a05010507020d090e0a050402010c050d02330a0e0f01020c060f010e06100c05101e0c0207 61
    0x10412840340d65400059800001a120113026040000e520318121040840800d5070329441e100303101070608213044001420220100e00e050005083c0c20b050f00c14002c00102e050721032014140f0b0070303a400c0102c4a40001020407150b010400510070300041c83d42882a0740302c4941c0160300706040440c003c02da494119150344060780e0805000090311501756000c0d0030341844607542e24007181444000c03641402d16204e5008084c3c2004010b40104d4000e03040340d000c407011414840c1d400d50b449090744c020210210b52000015415001d00d40165800a0060401404d40c0034980c88081c141313013450301c800c80541d104444d114650100e140d10602034041a94821804644d402000d081c81e00000d440c4c4405952074515880c0c80e0b8100740f10303000702d40c11104021940c0704024080310703440d690308588982c00d000244c4000559203169458603403054400800c10188001090300554591300072800640d02446840f0000d180009180300c2c8116110f40c401100103400e02c281d48020a17120790501d010115002803108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 912876034 1250 912874784 912874793
    0x60b0a23071218120303021b01020405010c032a29070e190902040f05030c030705030c0607033b0d0c0605091203131703070209010303031107020d03030b1804 69
    0xb040003411191400d1491003a440703900402d00101074010100d0000080080b90402d80c16034000c040010454014100340850628058201d000c1c522445020a03c40009240000c1c890b888604240c0b00c1a54140b5a006160315014405000524101e41168240b080072202c0102c104041000c0400014080420315000d0002040406081503042c0202d41c08040d510780c80175103018400161002c4481191142d41e180503030f1035040071911030503000b8090f989401ca00c50402050120a80310b01400600340000c3e14000d01c04070340d001950a40410400303e980c0483d500d2803029031110304840c0c0307802904581313001e08100140260206c62074420b005140e003070400503449007194005c50740c0c14201b10340c5441d908008200d120130b000d4519942e9010000710141035204110a00301601c203480d0020021412200b05250b032480344407000f0b9030100b003180040001900c207802c02400c81c03901040e000d041803143d9001c00c0c80600e05d03220450100392120b0000459003003246164100c009518600c2100d403c00d6141c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 912877284 1250 912876034 912876053
    0xa090603030e1e1008070e18150a080102040e070e120c060319021207090f08031812010905150903040b0d020f0705061e0a020306010819060b0a2307 65
    0x103919000301591000700c4144806408840c00d4644098034400c44516521130041a030941210882c0100302d045000d00c1c401d0a0200e90f2400060078130707003151901e80351203a087e002e41d8200740384181d2059421001040100080c000b80c0300405020f01440b0303a50072b000358044e01c45060f103c01d0345e000300c20071705250441420000b06400388100580765185c2e01e850702ca00800c2c5c003884924045041c1c5000054044c86494441002c0d0b00c2501d25690303040c1600e4844001c1040403140d4860798025500034050407128081e40300d4882c1e010a0028000c000080120144c1030a451541c10280d4444d000b0b40c04400e62140040645d65200c02c600c0c020310f203440e013490314000b002d0142c1e80c81c20155950224403030a8869542080703440c880d4000044401074582400005494081c0002550743c0070082e0700841d8801d0118001d490007498140c462a2480d5070700c1c9020720140f0009103a0a201c0d43c0c5030703640040c410403070100a1050706000d070394000801343c0b0b9100c0020141c5084d8071403203541d4010000392000c070b001b510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 912878534 1250 912877284 912877307
    0x4020702010512072610090e07172a030c060c1207060b0411031503030901091e15020106030c120b06010c0609050d1e03090b0109090816110a09060303 66
    0x140101c6494440d00c0088070b071381c00d201002c0c440c403046250340640352040503003005d031090007130030400d49549031103629a02c156480c8201c4403007654084682400810b19080d104061492840c5c02c841c1c0c0203103501c4514407901704107410480012480d101d0140241401d01608c1c644032019145180703003d21100da50b0f5954600004919000c580c04101c100402c913840d0072184c200c800041060198a5200400000f1a8401e95115207030380c0c018429032a00b030a01105841d149034058558119803071807c0c03e10100104100c849200c0c83e40180b4003c5011192241c81c85403004d01680002115400c6141254003600c03180c005960b40d4003c1d10360f0300c00180030854050340c010400c2ca40342440181a1410070042d140011005019008050381483c01c01e90200c0c003400c1d03610101407860f184d0018a00c080d022180c980301c010308980d9400005000392407841d00414501ca20800341d107864104090180070700c01051030011901c080302c1e4101440f543ca03107194400090725481d141003040703d03d565009040d452800d07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 912879784 1250 912878534 912878557
    0x30c080c031501020a021203220b0304030807121506020c0102010e0714010513060206060a05060c060109021804110304030917030a0f090803030a05041e05060a0902030f0d050406020c040207020105 86
    0x6003140c0003c0c0d20a020416406034003030305207800725111844190300ea03041900e244141c040b400342c584201c003201030200021030b2102d040051850b00c031600c3c2140c005000070300300f4050000c007441518460580d445100070310100b003401000d11509066000741001c808241407170441e070400e03500000752100860090700326410550141d84000c1d0040060711980680f1103241c608580d00740c0c0020f43da54022451a100d058102c0d01c00c05402d841d01c042152a008101310100d80d90300041c0107202c0b5480320b50080c40070302000000d07243c1c080b14800000c4c066a610301d16410a480e804000d01041542292459001c2c0513000900d0f4035100803070304140e035030340152a450804c22a09414008146028441d00c201030032184d0140c954034507000d010030010b0203050300c084409203801c0043e100c1115681c540184030302d5200d4041c0c040e03619600040400f030303c1e01e2001070707030700d030040040f840b45010301007200d883c41640e80c0c1c9500d0b48032850828045c0c24071001610b5507001300e004011140042c3c2c0d11030300b190040e2804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 912881034 1250 912879784 912879811
    0xc03120402011814030d0f0c020f010e040c121503030206041104020f0a031b030e03040504021b06012c06100f122405060721050c06070f030c080c03 65
    0xc07400100c0e5003048100d011000c450200301c0200740700c81c1407100b42c445440103404590240d507810354100c1d418191100c00070700040e18546a4030041c9000031849006403c1450440441d1100000007000c0354203044030180401c65036040c5000c86000c078051a40078010300e1040c21042803958802030b440d64401000206100b804407a1300d503056880d035058a41c1203582580c0c0039141c003801031002e4010a00030707140f5080c11008804041c007d51080c0124800c070b4440700c01a604048c50001800041c1d0403034240c0d9211310041150000c144403040142c18024804664225480b4601e401009030f900c0518000d840c0c0900071b0001c1005a4030f0f40034500111040c00d10f400116140326102c1103e540700e071001e600740442c2c00c00c1c1d4211003079030758803001d04030344018082d084500e156035004201840c85a908010034400710b065001400490701940c1c4c01440e03405040030740c5014910390005060860868280021501c0481005429641445020a103065500b4000310360300f0003c0c1743d01120300009003130004440c0b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 912882284 1250 912881034 912881041
    0x6080708190209070c1b03063801141b06040b0a0606050906090607050a0506011820090a1802070b01080d0c02240f03010e090a120c1106030a1506050c0312 68
    0x1070803864840c2500302c10b000c1c42c0d112034407443c023580908000810140e0080150140c07485001e103440d480c80300074001c0210085980c4054005603500800c181845060090600c1408180c0c4000310703001c0000d41400c4082e1071146402d1801500007180500302d2200c0c50b141160522600b0b030001d0440c0c10100e41100d007140c4401040e00050400c1c42001c82c01881d501485952404000001507014143c45200914205100700840154103d482d040e81003900d19070302080c07450503028010000c062030782014109035503513521090b026000d2161001c0402200c0c1c1e0014064041c8044000107901500c0d5080151040303400803c0c0003400340010820181c8280d00414a942039104200080108091038401a40d182c0045c43ea202181e40c0091003071030a0000e402e00020340d21440822a182d007160700204800c446c03da115011103024003507c0044800b10b50704042034646030340d0300700954484d001d620008101c1c08000080300780c144009502c5070003408421321201d041800044196100354454900000e400d58 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 912883534 1250 912882284 912882293
    0x203150708130f170c0d0c0b072f0a080f0c0709021c0f06050406091b0905010c0b090c0603190b0f061b03040e0f0f070507020d031206050406080708190209070c 70
    0x200c0d84030303800014416060101c0e29203410000702c000213405444808c24030b5239211401d0b1641905038048410390211008141983d00401e8040d555a000c03000454046007a241d5032110b066001480c8a155108082608881d03282c04001900140c00381650035400c0c450316409140303108058841605407a919100c048440c2c101e00c2c2e00c14001090010414004540c1d1940781c1030082c40f44074421082d511011a01c121b41a015500c0c0f04215081a5540f2141060b262211164808064813808050044004210060365080c1c003079405400140380c001c09410b0703907240c450101c8000d906040c0c029070103203400392071542e0b0f900c09403158000300d41000345800c0003440086040d0b2245410101592503500300380560001c14510740e5105884105d00341e0b50781d0301c41240542e5680a000c1000b035100c6120400754000a10414401407403411b4035901050f1161a01e0000342925407030b41142615a006440c101b2425800700440d2042034000c502e0410728185540100f50030300d1000340350009012440100e6000c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 912884784 1250 912883534 912883537
    0x6040b06040c14180402030709050a0504051b030414060c04262508010207060b13180f0303090506040b0702010b0901140d05150108070906060824010c0203150708130f17 74
    0x1900c0c024170840d6286010103001c1c00c0b09150340903843c01075610b1034001ca1242454800c00d40541c260081c0c046150718034030b0441d4441e60006008527140c1081200702620000100700c00c9020342202c80100b601c407402d00350001e100d2101e20200c20095221001d4140325410b003c02c002c4e40c030100f0141c90a000e07902a0124080e00016030f070004801d90320010310358003803003e103a000c2100e6203000c59501c003c2d081040042c500b03407080c6450200b08458881c0c0c401000403a88800c0031215440303410080780d040140c4d140d1500b00f642c1201c040d03a8144e038000c20014a6a420300c2480040d1200700c0740d15805505060190000c045000c0e140b50140c140c1c0ba02620900504100c040100960701031548030540c2c43d15402500c0e01064450440d40e20704003000442c003075024100c0c1c0b03441665070398120840e184025210601c6401c00b41c8030ba81c1070224000c240000350701c0600028881e1a501c050000795801d2984000308602c82c010304030b040012107440c0000000d4180b41010b400c454101e08820302415049543c0100d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 912886034 1250 912884784 912884827
    0x17090102040e0c0c0c030d0e22051501110115091a0a03061e060b03040f02011b0c1401050316051806070506090607030219050309011b0206040b06040c14 67
    0xb6009000704208011091100403c0103c0d03060043d101114034070001e060b6034090403812640401d420780942c06d4541000464043c0100428204040340182400418210780c3d05640d0031940a01a034084800c55811480310740e50034000300000c003c0c00920399841e1a00d500b4501403003480b191610032604a52104d64005140400010302d000441a52490300b0402080b4000e0300c103401c100448800c0f07960640c18450300d01100c89040041d45036585660320b12400caa070940c0700301e0508c40c5494442e121007058240303070514030b4464210940d040782891000018000d050001c00e040040c10070400c400c41c0d142548800c0c1c0d403000c3d03040c042d44841c00082c4560000c49800030440e0042404a150b100f4070800066181c040c02480d01510201c5e141c080c01201688550a270b5803003940f06019a203941c1e140300c3c60003141c2c00460800006180000991b07080502d00c4414058401a40304501f1310007401b8480c60700f140c0191b0308407800c0015104401000d0051041007007400c05000f40031824204a40030010030410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 912887284 1250 912886034 912886049
    0x609090c0405092e050708100308070f3302040b07121e1710080d0e1306030c15051c050601051207111b090412121506110c011709010204 60
    0x42c0421381c025a4035071002100704180119082401140e502c03801680e115028190081034400441c2c02c580301d0035510341c8100c604940700c003203060402011401000c0300c000c89480d03e80c1400c0d2501030b14110803001030031401c90305503032a2041004004005505013180c04d801e602906840302d184000c0030680d91450700e80c800380e00da4517480031104003c640c40150301440b142520009a0a40c4607900c01c90a0b043c0b02d402108910b52100c6120318a80740070300194440100b000340012140c1540c0c0764541d00ba10b000b0741c803ca60303c030b840820034040618a4095416085403510b070040c1003441088105071f4049100c0d141c00e21260352040490b04e0b69100710104d41005600d4100381640d8180030100512250401820004078042e0310070310920340180e20403500c000c01d03004114a401e41c40d0790b102c005031103c4c548030384420b00200050703c5c040640759006000c0111215051000c80c036242c0240078140002c140c00b648081e402000ca410516070b0440c002403000b401c2030b9a010707226a506841c4600a00c01c50b000000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 912888534 1250 912887284 912887323
    0x8070302190803030114090a0506400906180c0e0606070501050702060106110313180b18041a0910052e140607080a0305041e030c03080609090c040509 66
    0x180741b02d11039040c0c2c0c00010f810344400c10aa42d0b0011101c003140c8040d12000c0d0300c5a911842a040c8010540440e001c1c1c2c07543c90104580500141810042c0203000c00048460585030115101400744600c110b14030490f410704040e05602d001c0d41c6c1c50b46204140e003c3d41d00004d1140c0d0205d0403a03140d0300141c0d0b0f003595001008011341e081209019642c0c803001d21945002515110301003140c404080242e03082190000c9506e480d035410000c1c203000f0380942800005402c0d6982c9002c8285654000c03140200e004011811400d60403c0e06003a5007022100400210b0b04440c4001c0c2300f01310380001109860320a00e000c000070700b91a08002c041070b4080705205050304d05160040703d100c47d01c2800d02038040f1442d0401c6410031107685018401c1c94091040054601b0b5020720a040c1c0c03180c0250840b80c1e0043c496004c0321900a40c1c1002d80100150749001030700014030081c3c4031010541c001d452542c000c0305c01c4600300070900d040d19000790380da0141c002d80c5015503102c2c0046020000100600328000b01002c140700e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 912889784 1250 912888534 912888539
    0x14010905040b06060a0e01112803030e0c0a0909110405091509060f1f150e04050603150a02090f041805100b090402060f07060c020303010603060f080703021908030301 73
    0x2200503180c2507a040e240042c098010440b54074190040b41e02001d80ea48862880c45040001514940713850349080080d0b000b10511000b101c2c040048040e1405000300c05135074512550308006003140e1495100100560042442c2d00869558045e40011590003e402285002c01803400318445400c04034610303041030800c400d000640f68041a1141202c20380c80c82540295900300c0c1c5a56500019100554080d5109000c51340d940c2010305000040400c42d0b5029140a0380c90741c64141c07643c1c2602c2640005000c4900c0c0c42d40f24074140c010185c11000442c02480801d40304500440b071400040d00c2c0060340750340000c8014150300c60003400f2400000003032080000b80031501184006540841040380c883c056540030014056040c8134607403081e640500013103003c2d500c503400e120309079010450000d500503060082d080080d074140102e6031104c2e80d03036024549a5261102c00b8040d1141604a13000da0303c1c440388240110800051080122601101c1d4410b8540c480880e001ca008840d801000c40340c00000000f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 912891034 1250 912889784 912889799
    0x110a11100201090b1605070b090109060b030606100f11030f0a02010c17010e040807050f0f2a040b0a03080301030503041410053106020f010f0506010906121401 70
    0x209044106a030040e0411108500c100d088841c3d80f1401450b0261100c0130844114007801203000c2050746003000c2d031030082561180414090100c1e4020070580d140c4a49004011182c001d03034103503039000d800401c401e0404000051420800038000010045402c0790f0108241c4201b81200400d441441900d03a07654102c4260542503100c1881d981c0075600304001c10071202d01c00c4641d55084004500008003990900c00000c0201c9005041a180d00c1004d00c00342d000310741e040c010b004000064030014640301d0400b42c10f03517090507030510000b07003c0082d90a0074048030b80030500d074150000e000c96000070303c00503850001d540b8407200d4001a0180c44040300200c02c1181c000003c00948480d8540e041e06040c440c810030892a414611020000700b0030321403140440701020f030056804401c0315411814003108509804c140301a80c0c07140e8010b1744031664002d0320107000c0c49942d882c464080d206200924004001805004003807207120102b03d2241d1244c6420002d9a0002c445031036820100f00d500d503911761030b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 912892284 1250 912891034 912891053
    0x51518010806090d05121902120906070212040608041401020a0801180b1309021201020d0c200a080706060b1c0b0904110409171b0d0309030905060a110a 67
    0xa080481c442c030000700c0d000f4900042c00b4407095003180d462501d031000c0460300400c0b060b8042c02e64481c2034808802411007080f0390020349507410b4070141b901c00311710340400810b107898030140004095402c00080c1320342d03062401e001c42c0c3c103a40d0347d030400042c07a48841c41c1c820002080c00c0850005540701046085240703601800441c100d6152502d1020040d01d0b10500388120b40c41e61030030990102030220500705040d8a9000248502e000030240402c000d032000f242401c0e42d00000c002c03141035648103000801c80350080204032044a11000c1c0031000c64900c034280742e441441c2800501450b401040c0e52040003119004000644000e0381c4654030340b404600d45d0410162483c181c40355060601491001a0519184803445241c110301101c0041a11005000080c900030005036038603100461200d9000301103030014120103215102d4040350f8060241c0c800d05080842440008050800c1e800c9c501095004c00814107984c0c0480b8074a0355040e4005040e100903041c0c0c007040c01ea030b008080345101800460301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 912893534 1250 912892284 912892289
    0x170c0d03170106080f01090506010c0203070f0501030c0903050d052a0a0b06091509090c03010203010b0403060e070308030c0f070204091437020102070f031103010b120d0305151801 79
    0x89981e03060b62104415910020102c48985103414840010009040c4680145401c1201070501c0c40280c0410b40100303040c50841c0d000100c2042840c0b00400055074184180c403203800141c900101094116a03c2c25125501c011030141000804108450a840411119000140359110110701200c8031b0b5080c1d074592041c11b00580300325145100003400e504026110501c500f04000e402e0010643d20810000e20000c0a00040710038400c3c0c8640c40541d8400344001c5002c0c00380300041584582c61443c1010a40b0714950690800b9041a0000c10000d400c03481034a400c008040891511150034481515050103802c0000c1d5005040444201c28000c26100e070709030121400b4281d5240b111041c041c00785104551105031800304c2d040046810011401140a050030320520644004680e120840030040440b5003090380d400f50501d85410b107501d02407080e00504a401d0720422000c003003007032040d9141c0b1604e900000c2032540f540006003032000000340d52110404001c3c41010004034000b50f401c2d10300d04c00d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 912894784 1250 912893534 912893567
    0x301903060b0909061504170c0f030c01020a0605060103022502041a0a05010e04020426070501020705090109050604090525080c0d140705130b101701170c0d03 69
    0x15a0115154040a04540c08000d01030300150f50341c0c85100070710844540001510001010600c03010400c844200004031070100c00340e0050586030b0b100c50800000c5888003050a100b907100700548062a42c01090441106030000c00000399a0307209401600680300343c2184c05120760954140f0124012200c803c655828002e407003c01402c001030700800142409840410b500540d1130f1f50820503580300f000e44060204000e00007504090760340c000000008007c60320b0400e44820024500c25090301000008018042403000784140f0385490042503040f0418003442c9002603c4600042c80741c4c42d10f030810180d00b60b0140480d40c0200c1c000c0d4410300085003484140b00c05540b100380000304448001203d03442c8403801048000d002702140c2d545400c20500e4005104a0f004015000801e9507800e502c1100f4542e11020201e240701d0000c0130071480c40c20801801b010702c04c0d40740403440600840407105054403101b510140ba140c0148080b03d1908452160065008d228504c24008056114900180150f01d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 912896034 1250 912894784 912894791
    0x1e0207031b08060f060609120a02060409050412020304060e01080603011805011505090103050304050609030f0f0a150e1e0c0411040503061003030c0b10051c170c301903 74
    0x40d42c0142c4c040c00c1c0141c80b0300390b100e203007401400502c0c40d0294881454a2000b03003241c0032580164003040c81c6420031752150f0003081d9501c0c10041842165071240880329500c1c806035240900b8014007074117149403d0765549c10006018005039268409601007040c1035855850b140400c132540c64200e010700060310400c010a00e41d01d0000134541801c4c1c1280307040e81c2c0c1c480051410207040000384078060b00451071483e8075125811f030030490030b8024840e85044008170405003085601c1810841c2c04d16443c0d2a000343d01d280b0b00206000840c02c0403c1007400012043c030f040c031180fa81c0c1c1b94031621749032021414507806031425115400d040c8642008104131801501615820ba850303070761400701103402c1d10000d00419400e001050019440d601c0c140d5015128070700d801211070302c91022920580c0e0300d543c0ca000107241c490300607050003510004a0341c1461000803080c50300d01c4810840d9241c041568440c089602d855112000710807903840300204101070100155211003181540e158510401200c180c040391030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 912897284 1250 912896034 912896041
    0x12070c17180f060c03030103080f0403020604090b09070c020f0108072c1206040f0803100e010b09033d140c0706050108010506010c0210111603020306090703031e0207031b0806 77
    0x20708105540f40001d01380e001d1810b5a103151142c032529441101c015079110401c000200060f0b503484c01030006840309900004034048400b061040503000503000741c051007503141140c40160f0303400c071410380080000c1c80d202d90f080d255220140e45078848244440c0003e803200c01c2168598400c2d521004680c1011500309000810580c0400d4803504103071401b83c1805d070071020b29004209140011500b081e03420030110302107980c6001c032030304515080e000b203050400005103242c4070b0b241c10001e038100007804a500e000d1b481d54080c1000c0d00c0307485000b0780489214003070503143d40758243e9920500811039464440c040500d840400c00250b540720325000c031003c80c549400403030152014807496114100c1a1952002c040e410303000c1000e2007100c441c8040030040320f04010000c1c0c2a00b0b020b04004040d864014103d100e0440c8101801c0180050004400d40d004540400220794041e4000110750312680030062070207d42d030001ca04204031500050f140d2811050b90f55001c03110010244221041c40d0107485440d20b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 912898534 1250 912897284 912897289
    0x1104230c072f060a05091809100e070302040509030a0801090605030607050c034b09010e0324041119051e04111e12070c17180f 56
    0x24400014000e1404854403409608410b0782036400c0b109042c050b00200d40c810000501168130840c00180000c402286041c540c0c1020000e21884801d12440206c10b031611212066541901000488650f529290500c81507841848258051900a0b0003408a45041c002c0150790754420700039800003580744030001444078814810300003502d40c010054081c0f92103110044031290050403000e400d81c0010004010a011021402651048080213502400c0518442850458900139041080011040d1000d030a02d180c1d42c03c03610055402d09004140b0120306000c240b500c00381e114010b20360035040803050301c2d02c0010f070800c5203e1072062059421100a840c00c1c084045101d01e440c452076610b411080c40b240c50320689401035412007008407100c2c000040001000e4500101004000b182c000a0005550004001c46802056190303081454080c1e0603607a4440d07960001d0841c1c017040450302c2020300300b2040044440899124400d020385445070075458035447d42c0b44803a403a2182c001e9480310442030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 912899784 1250 912898534 912898537
    0xb190212031b1308010c0908010f150b03100f08030c0d1115070311042403050f0415090206181e0102030f0903030d060b0a03051b040302010c1104230c 66
    0x1180011042910110030860611a036003100c42c3d5248640b80c044408100420b00740300c4c2d1400c60000f070396440031280ca455159801c6030070300740700c800c40c884c2044200031400700b2140456049501c01c159195513a0750300c800f805e240003180c0e08030072110b1010080015034030200102418101c00b240040c2d510040001c0c80958840080e04090751442c3c01c4055401190b003030580096611407540c2c100429490110344127404194010f4210415104000001d5060951008214420885203003030400c4603040003200b81d0310b0301c080203000400c81c00c0024138041e6050610f07001640c00360307809000d03903032520072480c035440140c80b03580e42c610300072800e841c103220540700c03401284294900c0c182c01031480c003810345a05c00120743c01442c000e80c0501c006c0001214000c003d1040034000c002009015885d4210007200905803403018001c0c082c80c030b000c0349148440e46024002c0b40d0440e0350909095078003c00914000850300e80140140f0b9101d0310f001d404241000310000e11541c4c49c264a0400900e07562083c0d80d4070190f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 912901034 1250 912899784 912899791
    0x9050c070b06100201060302100c0c0e0609160e0a0f031203050c190207030f0602030115080601021b190305070812031302210f16081c0302090402040b19021203 70
    0x7540c80d410080b90903810300e0003a0000f003030418400410110307120340110b4001c2402031014000545159000b2051111004401c03000c0c1461000b0202c0b070713041500000b003044e0b0000d030015110786c280c000003020140c0680c00359503944d0006044d240983e591004115020285d911098480c80080c0f1100d0382d80c24841e200e2148a5400c1880150030025858644140060070344007100a501c291503011010403d120140004107120300c20160b035a40c142100c0190306520000040140031000d803d226050382c020410142d0f02c003203102211917842400303000484031018241c0c0c40b03a20b032200309004014080046826800e8500303c1c02102c6841444504120315844110780038004202c0c04130341c41d0300500d400c101690f40101c45252070028500d50760030700c0f4144600712203869044e0b4410840510b010b41600e000400410544005d042e4026001c0e8038119030350030801070181016400607484489560302d5050344d0162540c443e0320f03030b103940c1c0340c03030802080c400e80912103000740c031510045400818443d03044a20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 912902284 1250 912901034 912901043
    0x50115120b0d0803060301090506040506040c1203090e041e030c02010e01091a0f04030209181231120609060506090c041401140a211506080c2209050c07 67
    0x2e8000035480301c40b210f030000707001c0a40c19525812110b002c600204101e5000c0d500520103014036060603c1c0c03940f07810031198402e1000320401c09980c4c0100b038101650408403450071b10f2810556840d490008400701020081c06025400c29003200149a48003050510303c0d4402e1f2600111104c07550015a40580503110300011943d0034800c807400741c40800058000c084102940c7c0c0d04254407980003e203805403c45143c030011a00084810344400100074611005205400082c80c21401e40d410240c0c824035003101c00580009215003112500d01401c496004000058905080241c45c0c900a00940017418040d254682402d02040c0d05181901e003185c011790032804201c0c5020b10300b552185002445541071410f000c00d05d039440f00e612190100034040c20680ba81e80041d81400d0801c0a405c030380182000600c2e07546844100d261800d48503403414282c0d442410494116030b03031921485468454038061162280c6d00d40c01407026818882000c005403140e60304140401d60324036034003400134000c1000140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 912903534 1250 912902284 912902299
    0x40c020a0204060e0c070204020c0f2a040504150203060a050a060f02010b03240a020d1e0c0f050406030e1212061c0b060f010512152106040803070c06050115120b 71
    0x2d005144c42e0f40104038411000741500d904075405032f50389040141caa100003101070844540c40c042d101000030f54420f03000c0100c0302085503081c90341f0b5505450500b801d24068103680000400e0303045e5155000600180f03001401d610b013141d21240000c0107403d011080002540c00e004103004180f50101d40c03090601c11061400c4c80c104c120680080398103c002c0c0000440c030b5800c01880000d4080e5025030300c1c2e101401440503c004008110081c00ca905440c00e030410408d45103583c0540c65030180441b8201d840600d80443c0003a408001e603400c003000780c0e0101d440b118001654540f00404010100c1c4a690100c80c040500d028907019084d00c0c0d0a14140144030554020001e5601e14091000041a4034189042360404e0740502070024010713000c0c4c1d02101015044030003c200e918100300074000805c072441c0200a2a204c50f01601e40d1004003600042c8880c10220001da01e2030721484101d4841d580001080c040795030f5800301800800050701c28400024410500d01da61000c0d1800b9400100134040c1061 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 912904784 1250 912903534 912903547
    0xc04050f071416030509010f030212060f0f040f06050f030706020304030605150d06050105040513020303090f010212031006180602031b070f09060906051f081302040c020a0204060e0c 80
    0x11140310b0b11101c031140034140c0c18003188800450300c4450031103461003920b070310f07035505800c8002502102240041d04d0030107004000007840c00c0a03010149405c5a01a80c3d140da80300c0405c00003880c50211891000d802c24600380745003011010680000c1d04407a4140c40d034003040c040f0308052589902050103413101585c0308000400028199a00040c2e000d03c040ea43d6005c0c408504001407a09040c180d0282e4901e52202c006000b50301c1c5c13912807140c11024440007a5982002503010949034010072403a180302d285400504903080e4000d01000e88651103143c03640340d89103442c508018608001d4002c9100042e080c0a01150795040e03100c0e04010b4030351039001507050461703007a040801e070450800691400d001d1134500050114071641b8050280c2100349002c110305040188010840311207a02c2144502e003c0c5001c440b0102a607980ca42d48000e6500d0114082d40d61030300310384000040c03500700030b41041c5050380c540b04860f80807514603c0d0f039108072014040140c4d100c9100c4200d10068642e206005005c1115 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 912906034 1250 912904784 912904787
    0x30f031813060e0c03041a0103060c110610030f062304150b011205060a0306020d0c18050108010509070e06040b03010e0a0501060e06070f14070518010806010b070f0203070b0c0c04050f07 82
    0xd503511900ca01c10440c7c07a110a10100402803000782c3c0200c40c0c1684034007070702100540040640c0c2040341030500a218a29011281c1e010ba1469440f024007683c0c3c01d013050009102d200d8000131100e40c60011003050b07241144a8855030100100c0707003500c650042d030441d002c2d10030b003e02505801e100140c2d40c0044a80e0038544034401884090305a83d8011040940040002c260b8006020740103000c01000580d07280416019003003654800d0901d00c00d00b200c5a041c0800c0e078005880c141900c40030b03034626400355036001080d40e455089000c1c1d640c2c0403601040016191061400850685003070030305005940c0c860301f07000e2040e20710a0242201150100415040c1c0d401c0c02d0010f00a25030050440f1011003e0076120346018190b090700c0455142c00603041440103040906005c07403c0c9084014001045d071600100c00e4903203006003d06071146600003540010301000d004100c0259400500741c2e808166101850940c5a20102041c0164040c09034007100903d010310900b8451021034000b0b242550307030411b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 912907284 1250 912906034 912906037
    0x2190e01091e0c050a0e0f09010608091609020a0e010c1203022116080603060412050f091c060e0309012f0708070810050c07030e030f031813060e0c 65
    0x14440b407402c0c44126615103000c0c1034001d40401088a40716196211403080300100103000000d441402020400f03080341154440b416210b04440703040c907041040ea02c071200203500744406001c040c50802d400e00d034046800c12065005080104003600c0301030b030310800c04006480c809011000505012501404010018040d800418094080350271301c0803224680011448420402d40301303081a11003002c200003510382c0204909d50009000c4000740240d10305903035501048103a1403200410030201085101c540c00c500703000c2c0d40b2000700c0241240090b400e420002c11040350349107001d032491170800410a0800710040100c405481c01a5901030000c030744461220080b640d076048903141c9200d0600701250382d00701444414090151079001c0e1408501d44104180780840d410341605065140c40c0c1400048841103044400b204d90500b0205401d64209000904000c80c4040d4041d00d0f000000d16002d203064000030f0400040400c6403080f0001440d030b04a00c00712101402640401102600486d100210f802c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 912908534 1250 912907284 912907301
    0x3050c090d061d010917070224041d070201051b040b0708090d0507030614130f060608030414150a0206070c140d03020c0d030c020705060706060b0309070302190e0109 73
    0xb010421070144060f8001c0c0001520b502510b59644240f41c07010008405806000702c6840c10103035080c9051500050055407815a0f5002c401404e85010742801040b0744c29240246108032045491404855502e10a8502120504019480d000c00038554580408a9181ca1018602c1890616003480c0b180d4810760312018007542c2c0401e060164007020b075944074041216912034005000310600c0c500d07196050b034440c5580300301001d4400303080200c00c5201090f100d443e2a000b00710300708500c04500700900249aa90450f40782ca010004020078086200001106c0c400d41c1582d140050501c08a40c40145000e00005140103030007810203e0021485140714050080c0103030300c620003c021208806103012020302da0480442d4011450b0000d030701c1d090040e8842403045003801c2c001c41c0c00300b1074002c2d1549000d00a541c85440040348520a100c034550100b805042c003180420f0b92801e000b844150307100c82520040b031054000c180045401800617065100321227103d41d0081c3c081e420900e0f240098103620 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 912909784 1250 912908534 912908543
    0xf0b0708010f06050913090503220312120b0a0332190201110303040f0b01081501030204051e010b0306041118061e0a0e0405090c180912070b0708060103050c090d 71
    0xf0850340e10106c0520800b402988108002d51b501c80700c960001c802e8400344584041e5001010302c0800120381c0e5041d02e0700350102d9601e0500950a484815440100f080b120050f4110381001004820404401c411140324000280c800307500030101001a032000d002c2c0c85240245400607084a10070708041c55003500d10070310505182440c0012548014030f19001104c05540c1c40c940744c0602e106020104044901500e5076002030706011546c564422070310801880001d00480d074840000c0d014580c3e030034075488402600c00c0074100c00e507940c0084111075002a00c100d07100381d01e0300f61404040800e04044a46004500b001c0117603900800c000c105050308510b1100360414903d02c0c440034490781d410300611030701150762a94408440740c0410301c811224000d1070302c10164495030b641102607541e141010b1100760038003484502591901c42044c1440d0000e2580306214201051480800000441880c880d003400e56030204039036580c6004409403201520005608902088071241d642491820212250b004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 912911034 1250 912909784 912909799
    0x9101503060c0e15121303020d27080a050c1009031119092c03121801050103080d0e011505271906050607020108061017040f0b0708010f060509 63
    0x3c200c0031400a80108009280600d0b0005500d2803000c00c1e00ca071250030459040079072034414051368019585140520000c018801440c8103800c0304d6904603c1c0307440035045090000401c51390b0fa01055585c214141e011616401884081500f50500420f02e440d800d02681d030342d290b01761a41c0c55540c04007003012151038000d0701850200010382e00d40a0100b00400800d40c4c001610031101100c1441c6000d070b5031400c64501280304d502c1890400c0001520000820120010340c00c4d20f4001458806980c9a44501682d5007020000401d22180c8400303440786900c07100c13080c40750284400e405c81c00c0303580031030005c10700d415000001d0101d4144582e14020808401a4409408141c00800d08000304201c0341c070540704c05604142d96210f00c4d103001c0c11000301003c2d200542001c615a0002c0d02600c030003040c036805110340140b8070100c640b10b200f54503442c0c18608214840340c1001d041031940f102450303900307440303c0083d90085034440e44500d5006040b215001410b071055800d1050072902c1d13500c440c0100307512424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 912912284 1250 912911034 912911057
    0x52d12090a052d0706050f0d1409070e090c030a11040b0d0503130f08030904020c0712030903110111060c091215090d02121c0207080d0509101503060c 66
    0x30440164940d0f200101c3c803140d6055220400307840d00e0441000505900400000c0020981003000d4940c2d0840c0d284d80151150040d403200c0004280411182101254500a00c165801e0106000050307644035143c03201181e607580f8403543c0e00c5040d03480c4150140d00401c0c0781404078a160b2569400c042c001403011505816010008a01c0036001005840e160400603079446000024070002d0300801c60b000e410403041e880c0c00101600c0b4050018418012a0000340d81c00b455401441110007a00c030507111088c52107841c1c10001d2802d02c1700d010480384503c0355030140c1400e40c000c1514003101c119210090010350b880780720002c0d07242c110440c040e03044810041a03c200e45020b00544110014160340036466103820343d209441e01075070180b000d00755004250641005107080d01182c59000160310040b540e1442c100b042c8001340301d42240238141000c04039294001c400960461030040022008480481c280c02203541c1c21150024182184401c88080410020721641c003d80c200b18181d013403070b452891 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 912913534 1250 912912284 912912293
    0x1081627020a0e01020c0d030207030b13050f03030402040b06070503030613023a053c01080d0e0a05180402060d020310080f07032a05040606052d12090a 67
    0xb001030310080003141c0480c00002595038100410060402d003240c83c1480344207030340c90113034941d0303a1408094000e1076004001043d64000101e511120381d4400102e8948100784803107180c03660010f0340c080344a5411309003803101d10710705402610012608080614a180c0f500e4003001020702543d022030120607002c1c044c01054604074000e03112034010702104c00503056940020440d40303c0100c410002c926141006000704651680d45141a1000e02c0509108071440c0403c442c54000c03641c83c810b015240080c0001c102c81c08007150395940400b4603203031300c1d21400d844010403601c2079050162542014840d8910b4200700802c0c1c0711260801c1c00605214a0100301160440583e8000c454518020401740784c1049604400c2102041c2441818080d2186505660710b42003040180e541c140103d070160758151010880c0d04004000500c0c1c001e2040200300e40c4c828000c2d10b01c0d0440700c425404101c4441d44170b1400c5042880c5002400140d020880ca420015890018020300c00780c0340c030105100c0c2540b080b0008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 912914784 1250 912913534 912913537
    0x60a0305030316122705010f0911041a030d05070f020a030b040b012c0a0e0a150e0106031e1b090b041a010e0906060d0504060c080108162702 62
    0x8003e401c60400600e152400c01906507a61914914461840c0540314014003550001d0501540c001c1c8210442d00ca140342001400750403181480d0700d0444c5401805410041d510a066042900541e8148070a1102e410301094172040c0014050300350700f241448256051245004045051080d040410000419008201c04c03800c2394000329070198150b0280002e1062003880e440c014900fa800d102100b03121801c0c5184007940840a0103c00c010074004582d1015072a003007040000200c6084a41c15138040c144000071000051041c28094a4550f100c504442e040c041c000560381c110403400144100d841c00d100720150001015034018032640c051b0100c03d800701d00c08a0040050f08404101c486500040004640d084019141c80c00919001408142d800014034182140100da0720b29190340c030301000c0b0302c8a00c1401c088400f440d20749030411041210310740c4058101480366850201c16a00c4180d495515140358100c4201911003610070403120009800061850113048240402c44c42e9140da800300b079 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 912916034 1250 912914784 912914791
    0x3060807080d0201060b0301060f2609012906045117130203030c150411060c070902090f060c010c032a050f0f070b010806070224060a03050303 63
    0x341c1d000082c0001c0070070703824042c00010309030740a06189154541000a402c04041544c00000d2140c1040130200094221941c0c408601440060100b030f45410140180242041000c40101c0d031600d041c0310000948110300010540700c0a09400c3c40e05080811211031750350b1546c000725000003d12086031401c0c0c0c0c0b0300218441d40d400c0c1c5560110003800c1c0c8000300002043d065501c0d081040291400c01c1c4150065181c54111981c400619840141400441c0c190b1240341d026030750314440e0030100e00103c1d8041d40003070b108074054013010a0044201c0304001c401d200d110541e0030154000441070019a035550b005028803540105403008401d03d00b8049081c81d0400f10552000d6555a504074045c95050300880f03041c914411002d00301081302100800403007a170103080001700240882c040048984d44000c0301c1503103d06100b0b50792101d0551a10810040c0240140c0e00c013402108003041c5101d000095400340a0a02500360106940384030850b49420720050103264890202e24001002c6102800290300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 912917284 1250 912916034 912916049
    0x9060606050706050a021206101403070903050613080a050a0306050a231516060617010605010225061b241a060d0b0d12020607030e0c01080f0703060807 67
    0x100d80c55281400002c441c0c00801d005c903880d004014880b510118200003581c04101221000304185008004442d00d20f4421910922148004140469290070030142c2c0e00b1244110100c55055455901c0c41890505240b4002d0141e0002c0c004007110b14014400703054003040034600090007555400014404040b00d520545040c6120303e14441e006a10180c00c01c20200e094441206400c807115aa411920404403a02ea6050100a03500e0411180e03400140003031000b5508945200071000040d4000c001c2480b031540544901e041403000e00070b401485000942d0810b1440810341d00e84801039030b01c45406025550800c2c03806800c0307000100ea01c02400304850355014109140c00c5c041d48080e044550f901d95421140341725415400190f0380d05c1c0102d8060768850040855000c2c1d003007010920b210b1056200400d00c1c50f0316410a015503500050b40d503c84c1e1919581804a01803104165031103a102031714131400954080000350f0880701c1c0d00d21140e0040c405280c00640d10740d541000b00d00b40310744d5412940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 912918534 1250 912917284 912917287
    0x60a0e030c0a0308071d010801050405070302091f110a030909090206040b07050c0306070c05100f0e0d02060402030705040504122001090303060e0906070906030902061603050d0f2d0906060605 84
    0x45441d80003155000d0118880f8071680b071b20754035a00180013508140301d4940300e00e0f182c00016a0f41c0e44070360140d0700a428050503070902d1549190030207800c1c42c0303240781d000001144050964038540700021b90f0520035030140c443c02c0c000381c280940007026000118040c1d8201200300800518201100000c0c80c1060140002d450301c1c02045042500b0f1402c00b0705058200000c2034043e4012420110b40300010380001100020699040700b200c401030505880e4500d039900604100118982e0003150261046100f04c00390380700d050b152001c0004503101914081c0030600340400c0103040d0360140003548d40307a60a44085100940290f841c050a590b0403040803400252200802c100c586940ca01440e044088940940a149030188006003514081d01c60502050b8840f1292815502c445046610000081000340b01e440da207400d002c2e1041e40102c803801d000303034500300c04080b8000c2d035442645006100080180b01512204028112820031185060140d0ba51580141b001400500c40c041c02000303d80c403400e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 912919784 1250 912918534 912918541
    0x18010b0304050d030b030d0c0c0e131127060406030803090307031b02061e1909140102010605090a0b010e0405100302030f0c030d11101509110c060a0e030c0a0308 71
    0x9007450004400f4000b4942050b151480c02d81d00494160720b170100505d08011603242c14241424070b401ea50f4044448801d10400340f260104001c2c460b0340d01e02d405441505031805a1809101804440302c0d40c80303d9403014035401e464400342754001150403140003040415455181d403120075041c0e006440150303c40d0700000e120001c064000d41140101005030050800d202c4840d00810181d11940034081c0303002803141030980c01c13007206074140c6e003804022003203048c80c2c01b4039914068101e544c54003904403442860381d8030984540c030502a20094540181c101600c94480c00c110360054403460b1045418801842c003009926211842205e209001c00e800038401c051030b50060504114003031503092855007100402e06959200000c90300c200b03441510b06603980c014aa05924140b2100900c1c1039030036410607840d000d1468090001c441641c6a0b418200184003241c03496031494401d414000265401100000f40c0303024217075205c400072900b40c00079a0701c0c205c3c0c00358406040a01f4a00114003080680c0e091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 912921034 1250 912919784 912919793
    0x207081c1d030702060405040b03120d05040c15170703110705012c0304030308070509120106030c092a0207050a08060f0a0203060607020d1401090312140705040b0918010b0304 77
    0x181041c041c0c801c001d103142c800303a50082400d510407801183d0140d5201c20360040079840070002503042d0328124001b643c0b0f034040f48140340051302007500c8c15600300ca0740c1e000106006081d41c40030110302c0195210030052100c6004035154081000780508249565001042c0103604003000802091303100740b00000e14480c6143d060440c0040000d2031002c1c1c190f44001210803450000101c1d0305480c1c141c00d0440169407403510440c3c0600c580c007011078000e40c80c00e0300300c0303081441508610141e034030070000c0c0031711182c58610800486241030341c03064582d000c14503161201d80c4001d0061640207841c0c416107005c103848101180890440e83c1c0110030782d50110f8200f2010665012195401c01744240c030962841c100400000c12901465002901c45c810302c1140000f080b0010000c038880c544c03040000d00c21407940b420090100740f056404040124203050b94031130710500c1441114414460303511117904082c1010869442600701e181c4080c2c01201c60000c071869855080c82041c001e0265030712040d520300c0e1a04d0f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 912922284 1250 912921034 912921071
    0x70906080705280b16030f050a09050d0510060b0a12110909181b0f090609010e1b040909110a06050301090b0f060f030708070906020d030207081c 64
    0x4000c1541d0007480040c0420b41d0b481841e0518401110020b20503441441010000980168050141c003c0c00052580d900038156400002c058041d03140d00c050b844040d0401d580510035070110200003800304009010798901103207070210b214001c50403912004000841d40040780c4c1680c0001c440180c010818041050348801c030090800e0000409002092180e50510014041c418515100b00c406100041181510032090f0880e034841400303c850102c600580200309900c2480c48500400f2859100b040600f0480c081d075015950150460304182e2902d016800a09009020301d080450101c90710881854100040c001400801c440000c0310b4a162030411101743d1504140d034020b9020311410011181c0080075a8119031513840c010420107601c50010b01d000c608014055030080300810b584480c000c501e40918418826501c40c0c1c045a01c0b002c5d02500c4103841c5104850040c0d010901010045200fa005440d07900d00c41e10b8401d017000340700640c1d11829511271002c0c0e43c2e00c941e01c00006040e00981c08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 912923534 1250 912922284 912922289
    0x901120c0e0403050c070605070c330e03010b060c0c06160507060f120507020d0e04060f090203040b0612060109020a050405180f011401081303140a11010c050c10051b070302070906 79
    0x2019441c0427115900c401c400010f030311171140340d1407401492462207101500008903c5500c2c034009295611020000b80151400340d10b882d0107903281c141079990394107000048402080d10b0100034031804003580708000c0b1992010b40928404030f032011042002400c100002c06c041c0c4070340e8458160200344400010289241810710070041400c01040c0034030283c0225203c1701600b031900e403003001c0c20303803400200300a81155480f06103500e0f030400001a50a1481e4043c5010b1840741c80195060384072101041031501a44c10021900c0d000780e4010001004154000e0544210a003861810180d482c800070340418055010040c3c1c083d032600400100e100a0480f043c00f60141400d20764034001c0c220002014104014403c00e105e00000f0340003c28540181e80c1022500101868165210b80c1500c0050a034910010040305030760810048030620b900a00681d44840403000040102070b60a0001e40090000a0300611245209000004000c0c1450004001641c02a0010003441c0d2616440c08201c07019075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 912924784 1250 912923534 912923537
    0x1103341a090102190b0406090503130b030603060a02070c060503061503010801093e040f2a080402150310051512011707120c090f06090c08060901120c0e0403050c0706 73
    0x1001340e100007072440e00300c640d0410b400c5030002032000d41500d0300502e140f003a1012042c01c810000d40008846e58803000035031285070150266400303521014884d1003a4000d4a40042112001410900c0310030300c105d01460340110700500b80010700c1040406080603500a0304400c609944441250f801e1202040c66030078684000c4203600c4e219606240b0024117818103503680c000c81d0760500d01c540c89550351a0070684100d20008409c00014421100b182104440038600500e1942c00019001686000d0300005104680290002880700c883c0d02c890501640002c042d0800c04141d8440070070300d5212201402c3c4106003c800d91942e4408140380c40d618003005034001a8401c6210206410f1040c0200b0740d40200c41c0080e0326000614210314002d80d0101d4107401080740c15190401c079102d11442500041d08448035403004004182000000b150a020101c0340c0980000d0b0482c010020480044035800800d07024048122080ba2510062241644250b60903400600d01003805480c8030740c04c1c0003010082200307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 912926034 1250 912924784 912924823
    0x1e0506060a21020301020c070611060702011b0309021927021305040905030d0c1701060e100e130504081b0a0312050711060a091103341a090102 63
    0xb03280020702d22400e4070b040c22a03400506411a4115102501664814006202a80d400f503454000090001065011505484c85002c01082c03140d401813180c15a081ca0340c0706084049140010203070302a000b01e00d4101e800c81000740000292035141e0301c01102504c00318006548101d001d90f50f50496488610101662610401418020126801c501b008951055401050072102410010f04500400703001c80e51443c18861002c03070040c0d0041401a0300300140354106c5080e621400308852543e959001980c20500d44144291298015010507100b003000921940b50106062285815076105403800c40300c6c2071011500003c00352000d40406e40c8407051500410524034a80c400400c0714190290010300700b550348e0045000c084c880d801e40071071802c445007202d24504003640068010614118143c52a2a00080c01e6416182c0807404520703681c242e5460151070465150001c081e1900312950b0b030b000300c010a01c00603101d003202020301803150a51001c540c0340c0c41203400180c140032002490341201c0c9a0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 912927284 1250 912926034 912926039
    0x120206090705011d0d0206121b0a080f0612070608041401051b160602030403110f0106050d03051c11070b060d0305071b0513060303090803030402010203030f131e0506060a 75
    0x9108401044c44100c94040c9040b1601603000300700c03061440c2c3c501940000e80050f107d03048040d4002300300e014401d03410703d41080f20400c1c500e40c15240a0146180c00042406010440c0e080d013554607141c200400400b12580c0208040c88a490110160f00840205000000704000c0c821414400c2c403145d10b0600013440f0b24900000300401181a4001101352903402041603a05015424600c0c48070940c8001b0455590070503040c0649410000c1c1c00344001071190719400c16141d1018021a8211a00503001100d010059641030360350b908140511040490b03c01c82200020010f401a48c440b40700c00d01c001d5a9908031400d002d00c41040040c4071030b004003000804940065440000c441a003900800014808600b0f004032861300d5079070b50720856010708100b0800000c4411036104a0880303201e0b031900c41c441c2c2c2e81c0c0ea41c0c1940300c0c0011140a40542c03c10300000710101c2481800b541d20204442400094044559680c455602a240000d8880700742c079038000d0401804101d81904001c0450f0a00242c2d071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 912928534 1250 912927284 912927287
    0x1d0703030915020a02030a0c090e070609050105091c0b1b090603010b0d021306030f0b1c0206160f05030a0e030613080c0a0b130501110c06072a12020609070501 70
    0x482c400c0210b0111002d4046580610a205402c40c46074010142d030100b60302030418107454505801350200702446e260605402d072000003040002c484581d1601204640351000644242d004556400d070851014100c1d450301c0c1d40c207200c0035201d59100300b2010344903081c102e8860b00f42d040142c400806400c42080713030310240d603074100540781182e0920607040d582e05820450f000107801041c54201482400c07103000b061540d0150808910940000e00c1009221150030030000410585480600401c035070035004005400c152005191829002c1c1201d0407076090f559803059090000001075507113030130108a080b021a4031075403c1c04050000c5008000034101031009000700790b81c00c98014000900001c1c40540340e0010301c40c642c100c50300001e02d15181d180064184402d0011010126500d5180940c241a04a07403402580c01d500f00040081c9130680c1c695006035100e0003011451141c445040c684039113544054005100080c0c41180c1d86130520492000180c80c103070000d44004610f4224150500c01c59 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 912929784 1250 912928534 912928547
    0x120a02061609030f06020409051003050d02031206040b0406030b01080f0114060319030e12370f0302070e0a0c08060a050607060209060d060e31030f18091d070303 71
    0x2660840013524036201d651070100000d10a60707024005039420a0200710001c002c2c2c2542d402140c2c000d509035034504128100403600d9100e140329900600030360340c0121744c4c98102070b40b003256050f10107000091115200d4a030b0002c1f50801340c2c88100103901100031341d010740d682070194401880342201a106da03803d020000030b440b04420390110320340800422540c1e050510852213200d407400094507240240a6900300c1d940c64201441d81444090010b80041d049406180d503030041d9008400d4040080c2e184958544070300303003103405e4158214402c644012520000400860380203100114002500c1d00801d40c01030101503008010b60f11410f0754141c108515141c1c00112000d00398802070040e512002c4a000550038011100170590031441c200300850914064011140111405404109041d00f01d1298825003101c41301c80151042c0d00b0160200064021580144081c64906010320261040c0c41150031090599008400b402e4039a07500760311440f44803000d803100114400207030411605540f0041d084c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 912931034 1250 912929784 912929789
    0x100b1201181802011209060c05120f0108030304030f020f060a020c150601080a0923031c0905030d0f180813120f02090408071b050108070e010206070e010c05120a02061609 75
    0x10301170000030006022005a0152000c154001d00c2007000856040700105590048101e030300d486a010b4003c42c110b002c0e02d13002d190403611740d80021403035030360740356400c4802c2500102048203603c241c80080b24490000e0100310310aa4010317500586840020605500d4105032240f400483c040c00000d10145903032040c040740d41f00ca0703071910100e046952840d0103070f00002158405c1002e40b04183c28200c40a0011000381101d14580054049543c11000510b003240d91100006215a004110118030741045404c00c0102a92a410008410f201c40b02074034a1140e64001c101c6200b100040c0c8400c48292108500001e8a8240c0c01d69a6010503a0383c2d8004111107258080d100700d44180000c1c00300303d204011140643d80c4510303c0400c42c4481000c2041040a030700a03079020031000400504c15a1241e441b003607402005900500e07140d11030007016541000150229410001c49080110110f0000c001c40c00c40b8450402c07622ba070350b86514200a040c00c402401a030b2104a5100035076100c1d69001c08403000f07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 912932284 1250 912931034 912931037
    0xd0b0f10050f0f030103050c03154021020d050412020d050a050106050f01050c1f0b0d032c090103030813060509060f010509100e100b120118180201 65
    0x50b41d001d6107200200c940506541200e1103080000044104000412410107056041d07044854480ca800d6282170361792401c40e040e0b003d500f803040101c0da40740c40404101c0e002c80d0030b2001152000350721151907640320400c4801580e11a100c6101d5040c022500b0030005054001880608046012980014036034840c6119001a000da440705500666075102100103045a016048900001c4a4a0303c0e5000c2c1c2054429588120b01d02408803807554001c40840d000607001c81302426036071880e075429481681c185030b943c841c00365856400c20034a4413507a20381c00913075010fa2100034480d0302c0b1802049a00c2c403210b1012000f00c001031038100c03c54540b1882641525414208050b16030790361030201c240401640c03005800c413820101800741b00600462850b004151020b0b003074a09130780f2071003072046a4109842000d882550310600b008920f1002d019650808090f0082d2038000b60b441110340314982040d445000428000ea00400000c404280b009008100e07850302449080044000340840000e107290107030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 912933534 1250 912932284 912932287
    0x2b0b0703110d0b0406081e0c030321040f022205060d020a03020603041a010b0a0221041a130602010b030d21020f09040507030c0f081501050901050418020d0b0f1005 72
    0x10700710780c2d82e81c0080d40640103110444180204147c81da5103582c03941d08048110b40940c140c0e554680c00c0c08000c0302e01800450f801d004201d036540c3c40411040340700500a0301c210441c03081140040e40c0d65000031b522501c89541050344107441400b0002141c002401c10391180300308110640060b141d2800c40c3d0300b140c3d012100d66480b9501c2d4103000508106102c03403c810164010b001003941071090000e400402d0140d03089946180154190030f05000005032154003405052100300051800492009854149802014100082c059047c1c81001ca1600640b001d41d4540110362424101000100d115034014680484003459031110100b461480c41212501c403500099001c02400195040380d81c3d280c1c2c09001003080f031603c18801002005003641100000c0d00c00d00d800f80c0150b109040c181e0184c5070b201e04040250f400100196101e46c002d582050600c98184400914082c00302050f01022982e44409a078410b00d0441500c00c49805680c400c0c418001e2440c60728258594020742c0e400c007181da06180c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 912934784 1250 912933534 912933551
    0xa1509050313061205060d020d1103030f18030114070c0809010c12081f0503120d090209010909120c080a030507020106210b0a06031509022b0b0703110d 67
    0x264154031034401407110364101c5010016510798031134004001d290046508000765154041008091110100003a610085410a600200711000c034040c1b0300039001011a0b103031585030800310000e50081880f011201c5c04400100d0780b141000e0140694001c0103020185591a1401003e000e0558050000c0c0040d400070488150a9000b405a0080143c1100c5e500982c9148510001c00b03850701124882c24180d8020803100850444083c01c0c40ac5e00c40c001c01400e07070040341450031304007500111070709a1456103a503410005603d544d22450f02070406a1004140b008a60400c540091500c0300a002001025040b840200345240c090341c54051242c0340c040707015107904000328050401a007040001480401c1131200d43c0d103400400207880d40c850951451181d42e1000d007501180c14030b102c05802c1030003040ca1020b00c503d280e441034034010310007094400d040e0410700000e40c0c0303038080100e00d1110303c1d00e01a004080c0301000716041c0d40083c0e140350034045c8200c3c207520440540288a00305100c40d440d903885 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 912936034 1250 912934784 912934793
    0x30319020114010902130e0601020a03030b0409020603010e1510050a0c020a0305031324140304080d0504120201050a1a0f030a12030203071101090c180e01050103030810080a1509 78
    0x15652181040781d0102c1d940c50320f409800a40c0010641c09409013403090000d01d60302c2940b5254072a0703c058010707024049654070107070040c1400d60348440d0310076581c3c5490350050b900c10014601801041c04049080e20b840d40000303480c030317003a01402803241901041c0603c0c1e043c2c0c00030440704610202e1400000c1d9005603c0401c80c0e22250b03400003400c0f4080410030809002d0030b80d85403001c4460320140b80306149000101b09100200c680704050004010007200100411158020b580203071080340160315040d0145982400c840007a40d040314040c1d400b81600062075424001c0ca07401040a136410004404074120b10850dc2c406520f0b1139000d041c2d01e461101980e50300b0f110409100b40c11500c6110146a1344000800944c82150300e9808240070034883e0b100389070141308548050750300c5864000504d081c26005c154860b04000350280c40d07a01d40341c0107110a2020f014550080d40300f525464051b06003ca0035441441c031542000c0019408144148040746c030183c0c031800b516440f102c3c002101101400c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 912937284 1250 912936034 912936041
    0x21b0f040b040b04050f150609060d240b0403150e070303030b040f0e01051e010e0c031b13092412062c0106060305160333050306090601050303190201 66
    0x180031354481d03e402d04104d4164401c1c00c42910841d441401c04d0002140c1c002042241d00622120a8100e031051010041021542c0e002a6442e00802d158194901415400e2015510180c01102200c40003007002c201f04680030f0003109806400c4102030145c01ea46071901603a50001d031001a04243c0c9400c40d9840c00d85407940200d140321280c8a0920100032604544d034080d1205481d26041c1c0c2002c054102c0c484926200c045050390900c86050341a91184001007800c0c1e00082d00b01e280601602c014044512500320040642218903500d84001c1031400c0e40d00d6080b01c14452031034035070001c495104522282091546026100d0760103a1203006100c60501c00d00070400b1607008079800c2c050400c0803010b20480880180442d0702c200080c05515201d580480513168140c694070309003010042600a840d000340c200b502d0040e881202d00650350000e800d00000e0729000401c1e5060452030290501850405100e02c542c0000341800400441d450030300130030361324418490001030703100c8213010001d42d04c0d20070340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 912938534 1250 912937284 912937301
    0x21c18021918051909021c02130203070e0a0b09101d06040e01080f1501060c03020f0d030e0f010c0c08071a0420100e010507151506021b0f040b04 64
    0x6511190b51001c0741c941000030041a111341d00801c1010213074110826590050104007980509403092514144042c0b100301c40800c8412030780010480c450424600d220700c0614890f80f4030341c2c0c032003024203409402d02c042c42d10241c200c685c145004108a5820fa280e07080031284a030110710b0a4601c0308490720102c10548801c140ba542d1100c000580014120304011005040c1e44090050b260301030100c458965803035903403041540309454000b00411506004020711603550b4002c0c01900e840c0380c80312150310300300b582c014440b502190743e41076010f010000c1040340303003013454544008124890f1520700c05020303800080c1005040c5100020040100310f80100400c14061031600f04510301d0500740380c03012040b4070001725141c10303e0340511112402d103000500305170000043c0d2900308481c445c1c00c00440b8513500c001d0003a142d0900e400301801c84c2e10914402c0c88880300001c3c209180f26400e01100034200307041c03c0503200d125122050b541075076507500ca03082c0580480840780042d00c0749244021901401d100c3c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 912939784 1250 912938534 912938549
    0x1502030904090303020a021204080c0d020111011407020c0d0b060409020d0b0c030105040f020306150307020106080f0609160609050103020912061015091a0724021c180219 75
    0x500c00780c20541c04d40c010b030100300c0e141c0d02550b0001d40704c801e22a07518002e5200c1c0c00f0296000d00c4c460149410454401c0c04003e006240c8000c241102095103400c0d54100e41c1100f0340c00d11f9503c1005800c0d9810701c8007034031481c8115001340c2500d0680c0c80300b44115001600f0035120b0303692264040219501e4007100001c50b82d100007106060318100f210100c4c184c100b449018002d90410041846030079a91013103e1041e980107020082c81030340b04011118981000b000103043d5940e600010509040c100541d604181500c00103200701c1c0791100e070041c10035a0221002c0300c03a00300f590b41403140b181c000c3c0c6500e007903500c00c2c60700680745c10354400059040074401d00d0044240c054079091040000c4886c400109694480b61200072400009400300d9120713580340b15011b1101055420131040c1800b05006007811b5000d42c60440301010744071011080c01402c11442d400d8183d0008009503440c503011002c20030003800060800802c0700340801c1008056000303800a1280c41d602c07410680b2054404c1408001d80440f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 912941034 1250 912939784 912939791
    0x3090f040507110708070e0a180f0204020f120a0c090305060c2b0903020d02030a0c380f060a050d021002070b0a091403012309010204030f030f030506191502030904 72
    0x83c5c151254680845e030048880340415a8000f60585510340640e004120401141d555100207688a0b03101f801c01c030010499100c7e408001c142c64005070740014100c000b81c01c660300c00b41400d00c2c05d80002104d5041e00c207401070121115007000030410109045522010911013a61b46032002c64400e0a10350b9003004410103800280b0640900e80718540c000c0e00490702c282c084845901c102d0364207a036280620004c100c0004c502c0310044000603c3c800c0100c00c0102c1203814006036250718000c40014902904c10ba0745010026420042c1a0004000c2a500100281c07003a6001131f04000110300044003450001e4050800c01f0900c204940c03003040f010000f8012002680d8490b45445c0c00144a09110302c160310154001050b240010316043c4290b000324610040c2c0300001c90402d0790322034a00c1d900106000b541e55070a01c0000041503c11585480044c031075500c514144030000b101a00721207010307008070700400c82000b01e90302e1808002d04240649001c01c1d01d80d440c84001c19070480c61032260038082c40d0000c2c01c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 912942284 1250 912941034 912941039
    0xa1802221803180b04140112021207233007080a14010b03010603180501051e0a0c0c020f030f0f0d030b011b29150f0303090f0405071107 60
    0x68054100c032a903100756910719030118042c3c003d0082014a01440c43d071400c1c00c100030451410000640c3c004018181080f515204c80780320b03424203d0f04203d404245000701502005034103640418002c0c80a81c010b04003042d0820609000070b00e50152040810321540340203955102d4403030341401e04504001c19999104240340c0240e00a1040a095032030144440c1042c0030180607496a281d010b0503034403001d28040c196841c010b005ca0240805a04403c40c40300b600e41504040390b000e025151065007001c2800e01c2040080005005464000b04001c0561b490b24100e402c110368440c9200802c1a01142c0600441551100085c148001c460741b018040c4540d60050501400101d40380312a448251010403500c03610783d00654100e001d640382e1100462129403102e00140012440d64441c1c6510400f081050300050794150f44c1075425240e51440003080f110141c2d6500e00807644014191003a0b000d142050000804145480d02e4491802d01c16911400003e041c9481812500141a1804200c036241c43c8e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 912943534 1250 912942284 912942311
    0x7030e03160303080a0c02120313080a080702100207021c02130905010b0301050f0f0f22030e030f01150308090312070f0b010806010b03070e1f0203040e0a180222 71
    0x80d0b03100880100b2500400502103052910031060031980c150041d00e4400a100956030140c0d100400328040124180301c450049200714016100c4400151202d40d0f040c00e102d800a41303030015950741500f0840c0100103060040c0c54400304428020203c0103032580c06251480003c1b014000c20703100c2c01c081450040c0f0001803200542010505140c203400800040d280c1b110001003400741140e01c0c5c100c1d02141c8020070382a901074001e80707a00a070200c84200ca403400d02c180c51850584a40000c1d00020345130446014140b40c02c0c00074440054540000b00700f840e0010030100d012003224480a080554041441c0515032030a1000280010400d044913a84451307510705400115030300041610310b02c40c02400841c500100182490580d10000112411a80d445204840c0800100401e0381c21a540036807484511340352083d5000314040d240c02943c0c4a60a100b850a480c1c40e000340342c000d00303070304014009602c0049000707059142d980550f1481e00e82d405104d220300084c202c01240c980c080d80750034820a0480c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 912944784 1250 912943534 912943573
    0xc02010213050906010f050f130303170708010e071b02030307260a02100221010609061103031014031e0610060203030f01230301051005030c01180b07030e03 69
    0xa50100da85400c01c0c0b40c0729014000040000c81d141400300d00000480101c15010310041c0c04800c1c0c0360b42c0406e250422124003c1030000c00d46d44100d000c6105000c20130448a84030222540c45800b0b480c004820350714150044c4070300030020340900b0510024080d0480841414103202400ba038000e000c1700d54800d11458448440c03080b48501e41019400c0786499407481010344102d420366103c6600420002c0c10b0850180c0081d032200e006001021300740f40b0061840d41c0c0c060b000d00e0082240341c6850f4030070f81c40c2c8040070305941c2d2400d20075500ba8008004024038011040c55100a9680182c4114014804003000c0380c54204164000418684909200101420001425489550200910030030941c1e280b0081ea035038001903d09002c0100341d000140882983c1610906400e5030303040700400c071444128046401c60f50140d03040000511511001d00c89401c0030000c0c16400b1400b0328045203000b02080314021940014020502d0050b4006090014544506055450800c0c01030a50342c0c43d04400107041c070b17079 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 912946034 1250 912944784 912944797
    0xd11070807120201031508150a0b121608011404061104080a0501091a0103115404030909050a02131401170c040303050318030304050d021614220c020102 67
    0x42d003070080807501740c0321104411b0200c5080e1801005a507949501401c0e982c9001401c00c6030095688440c0059a03680042c41c0074440c820402906100d03500d0b0b2408001c008854210064581c10f0940d880d052842a00005034890303080100000e81a00b50306c1100c10300e100307907031142c1c80314841e649240040c0303d8194080d061040c480c42032207410054040071300c005070030244009060440449035440c21030501607420183c00c1c07038130410702c0c3c0300d1a942200c007140c844220340c0405514000d224000d0030303003021850b4422040941c403007280b120316081d50300600c644021701035034100a0b103800115540620766015110703c0d8402000803c0400d843d100007804402004036000d00281d154404141c507019070070181e500890501040524150540e00e00b0390b15984054003100040b103003108654044002400690701651254018145020b4403000082c43c000c141010280c03540214081000240d00303090710541c244c42c084c1c4080c81d188a402080d1003609035030000800a0f01c1c10010b402c6006541036005107030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 912947284 1250 912946034 912946037
    0x2040f09031809050714070609051006050a0b0702030d050d0b030601030303140a150621091101020f0c210f010509010f180b070806060f040b0301091d0d11070807120201 74
    0x102d2035070f10b076100310a0301c5041d165203000c584400898109080701200a09109004000201d4503802c1542c07501d2034400d052076620b80b0265650400d0100d0f00d448540c0708010580900118140485d580004e0340304d5504115490521800103844400d060482e000080980001416a4440e607564103001d40030300a47c0b004c5440c00c243c0a80040d80f107030141e12030044042034610740d40d03c10718208601602d040d11001d19002c1003030304200d424014500940107040d4854881c95604206507554000a0316041100c602010306400445804960b034965138015010380412851100110000440311401c20b924020066015420b01007045001d590540098172082c150310020000080102049a42c1d00792000001b002898040081650390b88151034890700100c0c010156458228400e411045c20360281e802070010034404401001307003041601c6001140c01481d9146250340c00c0d404c64154403203881071100401d101071000b0600030300c48104640c41c003400d5010b003240c1e40c0340d803500b900c0010b0300b4205904a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 912948534 1250 912947284 912947327
    0x20703031406100e090c0c070b09031204062109050a0c061e0203030a0e01240e010611100e030d0204090615020102120112030201180f11060405030a0f02040f0903 71
    0x810600f05103445140c0308905540c2c000d81c80032120f040040c0018041d00d0241480004c1c44094024641886402c00500c1d280207040d80d604000e50074941424074595412001c8030080c40100055500110000c0c0080111074003e600310300300081e0710001340241320028005100349035400c2c00300560205040c0031340e400d54a60715552460351500795141aa10000400103810900100780c01140b40d40000105591050000c110fa40c98010501c145499035101350071821030380901001600401c064850252070300d8642221040082102503030341c1c00700800e8102c18141e4842d8000110b55050081d5464101841c6d0195919030303030b03901b42102070300c1ca600a20100c0f203219a40000d80c070340148210350550400b0030071004980c0c64450402e45040ca0300380140c0965403105103170503146503c0100308c0c9406120342a0701d502c00581c0c0c18111014402580b0031801444104001d1003240c0c1d00040a2007140d52040c0c400c07410003114400714025000c0c0e149001000c0382043c404102301a045480d0b21898041e026000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 912949640 1106 912948534 912948541
    0x60a0302030a05151302210124050301050109140601230a200106030305042c0906040215090a030201080a0e060c090a083d0207030314 59
    0x454a642089640c650741c2d1140c0800b064005c000007807170340e02ca101d0950100d04240350b408680e480c4280300300704001d4104425000101000044076503543c419220380c0e800214400ca070f00030980b080d420302d800421244090f11031980c0e0882800d101002a84416005441c0c025450482645400385d46100c010441440c00044c200300e40c00da0344104020715000b503241030341a0740407a0901c40ea41001d008101003684030040d00c045e1410a00d5180007440c810f0111944102c1c2c0d03280041080c0c1c040380400c41641408a003403440780c0d0098600e054900041c1a03142042c1c400e40f1961540000c00c0e110900155100e0503003070b580100501c1000404001e4611a40d02e007240c1188c0285001100003901c140d80c1c180044800c008042510040800652200410030004c41c0b07100080e0007000b24a2070301b4524404400c02d40501c5a902c403085540da406c0c2c1c01c0080103426070320401c88420f070703010021 = true := by decide +kernel

theorem cover : BRFrame.Cov 912769784 912949640 := by
  have h0 := BRFrame.cov_init 912769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 912769784 ≤ n) (h2 : n < 912949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
