-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4803
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:46:57.255844+00:00
-- url     : https://prove2.me/submissions/703bf1c9-9293-4bb3-8125-cb1df35a597b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 863669064 ≤ n < 863848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 863670314 1250 863669064 863669077
    0xf060905030309100305060d06181e02102604200315060d0201210c020f03130b0c0f120408070915090209061908071b030906110111160b010605 63
    0x1219500360b110320b13064029001140c3c08980a404d001007440e49880b01c40544011200504203080009100001c7c000e09881c1035510001403507614080f40041c1c0e02040201c449142c0900400041307107007400d001c480b158141e5050703c1080100c0a22810281000c3c825000f031030350082c0025a241944000908012481309209054642000810380c5d91509006032111040000c074100005400800030064030400046121000400e0004000c2180000640ba1881e20b9400340e00d1948180000306403180f81e4081001034622507050540c49800d0100e040b49011118004400140500964546401e24400140c4111804c0f41c0440e0440d0359107940c2c05048555803881c3c000061300082d010f200c410000c0d001000020070181605141001c034110078036000c5451000b030000942c0032018841070546c8a8040d0411007480b05022172407090316500a0a0b0003840d103e22000e0041c560031008a40d2401e60001c0c41d00103204000d1aa06c0d440a0074070041030315003030000c80b050a001400810550700c908107440c10f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 863671564 1250 863670314 863670319
    0x1051521150c04090e030705011104080d05070312330f0b16051005010e0a0216030e0a080a050c1206240301021c0b0f09190203090111040f060905030309 67
    0xc0e900e56560038210180c00420301030096104010024584d959441116040200340d005180c4600a62030040d09451910502e100194814842444406400700b001d400c03107012414020790ba2000752400341c81c82c3e06034010b54031110f460242c01210224100c0d0f44140c03503203a05a1400404400984501104d04580c01107001614a0800c00c0c0b104a01c8407000340542034204201010b400070b1a40c915141c4200307494040399054035803004001001c030390f030b40b955041510458292304045014204030084c1e0b9428401030b080144180403c04141c9070241d20902900005d0107481926001d81005079031516080d808900528400601a042c4080440c005004400ca2600e4242c08480d4043c443d50080914110030742c5075608000d030440c014903006440c00000e84606c404038240d01107604003c9011a0144020302070200b2074200030a00d00005501c0c2006800c003080140c498503030081403030041941140c0713010050ba0000d4045110599800140b01311542540e071104c140da01e0380d05040d128080c040310b4a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 863672814 1250 863671564 863671573
    0x20a080a21051206030313031b080a11040c170c04031b0f06050706020c01020a0e0f010c02060a180302060c030c0d02150f040302150712060b0f0706110c01051521 71
    0x41c240666120095041314006049038180302482c3c010300d440340816070003161800c60400c206096620010780c200018203101000e011207400644400d00ea00d407030441c0280c4140d03611000c148209014440311f40c444903c0f40740c0b82c0b445203450a0000030035030090009582d10490400c840c0c01032a260f050480503241d48554003016145001010f56039508440c0c0100d58554080c400660740010910207070039046829070f240080d1280704402d11802c80402d0307100c02d0401403045105405070b02d600088840c03070303502403801e40d03110240604284c03802100c68000940c84030000510003030031140000a84013050142041e155407100e91441a603481103552001801044c81c80b000600e001c203881901a072080c00382c01962040c2000002c0d401408200b156030b203011550b03100c00c0c40340d502203622072240681111120301d49450075503405020503015500c00105965200d56141056054041c15140d801c44400001e001d07909011145900314101003444500417003a0301420191850580115540314603c04080c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 863674064 1250 863672814 863672827
    0x250801180e102d0e03072904030201090b16210e0a0602280c06091a091006080d140903010902150d051506070201031a0d030201020315060301031518020a080a2105 71
    0x4160030441f04140c00c800d0b507112038015400c40c038102083c0d03100f01d00c283d00000d40c92101d0700c0d2440303200350098041c00d01195190845e0b001d498110014101c1c000d5010510601001c00a06120185c80034480300741076402078401032010441715070003a11081343d4400d0074144c0c3c5420f030041b2042c4044062900400900201a94001716129501c5842090700070204040f2801c400b11461603420816500c0e18510f03407294680c1016541103105020281c03288101400c0161441180102000c030700c89001e91000d00000b5505034241d50035488031416550290400c00411410301c04400b0030303040325629015042c14400050003610f0011100300103124001c1c4624104442900114020400e0405821299407401a800d68583e02d04000300541d9101c0d90004d030340e83c5045600500e00d503001c2c0280c85c0c0600000c1c00180300041e2140900702400500a20008030343ca000385080324820007180c00a5005100c03a0030100d015680030860070b151a01400184481d0601c410500e00d1703ca01d0101e80c04000788060064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 863675314 1250 863674064 863674073
    0x21305010507052109120a12030e151e0f070f08060603040b0406090c080a0c090b011e05040504060b04060f0207050a18060e250801180e102d0e0307 65
    0x4003140d806421102d1420520110081411103445030106c441d1a400b0b05164130400c040301914007065a118603050110311040284a07035900360b2403d84000c80180000003403200b10000d02a042a10314100034040c140c240750452100c40300003581c00100245071303101035200c0a0b000f4010207019250150085145990310784880c1c003013203005042100c1890f215140c1c030000c1022011404007600700e003005405035800c00d1428070007941d01d65200407074660811041d541aa030f00002c0c0e00c41003c070105007400400342c10443c11601485a0b800165210f13107403403030204817500d15a02410944600b5102d9039010003c03114141c5e514200d9100d550361001300c0e040c0a0010082d000c0050398415441100414038940718201004851030403101c0f100d45400d0f07400680b0030750941c3ea002c6c0380160030038141408594102404a03d201400c0042d08261581301c8200003026002000b01c82da00c20340c088020407181809880204000040070f0342c8a170300301c8081300b4511542030a407046860700c414400c001c1d442c04400b9031b02d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 863676564 1250 863675314 863675353
    0x623190603060f090c08010e1509010605040501180302090c070c0e011401092312010221061f050304200d060501030b0a1a04050a11120108100203070516020a090204060302130501050705 81
    0x29054445274649032002d01600c601e0300740c501a003e55120580c03a617040900040c40c405080a5601c160030171200108090384401e050380b03400c46010f80f00346030380d1071650515400f80101a032043e441c8468400c00059001c80c9141c2240c0300840036620028507907640c4102e60024102c12001111104007140702030054540000071111207101c038000541091011002c00c0700c0c012481c01d81c0307404d0b2191002000228504008829140302010700b11003809100000000e0260200a10040400c000f810103142103280028514103811401407400705000c1c0a46801c1c2e001e010288400c88035580242c1c0801d02c80c107123038080c103000e4103e0202000414105401084043c0102405c1d118040d95604a45401807401d00c005104c46600b00c01c00c41041d500d40400240b03804005800030b03a441d0301c140140b048159024049a0b00c02c000030300c40c2c4400c08160f000146401510364000c101c030500c0007400141c0c1035010340240c125000c181d0206418140d0342c40040d95603100f109401001c0d40c1261010303c9001c4200c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 863677814 1250 863676564 863676571
    0xc06070c0606080706020a061506020613020f090405100507031148060f060105090f0109090203070306170d020d050d1e090b0a0623190603060f090c08010e 68
    0x40302007801c40d56204581c0c105006038005d900140c00403041070040c4500fa0248050404e241480d0740c56052802c00b000352105805407680d911506a500003009540e00c1700925250f14a0052164a50303013010301d00719983d081502d02041008d410140043c80541c000e00c1129420003503d110780b031420419000388071051620040d8030244c4042d0103034601100000d10b00990312001d00a6114020026101141c0d2420380010100c01c02e02c0c44000170454640d0b404001d940c0c0841c000c1d24240d2002c3e0041c0010f9505ca5001e82040b44814030101c20004801c0c1d2503000f03101213034011108101c0500d400c2c241e56071210116800c00c80540d00c14a28954010b1250000b4600d0402142c00091142c2d0100c0341c1c071000308011000d0a0400c3d44420b120828041c5200d511030304000700342401c001080c07030000e200700c01c2034101c00401c8108056036001d2641d40c4070900040700a03421910103100d00d030b0b10380c840500185071900901d44040d00030b65022515002c00c2c4070301070032f0314416100d440e0640c1c0303800c044100040009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 863679064 1250 863677814 863677823
    0xe180105060a1e0e04030509240f091206070801140a03051c1407031e1d040203060d020a0f1a07080415050405090a0c110a0c0504090303020c03030a0903080604020c06070c 75
    0x200e40020714184c11000240118880e41c0d84560341d403800410042d52a0004ca600301e0080c0e8014aa800680420300443e0050047c129540c0c5d06c441c889030005441242070b46041c0d01601415041060310307980b0001c0b06043c0c98100c01c4192400b4150320030300944d411180401819948280c80030f200d145210640840e106480d80703003008039000c1048c6248000c1d00300305030072004580c01d9403007002500c4206821026000d00d9241c00c445e48002c04030740d000a00d050303442c04c2c0d00881d070000110300c841d00c409002001142e0042c02016282d0b645001c00c031111403a42c410319030001c1c074013048a01081946c600301c90800b900010850f00b0581418103a440800411001805000c010003000969880e412a414440d040140c00096007060303246029040301000440600540c014042030400a40380d00e15250a031881902c0024104501e842d09a0082c418114151190700c0b010080109840c0140c10286c5940e100350b0350b052094071a0300921047e03001d01c2040e0211904000005040d01c2d1041601c60302c441c0c083e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 863680314 1250 863679064 863679119
    0x2d060902121c08010e040b13051e0f010507021203180106032012070b070602090a170f100605060703032004080a1b03120503130b010e180105060a 64
    0x185034014034141c041082500b003403042100e040540341c0c22030350190040802610140701c81c68a95140343d501c4c40014100704520600800e00420f10108005030300181d00c44882c020705280d6404207141e079aa4603031141b04241d40c2480300081e021427000c9070210004d40d007040e00c181903840c0c0c00001a000700b42900603180399035031b6000c00000300d002000740f44c420082c41c0003003450840e4044180614007503c940c4041e0b180e40300400420900d41c0c21422100310381d411950040c3c5a104800c0041c240042030743c0011a01005a0250182000c1c08198803810b11114401c40d0740b15940b0070320344030980d4030900c81e01da4040000d12480c40801c1c000d8000030007041036100803040d4000d000c0354421a40e00140c1083d003265000614a40402c406c054040e03c012140301c00a0ba0303260300e582d45040c0400202d00d8508200301d008004108030404c8c3c1410750a403203034007019102444d03865a2107000da0f03040859261038041a0b4410103070b40542c4c1840350034050072028002c032807440d042000300280440361580f00e1130a03000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 863681564 1250 863680314 863680339
    0x609111b0a021c1112060a0c031401031a07080705070807060b09011e090506030a1e050a06140115171803030f0402010807050a0816051b01092d060902 66
    0x1c1d01040841d5984210f011607422000c1e0741400b044102c0c8621102d0b02542121002142e41c5400141066201c8161000171542d0748903244100c028022514107420400110780022040100800b000b2810100b815210a00c0eaa40d5880c12100d4043c10380e41c40c0080340041201c5004506032000400c0b0113801020045400d450389400310310340340c0c401d138420187c2c66a010360310070603424809401002407154010502c043d040100000342c58840c05c2c2c000410313040c40011030381c407185541864090301c160408240e4400040502780400646202512100c1c1c0c0c02c0303082e0010500b0200703842d034a00300c5051692902003c00034810035400340c4c000a442c00301d202c0280f0040c940c400e9010001940306c0c580340d0903207080905243c030006d08544005070a4000740082400454032580d03000c4150355021110307807082c0d43c0000815030285e800d4401c1040d001c80d0540c19400e150f07180c2d101500071981451013911041d00f01c1440081c1c0301c10b4035240d803038408030f8511b1000c1d01c03101091440d040160568001003815960300d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 863682814 1250 863681564 863681569
    0x70c1520070309090e010614120a0f050607090b0301030f0b060a0b04030303020d0c0809060c070f0609050d081b0f070c08071d09010c09090903030e07180609111b0a02 73
    0x1002074030300300d0001e00a8203007801110344a015008103900744500034050a42040500c2064101d1f045445010300342504880862441c100005080d540d0043d6100311820000c3c240192550000c9a150f00440c03005a40011808540e10850703040342c1d048003072a015144c481d518010014005400c02da0b001040c0c0c14082101c140d464000d0004610a890040c0e0f11812803c4003c255002007003103a040c00820380070010110004522a54006c1100400c0c580e10a0a45041c020340d403680c0b5000b420891828454004200380000e41d80400083d03511807203c980e96401000d040311240d02d1f0031080422080c44109100902c02e00602003451141d4800030015482e0040035145c03003100e600042d5010500d00b210080e0b58841d805540d041901d441c02801406500480645100f49a108014440d55504205010b01d48203074000300c4000070540580720755955403e800e85540450840440c40545003003400940d2509038071943c42102080318241e42044040b141011034010001c0b0345502c1030180e0303803414006030b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 863684064 1250 863682814 863682817
    0xf060207050a12020a110603070f0807051e18030a120f0e0415150c020d020d151b030e030c1b03070f0b040f05040b0127030b0f0f070c1520 61
    0x1070103e41d00500b403481960800034110507001c05458029034042090054050740020542c820a80034284800d5507103526a04551912401c442110641d950f100840208024903004002041d400d2402c056a130084100b0140c4520440c0070051030110f100d00f01214103801524900385031141030520102607030b02800490190303402019804005c40c0000010300c121482481c250303071903104502d405800c0c86207130b50100d06801e203840000b0344100389031070075442000500c030000c443e122030344c002c1480009482c80c0c110011806d00c0ca14080401d09200803202c1d0400000180d500402101c0000c20700e5005a03450740401040d030a12054140c06102404a00101548130041c010103c048000ea0b45904c1d08504981e2080c4940003030307100b5800e0501c2003c030350303910040a0b07184c000104a1030010003408a6109900c02c0158401418103201d101005000c90100460f50b00c1000b010b0031503169036950000c22984407038803900041690014080741d40c050111603200311215050300120003002d00c3c4030606007905 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 863685314 1250 863684064 863684093
    0xc240405030f0f061f06080a0605030d080403021009170c030903240115120e0c0d030815030a2d0b010e04170c0a0f020411040f090b010801030f060207050a 68
    0x1550040d202d18902581c00c001c450303400b45101c030684c000d00c0003038481701203600180d102d040100103046020400c2818280d200030000c0c0b80040403a5110018820b019040700310032101500980030b840007040100c040c81c01800c41c1c03c1c0d444010b0902c0154017a1030024103130070685510019100a1100d201291002c00018108403400d00a84018194405426a02c60f01c160003000234a040d00c11450038043d04000203030080b401071600800e026004400031461b16041c42c410b598440205580075003410381005085000c0c101140119a01101e040306260790b40b042644001c04007012000f44440d07510803180004807066a20700c8560340c011326501c0d60b000d070ba00207030003030344e0355954070f006100400402444a801d00d030f19031420b0300c1c140107294182d03d07281c107401240070700076081d030b1101e050071907661354001e035808003080d8500b5840701d0310380c040e400a882c0b060090039181460580c0c0e038491503004900b894104c0741d0002c04074a11402c556a410b000e0b40041008540511030544241c0c001344001308131006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 863686564 1250 863685314 863685343
    0x513020708090a03050f12070c21052d0703080a0516050102040329091213090213030c0b0f0405060d09170d142a0c0304140405090c24040503 62
    0x5902c258203514141141140c47c9400020100000800201200035060448a540103145a0703c440444000b11050784842c0041440c011050001c01d51500441940e901035040c854440b0004102221143e4039680c03800301070002d060a0149130708480c4100018000008034003615580e141c03480c1d40c0c40d402ea821907042102e01c0010101404062039070182c81c415501e00c0c80e00154101c0c1424294231780c031030485207103015202000050280a507490340d15058014074000004540d1034102e001c010600a01c0d134007003124030100801000900c2c3c1104401d649141c10100c004502d45031800c020889140e012006903249262292581e0021034014000040c0b400c586c02901030f500e2008000100c1201c904d54024203441e041c0c00e06004651407448207032000405880c2599510481200c2540311038026500703420710b0703071000080104603206440360081104c08299000c0c4681c4c4c60398075007181c50303445c034610f440c0e0044010620401c50405054a4040e141050f0705024074050700c82012908190042d2079048 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 863687814 1250 863686564 863686573
    0x2a0801110717190305060402090303040f0e130308010e071b050a111014070305070c0b1c0606120f0b040c0305061504051e0414090a15060513020708090a0305 69
    0x140001201849000110903081c02d25082040c0c601c0d5202d03800a810280c04c240c2d88130000b80e0a07840d00d904642d11010020106c0c0c1c0c50381d07661501a04d40a80380e000c1c03ea210082d03240070030404030325690b4130620306a040c1c503400c0c0b02d60308180c04441c8003900208030b101040fa0700c85000703644200105940702d006002d10042c11003007495003000380f5040c440c0c580387d50061140d1300740f0408680d807000e82e1b4905c84005800495484030642003ca80c80d001c0c800000d044c118180070006440b9540100504840c003603a006054503000b001c103203070304450484c0f081c48041050386291441006481c1d105c4141c1a240c900f0014020a140c804213003101c600e011003402103a034510620640f071828a0001d0046030b1038820103454941081c000c5220400100c440346041d00860080c0c0c2910340d119008001c400711b07484205401440e011121542d07aa002d014141d91416042c06084542c032520b0060409580c005408030707100a103030340611402503001e01404e9841513000e112205c516900c09034880c0003036001e00c0060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 863689064 1250 863687814 863687827
    0x2060d020f03062806030b21030403050c0307032d0818131a06070507030209070c03080708011511010e250e042102151f050901032a080111 61
    0x142c0d20103880035500344444c2e0091003d80c1c10100e01c84290a81d000c0346008035034100305a0104080105035000e40c0c0c5041d60603080c040c4005000000360046074011400c841d0141c14081c2450384480c400c0c00f0140582c1c20708101c0003c0101020281c001303074080f00d00c02000544480d12401c4a640082c00c00c0340f2407030b00c100034048551400e40e00d00d0010200c0803004021910201c889050080480700342c1602a1401007204c00a00c24103100c030100445c3c001d85210a80d00e01641c004045503950001200401c81050205100300e1040750480d041e140050500a4038094141c002d983c01e82080d88440015900d0f074031083d10301d44e82401031100c000305060307045d903031040414041406100c0340e420014981d9200390800c00422141c82e00741180c0d20780014040e4244110000c22410003842c003c00100308a03407034041c8201c2d90150381340d0041c4007142d01002d00e059034680f01041207440d000e110142000510f0444400c1ca0b9100000040d110500a0918441c582c4d88224860a45884041c10409a036012940 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 863690314 1250 863689064 863689069
    0x30d1514030114011512090507091404050c01030209040204081509060121021c05010203130c08030a05090603071b0803070f0507081207120e030304050d0f080a0902060d020f0306 78
    0x40103058282100203000c403421140c02d2501e81481403040c00345001003603514501d0240145486500081648410b0108401030308080f44e968140e4407515840354900052420300350b0044d030045000301e5002c400303041000442030046000e0b410001400b03600582c2008002040751b000c220860218080d240e0740c9155181ca80141410b000341644041d8070f554011060701b151880311071036115029411220188140c4044080f0b009410396088000d00940c400014428115070400d20059503c0c85840d1280b240c6d6150351104e074981c06418801c0010420074440e1480c0c615100016603403084051400007007914000e0046007080c0309101c0150741c0c14400205204019902c119000c54104580c104146020300690f2402803902c210704809110300300c0e14022030040f6204850b0103280d0100d401007480342024014030b01d5102d038000e58044650b4492148000e0200b402207140c2d500c5130703102e92503502c40b6070740d0003407041c1c00341443d0041244d102e4010011816464102c0c800340000d031010010068903171610303809 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 863691564 1250 863690314 863690339
    0xb10120c02030304020d080f1c050a0b0109120308150d0b070914011e031b1d19121416060e01020708060117070b0415020d0c020a03080a02030d15 64
    0x640da0864104000b00300142e100c0c9445101100e80c4030000c0d41e655405036400850a01a00c400700744000c030340d0b8110756250107042d040304c2d0241150711010420420303420015075096a0b10301c5a10350f01012220940701003402502c00315440460f05c8806071a11070441c000848001502c101183c028000c681400001c603841103c080180200700c0d1010881c03041140060544550040c000850b032100001003044140b103030308001c60308000395187c065280d4811902404c222001d1726200101d00e403000840185203002c3c0041508200c080015003489400c4c640c04011000d1589d034281c8c1c80e0030070703003020201c440c030300304402121032070341d6000304d64110708110000f4030a07504420380074110740c400c900500184402141060440d06845640b00400c41ca1074129414100c440d0300a83e030414011400003541455003020100300040c1e0b46c02d841941087c100245c80c0254a01d81c0a034221104003001d01c00240c2401c01007500c103042e80120381c200000f03518200d040d0350a122212180f01c000803010000384601c0314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 863692814 1250 863691564 863691581
    0x5180a080a0b28050612010e03190302040b070219080304090504120203032e1d090c2d130e0a060605040216201801050306070509061c0b1012 62
    0xe10118020b402890044000d003c9030340301a0f840d6441c000700381c03583c1c0c0d482050607407480000000c5c000d5005204141e0f4076030300a4081140d407c1b1040e801414818401c2c82254280d52110304103d061042e03680a10610054000000b100301120b01d801140c0e0010400141c0000c240b86a0046018039091500c00c07442111030f0f20610a561007403003408405503004d60039808000000640b0030301c074146082d1040280045a2001c00403035000108003500081403900340b8464040c14084407160855003090140100d103007000030032003030320012100110400e0035040302c0c1c09120090030190301101e501180750890300b24031071411540d8002c80803641008100e014442c000c01c8202c0d011410803d02a401150071305252000905080b0be92115505c5105699261a0350400181c000380d40c810080d0403202c0349180a01410380b03e440380000081d4030602c144210b494424025020a0a201e1100001c2c00d42000d001702c91518640c4903501c40700340342c40344036000101c0881660355000540010320400120791101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 863694064 1250 863692814 863692831
    0x60f04140411070b0612070f060804020f010c030203070605041a01090f1526010e030708040602300306040f0e033610050f0d0c0f0f080705180a080a0b 66
    0x140300001c042084e128689512200c01d4514108946030b00d58074030b00301a01c4d90400d0348000042070000c02c1c0240d100101a00c0786100b034030511550142100155040300b540300e03000380168000c005e07050009003103401c0b50713800600c20440007011403080c0c4442184e50703800740c100b1141c01da961a03400070468024010305014846044031001d6460a1452054548400d001c9802041071021400c100d840001d6009079480c0c0035034005e880e00d9115901e00b8181c00d40c0503101c1c400061250008082a0445881807505031401400c00301001c0002c4070b108160940000700340c103502030350340c0c42107060040c0302e80075010061056102840c0d5034054240010403241c5411007001142040312400303c1096980c400640690104481c1808182042002203425115861102605401c017003601c0c4400f41c0236810004010800d500c03441340c00d4400c2a0215005035481304013400140301800071400f101d00400080402c11103051340b5642c001103540116030805d80380e81c4010340c65032107113000c8014400440c8580b500304150f07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 863695314 1250 863694064 863694067
    0x6110114091009080c030a09080d03050705090904060e0d021c110a0204020306150f04030b0108030901080a0b030a0f0c0f12030f0e01210905010b030d140702060f04140411 75
    0x4100740c141e50b205840c40341d074820b0703544403003440a001c400d5050345c1c200302000044075550052000c1c0284403014a229441c40d6100c0c1a40d20101140240500351003a407065980c641800311410800c042020003138820b0301c40c1035652001e2003203524148008404545207030011b01da0324440000b1008061485c1c1040e03410007643c40c4800214440114585400396011900542c903030b10703490001450f00c441c01c019101c09035000900c4802c51449000030b00100c9004403894915031ba615400c603612403080b00842c5000645600000d032120000c0c0d07012601204001d0100ca443d56820369526001500100b8161485260031908020302c8000c0c0076504050421240036056035a842d80d00681101b2011451105000d6900e2003140703541d100fa0132007089601c980c00c42c0180d030a82404000c000341a0517070162819400d213804c0b6005410005143e02140302c0c1540c034510784801d50340d41d0749011b800400c4102c0e4081020050207084810f0300c4060f1000e4000009081b0019011604200854030000d162990502c1c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 863696564 1250 863695314 863695321
    0x100501030c0509090c090a08100507080f06150d11091215040809040213060f0212040b070f0f060203042103110d0b010e030d0306030b0c040509041704080706110114 72
    0x90100a50f501100c05544900407030700c41c07aa0721180303400340d5003079242c0200c004240010b9503000001c85c000444020720041150351154401110400760442c0c0300202c60071300380007048441c1030414990201d4103408002d18141034406400c0c505840b00c0141903a101400814410104c3c40c08001104050f03d4040040c01001d0907004a40130400b00200701505040c5e0100b0135a03090384498040b1125042900d5100780c11603251480a000a20b4a012410044c0f140810701d06107210700808450659803484c01e010304040c01c3d07646802451042280450b4003090843d00400007402500142d80207500c601c8a40a85141c400004121500b603070221038200340c100604200c0c00f648450486a03a0407640c403011401198920041c1d132021691289650103220329114003527601d51590200040e80d1240341c401c44a61a4002c0c212030b40d000718081d0030782c004100804140000d40c00c1c02d00001e0715025107181800c169940038540c2c01c006150b40400c02060425100074248107080c80707186070710603c9940701c540e54203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 863697814 1250 863696564 863696567
    0x1103030a0206060d06090f030c0b07030614060a0314040614070c0c0501030c0e09070302030a150e1513151703070b0c1b03031f06170a050a0e010203040b100501030c 72
    0x541c0900083d01801482c0c1320642800b4050b00070340c0c5050340240c40700c03c01c4041850010140c514128041d2110380380400400c034004d100f40144801c139401d20242c4004460030408101484e481a04d0903c00d044d44e41512601880a91460b80c2c441d07409068006401c90301d030304145075503800c01402013080080c040101000580c412104000741c0b4428a00019400300004065400e01651002c559010401c28100302100e50f05400541c81071034814404e01c100300c4454400c51400d6230754000c40c00708500307890015040161003c001525070380010a02680c1e089002400c1007101c1c42e02c00f42da0380219922005110506083e494100e0b4402c420008500d0010b003501c41c07180d02c0b1001b4003c803129410000e4440312506820001d00003c140ac10300781c075039906000d150304c80ca180e15043d9000340403103188400281240a00802003a449202411403480e0340d03148403410090000500385c8581d159180810788008500b407000d188110b228083c404000d09159a20802440f15544014101801c0c07507a000c56aa = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 863699064 1250 863697814 863697823
    0x9010f0501021618090c080a05071a0c0604060509070b0414010201050c030411241305030d0203041503020702040f05340516050a0f0812010b0f03042301060b04031103030a02 76
    0x724540c0000142c050300ca450130201b88000d07071744510780c5481a01d040d80c0520402080020845080204114146001d10240c0d000b9008180b00c0c50b22981007400041d01061480c0c116035400920b61003901d950b151180030380300036500240c0000410509011410343d165809109580d00700c5140c028280c00c5150582e2401c0b00c0d0201600c0b2103000e0890004484508080c0702c400c059000310090315141c4a00380e9050905c5e4140c12840b50758030a01c10400e8190b500c600120407030b01a150401c2c0c0c0340b418040c4140f0150060351004c00121f03040350b519050710b0340c101c0d0749208440c0101e1002d591044008429143e840c90f08404605090031070f41c10380c119082d103d030400121003846074010310010110440e41021350030110302d200d0140088401304004820401410018000d2000e04815102540d0b21070801c01c5070b5004000b004c06644100300081004039401041998044a803150400c0c00c0d50400c01d07150303003912031030b9110400f80302010806004029026038205020030042d001113040c08220f0380c0084d500c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 863700314 1250 863699064 863699099
    0x1a0f0702160902090d140c04060509040b160507020d0305030a0c0306061e170c1c05014209090e0a0803070809030c0d0f030b0f0a030210090509010f05010216 69
    0xb1603070000b4202c00d00c0e102c60198105403504001d0304950030700320817009520345110108143c8558600100440e0910b480c52002d40680c2d000b454012003a03a40007030075582d4103c110300e4442444bc080c00004010380d5050301307103610103100e503440030740728201141031000b030307031345140b108401c0c10708042041c41050707800340038541c0b00c03000e1100c0100c41c2040c0c2101078034408036202010344001441410001e040114134024001e210707110420030300c2e44151148050032240c1c02c2c043c40745a4070f0300d0b215415a0314800c00076083c0b2542221076610702604180704200d0304001c1c03421300a000c20045c0500304020645407003091186000388014000d001c50030f660f1218035100041c00c2c1c80a0049000c04224440c4c0100156045aa40c030780413071395480035040d0003074400151f001c450400642882104281400c0130000402000070281401d000c0d58110390800144034003a200d20b60803c4076181c0e00158994550001500800c4603000b03403105242800002800c00348640010011105138400402c000c40e03144030036610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 863701564 1250 863700314 863700329
    0x19230a020a12090f09020702010e122116060912051305040203100e0108010203041118060909011b050403060609050108030406270324050105030d1206031a0f070216 72
    0x103074244a40030356010f6455042905660b48852000c2540b0115a0040c07031094000d03240c111143d0000d204120b0308070301d6106000d00c80d0300020344142488803030030442d11001c0e141c038030b155052990601480d000d091203100183c9015484620345010304c03411a03ca5801c4000c580b4216191003035424420505050504c1414015940040061034090301403040c0000340048c030204002030751b95002c64902035001914140c510811a02c4451050314015907001c8000c0141c404e050030356695002045401100105400c80310754031142111100b59030703450340340c3e102151030729055111821400d0080403900c040d00400d0155103840c00501c00070f1800000e030350850341549005100301402526010303000300034a0200e91082d0701554007104022109002c50342000c02403420350340c0c01c03c901503450181c600070b205841e00740d0030070700c200c60110380724061618207443e40550116826a5070780d5550304a41c43ccc0e070284200c1c402c400c02802140541182981e0b000004c52000f0500203070341000e40035a80b01079205442 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 863702814 1250 863701564 863701583
    0x2010f0e0c01121a091b04062c090c2208011a03010b0d080714150103030f0804080f07050f0d0e190f09021c0501060906020c03061e060619230a020a 65
    0x10b00800c51003009a040081b1040b00070340791680d0b2000604126000000e00044003180c0c00400d2412000c9000480c202d00b000307003550066191070751030040603031000003100c0202e05045482c024007000211290010000078000080e5280010031003103070341601c005800d100c1c0c0d04020716805103595006083c050160400c4a5660360b10b40c500e0001038041c0a481c5594081c0124100c200d0500c00b003104940c1200e009440c0e10700d101c1101d01c01220000c00444005001680c1401115119450000a414820b105070b0440300405524400d01303242c5005061190001a517100790400c03281000024800011010103450080354200b2400540c494040d008608002c0d07400701d45180e10204400c01000400030440c001c003c507503100c0c41e00620b510018007071813026200e142103006150800140107446140d4480120500700c80480943e000340b000a040c1d6a8840310a2100c55040c0d02040c0c0c80451880407600e84050030b40d0300940328814081c012135244418482446036003102034001c40c240c811241d01c441040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 863704064 1250 863702814 863702821
    0x3010c09150f2001090c05060703090e070309080d1d06041203020d020909070806010f090b0f16051f18050307030c03180b03400302010f0e0c01121a09 66
    0x102c0750120f01c4001031008464201e100c072074000040d4050040180540c0001107402d85800c1440304c1c40c882c1510013800070b000c0b040d04000c0c03181c2c003240d01c0760404440c0c5000314084040d030300c4581540d04442030a00c5d007255100c20000544003000e054203100c4141c4070103415685040e482d0000c01484489503003080c11740004421000c401d9941c1110100c5000400441050800710402080304e01c0c204c401c540803032842c0404001c0e00f401031054500311203e04000502d001590f110b01d5200c0e410110090170f00ca402101d08034006003091141c10b0080900340d40e242c2403000c40201000aa03170711281c0e112038000c528007801c000f10b00301004991503180c05040c4107444801034030f0129031120400c214040d0604420b0000310301100321000441c0240e0808031100c0141e0300341c4485c84442c0303003402011108080c811004c0c40501318040c079959945030180c00002070282c1d840c1c422070f0035140001414915608030301031140856030081440c0e40103040029080100c00501000d400b8460395070380c0c0c100d00c5007040380f000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 863705314 1250 863704064 863704067
    0x9060b0a030902190b09030d020105100302010c0c08010608030a0f0509060306090603100609150f0803120702010f06060507030f02150c160f0c0e0141040c0203030603010c09150f 78
    0x307052044c1c00b40c031581031503e0340c66491112580108061500c02d0042c0001509550b01c14024680584202d2150091041c99680151510381c001c0504072460010f010001403228020301c110350080c0008070165a840c085040001c0c0f8104068666009210050000c1501ca03120802603d80c864004d85a4038480d423100c1000070320307240d0f20300c1c40b009809051040110ba442c2c0141c208112920b144020114156107403444921880c0c0c42e401204800c1c1d1091169020304100200c0da160003c0003800002000100c40d002d003800e4400542041b80422800a2400e00b01075109a0200b09022a84041c0c0034000c21204204580385000d0488218840046001c040d881110345940310314030f07400007050419140034070f05114005914400e0b4030701070101400005054a045234410b290b075103c12500301c00000b0b42440c0b20540e641c68a2130500e05800700315240c0e090b44a45c4111811080d2680041d42c803864500105800c1d1440300f1400c904000711484108001100380116a41e0f20b02c03141480142c0d1902d0f00130 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 863706564 1250 863705314 863705329
    0x3080114010c021221090d1101090806040305070c140108011509121a0c03090d2a0609110d051c03020f1209070b0a020c280806010e0109060b0a030902 66
    0x658484c4504074020f00e0704400150b000b04150804500c031074000c0c035120240d03031a8000c00d48491f402004550780b01000540444014900b803038141040300105850340ba0306c1c0d141c0031003100d00310042080050306800788011a40d80d24010a40300356101c4040b260f07080020044072041c810b84400c102404001c0b54014007031000c0c0c00c05450500c44c4998102c485047c018070065440103480182042a80443c12001450701107a10a080600003402c081c1070403038044038580c00c40c81b0361031900030610060040140c482180800114010321011621460904107082c0b00240f08181034411014149a400020004204000c15960401700911542803104040d0b0282c4600410103907900c000140000d440303010704034142c1c000c8626504071180c0310b4881c0c0c280e03c268803640382050090380c0081d41644091901503000c508904001c030882c2207038885655040e211004070f8008903810340203100180304103400e881c42d43d4010709904205110b4540390030400100391044940e900c0070517448101c100203545540c003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 863707814 1250 863706564 863706587
    0x60303230c01111903020c071404060e09010c030f06050307030b040c0e07020a11010e010509100306170705033c0c060f03060117190915020307090315090308011401 72
    0xc024004009000621100c0d58458131076003203402c0c2d80882c02c0e94a581300f4826288000307140c40080a100e0b06042e4568290480b41c103605130f0003612054007050090b50308031142c2c0a4041c0c1000440c144100c60002b500b82d41c00b585a0049240c43d0400802882d40d0000d4144100d070380005c1c510f10282c07a02e09060301415400d420510102480c60f041c482542c0d400154104000e0041c40c50f540d00c48000300c0115500000741c00e650b4001403060128041501c0d04610b03481a552440c00c0002d80b5998490082502201c09070036100b568200342020029810184504009000191801102c4c0003054924480b081d07004206d10040c2c8440050417015241e04020002e65070f03030020041511408802d9950303072603510482c0c42600140100b000102d0100d41c00d200c00380502c94603204207000c1e00307040c0e00400003410b027040143e41068500c43c0e41c1d0071406083c8011400b8041301d0762503100080c1141000d0801001c00c046210300c40e450040a400481d600845203819181141c1076440090000401200c01107030780d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 863709064 1250 863707814 863707837
    0xc05040b04180302031c0605060702040e010e070609050f0904050d3c0f020307050a082104050109170f03072001020309010c18050108040f081903060509060406030323 73
    0x20054003d154002001e8030840705050343c2c031000d5940300c201100907140b00f0b1050316080082808014014549504419118210000001644400d140c0c455103000040d60050700410100c443c10700517407c02d1700f41d00c1721104056400340003d05055030760940e9140418400d17000c0001c2605154450800702d01d0f4410054400d5a41e002e0040404c00081c040510034070660340800d00040068a01c00d0001c0150361a0507000000341c0401c01075a200c03002964040345825681d202500c414801545035103021900a9010700000030341d601c032500c0c214003c2d405107450480c580e4418031021042d60741c2842260345c04100d524004031240cbc10700a0008955000724410303191940088104018600c05510141e101b448503a2122984102c0c0c401c1c00220700010301a840c0024414400580854484078805150912031243d0034038040f40d0505a21003040d44150001c0040d0302c1340701c20409490094001348e00190304031030070031034241746540242c41d200104018540184102034001002e034495020b5034022441c030b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 863710314 1250 863709064 863709101
    0x91a0907050c100c0c12120e070509010801090b010306020703051606020a020705010e15030c162f060702100c20211e030c0a030e040b030a0c05040b04 66
    0x1804001e01207422982050115100e4207018049051840c0100c00b8104180d4651803c07203c40f03500e038000404550500d12044c000182c0740b1602e0b00d01e081c4502691113250b41c000c2c0510500384801c0000e503e0041c1e20065060b81080d03c40004500b46492940c11694032101c01a5540440e18080d03805016103600643d10b000380143c003106122843c0c005000403019035080d94080760b150401901c6114603e0b25a50b08071200c00d201021b001301c0d440c01150000f50b0001424141103800003008240030030044100d50319071400308000100a44200b46410014081100354003203800c000224606000380c800180c420100d19000c032a90600440c8a500c44a4004103100451844040150309120030b140c03e01e40034059900c0301131011010445003205030200c40740a40009964405130003c4032100b900442c0203800f0822290003030130001c0290042d414840d0b21203244d003d409904200407580845841400b80d0001c92902c0005008a20100195001100e00044104024011800800c10310800ca00d50091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 863711564 1250 863710314 863710321
    0x1020301060903110109261e01020a0912080f090f040924020c0304030b0601140d06053607091a1b0703031407152c03040e01091a09 58
    0x42c00004802541e00455071408220383ca280112080c0100c3d02c10090f800121031316000740c24190803840300c00044528201d03519240400d40c6080340c80c0311032824020b81c0e03600198a608176604280030400911640310b0b0181d8000f095101c10500d41b1500201d40e801c548001680103e036a41d6110f1751501003400740041010320a81d14003d5220031100c90300340308104182c0c82c0e003004c0e40c1c1c2e58000c4501800daa00d001c0c45c1440d00d17590f00da240490019000605024210a1441d2009801c101610300725131852030110350107251400780049010030b41c1e032841103042954a0408024041d64141400c558086690b0341e5641e92240c040703c816403070340c20440c841030150b441440004546001b03403483c80e040c46c0a03c589c48008181e860354030021480010301296120b0b944140403044040602050b50084c20ba00400303080d81e9181e04200c031414814440c1c54078803040a44480c6c9030040c0440c00c0d03800c111005501d040d04101071110721b502c0501c40c0900172600c60410301c00c1c180c0b0004408403044005409000c2504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 863712814 1250 863711564 863711567
    0x191a04050d110307150b01030e0d0905241e09060703030504150e0d0e011707080712050c09040e03070b0f01030312150b03250203040f150e061b0102030106 68
    0x203051810000c0040c40e490854102c21401004560784c1030b40c41081c003000c0c4a00721003d01c020346049083c0c141031540e01d6656603c4294244000d03a400d0900e60f8803a6009802e080400501c0e1245d01021074041c1c0d4034041c80f40c6c540d0110b0003141c2c1c202c00900900240c440e40910044114440c04c01d4250b0049004a955410150150007207406180705908080c08207602259100480f0a0100e0368403055111a100301d007180e000b00c050440200c010b1402c0443c2d0382500004e120300c500241c0c4c13031074000350440e41040046640034914801c1c82201003028440d504180503010000e000700300b03000d0b06c0f860780c95550005060041003299591a40b104050941c1e15080d80c0d5418070352400d12082c0c0120703030812b100082c0c4008500c2400d928034605107403091050304004071700c078040c4c200902d00800a00c0c81c000c0d045ca0781c8080e0f01d41c4407480d50181e0085640e00d051400c0c400321401c042d40720310407021550355030b2038406400880c00820a142900c088d0313120350144881c0900d210044401030303880d510000011418a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 863714064 1250 863712814 863712823
    0x209011d030f2a040c0203040605450907050306040b0a1208040501020601330e03010609060510030b1027060c0c081b0910081b0909060108191a0405 65
    0x5005281503400300316032410b20080d220205005c10050f001000140191800b42c00a04a030454880c112001051844030101c024a89251010710340740703119404000d8840d1000401c2c820761403e44d60a015800c1100024025020242c80103211701d0316a0030415054450846c450f0040403458140a5030038804d082000301507100e801080d0050141d2000800c1c00b20b000c010841007c0c1010100c0c2e66115108140f00104500207001a0104251540403e07102e07902400b07502e000d4034001c0310000340c55240104000080905240000625040070007084803603403070300710a6452001c1e40c248480d940b0342c0243d031300c401840348800f03803428400c0300740700403650380c2c2e111044041c0710b03100d5403422200c40d49545285031b4982041176480d958021261075a806400c0884032a0b400540c3c1910300051251115121400d0036500d42d03c3e030103620282c0c0c0c1d5080f0185081d211031134009160201801715035040000c1c154442c10200319410010042a1b02074007002880190703000092510b141e4040c180c20540341980d1034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 863715314 1250 863714064 863714113
    0x3040b07020705030708060a020a20072903150f06031018050c1b010f020c060f0c040b070f030c020d082206121802210f010209011d030f 60
    0x140b040e100d01040c58103000a0701d40a031040300c802000282e0b40d07545800060f621a81880c004c1010a071011000d62402da1045d100840e00f600c09081964240410310740e42034040d600c08070002100c0070812840c4400d00781103030342210a16803d0042d181a8002050300005004c2e480e5800400010400c42071401052008003602d10034200d0446a6083c0051141035034000c0d200d40e11803e00410051845030301c0c00c0d00300d9070740340741c60000030a0704d400c0c007100c10003240c020502d0f015080d002502006035110b8102820f0764000c18072070004d0304150500d085640340d8014584001d100c800c80058450605000b52007041485a0041c60112080140d00c1c0500f000d4000281c0e0314060b20104a0b10340b22040d070101c8c01c06c15550740e0742e508241e4028a00f0550060108050780403000c003484c210150150729940503110b901e900203440b400882c0c0c64030032900c0c45c01d01840c4c46d108180c0d1062000e128035aa000c0700c4020f10800815610f02d000100e075001a0902c0582c0201201c140718100041d04003007041c0091489 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 863716564 1250 863715314 863715317
    0x20091006270603050403020c030601090614120d050a05070501060609060e040507210f02040f0f08010216020603061309050606030c0a0f050603100909031d03010903120e0f0303040b07 80
    0xd001c0d2400d89000344201210665046038140d20080c40401e2203540600d50203406481110000040080428100300080e0400b0340f0b16519840203001c89880013440d071604200030b4803544280e05842e0050f0381c0312080c0f00b00c20b904202c000600f02c03008a01c07510558510b140c202c002041341c5965048040d0100b4100d1103488042901603110026601c1c1a00c02c1d20300c120030588551100080d20300e640b030503181c40d2042d0607007015900c1040341c0001d100c61016201910b1a100560055410541200301442d101d52000140c2c0e1700400ca04005901e042c0098500964150b031895240d49540d00000d002d2000080d040510314500010f607810300400060143c0100804c0d015521802203800601c090308481d8000c2c0109020154800c01181c02d0800085030722946c103045049036640c4031802b0b401641c0b1014000d80004090038142400074022802c060b0540004038005c2080741c517582e40240c29400d461f510848a19030b218581c25900000784550401070700f005059a541e4945468554001c1c00305659090 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 863717814 1250 863716564 863716577
    0x10050f0c011416050c0d140705070e011d0907050d14250b04050f090405010603050a0f020109092a12020d021e1204064808070c20091006 60
    0x10340f160103032045070b840703110031006172188004000d0180c81c1e50409800e141410807007040440701040c0705010003801303801381c0e9004c90500e514184c64041030300c10811080e40030200810030703c000301100040c0241142d200b80d03900302d40a402d5041c41d141740340741c070f580a00080c001d0340c1400c8200008916080180042c04810407040781c0c0341c0385038088030f0085e4020503401129880c403105151520761203041d80070b80b00d8000030440d00e440355102790811180c0d00f41155110158042d43d011503800c5400f0001510001008200e1040e4402d90040304c410722440e2010b5160141c2c4a81c001688500fa40058040c1800810b5540790701c0b42414000a51040084600004480103282035070446082100c0c1184042e074101350542d141c1c0d4542c1c800414103400300d400e05401090700c0e5491160741d502e00054062044000050040040303803103290414a142c1201d04011095042000c440d800c240301000f0140c10a000c99907000c1017003107010402402c4511a0ba014401900700400c04201c0c03000380d02540e5080c1e03a0b68 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 863719064 1250 863717814 863717851
    0xe01030c02030405031b04111908071805010804060906020a050c0c0609060724060e0a05180d0c030e030601032406030308040f15090c09061410050f0c0114 68
    0x4070385900944c09082d03450740058440940c841d010040d06846003100a00014401610001e07600312503101c055804003042d07410600044051b00f08442c0d95000c00d842c24590504580005401741d10704180c058141130017800c0b00840d0600585a010b440d0701a4417900440d902c071307400f100142440d007040200c800a44170361113486c0b041d4246030080cad841200c0c1c0540802c0c00d2005543d43c8000000100444c43c039021a003022034003004009000701402007111351481c404504107005090241d65004081705000d00c0d00d01e100c80314240d00090541040b21007490188141c00715403904031458080314a80c50350500c140c03c004414041c4000c8171415580e00360500115030b0711804140c50503510b5078400607011551034000600030829803c0b1034003900c0d02c2242000402c501c01c032a40402c440301030205031186420310800b84904c4540d0b20403040580300071008000001d801e0800141c2a1410385110000c01c1004100c02401030303091415104082d06000c001c0c01442c80750541c500541ea011588481061000ca080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 863720314 1250 863719064 863719067
    0x1090e07050409200d0c060e01110a03120e16170105100f290310080601050301020f340f050d0318060506060d09080301150e060d1a0604060e01030c 65
    0x1000341d842d500c1209440820740e003e103013140400c0040405a08844004040c10000e0514100d010191041d0f0312194225a000c400052594950001200c859800400c00c41c4c0465040151100c5000740c42c580400e00e40c0f84aa086401d00a0401d0b448518082626002c107107100300c825144017409100c002040103a5a48065240d03c80075440b03843c1c80c1c0b114980c0140301b60a0404801d80d40c420281034455802b640f00726009640e43d2013280c1d115a1981d040d0814800d240303003845914010702c0c04400a500300344c401170b45510f8501c240c008061481c1e076a601481c1003841015025054000550188000030a0074240010417060f40c802c121064000c08543d129070602a100354402e25501800c80c01080c503803555928000c08002c4c000950208060080b0801040680140104140301d1101c4544a514100c800007000c0088201e001c2444444100c5c04826269102035425081400c1c4000c51010070000011003013511107000700350000e10000f000708406803c01c00d8003d00d0802039a0401035415003900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 863721564 1250 863720314 863720321
    0x5010e060708130309170c040605030d120b0307080f0a03030b010f1407050c04060617010801060e13080d0515030606122a1201060f0911030403080901090b01090e070504 74
    0x11800042010030b804110403542c1e02d84403110301846424003040e459154492000004103406450340258410b441c400b20038140f40c081c0c2c0c00284000d034010142001c050901404400c3c890700e607403507050399856984005560420051b8010000001514400700300d403000c3d21344498031141b054012a041c40c0783c030300f03095202d62495040401c9d1652010400a003d688140782d6034020682512540b282c0301890803555502d00c9080000c10a40e11080d40c21524035560101245050340200010b174502042044188003414055604c240d4204403040e8110581c44d10030b10034003510910b40c101519110030460701d0002c4440f884410380c0114211801540e406080090080e1070448035801e035045a103030410f07000d44000b001050310140d9000b900c0000c0040340440d2841c2c80c1c99406100c00e07034651004024886400c040030b170103044800010300000e072030b02c2d10007400d03031002a00040c20030a9139000101c401400703520040c60503511040340707101940e580070084060718500241038164051078000250074a401e21 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 863722814 1250 863721564 863721571
    0x60807032738060616120806010f050c0a110102070b04261c0302031503120310120317060f04051f153504060e060604140406150b0703090305010e06 65
    0x1801940030f42da854140310f09a00240d601c0042d00c1c44015030b540004180001c11400341c001682e9103850341c60140d00041182d0140e2030b1407010f00804202004010308089034044100d60040d01007000c070410703440100c0c50103c0c50b900c6101e02d000d000c50701250144900400401d000202d13140c814210040101d15512201c65010350301c0712107448500105413a010350040d42d8851100c040c8174407041c82d0000800d04121129505c035200e44c0d40002004944800322001c4405000c0301041c00804c038100d82d4002d00581404088558009103050004541d40c0d2154020340607070744003620900490a06005000307032186c220a501084168104010279101c0520210a8107503c1941c1d81c0030003044d1107038041502c0c4801030118440e00085440b550300d041c40803188680181d100c2d0100041c0c03446203501c52800e090300a410345200e02c4c180000d4024211450144d5038210f84c000b000082d5100e10520303085810300495100a4074420082106028540c0044054040b80d0003031000780b0514184640d400c1d120b1904a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 863724064 1250 863722814 863722913
    0x91a0408070617240d0f0b011d1810060b07050d020d0903020909030f07030c0b0709030308010b030a09150e0106140907080702030c010f06031103070608070327 70
    0xb1000211982d50b0748581310780c80054200780040d055154404a41000c0c580e91007503a1117900c0050710000c0242c5549128010501c040301d21100b2400c07001941d0f40c0c1b500184c25014048404c074a149003e40e03050019124117107070b0403010404559078030041c4009030000303401070305d42e801007200012000e80003058414100f6065270301c1e400ca041c2141e08201c49804050010a010301c01488140d03401000040206070080c000c1d1130354502c6403041e18120300041703402000c0344100580c0303142c100002500003003864191400800016140c3e038440444400501508101070b01e0021311842542d03c4074141e84c8a6082a00a03000070312039151140070782c080c803001101000b600b004c007202c00a0300c006d00c00e80b140c1d5003006207441600e142058482d032923420350390b21901002c0201d94a02c01001013100105918074600c009030301800741140340610240080c000140700b40c007415100c4141010862103401507190781030f00715050402c3c1a555061955035160303019410b015409034000390310f44800308a81c0807180c10000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 863725314 1250 863724064 863724107
    0xf03120c0905060a0c05060708250e1e0901230f0f060306030a0b0c040e01051903020f011103040b0d0e0f0606190e09100c0e1f091a04080706 62
    0x104020722801d941324044040c1000005200800055400e100c200e000c0c0b02d50741d0f151001d80c2409450203030450801040c2d8600d0061200b500d0358000d0f0000660321072084100c035414520301800302900c118a20200c560f65002e109200040b03210340e8480203100b4489941514000d02210003030911010954160341c06074031070184280400c1500d05a8011580308002070150f0740f2030659503548001c0120151004481c424020400303000020306002882c0c01003804880040340510700220360345c0782010600001e030040540c0c0798100c075164042e80340101010000c100702e954070703a81da0450b0314003500a64201014213081c02c0d01404100c00c001251642030b040f141c050070041c1c81e15803c10011030340d101201c5100e00034004000a10b008d00d40e1005100e9088080545800c4410300310043c00c486400c46410b061001c07030b101d2450a500d410040b02d25416100171003960f0415003044c15584000181e128035141d01c841c0101c0c01104003075401801c04c81e0400b01c22a00030301e440d2501651700c226058050340c2480c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 863726564 1250 863725314 863725319
    0xd031b0912050319050c0d2f010b060711042004090b0112020a05030402130e0a060e0f01020307020a1203020f12041a0a1d010902010507150e0a0f03120c09 68
    0x14800300240d494410b4003102d04c1e260b4401c1003120b00d5042c050b0f41102042020846000e01542030118844180c071900e40b69001c00c03041845136613100070780700d01c0400d0140c0d086000c3e83c80900951150880b40001055951146240e2518040201c069880c40b40100c0c103285020b0f50454010300c2c4004640e0305088242d0800d0308040b5183c3c0104403140c40281000504803102000c00140e02c001c14030b20900c0c1e69030f15500e00d024014810907a03403100942d20020b140c240d070000c4802007c6595003060354030070404105c030300387c0c0b1089030710301a410104024654400410b0100c0182c0000d12011081c0c800c3c0e031032804813084250168101c1c0683c03034002c11030800030005842545951006194810300c4bc210b181c001401d03a10b09508588401c48090351056a500c04144202c41014036051401c4443e5000384007039105580002c02c51f02441c0c0c001050402c2100c42d80d02031519981004064a86c0f00007100c011040d20304080c903410044500a03030100d1038407114001145001e0280d0ba19480c981d840d001002403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 863727814 1250 863726564 863726579
    0x2409020a0b0414190b07030908060f0c1801030207020604140108090c0a1a1e0d060503031c111c0f270b2a031b1903050a020d020c0d031b09 61
    0x260041401c102e0040c00000100c3d4005c10400a81401d500954980106034100031640b0301d080300181403003400c24160010450040e56100c22940619400c031000800b1a2400780160040d000d2075000950120011501091240100d4002021268241d903400c8054440070051601e40c4001c264550300480312070824450341da1815075806108229071030b124a4602852004001138101c5440e03032990460000350715070382c114580a0700018201c11000b0798508010003070003030f0381d1a401c91341a0759800d407100d101448000152040d19082c420508952801c800c028265100a02024101c00403c52403c210b024500444100e07402d540403103c10070b0306403400c05450702e41c00c0c0c0800400a41c0040800511010801c0a60b547c1407202d413000c5030328580f030303040c0441c480d5110794003904002810041071124500302142184080d80c01103607070034000703055210204241c010f4072610103108105400011004050000020001c40f15140703590100301070302c200c0950b1182e881314141c0386400210244018000c50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 863729064 1250 863727814 863727829
    0x9050120030403081f08030a020f0c01052106150408010605043b0c060406090e0705030c0d0504170408160503010e030d020d02190203070312060608132409020a0b0414 73
    0x390016030603a1050346c2d8070842c540c41c0d58480302a040058008000703000a0083c104000b002c406001d0130800e0400e41d1810412044440050912000c001c180d4003040b0540c0b43c2840c2d01413000074158010b80d545440e29101d03400f0300210f1282c240980c2c07030191030107a210b0780301605411070150a09096040070000641900000c0c200340304451314050f043e0030060742d544941c0280000e04498881303405071450301380300d4800740700c0c000c00f90030602801700200407250100e0000c8443e00311a2000009660311141812035400107100242151950001000300302c46074001059860f020900b00e10380c9000c0c0e1240c05160030380e51086440700e00d0781d105010800000d04a40c014005144401c5070046c18000d102c0c1c114000304c0e810392203c2d009078000281034414590710148240c21490b0b401c0090100e1894803170700415580d0020400303000c4c4042c0000d01010882080c69007198a4160748540010042c0201c16000030049100200e2141007075001c0000c6056020064404840f01903043c426040c3d544014020507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 863730314 1250 863729064 863729101
    0x1308250b071e09051e04060f0602010501050904050a1704050a03060b040e0a11060d24050306150306040308060607050607080601020f070b0d0504050307060204030b0f18061b09040905012003040308 86
    0xd10b07031006038225203a10f8600c101c1000300f5030114036903102849e06030003038210b03030040c0c01040c051880c6100b08004146c002901e200c0c200c0e4020710000150744100003458040c069030300b142d503000c007687c5400001e00c14160404050300008030380410210742000b103060354860002c8402440003180c2c80703540c1c02c3c501e045000b40030005952080810402c000f0340682da40280e5080a0140034100c0150501c09030800b0001e681e070150006201411509001000130f90301c4000410050030001200c000030a00c3d1124403d8552482c1c0c081c0403176280741090310018091101c126482d50041c0303d89414607500100000300601202c802c242c186203064001c04403400904070080041d035451000b000038600150851000300019401035940007828240304000c44030090340948102d180e10b0b002d95214806140128510390007506511004855040780c161518840c000d021826038400c0c40c00107c40140702d019044140701c0000c2c01800d403002854078047e0180780c0000e80b0060300044a45000407071080526030510103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 863731564 1250 863730314 863730349
    0x50f0f1315020d090b04060b120304030b180d351f0503060f0402040605181302040b19051008220303020f160b070203031308250b071e0905 61
    0xc0c042c000607443c01a1855080c08036481e448010400081c8507180c4240844103500300c07040100201400d03580b99890041d4000030f8074858050001c10001c942002103414640b003104217035541c141c044180502000d00641c42d26080f8043d02c0f80f101e0011034001d8056402d4402089042c4480d260601d0411610140440c41d401a02d4060b001240c80e13a03041002c18800e0340c40b02e140003001d1419206020a0303446e542c0c00b103401815140c010807028000c1045541d070054440344100030086140c00010050b000c410150b41e0071100b2240d9102d103001c42c8014800a0300d1054170030303880031952650216040041241c10300d401e11480090f9410b0f0f280d89000d0303c04414000c0c81c002d0b08202c4140c182c2e90141e4000903812034044246644142085a240712280c0d0101450003d1811440c140b401004c41e2109420b00500e44040000d40703182c20f1004410315040740c01c800c035801c00ca04802e46050b200034042500c5a03804542c201c4105148040e950300c9000b401d4159a54040640c1c0c0303490700380200c801004040c4035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 863732814 1250 863731564 863731567
    0x7090e0114180316260d1a0a210b010603020d050c09030a080d02070510021b01150b222d050f040207031b05071502060c070f081b01050f0f131502 64
    0x1000040103100740b61758501c21704106655481d001260707411100110044001c10706245031040407962545c42c4407045585200743e01d03544410800401c022200070000c0144103400401c00401d547c0c0e03243d8041c01c1c003201480810403441c0c5502a10003064010070304d41c0b0740e169100582c9480091160005000542505d032009402e1014aa44d92804c0142e802000d481150380820418210000c1e1111000300900c100000c1060000030100d0b200401028000c01001050005d018100c002464001d524030740c03008402c0b40785141e00c0d80031380b410b08040c0c8040200c0d44074030894480486000c26038140b046490051030041da900782581400080d41080c80e054040c41000c101144414641040c0c0001c0d2900c00c5000e40021030629006020381604d503c44402117500010030407608600082c03c40b402160060000781c06d4240c149841900c600c20103140080d528007070303031480ba2641c3c0150010b5019500e1880d464940c3e59880318110503054044501620a8606568200101d104a04110344025482c080903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 863734064 1250 863732814 863732843
    0x5060310210606063f0b0105041212170f040b04020a0806090708011a0d020607170d020c010b0d020117071e17060a0609140307090e0114180316 63
    0xb80860704241e0000c0007049030a8545680301900c50607110b80b40c4090300d06840300380602c644e2201e41303007803003280051229a51405c1c503080c1e84c051010b0354010000d144c1d0700c142c055083e1500321007146040321107001090780d190011031710070600c68102e4401c1342e04418034000383c1d4498031046102e4a0162050340c1141103114007081082c414005107201d0b442c1c0c1001010300c0380c40d00c4201d0f0308488042540000c5e00840c603c40c150690f0702c440382c204c44a90110307502502d030289400c100900d184806107080d408140000c40c8240900030b42c001e08510341c0300a00130401400304105203e035460b407801d002800901180c02401000050350401078000740240f80c183c107120104200c1d03080d000c5040d2812000310f48102e5000c0c0f210020311a005901c0101900c2d641000d41c0740407006009142940640203002e020310049002c1500d0400c200f00060000c00000d01a03000d640c201c041c0208440241c6138440850000000c0c929000300e00070541c512002da00461400180071070049428813451002ca496803510300d0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 863735314 1250 863734064 863734073
    0xf060b07030e01170a091b12020111070b0a0c0510060e061e091306050105101b03050f031801050f220201030b060d060501110d020d0e04020c1b04060506031021 70
    0x700c0c0e105d05000c071800507044855082041003440907020b180c00c402d03500c01003881a0f556004010003030f01d50a00307105040d0301c2810310480c01d100b01c64009811541c40418804445903010344400341c041d000c0d50581d000030014180060a6900b68040c0598122203030f0301260042c206601c0510b00c41c100c2ca62100c4441c0034200000e031906405494580a41c900b44444100f0b200c168412240100300403520202c224000d4440a031407000c001c9200444218201812403d2502400c200e03501e0200c204d501d59034134035000703400d000002521241e41075650f182600213001c1100c0ca58503c0d00810000301c4034420401514019803030360068207400c03410941c50703400408203a200e000203080542801000442c0407824400010000030b000120070032158000c7c810442050f40115058810081520f0310203008210301c00424040c0c4030700138195085110b100300f81d02036204a1504442e40c500220780502c0456940c000b0454a800155000d084150300f04a0410810260b880d4499419139406488a9a03585641b80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 863736564 1250 863735314 863735357
    0xf020f07030506100905060d020d140d0512070302090307140d02041103161b021c0f0c0603060801061d070201060509090a02030709050c1206060417100f060b07030e01 73
    0xc031407036400002071104d08007440a00d64041c120b4844204201d2030315600196915508200103030265207520b1100040c407142500036940c20344a030046800700860840020b0072644050340d412a14100078001c640024440d0080350820203000f00140491410300304265500548030800e141c2c008043c010390401611b950041e99030108400036110303140c0c5890107400401c081c1da420800104943d21460300a660003003010303c01103d8040c1c81d48141400c0f50842c8000380c90b00fa010207003204080d08031440401820386900026a00140c1d400c4c041c0c260369050003407e84400d8008c14503501954032100381c503400003203030580d400202031001141e03259950380401c9140d00151001d46080e00007100720825400c2c1004014001c0c0041e41007001140b924421026190140394071208140b0662004907080340e5840c800d96010741642c1d40311040410081d0402c8e03035951046100ea184150401441d25048043e5204150454544000d06460040c0c10780e411140d90560b481202c0c1031000310115400143c84111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 863737814 1250 863736564 863736569
    0x190f031b02010504020301110702030a080304260a032d0e011d25060e0d23150c0415080a060b071419231504050c011e0806010f020f07 59
    0x1c00026660070b15006040c2500e0400e0b04440303040404000b043e0041c2c4001402c400c01c4c6401042d03ea17240d03180e85ca4071624040e101c0151041c03145003850014281c98081d0000c00c00e144550b1010802e42206043c070101102618505800c020044000d04208419542060381d03840c40034800061010360300645040202c5214403c500103500c003a600c07c40352442c1c02e1060380701c0801403020810031442d080d4018843d0410480081c0280040103015041040126800305008000c52040300d101845001d40c40c1e541c58190700354240b10070a100070031071910001c0308031400d5070701c006441c0c240101c80c25010b41d10f0b00d802074454032a00e42d0300c8500080141c14580600110740c8030703110144050301b58049040c9000d0a0030307562007203000d842034404001441b12129210842c929043c802d14003c207071030402c1c244a4283c0341900b189140c0d004200c2003007000f162403000000241c0f80c21000000c4080c00100c03110546104c000490301d00d0b004210320350b00501100010b01140e104540026541a10550400f416607 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 863739064 1250 863737814 863737817
    0x50303060a06020f070302040f1e02031504050121020102071205100c1d1e190e0f0f042006130f05040e030f211504050c190f031b 57
    0x401401000c1c580140c4840040c840c610080c40c0340101c03102e1403a00c588483c40020701c11a40d5041c94000400c0b0b58010304400000c0540c9014211040002c20010794000c80e00e80c40c1400256024841510b8075100c1d1754140ca03d0b030720958417000802c1b60121500016220141c1c1941b054940001d0508008076100b0203803841a4003600444903494001c40c107640300750f207824042c00400c0d81e20b80182d2240da90901d030550f5081f10031001c0000c103c024a91520541240f044c0c1026005d4541107181c1e4054613507100722142144a00140e42d202d41c1094a051010350700858001000c2001c01c000c51110210504080300c040d08040b098502800001c05c0b0b0303404001d003201c0c20910000200003910841002c0402810150340500c02c02400d082059141c0c81110004a070788003021801a04000e004241546040c0845031032003000e050000b036400e043d1078040007941c8038504141c006180100310707805903000610740c0311400c4205080500195194141401290100b41d9150074402030b4003c0d00c004503003110b069 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 863740314 1250 863739064 863739067
    0x503070609050d030e0604060c09150306080c0d020612061f030b1809370308090106050a03080415030905010234030203120703021204200a0b030c0c03070b01030503 72
    0xd142050404803900f50f0141450b1138001881e04050000c150a640503610850010701c010b001001940c0c4040c59400403801c1c0407010a060340d4190301a400082605c04210803140c54003039070300c2041204071403040000c1d0490018440e0f220b9990350000c56075086a00181800c0c030000043c0790038218140f080292030000381d02d482001c1d006d4240707034120f10000440d4000890251904030200d43c4d60f6144021803200c281407d425000103a101c03400e546106a582902c194004191418000c14aa0081c2c2d4102460b500c0e0a0340046d00e0318000c4c801d41d0031294803401f01400c080c5042040c1c005401070a00c10024151580b625000180f02031006100c80040410445002d590000c402c852100900d60018101101403036003a02103900082a600c00011084c0714003c15920a00103d020b4020203001a40808540080c0020022100d8035041c11041c900c00c207030b2702940014100074841000f0301c601581e80004001254402c070f9400d0081c00711030380e800c0440c0d143c2015555100d1301840c5c240e02c1030720107400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 863741564 1250 863740314 863740331
    0xc080d05041b050102031b0106121407060c050706030b010c1a09010e011812180e0f060d11060306121e0105071701180f020a0905011b0f06051305030706 67
    0x14032242c2104030703850804607820042c20a0b0020395688140100d02c0d107002d0034175855600950003500306002070205c010101c15010301518100c3e14440310f030300010b800350051010200382c41e8403844041000540180081007203518203a020390041c940c134481c00c0d0400c854101c2403c041070200000030900420081c1605841ca085d4800c1421204e2510784480981d06103041080742268414490b0003140e0000300c40000100c2c1d03c102a24481100c05005180c003d425500151120400b400c040c402c0060780309001183d6228810462040e0380d40400420b001c0c0c0750454401c003070900401540d408200a00401f02c4803440b45503040ca424952560b010012001e0207690384202c00c20700a10390045250704000c05110b0001c0840008138405008521030388007066028040400c5a401c6032070f500701341c0d050440d43c44100600041440155000709808281c000300300f20000b40d5480503114000341c003c41341040072819541c4140240030090951810b030f105c64080d070804200709100404401d440b030b003000500d146 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 863742814 1250 863741564 863741573
    0x3030201050a0605090c0309030c060f04030e010c03121505210106060e0901031719030510060207150e0f090907060e06040e07030c021c0c0507080d0c120c080d0504 72
    0x720002d004402c0345040480401c150b40382d95a4558120328001c0c03600e40c5079652908154918040c001548107548150f6091100712134103100900e018501964402000a07240401581c0540e86040010700140ca080380c04001030303003640d1000070074200e480c0a513101199a000000c4107000c480d41c00c200131504100b4081c3c08480e003441070000501c06400d10551030008480010f900040510000d4010071400e110201e409090030120b03a082e0036010160b0b1002481b240c030080050808440703413034181840c50000300ba0240006080c4049545c0901c44420100b10104100d0b1000c210711034840e002051108a03070aa80e44000116115614080060101310702d8440d00400c03038013441101601031070301008240084900b020f07140e03034008462304000c2a02540000100c0c078000c0e0703a80001d80d0b9440b88403170221400e0741c010551004c082c000c1e0101c2d0100d6403140307036160b01c44020f011203102080300316580f032000a5000138100000240c030304004c05414100c1d10303400055841200c9501c90969140c04000821 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 863744064 1250 863742814 863742821
    0x80c030406031a01020a1b0306090f03080a05040809190e090f070f080a060506120a2a0f0519170d171005060d150b09010915050f18060a0903030201 65
    0x1243c200300d03841c802408040010b5101c0761031000240c1110030100c10700e11580759050241c0f00442d4052800c1100e03900310708282051580091040340020801800b082800b900ca00986003d5a00465000e00d00500c0b0b07000c101c4041c1808000c6c00700340b4910000020741d5040d250465221b00c00d010007500003528074000700f41c1003c0b0580c208100d01c1c0160311080c8010303100020000c141c1540244001125101c400004218458040c0640154402e1204903410460440c5552000c2c2c1c0c0403405040a40c0720000180c055602240500300300c0d14504a020400303490107a140002950508071181003039916106541e003407100582e24210303d60f001451000e0708660202000203c81d0307004594a60301e041c4482c4070308804615100c0c2c688500e1002c104c00810903116031140240041201c01c0d89000ea60b030711081ca4040d0000c04a403408125102b0b40023407024400c050f50b40b03170b503002c503981e20b4a0000007050000540d00b0054141200d0000c000350b602140c3c0b581401803c082031340d074841511842c558a00242174 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 863745314 1250 863744064 863744081
    0x70b01050a1a04140d300309020d080a03110408010c1b030e0906040b0a2702090d15090609050307060509070f030807050c0918010b091e04050703080c03040603 70
    0x295004402080c4440c503400360fa040d24104d5210b15665502140010a801100c2001074400a40700b110319400071840d002e082c109004140080130311101c0d216007034048036503001d0083c1d0803a014060300e00c005111840240415500d605000441d80740d5076509100980140e08030501c569500c8405200701e070380003148580b80d2100302080d060000c10700e1f9001000800c0e0300742c0c6039002c1c01d40300020880329a10364211521190001d000000b0103a5a64a00c0c0c60350300a00b20039904805004859022840990080314072580b005885101c02e0120307a40c8480c0b060700101c240300c00b0507554034003171000203583c0e000d2544681c2c058401180c541c141c42c01d1203021030703401030100590780c9d2241c401004003040c0d02011310308a940041c0d4040d01d0700c140303040c104d040c0b102e200c1125900030700d20b40030885d02e81841d01c909180c046089000300685540103003442400314051b0b40d030721000d1960100707911103155010007080c1d001d0300c141d040d11015070740c0707543da4180c54021444815a6810201d404e01440381d00d8814041e6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 863746564 1250 863745314 863745329
    0xd020a1a07140109211e021018030c0f06020405090f07031802101b14060907151b06410408070b101e060f02030a08010b090103090503070b01050a 64
    0x88031a9a1790740d8015402d41c20b080c1c00310a0604411201400f400000141400d8488154505250781c0c00c004d4031003022180c40851030740b421080f1560300d003100300b01e000c0290b81034a41d01c845401503266484040d2042804031059902003201103015103400b41550f00403511190899030f80d04050b0b0300941a0b40c0342148151401106441070f801594a0811951200d903940c14584915002800c4070700080c0188000a4266454081e800100e0071001030b0346032080801d40c0c15110a44d40342c03042c0c2151181c1d41850b0368002010280101122044006a00e1311184512400208078a428503a440c02c544204886d500815034061485c241001407102c686400100400d8014549410b603078000f114003508038007801e2803015000050141071a5000d0740050b100c1607010712541c1111081088012405024000009408441200100c0c0c00001078586d041400d44031000b050b802e040080500341c105900c040d04168a0b18949000f20340e042c401086000c1c052041e251003507061070b06225010034998000d85 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 863747814 1250 863746564 863746571
    0x71e0c08031e03130809030109060e06040b010f0b0904020901031404030918090b040807050703050a080403060c0807020d0e0102010b10320a0809120313050d11030403020d020a1a071401 81
    0xd961308110710f0200c0c2c2c0070450546402c07035100403030b00408104000030f0045180c91f404146a060008106100314454080518107a0f280e01c0700701c4400c12a031148000d00542440610340c10b240c25005040301002c10300d40060003014442da010550700b010307541035010680030701c400d11018800900107903c544c0c50030018010101581d03548400c1c504020406001240c3c081201b41c10803e080c8a85001141c0000846011024508040c901640148805c94000346405c1c120f849540c02000101e11941c0203801030401500f040300c1c00c1d0707107115080340e040d4119503948203114110780d680701c03512860840a5a4a5004040502d6001520108100100701414034908450048081d40040741c1112420b4a088506604c031041143c1c609181f0700750901c0847c6020080140913046c1c2280800f04500407411103440101c0341006644070280600190780e11b800802c81070025052291540b500c0b170b8030103070000f0001c07541d5641d43c0c1c0030704900d044e81c00b6040800040d40014800d600400003940d02d0280000c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 863749064 1250 863747814 863747821
    0x6050910180317040e0708010602060f060a0e1f0f050a0e010b07151b08040b0f15041d0601030602130e150d02030a060f0e0d090b071e0c08031e03 64
    0x100c003604500c001001c01180303903496603e8600076020707030b4003c03e181710810742e00c0c1c1030440001d480d0000034001c4a00603c500000076121041c0030800a002d40c0c1d01400200030303507040c8441b071400010b0042803243c4003084128042e03581d04003544000c008000f07041d5103240c46820b1004204030000f42e54069680069450010300101844000315200316134090120b11120761000c0c1da040c0a000701d10750000900c41a854059202508003010610552044002c5078a07941e41282d4800c0400d000d858201a200c0750000344000b41c2400e5216410001c2000d618810051100342143e04e0440260011643d064000c14004025801089003401509000105003442c3c50032400d0124103542d46103003a4850f451403540325040d51028800e4407042e41d08004140600000c0b40000c1c80500f0a0340301300d080d90312400b02d00805980c071a55030b900c291605001803d20b0408280c44442a0103558144240c40b21071001c2c00200240b0f0072001c0000408110016540b99001a580b0040f10301e20800390b00210300003003040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 863750314 1250 863749064 863749097
    0x140f18060a06021b0d020112110409241a070605100501021203071e030209090a05040b0702010e03071b0503060f04060f0603080a08270a02040e120a08041104050106050910 75
    0x60300c2c40928240c80042c5d800c0d08900049403520080c2500001d0796140441c0600f400d0103002c000e00039600e0a14080c02040e80b00c5208410100714040c01d071142010180050002d100035200215004030350085550505200f511454203e820035a12452500840c000c01c0016513018011017040b010903101850540c80d00d0100680307455035003070345603240c1404c080702c411a2030301135810755070205006060714807039141c1407030050000c160540c1d00b034820481c0b10780011180c5105008010600c990130024504102c810765aa5551301204180e00d40b6040d52a080451207450401010303110710094955007105043c00e0400300c04075846c141c00914018146141031002c2103120084440080162800c1d8296075a19583c591001c8221042800c000c9a800b60009940d8030001d040b00115008850402c0780034142402c076aa00c040d00018807110b04000d20207030816a0280e80030301e9020307005240d95000900601c000030b0445409070025070100d800401c10fa0018146a4042d881161960034660041e4500614 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 863751564 1250 863750314 863750353
    0xd080a0b0303030103051506030319030902010e09011202130612080a0f0c081b070803160c0e060f10030e0d050c0d0c150b03030412030203030613090c140f18060a0602 73
    0x1c1f80c1c0382c0604040f0100b40b031f5407020001c4901c00384140c080c03990544103400008001d4007102006030b0005840200c41c44052803d84921070403102d4151180c42001000d40c01d00c090721180b5600101202c1c1d0b10080000c0341120300c2e200c1c0141038840c0307155a03551100580c01800307280402c405401044541520700c00003410000890301c62100e0901034000303503440c05841619042964000d08000e000101e0101152100107981c0b445c510b2044911032603a41d1100440503210f141102c400b603025108041e01c48103420701c0462803000305118a0041030350051204a2440c00e2000501500041c400143c4007a00075028010617220300950300d041d68502040392a400c4c180e8014440b01c904441d554180f0000c260340800894006180403e002242d804103418080d46a0700b040311454020140e0300600707000d4001c04d1080034082e507071100c1c80b461214200ba0030013002d405a0201f039604200583c0041c801c0b0f0743e50034100000c00e1200241c041305c0340f400d07105100c202140c60b400803043d5408081030200c2c1800b00380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 863752814 1250 863751564 863751583
    0x611220902070c0e0c09041518020309060a0b190f03020a0b0304050a0605180604060504030908031903020307121d07171b0312030a020405011b080306090c0c0d080a0b030303010305 79
    0x320144c0c5903d40b85090070161107207886080c0e000740362503681103040c06503010f03441c2201c441c10141c04280c03000300e6001e01a441f080381e0021a541000e000141101201d40c02622448005445207014600300300c0f05145c3c91100707401c02c00724156090000c0046142064490024089000d012420740c01c21f40e40e09682c8481001000703166a4403900025495604500c840d20060400c10481301e01d41003509100c8000c21060343c0a40000b00000710100d5010000011100c02040c0c1804038010401d116078110020342016000f001041048000344a030070743c0c40d0040300c0000f03241c8000c80784e016890400b03640ca40324041c1c0c0f0034818908a80889146400701080c0780092800804a8032000c9480c030340004e04114042403044000c46003c0203110207540e0342d0307001d0801e0310030a886410106054074a41d1040545a0100a095a04c00c000040841c201054510380150002e10f10310b0900300340000d06e604001840603120300242c551030070010005c400b0300802240310030940142d0710b90350460316200c0c0c0714540030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 863754064 1250 863752814 863752829
    0xf08031204110307030b1e041e0606050409080c150c0913020d090804080613020603160e0303180f060f0307050a020c1003051e0c0d090611220902070c 66
    0x80c80010309100c00103880c0030316a0b100806643c0e44a480b890b000f01581003d0320074020005d12145914907241180340c94500403038001c00e1140707040e2070030000081070032480c01d0200c407100e4446100181e262030314019464114840c07c881a10342402143c45031800f05040c06802c0b810304083e060115425880c0100c40340000147d80c0107400003c45888000684900c81c80e000720507185c16840010303c41e100018109031b03901a000d50340d0a48a403403031003100140070100a50701c204100003040741d50308103100d0030302c2070300c4181400c801100c0300d0000242540c016840005080c83d082d81c500d0200c1c9001800d405245104468080c1040512100e1130801e0100820340d0301070000c002015007049000300518502c0b200003c240003e9120351100c018050881952120003c0044c0364030040d121554135281403281c06080c100030b0030308140340d0325000502000182901c1c041daa84000f081c00301c60510007404440620a0108050f00cc000c4000141d0f8000d0b40c03000394420f00c10b10a03000043c484000e00070485195 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 863755314 1250 863754064 863754097
    0x130501060815011e082706060105090d021011010c2105040507030602030903040e0117060708060a12050304060207060f0e041a030109051b011b170c03030c030109060f0803 75
    0x1620016201e44058441c003940f0b1418480032070701c0003030344100254403032032a14010100e081b00708000e5060019050b8100303c4190007810001c1c58551294001d40584000280300b044400002e402003080404000f92060025061003c1d200c800760b0700340916130306150640342541c04140e103603403402840d13800d240615407403d4a4002080602904018a40103940c12540443d030368107001101c03617034980c4944602e00b443d0550b0070000030759003200c1d91040300c140c09001c050180d5607140070007110030582c020030711580000c51880105021500b40c188400f8548100003c40d0303110700b0164041d2030400c00d54001360400852001402e2100e5004010000c0e0340c80c196808103a40001d40710800c8186101150b09806610b4801050240100080c5801c94a0004005c40c1c40405c0c0d460011645944000c070b15912041c401c1200f4400200c44212120100251400603030406150041c401e0440c0c0c000c0d115507140050120051051203040d100d070078010308551074210358007441c0070150794807030280d0000c2e40800100c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 863756564 1250 863755314 863755351
    0x11401080c0303070b07170705040302090615160825020f030c0604090b06070816060b04050c07023a121e0513150c0b0907050a0302091e0f061305010608 67
    0x1c0704018041c7c44d04119118440c0b80511004083c5c1d0010b10040e4401e40c11072012680307500301005050101216040d0003440e01c18140c20356500c1089090341213642c00c1d410000c2c079802620492401990001d07048041d4081c140600402070215040c0041c6ca200c0d400c05a0b150201c8c2d61904112000c031404100041654134107040010092300800801070540c85000800a00d002c03490b49006d20501d00c44d0300b080202c1114401408100c4000302d5102c00d1a800070000180940752610b282e88042041d81d0f01da411184002c0f07034109844881d042880c1c124010017034036104020041024000c84038407481e00300c3c100056001c0c0120201e0318143c41c44240040055003982010220020f00301411480402c2c00f0f945110407401400020081c2003518134000020128580d01c02c0843c07660200c60b4000c1038040d2032401c5400300850690080c3c4200d07400000d142e51040e054017110708035485084c8540c181d082d5461f0240900022810701074440c0400c0e4036000044c040b19421201d010b802c44100028845a80e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 863757814 1250 863756564 863756567
    0x40b1023030a0e010c020f0304210804150906030c080123090f0603070f030c0b160c030308040b0601030228051308011a06070506060f04110c011401080c0303070b07 72
    0x2014505061004100004012a42c550358000141000212000700300c054840e8804913202e4501d070341d8400c580d0300b0400c420482c06940760f00707032240d60459009107900d40d0351994800f40598041ea10200400304940070707100110750000310f280001e00650038180701200728070700001c1481c4814001c0c2d201c50301c2240688002e40354030a901c07210406002e00b19500c41e00785200c502409050480d1454440c0c81884c0c1c010a01a0341c1c2d40510080781e42c40b680c0405007a0420901800301e401c100741c40c940f42910010000c000c5940005c00c580107500035115100507081900b0940070090006004078149801007044a114880340c1d202d101c0b8101821441d04807414a10504032003a100d00d03480140842075240011070000010361203050801210427552402c42c0115040c09a02c0c000d480026050f904194001035142c200b50444184982c00140001130343c186270b10b48524aa0804d214000150703545140c07403e12a128004800d0140030000020314801c030400c80000c4d500c0c450300c02d00520501c0c08001280d60903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 863759064 1250 863757814 863757857
    0x50d0305070605040308010504061e03140f0d120507030608030a03051801091a0f010f090e10060306020a03050108071a0d020705060117060a1107030c0c080d03020d0b040b10 76
    0x119400390043c051402c150500502c40002802614499443d1000c0040c100e10003141c58051004e00d400011006803070f5484400e002e001d03550303182007180602520b105046000b841200c2850465880705040302c01258003240454030000c3c0800107161030050180019034001050b1054680c00746000300d12a510204182d071054101c1c200b89d03040e90b0a11924504000000941048030074458814806a50720344c0d12040100b4400e1080d010308000d10a003c2c0243c1d07070103410020805032088101c622800741c2c004810111140e50303009440007940410b0a0a00340d80c103010362401048510700030920700c1d092611120115004c0181c2c803081d034600054010346c201590b010f848131603400c071007617a15075a5201086034030071016440003075840c040c1c40c0000d070110b1407511a441d20044c003145940c0c1410800d0340d040d101c80c0000802603e14503003214000840f070706c0810020f2140303c150342c4d001d42c60701032250000082e2100845840d20503820122080c0040e195038460040c0d01c9070924050f94420041c0c1d24041c8034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 863760314 1250 863759064 863759077
    0x71404090501091b060201050c0906190915110f12030a0216060f060501081f030b072c04061703090f1306030605060907020a0510051f171203040309050d0305 69
    0x715030204001550b002d00c0c40d904c0f501100c4a6030000c0c0320560700c03071216030385911036509681c0d400641401500c02c1140c42c551003040c3e0080f076045c03600c0025240d00b4180350083c4031100701000540004244200f510701400480e2460140c100101401071411011883c180001840e80720380300e50209800d0703031601500a40c08400c5400200401802200c14a000050500d600a0b0b9003c03078000c00110b4480c0745005020000c10861058401070a803c660b43c84d581140050000010440c00c10f4072183c0b10300101003001218601c1120b040700e041c1d1034030240819101c03954085009031f0b01c039005041c01041d010048450b4000c08545014443e04182c002942c4e14145481410400d440c0440110410419910440c090001111000350319501c000017283d4880c0c101600134016003000d150400000b0580d0071458101164035207055a905020078200f20902c40f80c0d04c6901d242040f01650b14210205006402644066104242c0b940c40d042d20040d0020070f45101d0b0701e01400047ea1010181842842521103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 863761564 1250 863760314 863760323
    0xa1e0207050331060f0e0916090b0a1e021c27030f020d020a080a0506060a0f06080711010216080c060132031e060a0b010207140409050109 61
    0x449100e2800c1a82c2e5035000f107100140f481d51a00641d400000e01c45480e0580105280c03e814001c50900300304584020017240c060b000d1045030004c00100c0c0c2d442c0075006105400c0c180060088003000b03440240349115a50001c074035041d007000070440c440d81c0041040d1040d455410307019884903044c00c04034900200c6140b001200310050150510f065407298041c00d40034001c012800c5d01c0043e602a03100d1010562100820a134080700c2c1807001810154400105240010710b144800e80d620101d1a04041c00c0b00780071903983d00722408100d22464452400700180940300c10b00324038907050000141c00418050001001c0c0f12a881e04036a0551007501142c4a031241c034048a81302cfe070307402d150424036500040c10181c5503016050010805600c0101400c21925032a041d900d600703030b004ca00e450200d0310fa028500790940030315400c190014180c405007441c101410f100500c01e83c90481080002c9900700042d1a0441d040440b00b0011041220000c817104402220001050310052400c94010141ca070760080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 863762814 1250 863761564 863761567
    0x703030c110d080d240905060d0b070c0314040f120503221401020115090e0f12070b07032c160306020a021011030103060b03030f03040501060501090e0f0a1e02 70
    0x30b04000c00b0b00c01414070310840c040b09010031261800e8101c0303012003070b503003480c109004084204400c00c21900071582164020300000c3c940710860b00c1c0c1031070511045504c1c002180501c1004000c140d8040042c010039000c407107499042500749800c00c00d04225520400c0c85507039141d0f0310007061210034000c071504400621149810049050b9501c004c54510744140141513828085c521005d50041c0210300001804080d00f02d9268100300904004000c000d001c0079180c42800d000e203022260403c040020402c14011050300d407905451300c0404042d000b40702130105410300780b0481031004500103004502c0700d910f040c00d031411408940c2d5468400010705005409000e28000001e120055000303001450300c3c4d60a440d603000254854000b41c5044001a80fa021001c000410119126a001520103e0b00606580c58180841c0080006801c103840540310780c1d5454104102d1303507030010321480042c580300c4180030062600501100500e4001055503900503195852031b022101065000f070060041b10b1000c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 863764064 1250 863762814 863762839
    0x311070f0e130b0705130515040f120c03110d05010c11010e01020c0309190302101e17130318120b01082a1903080a0e120703030c11 58
    0x3101142148160000d050041d40440d218908040e00a810380c3d030000d0b54007016032550501101d8a501c11075107002015007103030340491a40d031002c01065020300d1809140740c03141d080030100c03904060103a010044112030742c1003c070000f8060074501000c0b660402c00d0108513400d444003191480c031201318000c00c154a0100c0140b100b9401c50f01c044c8072a01d428008000d5074100000c560300700e106005d080422903002b4401072046c3d1402502c000d0312602001d0001180c42d50faa40413501c03000f0300d0048a40816a4441140c588401c06070a14100b8112840c0c030b08801d40310341d0f2241280c20b0f00034014461500406a40d0313024540600410402152071410081001e9620705202005903c003074401c03148044207000011300703814009481b8080b03050119aa0a480c1c000049613402982c034002c81a4015813450340c1d145c01140503d0f03040300154012400aa51602440c0b001010508040b412900c900c088000d05070241e0000509101941e42c981018003011910342070480c840c0000f06e03040c44e07001c9e2024002c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 863765314 1250 863764064 863764079
    0xa030320030c070506090d09140409120804051005010303080c090d0203032b150501121103011706091f0b061606020730051803070609050a1719031107 66
    0x340f0800e40600300780d40b00d688440c40d2090f201d04000c20044001103c15405000395440250038500c05680204001112440ba96582c500240181c400d040032604000821040c0501480110744080300303070b80d08222960660790090032070f55014003003d81440010034280d03029100c500b0881c00c616002412240c5072482011034100c110a03840f0103401c0a201d050081420511602520020140014106240c141020b00448083c031b000c1d06490500e40c1c40d48049100d0600d10001075000e00030020100901182d07046074103140c10809082100c003640846915010240503c0442d052248030f0342b0701040c0d1411183c0061003502807103102034580c000ea030752010700b082915030041003020700c00d01880c415600d01c80050740281640650411481c2048040009040e20600c001e1040312400c0c6ca50b840d0000c00c10012a161018540044000c162641e506004500e415201203000b0701c01c4c025540c05030150328402e1034550217490410310401d9109454401014001c04515207249503503001c8a4070140d9907d903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 863766564 1250 863765314 863765317
    0x170408040f050405011d06062205010f050315010f020c180603070b071e030c150f05010b04080a061a1206060f060703020307031d10030510060f020a030320030c 70
    0x1c009078103034004000242410a4040c0504072034500b5003496030604d00000e50302d0b84020041c00c06600110402c000c0d070341c42c1e03904c1100c15000040380f00107464007410300700003419040c070316860042030103014000c0000d40c0609040b00a8502c0d42840c100747c0210300380300160324001844a17a50303848507400d400780360228034038081544034910480454030000d5645124055900c10000080c164076001c882d41c00321110410484580103220303103041c800c40031594035130300d0551510716444071741c00b62101103400840d44c0034002c080c0500380300c0480f90f10745807510a00b155110000180241200e4031883c400ea90b03043c40388100304040c1405001c00c62400d141034562600e40ca02180e1842c40b50401100800881c2481c0054030115070b4103070001c61920003a600c0641c1c16140700038040740c4000b509401041151101040a8000001c545000c200b604000002008a1080c3e4000500300f201120300116410380c001041c250303080c0c1609001886a82c1d502c40e04c0c204c14a400c10401c4110800001d200240b2100310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 863767814 1250 863766564 863766569
    0x15220c1a0d060e010312110a020d0605040b07030614040e1501080d03180f02040b1f090f1205060403050a0e04090818190b161e030f050a1e17040804 65
    0x108100482e50322105519a840400c0c00054000c02c8421440d03d681070107640c519064901034001c40e58468200e0380010040c06c4444800c1f51000e44039010305c4100100d030403185e60424458101882030034200001080c5040301c50322951320994031780311300d904000c1092224641c15607000c03044911a603103c482c0c40c1d580760b04000e422000a8500740620f682087c0341035074014029031040c0031456400b40740c2c0800001e02813803070401d40d00540c034945003920a2040c4005115251003600c816a4061414900381d100d42010b3b07011802c0c90a10f0316402000442c04164142c1c06945810001c0c0c40d004401e100301c0e1400b0003110010f81091500310500e06200748100607203041000d600b0f5503024030f04039800740701d070743c42c1c03580f43c450300c08400301078180f109046100182401c070300d150882492817140754a60003108000300901820710304940343d084040c1940242d08811850b9507040092902e001c1c200010910300b000b8841d9a50030f0841c02c03040341d03100d2254806000301c1c45034a50486079410103040040b855030040c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 863769064 1250 863767814 863767837
    0x5030307020d02070b041505120f010f08071a1b0a03050d05130c0302040b012c0108070f050304020d1106070308090d1407060903030b120601050315220c1a 68
    0x90b1140c0301164400142c0b0301c103441c0b40b58806410301d850082d22170b60004015844100340441071201e03006100392001064810180305460030000d5140c01c0610f0780030704003074002c0380c1c441d049a1402d010f0401c0100131514200c0c00c2400300e42e90303009290500e0b44103240000c0c807001c01c1d0241170302d0300007410383c00005408111102201048107466250403001409208800209407118244041025140581c0a44001b25060600001a4007001c141c001c207480850080d9008513041d000316081960707c003940c50b03441a40d604006000104c011b4003d4150701001384004d1049804900b054200702c40303096047084c800d00107051903844469500d0090155202181c000792203215004680c00d08c0c3c0c4c454500540029100304c062031414415485500103800c04c440203400381500c0c0c032850300703140d140c0001c084560f4120001805d043c2d41400101804e14108001b191507030080b038000d024040c02e00b101010140d4521480d4000d4100701031500d010070003010390203d18600b17801c2d00052501d10086000300280b0214 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 863770314 1250 863769064 863769073
    0x4030b090717060a09050709020706021b19120509060d02071109010f06270e010801060902120f04021f0309030206250503090705030a0c0501030b0a03110105091c0503030702 76
    0x6901035a4801c1c030005101d80b0765030384104081000040d035035200b05c03812801401595100d90f20780034803030f060b03074806282284c1d929400502030400c6459030390440040c8400340e028104c440b40c0d017403440800341c00504003d840d80708844200300d005401501250710740c0a000e00126180c0090f1880c05c002034000b4074007604d80703440030600c1183c9440c114804906844203210012480c03400c02030300302c40c507500200a80c01220407001c036a039000c1d07510f611148010014811048903a6040a43c07490a5902690140c0c1c5181c0c0140320f40c4104035001041076601c0700381c4011000070707950b03240009441042e0b03230b070b030040c03103000c20318151015059250b042404031034000d40885641e034851b01442d00c0c8201d002d00f01210b8614481000724081c51280f00110f810200309800c42d590213803182c002a00b0030700c17022022035070074000072010000e550b00b5000315120b0900c107e4450f18440e03d152181c0b4401c2070014502410030200088025181d0391700710416100000050804204610314a0802d542c1e500650324803004d8802c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 863771564 1250 863770314 863770319
    0x210603050d09180b032d060108071703030c090d030513030501050a0c05030c031513020a1d0102010c080a0b0111011a0f0604150c0614150f01050a05042102030304030b0907 75
    0x480b8013035404040005401440f17004d60b0155542e02da095580d00317018030304c40d000130008540350081060501a02c0c3c01800307418410b28000c0280d203440c030751004d8281150828420024401401020b542d0006010303030f4540c280c5146031a0868951141c6404a050b81d90700c2c440c04414400b0550043d407054203181d10800510810354401c0e215800f0413102240344420410018407030281401c0c031468922000352404450215540d80d01f01642c02010005002400c01c1d188505d40100d0200440301c8003c0a0000300203003540011700600d00b06000700848035044e02d40220501030391050b00081181100360008221900078100022880c1901c130175100c2c03150904c1c210303c031035034500441240e04941140250710210120b4030800c0d180344d84001d07416141a42e1701c0c5581e140051840d003105100d081405900301d0428010405c00c40300c0c2400d0a421410004288001c42c0025000402c441c26100b440382c0754201050018141103003c441400020340602010a00000b04407004407098000c600000568031080c1c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 863772814 1250 863771564 863771609
    0x507050405190e0619030206090402070f032309061e19021b01090b030a2004060c17270324010f090506100c05010b0a06020d020616210603050d09 64
    0x4101034120001a80c905c00400c014941400203208401010300302504040f4151240c90400508072819004036a0310072202c0740242e4891460b05035002c0450b40c180c2007418150102e0317802c1c01000803100341e0030302d01c0d41035401c0728207040155001004440f107040550929004004c0d16a000014809401154990980700355030040d42403038142c0706201c0d40d40d82035035554807480001d40041d4005900480c94580100340091800000f00080d114688600355248031a140914400c400702c8030340c006420090081600f410809505001c01040d40211145494070034000641400c1001c40a14074031000551201901103543c4045da0481310907412101c52260303200064411340300700320307021170703001d2440205015094082c0f088400118020400010104001d0022440f42e00183d0829001f50f400200c80c0c3d44010740c1040f04550140c0c0d4958015101400b4038000b82c0a22046a0400b21992441d0b00907451064160300c41802550840200e1780c02c12403041c000341580c000d40c00ba90410000c044039102640 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 863774064 1250 863772814 863772829
    0x204080c03070501050f2b06050909060c03060f060d09060e060702160603050a0b030106030830040809060d0f1e09020f1c021f020706091202040507050405190e06 71
    0x10341041c4c41721807516003400c03c0801c25038001100b510366094200e44000402e0308207100350791403401440300018260700341010001e09400050015183e50302c080100010300c0040f400b600c0e0003102c2920100a1180741600240c4680500c42003400c80320724188540c403d12000d900320640b821100e030b007510201d458110040740c81d881300c0700e05007103911071740c180400415219501c000c0e0700801400340000e0340040c2c0d800013030950720305900c161a40440482e11026241d4403410701d051249508200c3c00818103030090365140144001c001900f9804040f40e0075107182c54440450300110010b04041005c070040386152801005294811f501c4503190a4050f5921030380c91168080d61034004001e419810014010800c0e101034007101e491055484c10001401611011840241d0f0401c0c48582c100004007007000a02e403e80b168480000c2011441c0c00308005040e0720419011150150b40c04a4156159003055556100319807001d50000e0360700e9444842c60789152072040940d41c21249a01c1c3c41e445400400450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 863775314 1250 863774064 863774069
    0x2011e0506120d02030712030209030d020115050604050913050a1a07090527040309080318040b060412080703021e030a030f05070516020d060c080108060a09170a0311030a0204080c0307 81
    0x5a8170811440d404a50311100705c03035400d0494600513185c6440d04020a0138641020f44043c0903070b448090303c3c50400122403180707015210944a81e4103144ca010000385001401034100d4802c071550204980c1841000e0140d441455045803400809204801e10000c082c42d084507868000752440201160318074004a0300320002444076848020b03a05080fa043c0034803c0050f02c101c040c0600310000244c060414805410004003034050000b640300c40c04140301c296103d2100c0648940c00802044c001540c01c808a22032154203d9060b035102c917042d243c1a80342c00046170748143e000c4078074441d03800406400001016542c3d85076030b0a1202d00802620501036a4096079440007080c0244001341c01c445549120980b400d00040044460011503202c410444002e2043c00000414650041c41203503030030440560817040c0c0c4881081101060340300c03944041035084503002c00550000780ca0310070521036081445500e105181099490030181342c503e000358410300c100c000e00c1c0110f61340301c04c807850041012805c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 863776564 1250 863775314 863775317
    0xc060305090a030c02100e0307150e0d0507060c06150b0c0d0207050f0f03010908030c09120a110d02060d0c0809010b0a0312081b0414040f150e0702011e0506120d 71
    0x10136807440d0b0b003041200203991030000c0c1007021004d441410b50341c4c00c100560040140c1540560380400d841d40052407080c48481d26805810b50020138800920001605000c43d01c080c60701203445441850444e0151070285400a9030702520000414142ca8040040000d61407035400c613103000b907035090140e850f02d8141c403407d5032018800804002d24108140d2400791502d0040002805500303640d205500c0d50001e944525601401058000e06801c0c8444400400d4050100408040c409640c03401e80b1103080495250040021300483c0085481d450140c3d080d540e420714007030042810030302d0000c3c00c0b0001120414195800c0190b1800d031400c140c5644e0f02a280c00c0b20721200d441404074019500c6d0000a05030740d01c0414140d00c0811704418460180000d0801c405003c189802c8050030402039071a0228220204c81c5000701c491180264100c90300c2c01c88906941040642d40d8511050b401011049a8a881c00842c040110380381c0366140d02c454800c20041700c0172a03005103001400ba40da001c903c61100c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 863777814 1250 863776564 863776577
    0x1080a140105040e0c03010f0605090c250c050303070b070813050604080c0712260a0203090d030e03011a100918180f06290f04020d15030c060305090a03 67
    0x48030b0f0403e40c01181c0c0300031050048034081c0720081c000c2421507140002a10b0100d60320312040c0054901000c545406c04594101c850510121a1701051302040d010b89880c005040e02d403044c410003020b000b08400604000f01600d0f1a00e040307080007003010800311140703000510120001443e40305070058041065811000070b0006580e0303541d41d50401d43c0051040006403040c0b850015010408902900d0928842d03690304040c00510301e4825070f00f4055101c5101e2000041c00040b01c035503400001d41c0c00480301110420600d1501e0b0030265150000f00c401c1c01e0b059428a190300851118400c54140a84400d642c0007240c1019200101d40040b454004c04031a140d82e04c034807400c41016074000c07d40341c107024204000542850f580d200c100c4030080c001140c0c0281c0ba56164116425410401400c0c940c50140100c143c0700d90740001a4070024400c20140300e180e002c15800025a0b40364001d98001010300d011015a07512400c0c1414600714501c14100040d040c0000101c48201c0811506c0c1910340c90f0300c84c42c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 863779064 1250 863777814 863777819
    0x9030212030c25030b0604090b040f1101030c0e0603270304080c0405060906120f01050711060a09020f15090406030501141003030e040e010b03120c07060203040807091d01020c010b01080a1401 84
    0x17043d10b407101a00071940036480740c400b80042811400c0e200e00076031040303400c0d5664007500d250100285038001d05060500d0303c1c0c0000c01581a401042070510400c8c11205140c0d40e42d12148400b600e421022244c0c0541705c0c00001c0512007020000090040d15841c0080f00d5403448c0d540c04200c107450f000c0360700f2500100d5080100703440b41422010300594154540070b4072113021103141a0b9007102d00031101c0350005003295000342c0c1055824040c440e080a00c0703803028010031301c894000c120300c032058003034142c051503010981856603000032080c0d07814014000d00500219030b81e424864040d090340342024034041341d44070114082c051a0404201220303415160980c0c0c10a01000b0070004202080c0c100c0e550307540b210f0540780300d55000e2001788000c00640c180161143c3c401850189407140c40c0e04141c081d94401c100520140400143d1350b400c07540740079030114012445491342c40414503144c40003040c075800841d4401d4a0364041d0031500708035500b039a61000b140d4030380b0041e40540d2084240107010054004c0107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 863780314 1250 863779064 863779073
    0x31d09010f0504111608040f35160b030402041b020a0303113703020f030c0a48080d0c02071806080c04020a120504020109030212030c2503 61
    0x15102c1e10340004c00c902d0a20982481ea24454103009078100c40003200002c050214100c000c0404000d405070200300101c0049120314400c0010f40b045030000042c0301050603034241c1070100002c1942003110031000300d116a4a983c030303075815002902c0c200e20581c180002c42140751103034184100044c2980d4011315815044c1c0c0c078250006c100300c0e00d10b4002c011003004202111250442403404404501c1810382034480aa604110161005000c5104250040040108460b061010703a500500c1c6403150a80c0c0b07440f0f4110540d46040099400701c8102c072403601c1c0b2003040c0805c400c421310401042400c84e0100c0034121003045000c00b101001442d65405000c0c2040300c00d8035034030012649a190041321065516a02e0084c06048040b40c1c0006440d01c0304000c3c030120304180018402030340c0c00c0c0c03015818000407a4000e40700b020120400084150740d07a00160540e841800140d0086401520780c140300c200d10f6101c10381380e902040400784c40e4031407030910306000c5006003286080890801da074900c0c0e090840e80c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 863781564 1250 863780314 863780321
    0x140d0209012c091c0201060803040315060909050a061b1707031512050708191e060203100302180910240602030705070b19030b0d060603031d09010f0504 67
    0x411402c9144000030320b08400e60291842409040554001c150203010000f403480b0500a0700f100e80116414804204103d03070000040d141565801443c2c0451260380c20030410050405e5486400c01c5070078102c1c0da0080c054040341e881e0f04140074050070302403881180304000908c40411201400202c034031207804015a2406201074012280d40340c0400c0f82005134051030b0026a42d07811082000031600c26110801c030f001c001c904010001c0401030706070600500303400180321403e00c0010701703181c0300811a54011845203940c1e401c965440081152281000e00011085c1410781c00224050324a0f0b900b14404c800750030312654070070032040e401071103941ca182421401a050320f07114071014012100004c0d00c0303802001080d00240c000c82d4002c0d500d807a5581402c5140203a181d00100b03035040c0c108811100c1244440101104462900f0041b0340e0178028404a6081c40c1c807918003a25039441d000000c410513910200c03c0b07990040b40005069640101001c01c124100c081c49000c048184450041245042c1900b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 863782814 1250 863781564 863781599
    0x241a010809150c0415081302010c021309110f12060c250501050907060906090b071703040f0201030c0e0d120513091401090207050d0e0a090608030301140d020901 71
    0x1095488990308011182c81c10030050310341921040c80824280442060030724601e0300030540b03140900081c108003440416005c040c4e00081c0c1003100819810303096460354a504100c900724990301b08040340032814100c2c0500ca80078403107845903120300d03211281c0e4600710741200341d0080140080d1080d500c4512956006034005020190791040c0702c0d44044810101e0491504050701480003c0be840c45d103544030505040e1039070804c0e410722203520303c1401226031106201c410382e0a6620165a00d80903820031105080b000303502c40002c1c2400008000402c40b20221071309046100b80c03018408107216071816140004156880b1343c00602c0d401221003c14600540400640c80c01d0908030300e040d01c480c01a9001d0480c0c0c1d00800040c945034000461022020100340b8018002ca40302141440c000d59906070712450b00070350301c10030000b40740c110a4555a981e4000e500030810302d0802c000720360f80d48500c01e8881c2c1091042c021851400101000300b82400c0b841c900d04151700501100c1d03186e0a109409002d80042d6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 863784064 1250 863782814 863782831
    0x1050604060f0537140906180c030a06090c0e09060123030411121b090103020d080c07050a081f020c070b03090a0602120103051c20030c0102030103241a0108 69
    0x200c542c030910180e00900380107810711500400c8032811440c140301c050000500440d00424003490341d123142c0c0716180d00890704150799007015070ba030340c40e07411010028140c107421500e0300c0e520340760000a041c0d800008051080e038094443e44602e640c0c02005640c070004a59101980b01940f50039041d00c0d101313000003503910501c20700c08007811070f0905000c039103802c4901400080c183e020201c8402e29241a401011006804881c0a030b60b640c11a80420038090f0041030041c0504070105841020303410a0100d800604409051038068564407209180d4903459000c03604101540171001400700019802110fa503004180c0081840c0c502e028285813055000406103040d500030700e00410005002c5000820409840016522055040d1300300075042c01c00041e201003040307500c112503a4140e600718042071284006141c01044c12411042d0326415481201e000600c5544000000301c1001301000f9900501c2c10011031055000900c0c0c2402070403505964108282291103415125866100342122076210410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 863785314 1250 863784064 863784139
    0x20405090d020c064b09030c090403020a0f0501050a06050405060a0614070b0a0b0901060f020a17070803100603060b070305030f071103030403090302120106052214010801050604060f05 81
    0x50051805c07a1040380403016a4030501803030364118603854044000d170780e007282400c00b8540b05c01d640000b03035141e0110300880c0c0603070046000039041c1802440940c1d00346400142c0203001d02c0003458554000c0c0421100342d44010702c0c02801080354201407091903c541005090480002c0c00c0403030646103000105e0022044241c204102d0300003070301e0400a507005540702d01000c03c030a00404204050403605030890f1040241030b42e0410902c40c0d00240c02d00702c4c0380e003241d0041c0e01b00034001d000c1a4148902070000e410542c000080c480b002200c204c15400b02c0380c82e0340c1c0c00c0051907100c1d150800c040c40352110160000e03005101040c00704000c208078540103000c1e400c126400c1154000c90a0450304200c03425004140744003c20015824802403c8410401e50703802008824200030006652003200c004404000c50460640e650494103a8000d440031100350900c90710543c2d5411449028240072502d6502903410308800049000d020303041c210503104c4c0200036520036480440c6c0f00341e1a980407a818110f181c078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 863786564 1250 863785314 863785357
    0x1406060c030f04080a05010f0507051b1207031106101a0c1f0b041d0a0f1704080a1401020708040522050c0a031808090d060917030103020405090d020c06 67
    0x90b02d40140014010768001d0503040145081a508481062a4541d00c66040904010039540e00608540d41001c02180799120b0540003910546403d02d4251080740c0050002030440030701d60868211202402c2000440d1415600d42c030529100b01d507244030740700380500e2284058082e510508041c12941c0003031070855106009642d14610000300d141d00440c07096940791200c141b2030410740503010500f41034000f013250391149240c0c9a60395410140d0082c0a4001f50080d40c030070080e80444510340c0c01c910720005a00c9940342c040c126202d84841c007048490158554131810742d448180241c0d540160403090003030030b16241600f8420f910a10201200341c0f4400070000c0e60b400380e09442000d0082041a4100f82c882c2660308000d422a01800b030358500c40081d00001c580015018001c440b80c4501c184c40280c2e05888a2905170050400280020a0580781c228140085607011000c0c6041304e0003181c0c2844503407038065403581c031a404a6103140058007c641c00c0021803d107071005004116801106820718007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 863787814 1250 863786564 863786587
    0xf0912080403022503120815010f0302070f0501020310090b060d180233040e0402040b0a09051320090f1003080301140f010908030322050102030f07080a1406060c03 72
    0x21004d070b080e00010b062908050060145424a40c1090070b1a030074054900d041017200000d420315042203039410080e0341c0c01000241442078041c0c88141e6400f10303405030200c9092408034040d40084540544003140c0010000d0104503a000d40d80210002400340d51074814030f21014400b9103043c0d035101640348030039000100161960380c1150440f950301c0d8501d054043c120304940c21101700d44400e65450355403d200a010700030590329a42d40040d81201c00050310047c08003c600500c11a0b40518040c91400080052608450600141c80f52155410031000c441440104441d811440d10280d003281240d4001000c1130b4001d401c1d00e802c04048003030702d01c8141c2c2e2551030380307060751090700300071019460358001e4202401c2c0b4411140c00e80d00c003403c2c4281030302d080105450752030000622422002510901d040741c0120080c510742d00b46608500259a2454018180c134904003003901c247d00002c860b80001404000c1510440010794042c0e2108031140d1182001c00900350040b078900307078413400100007450403407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 863789064 1250 863787814 863787853
    0x7060b031b0a0b131809120306060e09040b06091b1614030309060703050606070215090112020306031009062d0c02151314060a06090f091208040302 65
    0x45450081d501ca420168409000098886078441d4100d02001c0c40401080581c00f6494030642c0c442d901d00b42804e00c103200d0f00301c0c050810b144014000c0b01c0a10040c90340241d25400c070748152507158440035540004042400f520090464014111401590129101d0b15207081c0741c6400c407004800c1d503142c4d955011031241140d400b008654840c4020402c1220420078800c4200c0580700304803029504510301041c515843d114000c00d40070403d0350301d200043d1595034010581c2c1d601a00642818004002d440340301031254480072802d8081100300c8030502d00c2c0391003402101c0c4500700180180500036694108580078208201c070441d81c0790b03151401d2400103034042076400c100c0030181c2c0030441d03084c10f441c200004881c040d1207003100719044168130107609040c00000d0307608226520b101c00c5210b0741c64100710f00d41810780004418035000d480140003104d820f42e0014400e80d4501e00c4200461b100d01080c000445e40c2100c00100700d445142c441102c42805100d1709a13215001c1c2c0180c0700d92000d441c01c0940003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 863790314 1250 863789064 863789083
    0xf0c1109070c210210090c03120512040c05041a0307060309020a1208121f03020111100e0c01020106061701051c0602040618081501270e150c180607060b03 68
    0x400c15a0fa040c000190341000011100644c542e81045205c01c0d946503002c0d08000c03030001a20000c1203454400900b44690304a44c0c0e0389101c2d0303540080509040c07404030001d464a1103014800c500304440c0c0602480a02c403c200c80b0300f002002404d10300d2510500764064070103044107986c4900080000550710000c82c52501070701c9c1c0300b141c1e45690b070020a00e44000e4044043c0400d2042280c10240c02c203a440075091080035250242001449041d0041c1482d00d0401c06041c8009001d08008149445450024160b40c02410903002480100d0311004119051200428080f000805120042000c4d042c008100240d0007038140200500040544403c4103982c441d9200d20009116182454100d1034030343c10280141040002520540103d2108a803e65a041c0a0901c1c00c10a800c44420001101d030741c186040501d042048c0002a200040142c4814020032031080c0004440000b6030350100c0c1c50f0458600c0c28078000340d500068928818000681c010000840e2b2180e6181c098007056a404c0140807170 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 863791564 1250 863790314 863790353
    0x103060909060e06070c050a20100207050f0d03120c020a020d0503071b060e04050c040801060602062d0703090201020703240f1112040c0b070506070f0c1109070c 71
    0x10848242c0d088030b40384c124001c04030300c00c0040c43c00a100c0003820209a054820b034110001d480e00b44850391031a0003940c0003906140c1e0000c200c80c05109180d80216516040359411500701c52003803030f00002c2c0142081849070050000d11500004201004180d001d10350b0048684101d440c00c2c1c2d40c9501050a462041c0c1c01920b00fa407000c1401d40c1000b60107600e004050522014550362103182c50400f800355280030b4401c5108070380b02c0c40028190144034041d5002021200c00034043c0d00da0719940a5101e4406461801005000c10b10403a070903020000f010300414950120380b940c0340e40d48041140103000030081281140540e0b44000701140c0c00b240b4418500300030058481200e11420421001c0b1450400812062400c0c00007101401178240706941101e09a0680c1c0c1800f651546800d000381c20054201c0c0402c0c11011907280184600000c00c05d1040314103444108150302202c00c05d40300b00e803070110010042140b9104c00c61807410000d0601c0e4200541d41405030154290343e0b103800586284841110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 863792814 1250 863791564 863791571
    0x405160b040806010501030209090408030604200901030e0f1c02031c020d0b030d05040603150503060a091b080304050d05010f0e0f1b1302070206040308070b04020108071b11010306090906 82
    0xc0703140c2d401d1184500400c001d090840c5480c00d02c00120303611141c01030000d0402c00000c000a05507440b035411040820142140c04030141c04652000d15407a008110f8040c0001e25015020700380040000d00c41c0c0e0405421f8000b0f0560020000024105600f803079110411400103001da10203400035200d07030030034441c40f14002580340d140101841081f01e80b0405624480d903c120b0400900c80c1d003280450342134900b2464007103038030b8651482c0c50141c1a810b03480503815101304001c100c0d0645c07039548003134080c510072603911260855031064031a42c042e82d8028050f05410070002044645440b52000380800e214400203e03c1d01642d0415030f0840d20340020000b841d4100b0440711118030801d0050101c501c0002c800180c4480c40c5202064110310000026480c80f036002529600359550702003500c00443d030181310365644078945e240c019044801510100d000c00c04007404074125602aa4010f50742241805802980ba031f01a2034031820031192030700480c1855500d02d0041160a4140030340714000c1c0c000c41010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 863794064 1250 863792814 863792819
    0x111507150b0108070f08011703120903091c080a120b120a02150f041e0b040303030f0c050a0c3201020714030403021c020a050405010909110618090405160b04 69
    0x341490f02d00611300c40400041c5043c5000498000d21083e0540d800b0070314001040340000d071024a14418441076440103a022820400b8a10001005050220040d644219010713062811207107c81c264030350050074400d040c003100ea84184201a80c40303141a00b51004074000e0f0f00c150100701e814100d0092604150064030049043d800c21072120074041400c800d000c0c2c94005c107464503405030f0280307000d204001280c0002d40401a1a8140c0760000381104180d60b0f035607141c0e00e2501400a103200301d0340307076903c40c1803040039408203002e0700684c0d00f515441e032501c9802c13400b1a680c0b800d424030b030070310301500000b65402d21800c0800c0412191286098803c00165181c925042000086a91120069280e8410070081c001601c901d48000708903040f03005030000e1140148002016501c25812190b0002c0c641000002e840003940c010840c1d0724060540008078001c1c2909100b0144501101c00d6440c01d220751140c406810508403e90348540101c003a1030030382014030001d110307a00003503000c40f21011010806 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 863795314 1250 863794064 863794067
    0x140f13170f0f07060c02040f0c0c14030301121b090606030905071410081b1603080f04080f160807080c06130f1205160503041d04111507150b01 63
    0x14020081403034024032228242d02c10b0320b0395801d82d13402180d0400c00044108400c54a40780c1010500d060340400901080843c01c800410709a40820107544c890709005a8030038641003c01100e068960b10080d4503442011526504500410680844200d03920000d001501c042c0c1441038901800f0b00b41c0d004213041007141806d03481d00c103682e04005441c000c0703401800c1c0c1942d910042d04407000158141441c10760788007211f01f82c1c903143c5c070660b41150b0440060300c8a031a4040b01410310400b44a03449410260700c03011005450110212802002400c007044a0000301501c50054884040f484d290601102c925503605038081c2c00000044034148008544c00301c98540c1801040d51103405400f480c920301401d922141c4402c0d40740800942514809284200003d104504540100c109040c240c0358481580c940b4541d02d43c4184a14220302c1c04241001d00f60040d801400e41c0160b8100c09010201006c003810402080002c0384028040341c800c10040001a0b400c1c0140f00c0c00e100b600400081d050001d000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 863796564 1250 863795314 863795323
    0x4050318031b011b1b050111030306010206040312060503070b030f01080f060a15080f1507021f0b03191406060904080304330b030c010f140f1317 64
    0x2528401d4100e6641d035110b00011010003401040d09203440f440318201c400390303000d011007109800340105400c089294251481c00d488041110001e23a1030035403071481e0440e280c2c1c490000f590164010380124021030b0100e40320b00d800341e01109810400286041c0da07440000e18180300b56019154841002c07007007080c080d07c0759004c41c0c01030610001a00c0080e081c00c3c01e060f2a0710340282072229860380c810461139604a400202c03000342c00c13444115100c3e88d44404040e0b60340c1c1091b4a0340f100c00f40440780082c4440744003180c034100d00f00c91440f9120140c445a21940b000e01213000201d074041c030078201c8000c42021600d040380d15050040e1500d0905205078014541040d8005100d00d02881400007031100207195241100d0f440b507080b200b600c07003408000b0040400b4181080e04a018050100c80d030300d00d001895441100900d008400b125241c003244401990000581102070000c03a045440c2c407a42492404001d01101c094818128136218016420144401361504413041f045001003030b45810388030422 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 863797814 1250 863796564 863796607
    0xa05100203042301110c0115150e090a020c121c06120b280f0b180c0c0a05070311011805100c060f050403080601020607090b161a040503 60
    0x200a519510746a1110a009454403c540702e0701001e00070340542c40a402c0d44800041e10409040666400016003800d0103080012505517411000b02400151003d40130481000d20310203485003d0a51542c808102e841c003c010320000301a41c08014010404c0800c0c000c464040b41d1103080c094032403094601d0040041e0803102d002100034503120050280314503515141c00342039485114030f4115501c1c20103504502c0c0010343c0d06a00c00322001e030603c004103140e80110300c1d44007019104100c50b540140030003843c2d01c0b5004680b83c6001000020404000380c0398010034200040310b080755860007182c5c3d6450719094041e40309407502804600054119a4804440d02d1070880c0b01c900da02240e8148000603281c000900b01000c14420a41624070400c40e05d0303000840341600300b0400b001a433816050240ca40182220f029005000f0180020090303401858040305842002e0105403c0448441c104400444440011380c1c498003034050501813035603045840d17403190f8800c9000c0c0d0384074140c25280000996003403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 863799064 1250 863797814 863797843
    0x3110304050303031504021201170c1c03030203062206180b010f05090a0e0c0c07050102060f040204092a09110a0c02040504300e040501061b081b0a05 66
    0x4020401ca155000001e60b0303042420110000001c4c554500064000e214400c40030210490540000890443c0c4424411460200100703075041d0507042001c0164210300c554140304107102072030440303010a1103503015586c01180680690000c010381081a01c5560710b00002c9180c0603102c0c0001d0001c01c10320020140d40507404901442001c403080f001030440d10080c844401002404110000581e8030aa100c0e402030900c908001480d041c11240d9042e0b5030302101003819544200000080c29510004807e84503004e41064400c1c1d40d2101d46c20040a01415001543e4040c8070005040c03c005034060308007800b8100412019a00b480d00300f01001f83d030400308200c4400742c1e0a02a200501c1d0f00400e9410001d64115000075440e43d807481c040c0c070b03a50107050181d071000c141600d900150741026401c001d070100480d19861032450f41c100c02c000030b83d002400340030300007003008810800c1e0304505540304818510400c90981040403206880400d07210b9903507494001d5011040301014040244890307206030042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 863800314 1250 863799064 863799067
    0x607050a02041d06190b120a020a08070b0f0c0705060f03060a050f2107091b09050a140d0303452301060e0703060504050a150605071509030c031103 65
    0x54031032003615008000c1010f4092010703990410005c21041e40f1581c40000000c00039103250b00d944802e21341d07507103409500324000e01480e82e010441c000001582001c450704140c180703280000081010441d40c10500210107980b1130712001041540c0c424010305108500c00c05241d889141200070003000400c83e500080c065040f45403040303041c0d00c8000e1820349946949842032900c80c0243e070050f20b40203040c0d0282c00042d01d850f4135841c2d000801c40c4c1a000c01a07050740d60411450f110400c0000b100d409214105001030b071103106200608010f001c0e0350b0750324001d00340042c03c04100e00c2031607204502010303000e921030525511191480408900544040201500d01ca121f8125a899840c299110448107000d00010000100850701c00d4004a0140050000342d03030709410200c002070094a0517008180c4500d0819002072116850f40c40f40c140007049401c0900d500354504034040c7c40c9540011400e6131440d260704440200b4490500480c66041e110b599501c400c0381c003d0800030700c00743c0c00300440c3c82540c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 863801564 1250 863800314 863800361
    0x1020a05070501182d0c08060106020609010c2a02220c0201020f030a11072010020c0d02090601030204050306040b0618090619021c0e0d020114041e020607050a0204 72
    0x85581c05901d41c8410324040610400c170780d040540c81a0301900401e003200245c00490304d040081a0305049600a4084504680b1408140c07800c0e03e295500c101e00240680c600071180400c611a00728400021824201c84070906401042c1c2d15680410b842c6048007030001154400c001510526200c5ea0140c40214101070703800e00301c40507520003d00b0303840b50103840307a10285448a0000490303c2c801d5014960084079460f00a48401d13090b2031238202c1e03105141d6948240b02440c00426079124030040100b5030421094183c0c02c110710080c0103801d0030304040c0c0c2408049191340f820002e0f140124021102c0038541e10340002000649210301c0c1000205010358401d001d880600021410b801c1a8490901b40e250302d420070107103009000e8103103030040c0444c0f06076010a401142d03502c250003040c1000181c81d840111780301c0c140e090350402d9450581c650194030000d00400d041401081c52940409040034003205590000345164004c4031050350280c11144e00f103c01c520b894032844150320091080c0c01c03003007107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 863802814 1250 863801564 863801573
    0x30b010906090f050f01020f0a1101230703030e0115170105011221050f0a030509060105030102040f0611010f061805160807050a1e0c020108010f05091b0c01020a0507050118 76
    0x88a910859010b001179090000e00b983c000c5c000303411212102d100300c07065440e00d81081c1e0520318a40102c03a001c00d210a8100703500c4001022544824641404014030340400c40e5812002858044412240d41d5a0384044841050b521480c600c005c0903201c8004420303042d1150703081c3c210740d010b0303101603103001c0d0517103c2e400095407480e5981048416601a0151107101c400155000c0c0b04d40c14641e007003075000140b6583c00c03d42541c099409000400200c492a81c4c80390145403c034822401386a5802d110034034208201d030b110b080851552a008400440d0a000300da06540070348490350841a030305102a0050103456107984140340e4008100540110403000008015003441000350146040181c001405400366001c1c0d01041c40b5454404000713062040c11000040c030307401f0041403c9000814070400020041300c2840d02c1c4050369002403001c00251101c29404040080c0408050740001091216441c40309080c030180c61011a513032202c1ea83d9050300d103416800c40d000c2c400d034800d00d81c54030281c01c070106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 863804064 1250 863802814 863802839
    0xb120d080a090c120f1e0b090f06150f0904030e1201021312030e030f0705030c0a140918060a1a18041e020405090a0c050108070e04110c030a030b01090609 68
    0x2105514075110100135541040c40300301d04c844d000541040415064a014075024210b482074841c0126001112511044d100540302c0c00413003004013590380110085500e00c200c8082040058000034070b801407015040000c60710800c000c0303409334045071400312001190b0a02600d06d201d18031251008500d004030b5445852008850b5000700c40d142c4c101c1e49418010503009130200104420001e007260340d030b030035542800356442225000303c034000e024001c1a10b00b0b60500303912280c243d5181d82c1007180c01c41642014004a6000201078082c45810859460980780040c0a03050203101224030105a1980710120208000050020a801140c00440800f0b0521480400d950000c1d0f004581c48510036662a8162201d00b100002952080c540400e024803d00000341e0000c10502c80d090345840700c1e42c1c0350010340d0120011611179010070102e41071140b840c6400e5000036507000c005400203040c240e04e62461071458000420f02400b007aa200e03002c900039038004400030b0080c00c0c50300e8580c003114107203240700500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 863805314 1250 863804064 863804069
    0x615010801080616051602060706051b040f301115040b030a1e060608010302090604062702040e04050a0203060f0601120b241206040506010c14010b120d080a090c 71
    0x200840454103025044040d11b1809100340c0003801140c44503007034140032006050585043c403568084608a1100e80552410354003202c01351a00018810318001040c0ca40b40182e2020101d0100000c00048900002c004c9000740b003400341580f0252006110700784005801485207000141800703100c200140c1680b40300311303a4040c1401d94081250840610842012854214000c0d40030341440300104c1c03030395880001c00e4101c90080703c10b1006a02c548083c0012680a4001c07200f214009044003e44410001c100700c50039403c141c001440c090b520142c800380030009403400c07a02c40e001280a5170a519081000c19008160710f0b51050890a000001030700c0054089000b07020f0944403014000c5642c1d401503401013588205601d41031300380c094000036144d6406070a1a030148440d407004030300c40d81403034400d0620801c4183c4680d03507440703469111090080000b0140c0e510a40d2199071101560300c429071000c40740780ca50401480001c620700b07000303001e42c00c000340851107841c03070b200340e200201c0c1d07040254004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 863806564 1250 863805314 863805317
    0x40303030903120e0c040b060f0301050607150911010e0102010501050901060e3709110a0c0f0c090507030b0f0f060c1603030e0405010803070b0105060a110615010801080616 76
    0x4840440c0c1c42c0907a00c038100103010020030382c50001d5030801c3c50804110601e07826000c45003045a004402c2c04c201c0d4034042d24140206103607092006014505000009004440c001e050540d0300c5640040c14505a908007a011104a1210a803500760381d40c115400d1071101009000920ac0d40d810f01d8003080c40154144a01400c00c15202408601030300e850006027034030003c0d25219550000220700b0031a03c49120000182d01c2080400c1c0003512810300d00c640c0001c084000c0d0641e1420001c0c00781114200f00020080d520f4003d6540e0390000180d107040c0c080000c181080005c0742c3c6d45080c00024080f01c0345e0402d540d006161055640400760b0f01c5540355421080e0031200c164560b5210000356152101c2d01012800d0030000180101c2816001000c0000e014030444082c0320980c3c844802680f01d0003090401805d00030303c940103001c5881d0a0019200c61042c03441e041502104060540e441c0100c2620703900c1c0103001e0450b40e152a035901c204502e002d07006000c0205000e00f00314900a4414042020100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 863807814 1250 863806564 863806571
    0x1e020405010e192c010e0607051810120507031505040c021c03090c06092309061302090a0609170d05030a020307030603020d05030a120501060c1b0306140f060105090604030303 77
    0x307180d413105440d2000c0c0403071501d00200301d0302419160303500034214010209030500c0b440f0000381600f403041007155a40c1d07100c0051080820001ca061040800c1c2c80d00e005c0c03041c03050891800d07004c10381c039118181c404c034510b0341e02107100f003580910031005600940005004074242076500780d0840c1c0000e103583d00d0160b40020981043c0d100c3e0300031001840400b0b401007840040020000b4083e03881040f0b10181c59140045d07442c080c0100120b803441c612903840c240d42140d00e00000620516203a81c24a00340420700c0b101600c0c1c14400000664054050f402c01c4020801c64038050200d000842300030f0020f8050390004080900c4e14042c040d203d030200070125014150000001840d041c46604044011503001e05481a03c041034946103403203030880840b210004015000c1190700d41d0060207000d040704c84ca40c8440d60b032078540c0c2c0ca484809004691382801042d003203100020003c1e1191117910721404010400440c0d50a0099081c540b500c00503080300d040100522019a240d41c0d403400325011a585800c001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 863809064 1250 863807814 863807831
    0x15010e030d05031f0b0c1c08010608190c0c15050f0621060411040e0a0803181f0b0a0f0e0609180d020c01110601080715020a1e020405010e19 62
    0x313209800c450340100502400c0c094002889401e000d0180103214407040640301e480014466003801c1802407805000002c07003250041015902840c070403508808084a0303000501c180f50a880e0582e00c202d4000c07030005582d5000f101c103012600a000c44c0f90391080d8410300c228108020540300c0c4200c040c10700c500c0707070300d03950031102c1000165002c40d20401d0078031041e030b04c540c502420a0201c070100b07480a6030040b400d0042c4807114dc0c0c40802c40494180c2d101d0322041c11038642c083e0080c91a02d520041c81058854901003004201c6000c02d20b615940440c140403d01d00c4500083c4a075000b900c0d804000c0505d918101402555640c0450701ea00c4901682d0f00d03c1c496603001c8041c1e6100201c2c00c6014614001c600c10482160381c0032602540c0020280c9800c84074209200240303503655002d00c20241140c00064050100c1030280740403030303212100c602c1140d4140306103032900b040001c1e40f0a9140114142103244008600b414000d4900600e005409400c0c189072500b02480741341440403941540590310180c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 863810314 1250 863809064 863809081
    0x3001140d052518150b09030601180209030a0b0723070f02060403240605060c120a090509190506010c03051c021c02130e160809120304080315010e030d0503 68
    0x190030082441051050000c140c003002c140040014513034424076440602000704000c0741c1c090031100402c0c400f5004103096072030f10070304441c40c0e2040c1d0b841100f1540c0801c456091940d0070001d4414043c05a10740c1390305418510b03000f405091102c4084460013500e44113040440c0c150001303441ca03240d0001c112040500c1148006992449a5007000300300305105610500c80304030101030000307034818105041000c0d0707485104000c810301030100700c51125800aa10300035003140c220050861040f05051020784580c807440010480d580c12203081010b0b020070100038045402502500d6040300081c28100d00c6407000e41c030f00400c54410480d55401d28016a17003200c240307240301d80c11180d410614404220895000b031102501a601c44502c200c42c0000204020074001d08800d1103a02840850706110358401d1000410389803624014800d1040b800380d5050740ee01006440c00840c4514411882c142e0b82c4d140c6480601c0e03407050512040c0d81002444a120600381d280060a41c40580ca41e013860350701c035070361251f4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 863811564 1250 863810314 863810383
    0x30207030305030a060b0c011b11071a07080714150408041e09240b090f1e0904060203071e020d050d06081e06070819023001140d05 58
    0x5c101b1081001907441142d40040d03001040082126100000e002c00000c011100740f40d81000f20741e0a0703080035904109901e98210100e2a92580309030107400c4c46070039152441c8d190401c2b04c06480c04020100c41150780c200c01e010749020b644030341c0120101400c00791a41e01050240d400b590540000e0310803082141850b552140008100e044400d00640655040c1c014050050124552004580c8440828a00142e1040e9181c503003018101c1103816540008100e00380c01c1142000b142010141d4180d02d45071a900c0281d40b01e240070741c00250762824502e9000f030800c81c40d452903811003400798007042c20555020850300d9a0303038218076085403101103040c90311009101d84e40c00360761544100200e40d4100041c111902c42d030007a601081da403041e40c96003c15980c209088034200314035043c0c101c0030140c012183c2e003d08110300d0500c8110300b52140368a9541402401c204e000b0004110b41c100400c40181100b189003104001610a040d600740c02e075698640d280d0996504400c2c100480465648091300c511 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 863812814 1250 863811564 863811569
    0x10b1c2a050405010207060e0d020103020f0d18020a050402032404110408010f0501050a030c03200904060f0f0b0a2112030c08070c02010816050d020f18030703030207030305030a06 79
    0x5503150350103a1480805400c603803151045038094000c1c100009040740c041d82052511000280c4588590303e12640114020f50008003142c1555206028a549414080c072442064419104da2407000c000f032801002482c1c4180d07031001d481070340104100310703281c494840310007004002da5a40c2c20b0780040e0400010041c10320340d01a0f0080c50400700e000141d072001500720103114141c040c1d00b082182d8803030382845a540035600025100b0616504100300041e031000d81c442031524030015000f00d0040500008240c8141641c090f12075640300d00040030499130512800e070051060a038100f040501e10404208640400c0c480d10500e0a07403460740740d100130390880700039078921391201b02010010001c040c050010086c5039108000174046500041a03107004852039510a90140c441e000343d555254016a804000c90003030108100007070144170640501c50000d00103010703224440a484424001d0f901d0212103610708024440d901840040010a40101d65201501c0e01442c0c6039a491343c0760100361000d000d09a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 863814064 1250 863812814 863812871
    0xf0c020a120b0402040608120703050a1202040603093e0301061e03030207050102060c0301090518030f04062703120513090501080c1203180a05040903030203040b010b1c 74
    0x5880c0c00040000c07150740b20b07108500c00c0f902040075a480310842680c82c1200d00c0b040e00300100c10000321002c680039034098030441d0f18600d003421860040d80d400f50281d81180d0301c6500840d4980414004208003801c0c925804901d180000c034518034003c100c6001c5d40500b200c400311031452a07482c040e50391401c0d00b0a10281a01040320a0140028401c40f0351a980510054005004a40000c5007035172010403800c0c02400c1e51810070f811642002c501c440100005086a541c4040010b41c01e2450340c01480070301015030078140807d4980e0b01d803e030003400286219003452040d04041500e440280e4030025054140c0340c20100c805550380001c101568a0320504440d207401d204151400240710c001900702030b05958001e420703944408551010720080e0070710b0400c031070324070740003449103681c204110043d540b40000000c0c4502000d580e0740b4041011103258940c01d82c00641c000080006202408203e180100812405039141018030502075815541d4024207058a64658504120ba045040003000307946a11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 863815314 1250 863814064 863814089
    0x10c06050106110f0606030a020f030c09011e0b070c060e13110301420c06020c0f01110406051602040f1802100207030203120c030712022505010f0c020a 67
    0x48020203003280f00c01c40718039140c610079071180e209a20004074400340140c40c0a801400046101c0c0d003001719183c400307401150188610301c40c041003550780401590090041e004070043e034441000748051405a00d0700f04086007001048240002001402e980c0c0407640b49282502c04080c940b400140c98601810300e1034100d90502140d03410340d07083c85000394100d035940e010220200132034808020602851808400c40c9020240501402c11f6400c09121403071841c03882c0c4071540c80c0c0b1a580d118100e03003115624440c240c0c444014140d2030074091040301c100c10340c06111107092030300d0814002c0c0903101c1d2200741c0f070724a40c000980c00d0854a0f83d801c004003501d0f00c0c1c0f42c1848100c020b402c050090b610410b500b68450150240031259450011803260162500a805040b040100c4d5145816580c056030311880c19210810185000c45d18682d440404401254041d142c080c09810600444068440000b500140507400800483ea00300b0019035030301e0202e0030304810001c003a000050040031254088030b89a481c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 863816564 1250 863815314 863815319
    0x605060406030204060e040c0c020d061d03040f050a03020306180309130c021203190e03070516080c011d04090c0f0803120a060806010302061c110301080d0f0914010c060501 76
    0x100b640140064a550b076840d9225100c20100704002c0d5101c80c0800e07808614960724070000750400c030000c1c01070503000b440041901d03a005491204d000d02e0748d045000054001150034060301c8150f41080d0018038089940300d100c2c5085800081c0c031020301900840001e480344007140241c020500c1902e4a03140020072103000752800444600140402042220040c020341000c0400b20701e6910a403802451541e1030950044174888505c0010300001000d861940300c180310703581c0002c03410404e0380740c1d2601c07001040409901c2e0540603403078043c54a00305414441f500c101d0803480e050404111550500458010a5108460801c11005600e40d0070510b420030034144003141d082000001044a00c0003401c2030030140d076803290000e0841c0c3c42c42c02000320f5a0009401000985002d03005840040d0010f16400c90f4202c20901d444100c504101d48820200340210042045003400c0c080c000d40020113040c980960404500020105001c0f8081c0f04468105520a03082591003454001e40302c079030012080043d541c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 863817814 1250 863816564 863816567
    0x1308030a0c05011d0d12060911040e01061d04110c06010e010611010b0a032402030405010c1d090f0a2702040b0102030a09060806150a0309120c0302030d09060605060406 74
    0x141c0400e079000d60030440000261041c0c16240d01c902d009680103043d14038800e0b0012141c036664001c03d00c043d1610340e40c020407030751401e1107082d8100002401060360340d0300d02a4081d0310140140d0000044c4484803e4841e0182c0101405614400e030860b00050b2041030b4200c281c10714010400d626440c0e10800002250001696013102e05a40c5a601d90007406218580388509940c1c091000d56002003079103004000046050320351040032803a4650500c00041c403021080101e803c200d0b0f068455a44131290140455046100800b1020092848907800b140f40320210ba01c501d0b0281c04449082c80310310008402c29100e912440c140c1c21040c400003000c14800705540404110000709074802e6282c00b01403802036000100b10303107000302c0707030303103803503020b00e107800e40980714083e00400c4030341c20461002c2c890b20a041408028000342080741c4000031a004141009000307005980b90303900905c490a60b0101c04260000140d41100014041c003285602e010701e04000904001da12141e0007440100d400314029 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 863819064 1250 863817814 863817827
    0x19090903030e0106270b030304080a03031b0806061902010e0a060e070510140a02010f022a030903071707050d0b090d021f020a030905030318010608030c060c1308030a 73
    0x5103103a00007886040c2d21804002d1041700b058100024000444412298085550700030540807400101641d0502c1d0b514400c641c18203da403038085000950b2032407104034a458284000084600b503281c80030b0949802d0340441d01a01c10400c402e8a00704110b241200414400d411110700c4588680a5074000c440074a8040040c2a40700303203140f114010360034007050608080380d84e09403000580e0b07207186120800e074103194415800480e2880031552949900c049403102070008203e26503248901040003400340c11442c00411b0f091882c00741580041007502110354002031000d003603504041c000041d401449010303074070300161030744000c0d00207112001d81421300407081101032160702080103540c1d80c0d240c400c6040ba1104548180e048200401c1d0303455841c00402c50b030141907861480e041c0065035446030746509140d44c0007218544e2030054407001c60300d004c1d1028004e0318018039801c1c00443c10003d40031500c5441c0c04e401001e10364402c0002c62000c031300c400450400002418030205132a0f0320402c088004000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 863820314 1250 863819064 863819081
    0x50a1202031e0d110105040503160309030c0b0a1107081b0a170c031e0d0e010c0c09050117070f0e1b040605090a050319061e050a2f07021909090303 65
    0x2c04c4d004240840f2041042c0034144c03003154800065407412240581da2560103021000c02d804102d9801004000118503038035050180540581a0382c680c45030010060004420700c014603166009149e007004090380028040c803240402e1500c00c040d0010a101244030748007a0b03440042c0744003150f12111081d00010500d090380e2001507040c1c89012506002c0300382076581c81c54004429900c046a410380952080490850300c190506d41004103003030030f0f1110155088940c200031801507451004100d0303160500c103400e40c0000c0e0722000d042c1c2d0b00d103800c8100284035401d2050b0000c000c2d00f43c0014511011610003001c10390b00da90a15912a42c4902008240350400410310b1702032403074808085401c0ca0000355410303640c1f0a6815000741c0b60710917a070301c01c0a880d03a0500007511080c48002001062703224052a4421801e06000003040341c1c00c01d0351418680c0274000c0f07569000c08000030041c0c2003c1c200044a81958043d0f43c5042d41001d5406024a10511035000703002d001c0c60445000300b01581500074100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 863821564 1250 863820314 863820317
    0xa1d071406130e160c0b0a1119020c0a1d060603060a0302030303040809010813020f0d020f1c0b1609060f0207031e0515010b09010804050c090403091806050a1202031e0d 74
    0x1100c000113000b540d03100302e0750001500301c101040024a0051468200f00c04101001104070700b084a18100c0502e0145120342c440050b800000d00c3d4401800d000c01024010841e10807102c503290b884050054182002801d0b85016803030000010751943c4541d64024010f40c0c4c0a41280e40d40d1416090000c030300d402c09074109000074180d102090a03c40e0300400d094095070010f00009a84440c0000c01419018a0100700e0300000c40f9010b204c116070b502c001c1c154040e440e102d00d4a042003030603e4151500d080c000e203040001d0343c4e90401c1c14242d07903001c81d00400362041ca040107444001c0c043d0003a0715181980c0d10040548402d0020440c00c10352104a4011280c40303401100c034000320010300303400d1940090203003800d120000c1c48080860361040c1c81483d000381c00b4500b0f40d0001085140414000b000403102503002c229030000800c840380c04407005045115003000d04105490a280c0080c002c080342d4821003800c1ca105107841d0f001d650381400821415285600280021501c0d08191501c80b2400030a040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 863822814 1250 863821564 863821591
    0xb0a020f070b0d05130b090c01080c070c03031b05070f170601140d0606080a03020c0907170601030c050d06060e100306241707080a1d071406130e 64
    0x2140c116000690030305844410741d0403800c0409001000c001840020310004888a28011101c046908446500d00401615002c0d00e4208040720001d8250a030140c01c4e45494441080307014042514110113106881d49407600210040069954071442004920043e0a0380500800052102d40d06481b49044030020111842045415500103448000910800b00308040300420032255140c050394000309544603210005203583c0f1090501d2030074101c3c0b0400c40143e031010480440c646040000c0652040c1c2500d422008a0000c00c4a441030740c1c00905034605043e11158610310441c001c0060300c09840b0701d210304105003555044000c140e4400803071a00d000b00510395483c03a03281c2c400d00030582940d80c00b0002814009013980c0c180c2828040130010707030821990603864141d001404800c1e070b01810840e500c200882c01c22200410844080c0f0b07490360541050000c0024442d6008940c4104591424031110004030300c24003c1030b51403190074140800602100b0b004500c0f6441d010400340548007803085030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 863824064 1250 863822814 863822833
    0x522030b0a2d1d0d0905030a030e0402030604090209040b07030e1204031b08100f0c0809101d070806150402030c1210030215030a0c050a09050103050405070f0b0a02 72
    0x41e000c440c40000300c04040004035094a034144420300c40c50b000090b4000b800a0b40c0b0200802104011240541c0907a43e904910a4980c11aa110800b240030b444102c025098400301030390041c000d81250b00800e8000c07038002c0b0006105585079031003840758a401032f1111a40d0320306450082059001124468003003072078120441e4000800281064440109112461400d802d54a82c1032224455411b00080103e0340341012500d40402c0c000d08940342500540400c031041c20014a40c156002075615008000713200b4100405801e00042c06800c400c6081c0d00025001d1001c151085410b41d02c0001146a100d0070758001402540011400c1c803503003484d031424003c00142e108000580c4003d803000d03030542c0c000f0310090b100e120065040540184028203018040c81c1d603136000c03c010610311100c007a8040d1010003044940704490040000c0c1120b10315241d40f0b000071020002c1c2005101d0b0003828100b55a80c5c0000303040100030099030020342051800c80070502d644881200141e071084d032074100103000b00d9010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 863825314 1250 863824064 863824081
    0x3040302100b0312030c040902120108190c120c0503010509030a09091a220908040302010f02070b041809080c0a05070e09030315060d0c02060601030b0105041d070522030b 75
    0x34100d5001000b00540140d00341290b044d18240c1020b0036035020540d042000250404003480102800d4002c410124820743c907080c1024104128085800720004070704030030100086c50130540b901510f01d00c0ea04076011034200d00340040002d5090700300c180c140d07103010148603d40800001401020302590f0324034080c15103444541042d0303001075103c5984401000388680161504504e00714100c044d206a120030100ca02a01800340d520304201511900d900040c180309659005081c08161003041c0000c2501524202c1402058841e07440350b01c0070f03500340c09101344803010b0507080001c809800c01c0b000e40d1214004c03c03440707440381c081700c500b00c5140c4592903000270305092212083e40b00d480510095400c56590012254000c842040355941c048002c00c60501002694070403c0e500321900d600900702403a0800c000740c11140704031005818070030140300c01c001c181e4483c0c40c0d400c6448a4407030180d0107922002e800b546d00780217a0407000f860408100d000c10104c0d40c029419000c0b640103001c00886901d03020013 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 863826564 1250 863825314 863825321
    0xa0807111c05130b043005071214030a210b0411040f0501020703031e0318030c05060117120906120c070510050f0a0903021608011b02150127060306020304030210 71
    0xd0b0402022020003840d082003982444000c10010074010022403010b61f42d90a080c102c1a400031310b400d500050000c028010051880ca41d9500b401d0021880c1c030030a0800035050f41c40200340d10304142d5074003000e804198150707004070b100140003034000d10400200c0380d03c640c1d040c3c00c02d018100300c0400401d4002040c1d88006004012240c1544514810100201d03001081c1c0c40c0c81082c1d03400f81511014050910120244407248a501036620305452011629225080110685c8070b5034003042103025032003151901050f00004801c245101030798a580940100305180030301080741800c0280e02e0f040140490401c002030801c00d02c6501a5140c00c6a00003c0e0030840e2003d494688a80014400082000140342d0095402500034012580f8503400118080840c616941101c0e0f000d035181c03814100380d80c40c0104244080c03482d80c0060b05030300300e584280c400303080c3c01486000e5280904441c400025603203440004a4401181d009000c51912400d201c8003a500030340d0110014412300c0245a03c1d51100d21 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 863827814 1250 863826564 863826569
    0xf010903080a030f0204030f051020040611010b210d02210d0e03031303020f03040617070509030d2703022d0406090603020a0b0a0807111c05130b04 65
    0x303034050030048002003c03070040130488141d000c4254204404000b00c2e10340700304c80040c180315100030035651301c2c41582d01040ea001500c2034420400f03c101c07001340c0300306c105e000d80e41030315602d1801010b04802c8a41c001d01510200002c00d400c007075481d036018000300d0303e850500c51803210340341125012070100c10202d980700d07040c044c0300c0718881d004002c040054010000400c00e0362140c2e000882d29030450001c06007140c1c010390700c584441306041c0c980d00070142c0500100c60442a030740003440c100343c41e00301c0150107010309490628002542800041405004000755010b100014048070303110440010050481400c42c818800303400388030502e40000d0182c800800c0c05a03075000c1e10307008040a4844180c40005036581985869003000d00b0340d0302054840e4072544000b44040c1c00007280f124a1801800300206541c2c02911000d001000b036180301e940c2100c05150480d8180ca00740c40b220b081e4400f0181000d0f6545004620084031015422110303070304c070014041d5600c0710054071030b18550722040c1d0b04041c80380d803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 863829064 1250 863827814 863827823
    0x5071a0106111b1003150b13080613060209011103040e01031401090c0911070605100302010318031d2206180b0f04020d151220030c09060102240103020f010903 70
    0xc280b1444d05040a1007a034100d902e00300800c4010314200311103410b40031030308405100840462030300c0846003000c130780724000d103010405000d1070304040b200d0f034001c0250460060b11064000807082c966911170840700ca580a01c01d0156503c0b07545401140b20004001e10064400800c40451910440d4042c411039010941c000548400c16280c03060f010084c1c99070708654101950300f03010b801c01041d420b0150314440d25080300020360041c03d620000d021540d1071049160071310100300e42700000a4106070f00000e030a07041000c00c6080b81116000802c0601c048180000e01b0403e01102c0b030001d141d6800c41419100005481c8001400d041d0f080300498510b002850b51140c030540b00742c401801d01d0707401058001041c0c200802e80c01010380a600e60307110950302c110703606d04441c6000c2c428010f02000d50840307840340104804224500d20006a9200444e26101348119030070700100317005030b008100082c0395610b200c15400030b00c0e82401645031480c03002d200981c010200344000d1051507105101d20b4041d03a910 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 863830314 1250 863829064 863829103
    0xb0f0405070519121103040c0b0c0c0d0317070509031209060d1b030b04060e0a0b011124130b1f0306090b0a0f0b0f010c0305071a010611 60
    0x4142000003415029004005120003001261244186880003c210a1140d200d6071960124818400d00316290b0110385d1203140001c0c018000003c5200d031440c01141c00174070b4420f031281202c030082414105101021503101002070742400c101600044080f20b17002c02402c8071400c0d941c0b0310800f681d0130321462001d16416000b508085801080c04030181c141c002d800741c080ba08254074103001004444210a45148041e81c050103c00c00c01d905009512000000b5501885100c1c0780a001045917040034001d803064603102c0d111401b071a4480c002e00d03140c0c00012001c03114580340c003441c008641351441ca07aa01001401d180090034810b483c014111405074000500100c66a80f45001c9002a88110076103581c0941050000302103035981c040c00422a0040c64050060f0a0402ca00c0045a0b00c02c14180e0405040400d403001a603545070083c40811001c1c00d12540d5520705180c01c99a0f8031a5520080043c1000b80040d109034440c1800113040e9801d61301c9800c114034194001c01d44d0f480141459452054a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 863831564 1250 863830314 863830339
    0x3140105012105010603140703120e03100b040207020a0306060501030b0303030606120705070b07022a03151b070803060f0109080a0f14010e010b030714010c0803060d08030403020a05100b 82
    0x22005901080d260040e0000176070141c03266a680000c4180b011031062540c0041d0f814003d1100034a251350112416003400c20b0041e0800000c40d44800801d0b008509559860006003810b46441d01165529a402024101015103914120300100083c4c061240024a0003100358a207080c000212401584001c0c40303103060154888201c19540300051a100400c0007d2201000181c1001000c900542868000d000d0380c050700344c2070211082c001c10050340c00800c402143c0c0c020352404200140dc004540c0340268040d62040d811a14000507080300c0c01d00080d00141d513030700780030f141405540104400c50301c0f00e008060b03940c0111013440190003440d4558100321240d50008141d1440c0d4009107105000070303280d041d00310841a007190f01e00045851305075181c00441c5074928090080d00c01801465007654400e01444d40020a2401240c00007445000d002011a0fa03566490400c0e02401e03030300042140d40d80c40c140c03900a459040c5200b04480e607100d980000441140b0600070447e4100c0b014088071070f1040f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 863832814 1250 863831564 863831609
    0x91b030b1302240a020607090e07080a060515090a060507020924060304200907050d020d0e030310030b09031c09020406231e0906370314010501 63
    0x2041484203d0b402400b45030728400d03d025958821074541500500140c680f01c00c0a00a420a00024078a03410860907400038040445461030360b540000c0d5a150800441e0b03602840100200300d07039000345170b00040480100d140128600000e05009038243c4498000035a1b420059815010764100294400d2048000404031804902d20384007004082d00d01007514820403000c01c402c0e520580b0259680782c40743d0b0018160100040c03e00031442001d9400020134600b03031600070400e0044d0351070512400d800151520f6400c13600d8002001d1540c20740c09603550f0f410102071a85030f0151503c8100c4074a0544400a4461940402503525200940d03101c2e18502c141d03c65007000a01170123600302d900c41c2e601e031000704418a2601562101000d41d28222005100002c104038a02a500c0341440b58000114950b0070f0710f84840b02281d400031011380b5010114078440c05502c10181d018011040c0c140000f60710707021440d030540305d82c404032805000440d020100d01c82499080c2c074424010410340c1d82c00d8030440451803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 863834064 1250 863832814 863832841
    0x2101060f03020a030b1915030302150408190c17040e1e010306021b0a082a0c061321060c0302090f011112030c0c161401120b0d06091b030b 61
    0x2080c0c40f0b035006c0d684c0e140c40d64902c2120f1000141c0d24800000c4401841055010000c9007e8840c08450340b04142c50166554046031141a80250005120910a0f1312187c022142464119071004584031441c9002c1d82100725500b0500c6100c000502b03407000b04819101482503500c1401b40900d06030440d0b82952960406580010380410b290500407488501c03800042c4502c0c8e4206108071a0150741d030003000c1107008914032131040b00d00c1c006803140090300b20550029140d51a604103032903140d01d660080c40c0c080e803d12a0b0740d00c0b1403121400390008000711341c1100381450344203104c0c000400000b01a01c2c0110304038060100c0e5650070080300911100190b000303c00900f42c1c010050111036120580d402c0070501344d0405d6541440f24840801d280008102c10f02400d000c007032140116900c504d00d401c43d031010482040d4200e034140b14070160b8803a012100e0b80c20980c00310401038000741c40315049190103401444100000c0e00d050300e400c8000400d00390001d44600440380c100c480032030151203c40480704030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 863835314 1250 863834064 863834071
    0x21204050a0b1f091d010f09120914040905010207050a030903030206010614090d02040612030c15180602090f2101051501090504020d0e011d010c050901050f07112101060f03020a030b 80
    0x194001c0e038490303017020704090249240c1d4031905c0d500400d1320300d00b5140803002d451810134807800384043c90b01c0034482c049220301481111030742102d0108a50815003085402485031401c0070300b150080300703103001c00c1c1900300a10300c0031240319900311140e9aa07035650848100070221180341142d0381c100071844961a10b01d101d00c154034001400010340ca9566138a8490614181800320041a1082000c03801d01c0803002c0d0420880318170b64024010001c0c0210400300101050303800070001507000c2098942a207400b101e0f9000480083c044200400001d20001e140e0410106015403540c00e1a000482c04002843c150700e1754003040c0c41d50040c3c0b60a000402c400794100711502e14000b40d48110002c5901000d00440060000411b02c00c4c0340e2074103541c043d50a442d1401450303c240801000480c0482e6444404c036913075181001c100b030381c86595a1408941003c05032140d143d0044904000036140c6841a42054000c41503500801002d9540c15080072010800c0c8000b035880b9007046020008544440c0400350b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 863836564 1250 863835314 863835341
    0x411090402180703060e10080d080c07080a030f0e28031404060503090f070f0b07020f100323010305030a0f02210706050a090b0c0904021204050a0b1f09 67
    0x40202020b4502c0c8504604448180003e521110100480848028081c0d004011200c5410040b030801207055a1410f088072140104034000d800918814004029543c40e42d42c08059071350390700c00310b160040107485d4890011450500d002e484155810000489810b129050301c3c10701007200b60021100c4042503031800941c00d015410100c80c0781203041400a00c054442c58442a890342801403d040c50012070303444641040c1c0c005007061000180700e1502d442210a0350100551310504d0b80b01080a9014000b00543c22480da4084a0089501038104603200302940449041c400020380f500c910750782c820310010740345400070800c03900340d01c1c0300340c252145103801801103c140c10180b049600e00c0c2404500107450090001c01c2070010000306001d060b410110482040c404c0d0951611703194440742005e0075610355150005511400c0351616010764082e40d6000c07040302c0c85481d01d82082c41d241c002d0040b0850b0983c10302400500c0c07899484407181180c01080e800c50b0705180c1440c01400042c0b0346102c1141d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 863837814 1250 863836564 863836579
    0x2122030e01020f0708010c020606030d0926010e011a0303090a0b03040303060f0b0405042a0c020f18160201060303051204060b130e010b03030f0904021c02070b040b0f0411090402 78
    0x20b00c01d0a08001d004002c040d08000042c41f1140040024140131000e01418460740001e2003000403c2e40c080c8869064440403145207010a83c8615607900101803404411001e5080000184074040d065010310400700b248243d00c206105500f080507100e1181c0c1512780e9010b08850028441c400400300596402440390074002006900c1d17004100c0b50714440d0307000039291400080c06001d00e040c940101494800d400c40380111202a2102c00c80840031192800c1041010b01d14040c1d05540d40c1d400e503010801d034040c0c0b43c40000840d802e0388494505040701e00e4541c14402d03030214107503184144076074022260160307111350a0010040c10046850301c00360094a082e80c81d8251a99150303111200400d1214038130000140e08044100e40c1401c1d03815900016100760000c0c00300880f5882c0620445404c1d000880f40141d0340e9201d0300b4540100450590080d284510101e03009082241002c000c601441c0a4002c54019035101070380b94085e00d1f81103174020451003440c900c60540c1c0c00c006005940241c402090328 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 863839064 1250 863837814 863837833
    0xb040605060304050d14070b06012f010c020c030d080106080406200307020c1801180e060c0c07151403060f0d0507141807050f0706022122030e0102 65
    0x50741d581007510103440c0c0d60000b0b1240f081c425003129004200550380d81415080c05440c0d2540390000c0c40082c1240e06026060101245d5841d4402d41c6411010310344400111010250000034001e02503015400d001d44501a14261545000111050010702a82d1055000e03824407504450001014000320384140c1c40301e4504403600041280051403052000b841922480c004130000c6c40c00910341f43e101c0c01540c13070704014000004800340c400d0640c0c03001e11580c0e8a000a0700c207014002c3c480b007000003500d80500c005120002c048403006011100003442111190780e141e0402000c4861b10310000c9000c00d0745240c500400a0100019541c02000280706020050642000c10040c042c0641c003150035070000e80c4280008004090183d00d509415104094541c2803030300c598681c0c01c80580100140900410310011180a5030102c4a145500c00c00a6403a000c08094182d020102c18880703420050609000800c07400180c44059a08210300c07808030312003469900d0a565803940d42d400c4604502074803056 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 863840314 1250 863839064 863839069
    0x6070c020607060f0653070e070806040c1403100314030306101106071d04020a1e0e01170a1e05071e0215040201030605060c030705070803030624040e04030815010e010c060b040605 79
    0x1580010000046d074002c8c5460244002011404010072851081c0d1078624250f645035400580d07140d080b07010500083c0c0e291105005407401c901207078402003900c4c4034401218500301020020314010181036800c485036400200d804d80307540d910380010007000c1d840040003c881c94807800701c01020700c14034004122200b00c070101081c240e81c403145114000c1466000d12046152400311601011724040c80e2104070004031100083c84481e0780c1e44005110200b1101003010342908d0b40c000140305c07210555005459030f90501035805058122030150200e40c1907443c003507002e00d0b2240720030ba5003c9968050261a100222402c0e4900009081a41016a036107004580b0341c407003000401003130510704011621050786140c41840c0c40c041d504000940d420600c140446512000110f8401d850f840100707100a0180d403200f031046000d1035101911040700b0009000905402855690207045008034588031003d141006541c0314100b52900380c00520041c04150200d461075200c1c02ca8120001c00c0451400c0c0d49000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 863841564 1250 863840314 863840323
    0x320280314180c0f010504060806130207051e060412050a170a020403050105060d1a0c1c0203040b07143108030a080a090506070c020607060f0653 64
    0x1e0303816400d0700301c0c82c0c1c6400c021410400302d2540c080c100e90100103101040c00080140c040c91003414140526040407695658801c0072200c0c4660508204544400c1d803410403d83e05c0f090112800b00000111641c1c503003402020808512543e04542e01034800604d8100845950b800025454104040005000011501c05809900a201340640581ca0760304508140342140e81c0039042910601c10016440c00181160a400c1e512403010011042c0ca681c40410001d1a40b1880b1aa001070b41e40c640d42001c1080b01681c0594001c1d4020043c03010306640c0c030700064860111340d681080c0701100c2880070601e000349500c1401320704245a120310204903240c0c040814141c400742c06c860215000030550340080b1742d1064aa80d440414000203100d0b042c255110b250f100c0b54058410010450800f49090a548540f800c503a00194130410800c8440b034031313003c0350000b0724030790151111808030f0b9030800c1c2d008005846124500d04014221107038210004080c0b80303280707c2205034012810300c044090a00f0010900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 863842814 1250 863841564 863841571
    0xb0c0c0a02030604140d05040e04080a0909022d090310020c24090c0907050d050a021c153003020c0a030303060810060e16110d0320280314 61
    0x3d8100b034484080e0b01c1710340e00b00840c000c040b004100302030000700581c09007241110b82194002f200c0c00d43e60100c0345800c40c3d100350a5008a05d10343d0000610040070703408114a90f886c1c000d00c07031603007041c0034269040586030303c50301080540c55803081c0c2c1e903c00d41d200345900420003010310b4022180d04030403040001c90700d003070140ea4100705088cc1302d0800000c0300341401a026a000c0856100c420751a03c0d1101805c40c0c05810314080c1d07260341e580e00040c1142c0d1203074100c540310000d600540c4d45a2451500c0d00c000707440c1020740d00d00710302c10b035100c00546140c0c51085803403c0c41102c1008243c003500f004411110343c4240303a0076021445010200f00c07003600c0b201d0340d5102450090740d020561700c1c1008200c2d8541548003510100031490214200300701c4200c0c00845030000e11903860070400c00c1400c0c408440d034012840141c2094001c40325500784513038056022145440904685c000c0030040f11184440074000e50500b942c0e070300410032a4014030010700c02622240c9175103060004040d42c800758203414a01080307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 863844064 1250 863842814 863842823
    0x80f0903130e040c05030a0503040e34020708060601210207060e15060a0b07030f0e040f0b03070b030c0a1112071a090d0504050d02011709030703110a0b0c0c0a02030604 74
    0x1e000c3c0401c2c0420012601d018020940040805594598890313030340348101d1103950064070b62003001c85d4940c0404903042e080610643c041341014405041d609082c070b1510382d10b9401600c65002c0000d81e4441c0800c1b80c41c81224140c54524900c3c80070061038040c100030b0000d5107045e43d400c0207400005202840b984180780407035001002c40d0185e44495040410016000b244a29504142004188010000c48000961603d801d4003a155002d1094801541c0d4108644e4018280401d00c0300f0a5141d501000c20340b031003201101c0305969100203106440c0700a6561408180b401c2141c0b2000d035000d4604000001110400c40310310200c072440030040d0760440038040301d12007007803050065450808107500d40c20a100b10041c0c4103da02240b40034001784101c1c13007010f018000444054003035a000358242050100e03100d010952916018117016143e41c0300700303400c50205107820b07008141180006149000a507010b00280003e40b01c0c00d03589803180c2c2140d00c0403401403040e40308034001a1014410385004a225 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 863845314 1250 863844064 863844089
    0x90c1106101703031b07061401090f111e0319090f03030c0518090c0903010f0518190602090f04021308240402120a14062203080f090313 60
    0x24050ba86901d090b030080104483d90003482071141510610544150700141c608540383da4417800e1801e10060070040000100c1210f45000009400c80c554000c1d00c00500d0012080100d909042d4030300d41e6a004000390301100030000072041c0011070a00004642003002002808041c00041440704141d8105010880d9580d000c841903504054160191020494450403d075081c110404040401850030b10300d0a44900045000b14886100d05000c03141c0600c0c2c040c009010300d40c000220200500b9003507078075410144484203c03002c89040412081c5041c821070700700c11285001604c031040a50030503400a40c0c401c6810341c504d480c581d0740d8070081200400c44126074001c10b00d04108141004003292021083c8040800c0741700d0382980501c61242c4c0142e044494500e80001001c1451801020850041441c1c3c40420f10203046c0d41c001410030b10809040401c03c0e06200425100c001d11040510003c0105134007101081c072002d45562103541c000380890403203040441e0303520551030006c0642d0014251045 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 863846564 1250 863845314 863845319
    0x11031801030b043323030c011106041203180506060108010e06030a0204091b0e1504061d13080a03150503071202010f090f1401020105090606010207090c110610 70
    0x2094042c101440708203d0b02049072402a26100c1c2040381341c502c000741000d00c410042c050001040421801800884903030411820400180c000c91000004585209200b50004405a584503880d0901c2d9140700d0400b400b010b803116030300c0250403c240b200c00707014075480e41201c0070302d0303c0c409440901840c0180d0080256050500001d4071102c3c044e00110f0300300b03040c10704200154030002221182c8650580b000240003c403070911040c800f1841c0780340780c000d802d012000524040311036030407401188420300054400c80301600300400c860303444c411940c10405040d03100402c07080f1000034650102c0411407904020030160346a405560002c03c0c000c0c042641c444410400a229420550107400300f50002c2c45843c3c10245480c448616040c002810000c035082a41c4919219640d01c0009204500c220000d290721b5006000c940d281c1a0780c0140150b181c0000610000310005596000b08010b03009007146904111880c40a041d403060b003801031140e0080084582601000780b80e00c644001010141d1060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 863847814 1250 863846564 863846567
    0x7050a1505161704090b01020129031906060302030706050c07032301090305030108161212140301080606091608040308090111030a0c0f09060f180305190c0602070b03130311031801 79
    0x4040c6c81480741168501040700b000012018a40c0d40f01c094454680944c110050001916000507084800c1040c000664103008002c0039401c400103491088058030700094450a007280ea1340a600f00d0300805900c442c6c410004990003400c1006c203401c21440c0b40b03100d40c0842a05d182500e0110104400084000004002e070000c06d0210704080e42e65410380d100c40c540b6000b4035002814440070082c00400345480030424080c01190080340d0b600c0c02c0d4218944039a034894400b500c40800f142ca2502840752000044c40e125408003000e2843c6000303803110781907070300d8507202240ca20340010a00c8405650f560f4241074003401050180d4411881c0c80800300b00e1551620004104204168440082c00a0710006011141e00300c2c6d14400028094a454921110490341040396550aa400a00a030156400d190688000c0c200c522020034025080350501584d81d4100300d0740c450880c41850860102403001c20255441d0702e9100513424041d1402040c1240050b9000d8119804050a014400c5044c02e00080c5035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 863848920 1106 863847814 863847821
    0x702100305150105030402100c08211902040b040b03041b08010207020a0509070c02150c0601060807031b05090d032102070507050a150516170409 64
    0x8050500000d0300414059825030b8222001076240682940140102ca00655024098010084407014122142d003444101160108400c003c4080c54603000003000c9444201e400d0a0740e247d041c840d07604201d5101240009000714010301c0200010380a45c019103040321414091940d4075950b43c5800b202909002e03103c0b13080da2581da070700031038440015806004910301c29600211807584940c2000040f4000710f502c8000907044468410041c208483c01e46030391003441c055207003400303c02c002c0e15003440c00903001030002614200801c58400d5250058030300b40d12030b04020343c0c0c84c80f0021400500c07a00c941c48100b8001c0503074401c00e80803d84200280c007943c0c03090035080c45401c92003c2c1c2c480f000e54460681038070240304164001c03030240780020706181207401c124400d910380e4140302019605500102151000c3c116072040f81c002040c103000000040b2204000300f5640c4a08041507203044 = true := by decide +kernel

theorem cover : BRFrame.Cov 863669064 863848920 := by
  have h0 := BRFrame.cov_init 863669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 863669064 ≤ n) (h2 : n < 863848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
