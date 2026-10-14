-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2429
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:41:14.794651+00:00
-- url     : https://prove2.me/submissions/cc7a7606-6772-4e1f-acf7-99794c1e1375

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 436690647 ≤ n < 436870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 436691897 1250 436690647 436690649
    0xb010501121103070507031b02130e030f0304051e12090d03051c0209040c0503011d090f0d0c020f0405090703020f0301020903010603060615140a032007030e010e0d0209010b0304110307 81
    0x542c5e83c030740c4d00c071140d050092503e0340c0848200d544c034000c072050001694414005980803540602c000461240401201c0d01d54407415495041e0260084108010b1080c040340940d00340784803094501c43d40c66006802901c42018203814103403d1014080e0403603a09041e840d4044440c440d00b08146409014820541603030302c0c10800307510298000602880764101800340c10303942d11490030254215410705250301d01c008801d000c001810307407404000404d00c1c4810000e01c10654000701c10740c1c0b0003505a08008044508802042e0700489400c6c0681c0118106449040d20480200c0040c2007414103640c02c114401064625582d4599007c0c0044145644c00b8825540114801c0c2d0300080e003a490007a079110300344404030000e014801c001482c80c01c01e0000c3c104172070411003140f400042d00311800c846616401c21450704044001070214003a01010b400080c030420009090300c44038540025403040040b202d00da928005c0d04041040c00411100c0c44110146800074401c52180c030829581e43d0200f07140c0f404c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 436693147 1250 436691897 436691911
    0x30209010c06051f0506070308061c0807030203120106080103081b0c040608010506030c010804031e050d05010e0a1508030d110c0105040320030703080705090a0f090902120a0b010501121103 83
    0x3031328200000811140d8194010441616900c0c1015015200601f070b056005201c1801a17982c034010303541460003c08100e070250b6010002c0713921031415090003560313030700005040000000010004501c55000317110b42c0d8100d0381d001e10140d00e400201d642c0020038040b4001d00031000e20841c803c200f641d5035180100720141413964000540c61138510304240c41c1c80201d1001c40c1c140210203042c0000710380d0214a0706e200101080d980f000c0020100c000700d03540c1c403c1500c4880910f260030004994070303003052102805038036054000e0101d0503100c03600c1d00c03460390940320307541e62680b042001c00c2007001a508504107031040c644c890360801a10322001070940c2d004881c1200040ca60bc00c0c41c04005103414544018807000300c0c001c41c101a8140d601400204029028805200300400c0c40500d43da11101e140740940151810b40c3c141ca0f036110301aa000e8500c020080788a54401c00098008441c000761003111290800d0002c09141d1924006640d60740103c100407a40070f417141401c0401d1036110f4015400780d61 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 436694397 1250 436693147 436693171
    0x2a071407060c02091005011407210c030305060a0b041503020c010f0504021c0c03030509030a14010501080d02030310050910030c0e1b0901020d1202041a1306080f0106030209010c0605 80
    0x2180f8030410201950007000d01607044910801480745981c0402c94800008403807000a685c0c400130b003410100c45068204808260102c02d170841c40c000c0c5c2c801010010107120351000d004980720001001003070340300c5008004840809010801c0038a110340000c082c4a60b90341001454215200e100500307640c0741a40b050422034a44042c0001c40c20901074402c45041c02480c001c03941c0940c0d0365252106110740c40003504100000c145402c03540d4092104520885c0e0040700c60381c22a410b10b081d580608000d01c641034035400341c4039010654a0020003168401c3c41c6059034101d03001e04000420200943c0606546440da50314a408030000e8030442803007015041190442282d460b0031081030040030101c0901180f41d1800307010100107a600000d095260400c241404d0080a009146910090245a01244000c44880440036a09510301b006040104007400d0003c185502d88a055607944000e807404010685001c004001482c426030180901202c140b42c2001a211907840701c800303644083c2d80d100a102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 436695647 1250 436694397 436694417
    0x21305070332070c03050a0c0c170d031112040609030903020d030504150302040e0a0906020c101b020c0a030b04030527010e030d020a15090507030b09062a07140706 72
    0x180b182c820180c0c1c0045240b411a644400d10b0750300030618045c0321203150600a0030000403003009803002d03038000a84030084885203130001c041003081d43e48920750850307004246404c0c0820000d0a00c40304484c80340854050b0b0384a2500c49075202c0c0300030f162940c0700303030104010765101000584e0303410000c401040c0030740d4a8a0715142440701d80262030425056620a041c0b040000f04190f0382d000d500d0950040c3c03601800248400c039402c040c00a4840c0e05220b5919018182628220341c40c6070703100c2c4d15034448c10401c14180410404013030b603442840003c0950302940c90750041000480056085070f00078881d281043c1008034041e401111900c00f9645d028040720510384010140d41e02c02915265024105c005000900d02000084c0d250b124428015091001034806927022034000d40007002169440002c641209680b0309054004c0c1b401951245000e0043e4804119101d0072210f841d0040d01f54110b210700140d201c01c1d2011101c0c4d01030303034040751000315401c4180c190090a0280074014442c60321090707060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 436696897 1250 436695647 436695731
    0x20c0312060a062705101d06030103050c130e03180123040b09010e0901080607110c0306060f21030a0324050d1509030e04050f040213050703 62
    0x40001c0400740201c0700c0e601e08114041e0f0240d0052084040403107040c10711041007440200800c036a800091300200c04601d0546070a42c40420414000030311100310b2000720f04142085020711080c0300240c00d0354404038641146243c5459240002041214009032411002e4042e90a5030400341044c5080030583c2c402d903000756040250101d09100c1e400600700c0010042511908600450040003d00f52001c00d00b20004c6e402042c000114060040103403039590b80d0380112555450381110b2010000d440b22020100b60040000d4800030750100402802c1b20307079105000e10803a00c0b15135108550010501d010300766030000307400100e20300016400266540e1104080c010b0161011510000346801c80c0c08000d100000c1c044002600f0754004559188005290307003000790f1096a41d49a0603030061602106004140c0c01c140800d003038a605507001c0c082aa58001c0c07110011200719800f1350007020002d0300c09407525090740b002e50700c1001d03030400089141c140c1948070000030300b41d51040810810340a031800b03031b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 436698147 1250 436696897 436696927
    0xd020f0706090821251b11031204060c03030b041d151e0103150204031b060e0607050a0201030902121b0f0f011b05150a02090a0626060a0801020c03 65
    0x140345001c070994035150906200b40e20700050b2010000411701142c600065101c0c2c40b90240b11000700039503070381000e4406281000721492100400d424400d200744c000100030091440181c800b00d40343c41d01c412880c0310340f588090b00900003154201da841036540c4418103241089070145454949180010451f11011200e48012640d0152100f1162045100c1602d08172103007185140c10349601420008860a00040f051302a00581c0c0008000c01600e54081d160902404c450100b1a04030f42c3d00c202c4401495410b001d41c80c070990001a00d25000311700140003550080c1c00030381a242c40504110400d6540031712007810010100340380b0311011410a40c00304a817070000c03030a86006000310703a02c40c00280e001f00040c050b002080100740002081c80800d6052040c140403403141e212070041c0003200ca1a04503161402548110090341c0314403d009004195580300e0a10040100001204007068120506840e80e4180e030060140398002240d08021500c080c0c2030014000144491008689406c9007a07107a42c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 436699397 1250 436698147 436698187
    0x8101214060109050112080c0f0304031b050103021e07050a020306070504060327120507020d2306060a090906060b070f0b01090506031c0201150e09100b060d020f07060908 75
    0x20390030308160046c13089000b600c20b2005003d03800a04a40c0c0c840381076602d46d003482c12986044285000100f400420701c2800116406407000c0b0700402030304a40c4980054040b0f0003500540f1a9094040808200e00c01480c401080094001d10484441c041c0503400603240800485003c2c00040f4042010041c0b1500360045000c1d4584401c0031100c840607a48900c10140e40d00c0038042c000c800003000400009001d00122007400da0043c104210192082c00c285400180305070040030228608200090425400300e451070107180006c001500481c80e10441901900e1000707000d41d5002e90300e84d07000071251002001010494032807426190195603070300b81040c0c9588141d001045d258104010060140d801042a43c60015100e2100c103440411230400c1303006112400350559070140000c270209980c041940540e10490326101224206885100820b05998419050540188045c05500300a40c201d4002c0c00a01002c11010360030042c0b0ba4903000280c4559900580782c0d1180014092810010091000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 436700647 1250 436699397 436699409
    0x61a0102010623190306021801170f181e010b06040303020d0c060209130b040f0b010c08180907030e0106092d0f1d0c0f01080106081012140601 63
    0xa1589071800b56680c0e00c3c0103c1d5400341c40440c0035a24501540c03018140740c0c40ca84a484a0404681c991030101d009500550580c4814a4410210882d940c824048101007821410681c20940c44e11081885000c1002c2c0110002d04c100600c018a0040d080000c000c1c03180c10101d0300200754200600080c00c603600504c0e49030051004000038400300382c0020710004a01c02914208820389600d080c004007c0c090100c3c0580c0c0041002d22000104125411400c45902c0449040261846408800c0e08840d00c50002c0340c0405e10361000d010105102c10060840440126035212144012000240b0074090499561020070b945918200c00e42030244100b0015109000040103107603181405802d0319030066a6032582c110303101040505416007600010030341000140c0c288000020081440d00c0c0b260280c6030b40c1c5031840341c2c00c203400c00ca24003000000900da0301a128103165908000c000c41e661303c4d004100c848003207110000007980d050200087e440c41806045002c598104040c51682042d40c183e2003c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 436701897 1250 436700647 436700651
    0x1d0105040b160518030a0609110111030408070504110903120a090f21020d0804090603020f040b151e1c0f060b19090e16021e0c0d0203030d0603061a010201 68
    0x400c901d0f604032045940e03107809192095250001900040d24060f68107000420042c100302c0c0000c00c00400e141d1000070100262507150810811890030f0ba030300d002c0c0b17204030180ca600844040001e801c0562105201400d080401880c1c040ca60004c00e00e0890304043d01e0442250000d51002d850f0b0707020312200040c00440010f00041132921480340088115204c000c046c507010800003500b1595848100038866910054403070316240d50300640d170020415840141d02821010384400c074149094410300088290003041e480c07135204107280d60500758000900d00416002c1a441c01030b1101044000f81c6242004402d080c07200d05050400c44080e1390740114034800d05800d000e1305104c40c240710003e5462100c01c01c0c1c41801c0342c1804100c200c85078813035681b02051000358801484420140030380c0003064400c164007154254040c1030300404034070030308040e441020742110324078a44c0c0b490282c211641060004044074100300b52032860f4411504c207030344221806961814019900b0010050040c8060f07003d0000f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 436703147 1250 436701897 436701931
    0x110105060102060f1305011a01020f030c030d1107060f0203070306091a1005040e1006020f030f040302040911031b1e03150901022b0f111c1d0105040b 66
    0x10390ba580f009014400300f100c0c0380000600e501e410410b070308809500500240300a240000b801041030b070780441d84a00502550080358440c00c400401c0301c402c0c0300440001d503e8913280c00010801019040c09075000c5003030030803441c4c011030a6400358100902c1100001680c1e0b01b000c00002e070480d000e9070f1010340d0032801c0030072114942c8400b00c442100c07000241c0f08023900c0c45005504551920468206100840d0050f081c024115485180f10081e00c400d6021940003001006007266a07008003040792251075003c0205100509041e006540c45034400c502c40c1c849054104002400c2c1240920070400002244000e8006490460400e00c0061119028800000c84490110b40c2703a084140d4408400c0c421a4082040030109504403205030901260040c00404108103c2c10380f84a4001c000340914200304001c84001c60034801d892140982404592904501c0040c10080d08414242141c040b40c0d00d054055600403503900d4001c07129003200000405203010b00d404081000090183c0a000e011481 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 436704397 1250 436703147 436703149
    0x1030b0a23040f02190605040f0b040503030f0a020118061a10050906160519151109040504020d08030a0f05160504060c0f150e190c1401030b030105010807030311010506 74
    0x40c00e030b08150031803103090b00708626001003045681070100300c240848540c000021030321380c0710002c5c00aa58105030747c030341f02c90350360f46011640c0e018500810340d240c0c008101c02481c4a2040d40140b012000c0c0d4000441d041001e4040f030902d46502000990310301c1d88400c00c060000000da06602d0740424121204100c045d88840b000740107008100341203000d8071000072124090841c07940c912035450b0707005048508003085003801d50b403c000228800c940342044070000e0001e601c840c2c003955005458068075541000c0d044010131015080c058803c0ea0044c04040000d03001c40c80c00001144038180450022490050030180c1c41c1c11918000c1c05081d5103000e5110114145a012080743c04480366460702c000180043e0814541d842e0042000800742d0030303030080710505030019800800700e007039200003580d2420441c549441948410881c00030801d01c070152003445010b2605800004421041c900003c4000500d00400e084800070382102c0a607a21800301081010b80c021840034070034220b440240a5810280 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 436705647 1250 436704397 436704461
    0x111005010e1f0b0a200c030c041d0109060221010b09040c12050405070510080f040308070c0c080604020a2106110904091a0703020a121505030601030b0a 67
    0x90541c0c1424240b00c03045040c194100c146040c060420790504680d00c0c648400043c10841100441403485080c242501103011000305207600321110160261200c41002010000204041819400d403403402c901c140c091180f09208070340299110340360050303882035248001d0400300400b8910007082d03509000140305400d682e50a40381c245200752404079001080c10020380e40e0f080340c801d2444495140c20100002d00500050490845900380c80c0c012010381b0b0b00700c088a5030902190088a0070300b02401040000e8480d05000360f0000d120310301305a145d0300641da081c41802c82d981c41198250301c860140802d51501074426001800000c1503190411220781803c0c680e20b9031000b000e0726a0342c4d26000d428a042d100c07001c940504600030010041400d107403405e80040c1c10285603030705100000d40002444c0318000e100310f412014031903c405000300c848110000140c4080a21078562041042c0000f80c03d0b202004080e018600c00c107140d028900c1d040039200212032110400e0344160750114000c4010840c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 436706897 1250 436705647 436705651
    0x3050d0e03120901051c0e0a0b0406181128080a0b090c100804081b0a110103110d0b0d21080702011404020d030c0b090109200a0b2206111005010e 64
    0x1e80e407882c1021514880c060010041520103108030700610700c8e0b003010031040255841c8558800e100803c0400c841d8800c1c840241c621100080072004903a4001c10186002c19203036649802041d442241900302040c0002021403d80c400c1181d030703001010104c104007031109607550003181e040007031028402d80381c005181d91184800c544180000207000c41c0034440c07208100c550501c682452850f80002c105101507035500300503416100d400a445a50440398440d00481c8201c400070202582040000d046a0b03008008003560158401103842103000060307503805540700f106004040b00c1c1ca24107101c55020f85280d80041010b001c40e40341002d110503007511402c44075007098040c0c50400030348000e494190761104819501801009040e03007046181e2205402010700da901c1020311251000d0100f4004114101034048598044035902045c403901c290003024042c00d0030314605a190138440d0880f6140034000341d40003040001e614074800702050b0f02c100302003212210312060030420740d0b243c000189508400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 436708147 1250 436706897 436706917
    0xb010809060f1b04080a1101030b09071d0d021c0b0c07050618010f060b03010f060c080f0309030d05010306090b1612020c1e060106140301140f0a03050d0e0312090105 73
    0x880c00520003c65985415a4080d00f25401101d001c9043c03400c004104e0108000007600090820b00c80ca0b8841c140136051030300070715054075031100303011680341100038080f504040c1a0300007001c1d03103031a030140c0e840d160a20045c0c800250b52103146042820403074010711005041034124042009450009800080c0c110f500591280000304554100c2c0b00090240484805030000d0b5420100007040d000b0900c00203604840254004ca81c0d00c6035a41e00c00c1e900d4003112003015108034001e01591103c4c103c07810045a10107030040503249405025051102240d8003a0001d80d83c10340d607501040304200007260201c1d0042400c1d00c0c0c0320640e100a401c000c0205083c05869200e0039004220380012207020040f0034402c0b46003450750703484d00801481c0c0a607111000d00c94500003406034050820301440b0501140c1c10380d11081c3c420f54210290605020b0740b001d58510194005c8059080000440c0e02440701210141c802c2d44c070b0f150010440410545022042c103400702680f1020821441540c0e0000100c0725902a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 436709397 1250 436708147 436708171
    0x1b220e070e0118050601030b030f0f010b0a06020a08031b070c050306010e0405061512030a0e09100b0403080304021f02010c020f061e18010c08010303140a080f060d080a02010b010809060f 82
    0xc0c0c0c3d100101c002e0240e0808c125014802c20f8110641580f01144981c0c21341000c0c0001c00a070300c0c1c1e08080002d45440c2c0d10840e4050380003241850041080d00000395407000d0340c807101380c4d00d001581f0103015041e440810b09a0310f08981e56803c1c01ba81c6002e0000900400030084000401d06282e2505034a440002e0420001c1d00c000d07040d414036940f80c13041c000c90320142c0001940d444014002d030180041c0d803004a458031608200d800a03101c500a8040d490640d0601110701c1e00f02411562a03a019074009842642d001304062010406804103054030300c1486001c0e400071503010b8101c1000380ca04440c0820300d072440d800007000c00c5042c520038510540401d640740c0382c5440d01d0b01c50b88580d5680d0040c1589107203641d424031082211042c2c00400c1c05048030701c01d41c0c40582014960445600a00800000200054910340442d403044649181d50340c12400041001c00c06940c0c070365810100e58412070080016035125140500550380007150503034080c1c1e900c1c0140509207030001d012213005200901c0b06040c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 436710647 1250 436709397 436709401
    0xa0807050a08181e030d050c040b040312030605211b030c0424030b04170c190203010f05040b0a06080105010812131508271b220e070e011805 62
    0xa4200030441c0003143c031000f1440701524141c49135071070f42e01c044131100c1c400c1c0c02e160128043c90415800c032801c441039540034a051034216660f081c04190150b50040c201a1690000300395030b924403103209210b80341ca0801116080c0c01540719410996460b29219014592000c41344503520040340340d43e20b1420440f4009440025802c0901c9501c241800e40301c1c0898900a002c02044bc61016050050b4010301804070603103881d6200c482c0303e210b51110481c17103420810311600a10609001d940302c040c4000c0c00030031118031801c030500c11594102c030140d984c0d50500c0140302c240380552080001800c4001d0091159604044540f40c0e5400c01450042d030700039001405200641d03000d20b100c00509480f4a804414640c0110010302d802800d0351552004e5600189404010030092002094070201d00042c4c48885800f9041c0926081c1070109070360400c1103031a0712074980c2c0e003003525540e50a5940c000003c0a10308442558904003558001b040c0c010703144001401956007011072070211200a401c0800e0796 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 436711897 1250 436710647 436710691
    0x70f030614010e0f04060f031101021509070e130b16080c130b2b020304020f0109150e01051c0603050d02010509100905010f0501080312070305101206110f0a0807050a08 74
    0x24022a07000818211069a02100f005019027603801008402d9007100ca2031004a010b005a250701600c118803581d002c0035040002e074000f03d41980d480404145180e100f020952210311480718120b98070021a050b00b800c1108041e0404443d40d0024081b01516003084101d00b00712000400c03600828000c1c40001c1a519040841c2004016000921122030740300080340890400280d041560b041784585001d4801d01c10a500c2102e0910072662010465880d404400e803050b41d800d40141c0c5480c0c1001402c100301c18006000ca240911107802c4181d0010f0000d166044c141d080a1600d040c1c1e03000c40e4101070500240030000190561074020f20359002400d00602e1508038010045440714030040c500b401d00002d2006000f0001d440b000e58042e813090415651a001282124401c803680441480c40c1c103800d20000c2d1064501d80003a52040c02c00080c0707000044a03184a58000c01b440c540740110010b01e84400650000031541c00517041e08100c0c0c1003020441028001035030082c524003004170149050131107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 436713147 1250 436711897 436711901
    0x1c09091a0301020f0a020607030209060a030506030a0602130e0610170903130e0106030b091605090a1208040314061b0a0203120f061e030c06071a070f030614010e0f04 73
    0x50044020021907444c0310703d04041d02503802084000c0d000d03009200020340802c1c024000c070340000b10300500b480d18080003802d095000348000b81200340c161140041c50000100749100401ca006840349014035072a1a044c0010880ca2000f01001d004640d00304070300c3c0415402c511001c101003c81e809a844966a40000f2446d50254a05181030b5903d45100000d0700702020407203506980481d82c080c4002c0040b50140072084a01360b0b00c0c402d10380c818032204400310f8801c0024210200b402003101c1c0d07201ea074901e170040418607007403015180b074640001c0c00c108004510741e03032411001010000d000145001d41240c8540007038220b5407014004000b56240c00d061080c0304a90b95003140111210b854103180d230341650342c080c0444880d405099000d01c40007038811030801c0b002d802000207005000c801c000c0024031000e504042070843d91910503a90680049040400980c880c000700d40c0e903828a00d07030404004080d50041d520041803c0155602e1112690340912000001c0c0415180c1401400d240c3c004200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 436714397 1250 436713147 436713191
    0x1060f0614251704050a0914041b0e0108060a05070216050609010c0803090f07080309210a02121b010c0803061203090a230306060915030319030504051c0909 69
    0x200f00303402100e1800c10a00850094415150162011a08036468900203002c45984012040162400c64001030000301900c83e0211001d003403a410b02c0080c0d546505c1d50300410710a03080324449402640410941c0c940e28400d03694803843e80d02c0180041c10301207003c180248818001d450207024000f0741e180e0342d640281c0c0c4203c502948541030a90303e18000703010a444402004174603c16000e00c800005081000100381c4d10030240007410b148588001140300840c4503035a003603100b4203010703c0780410b0150b500c00326104404e1800e600a001a41241c0e808101c149003030000b40c5040c8070310080100302081100054980c0f000d01914003240c0c0040c4242c4243c61402074034001a40100900008070380c84000710400c484031000b6444100c03584d551042059100d07681260101d401080140004103c00c007140d4003004d2195010342581d252180a02c4c10b01540103041009602203030705c4009101c104642040180032414400e10814400300c0c0c40240100b240c8020b214030304003140c441c4030144014000f6070302c800e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 436715647 1250 436714397 436714403
    0x806030a0804080a0213020a050f13031202030307030605060304030c030e210f1506090705070602040b07031106090c220e030d06180b01021e030702090901060f061425 73
    0x152643d43e1502920303a41d00c1c0480d02203004003400c4200002c20300c6c0358000e0340e148001c00c0d2035031410000e001d4851030454108101c82410520300f5180040030500c0d181d61080c00c07400e15409180d803483c2090002d002c1e20316031392003180a24410401c010200e5030144101021706e902d45070038030b150304080c000210402403d00c00d1000f48a80c4a06039240883c00081c8800302c02414016105c4002400d044607103000f03001c440a40e08120800d002403180c520601c01402c04920825005040540b281d01e141c4003900403020450200b00940d410131304c0c02004020a03a03010f40300000030314002c0c1ca0b00001c55000a20300707076481180044020704007005000e0350010092503079204200d9454441010040d006030a00d4841c0c070314540d40d501c900d840d040d0704501440030f089206030004d1215101c2c100d0380d8054074035440e100e0f4030680020720048005075030b20b02c0424055100340c00046a19810b1585841071001c41742d10410510905001c0f88001342041401d403500403210028007a00c000c008094400c0080d9104801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 436716897 1250 436715647 436715663
    0x150c060b060705120d0f020720060f0a0f0311070c0317040902070f0c05180f041a16030501080a031d01050405090f100614072312031b030105100806030a 67
    0x3c51004407040003600174441c00c10720030b0040f07a60503950441288191030700640b88501003126103020110300800d001090b030001d02018540f800e010b40169094002420000004a0340501d5a12803a4940100410018107100b11498080a6a5400f02031003080c80b0080c8480050250005402c0014040d507004060091003503503141c00070b14206a000700408001c44602c2c01018002c41c0c9810030b81100a000402010702d26480d481e442a4801030a0000b0001c60301d4610441c4014903c4800c0c1c5402070240c00000502c1c00c039822003080140984405821420140d0b100141da03c0210341d110260300180280003506007140c1d040200101e42a103d242c20254001d6280360900030000da21810b114411190303845016042500c5540490313100c101c0c00010329452030240016800701304100c0b1040c10034501400c4004d0350b1b032400f1068a0614182408106403550040708018110b140762202039500a488000e051542d0f041100203040c0c0c140c5103085c0410000700710001201510700b085407030b40d5550800c01c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 436718147 1250 436716897 436716913
    0x20c101e020c0612010f0f03031403060d020406030b0610081b0c010905061e060105070f08090a1502010911030303010317130e190b09090303070c050703061103010f150c060b060705 79
    0x10b004d0130100303200c0e141c2159208600016204041802281500d5159840a000c0d0303000320a1300c000e580001d800a644030741010f14840c0166a94400c031001544182c00e47d00c000c1c60402c042003d42e40440303000d2020b00c0304000812141c0d44d9181950b104820380c2c1c010b220f45a0a0b0200c1090041040f040e005186104000a0007060f22301c0f240130400c3c03035400c8201c1441c55035400c401140c00c0d00540030010001d41100d00840d0014088201424117008003914400480345c1e01c0e0b440c45150902108408003507513440038040b06011401c3c2030000c20503c182c00440c40c6514594400100c8200180e41402c0400c0205d1803051180401c580b880007001040b801810318208083d1a0b5450b0030b4200010300f41c9498126200e4a178140034100a2003016280061421555000001c1c2c1e080c028401044070103000f02d000110004070705118003518140e80040701e40e00c80d81003062808204410b03801034501e12140c01230107180d840d8070607100395040b944814081501020400400d00e68005d0600050041c001c2d0b0103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 436719397 1250 436718147 436718167
    0x10e070602030702030f030909010605180405010e0612070f090504050f010c020705100c111509030f010603030e03070828080a020a0b0105010905130c1107080a03020c101e020c06 78
    0x4058415a4000c17002d80b2040303200c48541950342d00c140a0955048012034004010b820302503809841311211440224a8010303c1c2d40005040b904240c0003410784241c28000d002190900051101903030070540d0041c88401e04104960181c4069445030a5081e92620005401c004040c0300d415007845088000b840652141c0601945940f010302441d405100f01c4544208200d100c0d0040104985e00407c01d105a08820400e0110800e284032035500103000c01c11000da0039407820840c24210111040002032814250b10b00200100440b070720380c51196001100030702080001294900c804020041d0700003d011050b46500c81c030b8446400b019082400c04500301c1d0203150040380c00034682c2c2c403a808002d02a030300c0c0d02c015911803005000300b9070000b005080b07100001689074045881d081150902030350628010358401d140603140d40040b8075075049021128101a0100008d180400c0304549070740d4109e0051400a0140044948200c0400380400343c19200034001c4c0000d411240d8003030a259a501c0e103001e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 436720647 1250 436719397 436719403
    0x20a021801092a1206050a0902070507050a0305100903020a0206030f0703060504110703051e0313061109180402191e080a03021c050906190e03071412010e070602 71
    0x101c55180c20600700070200700300002e05030420f03881d5404580c50288a00e11442c04550fa2510300340100c0300c05503211004184e070364851065a00514400308050390342c111610b462804c024450f4000380c010705c0b480c00d080c000a1004a0055901916104002558035583c10224607003d820b003000794100b0b40000900940745800e62070b103481000d080d1014441681e9a400340800c541e0401c258980b0900180120000248204010900c41020441070580a0b1141031003407480d0f40700380d85440c1503c40100180d000c10083d80a0b102154483c400d00504288010f00410300c41d03090004900c0001031600005400c540e0341941a18800306819480e165094964002c005232064103c4624612007070b00400081c07804000070f40425071545940640401007621824061060a004280090020034041c6649984400b00641500c0080600041c0c29480d844c4001d02500803c030b0460b030080d00064014040d0691042040fa240d11050741c185605420600b48680104074041c03c41226000d1203c000130102e42c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 436721897 1250 436720647 436720649
    0x803010b030f060306010602070b0d0e0f0f060a020913020304061803020f120c15071e02010507030b12122505010b011e0e0910030f0f11030118020d03020a021801 71
    0x102d010718005450f42c2c010107030303103078400d20410005902280e01800b0250088019041c7c00031030150208001010003802c0e1b04001e4522810802584822001940400300300702564102c460729504518094580000c9017035181c40018102a0a4000010800f0449a41d00c0501110f46c0d09001c078940f415107240c003d44402d60072844252a118161507401405164002c842790788140c24020f00c800100703003055120092008204c0d105220780d0f044d4124501000085990301d020703a036800041d4504d40080c024084a44182a00b80505c603000d0317107071005881c001051426030702c1c1120484d441d03903200702e407043c00484503000c3c0c015115030800c60703c1d040ac40c05400c0210031003800d889031120703180020b401c17610b440004e0000400003104406050094100100704039001340991000510300390b10303625001c0081c1d4213948215501f1034010703615014025003809124014504038002e009003482422552a0b201c400c1c0310103807140184401907000c01d4001c0020a01003980980150707800720040c41c001c1660082 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 436723147 1250 436721897 436721911
    0x4081006180204060c0b040c0e0a020409050112051b0411160b0a0b060d05041b06020d030b010207080309041a03060c030103030305060a1a0c1612020406150806120106030803010b03 79
    0x80ca400c0299024007500030744007901c1c2c1c1590b030344500007055154022001000703001074518071042c03000403401400300380e502c40c410069443c025a81c1d601d4480804100c5030141d00103409100181401d0b00090b40c0031034901d120760907001c101c26801a41800143c000d203941d030640c28403d04006000d00c0c9512002d2040032181d8018821703404a50707220f10440341521101d50000340c1c4040c040120100d01c071b199900540c1c125014282d207400050010091100080e880d420080140c0e00112700036031515858011068024003e10140040500d00f00e50141d4a0260f800c2d01c9105a4035854000724130550008034001d40c48000381142c02d02d0504000c180e1032a4420300041e0002400c00c40040c42c85d08244d0006c004490301d0555030320b078a8007040303120003036034128216070b107640d000b425404c1c0c900c1415004550042e0640c1c24a01d1070042d4144100411035045034000e816030381600140c20f85060f04150300f1940b1a00a4800300050054000b00a005025517080204454004000030a28001400183d0f100381c035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 436724397 1250 436723147 436723169
    0x203071e110c06030408030c1804020f1210030209070e030c0415080d080907090911030f0d1209110f24041814150102031b0f0d050a080406090804081006 67
    0x256202c00e0141510003103034040d2603a001000030691400b8140c008100c1d4900d600800e25100c2c45000001c2d090340c0c0110300404844401113a48409103401e80e46280e084000080b035200340a1941d03001c0f40300200010b186100b8418464403040658a050021040c0000020010450b900c18140214140a031600691441784203544c108805103016000c9140506528001082594504000b04020308041d407401c44039000021080b028985007044004406802140517017400003000c4801400310303800301c0344100c1d1103090074424400f04240d580d0307803801c0c206c003581e010701c0042c1d81c140801c040d1086a504403202d1701d021026115140344150140080e50b064800e807800c0f01268007030351420360301d14101d07902e01461004c012a80380ca0700c400d2581c50070401801901d0030280444611002101603e260745402e0f0403003241e050101d4020300111594842d2810103600f0560500c1d070080440c480144018586a0b8841500c4280901c40c01601d00504c1c40344102c4c2c2400c5075889081c409003000c0c2c0f10b10340c01c040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 436725647 1250 436724397 436724413
    0x81e040b0411030a08072607230c09010e06030a1a0610030204050112151a0c061f0b030a1506020a031706010c0b1015180603050402010f030203071e11 66
    0x3c98003140c2c4014441e000150701d4100581a2605480100c50307410542441401c4031180e680b001c4d01002034090b140c02561030004841c03a03d54490f084400d0406002003681040d140c00b811039451130071960644003000b2601c8956507419003c42c1c034003405501c024104401c407114480c0c240c104443c030103101c0d02c425514034003c901c0c0400190280d018070701940b40030a1081244144000d001d41c02481da01c010450b540511b5a5074180d0105424410300044d0501e100004200c0ea45440c100200c5400010184100e900d680403038801401c849141c4c000c5018007000000440c0c400c0c0030f6504841c1048000c0d2804958841d90b504c0c01a40c1d896415908a01082400542c0b5002c07008140e8240e01c11001038540984090a0380c3d03c240c018400140401d2004d9407441001c1491a19010100821740240c3c41d003400321504403000441c120101e9001004160070b2034100170050760f1007404034110780ba03107045c056243c1c0c5817600c0981d02840070641c4450344540c10703501c15001e6a4400440c45020f0001e0701580c1c642 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 436726897 1250 436725647 436725649
    0x118060221180d1716030b1c110906030d0c051204090c0206070918110c07090203100807061209031e081006140a180906061d0102010e0a03081e040b0411 67
    0x4d10304010f00d40d01c0760304051000411000e034141c1c281180110500e00003502415410002c4c07207a040d82104c1450110060b9401010403014401007803800d1421a0003800d1440c0940c00070f80d682e004a8210782c100300319055110100402008000d0040500340d1029840703503264a00c000060040702d00e0a030040c4940b102207415540a40100030a80c0c43d01d80c000741810903801e232010040c006202c146401282e0802c002c10001500340039840242024440169481c06c01d0000e42288181301e401015407070700561070401c80550003210b107180b15581c01d2000b05503040c5c941029070b802c40444050010f100c0590f04c00b401500ea01480d5148551280201d23400029140c004c2262585480d035006c80d902c072410086022118003468055074541c100c80540501541c840b05c003002500e180d6803000012480002c405a1303000418810600b00700f00c203100030880c1513002d001850340c40c001d4000140611260754045503d80d14181c0b29405201104080e404142c1007524281c164844100c400781c3d00d203040c0a4446034a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 436728147 1250 436726897 436726907
    0x1081b1e0d0519051006030c0e120616020f030306130e03031005120a170c0703140307061a06160606150507050106090b09010b0a020c0406080115080118060221180d 72
    0x100500212010100d0621b40154010b040388405401032241040040a080d90b4040c600102105424040d1200e030074401a0078000c0c1c0d03400304401f800d540180c0c2e9072480310080001583d0b4003460032034000c041385566150040041014429070880f5020000c2041080b504500e00301080b25010344510041d003504d000b000b5127a0b034403002c0090103d00e86110210b00c4004e1440580405940d101c01e54071016661354a40000c002050a0010b0903000401c2e10802e111245c49040524501c040f02003511030510400295603100e004003040d010105282210705002071035100201404403280000110006a080070304207405c12101124158200600071035040868040c40071411000f5104a1559007080385c20038503500046400700c2144244400ea005070764460140500a0588400000b003215207800040050351064204922583c101010300301c49403c0238081031113454003c03030b0040e01c40c51000c042061102c0382e05040d20f00205070806004482c440000e83c22a05107846c0100c90510f100b00c03506030780d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 436729397 1250 436728147 436728151
    0x140d0801080c0409022116051f0f09090f0204030224040e040813060c1a0c030109020c01020408030a050309070806010e13050109021f030b01081b1e0d051905 69
    0x360741d08100b0100c401800c154010f0038107180300411040c103010f10340c410140c034042c503007221402c0d030780c0100c40c403810001c481c0d001d840181c4000d03510500141c1918204400b02c4e440d40030002c0070061040b44580c400b034071402c1e01c06c0152040c0c01080c030100c40148441c0019402a0105900c60503031503891015400e032000b21aa01a844907074800d00b0a49000941c0101c9600104281c450010070060b1003144206001c51a015018548071b4403005a11400c2405614000f52012001084d40006001724154284d050b00c1c1152642240560b0300c0c42d0110078140613010300d40c0300200a220200341c090403a80c0040203107106200348411200203650720682165611800c1c40380741006620038000c600c480468184045002d4001c100200e240002e6034003080e88000c0c007440f14840110700c0d001d40601182e00d40206095000300f40381120321801c10940c013042c84200c006115150080028168902da44041c117200603440d84103041e981c035404591281c101400f01140d00c036040075048550800c04040b54404e840c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 436730647 1250 436729397 436729409
    0x916110313150504180906050a02070b01141203040f053c150a0c0201020105010f030c05101b05100b09070e12071203020a11060406050a03020a1209140d0801 69
    0xc0003142c50701c5071841181e60240560303410042e0420002c58101508401050300045610001802e01e0301d500302031003280c4d8064446c0102d54010804a0b0104898100840c15500f07241e280803100d441c004001a205480d000c5007084600001c500001d01c070030701800c0c2000301e4005a8480e04603a281c61007050303111030054501a49080078000000c410703507500d090070071310050203000341c0301c18280c003183d000640c0c110140040c00981c3c1c1040c030b40f04659080c01070300d006101d015100c1c80682c1c1569034200c3c4841c00d0307000d914020f10a48502240e114850b104d102c000c40d1238018228840d0b10582081e686520103d90041125070406050040c14108002c000344a00030320380c1d07150300c001e0304031041082e00d410040f05070185100741300001c503e00030300c00304030002c41d80f00350000c141c800d019150030b0740000070004000e44144800c0c0820010b95820078226501c81d605840c0c0166503101c0428240c0b980c0000007141d0000502c0c00700c141042008041c4c11421002c24101111500c4440b018121080503003400b5031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 436731897 1250 436730647 436730677
    0x706170a0e1507090308070b061906050f0f0d140a0e12180a03021c060b0405012105070f0f0e10030809010c0203190c1503150302150909161103 63
    0x100d15507000e07044850f40c020b911840c0051344c1d2139032502c801d145a00000c1050707540d80c006505000651074840046482003810801940d1084c0c034045001c0c010b40103407603146004a8000460340c00b502848130880f40001c00c2301100700001c082207607101c2d410301011100181d0052811880c04014500011040c07150400842c0c0145000d200c0440340e44180b6100080035000440008040700595506046e81e000804482540d281c09040d802e040c1c085c2d805c0750b0940c42c01580f40c4001400340d03a14140b0780418a806502c48900051a03138038000e4904641a0302c0440365071a001c4001c0380802e202040c0c1401c88902c402e5001041e20f4800025003100c40f98400104411410410f2880d107500500000c00200c3c0010f0070341d401200c5c0c01103404a04000c05404464500c0c40c0d400c14009041c0744040c440004100345820000181c200341140103000715804007030b00c602162010001e22156010454001c000f010f0881d8605082005610542d074038224000c0000c50012140c120224400009940d5204260124 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 436733147 1250 436731897 436731913
    0x7062f0a0f050f100c030c11030a03090519050606010801090b01080f100b07140d1d0d0809030d080603071d041407050a0303020325020d030f110706170a0e 68
    0x266070041520024201e07640e00a1100a40c1c1c640e4080c81111000d400410022440342444a0001c0440b41000d04c243d05000a4540f031908555001090340c0613200d040c10b00042d42c4506041251030b04d100f001c10a0f0f02c0906048410040090200c0e410b80140400c0c0c90b060000e07600c0d00c00d4801a184080f401600080b141c500141040d600e42c4110b0781c03c40010340d40200741d1520741a001d11242c0c8000c074240c80200113100b00c0d0900103002c1101e00c80143e100c0c508031000e80e440b000504410701e041d44449100710328414044090042540172280c006100030b04942804070403000141c07800e0340c1141c486200303004807440040c540301d50024004030048007452030511696180d40f00e5240c043e81055504041c81107810208a40d19800a80005503009030000e580360103813003a10303468034019199049402e0744c0c030030410707001600d580e00c40c031541c1681800d000c0c44240055000f21820040d0351002041842101ca0005900c1e400c50960100000201109001c40d41d80140b0038003a155a202c01c9200d41e442400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 436734397 1250 436733147 436733153
    0xa030c031b020f01080402010302130b12010f180e072d0611031204060905190c0f050a0501050309010f051302010e0303070b01210203010501060314150907180807062f0a 74
    0x4181b039005105040060410860408200c010711154020a50704540005c82c0c502d01c4a0041103940145403070341183c1440c40c1051110b0b1000b00042451100d0790344c5540c0710321850784040c000f040280210740701c04400300d03c03200401d08212944402d074081c411040320001c00d00c00d209541da60b900c006650000c2d03151845100ea001685003005100741c031004da80d18071145c00208180001c40060300c23141100181e15915080910b005451540150716980c0502020081034407409080c20480301d003403d080d41c50b42c1c0c604916138050141500c0170039000b4500720800001d42200458104500d000381d03600403001100b0b605240d0369100f81a40585410b0503c0010080200c501d40b607440c864005104032061221544c0c040381c259072082c0c10040c003180d200d1141c600442c0019510507441050b07211820400600d140c0403440f80c4402070500d90410158003d007850982068610320001d0003c0401c03507036040c0c2c2d80d14000b8014110031034aa10448652006090101d009901c486800c0c140307400504174401042d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 436735647 1250 436734397 436734407
    0xa0f0614010c0c08060103140f010603020a0e281b0305251101090515152101020c101506080f07030b010c08191209030519110a030c031b020f01 63
    0x10004882c43c4501d8040441d10364410b0282c80d00039072007141c068500403101c0c60b00900305403d21908140c9603240900c1040503a440c0c40e0144101d03411083c0d551007d80340c0402c040c0c450b028218130358400c0c540701c00300d00da076064483e405503400340180351820421020740c00e0110103640702524001003006560780301c440c00c40252440301e00503d049050054019021040640c29103111103000c0d5200d41094401002c10300202581c47e62204d4801c0302840007007440400250118154001400002007003181008041380c01d504682000c03800000310b43c5141c40c034032040d001070030042c802d00c100d0319002c1d000003034076a0092191034002e10010500280c40e90b81c6000440c0282204900f81381044201c000d0b440c08102014010818200c08008030800101440c00242003014162500208a498880d80002007540842a070b612480c2d254401e003003031801075008950403181c05c01030900720b0241c0b802d44c104158001e40c9102209103c3e880b007603005000d51900c140c4107a0a51343c0603410180b00340000360590b20036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 436736897 1250 436735647 436735667
    0x308040b1e060f190f0302130c27080f0619020a120e0a060518060606090307031106041d071805011209140601090905100203060f131b080a0f061401 65
    0x600400b110071510003420b2000e04c825802802100c0382c030707a024029814a80080200200e01600c1441140f9000c00d0003001d0b542000340c00350351814404500d0f111501c42141f108002c050803400c0b0360042d00e00c81b002a40302c250564050300078100e103c04ca00100030b07050085c1d488214140e203800200c030a011003000013078000410344a42501500c07888100088291065078020600d80d100790340e200c03144006007842c051020b0862846280c0500c1900d6176a58006280003d82e50300c604e604246819560204001c0e009a80000e000d12090a401403001003840c40d12512840540e60b45805081c03090100d06000d800c680100c500041d1409003030071072040c2d01d403c40d02c1d80521520501c4000035042c0c00c03107414418203820901c141070720744801506001c4200141000d5001c180e2045146041c41b80003d034401c020000e00c0e6004025414110034441c07081d0f40096603500028040e450001c21180c0c004060b440304131440c3d081d5a02d05000707218400b2280c8140c4099410741c6654502404004005454050750 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 436738147 1250 436736897 436736899
    0x30a030b1203070b04050c1005040603150f230301021803070e0106020a060c18030501061a090901050d050a0803070306030b0c0711010320070b0601030e06090a081b06040308040b1e060f 81
    0x41c00424803529282c510231150380c003100b9914a80c4039030901c18018162050b240c406010032031102d10901520b20303c0d603204012201c4800d401031910840c039000e0b0281d00d440113002039055202040039004500c4050340211240822015903280c180c4640c214002200c1c28091b100041c1e100c606080000782c1c00d5849480d402c031460802400b8402c880d042070b651848203070022529039465101c00c0200200300c41a010031500385e20705c1e0030300309007071032000c0ba41c211414403489100b00e201c062030a003440014010218801d4201c1041a030703a00d06020041c020707141500c81101c00703045250000b100d4041550580321041d07408414140744250340c9004602030015405071a4440001c0d0f00e9008440810384010409140300e958140300c0761512500160482d020301039404000d801410070001200008510a0b024641c8003a00c03e0322603040f0b12008002d0316241b4103207021880741c0c00c180300901d03801010080c800c51141100d1901c66a42116030b4412544003800c0c0b4402c91090300204000b0700e000c40c0091700701c1038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 436739397 1250 436738147 436738153
    0x20316030b0f060a0e07020d02062208030604060302120102091e030615060405062205010201060803042304020a0c06050c18011b0515041b030c030f05100608030a030b1203070b0405 79
    0x2448801707892a000007540c020b00941d0002058002d12901841103941c4110400c00c14101490195004a140006000000d081c29400800a49a40e07540c5d40200003840c3c0180005a030a240014410300030341c0403665813840b502915909000810310001104082e403c00b802614080d00c43c41004091a6008000c0e80c0e80308500344400715058462402414055003500558140003d821080e02102050b80c3c0046045904044081c4881d1200008642c100c8042c206440410f8115698914042e80d08000303ca030b2160000400e0840260b0040307888019038090202001652144141080684a500c82c0d40300c000542800c03c01881d8080d80307444501006000e02100d001c0619071302c5604140250100709560040d04080c0010300201c20159141d1240301120f01046500310707101d980e2029020300c00140045102c405100400509210700e50030f41e0110001407008a40362240d094503600400200c1e8000f0349014014042841c04003c428040180200035610380401d0b516080702c0d14130010400c0d11544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 436740647 1250 436739397 436739399
    0x2010e040207050a17090427170c100534030902120601090509060c120a020c030d0903120f02281106010b03010e1e01060e0409020402040909020316030b0f060a 70
    0x36040309800b03a0360045c0004050392440024104002c403000f000740152040c1203c00010610403908002d904003a81219003815010010441c545240c0300f51550600c1c02e0041d1424201d14500c01d03000345000310040d400101103e400b00a0091088800100f01d101e00809100d101c0440e0b400b0b9400b1902d441d00182c0b0305131a4a1011900c2854100203a10015165950b01c0401c071400741d0504c095508941c01c141c0c000d18041110060711400000504011003513603001070b8920000c0030400c102c0f14202e0a42c1814401030300f00c0d05018140c0d8009090080001d03052203c03c040c0d42030300d80b0231507103e035103407501604e8200d0800070318515100c409101c21081c00440815200c47c1003007001010700130100308030304a0f580d60400107441030422000d00901803901404030309501c4400c10a884c1d50540c2c20300e18041a40c0d003280c01c002000780080ca04080e40285c070000d004507a171000d580040d81c1d028020b40842c1e40a81040f4000c0c07000056030b120151804c0038840c08900c1c0110381c101d41c541c0080004212507651 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 436741897 1250 436740647 436740653
    0x31209020402030c070c05060313060b01110d020601060201050915130807020a0f14090105010f0c082506060e070c08090a23030d09180e01063503030402010e040207050a 74
    0x280e01c1661500e2104c503011841800700301c420b4400401600040e0b413443e0460030700b4840110602c00409c401441c0b140c86882140c000e91003120704001c2d9840403422101d070001c40040183d2245420b0050318015400c0000081500c480021803c84450304110b06610f140c1d00d25022414010b0440300c1252940700420201c4003503501e02040340040e00c0050b01003081c180c5800c40b03160740b40c03824090312806484110010402030380c001b002c100300d0309503500301072008200034906028184140c80802c0001c900c0c1245100640d0f41610500078054441c20301048447d85611640c002e585085405400280740719815400040754000a03091600c0081c101e9a2215243c400f4005040c0400104100c40780d40042180f80c5c0c0d00e420003858100c3d12180c100850441d0810314104465000c425842c90035a441c0c03402071880c0002503100e0f80050042801c0c482c40702c50304612060101000c01c031200381504102a007803401c014040f007120701071a416124103008a00b07034414803001c1d400c1400180c0751406004029004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 436743147 1250 436741897 436741901
    0x120c07020a08070e1506030402010813060e010c080a140117010e0106030f0b0a09111009080d0504181a011d031209040f06080309040b030a0807050303010e0702060403020a0312090204 80
    0x50b00c4040e018005050504103604811400140920070442c0710b8940783c1c0752038079a10100c9421980a1810008a554000444600b0143c0c00c1009000078900304150060701010351005071000c1d0a55100b00f0700d511012550740503221450031150301041e00600420106024598040c80c0a00110000c612002c43c10062400c4176402e070b0050301d51301d407450680b03000c01c05032414607a0f00000101017000910400c0d242d0700e08464219440a0190320030000f02407201d80500032181c014409002100d80c60f0088400041458106105100c43c03558030f245400ca625110780209030032007070340803401c2007418034200045400400d0220b895103440800208602c9036101802890712a10302c580d40d90f40e9035001c3d1030a020032a03003002c50270340280d440c20b5001c0c0811a0080122440c0a200311004140941c1203c0020708080d202c0310001d2441c3d034001003d904002010002d03604a800e084800d41031559200c60580c0c413040100c0700200160418241c0200003801070002241042544000003920001c650104003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 436744397 1250 436743147 436743149
    0x1506030903090b0f03070905120604031b060204080705010e060301060c0f02150d06080705011d0411120f0604150e040609050c130b310e010212181c05120c07020a 71
    0x7101490001c2003001207034102401000809040d209c4150007041803095680301c3e8400350000b42040f019886820307035500104e03810400180c000ca002c640c0c0301d542e1002d1960300e0070b092240902044407038803020701510f4082c00340d90403a07a084d01c41d0a4919180d90b2103980041c180c1c0e804a905c20215681c40b44460b1040d0b024000710840708400045003400c02d00514605070440d444030b07040001000c0420980314107480081c1415405030340c0814400d1160b4224016030050034459080612000200402e0401111078a03000e5030b01a81c00304201c00951070f610070010740f02c2c0541032081400401050005505031300900b8140c0c052416103082046200024600d55045406080d1807031b22404820154541000140c4001c08243c1040c03061b540088a00b1040d030600441c0c2c1c01c18165601021030144102307404603640c403040000410076600d80346105182c1d0201c050008802032240c03080040984c0e4214414510b246507640351542000b5600e07042901442e801400e0281c590401d00c40f560060f2a80b5019070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 436745647 1250 436744397 436744417
    0xb01050d02160b0a020f040605090d08210c0702010818070305061501030e010209090c0c100c031a0109052101060b0415021902150a0203090d08031503011506030903090b 74
    0x102e911502070410200c2d121000d013101e50854410891004000000301c1160211103803420030b40d8a492024000503110584030310b0282c2000300000740104400001140c3c6182440300e100d9469590301c40c00c1419034603004149000b0b020988a402280d481d0f1187c1caa001000c6443c4021a1000b546954486041c9003003661010341d0001441c422001e00c0d0b170103025100114035680002c5003480c5141c40041c61a0401078003154140c14005420780c04220144058038009003c6103007802021110344000380200812800b02800541d4010082030540c843c812000032600014403a00f80c46c880550400913414040400300302e150351b5206e0001d070710107500b000350004006a181c8400040e20045000c0d0822843c1c07140070141d58030340141c0000503921500c5960030001103c00080e158403164205034503501c5481d200613400440074060074204800c4800440c890040c4089100c102040d0310245420790b60b0740e004031f18440741e0024040c07107148d210b6030041c01114000e2400c4030074075580314503010007980003a07440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 436746897 1250 436745647 436745677
    0x604020c120414120c01230c1b0d020d02060d1d010203090118050d21020313050106080c09190b06030703020706060e04033c0207030606060318060b01050d02 69
    0x40183d122075501075007003404181c50740c18544490781001070729601e003041800d0503c13244c400300400e22000025410b20b200e0a105016070750781645020159200b40c0c90072005a0245005110300e00c0e800c025250180e8682d014000004e0988550308100580e00607041e4240d0702682d5102c461030f0060405210b81642e02c2c0b0100059590030074510481c00d50b44000c080301a0481c0d8001d00c1c80006000050b18520020140b0340704c0c401d43c8044407071904991029a0b0002c2040c008003d004c5041300c0c01d880c200701d5034032440c000c00065681d01c00090712550b2000700c60741e0164050001a181190213034246c4940300745c11200003aa001120300080640c0c0054034424002603011801404003c0d49100704806003501801b002854641940d00a01d8020041403440e1350465989200b145c29a00a20703020100701000c0b80d0400710000500000d503036644611059038100d0500600044140c060300c070b030452207550380d0041c01d51156240c55030000b07042215103003030401c1800c002100412079284003402921041d0680 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 436748147 1250 436746897 436746899
    0x7021002070303200403020102072c01060e090f0610030207060209031e070902030c18150c0a150204030c120312050103080307020d080f0105010c050304050406030b010608090703030206040b0604020c1204 89
    0x413008220541d40d042c0c0320103410410003400903030780005038442240d18448600140340311116101081076401900c3c5085409074100220b0f044d508a0389601100000340c1e0042801c0d44c948001c41460300781a070b20359800003a0000300c449964400d07001000100d02424000d807038500808040303403a00340c180d80d0781c00802c1c0d8040d0001c094050240300c10030061111f200154294100f05486480e5882800e561140c81414200d07114000c0d143c040100070243c1c051720b6420b443d02d4040c03100e80d8850740310140c200d0f5030032030741500c07940801c1441c42524152608815840e01d40742c10042608100301707c43e0821350512605160f4002844818001c0c1c501071403281103015142e0a01e234801a00d884402c540c1441030041900411004030318180c0060704545d0300b441c01245c610b0711405d00b981180724a4210310780040c14450701105110303000000a04030781459031848000c0ea14090410b0b01c44141c2c4c003008006030060800f080105421105954001c2c1c0014401803402846804e024134024002080700e80c89032010030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 436749397 1250 436748147 436748171
    0xc1101110a0507260a0b0a0906090506042004150626070302070b0a050618060103060317041508100311010504120317060604050a030f030c050d0810060c0305030f07021002070303 78
    0x4c4c00d40282c03200c2c0c000b02007495950303070ba24004003c0140107030b852540d5a1502001d0080642111581903003120941d956424a03040880311140043c0c03000404400c200324505103401c00b032240d403c9441d021070300c00d102141801030880303001445058080103203d00b4031101c6402c2e40308495407070080c401074600581d502c0c00d81c94603102e0805e000340001d9920f86008100320254a8514030184c60a4078044404113a65036000164010a00c07030308080c1400101021481801d40706100410135620422a024290301c203881003115002000c448003411221a04001c00006006c515101142c0c6c0c0d0504102e0300b41502c2d913004e44150920035006500040e02c1410340450006180702c2079801c00407c0e20400c2ca0b160511001c601600c0a511005008400b4610070318141407103407800d00c130350036407100c19100c4035966518001d0041c1d40030342c2ca43c800b41425500020340c0074090070222100c1941034490504590701d441e0300607010f100081c6441d0030b500440e038550040d80f40c94130040c940356100c4d40b400118118000c2d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 436750647 1250 436749397 436749449
    0x70e09071b0201030e011104030b090c151914220f1a0705190c080d050a0e0910030c0602030c0705060408030f030a02090904030804120c1101110a0507 66
    0x25000e0414091003110341420381180c0a0300c0c840058081c2008520000c03001d100c14010100d0b0281d0540c8071001160100030070941460090084491400722080c2594440c03c10103000100464003d03c064100420b41507038800785240401040b030b6040c10f0650b0300081c0170221243c1d125004080311198201032040303204c0000602c41c0068070044d0010600e060803c05461003c1004e40c450842c148000304019040240802402e410315001103260160300606160a0b41d04000310700543c0d950340120545140c2e001c0c4120292804c01d00c1d01d40d25000704812032800c2c0100d0320405441c400f40d40c4050075011000c0740309000c2c100f0082280b94000c0d592601c0d562135450810581d43c0100d8466982084204105140041904c52004410482681e6616004000e00092180005c165085808407040006050b0080c210707d00c52405001c44c440e400408843c21a1908103109009003154084004041954031400c20914441100070898808003001e8440c20b250450350381c084001e0000305c101c030700000c481207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 436751897 1250 436750647 436750651
    0x6130501180c09090606051c02130506010507080a110604050c0102010c0e03060a0b0d060f0b0f0405160e01030902060c0c030d090605090f1c0c0512070b030f0c070209070e09 76
    0x814500340004026990360020300099128022455403a044440c0a0007010346c0000020980103000845018840d05108081c90301c01d40160711580810071421001c0e075890044501c81c1205079207072483d088450380c80c1c1782131341c01090303c0e10100001650310000d2070604010031400795028400401da001002000242502c1c961161581041901c5400d140b0076140011442d030000070300b520104a90221101041c0507440c6060098032650a100585140500387c0d0701034070f620001510a024580e01c200240401e8807800d8801520403001007000005031071080c41c0701071a0900500d0041020401900082c8403a000315401d40c00c66005265a082180b80400418043c0305c1c060400036000c524082024110380640c0b0456400b444510720364403100d5442c3c00c0441120f240e28001740d05019441e00b800700b40c1e46210301446009042c007000e1010040c00015040040390030070300c0b0407855540d905004295664009e030200d4a1200107121040041e683d0082040c4548560b98407002ca001000003080200200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 436753147 1250 436751897 436751921
    0x6061d0117030909160c080703050406030605010c08120a060b040305070f140310090302120d023106030911150a02121303030e0d05030f0a02150708070c1406130501 72
    0x403c10200c3c0303090300d403003284039404095000b40c08030344800300005a85603100d03168010442507001884604054101018101780c402c941d034100503081d1164015140709424000141010105001381010340c5043d0800c20b41c804210003001c5070079699491007401c25006504203d42c0f40c4c1001005006403010914407000411540c0261880d04940d040881d8448240b07020720b03100140c407175581c90280f50007002010203459019540d00d6840d03c440743c080000b500301c0523026a19650003807003041141405020b5964070b4005007074070b441c92132408800390000e0401b400f04499920788003460702030360307a00d002e01000161108201681c1d1400c030080020702741a450845030380144d1041c0414484030300e01500d880d054a1345400c108031210b1403a00000c04045000b03400a0003480001040107454410030081c04400140f902242c0c031007000c488001091b01c00c21900b4000044290000445840c0700f0382c0a00060350140c05034034881080301c80780351f04188040300c81614407000c902405040040c248161000c0400f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 436754397 1250 436753147 436753153
    0x2072412020f030f04050106031a01090b0102071505090301110415080f0f040b060f0a090b19140120060a1e020a0e0f040e06090618030c07090906061d0117 68
    0x28040701c82e184240800b4020040f52210701000500300f02007540660f000d1038000b084060307956194403149071541c03824000c003400d440c2441c640d800a54000a0f0301b40680d680b44600c2981103c1d840000c507055088281c17916455902c0390b540f0552640300340000c0000c2c0402415501030801c54031400b40111401500280041000030300300186400a040d4840d00160300070081e05107902c8000c001030319100c904664652014604400052050443d44034046403041034491441198031500420880c0c0028800ca80901c2018440342d0740a6108101100502c2807420881c03c41c04450044d039464490103c134101a8180c0d10100b116801c0b02c0300f450b000d1840b234041002e40c40c0201d0b00750010700240c9091019130103001001013136001a91035411620218014000312071951504610055640f48159070900c400f0000107558000c11102008071b81c000d80407100204849440c28498200409040700c081e141342c0c0e41d030030011a1480c000e07429038042102800c400c04603075041041c40c400e03800281c0c540d07010380d80c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 436755647 1250 436754397 436754407
    0x10905090c1209060903040603020703170a290315100e1608060d20150706052203170415050901020c25031707080a02060f0a180803070207241202 64
    0x7200081224140d8807d440d025840310bc080c50191043d402e00303d00c1e65070f40300305041000310080c240d034008caa44410002d00707102c01c4c4841c0b485050240841001841d05500020081c50b042e51a50101d6074016180d0303883c0c0d55455503034011000080c2d405907400c10a9443c580c81104000741d2001c0d030745402c03000440781c140601d001541c03404a5000d4031241c0002010314038050707091541d00d0030071040c0c0c8018021114ac0e40e80455142000c0107200440c1d89442484042d410400045908000740385402c1d495211000200008030075583c05070001002100c5445035800403001000345c0d4018680108100d1001503101c3c00e561f00881e00300711a00054258451a00d200d40983c54400440d8000b102e07040115050154003c11100406200d0400060103540e0300040e070080c920380c0090301d0742c8560a881400300c1240c680340a070b101a1003081040c01e0107904d1203030b2154042804000155040080c0e40100ca042507070720005000003c016900003d26100c9100c6408140c6030403013600c0c401400000400c500d48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 436756897 1250 436755647 436755661
    0x30201060531090501020c0f1005010b1e090604030b06030c120d140c03040f030b0a020a051b030706050c030901060b0903061b0d09060603020f0108090c010806010905090c120906 78
    0x480100704075103038402e041003420407000150342c0c008016950401c3c001d541d6107400d03081c0141e803034040c0d00c8048000d1083c0510002260120f00c10181038a400754011842e2000c00d4002d01c1c005041480c2441090004000381d2160365a140000e10041d0710805200d80e151070079004060401500f07890b0f040c055011000e00f9044a007001c642001f10241609202e43c6050a903030000f28140108848062a4400001d003c140855013084400450b48560f184810a030356031081c820690103003800242c0860b10600440852411055640c07006040c0380d01100e082024984407c0141d44e411781e1905280b4200009204020501307020b03003400b414441c0c1007c1c0c0380c0405180400d941d524002c3ca4280c0e05da00190041c2d0445800b201201c00600ca0202e00b4080d1446604002d0005c011900c03049201c1d01d8015034a46465001c0c5038014810000e0802a1440c07021880054540c030100a0641e81001411100440d03250b46070501306010320801c410b00c80e00c034000c1102c2004000c5000e0b00b0074409030300043c204560 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 436758147 1250 436756897 436756939
    0x50f0c0d121418030403020d061d0d0c0201050304060908030a1a030a0f0b0a0204031208070f0311070605100b0d2412060f0605040c020f070e060d0209190e0a0302010605 74
    0x103503c0c0000700100070100c00459085000c0c6800013580101400911000d01180d900822030900c080f02c8280490801100c4483c0c0e11045800360302c0115020348044405580140c01455009002c0c00380800d43c2c05440da101c8569900440d0300c3c10074199140300c0c0c00003a1150300314246001d0700031b9004140400070758849a20380858000000d0811950300009900c00c81103030180e9009550141c07009081d0004100041c2492100f19001d90003c1c0c0c5440c81110402d11070300941c48000c074141030551411405846460251000410001c2c0311209801c0020f03d203c2c094004000d1103e40040015070501d02260325010074121910110315078001c100180a42d884811250170f4a0b60b0014002920085a06440303018010b04d6005541c42844c042500e140c1035004581c02c2d5036100ca07102a5035216880f1404459103000503145d05800c103c82c948008014109010308940055001c5000300200004815910030b84803a221004840d0300503402c01000c15409010303203005020b0484042c1c052070391032220100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 436759397 1250 436758147 436758151
    0x150606091a18030d021c17070302090a0b0a0f080603060717040c0306051503160b0d0c110a030302090a06090e0705030a091209210210030c050f0c0d1214 67
    0x42000c0000b60801d6030b04010440700b900072405810350f03005040e08030000e9241d40c0017941201004200c0a03843c00c0961180862003000c0b40c0d03812030020b1070388641800300e00035040982c01c603400030010000405c5000c2030074007504240c59642d03203c021407182c2050023401140041d0035940264000c03010b0000b026041808900b0341c0c0619480e19010741d031030741032500f0b40b52029440603003600c2c40d20060001d20510760882028056059080ba00200d24080030707500d00d149548100c5811003420300c841d8007c1035035904181e110b00c40514050903984a071000150030070f41da1140c100c01103907000410b0080703400c0580314400201503d05089552a05d803600c0c1c400e50300310040a64041200000006007006800e501101c210303a00300d0080350601d00b00c05c0c005054070406014040401646403004644030003100e645c00f403216400342040d29020f0811500b60060401940c414042c40424008030000c0550440034160203640507001713080540c0010380141840c11520303a0502c51070300b040d800c0440340d242e140480c2c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 436760647 1250 436759397 436759439
    0xa1d0f0705102604020a0f030305030a0b010503100b030c120c0a020705010503010b121e1302010e0d050a14011e09030e062701030e0f06010e091f150b0715060609 71
    0x3c4090b40c0d05e20002c0c910b01150b0304801075180915401000741070340300010f1407085491220400c2480300c0d010044d965400b00f10f500320070403150034205210040e02c1201950304150f9001d08181020489074003844081800c44001d54240e1000c16421070f49030b4100000d0f002003d084c03c0c82c6145505042d00c2c0015482220860102e41750b07000003046983c0ea92207040180c1500e07601c120754007406c0c90120309003030802c04a0186e0010300c1d01e841944151420300a82105c3c158840010401c411040d0303500403025002c246040420b5580340603d400c3c1184400458400220f4544000b800301a51700d03000e4031060b9000c03081c1740141e6043c44444605000c10895800c105070001032119626420700049000e003140200d2050075000c3e2007014503412500085080c1a0307031021005c011696200d10760f540c0d481c404441a19170fa9000c0c0ca10110000340554800e00c6400d41c0ca40c1c4240c005503c1d407a5244041c0d001a4007114a41c0d070f40410141926510320465010304000d00d08068082d103084060314600d00d0700a284 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 436761897 1250 436760647 436760717
    0x3020123010e0c030c190210050a0513110a0e040c060807030c0518030a080a0306030b160e130e0a0c0314010605010e0f01031d010b090a090b0a1d0f070510 68
    0x101703107500804025140171245200d40f13068a0040b0400003900c0c4c4100c0c00e020403a50b420400410045101c03402500c2c0304054200c415468130368251204003055400c2c41f010707900102120f501190a202d4202d25920450103941a460170600d05a00103280140060030703141054a8003c418951a0b4012f0031103070182180240c4410070040500081e08140b4000d40c001c1046600003040f48540e44c150700a10210703401640d0703e10103680c609803107101007000503040c0000140e070b01c65643d0083c6082041c02c000c0f0009900000769100c82440700b0b501d0191076031000c0c0e84082a00c00d04008000c2c01e00d007680f0007005000005e2165501d41000a2f00300407460401c540716046440c0002c5082e48603502c0030900c000301018410386410b0003100d441c000d058125039603010300c40c1d02e000290815441e0040048041e8401040b20303245d0b442d151050010401d21040340011f1070a0907400c02519000c005000300003003400007a05800f0b01d403208124010707442c524044280301d91302c20903200d508021800c94009650110b40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 436763147 1250 436761897 436761901
    0x30c030f0201170a05011707121b0f1e060e010f0f030213120b01061b02060304080405030318030105011703040306050c0c030a0e0f010905030c0f04021603020123010e0c03 75
    0x181e03844240c4402103903983d8480001c100264405811a41c12a01c40d20341130800c0c803243c00d9a0315141c0300c4900507121064000c84407000041d04000c428001c0d515550000e2038942c0d00c410310781541100ca1380c4203042d4603031041100c40f810040da07028040202101d08080a0a0b104000042c00c11400c4507213200500168101c0383c01001c0c02501110924130b0391076130681c002600c4500300303a000035000c00191150f0307098800104801d4055003421808024489644030750307044907401c01175280d10051007200c0c940404d0000180301d840c00c00c090600003131801054002600356800341400c440c01688005030110f20081e209034915400710454003500d070002004103d0b03549005240c1c0440c4030380c0d4951040f501c40029412611588140604a4444d00f03e450188100f00b8200440d1080030340e000d0140e068100c04d401d40364030b2500740038403981d11201510141c14100d01303019030504a02914801d4015075100c190008111081090482c441c01d11001c20210650514407102070890303004004034208400040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 436764397 1250 436763147 436763149
    0x609040b040f0201051614011d0604080c0709050c030a0e011820030a0b01170c0a090203070c0204020f0c070803031608070c0b0a1a03010c1409010c050d020109030f0801030c030f02 79
    0x482c0d01c4003c2407004260170b800300b031810440707a02c82d030300f00c84c5000d51a1a15125820500070500e84180280c0000ac0c601619180c681c0f6800d5448018046070910415000245d1150b00f80111481100090115074885c900107020741d05503021524030280c2645080358a40c031441030015001d00082d0804880740c4900c412440314034800119698881c0d26202c0c0110003030800c20341e040e1407410b070b540d003040c9030003a042d129240300e035280e040c0034050b90720106d0003200307104203803080e400740d0351241c034901c1c240300c58003107a4000c03800f01c3c0d00c0708542c00804c800014015400c0d490801c032200090078810000d51845c54201009054138026000c070703400f002020404174076030324480c042d645150364202e03200101c11b0a111004100601c035400100a181100301002062454113200d84160091251502c0b16503003080448103020358403020602d81404540120800411400c00c9200c40c0311410b9000000d081d075050401400e81c426849088080010701e44c01031000a03415040311003140d610052170742d4400c0c6148 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 436765647 1250 436764397 436764407
    0x4020a230604260601050a0b03070302130906090606080f0c03040201020304031a06120309030703030e031f02030708010f08070b09060c0a0b06090a090809060a0509030f0309090609040b040f0201 85
    0x86040c0e0340c050404200411403c1d114819080044040040c804030100c00210840e00c0310750900ca8160f2110003280c00300024501d210040d58001c04038a001440c0800e6803014442740320090b00005e000079944d100a101e1944039200d1000a0039981c1402102031410090706454080d0080410078918008004501164002c10544014581c0f100090541562980c2e0f2407a1645045520503c00c50b0411100c51000c3c0d4044126504014050007801801d4110345094a1181c038214080c1e4041c46403040108166601c030701c01d5800c018807540056500d040545000381074030810b80082c00614505107042145000c002010b4040311511090302e038480a039000060358a02894140e02c44500038071007001c0800c00811482c6101c0c0c0c00444081400f034444084480031038501a4009052a800300302c6c1c44054070b010009072501807640e00d8154035203401c0c00b0120b0700b03280c42000004040e61004c06e0018003407a1910079140c0c00041500c2e0340c0e20528094031065440c400c0680060880350044050005591043c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 436766897 1250 436765647 436765709
    0x206090402131e0b040e0402040507020f03070804031109060d0f1a2d060a0608340f020c0f220c09051207060e1908121801020604020a 59
    0x48218900c02d6a182e035188005081c26840d40f01c00c040700c8002041403040d52058806441096103a41c0007903036103609000041c4405800101507100e4084001c81100080004001d2144242c1c440c3da26985940390030500105002110380c402c40055080000d1074554803a030308081908101a982610800c4c1460120441a18203130342407103e005040005115002c81802020105e141100c0c0b4042a020b000c1c0b02480c00c107540c1c40e6403010b0540c0301040b01606c14400150802a00c9000070103554200066408060040c2640c050f0948c0a0007510201e607003200480241340d8035400507188032501000042c0c05030f482803101ea4810703141e04050740c48900310818004034421424004108446242101038500a042d04c80c03d1321820b1a58001150381402040c000d0031582d0503114400c1c08603024041001900001d00310318070004600400081c0b400341000488a001b0300e61528a0b512806c24000c038030198080d42c1d8050540d0710180a010050b02c4008600003190888101e01c03600b6007a8500303a400f41121 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 436768147 1250 436766897 436766917
    0x180616081612180213050c0405040c0e04020703030b030616020d08270609011d06010e180303013012110a0203010e060f160509010302130512060f090f0303040206090402 74
    0x2a00300c00f01c402d8140c09007003464090080301c1444012901555540640c0c20031980c0114140090004103d02d04007604030581090302c50401840700964a401304080742c105a10a60000e62298030602c0d0390300f0300744011600300055505400c1c1da20500e90010f50741e038042c5826042017080d0000010a00b4000c41529020010029202007980030300d881ca440c0d0310307d415901003101c3d518044020350340720760b2002c00c00d5060820501130300f44c9a103031812100c45c3d640020500e540b40c424440340324201034008c6c001180a401c0796004400f460380c000035a644800f41107c81900400303802819203001c1100c071900c001540c0c071145021103081807002c5c0040e00b4808180b4009400d0340c01d000300c020500300081010b612412003581d90703048940c0c1e0000601113482d2040ca00c100418010000f083d041e51003500105494074800c003c0700210b6039503c0101b894410380c00c2181d20103400a8060008440a0009054028020100400c02c422503500781d2505d910025100920410001030802c0507a00c460b0160703144408 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 436769397 1250 436768147 436768151
    0xd0810050303030a09031b03090e0a021b01060801200304060507090503120903060610080403050708270103110901020705191a0414030a0f0308130b180616081612 71
    0x4c0940c10640034000c500c60481c0850640901c0228030074902410480e140e4042c1d940c0905507280040da04410040a80114002034003080800246410060101c0460b1040400060007900e44001c0a00b101c0c22405507031020140c2200e030890382803201041d0b0341c02a8100c1d80000d03103034450007400d40706d0104951102e0307014081c0e2120b40b41c844244902502120342c064054501d9581c0d884100001a88440303540e80c04122040041030100b880b42c0040c007510f0780310346411880c0851100318548144c003840186071041445c0b401c140b6540d40c1c54000d40c441945020282e60a2550900c0041c1d140c501500a4500030340790b201c0c0072850f0448c510000340080c511914000f0054a03101c140080c5648640202401540340e004041602e0074001668100f59800000f141900407140e80c0031500343c00c0141c8030104501c1d030f50f25464045240c2c01c43d2103001d03a400040c004a0080c0980307065007812402412245400140100b0140704e03500200400c2d4081048126602403540382c040503249060403d41414840c2c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 436770647 1250 436769397 436769401
    0x1101030b030f010f050105030c0603160315120618050d0c02030102070b1602060711060a091b14121c141b0c0a0b0c0d0f02030f120105041d0d081005030303 68
    0x5401036010302c00c2c00c41d002c4000e002e17aa890b5020301d60741c3c22030160980c3d00018104002100e1604035a00210102500c0c54081226400c110002844940d03540042480d1902e0f089094104400c610601020f590745007042040d10803a40c0380e5036121860083d40a05105903c40d140c41190390a604545840e58071900c0b07048542802c0b80301d25400c0a0140140c000341c8684008103d00b103014201c43e1004a02c0d40d8010305c026600c6201c803034041d001d445802c80310350100c003040204406580140001419000c0c410b00646182201000201c42c040e07094400540c0002608410750281c950031408144601d0400c46c43c4181e012041000d00e111300309002c04110840380c9908030a042c08924111008400c0340c003601d1365601c1e1a4400340e00d20441d958080d20341d20204801441b2400f401c10544d404c2618019603043c41c66188541e02c00350f0081d40040c01400b43d100050000c1c4c0342905c10000b003e035a80590701490040e6003200741d510f41e00c1110180600c2020000101d0300d0b017a2148030000b4060240903252a8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 436771897 1250 436770647 436770673
    0x1e0f030501020c0d020a1101140408011416050403020d020f181009150531110904060603090305040b070c090c03150501021b01120b030604050a11060a0c1101030b03 72
    0x1c0d004030203908511300403004001400c51000841d44a16500320300a64450100c035001034a11800e030508036603c4a2051000080c018400c0c8036181c0c6102241c000d01d80b543c03030719050250310042149402c406101c030a04c400c0c40981c44407201d4891041e41650409026400d500000b400c4505034184112403411681c10014181081c10f40360017126082d5000380004003102814810b40d010394010160420448055509941d41c0c0d40c198940302405107004d10020450103201c60242c440c8006040c1100320f00040c0c071078846c1041c0c49458003c110a2504002100255800a200b032240d8400d0f406291800318007030090203869807064008151621041162240c6030001a0280600f540d10000c8007440700c0700040c85500100384004010140d803008800315206100544034003031120b01805100b551440e6070126901d041284a02032f0b4040c40081800320154031700101d20013403038003d881c0106405c1c80f401c040207401860310302c01c0c6580000d00d011040760040c0101d0040c038140e03800a50601c914001c480c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 436773147 1250 436771897 436771901
    0xc1011040906050402250303110a11191e051c08150a0302010504120606090c020304082a152b1103010510050c07030f06050f06191e0f030501 62
    0x22681c0c1100e061101a5441040004a0007009482030703803042c0c04a102c1680e000020941a80640f082c02d0000f0000e00803c50300c038880d0002080380303000c60b031658000410141d08210040b2030480c4100032442d140801d903035080c00016100c0c00490200f100b9141401003102c1481000c0c01070b003030014180d80c00b03070035800010b054080c20740f4900ca4031070243d180500305090010112060300e406031261440d26141c00d07000610300c000500c00340c0744140c0c0c0d54400300307000b9070500070104440300071341c0103548035401c10150302e041c001440c04c442400244030552044140c030301c0380f83e040944002c590000e02c182c10b4459410140c41000011600d0071443d414400a4008803005041d408030300c07000402000d1124069600640320130b000c2c0031303809045c02001107003240c490401090540e00c400c05560b0340c65565a1024a0054404c9044801c1c50720766042045400ca1410110350201c0100d40d00c6003465041e40070b903210401280550018649540d521004102078421b800000303041002420601541d242803040c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 436774397 1250 436773147 436773149
    0x60c03010906080109021513030602030a0606110d0c02060f0d0e0a1506030503090f0301060b03040317060d02130c091806031401020a05180414070206090105011a040b0c101104 77
    0x240040c5082004211014144544170394150301a000411001d5401044101074020700c2c1499034040c88030b000030000844900141d8081d008142e07002c200142407500240004141c02140d0429502c18242100040c1d40f003a00036546d1501510f82a9603031032101c043d90250b115111410462901704604030440240000348039440901440990045551026800b004c0c0c2c1c11718800641641d00500160486241c410f50036800c000700103000041141e40c3d11039410064108072004d0300858640600c92207140c5c0502141c603800103080302c9001e02021141d001942c00100054030a80156641e40c501420f10302490700700340504503421490b4040200708241002801050108442140c607007020012601030500995004032038513107039523003400003280c5034501000030894a0f030351003070319403100034900459191140c0c040d0965901501180c9031003003200d429100107900c80440901d01e6000d512900303051400b40e40c02c0c0e80c1402981d6036511020295a0701d020b000314000fa08242c80c088800300311100c4040100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 436775647 1250 436774397 436774409
    0x609040203070c021513090e16080706080a0b01091701140c090301060e06090615070c030b0609071d0d140304080f0f0309010215040305070c090510091a150c060c0301 73
    0x15110b0001c6214101c98004c6c09040c00325101072140a201d20841504104200440c0404880d9400c0c0080d58416080c2c1d101c3d442501036403c1010142320160b0b100b009164000b40b1540180038082c0c1450008060381e00b036104d081003100e8555060303060703000203401440740c4200800c0b01880b07900b40044041019400300d0802446503103407400000d400c60f11a00c4c2d891040e4801418051076907118410f1003814035155242545c622410001e007400903000d0b05545001d14004c280303c103a83d2415400380f1100040103046a0f043c001a50300f00800b80c1c85a180d1608171100999400e10705070b00a00e0701224611010b54105800e000208010503003100c00124a1408640e0704100c07244918800311140c0c49206541300c02e1f00503040702c025a00c1201c140c46a050b0058820b242c02860300d40e1588445150031111341080d40e05c0740e16007003842026440350350600044d002900b000c103d83d0440e001d102e9055126105450702450343e1000f0030b2921a003800550340c0e60b8407040c096480900c1c00000c024120340c400d008903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 436776897 1250 436775647 436775659
    0x30e0d080a1404050d050304080403120e0f091302060c010b0a030501020c0601060906021c05220905011d010e040224090301050f240a080a061a0108090a110609040203070c02 76
    0x121010b0202960098011600310b00581209120700da0100c1d00d13030b0300003842652818002c100c00030004425640c44d105140d101d541d0307000c49000407420482c00c140985015880350f444181800403120009084d40b0f4840d074102c2d1407581e14608030b0402e9000d41032060320154000594100001407250640003048654081016912240c2e26224207a5260015000e0f070070040c0d21800184950201707100d400c0c00030048906280d420402c10340030706092000210119000540c062404000300c0d0114001e01d40900000395080c86081310903c0b0007a40824144146025502e0b084003007015511307800b070104008541913201c0905200070055010f007503417000710810300079880c1500182c413249101581d11b0141c0c2e40c0c50b000c1548001c03c00312032280300754040d488940c4801c6940300042c081c801000481b644520600001c581d03251160070282290700c0741c116a5046c40150010032404042c0801c44159a9074081000c03c4021201008246240030342501590400c0c80002407221040d041488125100d208843d8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 436778147 1250 436776897 436776911
    0x1020711030601080607080411120c011202031b070c0503070f0e01081b01030b0a0807080d02150405031b010204090f020414011e0f02190c080d0f0801060807030e0d080a 74
    0x140340d5203034400d00c80d29190350032040210706d295215030402508a03018005e1499403807801c01c00100c0310a040184402150b005440207141da58101c00c2c81910410058011801d503e0300135a1178050003a01003201203100c000080300b9040003400d4901002074100501114901526084001900d65003030054040709002e21000084840d00028600d50b4000d400d03000b000c5010f00e4400540190460f51040d0794464001c100c00b00d0184410000e540040406d60000d0035010000c04e0f000e41003110b01c1d0b031209d40072094402007002180c1d00000729000004d54120341c142ea0130740b0a030142e00a0090f0341005203c84e0034000105880c40f140c2c0c024000740c82c14030b10010302d4521030794019995202e1a85104d11901061000030108a02510420042070103600684509080d0140b002d90840d1945108070344083c40070380d01780036140c4101310141200d146808c211b07101108510018060900c14032492041050200020b02d51500c41d070099814100017200300d400c103002d000d402410f1040d0445020b00305a1602c14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 436779397 1250 436778147 436778149
    0x6010905061513050909010f05160905010e06030402010f090b0304061515080c030c0702090907090605090c0414120a03121838090a11040921031d01020711 68
    0x2101c0360350f9008950318041e01c2c40c182c140007641c64001d081c1d1411755a200f0712244004104c0c01824401c41010071180e0300c07800306007405000d665054202350304200201d451500c1c161220b004694000750242000c40c03002ca249802200d20342120b400c0145084400300074441000300503001140a1b000c0c41410f600e0340c988620421003402c1002005070b0008550b580030600b5a0120001150020b00807040d0515108182e00460b0280e00240c07061401d41d40301503010400481284521009000c04036115034072810001008807441c026406284000e50100030900065a180b02401d58041c0100e8240d862205640c2409411200c203071141d040b0840c185840c0801d40b2901c55040c2c0001c41d0b001184622401140c588203070f1250040880c115654120048081c1e000001d0040d00e2080181d44000c0207180100d1402e91010b0180e0f14403680520705118001001945003c05001150120741500c20002c030b1180040307004d0450701c4c00c10118030440000700040e0300010f400034580f1902038036400100c00b880c40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 436780647 1250 436779397 436779439
    0x30c031709130e030c1b0a06020c0d0b1f181b020d0305040c12080a021504110f1906030f0e0a170a091d0a050a0603030206060d02030f0601090506 64
    0xd101075070000307102401140000c01c0760303c503080700c41c4240708407401d01c42c52032030440c40c200c0a4541640303480e450710340c860181c1c80c110000c40040c1c0b0307061001d481e8000307a12000c207080100074000241b4204040001980e0780c0e10190007041400c0702c0301c0c141c11040d070780c40003018003070400300480c040158146603401d040081307203922011965102d980181a01074084c23004800410024204a440e03111920b000140700034541c0040040034002d03a9283e6a0f0701074200c029280621074101c4a002c80055410000410101e0001c0040560103030342104210030301600103150031028045000320200804404506164158840c42000030a00701c10090503250400460761007200341e0300140072030b501e14a40391400414102920036080a814403070340b0161a14461800c0e010404114690002e04d202046a0110310303025441e04140242010030100b410760300c0081d1502030013004c05001b040307015140710464404000c000f81c540b41e6801581e0701961101c2d241c0c0041d203020f9401c140f003100b500e0000b8804058503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 436781897 1250 436780647 436780657
    0x1501090209132a050c0109080912060601051c230105150405060304080f0403080c03031023100e030610030507080f0705010e040b130b0108100803180301060f030c0317 73
    0x640b02c0c4806034100080114003200d462280f00c01002400c0c071038040000070900552418502c15035001d9140c1c0000f1050100324a00040c2c00c41ca0b952005080c00041d0740c0010446086000d08601c00c0005400d250318203000c1d01c118913030145407000f051215082807110740d01c010f050300c100304c5130803076a9070b401d42e00740102c0d0041d4010b2541c40f883c00c0000c9070000b6404e01c0100b400d074044440799814a6900e0722042c0381d03070b01f00100080c00ca800c0042000620003a038506070000e09007402c484c0d556004801908200b00041000090040020001c2103031460f000d4401c86c4a0004010111182e13840c285040c980f0050f480d10044801d482102c0020031101008035141e040115007800500802e0f02e0f0900454660520707410f4150050307552801c040b41030f2203c46030034402d06292513001c07404800300000182030210007840220711019210007844a2007000c4211240444028035002d08070091030006030041c495603018580c203c0480400108115250000404503802442504541201070321410061b200e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 436783147 1250 436781897 436781921
    0xb180f011a090d03020a020306040302010608101b0e150c0106090c02031603030b01141909170d031109100c0605060d021f14030702010f180503030c0705150109020913 73
    0x5000c6042c1c40c0c1003000001561600904c1143d02c91001900403d08000090b1030541c0185d443d10400c1c01440c504000740c5c040d0a8204c241084403c02034901c0b0490141c42c0c003005410440920b2000e00f031543d40c4443ea48010350050141f665804900420500804032480b0300806d80303085c005503144031b5002000740c46c5020040f172480c070440341c0b41d0f0750114020104c0d000401d0500524140048010380410060000d01089024036114110001009002c650140d0320210708404012000c04013030b40041105880c03420341d401c0118041c84001d40141485c05140107aa4000a012001801c0c5a5000b20980b15180c0a4502080581c540c00d0500c0051801008065000014141f0300f00414507120140312100381c00f031a0507041d030b0306c0038a07403485e0070340c4117032010f00c0140e45454404101c5402442000c4030b40701c0800014203104441c0d80c0c1d458880c00022b040c11441803010031301e0024002c00b80400e80380c11810300300c000362560b15080c1c40c50003504100d06c81401601200030048610809225070308034914 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 436784397 1250 436783147 436783199
    0xe040b0405060d17070b1003021801240c080a020604023c03250609060c150c050f0301030605011706090604140307210305090312190b180f01 62
    0xd9072188101134461401c03045140d2410090030740070803c0c0d2055540071b00e0414040641c3c4900d54010808012081d59010145003203144c01007164038901da4140c050580e450b9070183c100040328206468090840101400780640000d800141039400300c2c4e10341c03240e442120001128440070442d04150a080840c0341000a83c0208001022060000800100340024200c40000349400d0950243d01c0da9113030418a41c002c20201407001d160050451006809245041d0100060544070281c4071807000015804141c0d0341c0141c4c0800a10403012595807201002200d41e403941d407480c00d00010042440b0307510911080c9010039943c8040482c20f240a405090005c0407651101c1d11011001c005640500700c040c03000b08160350000d002c0b0400166000c146d00c103c0329100c0c081d44406070580b50014502e44031600104002c9030904280306103d50411100300c404158085007110799001031040381e0500341e00120803080942c002c00e10409032031041400500b46d20003a41e81d564098030302002c01d15164a84c007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 436785647 1250 436784397 436784419
    0x7080a0605122503120e0a03080d050403030c03020a02031218030c0304060e0d08090103110d1a041104051e0102150910060b03070c0f0515190e060105060405100e060a0e040b040506 79
    0x1a106036442402030790020404105d4603030301c2c1e4903689e03190b12100389600c08036218003c010615400d80b241d03045941c02d07410194030342007001c10025200d1007141c11820980445a0200d078a90028290003040206c051040b2642c400c91800065600d8006105a02c001926201c96100c1402c2000240d214240e205071041e08045441300150058405048040002070f4240314032a07103810030b8002c020031500320240700d9a5448822040c4016180096010840c80344100810001c580302c0b0401001e401d204140344901c80c1d020381d40102d041c0070322204611280000c0d03d0a11580c820040f800240034035030744008000485d9210303d0603203940800c03140d520100d007002c959880401c0082e4101d000d0140300d01c0c103441480b07030000c14200c3e40710016121010030b180c500010340f002c482c5611503490410b1a80c40104010341c0f40100084141c8214003480d03000354041c040344851203004480703203014840001c0c01c80e5120b2000f01c40003001900c07040480ca2117a0709060b001d405078107061080a015030000f8203900c40351 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 436786897 1250 436785647 436785683
    0x60304081b070b07030e030c03030d0c020601050940110f0306010315020c01020f03070f0909060f0306021c1406010215060f010302070515010b0315100807080a0605122503 75
    0x1000703490003107c3d0035009800609009035024001401d0b0302c0712540000601c00c440410085c58004140c21040c003900303583d02408600c0040d01440b2114044a01601e9a2824002402604110009498003150048082d650704224445081c910300c444140d900d0032150038110200f643d500028803024240b841001c0d441407100b1501e4000304284520f92002500c0d15402c140d4070340c404c3c0d2003100da41c40040d166450707103d003299101500b070340245074144c0d040c007030142000e1906c02c4580551200400c11030740001d20030484001c01c40e058a2030a6101e10030050049960700242881808a403a98014014484440300c0805d40c64080c0307014240142580e208142120300640081d800454140c0d900c2c82554210400002d8001c61907010704046003060383c0300d0a115001242d0783d0308050103e8801d00620465815069100001c580e0200c16407030207011540340c19516200404070f64100a80100d01070341584d0a2a0001821b101d80c464030305403003a14000c107a45000301d103044c1d41c0401814000e12001403070310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 436788147 1250 436786897 436786907
    0x291611060a120e070b0c0c030105010503030f041e09020a020d0201270f0807050f0c0a060503040515062407020a080106051305070207090c0c0b24060d0b060304081b070b0703 76
    0x540302e03580222076482d5100c861803171203900442c10403425070b440501400721504080c0215401442d041c2d00450600286151000c0c081c080c0e40144032460090350040d21000e014040680300402e40d00303408669600444800a44070002200300714007560805240a003075003407460400c405100d10b03032040682072055641e60300f15882552016a0344150a105200100b0b0082c0300d84c0410321034000007041881c0101091000035000c0d5400030b4103001d410320800011440210749084030002d4114280c078240d59a00000c0c0c441200c028070382c0c0040e00c500c07080741c2d94040203200607d00b59000302d601600066862a041e42690110f000701034109142c4c028441108540380c2189400c42418019a103085884060701d800b00c400700391554000480c1000312409010000c2c0c900c0742c01842c07103007c0c941d0886050f44041c5a10507000e40e41e81c0034580006040000b40c070300b5071110b0110034004110917601d040c6030901c0200c1d904410700c1c1c2005412030a0502d1544d45c800103030042111766071003c0da81052099141512 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 436789397 1250 436788147 436788161
    0x20103020d0f020a08100e04030f0c031101110904060812300f0123010207120314030403110f030301061202030405160312090e060a291611060a12 64
    0x45842c1c4540d25030780c0658250001c0c1080c044c003562810481d250002c1d5416044520740d200f001c0720340d103880c10701010943c003030301c1020303002d6441c20400420340103450122101881031242c84025442d08424803984d02010000341b44d04401141c050107129100da4000c0d888a640c43d8180d10810b6003007240750b1040c0c040707541d0300725a42c41408081842102603008012251006c4803030080c241c851000500c114064000e2440c0c0c0750400401e4078202c0d401c480000b0b5990440c1e03000300c0c0d0441c030704103801608040c1320b50520014a40910031646c3c680c2400c0c90701602001b007070110700401c2d010f203400003401e00034004252812503241d030342e0b58aa100b002d11038050003540007500c01d550301e0041600440c1416140039003800250311840c0c1402d0000500c100080c501003564100320880002c07031042c000c40340d45400c2c41405030340c80c401076110032070b032040702c800140703064101c110303c00c42d2000c509031141c0c9060318001c00c4281d0056008080c8650040b080010500c150f03560200413030000c040e40150840503500480c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 436790647 1250 436789397 436789417
    0x406032a20030a0819050f0601122403120804050a030c111c02240d020c01060e0a1509090807150f02220e040309030305030619030308091e0a02010302 66
    0x549200c540c1c0c8100d0342954003040c01a0003141102007130100c60f00e920010701d800288151802c124a01300b041000d0710f080c402801c21030410543c0700d2024121803190b031180d00301b01001600032a10b1801084400d006102502c81941d8401e00350089150075070040500c2881303140c0c0507000d0322010105075401c2da01036108150645900005070b501d12556141ea456508901803461880c48101c82d4520401c405040d880c2c898400000070402c40301d1740c15040d05c0607100c01e80340e07001d00944c0f00c95003641d42e24010b10090340022000150342042c00009521a405800142c184007030312108181c45100600550700d41c45001441414204005004a021511142c541041604010415800070750195060742c2054215071088940e01d00a06507902e140c401d04002003000132034041440c502500c01810103405484040c050106c00030000301b42d90341f0340c3e5170300d035040882d20750510b01030b81c69007001480d17403c00310380450b03281c4621079441440c4402192010601403580380204508041640114003035001038001c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 436791897 1250 436790647 436790687
    0x712020d0209130203150f030a240c0519050f0f09030705040f15090e06160315030f0b060405061012060902040b0304021c02031009080d060b0406032a 66
    0x160107542e56a49100704210442e8013507201d041c107480a80d0005900f00c40135100b0414404490000e807000b08000a54a070032403100780083c1c4404904800c200b880c518800300301403401c0d908007071132500b00020340b0095030781c990408484101c007413082e03515209040c070b03016030b510301400096090b140308401000c01e01009001c2e5807500d0f955802090545180c204a140f04580b41c40d1304401c18504046548001c012544c030074003602156040c242e0b154400684941500d01c200b900302d460590194000d80900c0c84540d805625840e0b4034149040041d200e00021101c01443c031010695521341802118041c0030000c3ca18a003040d00441c0503920401140210035016032141c6002494030001e201500050440307504181c3d91303180910401c085082000041c2e403486035a50000800350b1400038104000c0010050002852917660500b400b080c0110b1210305101c900b002400b03d00a003212001d003040718240d8405001c041e18a251880c2c1941c0d00800c02e0301456540041c150b4028030401510300403e1010300b00f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 436793147 1250 436791897 436791907
    0xf08091b060318010c02010b040b0103021c021e07080a1d031510080601030f060c0906080103060c09030f0309080f03120c03100302151801030e0d0e03030903010213030b0109050712020d02 82
    0x805130079111500c807a4400f50355039403000c10880c20180550064072400340fa0440ca483d500740660704a0f80c14011550031156404184603031005403400041c50024601d610040d1030308014a014041e0307a0113440000d00048a25966504141e400240c0f0b1038415070080c0503191008203c006482c4c031400080c0044211039050100140281007801601d010390f02483c61803503042254180402501c811729254401c00908031405c00c803003a488407406054039803218001c034070115a0740c4100c074034504542000c0c03c90041c000c684010550049042400c407020b035826200e1480d010220070341c60340170301100e142007044560006104107603610002c42e8811240c9020f01c009585940101302004040311606c0c0e01035400107210010718050041200c5080300034070b818852000e2203460984c0f24612429030303c0600c403102030b82054a0b0b0f0306005844aa00d0068021521805403103000c1d405070f030b61b500c01618031201074000803440c5610340c000c2601c203c51548402c0d0b81d012414092500a6000c50501c40409509100e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 436794397 1250 436793147 436793191
    0x207080d0f0204150c0606081c030915021b101802010c230d0e0303030c09060a09030b0901061d040804171501030c1419060513080304060f08091b0603 66
    0x2000799540e541c3d0f5500952805c01d407410b041191082e800c8140b02d9400294110703092003802104c65544504c81c680851000c50b07518140301c0c1105e032070650203a0f00e4000303d00c0600100c0c1c000400d1400d03060020448400e40709401203c011a4044015042000300450800000d94021195105410300c01c0851820403010303412407511481b450300711070003036402a286c2003c1141d4804610803050004074040d5183d0309000050410b0340c860301000741c1c0100d5010a0008503940500300400c000c640001d11030006141100080f4020f0845004504607c566150842400b200380d6071800d10580e484440301e40384c6400c1245121007a07000c200c140c00c4c14410522034a040500c140368860085224050b18403d040c01c0401c07900140300b07040403440c0102c1d1450050310300d208402c0410002c5440da41445661001000d200300b205d0030950304852680d110010300003c00d1a803005d0013040000882c1c2d180a2503403501001b103500c5201083e4440ca504c400503c000c43c2c0c1e03203025802140c10103550310b241d001c0c41410704 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 436795647 1250 436794397 436794419
    0x906010e0f151c15051315090f0c0c021c0503040305010c030504020a080316030e03070503120702030606011b111c030306080606011716020f1204180207080d0f0204 72
    0x51500b181200b010450042c1c080d0306103100e5880e945810824002008002039040c1558254070440d071203a01180b002c00441125079100562020400008111094031692580003078600c030040b10942d54030300307407211609500c1011814241a8001e2070f17200b54112099100303443c40410502616580810400040018802d00c250382080660b41c401041324502401005006402c0d50311603000b40d0010070030780881c419170306c0312030320a0b9506080c16400c1a0046012915101203504500d4052142a103072840c1d08051402038448203108038203e034190f941350401154402c48129003035103034a0042c982e0b980000c6071081c40880711040680005547c015048220004440000080c0c01095541c40d0a001c4002c2c14000c940e8451409e00701442d81c0c1d02c0c2d007005680100002801c02a08030034940e200c100480c400c4c000302e01c02c0c40380c0d030003115542101d4000700d090356445486042507040c00448220b6000e0840e009591b003054101d0089410b1005455075100a0900300a20107c2140d0803c008111890340c0f0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 436796897 1250 436795647 436795669
    0x40c0908060a151202010f030509160b07050d0e01050f0d02070215030a050c3105062101060e0a0e040c030602181201021e0703030e06160f08060906010e0f 68
    0x102c1000302d458203c910503209039400f40d403c400c0c50f098404c2602000740c0d07005068944805071519000030590b0f80d1244650528034018030800c249003034400700040218240c0c000d490002e00400a44020300311244090300d282c3c00d0a0400c0d40442c00502a10f0024170001000e40016201da10001d0f00e402266400181090350410b64030f07015940120500c030000040d03104039507000c0902d230021481d000e071005a40b00002c0c5a00c03210719014003400b086440451910740782100915010f490181c648009907400041c0c0c50151070f0340c14030b4104103000000c00c60b1140200a0190401406c100f03149800c041071100b01d004000c10507034004c00742c81030000000d034491005040f02e0b0000b17240115418210000c1080344001e94030118a10303030041c011190004e076041d545809842a030244141d40f144140350540c0035202031048e040c107070b000d20010003440c0075002030b018030702643c90b07a1416106554003400717070394a00c0296400c44d00302c90328400017070040d400b80107503075100407008100c826501923002c00a420032840f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 436798147 1250 436796897 436796911
    0x15060a0306180614010f1b06180303020405010809071a030a1b020102131211060307020a1506032108180c04050c07060e0a030f1b0f05060709061805040c090806 70
    0x140f100d003040450601c1c694131980020910341080080110300c0010200d40c400c1948440034481d4000807000c000132544084441d02518801c0c0d03107040d08030b0401030001d41140c412180800c00d1a80024240c40c0080b0300c400c141d44040c4240f04500d0745080d050b001942005111898980d03940c00300c0b68008111305e19546413080e540d40050707914140a813200600c1074440c0e00c8001c0707584442c14008001600403100c0d40007960190380b074a40b07a9441034402c138540401032034054004540400b904480c40700e650065001e89001302030400c8404210502080040010040140040c243ca00070401c0202c8181015407108040401c5074240e18800001908852040c2c88504a03080f0000740442013204a00908208030f0f4040040d00d512401a1806800c420002076880c0420109a1142d00081d4003418281c40b020f4004802005180003071a05580e540b100f500c50788007042e0001c400080c04c620501180c600b202061469a0b02c0c0303441c2100f488064450704000b101442542c00d408144142c040100074481d4035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 436799397 1250 436798147 436798151
    0x50303030f0702010c0306030312020a0201150e0402090105010c080d0c021f051605090306150a032906031902090a020f0a0207090605010305010510110a151a030615060a030618 77
    0x1040c2d070780070f0300312100070003000140b60900c207041000c290009000545122071700d90159131224058000ca00500c0003201d988403013202004041205804c28005501c501e1094901c003c440e602d0700015280c9401d00c103801007903403208020203021812650004000788619004642a001101c0404c901060588805100072941c507010440301820404201800340410f04205183c4500e090100751600c6c002440c403800120f52101040c002e88505070880015900054004450b02204800c072954940c2050090760b4030303001c040440e0403407402047c0009800e880c02c140c3d041b10880c039801c0c002d011000500c2820300503828800e01180e070441100600e80500c03d9405020894107000810085a80c00c1c3c00c414109442c1500610003134803114042c2d240e055690515035850f060051400d840c00890000041c003521302c862180c028002d8540000c86090203504805040b200400d05040e620107088640b81040c0a903149110541d04048000b4044d81941c5e00e800b080f06501c4006d001d003810302072080316031490b13 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 436800647 1250 436799397 436799401
    0x62f07030810050102120f0f040306240509011403010902091510090e180c040c020d1d090402221404020a0605030702120a0504091107050d050301030506160306050303030f 75
    0x56001c401c1d070b82d0014110003080c1c42141800b0000b590340d402d108100c030f440f034400224915213915207010f48112a00c124299940d803500c900e058030103440300480b1030f49071081c80e0141101034041c2c12545801c0e180c0190145080d45c1c64450ad0f02d904d40d14210780960075541c0d4a44100145c0c07141d10302d0520815209a41d10f1010010209000d880c3c07020200e04d208000b5040010b001d4403680046554000d0300011107400d1901e400c000756800d04040b1810030354014035080010380c006401043d546182c0351281c503280c8a00020a0740d081d54664902c11039644440c112000400514142c0e0319000028211000e61420801440300031044501048205608aa5803401c0008610b0017058481c0074001c030780342203130860030205006551071403040002c41744100d002c1400c081480c07049040c1d0300100030200c01803000c0040281464a540e0208005888500031028815116400751003200e040b170742c3c01002000c1558901c03695400e07040b0909140c1040544914000a00c0c1c0d40810142d80501c044061002982c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 436801897 1250 436800647 436800653
    0x9010e09060112050606012001022803111c0e060a0911060a020606090c0c070f0305011b0804030c05011d0606131505041a030d090905071407062f07 65
    0x8058143c0c0301621810f10001c0c442e00050b030100f0030a420400a003840c1c480500c0012449501c0500080814415840803c1207500c048140d554030940108032003a03001100c1980b0b100720151150f00e4042d08803001d0407c146402e00c50404090030f09070007080d0000032480c189442c440c0c01c1c41030544540f201e0b0b94a41c4080350912a0fa03805802da8a5011203080c1d240203481c010213501e03400004c01c0a44504c000c1c4001503900700703840c401c076000c98602e00705940344030f6110f0302c240300c01c00c1045c0015a41586442201c50141c403004042c0404400b0b941c5800840740e8403981c089032a07820b4140200d440395203031a110104d0215250700b5003a0140094050301852511005000b03142100340f03000d03403456003005868004840c2c00d810b14415070b4800c4d503010030024945092075401109803154250503108ac45c114220a03a40140c9500903101000018407203915401c808684c0f0030f0391502e11940e050f4081090000048041e400303041e8000040ba6800d215500b011201c0035080c941002c4141ca1440c001691703020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 436803147 1250 436801897 436801903
    0x711030406210b03190c0f0509010504050a27051204030302120d0207170912010501030308060d0203011d16060801080d031802031506032103040303050601180f030606060318110a0509010e09 83
    0xa400220822507c0916040000d0301408045c401e43d030180e5507520108003c003145402617092400d852000700100c03213031901030b11040800044150b449018092080408c0c6522404850450f6010790040c9105900412100c0340759105010251140d84d00708400c3c8000340d11142511908032584120342c0e00c84003d001480540e90700e026000c0803c1e450800180b0000e81c11444180d0003407000d4030b41c8609080070b81301203030040508100d030040c841d443d11945210000700040c0b45110054a0f4500031001b0764807401518076107c00e0156030815044100c81d4055944a940000481c00c9002009200a1049d40100741020381d208107803440040e10382e04000c0e8605040005103040c50a903907800c484800c18252007405030101034002010142c4030004960303da07201c4c0c07189400003c041d61812507030a0b51074800c61b094264920044031031a0908034002a80e034064880d2049122003240701000355040f5503100724400500d000c4407688020040c6001c80c0a40380ca142c080c1c0600300d460121020390502e1040103203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 436804397 1250 436803147 436803149
    0x114010509010c08030c0f0403060209040b0a03171e0315010e030a080301120c0e010806040c05220c05040801020403050717010b011e0c1a0711030406210b03190c 71
    0x1040c404100142211641d12a0120000302d421091054690b162031a01c90311910512860040100c0045000b00c24082c0c164004c0c05480d6085400b0482d0981d403000388500311103944000f401c0c0c040d1085c680c240c1e240021000f00b0840e00d10f00881a85e100366800946031075082541d0800071200c1f0b503250302d400d5503040396080555a000701e0081c0349201e1385079152011440140220107006940822070b10402c07a0b401d4804004d082e032800c881d040ca68448800c40e9446404480c10354604004100001d254144245070417030102410700d031740c071810409016078000340c00640c60190800a042000040320907003131001d403000d1803141c2c01038016180340c0088503e84152182204a05074944070f40c820351aa0030030b00441c20360504549002014100301000d036108080031030081c000c00744401e64045480c0ea0a111a44920880d441d03103003001c0070010100f9541d000300d008483c0426005110310075080c1440c8034181c0e000c0142d8070003007085000340000c00e041010300c2c01c0c080004016030455408204410903020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 436805647 1250 436804397 436804399
    0x403030f0207051c110322030c0e07030f020a0903020415051c140f0706180504050703020301081b130e1c110730020105070f1407060513050405130f0303050114 70
    0xc0000e41c100d041703442c0c903481040508011aa41020b08600c0343c1d900000c004000e41c2c000094150142e681d1b80001c0000c08122000340000b8a00500702c209000c182c401d540c0702c0c00340341e80c1e9440c0780c038215030070b00c4003c001c5030b4807a01d540c101c1050300262998a80701d000f01c0074481c082c00c0303039000701040c0782c0144034035100c4115400706e81111070300c1c5000c140b002401c582122281d1400341c900c14141c0d5000050141250480354210341810104081c1c03e8160300118100c907009400c0390519030540354010368940042c2c4520340c0c880510743d5100503807900780e00555200440d54090b103540855050112200c69000c4203800003140b068100070801d0030782840210010070742c0d02c41c400c16100860100c1a045040c0148007000f0300c0b21b0f0300840065921400035501c4043e4000758445042c841400e1024a2210401055840e41700d08a40482c1d0302d4410015aa4440707540c0a0360070915081004000140200500c82c200380640c0c0300b11500400c4081244294203802074400041a5041440f810010301d00742c200c007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 436806897 1250 436805647 436805657
    0x4030302090f0117220c141008060a0e150301020412020a0e010b0a030c05040803072006070c03060c0302070510051509010510030b0301110a090801050604060f030b0403030f0207051c 80
    0xd0041c011001c001d1030348100d0039401c2c40c411754140741d000d41c1c40c012190380150502c43c4034100030803400c41419008001ca001200c03001c040e11101801290740c0a01240d10320740005450310b04001039420040742c5501724000c0d034010b200742c41c7d26038040b07822a0065400194220003c188510a50801c40f9515003d8a01848180e001d9814809407122a1040d00794003020565181034160115108100761005000c911050340d682d1801c1d42011440e20504602d051408040800c806000307141c941c08882d4002c0e404003003442c2503072440c2c803010000d140689410003415020480100001d809116070308074204140303030016803803c00402d4100920700d01e4400600505965005000c0c41e52201d417450b0850701c5601d400300d890301d1400c0c0868090142c1510f140445403010583d0690300e50002c1c8220291540d503402084241c0c1c403c81040140c941910030010031842520007030021130360002485502c10b00a06000c40d0b032195004610742240c0c0102c2c000c0d60795401c4403030500c10440e950385012010140780e01c3c2c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 436808147 1250 436806897 436806917
    0x20f031f0e04080315100c0203100c020a02040b04021e0c060601031802060d091401091406010b04150c020901030c0e1311120c1e0901090c0509010804020f0904030302090f01 76
    0x240c1d031004a40a440600b40700d20200006080c914400b81d14400c00744081c1c102030306241c800c0805400b14400c960201d10074055410380700010303031a034469a645101d040d40102100a19502444000e091032440c4079002078080201c0c51a610300c81c0d070080041d031040140681d42d401c10050355401c160001e070100d0704140c140038200c2c034000549c07009411080d070111070282d600d4815807900c034000e03c5030580040010185240e1011920010345c408151680184140d51011070b4141030341d40c88500c24001c800101c1001c1c801840810300b41c5124104e50403507030401041352401ca03000a0f16146091f4030484400d1154002400201f80002909800c2681006e01c0c03520074442d581c420180b50b07942000c0d00d01611603640c0d000d01d107400c01c10040c00e142c04040c000501d01c0b00380d01060565207034201a5070f4000d613804400021005018840e02c00c2602051740c949042143c021300442d108400944284e911181d02442508203a17264402c5900840c441e460050755804c1c3d54090049810042c1546c83c140609a04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 436809397 1250 436808147 436808159
    0x31a0717090c041107020a0605132103050c0f030403120f1d100c06090b01030201020d0c05250b0a02060906071d09040f080d05010602070b210603030c01020f031f 71
    0x10b6191016582181d0100302c2c107403042030308240d9004820700a548000241c01c00603019800c100102750541202c003509215a440c1c0c42c22800c2c032070f0044511100a01041c7d44d107000f00e84500040c090380f8004106803541001c0c21554a40385070016041914461a59000c00381c000350030080400c4070a07a039050007184203822500302d40d190200c03400340c50301600e640c400d0406c0c01ca120380d28a145da158850410009030815040044841009001c100e0140c0308640507950001c5c0079100d0400282c0e40301e0020903618452080f401000318890300c01c050b2246d15a2400702d4507881e6000079100c001d00950003400785140c0741c00b10f82e103440030241005007401500903040c1302012100c03a40850410081e5808415610f407450004050f0040007009001c0b11004580da070345a58403500076a040750020341c00c507500c89448008bc101144107030601c3d2085500c1040e18009017a20303100d8603e81c41500101680d04003842901510f080e80e10080c070488001f1000004c10000d60f0240c080711400805000310a012581046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 436810647 1250 436809397 436809403
    0xc0803090a150c0210020c0a060309060e01020715020a0e0d0503130e15060f070822060201180212160801021b03040b030c07111005030108010c020c011e0207031a071709 74
    0x40001e03002d00301517142e002c4400d0081102c2d821800c4050000000c4c0c1c0e6465a000340100aa600d046421500300110030054403014020345160f140c02441c0f403400c10340e00c0d400d860002d510881c0c1104c144511905410f0590b40d95a4280346910f000c0d038003440c1d44400c2c1d8070002c03122000f0303074000000c0015402d0601803601072040900d01ca80c0c5043c2c2c0c0f450382c0c0c2d807541c1e1800c10a41c09981001000104005216514801000c4c82540140d5801404034161512070109030709036180816280c00801081122902503d40311003441c0e50009040103444202042e00f60340c00b1503100035005002c00382c0d00060091043d6000010f0303400422141c1015501789410091080b401d44009440300440c1c0f00003154020901c80080003803424400020801d407001d0b112100b000e00310f50800d22825029501e0488003000b40360000c1903001050005a4449011503014841594810490004081148035018022000500303001111200d1070180001506500d8000c000400015034000350700c43c030a8000084c845440c03000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 436811897 1250 436810647 436810667
    0xf0c090905010b240a02010b040903021c0311070b07110610050312070b07180906030b0a06061d01030507050c07030f05061317090f04050403080f06060705030306040b0406030c0803090a15 82
    0xd100040d80e00c17580200101e0142407005405075100b442c0500030400c150300052608121990090306000102c0000c00a40480d039400c90360b40310160741001000d0000f09000141c40e4800d240d41842040403514044c114504141150348902034100c108041c0702510381006510412107020109910b0703d11035683e004c540e8540030b840402806064200001d0941240f02144013400c3c00c0351040010716a68140803204040036100210068540074010403410b108280e24410b0340b00d02191010b0080000300110005c12005004c10100702007030088101e665011b1000c40000c601031420715100040c50304010342442001340c0084034403416101010001445881013440c000c4203004401c0e00c500c2148003103849014002d081d5075200e85810200300030190002d00090160200704020140d0742e84480c10710501c2d104140018069501c24800203a4074a450703080840c2c9108080d2020651310fa40399510f0310411019042040c154101051000d05c0e030414a031030700000d20b902406071040c042d0088001e4400d07420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 436813147 1250 436811897 436811959
    0x9050a0f1808190c020d03031b08090a02100e0d050708070608060904030e010c0c150206061212030408070206040308031803041d0702120d090303060f0302011403040f0c090905010b 79
    0x411600110440c1c0105584d18500c0d4025291008081c41803400a00801c0d860403051010f40d9050f0000d14618854120b49100e00501001030040c030020342c08105404096400e010308102c0749222868194a500178040c2e0014424030042c00d1203401e1400d09400d140050700300c2420410b51200b04011a5a00040540c2040e00f50410f0292518860012030b5000d1a900020306010a42800000e80e88480d01400c40d041e0120703800c2e00d00b5905c45000304034161110380304a182d44c0e4055884080c036070b114400116003051180740300354600303940f95002c24001c0d04170758020b40302c124000c82001051202600240e581503803640140d0301c0d1070300381003404266116110001c13208840d50340004280318000c1060b455003000c1c44a2407516044641050740242107404400c0340082d090100024240c468072014a05070b80d41611401d40000403804d40e88066040180b041e24080301c21039000005c2103018451401900508002050840c081e007049400c1d100a410014083c41240001c5042801c0c0700c1800003504031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 436814397 1250 436813147 436813177
    0x3061a16140a1709040e060c0f0a022829040830090f0102040e010608040c030c03081b0619020313020405010f090e030a050703030b01030609050a0f1808 67
    0x22001914003400345400525114082c07039203c0303883d103060001d410f409004660034030107521210200c5071100402d4a1080040384103018400307020b4a03140203804400c509204869800c856049141400403035042202007140881171034400388802418948125074907003036030303084c84013032400819440e24009001034550350010400c1004042245000c000740c10740400a01e554400000b03007644111402c0c0ca54011034030034801541c44660060094a04803544580e02060070307803810100b52165131008000310703480c1c0455180480010f40300440c202c00b440c0201c250700d8568180c03040d0508140820707500f4008030f40c803074820406022074010405101e00d0b41c68002689a0f1078805980c9000e08810f01c0c0250300504000020881c0c80c0e0003203422080307642581c0b017804442d02c5d01c900b040c3c99110784102c0b2400a2010440f09021074042d411001b03058006260014201d65950341d41011108141d90340e07120715443d8480034440502c0c40c080c01440c050b210807000400c01b996900c21030b4901c520000a42144 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 436815647 1250 436814397 436814423
    0xc3a03200706050d0b121e0109020d121421060105180d1b0603020d05060406060917070e01060e010f050405060a080a021b03071a130311011b03061a16 66
    0x148160080c0401c0380014000c481554102c142c0161940705402c10f045d0703a400102504a0703411f038140501903a00e500503061950040c441d4680e401d403500303020100814024454410b071148210380000f8204060300e541d66180100f1380c0d089120b4040300c068030050410409112800007540200394480561808039650b04e0041844c0c40c04103501c00b01c81000341c81080036a400000c0342500354009103041d40e00c0c1d90007003040d5552201048220303655400341c04002170311003406001c03141e4400381300c4241c0340c40c2c042203d03c0d841c0e0700c00780386601c020260400e43c0002d800c40070380d09907560003900480a508040c02c125082c103040001142c420f0288030003901c00c0006c0305012a0644590360704480e10610180d078128000f10704400c445550343d11240080342c012080b840302c120303118401031800d4050160300c03940e11494542924200c65600f141e941c460a155a24a100680100c0300c1c502e41130a18010f40740401c10078584498010400c245081c58034846000304003002c0d103100311003035400c89294014094503c903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 436816897 1250 436815647 436815667
    0x50a050f0c010f0216030305060613030308220f020306060109031e0804030203030c01060f080613030e0105130311010f030b0a0b0c0715030203010f0503010903020c3a0320070605 78
    0x901841d06a14140f03034030020b15903603203000315207040c030b002406610240f105480300f0301844141d12842c04420b0340d40e0007000050000900c900c0c40130750000c454a154402d83d5071400c0583d140705050510841c5c00019945400c2d046003410f014141c0d00900901308628414034584940c030300702203584080070848103003194071130820405c1e03001d440c080e42d005011282c4540b13241545034000c2600f4081e991403021050000684114002901441035240300d003180056600307554155941e03445020510305000040c400003049511070030030000294000d40d00710003154180340003d01070120304d0000108240c01c101d00d407030036511000c0b110000c03202c0c034000300380e03403081d41002c1d050600100d03810140c40321086a0b03043c070420f649900a14180d440c0c504581588940c3c5030205401c964801d440140917030000682d01f151131410603c41442e070b000e0300081c191b600020030041c4d002140191a80706050301c0710b6030346c0420300d03a100c840070a1100b00d15070500319603062000c2c10b5a9a00c400e12601080000000f107081d16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 436818147 1250 436816897 436816901
    0xa1d1501050d0614030c0d051506060904090b0708070314180111030a09051504020f0f0406090f0914010603030210150e1e06031f0b03121315050a050f0c01 68
    0x203201440b000300319040c0c442d1107a0340180c0c0c4036030030703180b10f4898901420403c3c80d150700d42048060b4044c00801c50003000207000b00342c40c840203145603070020003800034120a440314056400620710801100c40a4607042a01030082c40b0080c001c042054074020001820500700c00c82e44c2d03000009440110b102610504226024140031050340200d40300110601c1141d071801c1c3c121080941c800e1003039a0040c0c00c1c110040b038844104990107540070031012100700d05070030807100450034004040e00c04100b150301c805c880d00c00e6030030211081000700d540380410002d012115100900000041c0e00070701008d072458400a603940c094039140c1d0000d507030321100100710107882500341006141c54241507000d444c0030800649840613081c20a2100c02c440c034002080c601e40440c00ca8100340d03584004121154403070042c0350051890f00640d07905841240f000070000c400e00405800c00740321401120410781d040907034480e5407110b034560b031000340b200a000000119030802c041d920124900c08045407903201c481040342c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 436819397 1250 436818147 436818157
    0x9020315040e160e010e01120c06050c0f0715030f090c051306090606170a0c0f05070c3b06030604030c0204150e1b0403020f010302030c120c090a1d150105 68
    0xd0208151280060618074000120b17040711018004070007160798428081010000c4001c0090a08216203418040c090191020380101131901045506c0d00380b101c0260351600e0040d401240100160b1403914008a515007d903504060181c0010700c16400659a8001003140c2401514803416007280407604100081d40f00d0801410310100038042d032b41d5504800f03040011104000d100076900b1100246000002d8003d031a800309140e80c0b0499016002d190131038258000403c2100c0c0d50602c0c1c80005070644410500350050403c0b04c0c400c000710603d24880b0250320b02d608100d6202100000108503070f0399004501540d2094040c00d1402d00c82c8103070b02c0010010910709071414056000200c3c041411480303014200c0c0701d88040c1800000e50100c6c1c00e400c503114003951100039032082c40100085111b52080d006160054050381c1100d05008041d00550305140b0212140c02042c0400303c3e488859281c410b101100900d40c620b40b414105900071000381030500c008069a1405141440f4004542d00c1042161 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 436820647 1250 436819397 436819423
    0xb04020105072f03010504030e0609131104090c020714010e0609040504060c020f01110d020f0903100902130c0c120e19030b07050a121a100c06050109020315040e 71
    0x49110b49258020720b040c0f00d5039407602d41442c20900c2c61031460605110b898021509515400da24805031002c001d1294000c1100c00d8204681412002d2011164010340145501104a240c1c945007000c605004442491401c07008541c003079201005000060710008220000c00e20341110b80c1203444001c03512520409a081d0741181c58001000180842303035100040280b055403d441002a00d006200c0c00c2c1ca05407030f552000038004000903d41c9000c0740c1d0040c0128441c80c4061810315402000003401c1110075400d02c400c05032201400011481d2a040c00a103018200004205071921010b004025200c440802405600101c5045003800e0140081441d04d40d4000d10b119208850348180b00c140147d940b10448141e0080301c041007429001e1f5090380c203044240d5942d0340701030010038007080281c8840c40e10303600420f0003500e14075200d80340c14800f43c41041ca19203a09100035030b80d141240407107034141d00a542e000e105005002001d040300f101845a10001ca4000c1860300780a01034605150515a0710 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 436821897 1250 436820647 436820663
    0x306030f0302010203061206072f07060207090c1d011d0306070e1e030a0308070e06031e070905030309040b15160203070626090c04090503041514070b0402010507 71
    0x3620805505400851240e6015600c041c4c0082003000c042d41c2c0c88000355a010040f4901c0c0f48600c00d098007400c22911a40e00707000106d650390303113144203860501055400500040e0000e940a2116071441c0c02107101049440c6820304400051048100402c0b180d5211141084490346406084028078920030310149401802e640c07040c108858040c042098009485003e0460580301c140070045200403a04403807000740c050013405007960340440d9002e400612400c20711122094440080e10748202035803240801040007a812810809034400540005010408100141e88148425100441a61040d400c16078000c04e1a11b00b98000800703008a01e21110342e60b1001107540f04000003000e0b01041d00070b000754162401d042d291041201c04a2046204507241d611030095540c110500d0301c00030368000c2c03900b0150791240c00004001010b40c0e040e04000d0792203510100301032001458041190380100414101129034000b5150680058011550041d104801400020b4290b9004100700d5800035481004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 436823147 1250 436821897 436821923
    0x2030f060f070905270c0c0d032306010e0103020328021b032805090301020703081807060801380403110108090c0409230c03060a09080d020901030603 66
    0x80c0100e80d05003102e2400024142d4403000800d03081c200f0715400506030100c00c88401c041e101040b104841c101070b2046c0250f503006c200001c07e18000b8000c0d40b08090140e41d001c50025440b01d0020f44000014260400300c80700d030800e01c032580c0e07084414490b4610007800d01503100d43e50307910004000294070402c0714031818422201400d000d070b00c1e80103017203020154101030002040128510741d00d0044141e000010100ba100c0148000c1c408500b903888428a454814070b4400c10350082401d80c4c00069003100451889000d204050300c40d121900e01c5c115004006040c1e861510000510001d410310554400d406038080318004200c0320841d02ea482203a041070040b00181c88010503110354883c3c442520005010494045ca562082000d54015205032004050054245003040001c0415807000c4501030114441403440410209400325a1740010001d46800c05802c0f05250078440b008043d41b41c0340b46000303480000515000103490380300c20180401030301c800340700005030010300060700090244480b11039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 436824397 1250 436823147 436823161
    0x2032a0d240b040806070315090207060b091b220e01150201060e131b05090c07020306010905041a0c09090c220806150a030803040c0302030f1c050702030f06 69
    0xd00c1254191002100e11a01c0707503520481036080c0a68001c540140d00488007040016107c0d411200f490100060a8140c1c1540c0f20644000c0344c1c0012400c4480c076842c1c0407c00c0e01c41c6010b01c0241d0b0300580b010490100b00c03080e40b01c1243e9501c41c807107104548544581c00d02e0b1400da055082c00010b000540e500c0b801c80d507155900e07030b802801c0001c0b049005609201020500701c243c5408035001e4440440105900005541d03020107228803440c0303049540c0981c400000e5183d47d065111402040b8960040e540d446217401458140301d0141c04c02c400e503078206130600002920b29186c02e020900310850459554645803070f03420030303407080d04580b650150f00103060180c01200e07100204040700e6812900783d031401304c81510b0429007016218109560b00041c00044040402c1190080707054001002180c0c0c064a03035039042d44a41060300d0984000500035014401c6090402c81100342181660060001040c8000b0222031454aea014150810074040340381021510100400620003204606907481460040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 436825647 1250 436824397 436824431
    0x11010207020604060c12030c0c0204021c051501020d0309260d020c151e18010605030a05070617010e010b0d0902040911010e0406030c12030c05121c02032a0d 69
    0x44411b40f00c00000c00c104031001070007449242c1c942005900c44078110746040d001c001c002e404c46c64a02005505440c0034203001800d520891744580340d00c0380d00c5419052100c0c00245048010313401071040c0352030302d01e16002007418246145a540c12032510581140100c511054443c0904d00310b61400b24001318000f0301103240400c80d0541441c0b2141c0d80105a07441c41c1d5165031154000410884402000020411100b402c450300e80d1800d42c0700002040c1c040e43c400c00b107407500201c100181ca554100704bc0921000f03900030318090212000c0600c4050550408101e81441001072155078924080040d01c80c0c00902241c00c144042a002001007004071303014100040200b585040c401d001070016404440da51078648a001d06a03034002e1400c150b0740d8102840c1e030026841d119020f03424009003602d0200020010450041902100c54801e03841b4038465601e4441c25082c0f040080002c2d00610400c00340c1030000009000c043d2603002131142010450281408510481d031542d142c80e410008200382c0b1130016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 436826897 1250 436825647 436825667
    0x1f0e0f0603062203120b1518010302040b0406030c02010f02070506060a061d0111031207180b091309020f1203040608090609060606030915010f0303020d110705011101020702060406 79
    0x26030075102c1540e60f4001c41c00c500e000c4001442d2250303040e0540b40020074441c3d071011107015241c0714005401c010038800118000090b000390000076000082840c41c01c1403000500455407020b00701076043c2820325003003003018022402098105691a8400345015100350000502e01070b14020440da40d11641c2405600c0d03150407036100d4021440c108000420900c20140d44141c0c8421048001ea2605082c0044076030484408260300c183c40144031510306100c043c24183e008039003035211454012000c40381c068508500c4d6107c1c501080f0207200500d03080d02c0395000b105034013031500000940c0000030303c0016240c0100814882c6c01c0009000246030098000000b0302c152462a00c0d030264540d00c902900d652000c003201d100700380340c01c09004246941058030283d500070600320260f0360050a10b029000d50765200364440f03040705629050070800d054042c01031440d00344017885c260001e04000780886a9070800c13840303030324100a00c00c622203100f542c0a40c15500300a900414841e6520350702d010091005c401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 436828147 1250 436826897 436826899
    0x408070210020a03120e03040905090304030201022404080a1107031214090310090f060e07030b011205062214060106030506120d0806041b12231f0e0f06 67
    0x2005282500740e4000500e031040036604d540c80c2c2e04010040b42d0030002818080000a041d44014800401d0b9441c141c0a094810b403501d00c011602d803031550000a207051304400301c030144a144110300c034080f169140c039400c2d40241c001044030750358164070004070b6803143c9a142d0031915006840c00401001071482c0d44414020a41c1d0325901c4a10100c00300012501c2540d05d66a4507910a80b540c030540d107580e07000010040d00609a0002c2d030900341c1c44110030349504450700c2c2c6250300a04c1c014401c00130401301c0d03d80500b02c900a40400c00030565200d5507a0b52002d41103200e40f4101e01800c140d844419110341e410b5039800000c60100e20401400e85a17520402e01844000c2800d00c000982e003424440c450645248001e401016912102101502c0f812005407000340c00035140c140782e10410003000c1d216201d490702030392200064000400744008460b64500040c0c480600300c05284040a100e80f0401e0300b00045049000380b400e1315154407a031020041e4805d905600d940d604100b01041c102d181d1030f1040d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 436829397 1250 436828147 436828159
    0x3280504051b0f15040e0a05070816050921010c0207171c03020a0912030e030d08060a0512010f050106080709060e010c1401060b0c0c0f0901060918060b0304080702 72
    0x90b01096550101042154503400c4443c000b101c900915280540a40e496900c1c0740c5203144c541c50310b04000045a0460340ca44480d40c440051180b00c40d40260850f92007102054141804049d1a00090951140f890010711418486810361024240072002d010b042100d44020800b0f4445603102a45804240c03041841c28004860803484821002c1140d110322420a5204800c511540e04103500a40000c0120000c000083c42c0124903800f010880c4400386000c1c2e11084148400d0001305494281198039010030403180d034050080ea510b40010ba40c040e90800c07244c200c5440c0e0483c0107d4010311003503d080f841181008000242d19400410302c0340940c1c0c1b296502c2001c961070b0a4140c5400c80c6010125001942d20076480001c0341a080150b051941030000100303d8039510b0410f44442e4000c0520034941e5005051094464500344e400103911050558130102e01d0340c074020000d440c140e801e02c5a00c07104000400b080000405503401341d00039100d500106234490401d81840d06a90f040710104a0080f6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 436830647 1250 436829397 436829413
    0x10c03140c040f061209020d0b150d05030f160b0a0506011209050c0d0203100f05070e1804030804030c0f080a08090105241504030b0402100f050703050328050405 71
    0x1905003070889080e2040e1158003100985809003c031001100c0c42c0350055115950700001c0010f030b0310300304461a41130058141c2c6410303041222002c00c1c5502064072040c8511344034400d9800088012050764015492410701944a203161b484060700c52440c02d00007070452085404204010b445a4040c40c01f0f010700784e0b9151704190401086000300d4451160181c4590f0080103201c4071403900f1005a810340b480a41a02c843c46609a60b14003524111000e040502d51201d0402480720360194542500d03201c110b584009903452180c1002c04000c4c00f81001d41048483c100040c14180540d0741c1c0320075240c3c40b5013400617045031424500d44a411440821000845000110759801070500481340200c01005202030106a145e0fa5107082c0403213116415044070603014402c43c554444006440103500500308400186468410081d4000780350110704140081070450b803892039070040507540d0050785070520f07503929200c41c900c03400f0818541c0e075686d00c0c03d0b441d130040300e00004803600076502591042e81110080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 436831897 1250 436830647 436830661
    0x803030f0f090a02040c050913050603010c0f0e06030a020f0f03040201080c0304120804020103150b130503010603050304060c0203030403060c020f06070915031116050a05060606040509010b0c010e010c0314 90
    0x52881501c020b54035900000142002d0701c0c143e44900d00450142c1011494030b07902d003003c2603024001c014440c401940d0b43c001c12000341408e0041c010300c1c11445c03a080306810100e03072010300304042000015001c1c04020002858501e0249c2c115070101c460020099281c3d0f24440412101d81e00480e0f040340010340500103d40c0040004007500c1c0242c2c0e00c40e11146a04010358011100d07490000d00590402d52200400c0c4040400c00403c400070300101404160707035000402d40d07940c9554250380142c0c0280c2c50481c080010070340100130748003960068904104414000c0c00002d155001c0c07a00b014210529148803c1c4030b00d900001c10900c4500180c0580701103544010050310819003900c141624040962090031043e0311a138080760400008510490601484d0200d801865030342480440f2241e114001140502c0300401032079900c00002c481103458581054040f41707034040c0620030844c02038004a11002e128900b90003000310142c0d8a4000c0140000c00f04005010300300689420311138010b242c2c046210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 436833147 1250 436831897 436831921
    0x412060b0604031a190501090606230406080901240e0a0b01050d020f04080a080a170c0f0a052209140402030606090603120403032003161b0308040803030f 68
    0xb204d4200411064200c3c501c505558070000042c00108444030350380304981c21070940d210755400380a02200000d1440c0c140301014155448034081d461400c5050150b04442c1c4c006403049900355070040c60f104005454030300344580505046506056000b40303c1010f240013526604221007140da0050340044951101e200300340c1294001495140014000c1203901c82101c55500141009810813041702d00e080d582d68106401d091856074119002a80025214442075102c109036100385481d804204450800046c0d804c1180b0844021002011012814881090040c0141c031840005441c480c0429030341c10b00e142c80600320710301908120301d01d804c0008801d40c0c00f44280612456000e40200800c0d1640410800118802000150b15102d016241c446c42010800980015403094a4001c0320760b040c4110007041e0786941010740080da10a120089441d605801d8104403507400c0502a0002c5600c0c0240a564488640000e0030b0b0100000b400266031a00100031441040440c4603030300103803101121400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 436834397 1250 436833147 436833149
    0x11072f0402090d2d0c05031509150402120d18270f1806050403030b01080403020a031101020d020406050408060601050310090b13090b04060b03060c18060f0412060b0604 74
    0xf070401d80b503624990025007042c1192040d900754050304d0044044240e0b215220100c0030000f2030350402418030420140c201004441c0390320720400300d80c101d80c0c0340001c1503595031404402075240002403070740800d082d5107800800503c5092000180c680c90b411400c2d0207018140c1d84104a01c03220300c00000003402044c1c2c0a80707020340010410b0410b079404500741202d0081c01041c01c10b4040305940740e80041c00071400031030312504684215400303d0b492030030b401c01400302e80310382040d01c0c1031000640402c00001d40c0441c00000300c5616080c0024a50082b0405600900850350013615081c0f000a0115880e6000f001900440f440001110380030780e541001107469010517039480301c071040991010b000c0100d103a0068200f05c200900062000c8418050b440705035040010705480f06450402130000707205043c0a21207420400360700400031805c00c1035181e40c0c24030a500c0b66048402c0003045c00046660340104035080410003130f880581700c54680c481001c074188155000c88140e8a01107501c1030905040007550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 436835647 1250 436834397 436834399
    0x10e100c0504061d040905060a0501090b1c1a13052413050a05060403080921030a0905070518011e03020d061a090907080d140d11072f040209 62
    0xd00741403500100f9154010680303106085600c0c1c10310200403980b175074031444024501031801407603d03041c4400f0300b10442d281a0007441103c0e0600d8650304140d2141000c000e110f030103c414000720511141014110f020200007421007020000c018401c6090000069040990190080e1801c02c01c4204181c1c0310000d8000c03003040718070300800018040400101d61103094030b0088090301c40b0b1300380c0e60b0380700c03410310300212412004200c2c82c0062040100003040200701c603004802191130f030501000d1044040d400020180e55206031100b42d58010040d052240300000d00c40030b04a0340180100305413020b144070090084405040840f449031024503864240340c1c080f030345c01030180b031080081e60703d4202c09055038108500424241c022003040b2034807000d00b15803240740010701408200f41800016818455001000e00030014000069220180c100c0200d44603840801c200180c107002c16003905000d4044c1410250501b007844603182c050702c03c401c0344502c164021048000a442c0210704200c03c90244040b49 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 436836897 1250 436835647 436835657
    0x1121109013903020a06110d0b1c0204020f040306140402010e03060c070b04060b060705010b042f0307020a080f0403120c0b0406150803070c030515010e040303200408010e100c 77
    0xc20850440300d07050b50750701e0301034410341c1c01064039a01c0e030038103071105e07610101074450340040e40e40da0041c803620403000040421034902c56410240701490808520f900700181c81182d0008003912000a40703001c9800541d8001c0060102c42082045481d10b44800c40e02a40450304c045807412152401040061140c002d00c0720303c50500240d0f423038208014200500440d0070303540d18103804160b0b60b5000007500c0722904c620004206e00703070741d034003408280c96444c0d0140030390320b81d10f40f0451380c404501c01c40d484620310300c01c1c0350984170354540404070f2074602c01a6020708403010014146108800e4580200143ca0003a6025202214461411245428480c802510704041e610106000071065040340f8040e040540340d10340c031030740c5420720f030350a5900c1148201d407842c034210300801c200a418440400030300b842c0f61030f9240a41c036004c507009061000800060030503548040c40308004040d011440c2d40d0440d01d0101707603216038548109074002c0002035100d058604c6403030340410480307801d401400d1043c00c06680d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 436838147 1250 436836897 436836977
    0x614030313061d210706020c0f0f04140c0c1c080403050702010309020a0801060f0801050c0405012604060c0201050f04230f160e01150903020607020112110901 70
    0x119450210340307141c2c0e2044103403603811402950b00d1007003844003801c00b00480050725a0f40e070345183c54283c484c6c0c0414103540086810341d0301907442001c219100d140603a0703c00e0454503048005001801d8549504801440d45000d02c2010401f0342c1c05000303d074070200111894801d516600119032044c549003500041d0720400000d0010384240040d01046106041c0420501a071784c2c0001c903051281c0d000b0a120742e5551a00f00440105440402d00800529008104500b014200300625201c0c90103418144280341c04200e404049604001024400300c0d418060f19080c0303445e001c2c016080c444203800043d07003460301007a411080503007960700441d8001c07403803407101d43c0110f61400708040040340c1246070700031510041c0d1065028050610609030400d1400c180504018180d101a0810b07040507002d1801e02101c00d002c0d80c1c2000d110019660111456511340344940b00481e919880303407030b016040c40c3c20503980719401070001001e454000c009803203076409800301a000b1203900c11200c000288030940b4240f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 436839397 1250 436838147 436838159
    0x4090e1b130f0e07082a090c0a2c01080106030203190b0d06020c0606030f0304060807030f0608031602041107021c29060109060801060203090118050a090614030313 72
    0x4030045020442d20008611031440b80c07003107418411180e00000342030f0090f02c0c00d0403040024006844101407a980d400080c0c0700301402003201d0900040c0403c0c040b0300c00044c143c010501420b1100c506080c81081a8040e203941440c0c1c0d034480b001014101d001c10121800421114040d00030780f88100e0702d02c000400e0540602013000080d10640b18002d8010f22030511101c04501d440c0010407008002c0d1004106c070381028002d05140402c0011004840d40040c03100340b0070030ba4007650013a0400d19034074000c9038030f04965a0007401070800d035000e060300c0d02c8000b03500c04c0b14060402000320054001c07607040020b070010356006181c500c6803800080d8014a401c81a80c04031040003022140306024004442c000d01c2109100000e12180404903a81c0001800800c44a0340c0c0c440f0034880a0200b0f46044412940340c0a0040c2d9680107507404a414082c4040823034400c03002c0e9248007002480300a140c21489070f501c06405005160307a0280248800c09001500079a0500108840b07202541c01046a02c07285001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 436840647 1250 436839397 436839401
    0x905031c051312020906060f030f25030f0506030105012907230c060f0d180209010b0405030c03030403021014040e010e1603270f060204090e1b13 64
    0x10200340901c80c091000354a00640d1421440c042c00c0050704500e03002c0c0090040000c804402000c080c802d10040001c904400400c0c070030b698010790b41e44031107a119100c102032007088801c0414010504000080c4850480c0e600d0b03000b41e00066040501004a40c07581c00906098038024015910741c2c01d16600448102108a491540c08201141019040c900e0640d912a4400000c0071025a00c1500390802c480c0450b051151494820040311418034001591074260350074006e001200d89050342d943c51141d002103529901d16180c4e9402055170640b5a101e51032002103030090300406000c2d10038558410220f0400108442c140d940040151401d108007040880e030040c01d00c02080092402800000381c0c6880304c0710864007903d1804841600f501c0d0440cbd280c40c480c41c1203804c110401d0300785045280b40c0f0001004482842c4114801d4940600c49070903e840301905000000f00f4840c1300103000510324006a0010040e5100740c01560004c12400c24045914101507a060350b20240300880e85030400801c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 436841897 1250 436840647 436840693
    0x110904030e010c03050d050a090c0b04062f01110d0605090103150e0f011b030c082418010f06021c0207210203010207030c061d12030709170708010c090503 68
    0x20f05c1d0180ca0007104284d4102a05d009a9450039200d855000c0c1c0c10400c040d4500c0040036081c200d0b041030030301d46089402045040a1000080102c0140c401c100c0d5803a8480103403d1101070841c0240001030002007500c0c0c59602a602c034a480ea480d100001c01c03185402c080f90b80c100c80d007040b20120844190380e03040000f0004011808014425181c4801d40200e003030142c0c54076100f0700101c007204000301d541c024099940003a01c100401c10550b0420941e105500038000703a9001b0101c0504604440e140803404610310702840c0c0140111240000803042c1c918442081611034a1342907e1307550440219150181603441400c2015030070003030051188007200c1c40d030034050050898100400940c0f80d0007080c220b904c4540b003a00003c040040a105010190203542400d14207240346010000d92180160784542410b1444414203d0000206100e00e1203905100041d08003d11100390810844550550711142ca100c0d0481c00d5080200c000004c0c1c5c0641d400404599028003c1c04031111000040c0c3e8024903d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 436843147 1250 436841897 436841903
    0xd0b010e090901021c180f0c0915051003020901080103030806030c10030b0a051e15070203010e07030312142e0b09010e0301061401080a020706050a09110904030e010c 73
    0x15100025103a5071006030301030080e2809000140e0b6003121600c0266558800104e518000b403c2c40d4111500c4002400502c0d900d0350060750401921a483c644021700385140da02483c191410200c0f4142e1104c60304036203000700e035000c0316040b02c00d2500032000c1e000d901982c4e0b0380700c5c00308050740c0c010000300f4011041140d0004005050715084035210740000c0c1880c4640049000003541c40202d1261410111010000b502e030864400b2410b101148144241d01c03020322010b80240c944a5840301d4000500c01614401d69006000f480541c43c44d40d440c13a030320403141c4406c0e40003d40201c02c0301003801040c46072a0742845200e1580116945c1c007422000516078014903500d508005043c070f0001c15080c048084007420000c90303882e0703407207600e0400140328101452091303200c0d0740340050412110503080e40e844202c48007820041d00c02c0e43e49003145002405141d00103041e181c02e000401009240035800341c090030344952846100080e024060010318802164010042041030980c0e010542c0641c01d9a2240c4d44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 436844397 1250 436843147 436843157
    0x90702030c340f0b090d060603030c17070803070509030f07030b151816021f05071e0801051c0606080309100512061c0f1103060108010e030d0b01 64
    0x1c800089a20306007426841c0b4a02d0081e000c20311107014054040c0c0e1150080d0800806074140c24030529403c22a22403103006403601d00042c0301d000540300c46070089080c9401c110300300001c1d80c1d01c0c1009000c45401710070403101d60b5640700152001030f0b0703202c09035032686420000032410b5036103041c002c0c0c4056003d9908950f0500c14503440e010040402c02103140954421005400e203414561587e01c8004001c504d070501c60810900c0040590800c1000990b2000080e098902c48250141c010f03410700c0e803e02000d405c2c600070070dd12804441c0701500114021080350340c94070030302d81001c01c411707034540c00c0524204009882040100581d02c0d000d4070100040500c410360003010f5601d0b540324011241191f0107110720b9003020840304031610b00b103030316100d41d2542410914a403907940d4440704280350f4001c1050b44a140740c41a480122039402505001080e408642414401030900342902000f82d4142194032900c208800460304100c180603031442040740d24015814500711060071406807188019090400c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 436845647 1250 436844397 436844407
    0x2a06090112020705100b060c1b0a03020307080706081302010e040c030b041805010b011106011712030a0e0d0e060406050d0b0303120a140402090a200316030b0306060d0209070203 78
    0x224984010641c69201300024000c0c91642256002516914640039218030380511007074103083c501046801080000d00000c0a2040700280064105020794002940501c511080810b01c040000f0b00303d000c0d1030762a11000c240f0340d50318113061180a103090300280061800c09265615081c00c0c0c02c5010170001074100071a215030100040b504a480d0882c400d910120304101400a00000384075094000c00281b070043e62000344100380325650300b01031090702d2030180d094103e194040d0061004e40700391910f8450030350b940d080c488140d0024007a008074001c3c141c012106041901801102668005003024050074200b41c07501105440503040180007a00054a5419100003036a091004000300100107140100a003000040002154194031900300000407100a00c000b6035180c0d1040782d13001c0f41c16200803035091850401450b4460402008500001002c001c2c00845100b4883c0e2030382c0300c03e08e668100000d2990354100f560300d410035659260000b0140702500d01500340041c50b40d600640d1401200d1800b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 436846897 1250 436845647 436845677
    0xc080d06030510290603010b16080a0306320103091a0108030a0801080a021804062a03110f092701180c021c110109140604052a060901 59
    0x40302003040f01050303903541540040d040741445851903229082c0510880070700c144080f03022884103005038100560041220440082070440400d100d641c00001280c0300d502400015015005a0150310b0003000f07207081003c0c2140608480000303c1080c124070040310070302100198001e100200056a85078800c214100c21050f03481c00351802044c0101c0110394800d0085070050030284182c0146010fa0450010b407800340e034030701010040160080d4a428403a885621f8000010404465004e640d120155843c0001c03210003404281d1b601a252400d20407102d8500050743c00e4450201c0102100000784900c05031070070403507541d440203d01c1c058400d05190094414070903225091788a4014000c07814460320300c1c1003640c05002d000381d01500050032524040c480c14003224a20050f07400800807105040180700a003504200c00301c64000c1940302914050303014040e140d2404490549440c030560361400001528009259600035201c07030f500c21402c100e0360400c056580702601326410480c0700c160343c0d001d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 436848147 1250 436846897 436846903
    0x10203031e10080312060f010f0f180801050405010c0201051305060103080a03021201080106080c040212042d03030b09010f0b041a040e090f0d02010204050f04090503042103030e0d0c080d060305 85
    0x100105c070f074040f40a460541c0c100118006c00b1201c0504000081084140c0305401850030076074110981440c4811820101a03d260700c0800d1b80440c0030340d1700342002e100c1030040641c441d001203400b95009000e43d0341e40000c080d40c1076902c241e004206030722090040011801c0030b8050410803203070349000b501d00410640d001c4c28804081c2c22682669644020030051500304001046e42c110317041c1c506500302441c81444420200b40203002800174440004118180c80c83c00540c88185680121a6018000c4070305005004007240c80d2001c2c050f100301300000c1030b20303d14003030108200c40d1041d0380c480c60f1506040408000d07403101030742e001000380c2c28400070901c8540d0480035803040107070310020114204a110264501a181414901035902c10030041c0440c1e01d83e200c2941880105850100f2058503e01e0a10b1840c031a40d030000c01e1880000794024090301507070496001440c003da900f0700c184952181d0b03064403400101c1c402b0022900c840103c1000558250180c0090341088500050142d9030b5111541 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 436849397 1250 436848147 436848157
    0xf05150d09060510060206090d0f084212030316021606050c0d1d040902010e090a0e1b03060a0b031c0906120e030f0309030715060f05010203031e100803 67
    0x34013609034405028a9034100310465020110754010024165180806441d541050a000041051600006840d8000d00000d01000240800b565501c0494030500b40080004e440d200d150900904081c20442d1034888511912460000052352071501e40300c203107030321941d5041a21400d5009103d0000c240301c00c400c2c800401000d0645034035503105070380e508103802d1041c91f003c5181844002e121030031202550a480018050091718005034020313041c001603800d9100e041d103c0d94055422020000c02d0781483c1c000c03a0609146600311002c090015000100710304100f10803981642c0980001009513005411030008128003800b038600c42542020b50101c070400440c10740700842c07942c110400a80b64800c81201409500c00030400c170080e4610506c58583c480c400302548440301c04008500540000d1003117425460f44050040c1407421011070b0840900050b200b101d28901c41c8580000e4a94008800c0703070301c070722140740d8080941403061004078001d1201400b0f40d802c5410100c0081740c1c10a04100810b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 436850647 1250 436849397 436849411
    0x31a100b0310030b0601030e06010e070c050f030a0e1c0f14030a0c020f1503190b030618060a05010605030619090f020d0c0c0807170f040b0705070f05150d090605 71
    0x41502c0d0540c01c100840c100c0150240d410103103880c2d811f4242643c0480c2e4581550144900164207898403001200c00100d103043c040c0903070040308108140340030000001d001d900265101c1050f140c81c0001004014514a00c040b156090b01c8181350001407138044001c1134042c450322083c20b06001d880c20b69807954201424542c04141d8000c1d031442507203404001c26100090495402c1115040c0313030341070041400041c048050800c41100302200c100a0b50304140c41d01c0002404940c19403501c21584401220308400b03090841c0983d202049585400380191030594a403621354524586805060109080164036180030031500a880800c007031000d4080c5d40420f134400000507031600c1422030842d040f40d1100c0c07001c0d4140301c1500c0c003c0000400800c1615001c42e00206008400c0b14201089a03d5115003140140c134036030006800311f18491180082c013481401082142d4416454000050102c0ca40d4018580e200e02e040550080800b44003005000c404100705001c03e1011183c1da0b40070964170190307003c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 436851897 1250 436850647 436850671
    0xf060a02070c0b180a0b0f0405060702060c0d0909050906060f010f0306090c05120112020f010f1103070b040b100609170a1709090a0920030a020a03050105071206031a100b03 76
    0x1a140d540380003103008003c0c1c080041d00c0d51a052440347e40031a51701c5140301d0300340500c102080d0700381075503901c1c015641a8010030041d641c81e840c40040007407402a081c01901d0340685410080ba500c1e40c0e00143c4d191240c1e1015200301c0d600501c0b0b1005450420200083c5410562200c2020800d0b030440d000e1060740300741d10388400e43c0307443d0004e0000c206050f058014030315058000708000003603a14810020b48580c0282403616407040142422244040c0c0404210601d200c0000c44400300010103104903c5030380103007000d1550f6210304485202409461040100143d0795040910035200c10103d840484080c000807a02c42c01c4117a44c0340804c0f440300f188940348851010548045c50306142c42c840d94850b103101c03010801000d25070b507400b5082d0090702400071003c108004074a19078404000b40400b281d00100302c211030750742e03d1509502034001100c0b000001002051f8421501d09680034200c160f0340e00010f030b03401e2105125040d05141303400a1220440c44a05140041c0d0b01ca1400001e500890a01d00f203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 436853147 1250 436851897 436851937
    0x90702010203061e06221406090a1a0705060106020a0309140310050709170705010306291c0219030c02160e0901020403120e01030501060e030a11030f01020d0911030f060a02070c0b 79
    0x1494001d01f0380240214096041017142e41075079518000018140c41481a4950382480d014061441600034280018840d2140714004100d05400080107000c1070300c26903a002e030713203910b43c00300b00140224502d4003601903000c00c03d60500610150821580b0000c00d140040681780d403118100d404101c9405007811039004400180850350f414001c89000d0400340030044506002c88c0c0400080000e281c0000e0041140483c0001400d01300004075240c15042000540d15903080740910f1070000864000c240c0403901c9c00002d000d2090000c1001c074405101c5000744100517180c00c2403441906001090000255420480440015001031505005a2039540c072803d060009c2c0d8005421510103802c958280110b05e030b02c00301a43e9000803009a860342c000340c010f400364100000f1078544140030b50f100005500100b4000ca00c1ca550381c1c04400f20900a04801222103c0d403414143ca5800100314115079030496800107204050940043c03080500c50301c01c1c49541760740c034025001c4d913400c4113031000810400c0c2c1c81 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 436854397 1250 436853147 436853159
    0xd080301090e0106120303020705010204051503060f0102340305070605180103180f030e12010e01110a0c0201081305071d09011a0f0103090c03030c02090702010203061e0622 76
    0x811103260b450440020011030781010083c441000076120014101500000c6403020004290180c82c02080050304100008400141000e07441d0421290b65001c0c0c1511041c00d55150b00c0085c0382c09d104000060a1494260039019131841e81541c450070404020355282c0000003e41c04200c0703100201005d0b0707a16900c0d101600d815a813020841c100c841c0c1054209112100c900c0c1c0e683ca038100e4140d0344050844440305440c0b03401e5480c410303e00813107540100001302d08102c140c0103404c50100c2803443d8000700508402104803280070300841c150b071400500040c0788800154040e0726000c0e00414011a000079001e840d5465901d482040d4001d45a00314421908400c507003010300415070804c058500900c611852011068944000700000b0f920803822103e0340c8060344d00907401003482e0394001c540300d0480358a07810f0160036506c500c0401c0f4062601c5100054030944180300380d9008180c02085134070505091044640100580c0c01c4030f560005042240c003070038003012140d00d004004040c10030311445140003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 436855647 1250 436854397 436854401
    0xf0316020307060e01050409020a180f061101020f0708030c0d020315040b060a120f0e01091a2211060904090b190207030503010e1f030501060e0109020414010e06090d08030109 77
    0x6848202848903d14292035139a030400140c0c3d041e00c2c44d2503030051f15012400011140c1544012124008140d064004500e035650380800c182955440d407501c10609013840d0105080b442080d04d00a0008400e00c0400b000403010001542c008601000003820b00782d00a8900c022030b4020340d020b04018901a00f00081418180100030450004072406820100c100c00c01030401c4a450080c43c003940d40d28480003882c2d521f66800000303100664002040451344504d00300005c050285600a8940c11100005100c600100410003200a008460588034115940d51201c0f88000c0000c550380060240f00e0220103482c0c41c8590380300a0b01074140c400060504540d401110700216905404040c010461711000ca5044401c5070704640c03c128011000d6619648141080c40361a0104094203841100c000148030054004900385e8100300d510342d109999440c2c25404910903841902851450800a550190f001b0b01a004075650b000d808a03180070b441d03000140e040140d04200b01c800d0240031006101a0060b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 436856897 1250 436855647 436855649
    0x606052e1407060b04330b0307120507090909050a030306060503060612090c151905090a060c03090509130501051617041403030a050114040902150c0f0316020307 71
    0x90300306025000703440030107903840303105007500500420b45501da60f0405489940c848913442c00000b088640914080604c04050100182002886071b4004004101c0c03443e10070840b802401103440303644400d800c01c8406406440001c054000b07100c4500303030010b00c0b108540a4001080e00c074001801d40c0006510f80a41154201d402040412100b07004002c503503225a801c41c0c603585020403604115a45403aa1545040c101d190626001520001b80c1c0b80c4e254281d101500401c0341c45940032002c1550350b84122064090200d406500c040540020041d890290b01d9260503a80640b801c01502c1b929080480c2c6144403d039540301030082c030300001301d00703018080c0324046e017029004800d441d400e0080c400007051a801c00101c00c0300c0308407000200d4100708442a42d544480d05030002c0d40e40342e00e461070840004007800d2141c0340c100d200174800b04409107043d2041d08002e0754014045074010802704a0081150040c624024880c401d5076202001c5c02020000740140710500d480d088c1260915206050a100071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 436858147 1250 436856897 436856989
    0x61017032703010f14060d05032206170f0a02030a1d031305010c171b060103030309020906031f0f0207050708010f110f0301050d02040902040e160f0509060d060605 72
    0x28008a140320000311740c2c14030350080d408583c05401e0301c0346800c1403403c6209050482154144021030240d141800d41c182130100d4055845981400e248029078600041003114411600d4031403100007100c6c00500e501960704850009400640580700400a00014074018040c0002d03500120348207600ca0720306500c00024117020310780600c0c1010b49666443e0342c60642015000382600100c3c000040e4642000300104010300c0d001100d410b135a403818007074010009100c003030340076941e541c1c0041c841d03040006000f440004500b0031200b041100200090080106140009120f5000c1240380f02054040040c1c00141030018000030302419840d607054211401c13800d803911a00b80600504245c4442101a60304589050711003610b03c00441c4001001000510402540249001219140d0800000c1c510340d5034040185040c1c0303c940c43e07001e03420020085200b4194010420f900045a50074841c0c10541654822100402d48c941c54000142e80030000c09003004007000e01c4c00316010000703c000069050020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 436859397 1250 436858147 436858151
    0x1c020f030d0f090b0406060e072c0102031614070819120509060406050702120304081209060d020f0a03060501180e04140105150103050108061017032703010f 69
    0x415148400e4a0307005444920640c070340d0780c0c0c45195a0040341d4200380040d55000400f50308031301c1c0c14500320f0018503543c01205000e0701c42d0b50019245274001c011907080303040c6998a0980004403011204400301c506802141180002e01030100018884060010002e00c0f680c1c400815a188401d16864440d0f240d2203080203910298050701c1d0204400202c01016422001d540e6200c605040150f40038800c2c110015040f440000300020350a600402408216100315010205040e00121140e80d902a9010340005500503008104c9100319020007880309800240c041800e1031640d0900004030b0700030504040d02c150000440711042d030341c503100c0c0101804007401c021444007560110080300c131007240035950681c44000c7c0810144001c158004151505280003030201e0b00d802202c00540703031900e003411400700b0300f07220000c1402000031691070302c2481c000642c01d44045ca00716045400d00459074010402d0301041040203054007200c0310b04000304d0350715180504d44408640501d42107842500395081c100e8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 436860647 1250 436859397 436859413
    0x31b18010e0f090115030308070210060506191206060320070c06050721120609020708030412200303040c0905090618030408060109050108070b030705160303060312021c02 75
    0x29140707400c1180c201d449098149a01c0d550152880c2c010498a00c000e403c0e84c040c0f0500008041c0c2c070421041c407510003542980c40c83c000500d818000d58006004c0d26a1284081c0008602400e0110345c0041000043c80d06224000c480880942100c026800c41000a5220342d2812096111400e00c400b803005580e66540c90425030b91101082d14150b4028081009000115541030086c00229911980311031420707040500e520b41405848407440780e071101c010394145000050809494030070b03036000680111107030b45596556541c560062080250700c03801e006070300c15100c3c0d200800030b42c10f0100d002014011030340e134141803c014105c058140e11642a444c00c00042104113240401c071590803100c0b81081c51103080741c0301115421401a90403d80c2c60b486140000203a2802c00d80110f0304030b42e4800e09691040d42c5030296041c0c80e02c0111402400324000b00296030103039030307001381d8400320600034980041c0c0562a40e948403410900c0c07018807001a4420741503601401c600d6143e20000380d00b40e00040c1035030303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 436861897 1250 436860647 436860659
    0x905030a0f0b04172b200a0c0506010308040801151d0c1c1d1507120f090b24030a060f180c0315020301061b11031b1801 53
    0x5840a071002051007250001080400c440d261070f80c4550000c45008036280c0c4948001082d201d040d603801d44407600240030307585011114500c1811114992100307107404060310340c0840c400c1a03100105c9441000303100030a00780491424008203000c0c0d1302ca51080e940e00c52030040c045007502c00140030310a40a082ea0f804200003802e00914044003e800810140c40e9900e100800d1107901502013100d4020340500c82c060382e030744203a40c0091403800740032002c0111503034003180440d560458440001040e40c2c00d00041540b150041c501501c0b5442c40303401c00305103484101c4404050311140c0b4400c844140010051000c481240459031905030140700815516044034000246d44020401028203141d54440180718241000d0b0820390f004948c40242c0011481c1300e181120382084284030580d00251019030031401c4c1141402104d040340d00d41d035228061400c1813260750034044110241216110b0880601541548042c000c120f20200ea0b84081c14010071710400b804032002502034124106010b200c014045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 436863147 1250 436861897 436861913
    0x9030d1d04020f0c061b0a111509010c02070e100608040611161109070206070e040b1f02060a0e0601151106101401020a02060f03220602131e060e010e13050402010905030a 75
    0x4c0340d400d034600100094001605142009c0c100100b4901065a920800840001c150041884131f0300300d030300b182c0fa5a40d440b031001458080c10f842ca024a42100c000c1000b40b00c1c8142d0009401a0080c01d00081000018000d8101d5a20800a00081c0c9800700400c2c41440301006034861000e90035601c403649071901c990002c1d140d0f0030040a840a00c0044030141f001c64499034080d20b101d000203050f4036a682c1c8070007044450a017020804400501c1030200280241015000746c0c0d0f00da820380ca0042120341d00b400480062030300ca142d00c20040002c43c1c0c1c000540c4200408c00d00780a20fa0300c820146885003000322003806403400303914140c1594400701c04540143c031a00e044508410180c0c00d816100d03104c0140f18280200001c400c44084082c00140400b4406c699004100c2c02c0c2d000201411a03035680c45298a02c081c6000b0424400354501d0340422884e8001c080c611050070051602040e4440c0e02000181810710343c4103034203c0c503540d0f00200f004658200b0003107009008220000d1030748071311654840c44c7e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 436864397 1250 436863147 436863157
    0x50a020601031509050a060e0d090f050d031412070e040605030a110a12060c0207050a06050a23040b09030c030a0209130f061b0306060509030d1d04020f0c061b 70
    0x460f9903240e0030440491034043e40400381c40e5901c002900d20b00080d505200d005400c0181e1b80d01c11070f0040c0746040396400e01900481040381da44200855009140108000400c040318500742e0a100c042501c0d0180b10300030380c0003449403002500c030300710b824248810001c10f40b4026003460f81c0034030728001c011700142e60001002001c0540c404165040d003186100801c00454882c0d10500442001a080d20100311081e04032000180f01d9074200d500707035555001041003414442c440c520200f1020080e5480d058805c0e02004250816801c4210a44c810141c4034400c9134050340c0700101c202d070041804c031500e10f024404007828074030840c000c001320465034001450240018054031245085600014200300c0002036292680b0381010342000b004040c02d410584051940003004006494008041086030090080c1c4001180150081490904d0504180c4080b000400c4d0b0040b0f41401090003000d0f6034603130000700b0741c4864001c0855102c3ca8400009441d003240504801210350310301250b0003504c003006050320 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 436865647 1250 436864397 436864403
    0x6032803080c0a090b07170304030203121609031101021e1e0609030f0a020a0507060504030b060306040b0a091b0602070314030a05070816150614090415050c0d020403030e040606050a02060103 84
    0x1035510101c5103045100f980300300d051f845070040084100405d060b004409817500c00300307084107030b0f415948507025501c0107820403a528001c99103900c0c041c80800c41c0d580c001c03c0201410b0044074401404c0e403c2a85e00c03194001403000c180c0d408404203a04480c2141c5042c0c4c121a1100001c0000e170500054a036180d01603548641011000454a040ea05100708044142c05030032038291102161100704c014410390160105903040803048001c207900781000240705202c1c0d038004820388415210700c100c11018202034001a10459901200030401c6c20130100b0810003480150002e0403403030b1075490321000c0d51000303c01450a46d00140001145541c1080840355810340c05011142e489075542c403880b0b580740c1c4000d00640748450035100881d800711140e1020302954030384071600191f100b03001c0401400481c110380080c0f60f0400e103400701804411580085800030f079003160b001d0600b03031811038060890700164002d0b000106040000c0107941004c3c8607901c003414aa29086d0302d00181a08040e68a4106220007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 436866897 1250 436865647 436865669
    0xc0e0109030c0b130e072d170604090b090d11120a0f1205040c0906050a050d0b0c0f03040b04020405060d0f0314131202100e0d03030506032803080c0a09 67
    0x950344500000c6201001e80000ea64500403801c010a00a0800d8046c20600c084500100001001d4000c0d20000a00b00141f603520a030390b003404450012801ca601078401d40c0c00a03150011000000e20031400f0741d200f854600c0040115501c0da450050882408405490a541010020890b80c3c0c110300100c2d18500018282000c00b01891041201d042c401d1317505901c0b9583c588418803041110900c50070f003c0b20021001072004540310390070008640110311406901001c42c502840006199449441c1d0140030619001d080540d514803131205507004031001c4503550083c600300300840c0fa1600c615904140d0a6a00318030910442c0e680482c1400080d4016080c031a01130440500701e60880c0c215150351011008203000150342c0ca404680d090f03038189007284155120740d010099148194000440210020082880515952000c2c2c1c003c11024001d00c0c0c050190b221007401032a2440c80841b80c41400f000003080c00b6a00e4200200711400251005007501800c10000031030aa00440d0700044c2c403820000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 436868147 1250 436866897 436866907
    0x18061a090f0c0a09030c060c02041521050a0803040c0f0b040302220b10020f0106080102071110030207020d0b1909050601060f0e12032d0a2609010c0e0109030c0b 71
    0x1d48121540f5400240300c8000b800001c148a540021200c803940d1080d10140102e515601600382807048501a078410701c800335944940c44904110109151801401a5000c11a444e11209640e0748220b03010748030000603078020003108074140e9400f00106038160340d807401e190650703000551504c89911000c01d20510800c0074492954968004100c518006003e802c1800031001c0285d00c9401090061140394a030180005100c030045c021140b00c01e40c0401c005056250180810220240c5c8004403000c0581c2400103200503102c01c540070405501aa1002115103040c00d03040c0c440c030201c42c00503007a0b107040c01050000070301c001849505451880c10806014642c006c1d080b5050203843d00c01c158003100313030000c20000500104c0103003070303d07050604103204e0806170b494000007003448545602c0ca07801d4100700558046109441e00080c591440340d4054a40d40141c100744144c182c244d030301c2060369643c1c00e40d144a103500f0040001a031842805c003100d0300742c07030f5440d510741110292194201c01540064 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 436869397 1250 436868147 436868167
    0x305060d060b031903080702150f04060507021e0703171216050f07060c0e0109061202090a05041a0102010f0603050a020906031c08100512060a0e0118061a090f0c 71
    0x304035100d0035030704400d00e044122805d0050400500351224400340c050305074081c03030130864646c00d60f02c5014203030307040d4409845a56452300182801885142103014035001c404188200c6c40321080c5060301c420050081070b003182400907a2440c0c00154029005040084910a032042902d06902075140c1c0c5d00b41302802222403050707800d8801c100c04540c1850000403a54100700259000048007400e954424000d84503100064410100d18040c1c840840e1010a080314190707159001040264006019045895500d01c080b4040d038031a900c0303030b850902d01028040f046590911644601484000052282c80d155444ea95111456240081d00442100001910544080060098594004d01c00411011040100509214054070b00070345d221142e4a0001350341c58010380041c05220014007425154503034100f14002007103804d101c00b21703035520741d210140042850011452000c1c02400c020030b001621620707501c83ca00b03280c0302031031040c0e1100062102c01d600d11b00b02c807030340400c1c4120126a22080f082e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 436870503 1106 436869397 436869403
    0x90203040209040f051f0c0f0e011205100317210f06040b0112050702071719150b06030117010e15061329030d0305060d060b03 56
    0x10b0104000c80d40344401d5003845407140003142c1115503090310520026410f001000c00081c2e80d5220380076a1381d0094213050111440340307002c270320524207040043e040c90003403421072806c56079810000300c1611031500600f0207141c010502c115034545618800c00c4560000603144172020444100c1e40c00030003140000341c01010f150010301da00d96528414040100010180a0704004850203d02d40700081c034030500d8024485980504103550030440445860000900b440000d940032590840c81481d10507201000075074007002010040c04500c6101e00a0800c0c5600140c4c0400c0c00400041e0004130703005032400080111009000d52603007502015207450042980c8a0512840c000081883c5405801171041c044a8240040e0038090784207100c1c03280301036020848844916008201051038101b140c50b0180d88145001c0c04540b030704d5001b2a14041007410000c0c19140c40d4459004a55014 = true := by decide +kernel

theorem cover : BRFrame.Cov 436690647 436870503 := by
  have h0 := BRFrame.cov_init 436690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 436690647 ≤ n) (h2 : n < 436870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
