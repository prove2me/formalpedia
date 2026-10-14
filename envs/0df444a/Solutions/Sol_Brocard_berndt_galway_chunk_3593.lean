-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3593
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:06:52.080179+00:00
-- url     : https://prove2.me/submissions/c15a339a-ac69-4633-8ac4-af76ad2de014

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 646043165 ≤ n < 646223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 646044415 1250 646043165 646043207
    0x609042a0207050109051504120507030b0f0a0501120b0c09030f1515090412030b01030b040c090612020a020303131a0a0204031b03050c12280605151e01090f06 70
    0xc21945031200700c145200c0380f01e4607914503050a049c1c081000440d201c9080b02c462207044808800200050070941c03080d40c0a1030229100e19001200200365841039111001752480002030038082018504140c0c0d000b0200e0784295645c18101c0040791030221021241c407903902404507000e525908080c1100e00507046283c4003030b500c0c0c07100300c20400304040a840040c203d0304421052240240250040e80b62100141000607540f00c0072400726082d55100c0002e040000c0705142c0c18010035411200c21126072092820841c141016140003940c1da03c030151510452050f85403000081100c0102c034607010569460041c080782c100703008040c020350098001215103040703001600c803424161143c1801100d42210061110f400b441007402a0b5000ca212700c00d446000b400b000040750707000712001c440c99819250051f122820380782003c20454201900700e94101080f10240c41e59640e0305020301d851600781c954180e4032080c060005885601940d409040b21600400c0c00069168100e0640e100c0f5550803c401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 646045665 1250 646044415 646044419
    0x70905100207031b05060a0c0203070b03191b0c02092203050c0607020c06040306150e07090306050a0c0207030213020d060b0301090e06070206070509030109060219120b0609042a0207050109 83
    0x88004d01c8140607190700600c003440405403040c42660868400c1e80003609690740d00b5120607155401d607004680702d2440192100340701400c0032403441550587c2480c082050116a000038005105010f2203030082d01c9168480042002469860764540d11410b28521000080a00f4030307003d8041d4002d610385004a01885000407042c034004944501602c0b0011f080c14038003410f683e1890700030310a01100c0190f40443c01d2001c2050122040228003400a9032603003140700d8954505001a10001004510600e0138103031344442a40c0c00003031100550394101ea004148007100c000b9000207028917220f03141242c1c1044c1c000160fa1018800942c140d41307c0d004103011100d581500a07aa5882c10354240c00168070050019612a101c0c2c3c01420b2070341c80c014004541c50000d510390600b41d8001d03a2050300d00052500710003041c1d640003103001c0303081c000d03410080c00700310850000034145014402d005070295031030b0342c0c2e48640100607002c2da02403441e4130404020700c082e4503d0020f689054500076540400c0c2c4038840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 646046915 1250 646045665 646045703
    0x300a0b0118150f1e080a061d0711160306060513022a010e100605040b0d0f02010807030e160501180e0402060703050f1803010c05070f030807090510020703 68
    0x240096a40141e8184500c400100d0100ca2440074010f0b034004104440549007009910702800310440f0380c5554940445040c108000360885101e540314081c00540350407010245004131450540c0664035003414407206c2c848105484c101030702044588400c00642101000700083da0b800321003512030955450603108582e0551808a1190200d14403a0300c100e2010998010039903000041d6a200f10000820100c00d128030316480d00440300040c59040b511440702340303c9420075208d4814a110f045070f94162140d5140c41d5509030f1202801c0190401c02d4010008807450b002c0d4004109034104902202d58103401c690728001d8030100d601503540080c0030301040d00c22741c04145a2040503150b401c60540c1440e1255401c100056101642c220284071060005030101285100a41002e80310100913100400c2013404043c01c41700d15680e5401030003004e00c040c1022072800192440c80c0c07540342c2008551600c07442c4055544600c9030307010b2544521599001400f055011a552045a00c1804500250f07060828 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 646048165 1250 646046915 646046957
    0x29040f0506010b1c0c0504050a0306020301080c03070518040f2001031103091b0a030606081b030303070c081c020301061812030c03081b07030f0809010908300a0b01 72
    0x248103050004512200c401550301c17071600c128580c14000d1070603031b545003c0744908000e50b009880d01540032004214860f0203001c41800c00740218040d00040d801e0100107040405488400d018502030b0100140400c0001d42c0f5681e00b5a40005411103407100100d54a407182c1c0d10804000e0009090000241c001490a0103413030044070070002500c1c1408403002c4460000103a9403205070301080404001000c621184541c3c0040e0040001600000d4058002d400d0154112412580280c3c0208100120305900241000201c0c2d4044040c55a804030b01c0e904056016000e01001f0046200000006010b90001609040e002024261001c1d45139500c102454481600101030041039203030b200c0d0400a803142d103169900c002070001038245504581004807242e04500300440210b210414a0003013a9000b0324019400100e00340240300840441ea1190114020041c9002035900300341c006a024030408104e1035190480003a030940c952a00c26400400b4000000602d40480d1484c55540c03400100d0407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 646049415 1250 646048165 646048177
    0x150c0c1203091c0f0515070801080c1315260c0d03050901020f071d011410030e07030602032d0c0a05090d051c0f0302070302070329040f0506010b 64
    0x800954180302e0100103200b10b801c20543c040c001c054100318000009002e11001620ba83e010308014400050400b550b019020320162144090154001c01001b05202c00210350400c0e07401079070b00c1c8148204440c00103018249006c964a403d0842800105460400d52044c401825074000d002840480c01103880b521051403080a50b00010794001800100340602c00030010007030184100c40700c51070046452400d0a401e0307000030100740d04045c1c1007108000c01c00c0d00b00780540781c17400618081c0b900d000006503151a0103040c10302071540311011440c101c10103210780001190482070555403032511188083c15204e1400800300c1c4246101d20b0f1030320549a1920071441456220b400781e252042e085000d075110b03002120302560200840a60400080e010701a0300c124034207500e0003203030041c03402d24040e00c0d5022810400b400c0620600103000420390010300c58044a410030020201200e0780c42c0c1c03952440180d8109021a4183c41060008010131441c049000c50b02482c242c1d44580d0321405006640c0c41a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 646050665 1250 646049415 646049449
    0x1303110a2d17070809030706030b031b031506031c020c1002010c020601061103070215120106081e04050304050a080f0105060303030f1810050903040302031c0c1e02150c0c 75
    0x12441645158041d00070034041e40901d04e09810964001c0000f13182c000d054101400103520760342a2002410104402c034002c0000c807000c940307050700c0c0310003103603039801d4000c0c01440718807200d00415110f03241808060b2044000742c080f031014010b04000a9503400401026500035400603060441c07103441840b500c40c080d0800e6010b881d4a034a03285080ba8009141000c10005000411082d801a80c030341e82d4411f100180c1c54561920352044d802e1030018500168401010f20082e50100b01c902c6a0308104241400804c0c6074180407a00c9a0802502e14082c503040244c0009481c200443c00010000c1e0003003020078550002e0056030b855200707041d221301003501c0005203000c0c0310780441d42242c420080140003440180446010451200805080c5d6001b5501078406030030019051081d82824060404041184071080f071300060040ea0080502c5082c0078050f1160307644200b0302960002700321950800d160024460b01c8d00d201204511855a40000380c0b950051040c511060f101d810704200c1c0c91b01c02849 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 646051915 1250 646050665 646050683
    0x3060c03010f060503181f1b020316080d05010605031807082d01050f01080d140d05061203043201350c0703081e1303110a2d 55
    0x10340311007913407690805811001009012016500e4a9a04115100d41c0703403001c1480b0450b008004c0c680600320b400d480760100b12240c02178019003a031a000400c64083d0b448075460841d94441c1c40c140b042a40c000c01100f403e11720304020000a480d54080d0103107018a8040c11000548404401015601d40003842104829040f01c401c804152074600d00c2c08030403440c0da201c00d0400820101099084400889142032104032031801404450020480e20002c1c1c90035047c01c507010032480f0080c60702030246c6020440340c9510307000010b03056107038030940800000d503a0007120344968540034403404031602e60b145803101031003607411020b04d43c18180d210440c0100684641e00c02902c1d040755130111030040c4500a4000c201c4903094501050081e420074808d210b0495201c0d02c0715840c4c68010030581c0060701014020b05c405180945c2c0301d001000c40d9402c4007070b00c200c0d6a4203140e41e140039508001c203000c06481e603001d0034500c1310074450051b80300c40b089100700c00100c243c440916106401d00316070f01400307040404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 646053165 1250 646051915 646051919
    0x3010509160b0310180e0d09081002180a09020705060f04020105030f0901060b0d0b0307090606090e060102070905070c1110300c020f0c04050606030f04030c2003060c03010f 76
    0x6200464024030654503001445444502022004120245945d140303590b8100914903280d0a000c5580c5051261811290031841d00c00380603079510303000c0d462000d80c96000440d8030080d03e0020100344140c0001d001100a0f5a6842111b0f00070b4202c01d80544460044000080d04846c25048091081354140c452a0a6449103040c80903500ba005016201c1503586150110719508207101408440220410100304011600141418640c01b039100030314032410038105001aa030410307250700030740704510f4002000f40d98140040f881c2080c0b42e48441a014500814001400c1c1c0c482e60111490f40a103040007040c501c8002030021400c882d01580b4000340c0c0c002070364080d800789000700700102822400e204501e030101064540c12105150680380140e4014110407850300000d0000f0960117034100c0f02000f1034901880490410712004003041085006a400502094060b8000c03522881c1c0110403044081c541411140b120421540613511920031000050400c482c5802128140c4000325400c00d8528 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 646054415 1250 646053165 646053179
    0xa0810030201080106030509070504050903090a08280f080f090405100602030f1315091a0304020f060f070b0a0501050f0306090a02101205070504090c050a080412030b0409050106050301050916 84
    0x42400390104816029409002920f6070b0354cc007031a070091041c58003541e59400b6440400ca020309141d8400c8140750007020390180100d01c110016101c0c0c0f084080b000c03072130080c249000d200035076080748000c00784078020070316074800400c01d40a400d40c10030944040250340c5075030300700591206aa00c240001648100207640d9004220009494003000c1c410b82c0e0110035886803021500007031036a8402c8001a20280204000c1d98a0401c1000d41011244220b2850030107401052807504460785060251000103000170131030203103600f2603d17220b400142003103040c107040d0900301c040c1c88203100385482105440d50759103480c40c0200e2018040c17903c40000b482c41729401d0b401e05c00100000d51040091040650350305a540d409802020b205502c1c0c3d40d01e1643c0e80341042081412950020b0303180c0100311082c0182d100558000c10041c2e04550010b01a0171022403841045001c3c20000350000e402500b040c20310f204100303054120b4030035154114002d102507940d2000856540022030124503012060340d00c100720f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 646055665 1250 646054415 646054421
    0xc0d080a1a21030708040e060306010f03081909050405132001081f0b1b010614130f0608010e03030a0c1e2615010e03070b0f09060705120a081003020108010603 70
    0x55482c071000d40b420b081490700c3d500081e0700160300908001400b901040303001c0c42c0902c081409070100e00c100d00342c2541141c80e40380c00e501401802c0c0101046180e16607200b03c3c0208020001024020014003142c0342c0018645400e40c1c0e005021582d0003500321342035104c1444d81484094100041e503c0c2c1003295150384e0402009100546031042480e44401c012840020040090440482e0300c420000004500e207001c60031541d256200080c03035010391803d400140c1ea03400504005072248040450208440c6040300c00500c0b82c0c0c3d1000540c0e620380345440d103d080700403020354811500440100b001d44407104050b5070000d0450310b681c18903040580c00040c0b00b4040c0d58030686807a1030315050009030116074455004144141e413a11042c0c18041c41c405115a1700080400c42120240c0161841a10b000e82030f81031030046d0201881210404158440f07141c45d002d0660f01c01581150031a00d00f0007495a12003191341c402920070b40021500300000d0790010100c0c070801d0480740d040c0d5600046e603203840011002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 646056915 1250 646055665 646055719
    0xc1a01050f04020702040207171b0c01051605161502010e1603020108130f080405100e010806010e0324071d01020303150d0c030503040527060f0102030c0d080a1a 71
    0x111550901408d00812000610480040400c00242d90303a1040450030010080c0c00c805011800ea00001445401e40d91117000e881d151400740c414880304280c1c901d400c2d420084a603450034441c0711804000074040b6400c100104c0c0f0300c10560000c101c2d4640007030200d91203504a4889641d007004885041005501c41d04040761f0001052810311503451080d070300c02d5419600c680c0240c5240c080441c091103d403620003090034001c0700c1818000e9452420800103007444200503c224180401c43c800f04078540ca0130b020a0501c01c042e03505800001c903060008000400d001ea8000c4c000600c9140200c0c925080b44466004814050b0000c5007195140e481440c40746001150280e0800c028081400020703080030035a00c0510310604c09192254240010b11028010f01c4840001074a150341d001185a40341c0312101c2d0700101c060307030703071112714461000103074a1840350000e242c10328811241e070fa00026900c00545801503404031001d20010b1401c0c280010380c0b140a036045648002e00e0b8100e00318202c04c440c51821 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 646058165 1250 646056915 646056919
    0x4050304060c230a0606060206060d120c150c020c0a030b040611040b0a020a03030c03060b0f090328030e010302030403020303070c17040617010504110f090316060c1a01050f04020702 80
    0xc160880c43c0c40401c03111454038150003a070720003408801000140d000d10405001c00e80300500300e52420b500024458180f1007800b81000c02c1f01c0b441c20394a580702e616101c0c4001d80000381180c0490100010000514200540e4001409031040a8045240180907030040ba40c01c480310742240d85803612418000d0039541c0080c1e40c140300070000001c8401c0301a025140000058024000e5040a4140a4265240d802048003010324009040c007141c035000c001d8a601201848029440d400307007101003881c1c1416011200c02c0580c0c0364070800d168007a4004032013041c7d417280c1d0700d050782c002d0a040150b044e400217550090150300203000268000784210285c0d440b281c01089289043d40c507076000042325600035080350000170442c00c030010281c0d1030b00e050756005050644080000c90564030f4080c540e405554820401c1078000030364500166010442802c03008202ca00341d581842c0c0c0c42c4005400d08400752001c9600c00760b100101419510140c0b01c19042714000781030040700071a0541000020b6005480c120b07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 646059415 1250 646058165 646058183
    0x3050d020d180f05010b0f0a14040603141e030f03010e060a0b030c0909090d021c0302070c0b03071101050609071b0803090a0c080601030f02012615120604050304060c 73
    0x4a12940c0c0050ba1407103000702560511040300342001821364541c44076542c0580d039241810240780d02c6d00082a4111a0705821410b40b0201800000b0301520407075102a0400010580703a490301407000c2549001c030301030300c0c000350440891916159100e00424031100c01c442814001041810b20a8203103640c030400040c1149030480d1101410f42d142d41003501d0740300000b2004500a505403c102c102036800c40c2d0035400410a0b414081c800940d101c0c0c4001c0070700c1b24501d59840f813852440c000d805036402d05900805030100a80c40388041c0110750030445558000030444507450241030010f22445014800c041c2202c40140d40c0c03c08152040104d84400702c042000051504000c035041c03c0240d80100d01c18009000710054906006408a1040c0c110380e0fa41d41140c1c0040001800c0e02c80b004d1001c990a013000c20040350b280010103031101c403080038220075401d00c1e03007000b0151148420341403103e101100c00c0002c0301c42d0001c5280e42c4030405c07900282568002c10050054034015080f40c0d01c12485440c81c6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 646060665 1250 646059415 646059431
    0x218090309040e0606041104181e0f090303050109020909040b061306030b04020f01020601060e040b1c05150c0406090909020604030215070209010621111e032203050d020d 75
    0x80b9048908102d42109260805010b00c0060b16041c018017203401407a021050615041c800340e100c2188490076081e4065640303810f070900351050b541c640d503d4002ca11034100002044003020901415180c1d00c1100007901d02000441c030040c003482500d8680300042c06d05021a0b407195a00c10300d0207805401e0303da010303403112210344c00f005140c05804041e610070140307a10142054810f001c0c50700820318006041d13401800c01444480da110303110190421341282c01042500f00c2d040801c3c0400385070701c801c0201d0900c005802e81401000180c091181003100340b44441c669510b80d9040450140d030040c0d50000321016001c00c5441000e4100d11201d0307000420b160316081e600d50001d6201d003945480c5504a00d008076046041d458203441e4140101010f0070242100407203814070003141c5032020b000318001543c0700c103042500005102034444101d0440148040c0702c152090200d03250b0812910a1160140f42480001c030a001c204405c3d4216410744400f41000060007142001e07411520090f80f05982d02c1a903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 646061915 1250 646060665 646060669
    0x10c06061e050a0501030506030a2010051c0b0616060204050418122d120203010803071b0510110a050303040605070e0102060903030115110304060906020d020a0218090309 75
    0x94485005510007001003128a807400784401c2d41e0041d80200d0502d45032404001250b1400701d00c0c90340c415801204091030400700c041a1182c801c2030148150407a100e8800880b10903080300007490131451100032101d004005e905803c040c1c0e2041494103800100c00d0010034508040d880380702e0262031240030b0150034603807030b40040740445110b0740c0440c0c01b226910b5810801d2140007421200300704140d1801811012041840b81840c030303c4c900095604540382d0380500c2d0210f1040800400320035450304250750344d5039240c109035520b41040806032070085406036102000e5000c24107600442d44013501d8010302e02207441050700d8407035110403c1c0d4041d000d000c1c003100008005000840c07081e8840d510004840c102000010103030016038210078159840388040c040040400801d40b41100c03868220100b021030624003c503650482100314070064400807602140081c3c03c003420001761110b540c22a504000f014100720380e6914480300c082c0d00a0008084001102041d209040d803068141c8112494458aa40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 646063165 1250 646061915 646061939
    0x20a11030c0303040c14030a0b0a02070516081002071101030c0215010305100609090b040206160b010305242206090f06150602010614090a0b06040f1409070509010c0606 74
    0x104104103402c000b08000800201c0c0b9203040141603c511381030180b45c4401c02103640c2e68950000a411614a030000031407400da160100c4400552100546850448203940e118070070800b0300500c05035014000e8003c0003004a842980c5404c0c0d0000561520b07440c1e40b0005400a025a200203002c6008400da481c0101c2c055a50301802144038000400103810320011610480b11550400040307142814038040210f600c0442041e00140c04995190366000c0c04100c0e034400c049075800c01450840204000014040c01168502103010b4480e10656101c44010035124100b5046898180410380301b00d8a8440300440b03041c040382584101e400103000c2480d516051048603512908072001611071590710341c10509161f4100c0104444c1c0000d21959040c00b038401030002a1020b41401034406a000600184254111003020007018161039640c03500e44400003056149406078113000040c619105800b4100102e004d403180b0381690329541881d01080044554800e00401916840d84610001c00c00860341c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 646064415 1250 646063165 646063177
    0x6090a051c050d0e0109090614010f091205060610020c0d15090c090209041b0e0105070204020d0207030f111504060e07081204060212090607021203043222020a1103 72
    0x103112950401c10103030004104038525003010450724180a4200007444d94030300d195209c400d0074280303612411002c4004440c901e107250b010102d44100c543e200400e110b40820524000c00c02640c8101544505001c182c2c1d5941000000c41e402c44001c980c0080482c81c40303030701105101109000030400551a88440d0b520504039000201015800240b00751146401e116401e00c4451302c0d0914603140c0b60402024160303180414030507040c084002841011540c03168119514220032090071515008a418000e04440300400324102050750f00443c00c0c0c5080001403080761510103c0c040145035919641e51502402d1003d08501d040d110b0040d000c0390a1609100008003040322044464490b4544031b03000b482c0000300780030b00000c01c03000c21410180e031311140d045a20050301510142140340101c042c544c0303144901d5000c1100207200250b900150414030f940c51420b4001002884511480780041106510740c4010f0544142840300c01040d0301100c0f5000340007610150704140303821880c5038803202d00707543c481 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 646065665 1250 646064415 646064417
    0x303030708090607020d0f0f0c08030109060501080f0c09010c02040b121c1407030e06040e040b0f0c030906041e0506190617101104170d0e06090a051c050d 68
    0x1d4000c100581c04100030842d0701c054284001c1c400000c40000207080d840c082241c110810178140120100540544000c29100f50b20035541c41d940e40c0c0d258024001040507014a50000f00c42e4004a40c014000e902001d00a43d40405a40e15055130036005488140c1404000c0b40c1054695407401682c0da2648007441c98903a548000d041c074010f098480000095030036142000348840401030b649480a41010340388030b2a41414268031052485c0002202c3d03006660107013909160316020002005241110640120741c22401121280c6904184031668082200c2c0728401d584080b00007008110038058065041054a01e050030301e09031500d443d82001c000300c40400c807484c00000c41401c14000c0d0710554000b0300c010001d00e51701c0722400d0800f0341c07980040503400005175194101903000c00384140c11100142034040c0d140c41b00e01c2d04a104161520804500701020440d001074012103401c0c564200d454920004069004039070030f00b0100308000b821500384100c0021170303142d94800a41c1c01c01c82c0094581131 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 646066915 1250 646065665 646065677
    0xd0813030215070c14030a0b090a020307060e060702240c010203040b0109050603060123040e150106090b270306040b0a0501051005121b0406121107080f071103030307 73
    0x318018809030000c50400344003080c00401c90000420800c2e620341e4142d480d440c14129481002c00002441c01c440004e000d42a019000107000d5040400102d80c0300d0f240c400c0e07003641c1305a0783c0e07800c00340c81404c0d86e4401c0da0780040b400c2000e400149030045481c5c24440d9145011800440802807110700381d04030482c1c0c040c0c16035000060100740401e03240c12500501002e40c00340264540000440c0c0c4800d018440c155684c042c442171303c14603540c1d11426840e4580040c01c10083c1d0b80b540012107540d106000d12041c0c54034800c070000b0030040d22511940060303a40f0309048610f0014140c00b1400082111aa150a00e0b40505001d041c076036020b07c5814041c6020300940303120703410300342101c00c100c0d041a80070340c1c4504401c0c0a00f4200c581c12009581d80c010401d00c1204280d51a102945a01704000103043e0078210001b0300824201c0e00110701f0b0b18840540c1604201e0620504868241780c0b24030316000c3d00303610040c8204441c02c0103d06c0141903a5125905445054888001103461600180c5111000c0741c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 646068165 1250 646066915 646066919
    0xc0b1e0a050601090b19030b0415120312140a0f0605030d050702040e07030317010e01050d29010e011d01050d022407050105010518070f081003020a0305030a030c140301140d0813 78
    0x43c7c0350040c2d203001081180e0030841548024012203540a81d4460030040d0b010040700d500615001c2c91050161440e91030061102c50501e10000c84d4a16040f00e043e980a481c0600505404029115240540343c000c0c1c010a8070640304a005d80d010f410440c800c076070098031140481407000050010b80029442500c5080391059034100e148020b04050700404074803000c040c01000720b903131a403880781c4019030840356480490b9184180351441582a1100c0e9103201e07a04000001d16004166002e130489041c8071001e00e2210242464206901081c81107a40c84174001000102610346441550308030040170705c5032201d0995110801812ba00002c2056030745c0d0350b4a1004100504016074981c0c0c03c0c0400580b508024584081c02410000c0900d03e0042042209000200c40c0080d41d6020780145d900104a20501ca80e08d1030704994961000f052000003d0600460b80d0700c441c007400440082c20a05060b2500b0360707082010034001c0f026010b585a07440300c0c0d04405e103000318800d40000c1220078020305503451518 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 646069415 1250 646068165 646068167
    0xc17041b18050a11030f0c160f1103010507090503031c0b0d050c040f091e050c033403050327100e0127050103020304210c0b1e0a050601090b19 63
    0x8100301189846030390204104030350b4100085805600a422258a940f6640c07604554200c8c1405990000c169110b0560740c542840049880c141e00002d045009005640e20000c0880318200148107280e050342c414025101d8082c11900280e040c20315012000503003c11550000f424040c440380c042d2600c1e04010355544181c105401407004214207444188646a0190b0f90003000d030480d5403111031144516100380082210a1081c10003c0da0300804445d01801201000852040c1d604a1015030030182c543c10440ca40b608058001180c1d0002d000c0c50804200303400d04480040d480008060101c85941030441d10394a518050a00c00311701d94410058851010000d0912200080c120180c144190080504414020891070540d0020301e800f5850361207030303e468498011000b00c03100804050000d030190665002013040411400f40c2650b000301d0326125148410000006000e0110340900800140004d0158000c10b0300001e043c580300301c4d5555105034598a6400c1110101e900800c0b10352a10f60803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 646070665 1250 646069415 646069421
    0xf080a030f0506010903020d02040b040203011413060501140c070b0d1a0406080709090312020408010506100f17070e0a1e060203131e08031206040c17041b18050a 71
    0x1d4a50420090b80c146900041c240e880c0350b11000f0311410301449004115250341c0c2102c2100071010704150345035610b40d6000c601c400c0801515500580302d0b001008190202406104104d440c103845089903103620000441e440e502c842c044202600c6408000118655900002d010210300700030002928080c42034110100d00c4c11a801c01c3c419410440280407a04020131070104444800d04001645822440c058a030325a02d0008494240d20202e000034602c003040d004903100d804100d03048042580c0c89801a91180711b410603105c0000c1c90414184611105259500d0b00304280c0d0034103440250011001800b8080e003904803940b01d10030b0b401911414820480d0b110003a0001d40081c604007400082d8030f500d400014031078071010b1503240801c2c103083c40d00d80c21010090300b80503040e2030b0f0790010b0892881100340c0c03d0f1940c0d070056203400c4682d0b4000d84030f2060641007690050703600d1201e072100e454080d030110021003044e48410001c2e02c0003880d928440c1004030311080a071008601887c1008004d412 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 646071915 1250 646070665 646070681
    0x6030212060907171807091505010203031b03190213261209011e020318090f0a0c0509030102040602010b0916050d0e0a021810050a1505090d0f080a03 66
    0xa082c0b01810b015440c0e4006400300045100f0620300c12895450540c2c1441d820405000200709014918010620b004542c2004a0341c00340185001071896548004a940e4030040700e424200e84030001111120540c4c2c0300046800201c0158500141c04070500804103d81c80300d502c828461040c2101000441080c10b514005150a5580c07000c3e2043c0f84421070b40c86002a1021080910000031103041e0b2740c4c052000441b00c5030310410414401094103001079560390041c0040300b611614520300d0130340c501c4c140321042d100f08440c424031a40f581b682d011300310203001040e40c61003d100d410301006003a41c9003413001e0f0000700119800030450038a41c0d01808800c440181c440106480445900003c49400030110b5040000501c40041c01d604000009410807800c094025405890b81c5042c0b0050102c9400c818040c02d40f001220303400311380e64400c01102c5d4519115501c1c010001d03088008080780540e01800407004098560709250100da034400c0000070440b00115887c0324040342d060380440d031521900762 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 646073165 1250 646071915 646071919
    0x120a200c1e100504050f04050a0e2d010b010e040f0603060e0d08011703120403050409050a0b040e0d020606010e040f0e010c02100b180403120c020601050f0105030c120c0c03040603021206 82
    0x1162500700400300e1306c8a0781400304d45003c0c68071100800c402d1500d5501000005100e00c040e101c02c4603882182c2c400d100e070120810030703109103082c0b2a14409901840f41c1108500161034000a0103c044207110140040c0c52000ba041c50351307000c4c00000f02d0b41c01c1c016044d50300c4902000d82035185010101422000d0b040c2c02081c41c14940c0b484d0100420740001c101c88150400301d1100c84144c0c2c40d40b400b140d00b4804d61300700c001000d06000070300c64040030030b4104a51041e411102848030f5840f02d80c2d85651440e40106801c01039120b41c01088165004108044a040c00544003244034a01d01940d0000d49816203400c0c200c0341c0d91000100d042c6581800030000f0f03405000014001e0503170340000201005c48401182c440344c5550b0f8003003010540143d0207450706098034942803020380703031108010752215824840c06010307004a400d00c40031984124202d034414508503000c542402400142a00d0143c00240850420641008030b0101050200081c1000f05029030300582c3d030358020322802514106c0584854 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 646074415 1250 646073165 646073167
    0xf15050321030a0e07080d050a14030403080a0b03030717030106033c0e0d080108070f1a0a020307080c010204090f0b060712090512030309120a200c1e1005 68
    0x3100741c0140045a4204045140105444444080c0c06040a00a9010001c40c0c070481c281c00385820781160180940302c0498880c10039258074895682401d01c03084500600044210000070611107150f80b15550303440d0094100d0382070010554030407212880101c450b13502d0780d202200400806515014145000e2202c0740300b60b82500c00402580c400c980c02070b42c1c5242d0003006c079004c103580c0b4903154448100401c1c03020440302c0c42e00b91050050440c100a000d1100f250084031004500d110713000c00c07084210f030800421550704096010342c00c800d58110805510031804100040f00c0843c03000e82c0031b850100d0781c200006980c1d80c5802940000c454208801303042c0d86041258840c4560f03110780c19101c0003030300000d004007024110242201c0014060300842d5000c4103608110758481000400b4620848054044891061007050050b101f07003c1c403a0b2803000902101400c0e050301803000000c0c2141081c40341100c2119065a0001d240f8045040600080c503032600212816890006d0b4028150186403c0c11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 646075665 1250 646074415 646074463
    0x702060403080901051612031427071205070602060a0b09151201060b04030201031401120210092427051c0f030201141005010e01080a0f150503 63
    0x2190090040d80301c042c02000000c00c0400b001d034052003c41d40f0008040000070600480c0386010744000c00c0344c074942c0002034a03220003003481029000240c2d0150400d15148444048507954589551109420030f1100740543c650004194010304900d050961249005d0203885007002c000034506a00104a80c1403141080c0100543e0303152202101e03006076400320041385401000020600d510209120b200c019842e014000500142c81c00c05082503900c02d81e0240b0012110a0001c1503e0100b0f001e100750b02c144400e1030400600d001000310203000014280048807964413607046200810014030f103081c580036a4405580c00d0380c41003050301860410404481084003d1691014110590107000d0040c524008070500c410f82038107a08541943c46a2000c04000c85850001e01812809246404000020010402000202e0440b80c00d60340180c0d01d9640803101c4000442e48441d029008615080d80c2d20341d085580601c0340200070448601840f0402d11900e031206240c600005550030302c0e03032180502d50f5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 646076915 1250 646075665 646075669
    0x8010f1409060403090b0d0e100f1a06090d14010c08010513020a0f050c25050a0b03090a060f140405070e07020106080309061b250b0a0c023609060108030702 69
    0x5070302038811006c4c1003520741001620302d8008058040f1a182d507480341c40d40041d1a40c90603001400e000801d003c05000085041400e6a200010402180c0d0701c540140100c4019040003d51002c2c05030050807956941484950454211031070550300030700080c420740047c0554204154003400c0a03090310340441ca0240140d00052926408030000400c0000018020301e400b00100605d4040c8940c1c0e0303800d000300c50a40d0399000000c2c8203504c6050b0140490310310004010100409070f82c42400040081c1006400951780c07100142086a0900c503400c0d52545110b84421403600c0c44d512a500c55402005414201900006c4651000381048110380c101038061050f00804015208441d03015104551903005c0c001d004843c00101d1864210284070b8480030281c8003408407000050b070003440c40111000b43d1501c10018580c4120f002040104008035804001403c080340c46004140f080302d1040400c030955030700502200304a2002d0244100c18100380080710400b803200758010544080154900a01980 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 646078165 1250 646076915 646076927
    0x106050f01080604050c0f0a0909060518042a0e04030e09060a0626090304151e2d051201090c080606030a020d090f1a010f09021308010f1409060403 65
    0x3c9040d00898546000c2000c0b280000c1c02c1d207031360040340600c4030303200c0b059103000403ca0116031051010450a019000505003401c01c0c000506003100c086030b948a540d1a00d034a14103c04501e81c0005c0000d03100c2410210100c0340712108050850140c4c00787c820705150500034507074041e011001e4030540001044c08400d41c0d441d4808070458045040641481e000405141d00344507540c03000c00a0030900d10200414904044018400c0e14084214421621030000080340c0c1c40c0e034060f03c801e0b030741c42d605a5031844003800303003180f601c40a071a00300d4005a14450701101844001120800001c605c02041800629410084480c09403c1ea5401040340741d610300c800528003100900040d010348030000c00b0501c0c5c00c800b0740441d404c13941112414481803010f860540c4100c04260400c0d02d11505910f2141ea400c01c2d00b0740030a0484030842000032000b0b081a202070025800000d10840c0314188060000300c140080c000c801c40001c00ca5030000725034045079164484210020038440454010104200000307070440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 646079415 1250 646078165 646078171
    0x3030e0f03060a0e03121e01090e0304050f0f0406080120162a081006060f020d0e0a050d0b04170403030f0e120a0c060e06210901090c03060b030106050f0108 69
    0x121010840a4007980e8043c01c0d440f40d01ba0b0042400e14940c01c2016052030507440720302c20030100002c030030030360f07a1016400200e440d404448034603a0400c000400c13041c035000345000303c4101d0040c81c1c180410000e8000070101e82007070740030128603511015103400b11601c4c803808002801c480d402c05441d0201005050402403007104009220340031522644580c40c0c1d0070800c02c42514021408440020b4444c00303c1c943d2031035808510540350381400c01c04140307103220740311642c0c05d0000c94000301000310403180f081d5042c0443c1150590411643c1c00c001400f650768030154504980120300740030f41070400b4105400c403141c8461070003502c810104020800250b0010440842d0348103854880031420354200080d0702c0501001c00071a140c03213400c6428042c000d4111008045a0300381e1180c0b1a1940000c0034400c42c0e0003454000755100355800c02d001841408044016030101c0d1100000540511503074601c0d1500b285a0000d890341640c0e00c01c47c1d07440307040910520000d04403c8401032080c28542c00000e226001c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 646080665 1250 646079415 646079431
    0xc0b0103020621040b06130b0117041401110304050c24070c0b0f0315010f120e03040f0605041805010e04110d02060d0903170103030921060606080103030e0f0306 71
    0xd51401080240f8111801e070036204414185142028205001d00c80000d4803014450b03840c00c00540001c204922462a0b121410384505111044158a00c1c0c454400184162030f004000c161811440c5001c5c80b526440c101c00203032203512801d05050451a04072681c51050058100718560400500d040c2e0015140511200b8100d83e1000d041c40d107219074114640c041c081c1480080b501605e484481009144103110000d40090443c044000440398030b0095400740010900e680e5200d01c4002d07840e0460b09412003090101c03460241e0b185180c0d003c0100d80e9004900142c008035003030180c4402003c40780c0c015185032070706101d42d50402848245602d4043c0009104001004c400e00c00794035000411070007240c00400890304d51031081c06180103402c130250110001034900402c40f1851210300e038500d05803600b581e2019039441c02c2c008060482c03042c03000300030100526644540300255031400790601624641d81c5080d0907500d1442e028001c21044141d00703125030420355003454281c03000200f0a2303000f07440c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 646081915 1250 646080665 646080667
    0x10020307020a0b1602150c2104060e0a02090703090201051e19020f0309040b032a03010b060309190f081c270204050c040902030a1a03060c04031b151205070c0b01030206 74
    0x16840000b407540c0309035150713991100c110102448e03006110110040c40765000d8a000d0001c0030302d00c0040c1d07488602c100c0c4000e41c4249003c020400f880d200f98001099244181019403810810000d07400b185100001c51410040c030020f1040302600c4004160b45200456000030b260b8100003403020380e10f0380203180040d0b01903076071081c000d862680d0802074141e0140684006801c05002580c26440910800390002c1c025801c02d26100000d00f0b010044a05c00c52642024004035030b03269240441c00c0c1400380d000d8669042c000078036008580034000801d810003400340ca650094001240c03960030395616514038050519003a6103c0111012802e99800b402d47c11900003c4a5032118a180414051500400c8600e0b1000c001c020300ba0800c1da01c15000040030f068405040300c0b101c400c240c0d403068103c407948414002400f080000400c03051a0b4200717945000c03110a101030719048080000e10086480030700040d425050340b520181e03180305a075000f002d20314000c1503160458551442c0001d040c03000070701804c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 646083165 1250 646081915 646081921
    0x403152f0906040324150303050304020d081209010510090608061b0d09050f0106050301060620071518080c0a03081309150f0609140f0310020307020a0b160215 70
    0xa90001142c000d1540104003c0c808030201e40e848602e1205d074040b130048540303424030054441c82c0341c0480e042200d906035545850341d40c40c0c0d030034030107040c1c0aa04219038461043c40808440c8891401c05e51081d04400c1c0009181c1c500385145049a0801d584a0782d0003514000041c800ca41700408c0d00b07a403210b18440d4051041c1440c0414101d1031040c13404401c0b6181c83c0405540070018042404490010094020b0000584403030070542265000c0c42a24080380f458240b050760540b070450380100c800401320030340341c116507940d100d00321841802d685e03580028a00328400d240c0c1da00703000450300130300603080c0200362010706c4170f0109186036000e02000d007540074085101101e9554807400d10001d8280307518180310424482c45d4901d0341c0c2c10340d4020b40b0308498180d000401c605110780400412a0100318404080612840a20188000401c401074160081141c01600c451880c00214000d890076401841d40315014102203c0b801e50190400c080001a000003611980d4001400040b03000780c04c02640d5035032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 646084415 1250 646083165 646083169
    0x53009010503060127081c05030402011b05030703080105091006051b0c120f15061f051314013c0203070507060203030105010e0d1203021e0403152f09 66
    0x481400c015080c8058140c0070340010480b0801e8034400c540c0c1c548100c60500d00d00c0c1f02610142d1507241d0302d6800080301407001502541c8101c3c1c400e000c1001d4840c0c003106048594031103a06550104400b5000f0842041c010403582c10400d94056000071f2141070010010304100000703200d882964080c503130420b1949031003410f010043c0840e1585050083c98210310900005840b034030390499144440343c0e809440c0c0342071190b4642c8040584544ca0040160b0025003070b002004081c42d0f000c1d8401000c20030284850711480859000c07800107810030401003500340314031000060200703280e405440305002d000e10480c8000100c03030540003a1002c8072141ca0f040c0c0040d0340310880c954010340c02c0180003880341e40780004c0e42c0d640210045050340c10030b0b0388140c1e81d5010301003480341101002c9401041c8070031800c4031002c018801e60141000700458411040310140c402182c041d5078000d0b400617a1100601050340c000c283d500c0c460095080322100030302141e20304076905000160f140c0c0c0b881d0100c500000900514a03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 646085665 1250 646084415 646084427
    0x50a0303051801060e0604060f03050a080d0f02030703060f1d13030c050a03030b030c06030c0d1505040e0705030d0314040f02040f050f090c010207140411070503070530090105030601 80
    0x3420b0140000c0242568076407102441316000d480c040e00503480c1060200d485410350b42c0400640c1c0e0480d004100d60401a175a0103003640c001a103076159030303590b5030744411048500c0c0005e6000d820030ba507012450381e04020030302c02800355550021a269032051000140d00544000450380f01c0d020081c6003140491900b015140b003482d540004059000b082c00300d0080581560082080b4042031342100c50381500e4200b849101d101c287e400342d20301c0c1c5050200c40038505d0030740c00c01c04c548400c2440242c003c5503600d01203800d0f503031030f20858021604000028495402c00f0030041d13649811170700e8180b114150301104248100405800941403c02c3c0c3c5001005548490300200c09801103148100007900c2e10a055500104059070940f00500840d40b010301558800142ca1050702d5155106503100c40c64030b030400008250420000c20320744014002c003004140700f400075001e1280100060280b2405049480c101c4414001503140321000e09d0f11552000322050781070b5070b4040d03828207225940741c03100c400580d11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 646086915 1250 646085665 646085701
    0x1e010906020105190e0109171905040b03130f050d02030c0f062a16080301080c0f0306071d060f090a090204080616030b030a030905040f09120516170a120207050a030305 74
    0x1264000058580307070100500300278100b40700101c40c0b4000c203810040e0100d802e48a148181c00c039106041c80810010640322451905d441c0c0f069810403080f016541d68035081024928410000da0404039010400348001d100c5000000c68200c0900700c146858559500705a9030240f00c69181c04141401086d00d2031380c90120351310135164145015404c1000d240944441d4824011b008840c05038a801d42c58904290303914400000c03004001d040140d5403240c04aa0007455850390601d542e420210800040e114040140307a00180480f205590b829030740e081c00040495640402d441034810401048003200110f000d40d04454822404039a04100d401c0c11006400000c910315814082c0d29003070317802c0540000508041720801c1d80d0030b000d000115400c80d4120b40c507100000e44a00034410282480324800c07401400c1c54a0420074414ac104140e0b1182c0c044900085010b210960ac009072041100b40c005240d04500b4014241c154508103541d980c95490b000f071a48000d050589660100d1842e00c1c401200c0d86e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 646088165 1250 646086915 646086923
    0x10050f0409060b1315080114030304260c12060103030e010e100806030d0507020a03081e1602030c0a081f0b1e0f03120f030408091e010906020105190e0109 68
    0x4012501d44103d0850341c0d00a40445620400c603000005a142c91001002e0310000b5940343c46000d6840c0a920300000e04002c41d02e0340c3e05000c204008140400e2050031645142041102c40d001342c1100700c451450040035105c85031142d005600721513029000003400c1415a5454605903074040005c00050310441c04150b0380590041e0148840210140d000510500c1840308030300b102c00400c1010402d444910401e00c0194202010800c18404075000303500410079401d401c50992148114043c42c00c0c001d0b0030142d0200d40000504002e41c043d841d0410800f00d80240071924010140d103400201d640e01d01c038044241e90080380942c005522101160b101c102c1040c0c001e071004078240c5034a00b2002d45020191809803041d0810800024113041c002010303c404824100541e140410500b00c540c802d0b000104100e508003010048480780352a1103d88050001c05d804100840343d0f1900000340440c51780703070401c40c04c5a15240030003100c9040a030213a08804600e813400140000540c080c14098515804050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 646089415 1250 646088165 646088171
    0x9011404060f030b04050709030b0415150806011e060e01020c03030d0c1407030c0312091505181b1009091103010302032109130b10080a1a10050f0409 66
    0x605541042c01d0700086881d40c1e40c01c1220f0126101080112807003500c1c241c0018102130828400942d400c03042c1600540a03503065a025040c1c0d616880990300907141010050301d078010f04002220040141d0760150211460541003104003c60550b94034005100d49070820482405480040e4000c0c812840f8196028091300c0e650894071440d82e018050325503015000891a2468504500408050350a034550659401c200800c240e01c049800c402c0005449403525a00c0f41c207640041e0819000f0109042080c0380803405240001c04144d2251107510440b502e50030100c48400c103040104842d00f504c0c0002c50b1030282e1824580411502c6651603081007090614000002d400340c0e580c20090340c101d91003242111403481840d006d4556207880d000c10450303a0ba2041c8442140c03032802d900c0c02c201c0c1c10000c060000c0c0d801d07001e80000b00c07200040b048650120f0f842000740420070f4050302402806c06107100189031a290505c000c142030408400b0142d0030407030042507103e51909000c1c1100c005200c100014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 646090665 1250 646089415 646089419
    0x270c090609042303130e04020d1202120c07140108190e0a02131401060c08030112020103090209070905092a030a020702031c0206181c021606030504050c1c030509011404 74
    0x203070744c0c0c80d4400c0d0440903500c0e2040100250800000340c1285c40b899002d030912030808010f503110000720400103028425801100a031b0404641180050405260b20a0003040403600c1c01c0e051400000b00044030504010021041013204c40d402d03016007000200384000020601401c00390142402c81d0400001d41c8022909100803803010b09401585841290140c0382c04980d903541001d0303640d007a0440000b000b080040c0010003110310710201811a25006043c003164aa0859000518500c1e0131505100400c40c215800c2c01582003504184d0360000c1d0f00742442520080b81194a5015603440c0c0c4da0392180b880000000d26000100d4054403540c3da40030302116007010b00c0d02240c0c0c0c0350103410003040740184640c100044600f0440341e034105028030000d0151151b00380000c40075506040b4180010150702c20340e07112002450024072101c00500140c5e400045605040c41c08604242c030010030144102d80507034400c196004202c0043c0c103050b0b41410540da43c1c000060050722440302c0340d144181480e40100340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 646091915 1250 646090665 646090733
    0x6100c0f110415080d11210403080a1d120a060b060403020d03021b0904020d03110133080a03053a0504060e0105010f0b0a09050603270c09060904 64
    0x1c03003000e030f03000302c4280c175000810280216029002e68448421541c00400900f841800b404c0c40010552407100000d89001d480e9143c00c0e180c0c4d403280000c800080c4040308540e000680602480392072901c200c4038501682c80900300b0952710002440c029054554420b404800c60307547c0c1d400c9400841c0d000e00303101500d0029040194682c44000b4050200c00054554581c076460b288041c584510350091140079485015102155000415070701100e90750341c4c524400000c02030044084201c004c4c11040200241d412500b044460a1242d100e00060b6100820703020010ba00202600c401c1c4854400401c002d101200c000c0300b400c100780b00213a0000c41c481c3c1200c0d40e03410103030300000e208134020f0201f80301c0c54000500c214200ca10034812041d04100303880d402e010504140e8020401180b162805c464041c1c1c0b0341c000184140e0041c1c440e071864064054a45031012402c000d440c0e000410000509502100200818004000240301c50721a00d1103c002400700045450702c5426042c090a5085a055102803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 646093165 1250 646091915 646091951
    0x6020d1419030e0601170304030803060303090306040b0711161a041d0114100e01030b010201090203011b030e0312010306020d0e01021804050606041406030402010207080a050d0806100c0f1104 84
    0xc01d00f0058021040040341c1e5030150940c680e00403003140011803510349580c03101000d5030400b424207945404100003450f026070b01004924005d60191428079242e042c200303005046840005001e160580000c01c50981c0035400400e20710848001c2103064210a80491501410748500c0e040f00d091803128452076219266022030b854141c4a41e05540071000d00c950041280c40c805038030442e4006050803c945800754465001803d020a040c0004036110065a0019007502c1c900800c031050090805c5000b00da40b503241c0140340001d40303000061403601145240513502c14005000181c0010f030005140100d0540c21307401a07110b2003003200210745032884100c0440b030360350b8500003a074403480c140800314241c2c0c900841118100c5001401a000c0301d110003050040e250030040050303044d07024155000030004024080f8800d0144580046d0080399a0444003078020000544001e000b00f520041c035500f582d03000310a002103140c2000240000311440d20b0000c415840500f04c054219040120a04200c08090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 646094415 1250 646093165 646093181
    0xc07060e030c0406082505030a050c0f061215030a0818040b0105030601093b09060901060506030105190b0a02030d0b0405220611070819020706020d141903 68
    0x202601d00d2030b450441007000340c400038083c2c500e468008030940f00d1041c45040c211200f205d180d40c0c00e440700c0b660300c0e070000e410b01400781026a5540c02c0b204010320309161a03114105c403c0401c031052410310701c440005940d450b9000300b102000c403485100103600e55030100610380110b540001d80c10780c0c031100d07500040010030041101501443c02e00580c4405980900e056a202d4001a9550070240707251203c601d196004440d0502c80042a0b0318080e06d0380e600320040b400d01038800d44412a0541442c000980c9010300c001d04c1803409901d050400e010700da4540d01100d0468000301c1e600d1000c0350000f001c003113a10390349600c904440340c0c0001d01c1d4140d20750048058101c032024100301300b014841004c10b1109480e4215400c50201c4180744c1541c6069400d03040c03071040d1074051800042e0070110f4200700c0c0d0413640301501c244d80304a004208045079651405d40d08117400814070282001c14580213000e580e604800007800180a0026500e241064060055030050031840d103480c0780e00407403410040d00500e030311 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 646095665 1250 646094415 646094419
    0x6150501110a03082202102001060602060403050d0e0105010618061713210c0c0b09030615030109080d0c0305010b0c1f0b090f0f0601210c050c07060e 66
    0x2008103640701140108801d0342c1980c05841311681580c92a4002c8813502c10720000072688044240c200b000742c4c8a2821040c00001a41c0351080c003065241c00540c0c6404141110169680c103100c01800101c1c0d01195070750700300e81e050610b940c80d03105141d8040081c0803080758407070066282000006040e94080b408103500d240303000c00d03100d2407511034038100d642d0107100e4240036184980d000440c114104032100005014082e145e0481340002a2405042500c560031403c4006103c0a120070f09114810300b50360000c0c050014000d15002400002c40e458040062030005250b000c070381d8880305920700703404c800c099641c4840c0b003660307500c170100c1858001c04c0c5541303414001a00e4103002090759030000d41101c041e1071000005100149010110502c42d40307110b01210115a1142116a141c2e00c0300690315018030120038100f41c041c139010311170030102d12005003891304208080601305581c2c650514490610500c540000c1003c1c95910015121407041640990b1b840c07080400010740f00b540198841006401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 646096915 1250 646095665 646095677
    0xb03010216120203040e010e0c0c030a020106081c1b02040b150d0b01090f09050a27110105040f030f0215120403020c0904021e12030d06090b04050103050712050a06150501 75
    0x902c0c500f00e907603003c0d6002e040030000c4200d0041c015a10b14411180e8080781c8e041190f494140002d1102d0b0650300581001c00150391600c02c2442038080034030012880ca19050005007287d00400d0005100c043d401c19179900110401c0b08500035900c0d140c10580700690701034000c00c00c04110401c0c9c82e02c036501110b81c11150307610b4034003001407075031250343c16504881000100ca00d020782000040300c014400074120b0010300750703a42104a4104c0c0109004a06034403001e11880c0c284603141000410340402c200c003e0704002c810003090007924001c2c5902003c0e07030b8103e481075001c603026101090451980b044c01007400703072011815420088580800c01c0c42148a43d0965026100d80004d121000800340d0b0002c0d800b10301c0501c1c2c954929a0303d5054001c0407401016030099000c03001243d811940700303182ca2846180c03141428030401003240580e010b5074030203072030400096165858043d01c44240b40605d2110b103085054000501074100b1900410076041034040100b034102d42900c1118030040d106031804249 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 646098165 1250 646096915 646096943
    0x48010c0614151e010507120315030804091d06160512010b040f0906030f03030b1809100e06060d1b0b0c0d08011e030209190f020c06010b0f07080307030b03010216 71
    0x214103007012800303c0180c64142c2424503a65402d44c1c84850804500304041d036407131080020b100c403104400300646c0600309981da40e80c10b11143c0e0701628000080400d8041042c50303484400a400600c09620018002c90900107008030f9104480e248940e0a03038418800302c020002c00e005002c03000400899071307016444102141d807544640c4c10b6409502c4080d024115858400c80407038000d4210407085031004020b808441011200c40810a40640e42550f40d0742c030908501c490700880d4491100f00044120041c03856140c08000540a0300c03060b403000740594590300c20145510f003480c035204041c0c0354082156803075091650f10940d4860000520390700090703400d00005000202c00c1115803299545084102ca507500755001d01c94140070103004100c0e081031400c29415042014498400c1d084544040503030344180c402c8001e80340c450182c00403a09000200709841021442608541c9811ba02212942d2030b5900c01d50103500600180c091650194000100a012810012501d44c0050320400020030071407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 646099415 1250 646098165 646098199
    0x601020a080c010c0e0907090b090a121a0a1e1a0603040f0213140402040e0f0a0501060302030c010f08010603050a180305120a2c0f48010c061415 64
    0x2107807d4a001002c140c0c850014081c02c00a007000b4007011501030010342c407440e91a98088000d901c2044184c40070582c00322036500d04040c81100303903044001c5003420b0040c20381d004050380d8911500b00113202003c0c1d0b5800c0304003580200ca4890014403100400c100c5e128a8181003d40600c010206c0c0ac0b03114040310a5004c0d000c0889105105580e864000e00e20306076a02c56081c000104420801c2400c075200742e070350f00c442d80300003048542d117020b00c241d0010541610310310605280c880030304a55414080385c000360940c081c3e440881203044030654030340801d00780c80d080c1841004200416514846007840b8101c5000e250300310000b4002120200c501d1001a95195940d404030303941d100302030111030038202c0314012000245001c0441c0420703035826200e54240c0030040c0c601d0b124180310141132080000072040d0800411041903c12118030140155556125100884c03d00104000490521460382c040c4410b11040d41d20000514002c1035085245003000000240000c0950303a0031840f541001140840c2a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 646100665 1250 646099415 646099429
    0x9130b04030c0303062103031518020403061a0916030b09180607030b01120c021006030b24010c0b07120f05090c01020307020d0602070201140406050301050127030b0601020a080c010c0e 81
    0xf00c6e00741c2c8016004100340703560442c080c1c9440146000080c144181c003040c010140701e040b141040c5c1410006035214034503d020700958058900088040c04442401d080f5600c0c0d105c0540d034003801400f9a07085180521009400410007420040c0d0022000803c0000c0c001d14010340f031010400305800c4178425514404220140d0704500b00c2140000c4000c01080e14884a03074000e40003410450064600001406490394100d8036190300075900b003103c09041c05582c82c803031040042d9840c1030581820700e805000b400641483c03003e00c0300410030035440c070008440358440c41c0114042d50480000340036030600c40c00040003500058030030000900810003860410f600000031207801e41d9026280b24030000498a80784000d401009099042c04490389000c030700c10030464010000340a0741d403509a00da505100c0014000e13030b081400d620842883c0070404c01d01080440c803400071a070380140c0c1800d80d5610600100d09000300740000402121010030303450f222840640220305851401e645220000101008121070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 646101915 1250 646100665 646100699
    0xc121603030f1709070b0d0b120a0606121e0320010b01020c220f020f0a022107110d151a0f030601180b030102130e0f0c1809130b04030c030306 63
    0x21503004510400501d1506d60182c05621244140040c1c130000510100c1c46101a00003440095000031217413008010307040c031805020b00b6074000b405001b0851641d0b01140c100080b01070318170031401d181519082500ca05046c3c0a0009865440c5480000c101503040c0a000461841c9015008440d40864681044095140c1800c0300c0107010f941c0d8104080c3c034038010060104050816902003100c0c10352803110000500b80500c6a500401a98200151520300c0b44100d2505411028040040c0b00c08500d0001d10800d0310542255203240f184024900808043c118907a81818a8142811410340d4841140c4d0200c503083d0030344010f10440401da007010784890342400b844c000c64540c2c640c0441d5100c600e80c828202c1c2c01c40540010300e05218240351200d039810592203080c1c80c5641d44204210510881c441c0c5030003c0307403540e4580c105550101c5e005050070a90b00b025000b0f01021000030004000305d82d6044010b0b0300141c000e042810a0308004007400c030310003026008642042c20010748841101c5403004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 646103165 1250 646101915 646101931
    0x306090111070b040c0503070605040609120804030605191d0f0115060c0c12211d0103181b0e070815060708070c0b0408070608090c121603030f17 64
    0x49800c40580d1100ca015401800a0305d210420040110301510200310020141480341c40303154545240c100300900c441e0b00b42d0040e16240f0907200b20000000c10160039101600d621220101e10307076642c42922a10f403e8030100400005080203040d2001d0300304400d0501007021100d00340d450712a0b150528500303869070469007000c0e80b0000c10b010400c0c24814892414150303c070f07100344600181c0d102490071069000c144c06440025001406a0380355909200002101034981001d820601c0c20b240301d032941d0480242c0807814151070f516410200045403240c150215032008803d8045403441c80200d400c04598020211242840d0010403600d6000e48682441060f42100f280d40b1120f007441131042d2170700b150038100c40408003030000400040c02102030304080c100113000644c840f4a4526020b1174801c81d54000e80510000b00c0903c20b4035070307000c02e00c10a11003080c0e40195a9250342d103070f454a44a010195500c078581d04040c044109071340281ca4800d0221103540712810307072542d042111080074081c2c0f4509 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 646104415 1250 646103165 646103167
    0x605090f060907090801021201050a060c0b010b0306010302130f0e0c03090303041e02060a02060906014a010e010f05060406120507180834060e0420090306090111 71
    0x6541ca1030700391501540040249015903070103039200385207800d80e0416500148003280520061005050406c10302c070040c8900d1400b5960760169484841e52140c040c00b03000c0d000c2c0740001c0024038990003601290000e9588842c140700aa6881c00060049601e6000718000380540801080e12031060340240e80c000c42107600914070b580c985503500c0541c000c1031610f560b0514078400902d4003680d03e1001030a500d4096401800ca103150001d1850700b4244140c0000201c90b1691619144c55481c81d0f10080c40c0c1601a40580103003880c81d000d0990103c1203e40c09401c038506080040740300200c1080d814101c0e98100045000c00e900c0d50104000e80c0140d004680001d04401003003a110300784d41d004036811410074181141035803100c030b2801101454075005904240e02a01d001112550080709014031000b0440320000d0300c1c0114101040d02001030b220300c0c07040007100c522102269072103500400307041c00c0c4807101c400c806001c40750a4590f07400c8501030074441d006400000b010307482c060213030b83c034640c00042950f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 646105665 1250 646104415 646104421
    0x70603020d090602030c090301143306070302030a110d14070317010602030702130507140d021908070f030506010e01110f10021b0a02010507080703020c130f0605090f 73
    0x22002504141054800301da101c1e215032000c0303640d901c000d6000c1c180c0310017220f5487e110081410b007550401c111018411000000700050500c015480311200c0414110401e40c0350408959921400d80310f00d10039a1200e00000d01030209900000101950201354403403000003003480503015100c5120401c0500418020f04000000c80605801013010a00c01e051601031101803040380e18000c0c400360000000b580c00007800005615001c0c080c01e40a549076203040c0110310f45035000a000c2c0c00c0c0800807402d05103000c00c0410060040f501501d0b07410760a100d04624406000c4001048007400740c802002003680c219407840c2c41480780c060349206500684602e00d1020314100110381003c0380b0030300c00285015020014a000b8014441c5100040680c0000b580710140350b07805802c1101000d0907400580d000c00c07400c5005036000001c2d202865000803803191030304e0807414180d0410b004400220383c08500d0710918010f010490380f019040c0f10910301d0410820b5120414041c3c40c0d20150b425044210b900000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 646106915 1250 646105665 646105667
    0x307090b0313200f0a031a13060c0e0f010314070e031014151206040b1302040504030207090615120b01020a0b0106080103110f090f07033c06080706 65
    0x950b040040b10928001607121511000310150348541e0039484040011080c900701e01d050950241000000c4458070400303460740e030f1038064400d540c4c8014040780149500040e4250045010b01940b00d41109080c00410740710680100500504842c05109500d51006041c07954032070f100b14082e425441c2c524044a8032100c5080d1881d20342403140c0343e4144603840ea0a00585407034001d00300141b10200c041d110074107140d091122090140304056014003034a6140c0c8041d490006101504030341c000e16004800e03203c0c0c501c00401c9080040c8080e41007401c3c40140410158009804011510340c03002c10010701d0789809181c101c41c1e1405002d400003940811006080d04003031350107003030407401c140101e9800c1901d6985ea8188134400f41c1c010f10104070288010418001113102904041400305d03078000d03441403601d000070b4600d000035103507081c8004070f40b0005480c24007aa0200060000c24686480d48a041d6192204844094520424014034549141010700700ca130107040240c07250340d40500b05107070030604 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 646108165 1250 646106915 646106917
    0x6031b0c080d06082b02061609151d03010203092e05010605041d0709060c1112012a050702010c030302040b030703020a0318020f0607031419080c0307090b 68
    0xa007a1528401042103540b10003181c4114070042440002078003114240c07500103c0140055a11040c65441c0850b070300c04601d40c0801d03001e50201402000e004c1c11801c004080744c030003c45421050956000003013455011b504100560700384a0980a88009001301c07109260907400103840c480115800101e04404080300c002c40f2047e01e1444282e061568252200d04a0030b681080e404000842c4000509100c544031b00ea820820459403000000340a0034030301c1009120808600c1003200300200341120408000d120010403011440060803582500c50102110b4000e1601e90b90460412214400010180358105c1e00002c9140b003903298542024003980040d05c1d400c8003207000303c0405500300400b203504461000a14010309503640c0041e10340b8840790000e411901c1c60001031981103200c0c00a100142c2d52200103405406058070165100e0344c080c5000c0d104100380d0a10300340790f444040f90a8038204071440c041114207102e6501c900031070b101d01e03461000d00c0c841944d141d03001800b904414031003244018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 646109415 1250 646108165 646108187
    0xd08151e1513090905070603060e011208160b010915080c0f0109120b06150310090c030f05010902031f0312031802030d0804060b01030c3510030b0106031b 68
    0x10510750301c1e103800b841004010000c59081140b185a036400d8040030300c4410461a07003d80700d2400d08101c500d04041c000c07035213405e0522440d051503048803441c1d81080303041e0003541e12080c503103a00381d4502e285030300e031841c4441000d014001c6020b00e82090b014112003001600b0007200c0c6c820f0302030090035610347c0c00d000b649040c5050860501880850005441c00703000d1500542c1070160544c201282410820020103452113aa03c64030034505005201441410b44105011100385020004040d4400b030025030180244001c1491414074003c000285065030382c0095203e02c5030741022078100e00c0205c2d1150000074081c080517010408440c140e20040f07003c2e134048030881260165440d065599a8006032030001000041c0e00015501c0040c801040081e005403800032000f401d0510004000301401015003107107000f04034092010342502111401c20b5180e10500201c681161941c0e840e00c011501c4010720948021244000c039000000b860130f10911854070450a943c40b150811b00506004480150f001c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 646110665 1250 646109415 646109449
    0x50d0b0402130b0306041a010806010f18080c0a0f0e07031107020d081305010915080c0c0a0515070201090b0f0a140a150b0909041e050d08151e 63
    0x20001154080c02d580840d40007061070801031552444e00e0b200348420788a5009080707030102090900075a40d6038104a00e82d51200003840c14606c004182801120740281405240c0401091141e010406610100744080b000d60700b5581e42124a03520741c0c0245074411548038441034001040e000c5102c0c2e5101c0e40260071240c80304200c0d0b41c140541600001d88000c085030040720594400541003110508141c40d55008003c242050200380e85000654a43c00c03210300c9803030f41000798074030001c3c07a15650401610b280085c50411070711100000c1c90126034841200b01040c59454244001607001c0f8070500520303822a0307105915005988a0b00714150031500050103040a09813160210454241c488a43c14070440f00102c011508210b504240c4090409a400542101c20204900c400613216800003c0e002a400045944d00c22001c415200c0f034800c21000080641c01400300c0345189030344c00400e1340e0094001c5154910407280c068100034200d44e048081e00c20694201c141d030081460400e400c0b902c21995 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 646111915 1250 646110665 646110667
    0x708090d050a08120a0e0c09010b0702060c0d0c05160b0a030911030a111305012102150c0703060c0e010c0308060d0b1003052103060d14010218031c050d0b0402 70
    0x1103699a100c0c0780e00100480d1004c10741500403c40ca444a0f80100009000080d0180c0892201c080c0811001d0340140240c803906000064158110749441045900031160402541e0034540d1080c2d00806280c0000c03400c0d03d080c13142c146d074044600d4000d1385400031650b81111051a107056800250003a2018804c1942c00d0716482003e80c0058400740301c02e01c04a48140440c0120410010411240419449002202514040060011400c200b04c550f0b9001140705104005000d94400540e500346001c60401d400440804c1c80801404000f03810000c0c0e0f440b500003800400c03030620303046a074919041003050000b0a501e074944040307070040042d60b80005024100145809407601d0f0f000907800c040e5403860f40000340e40780400030701c07001b4080389030011400d40852709480001d01c00e80b182400058480c0c4d204403560141d0f1710030400c0388142e8030356854402c0300070b5442c0e006402c010741e0001c0090004074084c0c016400102c01141c030034103044a0680085e21010304201a00b15840020720b0000d81d405c0d04194 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 646113165 1250 646111915 646111933
    0x111903110d06050a0b0325050628030506270a09050f07170f0c0612061809030a0908070b0d020306040b0d05030a0f03090c0e19020310030b010b0708090d05 68
    0x90b5002d1a4070424402502294890282007407602c0e01c84503001c0d0b000c50350b280f00312449040201301600ca0861b141100c3d099101c4140201017440c440701410901000c07000c0c0e2068808603601604540e1003a0b4080760202480180008980e00071208130341c5014030403002000148480d452507000d81009401101180e00002c9207450140c500710843d00840e00c200d40c000781100151134200501514102120058440d03080f843d0045400c40c041c4440c47c0a540541000007122921200410141e6206a940d4013009041c1304c01c1003074880d1f00242200c00003800680012580310300008603401210001c0a00502c3c1091140c1d210009400141072550b100d92110620009982c480711000d0780c080c00f40010355528100104041c01000106408005250411682c0c00110f50600311a204494140c004100c460361016101c01c006081203000c050824804800c2c8501c815401c3c841e401500d2040ca490030701c0ea6201c4150f40f80d54025008020240b40040000f283c0706d04200203144c0449106004880d02c1c11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 646114415 1250 646113165 646113173
    0x23070503011d0f03090a0b070510050a06030b070915110f06010803130e01120602072907031409030d0e03130815070f0c061109060c0109111903110d 65
    0xa40042c2001c0081c040d240708000a0301e018446854030b0402000207524145100d404a24110854802c0804020012899200780102402500c854000c008020451440c10603a808000c211902040c0d4029100c240060402030081c61100c003665001e405810a8002c2d0031400c50340185078a02c00241e6006241d0390000740034040000c107000c1d2040001842d2940644110309005c40c03001da102511003001c0f000100502d2154160796819039400c10000340e03a074105030a00362061004080c45105600f5108400c683c40c14640020781d028200d140da00b0300c10003140c9581c401da00201954520f003950030401c21076610340010341c00b8068640300321094038240a8000303100300c039141403544905200c3c2c00106203140342888412003541d01c4541c0d4248107102002100d0002c1100502e050300501150740c80c49045040403d401c02d644007210b00800c10b56541003068401070103020043c0044a0941d990610800240f4014a000c04600d4200c40c001c0380340c134503641312000744101c813442c26608001200b0b245070200f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 646115665 1250 646114415 646114421
    0x30105060f09091911120d12050411060304050705090a0603111011030d0203041a07051206150f0712030627110409090302060c0a0504140f0a0e0f090102072307050301 73
    0x15500440c03401002c0c8081109012204001c6e91420495130401d1b1a20359a0540041d81d0a000044801c00000c40f55103c1c42c240707192100422210368071800100030401082b000150401c151502540c0c2000a070321403408400589d01c8900000b00108111014800076042100d00000ea4003054030f030030340070005c200c4c4509003075502c62250020b041d034001007000f040c0105034481400c440e50b00704803071810b850701c240018014000e4041b2200005144808102c0a9031400715000360381c640300310039a5440031401c6442220358030660701121558100401041624000d00c121422210000e4505d400302380c918403140d0700305441568442030a40e48512024030700c40f288000e0005814200e0300021103582505019240400c000c10080c5c00200c104582a00a07601800381d504854900f1519081640c4103000070b84d42d40020209160440c003828000a01c0a40589519000e840b03841801c0405464100300c0c2c034240c1c8918640500701c64003007072590700c60110120400305040c05610942d0700c05529800020b0075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 646116915 1250 646115665 646115713
    0x6030213030f030917150a1d060117070f03031b0302100203190b1009060f02120703050316030207080304080d0e0a030f0e0d02030c1018090507030b030105060f0909 72
    0x160400303000340242140740c951410091000b1740240100755007500c2c60a14550020100c0c404161a2404000e840004d0501d23084403038404000c0d10500d40c0c413658440743d40400c103000c0b02c005100e8a05d0010b42010307802e4140c3d00b07803901540c44606c3c440703032000c0a441941d15154102e003148101c0095000748002e6101650080480d280b5408050f03800023010003d4511444205109602daa090f02981d5900922404220707159070920425101b0a04426410010300b50307104003400743c0000e070b0181010340c000000c600c6105035007034400344403600c0b810413001c901603c0c0d001443d0b14010030104002c200d000d00038020304a10b82401180007180c14030882e0400c042c0480c101c01181036078900f09442074000309400402c0c041664040d0440009070006981c0c3e82c6030804107401894000c4040000c64030404444058243d440d11050516565501c003100800d4111406c0c0c0000b41343c4490391110f80380c103014107800790300b000b0000000d6211102c10408000b4000c0c001445610612074200c20391290481c00f0b001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 646118165 1250 646116915 646116917
    0x30c04080a1208060102011a130e03031003030305160f2a03030c02010c0e210309030601060207030b0112200102010b0a06020307020a0504020309060705090604090914010c030608030406030213030f03 87
    0x300c501603414060043d0350068611415a41466000001404854541c40203800c040342c2c06803844625a2103171001303000c10036000c0d0f000d0000000708039464028050310400c981c8280d40405c5030380d40e100c0c031441b40d45170b0301028030300025911510000b40c0d511440200e1401050309c6014110402c1c6816440d00c0552a00d804801003070f1200c0311503a02507020320454030b00d403174241401c0006c88004000255040c88504000103001035007091030307013441030800070382d4080380000e0100c2c0d60039612940d0180d941c90071480112000c3c0700391800800c00502005520002c9a03106c2d900c42c05c0481020712800b447e24420301068115036a852249096994180768240281815000345980c1d130614018401003516541101d0301480c010800e0041130400060301c240d01050b5440c2490f1030341800c00010703203148281e5110b600080e0400c41c5080a000c200c0d83d07039040030004007000b04115600501c00b03800343c0e041031041010329001400100301c0c55000f0b03001400d00d603800d035400950068603566548a142d00b481401c1d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 646119415 1250 646118165 646118183
    0xf0307140a0c0c0b0301050f040e160807030b060114090108040201181e0b070506010b0f040f0e09060603010b0120010e060a1d0c10140702031213090b090705030c04080a 74
    0x4014440f50a2080000c0e048404000c3c0c5950304007404a0480041f900046000769a14902d000f03003144d082c010300c6800180780b09110ba115680d09005a0786044130300045c3ca0044500c0b0204003250300915540d040308140b0800c490509542000540b0440b0740104140c3c14012061240074501074003000311005410400b4051000c514812900c07520b0400c00e800150240b030081203480080b840005107203044030194018282c0c4c454080c880d02086003e2a401521848000280850060080700301c9034410102c040c201c8480740c0e40c0f0000c050036110510622800700c1e089403400d80181c2c01150440102c2c4400c0c00000ca068000c1110182c94a0011664204816614101c50b010201c400c0410420311860100a00701c3c440c0e07510000b00c05840000c0010140001e451008500c0d0b040d4905640c21b060300202509c890034244081920140d000d403402c00d509a01200b404030750300c0b04500c20340c240680c000e00040ca140c0e98805068800d58005010308200c80d40a00000800190030000551224030440c240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 646120665 1250 646119415 646119437
    0x1f031707020925051606022b0b011d0a0603051e04210906020303010e0709230411040803040e0406090203160812121f080d17010801050702030f0307140a 67
    0x2910060f03007000c00d460400504200c2c1350038030341c200c00812503441d400c03d100698404290341800414003606800b507061041c4200103154100241d400316080900030b0b00c44207000400c00048902c10b010b01c094650b0704c156440400c0c030209120f030b0700240c0d0010118401e07030303404110001010981c035000c880440d241d400800504004446110345194035400900b0481c07001c0e07042441c043d46a0005024480b8190f9200000810440c481c118400080500c20300c451048120b0404c600e03040100709098a00441c10500c0c240c034071061210803641101c030340c1000b40d41043c6c1080785441c00900c0103801a11030300c3e03c0b9820200540e5003801040314516100c10f072108240d00d0002e40c01d04090220390380c850003203010301400c1041c15061140551100d500384180c55180010500c00c0708061780c40d0454030345442001c50010009810031005000c004c02d040143c0101d83c0c2c0c80d0f1109091720000c41d4900d005070418031024100d0109400950340241c09070501c03800750581d1a8611840d504182d4a040020780100c00f5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 646121915 1250 646120665 646120711
    0x3050c090d050c180603061f0506180906010e0d0206130317030106020d0206130f02040f150602071203020c01050f090301020706020304153804090c06081f0317070209 73
    0x281c4c58190340d5480307000d10303601d001800a03850f41e4005044100050790604c00300315103031111030f11034050711004150700c4d00d662030900110a41e507443c0c0340b01c5000d02a04c0011514a60085401d5807502c01300602c0d507010010700d5800d000160704480b501c411f003010104008400a234002410b003500301410100e5948070340c03401000034030b80030340c600f820019500141c0912824030010010721103019001402c410f1a000b01d807002c1001007210030034103441507252140b00e264100c100141c8030300301d859960854600315103800060001801c2c1e00c03401405603100380100c190341d50088002d801d03010300d15001a0b04144a0301e002c0390990b4043e020450344a40d0000411082201aa03d040d24070181c0010810100d07100350f111000032a200d00700300740215045085030210481e00c05001400d800d0203003090054a00c507182040f440111800f40d140421001000100400203a03140c40c083ca40f0f03164203420400c0d00d0364903590102c6000d03000400a0070801c220580140e1502c144490083c1c5280036840740d18003030100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 646123165 1250 646121915 646121929
    0x601080703090c0b0f070c06020601171203010611031b0c040e0f060a0e0307020315040b01150518010905040507090f06020304030506190b0d060c0f080c0a03050c090d050c 75
    0x32010040c5032a16040e034001c9030a00165030191030071003222aa9841016050802c107014541d00104904210f00c404101182d011a809040704c02c241010b01520904580e007a4039907a0203483e09a00e00c0080c8010000c4521400c580f080904111059914001c00f004411450100091140c015030380141d4005c0c180341030600c00e20440100e0305002d081c5072440304015646503003020b092205541c2e16804900d94000050040b5200f59078014100c81e601c0c0346000084079007070401c80f010340d90700d2048000010b04d82044c1aa5220000d4541d582074a08480564031641440720150581e0401241d804042240d4695215560150803030340c40740c9800c646459400d280441d2181c02c00f01c01c6410510042001076000160b45801082005056400f8140460000010300705400925404015030000605004595110000b4515141e071035409001a256003036943c3c0006443c103907500c00b001c004080c18130744264401500550000c491a15107144400081da04444071041603481c2c0e00160307000c2c001403500807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 646124415 1250 646123165 646123171
    0xd1802060a020f07210209040c080a0f02031002070209191d0c0f0111100b0607060207080307080603010b010c0f1b09151d0c16050d120e0a0803011415040e060108 71
    0x820307030120512101d81d0301d0800012442000f40114507d101113020004a2401c08020300001c10840c0c5102d1801c1c201240340c420340b40c400764040d001d80d0401e40d000c00c0b040e000b1520410b070050080300742c94403a840b10002ca480e211028000d1241c0d9180c1d540c45404640d90318612a80d007003030082807460710000030080d13480310a005031814849483c00c0d200c8841c80105003c214031140351000100c400d05d1201103000c901c90031000800d000c0c4002000b108102d40c140140d80a05141c1d0b0b90795400360f170381c0c4003071508036481d01c0302d41d5002ca80d1000b0207900094159500d8008544078501030141c0b4032140d13125011502603900248100c0b502e640301d40341e4036150303c0082c20040480120789160480080460040c060028100443c040400141d001050102540b850b000e50750080444d88034603501c1c0303401442e0308100240914a141000d0142402c28000501260a00c3c0c1216105280d6440e00210688a171816100a50007141039556406001d0b046006072005110841d5126900c0c9060b00004006400c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 646125665 1250 646124415 646124429
    0xf070b0f0603061501050f09040203090a0c08070812030406142802030c031501021906090209010603052806050d050106061b15050a0b04020304051b03120d1802060a020f07 75
    0xf44041180d104000c46070301d40e0060081c00c00302d60b00c03000d07400c401d091882412000fa030440e0000003800b0161200080350413004bc010706816030b1494480034020b07281c0a051180416035808180483d0810300e010004641051040b040003510b0180b0110706c16079102c1c102c41404500c400011130310340c100009000d840103050003403400c626603d042200c1c0080d41c000a00544a1a04034604080d00d690080060190140c52016103140041c00c5207840380c040d040d00031049015040c4280000303411070080c0a0a80546a00585152110300900030002c85680041200044684611000660b0f4803070244101d58540500f00115050f4100754014100d8010b0901524a1602513a400404240100141c40807134070001c50104058a034a00e80c03a01030040e040800794810302c00800e106c00c2080000c0ca101c1c3c1055181a6083c004035600c0415884001a8584107440b00c010881054072800c80c2d8441c2d411032016800d1240c00c0700554012030055000154040c01503070141210b8203900300d081103950010300311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 646126915 1250 646125665 646125673
    0x120905070512070812070201140d051603060308030f1005120307020406062d051209030a0806010203030618060607061112160c03030c0309060e0d1704020306040f0303020f070b0f0603 80
    0x4d41074410380d86140340c500c102c104a1002c00c80408582c80780e103d0800c1c1c10111000d46d925541d40c46081402083c09a800c4200300c01410b031007009481c003074004c1c0c0b01100d4001d13030701608603038442e1510030403058000c100b02c59807402c500020541d680d860130300c40c0081302c06000075601d908082c030610003101c416070045010700c500208114822001001020840c00c101c1b078450f06000441c02c0c0959260007001240518034600c1004c02228007030000250106101a5035051640d450b100010b907240e2100350380b0300740c00c040398209410007000754840160304108090006883d000d110b03140c01c812151410746403402c031800051002100008039000319049038440e40030a045a010801c041c2c0240a40d5a0050034582c0351044c80080700d01950121201c01d4026009014403070304040001d032210006110280800c65030340308888500c100b003032110300c2103034060001c229a4865485160241c9400c40301141015000c1003115145030101014046841c030611003990207060071000304021110061480c1e0003580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 646128165 1250 646126915 646126919
    0x10090510051005070f05072403052e050307090605030607020712020f19090e010c020109020a270603051501090510140a0b04171c09030308060112090507051207 70
    0x7940120340040c035000c0742000f40c0d4503480341c5803040e00710100d0980600351780904900001e41d0f003588400e4040440704145451107000c1101001c1d4202c4805441001c00041d41410440c80a050080081440307003403501c0700d030045a6102c0021303240514540124503e25140d0f80c041060b410108040c68122030140040c00e1032508040c44941ea0703e90990703002c0d10424024041c0895a25800411420b0b441c000785050314858a81c120480a402105600c4032590b1a04017203041091042c0b04858a084d401400500d00b01e10b05620803021211485020b15000340340d001c014181d5081f40310740001035104501501d901945500c5207030f02648140e000715100381c04d200070403075101c140b0040f450641d200043c4403035031900020041907a8000a801c100300024000402080281c541074410101c441e0b100c4c1140c551420454028400c03509060840e004204484030500000e40a140903540c41141850611818001c450482c0c00396408103500740e41a810000051102c0d0810344800d104201206005101140c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 646129415 1250 646128165 646128169
    0x109061401091508150405040615090e031905220f090b010507140304050d0309030210180902090303070204090803160e0d032a12020d0f170a0b091009051005 69
    0x8000c3c04490b40400c2a080005601800310440c00700802101810401840c90585440b4004000084030351000d480301003000508100340b80540240d1a050368050f5090846000c0d14100b44c0c5c85030f41040c000e01805010341001425803102200e4089000d882080e0b10a140071414203442c42c068200b018201c0c10045955a50798008c42220b04007a401100d0075090040300c641c0d1420742c0900d4101541c01445c2034145d034240342e44100f51005072402282e42a003008894042a03840c800898001c3e45011145842000b0010542d030140040c01d4000c1c00fa82e00d8103940780d00240850311901c008070303101c05001c4103105111703800803007010340391030f0b141440c00c44904a000001c1c1e0012026400074208a007059a14a111403901c00c0f44540b82211080649041c2d100d14000201c042c0d000c88010051048a600014192080c5c0c48400c0910082e2240b6401200511000c0c400c42c1c2e009000104240e140c00c85803640340c6859401ca032188030051a111a0302d03080c03446040c2543c00203031102301d00981408083c0701c3d0f5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 646130665 1250 646129415 646129439
    0x60302040e18010f051512060f040323071202060907030201120902041409070812030609013506161e081e040b182a0d0b010906140109 59
    0x400a00070008441042c0400d609001d019a0000030f081136080106101c01e60300c00d03c03448040c00360700700e580086107103401682940e5210121504181680c0042c04540803e0144e08001403440c2440020443c04800c90302c0c0070a80c0d44007103411980c21000d8258152010703414002c0b5500010450080c210242c9190002000842401035014111343e441c2d450780c00715070781d40e070180040103817903260000546000b00e4181d81b65150f5210742c0166024049407901020380c400b04480c0f00303000007414840542d085c009606103408800414074428540601031303031980b045025001c55101d40b084001c140030720305262440100c01903221601c051000c01e001d102c1c00146941c001c00800682071500000b1a607420b508480e82c64030f100d00f85030405000505210900c502c681c41c0031320442e61847d0b224050700c0810411681c540c01d021075030b03034210008401d200e5440e0b4804001002c0c040002c1c90b10040707214075116030758040b4007a4045d003000350340da1804010181a100041c070480c1d800b401c0183c03070b09203405217115003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 646131915 1250 646130665 646130671
    0x91c0f1e050a060c0201150b0a1115041506090207060b030706050c070306110403140c041404080313051c03090b010801110409180f0302160f0f0e060a030f0f0c060302040e 75
    0x6202c2d15140704c00c445501c02d51120001102000c14a5080d030358031034590f0700540c021420b01c000103039070101d0a000404c002415140c200c0360030700d030505103941c2d94480229000b20060014540794686400140750f642d9800500b224074050390780028600d214a0405203010100e61059050201c00d22011b0490a40444d0310002c40c3d8000501140098185400c4803c0d840f954000800d108450300130f10503444030004803101e5240e000d81e004c0090543c1403030004940e41e021103000745040020000144224100111140c02601c1103040324021408814403078000701101c2e40500004e95110024003d100041c0c2c07110b401400100000c0080c095904a90002c038800d80c018280c03410b80300c0117201c03881041001c6803040030790018000c00f0100c1152900035250381c661407286280500203440400da0900c00701c45c490072a151641030684041c0b0b0508400529500200306540c030441d29000000400c001c1c170108001a0720a00c40e80038190380a03d422107004803d60002c904051041c00306000ba10035400c00150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 646133165 1250 646131915 646131923
    0x11031509092a0603090f060108070f1401090513140c12040f05031216030b033f04060c12111f0905100b03070b09030c06091c0f1e050a 59
    0x200300b00582c0d15004016507840d0007a03000034001042007240389020805551100181d002d44030340307903030307803490b6550360107050190110f444200c000400c5407501501040c010040c06043c03001e2110f55271800100700400340d9440e07100940e00c1d201814202020038146c151700400b035208290904040c0000c600e445100184001c0000c04c00080b12000c2c02010000d03180c17203910b0a00303041181d144c5a5280b222040011140501090406880e54190324000c0340700903407005402c00326034100842241190354810f40c0780c0d08000040080100298911a803801070025000b103840e40c1580048525102e0481c0643c0150501040b50492080400041c0446c032518242c14900001540ba0041101d5600519620700d0041080c480e030b041c05002010796410081e01ca0300201d05a0b018940c3d51044001144608100b46906030012980480340d0315040f4050107806130050074040840e080f00001d4030030340d402030b01c041d283e60150700ea107201002918803202c85418072220110488003a60382e0303019602d2000381c1c4028 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 646134415 1250 646133165 646133203
    0x90f0905091005040c03020a06050901020607030f020d020414031905060105010f12020706090c050402070803011208070816021e03060604090312060b04030c06020c060a0309020d061103150909 84
    0x10038512041002d00712003103032240104054149840e00c0704181c84c441c402240035011304000050083e000b01c09403a581d10041e0081d20942e0381c1c14108400810050380f69038110f9a080c05821042d441c0c91001d4009015001107941c9840720001c201840c2034400004007141c01c6403103c1e01400200d0215605044813021f00781075a02e4410700a041d0b501c600390f145101c0c9100d1000c544c640512125400c0301004900500c01211400d898109001c146d1181c810090550301782003004020218800a40198060007101124288081c0d50340d035a1a40d84180c1010823011214503042c8254688807a002440c40c424145090942c041600800c0d25858000c001c00d01c5140d403002030f8005d150240e4030f4400d5a9000000c1005501c0d26811010314a400c5800107442520f0071510104180b800098085007406000b4000340c10100900c504030080c245204080b82c1040b078549010f07002507018015481c207200d05682c40c94491910300600c031340b0006c1d5444442d100701444000c0c0103075800c010400942000c0c0c081c0070b00b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 646135665 1250 646134415 646134421
    0x711160e130507090509150a1506020c0102071703070c08070e06060406120c1e1110020c060c0a18090c030f14010915050a030807050d0e090105060a0216090c0f090f0905 74
    0x10350a200004c00c034107c2c2d542c610300400a4a85035a4410300d10081446030085000c0d80311355003240d68900b80b05400340941e003d50f00501800c0300403840d060100180c0b10480707107000350664614080054075804507801764469001400340c1c0310410282a4040c1e801e0340c0c1c4074142480c0080080605e140c0200001a240c0c0d1841c40f01c003014466070780b100c1610b9035220202d02864a03244001c102689400e102c601e02c0c003a2251026034070500707008841c0f001d410100240000e4413012005ca034142d11045080082c0b10110402105c0e9a88507440d813001001003072400146901040c0000c2c05942d803101001070b80601c0d0483d50030341000e00a9a283c1550451000010805440500700c00c0050050300400ea0222900e5000030400942d10020001140701c0c030140c1b00b0000030880309603a050b01d1250707410390007080c42c0014412400c104002d40b61514051044bda401c0102c0da284171115007e54105050090311150b0244849400c103509100b0704c0c990b481c4c00f50030700e0720b0500c0c0020052418018807458030788035004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 646136915 1250 646135665 646135681
    0x1d19081b010f060305100f0b0901050609130e06040b010e10090b1201021201060e060408030919030f03020f1209061b030c060f0103060506040207020d06050711160e1305070905 77
    0x1403042c00040b1102004215200e0400c06e598101c044040c603081c500380110011082c0280c055200300e40e4025022900c076909120400c6545e070070005203140c02c00e09100760703000c918900740182c0400d427603000c0c0074040d0b9040030b0801140b1010141c02803014000d0000c14006482c418003011003c95544074400641c010042c00000c00d003912115400710250300106d1001c0c803040c5081007160413280191240c514410b00c0000f40040c50245110741c8283e60400d200015003400c101c084011625844080302c9401c075242e0b40c896845e90a089070a40c0160f00590101e00340700e00030031010001a6200341c003641041d510310300051581c1714402461885a08107184c4180c05d18003002610180406981a240079142010b0542c004100034801580e825007070201149880c00e16200300c0e150b0035005080f0101200060b2521400380c10080c00103003c010800f10f80c030320080c40c00c1c02601d068620314202d400700075240007a0304981c0b80010307124140ca6084c12480302d000a10001301141110b1050a000ca8a50745041da = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 646138165 1250 646136915 646136921
    0x1030b060a0818070f0f080c0a06030b0112020a0e041104290f1c0f150605031801051306050604050708040b041509060f0c0903080f0d020d1d19081b01 66
    0x283e041200e00c104c8101107100ca0749802280d054030681036101d222035036940101c95456855030b241c10303006090140288805446500070104620040c1403000c1040c0758444070400b2640031010440005e0021a0200100d1515000c0c5040868180c4880c1c0e09060810781c0d4038044022152604640001c0380104a0381084c44405071820036110080040d2134550348004005285000e06442503050324000420100010b5807143d140c0300c1c10256001e0755185d0902e80b040c0c829510180140c3d00011101d241a80000350900415106420843c0d4480b6108041d241004c1031300d02c050031003482242840104003010381d102a81030340c41604151124003d07112420305290134107211a07110344150030040c903a03040c400315400401455a0000d010414407590a50403161455640001024014200180e105050448018110b4040b00f0f4000600d0300b2540c044020441d42d4001585c01c08128140c005000180c040c0210105540c04100b110001c2d8010b64644d1118400d610321558803810340201c100c170074a4254 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 646139415 1250 646138165 646138201
    0x31b150b01021f060305070b1c090201020f060a02040914130618050f03071415040219080313080606030d2c030607170c0a0c020616021c030e01030b060a08 68
    0x50603c040741040d080c10b100c05003001e4041a03072240b00d44940022500e0102e01102d485200050400406070f4603240050003408250902340c1c11480350702500300000e1804d00c0440d0141800280c0180d440f86801800d178155003c004206034080c480100300a201c04464440e980002d41c4810001005055888100007081058070050454030811486401886000000b0040c850064111540d410798058816640e2030b50681c1202000c211840403c00500b043d40c60541804091000c256007144c03034511740c038511780252440c0701c140c20484804000d03c4d60240300143c2c00140a030040d0001070440100908040740319409079082e91004c040017161502c0c0b42c091803420000050907070750f090608041c02090404084a00100000303000c01044607880800e003100d03406074454030f03406660300039074007080341c69045044030040c1e54540509450041c1c3e0350307031102240e48078680380000e411009402c1c010200c100354140f603418035140111902d110703134800341a10b91268151502c1a0156119000c440c8201c01c98 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 646140665 1250 646139415 646139443
    0x20030403200d020c060901170604061701020403061508121303080a11010b01110c0d06201b03030402220b120c090c03010510080901060b120103031b150b0102 69
    0x203058244050800401c414508101950813600a242110100b003498855900312602040e2059889804514485481c0b42d101c00010400a52140c2e0b610600003000411a4000c001ea540000e041c81040000c0c41800d041d8028240301c2c000960800300e031150781d40e49403c008480c450b404120319040e05c0b04a62918061071740b2071207064a8103015880138080c0c134403e5803810899420100200c0887d44a5620490031014000082c19540812400e026001e000c0040541f20103854003490703810341c0203145000c41c0d0788060b0200641d40f0100c084032036201100c00c1030080081c0d0810814400540e40751681d4500102243c80c0c80b904145106010078001c0030480c021581250f60622080102400818000c080c508162043d00306503031084144079840c4024020706600c40c5003c1c12020380c652003220030035848243c0a0001913050f8036100100e411741c1004140d11a40703901c020050041582c4150030003501c003035000750035000c41d10070b84e40c0e001c6201c0c007440f588a00c103568080c00e210340d80c42049508250860 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 646141915 1250 646140665 646140707
    0x210503090d0c0302011b05030301150504120b06091506040501110a06060611070504050402150a1407080307030c03020310140312030f0f0c07110907050c030a0e0f0420030403 76
    0x70a1500d050210302c944000ea0214400094840e00218400645c1d00010380c400081c40c030796030805400080210f2614010001c10030103220100303c03c2001002404068040ca50010051074030354204401041c2c000c207a0b000d11003000c1c0d400959a15a241501d040d60000d08011040c10300c1c0f591040e10b00002e80341d0182034035040c00070001d046504070314042d0061000000341e9023150f0301c5500740815a8400d42d0300070b4100d90040708014810380b0080162602510303e180c4421030030760131903814681d5002030390f040d01d803560b0010601900e2034040c8103440001034181019070461400e2140403144014911440174100da88086106440d42c09001d0000035080040712151241031903042c24175108401c9600e8025070b115000842d500500d10015035203403580c003440e1b4980c4940400240146098054045010f02100340180509043c01703102615a0043c160b4a440040c0094020048910000000700c4d000314542070381100321404c1401d10f00003000c0704219041d940d07255842c08407002d0089a5880d28200c607 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 646143165 1250 646141915 646141939
    0x121503080f1605010e013e120f04230709090f0b072c0d023f01111c02072603060f0a0b071113060e04050607050f0301030f21171021050309 61
    0x5109c8480314002c41c01200c0054490407014103000c020344000780b04541a40c0003000030000d05040d5040803d040e4450005030361001015990b142201c08181c2d0302d8000329005124840c091103000d0848180401e20805440c540c40b580408902d480103240b20190080d03c880100d50105110011000249912201616a402104a103142c113909904105031419401d040320160031040050a69400070300300c24217907440c44c4616214500940c0042c2c000c17610300640411220011038040390b0341d211081d248240c40d0b528500f0078104020100191a004e1023a501c401d01404000714410a4590f0261b00910501071020248001810307102182d2070b10300c1d15410000081f0f541e01d21010b134103020728410070848070941c568000a803410301841c002c071a2000824001000030074503803141d201406001c1c1d02107106850007852042040888400c0c02400320380610460581d00c2c0b600781030180d01050401c2410041e80c18000800303102d5040d080340048040052000038103005061088034000500100768220b43c0c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 646144415 1250 646143165 646143181
    0x30609060e0f030405180709180605180118201b03130f060302030606070206092116050108090d0c1401050a0c121503080f1605010e013e12 61
    0x1504c54020580602000305200804503030861071180540c0721030329520605070a00c80c020a4000c200c40c0c500b014240c49400c0003e0940303d45100340e02e55403000d20290070660600c903100e20b50440200e03182c00d9040c6071050303442a040b0180c40281e00100300285c803964035140400a803003204000307102214540400285031042141028240c0200d541050212907103c2c3c0c1c0d8030090b422804115246500007508115507001490a82e000b00710340d150061200303507046000140b640d0310780c03249200c1031a10381c00401b080d403426000c04440e00007007609180021003481c00107a01a100c0d0740015090040c01400c25042d02009150070301004550120b80c000c010525064041002402030581e403040801d101500d480400c4200780240b110059420b240d007205c080c074580da4814298800c001c0442c1881d002c6c850708250604246001403000d020304004100e02c0b41956003142101c0c085020241445003440c4061110200c0841134030b008807040c1d8803c4c050f03420110030044a44120046220100500c0e41004524 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 646145665 1250 646144415 646144417
    0x90a0506010305060d050316170c0a03020120091201180303020711090f072102070501050109060b03011508060301110a0f12020c03042303060405030706140105010504030609060e0f03 80
    0x5403100766014400b42e2622030502c41c0c0703518440f0019080780c10402510103481102101c2c3e5403400c0c4581801c264903014405000069084400100c010b600404018004d240e824040d0700350400d0400e690301d1503504240300212052044100f018010000c1944105800700c0c00c1d801600081c801e074040007a841c0b0340d460020020361040c681164190100740006015041034030f81035118040c012089803140c4c80300388054030200303e001c1c4880103001c5c0b890100310741100940058800144207000110b02541007841c0c140903100c41d60801100c01800340010032002c1d01d0341880384014802420121b42d641c0303424000c03c0c00b6090020310f00f001080c0001d200e503062540611010314491f956903409002103502c008200581c0300d0200d580300d241d841403000b40a038a40d680e0084140082c1c1072100c04c03a1071f190001090520a04680c1a02e85403c04200e500a100943c011020410802480e05450b0360604002038900e003d0707404040e107090390710303e41181040300e680c0c82000024020811280d020200d4a0b1380c03607807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 646146915 1250 646145665 646145671
    0x1b0803130b070e060f03040f230705030c06120a0902040504080c010c140d1e05010801020316020a0309030f110916110601030b01060e130204090b1518041a090a05 71
    0xa0700ea4440005030140f845014aa00d00c50002004680b030700d000f1020303200d035680016005481c22400c1001020000300341c06a0b8005840321010083c181c1d09958030114100038040d480760b40660400b07070070001d007941ca40b021100d0040051116142680310084010010038150100a4000c1c2c40c04050100f4001c400028040444200000b0b0041b0051a00100d840078201d5000b0280a1400d2155003079964041c1c00c000780380b10803d880c8001072045c110500f4181d0f0700a03400110700365030006c01c0c0500f0803030400381441c0710a40b80c001020714910903075000f0601403072440050030811079641c4502c204010454a5a130040d001052018a070524180e0b4092081140130510040b500c011005020b1390380c0894040d040300e40080040200d6846c0400c255000303000030f0358003a4004901000401c03071040701e20140014180070900029910300c40e10a00000301d440c01c0c0c000c2405a801c0c02600240c94200c829200c00d000140d0303000ca00780e403403c00100c422204050040745d10030070300410000c9905c0b681d40020301c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 646148165 1250 646146915 646146923
    0x2070f06050a180204021e3903030c0d020405030a0c15090503100f14040f030e01030203270f0f060f0a0b010c0f08091507060e0c0307061b080313 64
    0x441520b458200204803890507000ca00d03840f207003800f1003002d450315501030b00d45614884401094051004040050340d4401c2030841490340741e2030960700300d0403000d182949003500c1a208081d00b226000c8003907540d9010040000580e11000100030300d42001540540b80140f601a007110320210103881c007400d00c1c0380203018011003881c1c1c01919000c00e034810300c07820049130001f80240c881080383c441100c0250000d80e242d01c4426032501160a9651a0300f50454881ea000b04068800c1600074a40140368800040300d550406005105021034001c01d900004d503044000c00300c803034607078411030380300b81c18036440741c80000981c0074806000305c0c440401300702e00b8800c2c0303500a220f10b15651085000b0080301c081c00003c41c006480d03007160400282c056522131170214060542d2900304092900050780d580742100301040c6016001c1f9220041050034091031580b445110040d001207542003000c20b650740002d1140d0b004200000020751000741404c5118006203402c107841507a41d1819018111141c0e048030380803a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 646149415 1250 646148165 646148171
    0x112b060506041a15070c1502060f041a0415020d150803040602031903060306020406090e09060702190c080d2304080703171b160608060607080c1002070f06 68
    0x803928945881032404501c500088044161032080c10710039135030009842d440d080c09040001401280e20200078400506100300000b444420b201c3e402030410f400906001c1425103084148130015400d482e8500070000d1a00c5c000c005070391281064818038811041c080c15189c400224001c0705da525802180000300342c10240c080c200d076192002a524230480c071a140047c2c03c03d0149051440c5407038101310210a09141c0170501940b240c54420480e032156000c0c0003c20401c0a040051f4021a4a00d03039016100300003400d80c41c900404083d4841046103040c080481a045101c2c0811100e001c04401600070081115416104408058007030040141c045d40140c034508c0d100d078440d000c5c4000f150b00b521071490181440360303d5a039410501c0c881a004643d89841c3c01d01404441c0c1042c03203182c0c18407a100ca0014040c41c4840368000b04411000d802c548104080e500070042c0588440301124100c640c40142c142d50b6201d40c0001500700700d680d00051410070f000207a240240012460a01c02281c0151020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 646150665 1250 646149415 646149421
    0x292205040e0715050921150723030a020f0409060807050603100902070f1b060806062b0b0d0c06030606050306031011160b0405010b090c0304112b0605 66
    0x31542d1062984600b000000e50180c41418880c0315802070700d01000003810f00030305c4001e1030386c01280d42c01c0200020900b030382c080851440c40705130b02d40f0566000070144c206455945c0301c48082d117000340c1130198543c004400010214500d44126070440307100c0129081040d0316a5100d5075114044d000303510500206108900000c25640750a00849005168054082070030b245410030240194111080550300642000c0c0001b0100315000c0c804550290034415020302c150509401528441c405030803280a02d4007404036041e13503e0030120b032004c03500001940058540d860038007078000d041d00300342d099000303680798000030200240520308006031900f83d1001d10080d6165101224240811612030798154012142100b42c0e200e1584948000c44115148619080880303800e8559010800811103452800c1000c000910100b071040030443e040032142308095040488000515020261000e07109203842415200107030b444a040c0000c3c1d01954044240d0a5103509040005080084054510328109000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 646151915 1250 646150665 646150691
    0xc090b0403050303011a0906120615040801020a1e210902040204030c090f05062b0b181902030a080d0b090f0a1d06011a2203050f0729220504 62
    0x45d40c01420000d080d80c3c1c18130f400962a101d00c6400507100c80d4002c0d2f51440000648036052000340090f0a020b40003690f6641c9400006008129910084621544081c511840594030440da040100400320305181c500c40c0040c10080208a03412000354481e00c00200081000f8245808000b02c4145036810800100950743d001c042c8d62003194050b91141100c035100021424a0102c11000d090740104003440102c07990703c171145034806850182c2c00c001212240c0c182010100711400c8544488444a800b9201c1d07a8042a0740e010034243c001e042840200317828245016551089445200040081e40300303040c580c008801e20503054405d00300030f5003000c20031603954440588030b81526800fa401854940e00c0d007e41030f01c1c0c0200d03d10329813407042c6c800c020700b618040c0310441010360b410020f007421b200f0b240742d840e00360f2501715504400352440d000f1807010072076404034845a81c452403681d40d42502400e01c1c62400501841204200501c00040644880c0680c00d0400800c0a80380b003601e04000c909005a9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 646153165 1250 646151915 646151917
    0x2090f0f0606030411030a051b060c0c010305250309060b040b01210f0525091215020c011812090b09040b0a030203030a0305100906180c090b0403050303011a 69
    0x9984110000d400c80460070030b0a11100844d8410301564640315001e0320000000c1c10040139580594050340010416240000c9403007140c142100f0454499260100c004035041e190420b02d4452030516a0380d070005002d0400e80c0317102c40c5010314241ca042a96a1080d0030180003041d14034001d88a0a142079003020603070500e449113a45401e0140c4035181d03654884103508404a00844008807141c0d1036020041540546000d0540222000c81e280188140300200140c1c600046800794410850110340800100d840a10745685a942150200c20740e5400c44071003102a1148440501c2d041d840d00b10003400c079505003600a15414441c811042000800d03050803503d4100742d0052900b500340c10403204041e407615610581e02040d014180001d031550301d40019003141c001000d680701003a280c400b000165601c1c132142c1303006020348080410142d0300b000210603032203e08091800c2c100f5900c116040800307005141420051200707039056580ca0780c807490460303200d030001c0c41503807160b110380643d50b003401010304 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 646154415 1250 646153165 646153171
    0xa020307090914061009230906010810060c06060b0c0c0a08060105030d030b030c06120a050702011a12010605190501030501050409170724021902060405060a020d0f06030b0402090f 79
    0x1003c0c0c0c080b525414100400d03d00c1c0390072035005011000c80001143c9000c0303900f0500100e1000c107101c0c3c15505403000d22a02080c010181c030f040200d44030801420712a00e07008801610154644800c1c454110310f4501700409058102545d06040843d660b514042c1c002400c1901003010384910304200d0380c030703c2e0712541c0e080c080c0107160341034201c0115180e155100343d0040001820050480b009541280c0110709150710600406524a4103001041060800c1d0702600b03030000f07004c0c802000420110503140100c0e80c1d100460501c9080c01065a50b0084000d40200c0301412004062500c10076101c14000140081c0d8030480f80428100000040c0503e01031080c4900160486c0f003049041c1184440da404a0f84400b80c2103e40350910400c0c5605410211004135000341c40322001640d0f000709050000107165a14809000c5602c180304000004001040190300000343c174a001d80c90701c040c400c0c0a00075217007098000980c40e2a10f0300000a10008203890707806980240da1a507065140c581000d800c0c60030803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 646155665 1250 646154415 646154441
    0x90c0e15010801030c060c081e030f0f041a25020f15010503060604241e090902151b06101e080a020f01092411010c1e11060a0203070909 60
    0xb84e42e01b049143d014581c0003c2441c85080d4040c0347c407170f030304441c0d00900c400002c480c0003144001c0200614020302c1425540c0006018920340418601940c2e0050521140d00c01d02c50700b525044046100300c548040d05180700e000740b00d1011046d0405010081d503c6130350002c100140d21584500082ca100511440c50580c0e4000e009456280d65590a020141100c4540500440141ca801c020030344a240c01c000044d00d1800100e011141456000b603020404640102d25001e26044400b001030303807011141c1e81c80c0c0016680300d03612241070b070f030210700803100702ca507440340b2400b5038410003060056192944058070090107540488101c0d044409030130220134042e5101720f0703120b501d800d0b0152924420042c9500030505d4200c04054894440e0f0b41908400c02668154450707061a200c00d15400001b420295007030300c0002c2000c100c09040050082544000700207009a90038994165240315140002e085e02550b0211101070500182c0013000350310440c0c0700d10000355020b20210341250103004403001031200c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 646156915 1250 646155665 646155683
    0x1508070b03072109050c0604060518040605280806100b03100512010b030f0c0105040b090d0f080c070501050a080403050306040e01150602100b091801090c0e1501080103 74
    0x14403961604650000e40003900b07110121501c4500d107190b118040b0042c296501012811800f01d01c0c000e1b2510701541000c80c824030b003d1200703101d110f60000a8514540781c0c07600802030b090f41680410000d10341d40d00b01e15000031390301012001c2e0070110314900c000800c0342d003010906181d13903d01d20354984800703440c110218203019008000410103000559000050445000e0380c0542d1440000d410710081407000c00180d450740c00d0700c500c601c0d0a01802e4141000c2d04094a41c580d0b01c000028602c0c480c074042c46615a00204512049496034080c01c00907940c40850030b08061028105010301e0b80000e0741003030140c4110500411554450f1003964041400e50311440800d4a581d5015201900005c02c101d804c11354444506582c44c409001c0c400c2d0401032900702181890400d0313030090404c00e4a5140c061401d05001d40d42d80b45881b9121110b50101d01402442321200c0c00b80c0400780503000e411009010841051004903c10701000c01c0c441c0103803100c0503c080701c1c410329001541c803041c09120141101a0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 646158165 1250 646156915 646156919
    0x606090103140114010f03050f06060604090f0f0c0513060203090904030807020f120406110304080714010c080c150f060d0b06061e03010e0112080a0c1103010c12150807 74
    0xd04600342100e80c01c0c204002090041c1d0382c8010140d0308000340d00101b02e11825550800a009084c4000342501c54103c020700010b1620030003062052069103d07100031140e450380c0d010f0b1f0245480c0c0c02207800016520090042c603881c05401000c54110350780c1524501c0580348001030403800042210444940907090f1101566141c0b001d40b141c040091400041d409424240010004180410140c2d4444500a170340c039170b800c0150050001600c0080d0880e0340c0c0c4104010321a120740000c0300c0702224500d4181428459090300101c1e4014500c0000401c0024041030484540c400840d40341c00700245006105401c0e981d035249070100c404142e070125045941000d1007004640300d0946140e11020140042c3c0c034041281400d1070300e0689801c10010f08131b90210042c048250400e000c41c0c0180401700c1041900d90090311440001e00c1048104400d200e0a4020340c000c20800c0e041064a0200081c002c00200c404140050070380d144541c080103100740b078440b4a03079203003030f8102003001660342000c02092414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 646159415 1250 646158165 646158173
    0x902070f0609061512030c080a02010b0603090d1e05030f2206020c1504032a150c02073503070209070c11010c1a060d060e0d110606090103 61
    0x9406404151006021541500046407032030040305201c030301c501c0c3d0020b1144a00d00c140701300b21004e60021080c80b040350126a0210b40c0c440140580c0c0750b008210155038800000c82231740104910030340c45030410004010030811620124080f90b0071004d94a0340251005851509004202c0c4074041002003031042c0046001c10740102d081b03a5000c07a222407d0040440460740c0b01c22260340660301115190f800103003190100000344650f41d2840701d070203810765150a151342c001e00385441c072500b0641440c2003a205000e00b100f0010140084035089550180c0d046041500c03a03000e00401c81c108009485031900c0000c4807280618600d000e0400f0558820078030381a05000e41440040c840e00040c03510040c801c40300503a45078840c903402164191a051140340303252030440a10f10185440906108030381c900f22001c910b11078208440c03010705284400d01540c42c80002001c010390b00b440500281d140c0b5030121100000004c950801340f12503114800900c00c40782c030840d541c5800302e4034180c1004411004100003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 646160665 1250 646159415 646159417
    0xf0b071e0c060b121614120607050a1707050a1107051e040603060e01140f09030901032307080a0b031209060325030218012d021011030103050708160902 67
    0x1500c002000d41e4403680c41c0600d0315141883c01640e45c1c0c00304100c10410000c13201c108840110809095401c2c00d40711604030566500c1d201c00402503401d0080014903060140d1240c4400c01100328007042a0030301c1d0800355001420390b04182a0007010580003108540c3e8440009215400c41d10010940e01c0300810184404280f6584840440d41203500c0e40300101c00903400e40a044c1c83c003034850700000b40c8194031a0302000c0891014144601d6000c541060100702400441211041582828045102114000030460120842c00c03001d005580c0380092004243d030041c40303a4003c0c030b00039909100351040d03641055100d860070f508001248404000001c62030808502441c0c0c006945d11b00d40146003161149090004010008500020b60005188080e004011429040c3c01000e10f001c8030301103620741c8100510f0161080f241c0008200d210721100c503600c2000040c40414600106200d0464411b41800710764000b8041100c103405500c1c4007103170b2440c00040b000c0d011003115006071060b03841c158001c0c0007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 646161915 1250 646160665 646160681
    0x130212030d05040f0c06051201120807020909010f0e240c0903030a0903020a09050108060403110c040e1b060c060f040201020c0d031205160203070201030510030f0b071e0c06 76
    0x2180000d026801d4848040d1007014410350080d05520b0700c402251030200b07244446604408103110084c05810400c4040b00300c03160640308510241c042c94003440c1010440b1b4050010700a511502100c104460f40350190092a001c103c031507028003840c00092602902c80466000c49583d103164800001d0a0555842c02e2a8014071a20007240c58400c2890200341164804a01000810714296040045040030021f0708020300c44101c04101550410811030b445000c0544050100a110500714141920500501500e00d000400030850340d00741010a0b62191105042d010340014407c1005013603090034412a001c0c40c802001810481d5905070030740076074400141050f41144200c044821598692646443e00140a600c4050303490b50105580ca040c3c55005001c0c102d8a00c5000034420300507000000d4940c41542405c02044550304c82c00141c56409040d4005030108107071100100501039001642400340301c042c0ea84800c1c4c4007103003140f104804000b00e111400280d0104d24507011030840c1e400890307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 646163165 1250 646161915 646161949
    0xc0c060c040602252103080123010509010e0915090a0203060a1e03200916050a0f032306030f010209091b070c0f05031b0a0b03090a080a050a03141302 66
    0x4c0d29445031148101654000c00c141c0300301200c00080e9091540106c600390040100c040d40c0c101680d210490000f00481800b6070b981070201c00b0600d01071a0307010300c1103200700841c0601080a00d24003401d8540d5803910003444103000304622000329a40900c540222481307104064007045e40e091810b0303103000500001413103d900e00168a040800000c13114560002c400d000003402c0c640c60b819200030415242c07800341424100b80c503050307081d0a1040c0c2000907035020400340e0615500d11310300f895058010382900700d0215103405120048401071540441054003408054040322001c0b0700711b41c1319608074440d800403030303900c80e03080c0c00040c0307030041d010200c458086240c2c1803450504006035910481300c041034012000e0309450200500850400700413942d85011383ca00c80e1085c110450000c039100110701d01510315411000000105041010850800a9030340085001ea949041c01c0c0000d006400c80c55100000908129403103202e405c07024100c90141030300c0d000c48160000c0507030030490a4640198011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 646164415 1250 646163165 646163233
    0x120606041203030501050a0b09100f0909020c15070503220201050c011805190305121f03030909051e13050c1503010503120c2e050c0c060c040602 64
    0x12074488602085248403038869100031807294103100c00c0169000d040d40180081b0602401180203a59850761090222102414a10001e00020708105c0301503842d6005011003600001e0498442c0000048408824210178040f01d92516a103208581d68403007a9a40302a03042014245681754590341e071081c1c6524814100607203070081e6030203e0350070f44841d214085c4203061100c100390188141886010501c2c00d400603d032034400000d070b50240c62030290303842c00e1060080400001e5101d094214034522040000c080f0f030701c0f00301da980c50001c2c00042d0390301030360152506080c046458034001144044000190311451500ca65440800302c46640c641d00c010f40b41842400450315183d202c6803c1e216042c09917908140c0c0c0d0358140404d2515080440c031a08849803000c00c200c42c100c04000c610411400c0d4400405005054080c1a080c00030101c1d03006100c00382d14060130f0003249103054004010b242c4503102034a4242c2c1e2405002c1d81c16001d2482800c0142e00042c200d103202604485a920040e90300a42e41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 646165665 1250 646164415 646164419
    0x5060403020a0b0d0623100e100c0510060f1502010c0804020d021503090708010b090f06011110020a03020403120e060d0f021303060c120501052d030a030f0e0603040812060604 77
    0x251b42c001a0b03c180e0202071000d8940005203071b0500d9050114840340d01d00304401a40c01440119003401c048401500801402c1096801042014490040025000c90003400410349a50b8007210040c1c46200b00c524030852094090030090060203a10f850203aaa22804019561a001c0c44a001d0007002c0c01ca0344100072000c09120341d1303000c2d0050b600070100d2100901d58142040b1030f4030b003190107116005204038120f1042200050400304075641c817100a1a0044d02c403214208030910f0700c00d800050100107800418003241c02d50313041d8007030002c480c0104000048241006426540105140d102c527402060410440e103845401d0703080b002c0e0040440100528242681098110a15294004607640b6031290a038064069209801c1c180d40c4034807038400c024039494403002481480c0b10b403d113001118140c1011201c808051340d4023106641d4058280c039454015807400078582c0d1405c0c3e4524012031207035032200c401c5007040c40a581c4601d601010701898002480003049990350002d0619900850405c40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 646166915 1250 646165665 646165679
    0x1806031119080702070f0305030d020c030c0102040914011e05120f060109090614011508070306030209070e010207170c06090406030c090209041406060702040b040b06071b05060403020a0b0d06 84
    0x8405a2020030ba540c02c0064204040024185100c50b4415801c9590703e000a0000c2074022040b140c4d00c100030000107aa0342c41c4440d525055000d446142400c0c0e501c0030500154034006034201410a14500d0307032040e9036a0f22040000103e1903601e07510401104901c0c02030005040060b41d07000102400c10131112004d0b840c100361807034a1003d1f001001071584801e49141000303100d02901d0780d030714002c2903a400ba5605240184400741034012180c0c04000d40c1001003220280243c0c0f15401030f40e00604000c130581f42482015008a000c40ca84900620401030b00080082c070b4150040340400051001d850031841c5041040310640040700708581c041c6d0381c0c50000000529034048032009020442025880c0c0b02c200c801c2100301d80c40e0502d2003401c8429142080052b50f10003080340c20301541140c000510075000000301e00100b10802c40d441c1c03c02c500181d0f410522514110020404000040983d204c80d120801e20506010300d10009402c00300380001403040d1011400980901920b450380010090740d04e80b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 646168165 1250 646166915 646166947
    0x180606050307022a100921030c08030703112803051b072102100c0c11010305090a06020f1b0c0a0312020c0402190e15040902090105160302070e0718060311 68
    0x10003180400c6c005070302084a403410359442e096103c01c3d40c0484603c0722503500e015010707070110352006001030400000104d00e580260f0240040d00750b400400ca84816608107107403404103189102d0075041401d042e1801c1c0d981e20900405110715002e103d909071400301c219100c082500165403c031802c41d0141200c4101044054081a03407040b154018403001d007401d1011011650700071409410456200b10281c041011003c1c1000e80340000c4c41c0014071656040242c03801d0440d0300300c004010350700000c0c5200000d4005000740803401c40ca21a5450500c82c920b00c125942c0040d090030642100c00784108001041d524120711502588500603509050700d10310004080f40d205c0b1030b10062230f03608400800007842d8801100050500140c0b07020140140b443c0c5110294041e07441012050740d00007c1034180c69108400780c2d44040c0710b00100600b83c907582e14000e51299810b000d5400030100c100c00140d08948980d1a4081c0007180e01c014000e442c1c10004124040c0c1182c00c8000c4115004204d14030741c22010301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 646169415 1250 646168165 646168189
    0x30f090609092706040512220b03060f0402070b0c0f07050609031308031315020106030519060507091212030e0d09031407080709020307090f180606050307022a 70
    0x440f0104031800c100390700040040c41d020240d80070303912040c1004005980061440c3c82d26540014550b182c0c0c0e4030002080c820700b0850380b000c20740c40725400001802040507024500500342207550000310650201400100d00a120028184e182c81b90045004030b0350090081500761001c4008501c1c120803508c3c0d8a1506030203460218a69000080b403900842480b5000741c0540380080c0a54545180581100400041401000309103610650319240c954000d5012074019a800001e84200350241d035402c03a0000e2481000ba5a00c03070a080003d10b0040c820f01c0e4039400c0d1001410811145001c0d500d5031300d140840c6001c2107050554624121020050411941c0c4e400200c41e910700708482d0662804500903220580609016031103628240120200400c661065420400700107880780e0701d0040c08c840c0103d507039020143c00280160041100d034825070302841c0d0b0040c00751050000a5079020200c1b030314402140c00d080180c101c40f2920786012002c14400c110103c00010400541d154000094504400d070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 646170665 1250 646169415 646169431
    0x3120c0a090e18100204151404180203040203210a03020906040905010308091f050909090705062d0a1704050a02040e010212010e0402010c0b100f12020f090603030f09060909 76
    0x10190104241010412042c0302c00a13400b096060a240c9802c091500160541d501d09004a0041103070401c10a0020394004280300b4200349505018103058100a60094030140d001e402a1b111205131702080034903012400302c000caa050300d000c04041d02140290082242968802820000020144101c3c015140a180118142c580d0340744100b0800080000d0a075040c8a88200c0b42040c04056400005880480c01c094403040d009541d0311400c5801e00c2242e4000c160700142c086200f401031507545907199044290000383c891070800d480d400c4c07082402100a030750002003000c0201451b84100d40d5180343c01c107120310101ca0752038040d940010300341c81c1d807810b08900581d0b01040038111392004240890050020f4210800e0314142500000c0818103102c8018040b8ad1210b80459a1445412210030003009002c14010300180c0b10840c51614112200d41a8480c81124810301c080b49040c460440c09900300a000354030b08508107050344d045400c070b1624254403100c103000780c06080c0c5074031100070f2180d220 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 646171915 1250 646170665 646170691
    0x4030f230607090b0903070f080c0109060315031e050109110a0b07170310080304030302060a0501150915020111120103031413050103110d150e010803120c0a090e 71
    0x42003000e49100c154000c0020032903211a061009854000340761000b0769521024082d0303074281c084040381c5465281d40c0984036005d500310002440d001c010400241c80380d000da079a401201d075107240031025580350102c1600690104041000001d505041e41d1070b4203161035200c0c0035440855202e050855407402d00a85944884940c1041607250150486000d0035032740c1c036020704007000380d19031402c20884030242c2600c1c0c0300300002041d007182003a40e04078000c09042003100d82d10b60710ba01c0c001b501c0788000c1c4e0707503161000d0502d00085810003201260b1050980170f5940e4404107460030b1030440800003002038103001d556950036135259100c5081c00401d460514118034040d954034514000b820214490001008600c0c103020714868903905003024800c807842440e01290900d450049000c4030300c01c002113002c0b01d5203094a40711074910000700b140100c803c841d03a05000c0d40c1c1d850700e60940f64422800d60100700040c001c000b4850702950005848486500c0c5407110f49142ca507424406d101c1400c0d03803c0c850780c0b02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 646173165 1250 646171915 646171943
    0xc01050304030c1e0c0605042d18020d18080d0f0e0109030c0b28050603031b1e0c280306063206090405060d081603090506250804030f 59
    0x45d0410140010074107450301c42d1901746424072480130200d911880e0116428114101d800700c0c410201c050002e00700844401c0045403061101c400298842c9a81d651414202240400300900c00c030310700002540c200f0340151500c0104400c020080030794070000006603607030b900b1040401d4424481c41080f1440b0752690010128182001079980c000100016a08148401940070820b41110008181e035441a00481e030754039401d000078210301403902c92415042c494001040782e108001401030a41e00800c48480c1d6242c8020840341d01d235508845999001044800101c41c00c1c3c001f4180702c0403416082105444890302e903902c5100703aa600743e000e00d45810300801e42c1540c843c1855034480c001c0015048000c6480c915001290b060700550309024030943e03960b0000340300c41c1c4540d2a0321600552061b441c0703580300d0035a800941c0800700c1420580018a40d44400315031401c1990482d4050716802c3c89003000044034803801201440d41d03580c21a00840305200000001d8111000102c01c0307803003170030383d1000f0003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 646174415 1250 646173165 646173173
    0x5010c1227120224041505010602060c07060603080c1501060309030c0201080c1605011d1f090302031204080d0b010e0f040c1701090c030c0f020c01050304030c1e 71
    0x1452820009007194814121104001c0d500140326109588000080514440c001080c1e05042007000d50084019450810855890104484911482c03280e0844a0395095a01c0d1200c120380c400d02948000d80d0018000c1045000414041c00403c1d00c611408122143c403a5180c1004d40c2126510952550224040d912001801c602060140c0990310b02040072214548004210000780d80b006411f01440402080b600c000003421241ca41104c244c80c5600f1680a14280e030080107003150030485140202c0d0100c070411070110b82205101d81e202000b29040195541020041900510840651004021000800e0301500c6014811070040c0411611408412008000c0c1ea1844031060f04011b200c84600999550365101380d074488401b40c80014020b80301c01003e0b02d0b0149541110061500c0030000001c0c0000f241c5c1090400c940c4a6800b4008400d003100c00b501e00160181e050005600070f032801c019154890009540d000f0b003e0314190803114010b0b100c140010600d05541c21310390910350910700902c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 646175665 1250 646174415 646174421
    0x30204050a0612060509071e030b0c040801020a090f05041104170c19030302010506060903030706200706020403020a1a1c0221060907020d021b0d0b010b042412020304020a0305010c12 80
    0x81003823000f0340d14042c050180c51500f00d03520b4080204588004008140e4203e81f4100740c070058290400219501d4034140d0000d000c11b0003610610f0850101e00e00041402d0516019086503018460702c0380d801c0a040c2108004501c0c481042800b06102c0c0701c14800603a0386001c1110840015841e0341d022003800d6050003030035290000c201074020042041240e4103520300000729186981c0100c2c0000c0c00d00c4010030800310f2110b94800013802a03c1c041003403010310002e0341c014070444e40f08460020070713607a458481c0144142c54440340c0030064800e002e54890000380101c504010350b614070006190501104c080c0003e0f412031800c815603181110104041da040100c01190855403a00040600d00411a0000e50310020707000c2605440c0750421080300c1907204d01641011059114080340c240390b07121114035500d0340161140050100c000001140c0714141411a1800300e28140d03545254107545400d020f020394000780c0200d030406800d11002010070000c0c811103d1000440c0c0d140307503030b000c091000c980039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 646176915 1250 646175665 646175669
    0x112110f13091a09100f090e0c030604031b0f0209042f1f0c080c1f0b0306060405040213050405070501030c050306030c10050403060c080a11070c030204050a061206050907 75
    0x60b45140111036003d940090880703c805850858071080142d07608985c103c41e165240d03114003000d45424402160100558200a40c44070050040701c500000902c100b542d548025540600070494010500c414511807030040c1f103010740100f0441d141c018072540492030380d802c101c40545522594032000101e4540d80c0a080140c40035803a410201c01010800103544c0d60f0146003512034034211030f000000242e00aa000d81200b03600300600325220b120b54a2241e480742216541c101d1075195544a5840701d00e03441c441c500405001400800c4550f0355041031000411014109a038400e64032074606402207014014544680c1c491005058168a40000034040d40d102e146d14109204060003000184c0d100020854003988003220191040011244180c4441c4903580002d091a820400c0450446401c0f1903664080c02e401001005404442d4000702610f00681070010003111104504002501d416041640c03c40081c2d440029810344d40d80b040712040e0030400d403c4983c6910740c002c01100c00010300c403001c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 646178165 1250 646176915 646176929
    0xa05070b130b06190503030708130608090d0807050903100b010e0114030a0f14042a080c01030c090b041e0e220302160305060f0709140112110f13 64
    0x1c0015036201c41481c003005250724000c011140000c0001d4051000c0d5100900003e400c0da45d8070782035801d10110300c0d4454105684500e03e884070010f4200e01c524000b03403003011500064007072500943c001703c0c1d10307000c0940014200a8103000d80c00785070741c1c103124120066050383c0c000181e010011001401078000e401549050010968031041002d420310300700d951246040c800000d2050b01055240300405058800fa10f559645600304420011490311502d0914414000802001034140c070104d44804280610020398100100b01911540260000c3c00e0900650130451001610340c0032074503079034001360f00c5a600098610100c524401303425803658003400c0c50030002d507a6031608440440c62000518040952001420003c4040c540f00b070084807010031980d03000c403c40320346c2e81c100340703076994401d840150b19154060081203e080c041c2d180b5104503810100e01d42c0c004064900156001c0250800700c400341c80c0c8800300b0752006080000248008100c2180180d2a140000600801e41c1e2290300301d24 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 646179415 1250 646178165 646178191
    0x1d0907031e2702060412120201050c311a0409050a150308070c031a07030c030b01022e1418070b040e0c0c070b0a030b030601030b01030803040302030c030a05070b 71
    0x2004450400402c0301d50300d28a10307814080c4005901c08211603116550140302ca400443d02c01c9400c00406003440345c4a04000ea0080c081f64650031551b00c903d10840a117101500c60b1b81039203200b4041d03402030500e0700c03089144035540f290f030f5a1003620701ea00001a40c49000120001803e000c1c2110390311920350040c0c80034500700032601440c0000072030300c480b40c040030f4001031002c01c00904219031440e100002c1c541c042d41001c400c09003c000098041001d880e05000b00c0c1c148150111352a05c40e10400313070b04000580c010107041207007894049a0320040b07050b070380030700390f504e03c81600d10119402083e0041100a00503c00c0e442c01e900520941407030501d0810040e000f910301041082451815182a15499000d10074192900c91111814bc03180b81c203588018050210300048006d101005000c009400f91014050280390034109900c41d0f0b82400014003c070100d20051010814803000703141e20911900407130b031501031400105450758025a0202e00082c0c40010050104006d40c4070980d00280300300861 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 646180665 1250 646179415 646179431
    0x608150c040306020c0f0d0909050c03090606100309051e07050321031e04030309030e0402070302060c0d200408010c0504080619062c0915071d0907031e 67
    0x211a540310354032001d802d0f82c2d00401e1051508038140616004541d007801110324010030040c0c09480203085101d181c40c0185014001049205130500722841510312401420503070341d6220400c49c149001c88500400c00da65480540005101004481e01c054604169804c2c7c0d0005210407238502401034205038040d41045501c0181041c040040c0840b48512181d0503440b5583d0780ca071481080c00c6024010112400e41c0240b105040d0994800b4001e580241e0b50b0072001403c5100f440180d00c1041d10060069101100044400380c10b2000340024042c05d075404a00354500e8200d07504255100c1c031900f240240006010440c01030248104c003100c8030b19017000c82c140b03841d00300384a8450200a114590b22a0005684c071021300b100c1d4030090107014000f040450f81480c005044c5d040c0b0b6a40700700c07002c840d00000c02103105940d000840f0700306581c0c006150700091f50380713400c1201c43c2c894168001c0c5e20301c0d11144800c505a9100d181041c40b408031a0b90000e244801c0403004e00000600e90300c0d800c005450b00c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 646181915 1250 646180665 646180681
    0x41727011107121509030522121713030506220c03080a0c0501050702101d03071401090606151b03020715021c2c0a050f010e0310060815 60
    0x10303540454100c0c510300411440113003007500d96084100c001075082440e0036040001c2580110190200b07581400840254455aa051101d0f4441e58010311012602d020843c1d40041c41564031554100180c0c580c0a0500c02d001c02d6098041199400c00c031099041002000302550551001c80d2a8190b01d25020301e0340d02d0b06842d1001009018000500040000124004182e00846400c0b5010754440c00030040c51600c0203000352200c61042d88401c61a003400c54050365030300e440441d0302c41301c0501c202451034034007166100b0090720068200300070513548425121000c621644078003001003840c00000580d480303803040d00505400d002e030341d102d0700c0100800301c0001180c1d0004aa600351080d0500c0d003080d03d9100002646804004904011007202080ba0f510445500100f4454449024245d103408002d410950800da01d6280740c6650b00000c80b010700304920301c0c0c11280203400440604011440b01685c0d00460b0501000002c020089519583c1c03c10113110100301c58444503401c040e00041500300550703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 646183165 1250 646181915 646181923
    0x15090b0a020903010b120d020d050304211101050f041415240406170f2b05120438040605100b390c090417270111 50
    0x41540e0540d50302050003038243d10300358451341400c04010820318502d601c0d1221035a94003c1020843c005014400c040000d250240050320700841d40700d000807000c62010100320030786001686111080003554100d052141e042031141c60700841041c050f040c3c0c28501810214108603103102107129952156010310a80400e038940c150300009008024100c00c40141960301943c403180402c290711519003800000c42d200804100f9000c04020810360741003181c0c2d00c0109403681c00341c0f07541161f001c01038010041e590b11040800e200000c518180b650a000c008203e500d10b5400c1190111003490a108007514824400305ca15110402da07105070300f10809014009198004001c0d0000b4500ca8a840c04a542c10f000481c04030301074030902e450642c840c003521702944410703100da280b400c10001d007082015032030320302001e00d42c40c01048901c02050032a400600f0b002c0207290060054a101007020340480354070210f01d00404e402494003040038146120082010a1840d48251081c140000301030440c0d81100003003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 646184415 1250 646183165 646183171
    0x306020a0e0d0302151008030a080103060b040204050a060503100b0a030c020709060506120402030703060c1806020a020f0d030e03010e0106051c0b160c02100c030807090b0f0a090b0c0102040315090b 87
    0x85d0584c4548800381016003414054228040a01000c12140021584070100741e049a0150506200700d070002d009001c124801ca005180c0c0140d1403003000d01919008000031600b100c5050052004c035070740e809003003007160071946440c00040d0b00ca4000c0a101c0350f04000e04409420740c440d0400c103491030000040d40314441e4100d41c03540c21800d000010f081d950140844001141c1042040c8045040e030400100203001401084008541401c1c001c80d12510004854011581c054900160744000e00c041003030388030004400300c1c100207041c8080c2030741d514203004052090807148004120b540c28603040250b00c1c07025004d608022818444c03a500410f0f850040036410095804004441d0311000904480400c0002400780d0007486400003648040d0780090100301180c001d075180314140d1507000007100e00300f015100300d02040c84180b00c100e2050811a00038131008059003043c00c4541c4c2d076500e91420360f030444c056022003030f580824100b041c080440039052040000c0c01042000e0840755445012400d006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 646185665 1250 646184415 646184443
    0x1a120d0c110a080d140903060c0306040b0406080618010b060a03022d18062a0a14030318192d0b0a0b03010c02100b190306020a0e0d0302 60
    0x200d50104184040100315045404000d00308a01494072044820382e900d44040c40d01d00001c2e10307803814040308a0007005a071560b01c002806006940c41c2d0480c0300f070082d00003074884c07540642da800640e0706a540e5441100024040080a803d0501e40340412004651080c0240601641815544240d40d947c800454441c10000e050040e01c400032400c2410400c0c216140c2c82d0b031a1a4010700c001c0303011344004041c101c8001d400c1146403d402e04542800445d0040c006410700401000241807848003691910b24024040c80048800a407115118801c1140a010080e40280c0001040c05103012000b60360790840300812008013180f020003009426441c0041d08040e200c6142c8440500201000b003402407034044801c0440c00c510815070400400400c41a1a00c0790301500c0d01411480720704041c001d440c030200c400c1e005443d1810300008040b010382094410160f005440c03040241c0c402c0c80c1c201d03401000d540511f40043e119a003034500504403404468009100d081512001e80019a000500e100c00b5004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 646186915 1250 646185665 646185677
    0x303120415090b0a02030105241e09061c05180d030507051b0c10031e0f18051501080601050907050c010b060d0c120908030402011b0501020d1a120d 65
    0x141c41000006101000c0000d042000040a0040c90100e680185040e550204c840080c8011701400801c0713580b07280c84008480e13642c184036645501194030800103014208859107440c0403030090010380d450740200f030103144103c441400c0307032441051885490361021900012000c1c60107030b150f005680e511880d248800301030701c540018a201e480b9000352900c0040c042860f40d094141a0b48490b00c984a034203643e4001c000c3c0c81008940360307101e405020000c90501b2002da00c8500030960060103800d038001034032203a40e201c08a1544d51091417000c000c0c9a4040c0c000740082e0703154103032291554981a44803000c9503011500500c03583d0365082c0c0c015044055400e10a030b0300c11011241902402d41600c45551100c0c0208118144220f2500110b100246e40e550b07c0e0060110000c051044410021000e03080c071000b0f0000400550245c542e20b1580c484c1081c0c0802c1c0c42405503210fa00307a071b00c0051060440342d255a01d8090b024507100c1400380544040b608100d04200301545260303101150308450b010004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 646188165 1250 646186915 646186943
    0x2306090a21061506022e020a0903050a0804081903081909021302251112150a1406010e092e0f080c060a021908090916080603031204 58
    0x1100078031860006500c54000e200124046002d00c040ca01c1904c90b04025000703c80101c1850800305625401d5001d481144038400c84c1d241c041034000307412030b80040d01032082200d03020000c60400c00c501000c0b02c0c802c1c241d085d55a420001c02a061202041e070502c6a100803c8108000a0300004030962040c0061150200c60141e03180c4040a014a0703640650082d05000c0302d11491201c940052124200c1400c0010109001c03603010703000110f5140010303028072283d2040c0383c1503240500551a4240303c2d04200d415490846503054001e000c1591400300c2c041e03a0700074000d01a8204541d0075402603003420842d0b00200e4140c0030030f20303803240201200c604100c1d04c0c0340795803600140d0b50200302d100341d03264149d90301d280c6408007071082c01628055419948186c0d07075540c4103443d2440460784501d410340c1c00707407011090482c1c8074008200c0c0d09804540e82c40090065210030703128250418031602d40b20034a1074140006220240242c2005070120780a604100314514104520010094000b6030003681030403455 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 646189415 1250 646188165 646188209
    0x3010e040f0b0f0a0c0906052205090c0904060605120f04051f0f0509160e0c0d0903360302010c1103010501080a0302120315010e0301060f2306090a 65
    0x12101d840020042c4600c0014400460010f1030050310460540400308004805c80d14240e44c07415140c8100c0d4001001040b80e910b20a008081400407001c0360220445000c1e10b070320000c0c844907002c0300d03000101600854691094901402041e0003001681003440c41e02405480002000f00001c2542c180c5075403a1317001c101003040070042d04040394201d10f030702100e04180c007e43c01c0c06032660b40c0000500b141403401050402c000800c0c01c44401041c2d01022850500d00380e4400e03174200006182c40e490342c0301400035041480c0351b0b019401c40300344a0356031007648680780380050601c0b82c401b00001120500700c83c5401912820406e0a41c2076903024208503503014503034681705102c1081c2c40d2181d0303055401c0100024141d840000e00d41041840394098031221404c0840c542428002199410380388201e500e082d1000754015140840e82d0f0b00b0241c00410015142c503c035070075036036081e4811500e240017091594140c00301c803458060030880455007249007100c80b40028495403040e02480c00780340304030759044002c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 646190665 1250 646189415 646189433
    0x5010c110301020f0408070f05060319140f041406010302011407020f13090c0b03191107050a03050d0c020a0f03300b011101020a14030c0705030316030c0c0803010e04 73
    0x305002802955030328100351030081c0e40d401c544940142d520801c440803031252100458142a03a8000e08100d040d07543c0c07030101504104901c807005c03612542d100e21080c030340c0340717044200d43c410300000440c0c0b58141080d1500c0d0043d109014500d540b1500f11100510050380c1c440c5402c00c00281501a96803540002e00000f9800300000c44860b030710444800301007035503035100e07088000851b02601d880080d4540c2c8048400300c44c0300847d4000c1d4101d001a0140c1c105001c5503004c0d110b205d441070505402c1500a40d078540c60b00251000c142c1c00b10f00007261020100040d4010231020030031910140003024410380e2000d800d501040e5005042c40300380d448806803030200e009580400c446603201540001008001c00e001440c40303590950014080c0c03000d1580f0001e050080b0394425440baa034030b609040c40c400c244045500050a1000c81e0300082040d400804d83c204055030140d80780d03414170200c81c03525400142c2103580e825107150074020104140c0c2e0120700954281c0f0704440b40c0c0e42c03d04042e0390311890001d00e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 646191915 1250 646190665 646190693
    0x2040902041d07020735011a0f1002060a0e0f070303050301030c0b0913050903090612091501030b010b0c100216020f030c030a08280807020111031005010c 68
    0x11031022600250304a0480d01581d2a04681006042181c0b201d1604a071280340b54007071102040d207101c404440380502d590f410b241c03800300c1d0000003140b2040c0840303a030300b59280305100d60040c203450400b03a40030b403500c81c21050007031104484410300c44500500c042e403200ca006100040391643c410300340710380c03030810720400000300003800a40381466100e1801609a07002800107079030700365250394049aa079880780210340110700000c04014015610840180182000030440a024003003800324403c41d03103070300014180c0c1555500140e4468a04801003d20f0310901a403c070024503c088010404251440b0800b81504c1a002005542d034541501c51460a03600300c525000c1d5510004190744a11032803d50414035038800c0302e80c03030345c005000020143c0d61031040000030791640001d000c0d500000e0b1848000c10000d0380c1071301c0300c4842459445440314082411888840810700381c4003002078a660a200d480e50000c0d00d000d0803410360a00d0b44269031840d94500409042c01501044201842008649031503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 646193165 1250 646191915 646191929
    0xe190902041b080109050f040c050603070909290402070819021c0e0f010207230d15021b1501030201050304050f0d11070e1302060306220504200a030201080a0204 71
    0x10308004142005000d40000d2203820f01c4d15103001c02060410b958010703902d001d107812052822015090ac81002204c0d0720142080050110030003001440b00628040d4081c0104500c0302900d0080d484121200500360031116240305510412000c00044c00303071800d540341003400c0c80c4000107040d81204280d240191049051030741c01190110840c03050362080c180a86100280d90700500f40b8540401603a0302c088c0d43c043d011014055003150000c43c1d202090000d03991600401125840b080e6031100c0b060300c0400107894003e10380015001c081c02e0180000f074000580c500009040c42c02e15000384400002042c08004e041004c0003010900344041000301042e00a0040150b41c00c4182d01180600034801a0000030001e0096600000d4110381000346c0500c5204803906504124041d1303030030042607034002482c0c03d03800400380340540645103000600e1140c02460060020301d50400b0b05103039a040c21480b0701c4000052074161410f145849a545407002c4950a08000d00e80391944042c0902034051904110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 646194415 1250 646193165 646193201
    0xb090c220b1e1e0a0314060a091113030f11060708070f1a090d2c0d0501021b24012d05031b0915091308090a090b03070e19090204 57
    0xf0140382c110a005012500b22a2010001d10201030a4401059000c0344c0c4070b6808032420408201160054001d20702802004043c2403500820b1203140308500581d420940f1040160400c1c5810002d040f94681812101151810704010040c3d5500c0060b03c10094010200e501410f0703403200b08884520b62036002102c0c0850f404c25841c140000b1035990305903056400020b04854a07802c90f101c3c1c642580c035014890080080e40262400c03003804050702d40c0000403141590b00304080d200c2d0122140e204000c00c28003001401c0c00e21413810a040c02c4d5496007850b130198642a1004101402c2c241848204070504898240c0c00c2d001d1003040310172198687c0d0f014a4150098442107100f2004203201582c8201c8120351000c2d840e16500d4200b0f901000004074a0b401c501c6040225542048907030703560340302c030340300701010703441c020490780442c204441551020030060f48414a840309071030140051009041111102c1c0d0f0246081c10b00303813841d01c0300c080c8180c600c3c0b95140342c50401e41d143c0303070000105070304031806d64 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 646195665 1250 646194415 646194457
    0x41802120138060c213601180905100306090b0106020601080d0f03051b0c0109050f060403020d0c0c0801060f0503011802060301061202070507060503090f0a0210080a0b090c220b1e 79
    0x8880c007410906e058a20415640380c2003598012002c41102a8a20000001081c109000350008050282c60f20000c0b0265541c0000050624040d0842e0790344140c80701c0040354944003010f0310308275068114100c2c6400c030400b240307142e43d40f081c114803444a0600e000724142d11880501d011b440d042090300c420300040040c3d10350f1221415000008854441c00446186521010503036448840c02e842c01030050300520b03000c00c2d40c40e200c0c40500c4e003a54056203a20070203582c1c41d206c0c50f08441c15a44000340500340c024080142c0d103001e01c6008400f80310414045407488081d80011a07601c0705015007010f1101054803000b111480341d058800b91381d8450111104251144000b0b412038100f1256142c147c0304940071403c2c02440410f43c0c1da559035001e480003501324000d8405488080c001045600c2e4103907500d944480d00d9449104003130203080c1180c010b40e40c0d4500e01c00807001e83d041010f00c2d0b26090f00100020032403a54004100c0742555603040500750b11264026940c240340c4203260f42039258803800031070703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 646196915 1250 646195665 646195717
    0x20a0f1d150a06020f0d110a030e120303240414010618030f0b040618051203062b02150a080114151b0c041802120138060c21 55
    0x42c03800401c0c080c1c0c2100e08a00601e02c041340c02c1400c3c100c4007909904202a0307923000034041c0c0c0c071500d0041801080c0e8107425030341500c1c4a00e5500103ca144017122a610b055441010300f0f00d0380f4102d0300105681c01e02130030f00f0b9130004015014040c8035100070403d400041c803d2448200c0000000b66500c059240c0c0301d8109810803620580007528243ca145190001440402d85200f40307051941da072042c080c00505070440b004400e0b5400051005130861900440040703070900422040e00c0004240b080d048042c034103030040c03003050402c8a4844009800c1003000f2070280b50082c00150446855a8012044400764000b00d115942cac0c600402a60301f43c04034621210442d007903840300c040c210200484400d04503513801c10007601c0f086403081c0c14890b1101049005030130442900030b0001902c400100b541c11001481c880c0d00c4aa9030303040c034028198469010000d10001024cc40310980486125080c6000030203171580711094132420b105202c4140b49560300f080c0614041e038051000c40c00340240e8904014507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 646198165 1250 646196915 646196923
    0x30f0e10030e0c040b0a0909260703031125080705030f03220b0a050a15080d030e060105090c310603050a2a090306020a0507020a0f1d150a0602 63
    0x8000807031030082d41d00e030102504191042044071940100b00e82030a510b447c0303041c0300501c5525026141d01c60060b503005255080c040c01c10807140e14803500f4070360303a441c1420003c0403205100b000007c0d8810410076981402c840621060417000c108403070003003003029842d055070b0038410004001d00b2800b000c04d802180804041c0554400c1007041104c05040700b0003404007818041c00d48009000c059050007240c041240344e030006902c1442007100046000002c50080441c0c10306078031002a550044540c94111a414007800c813400307003560001d09141d410000011134210f402040040b05940218a8401850b070b881710407000e100300a01c460381c42c100d03841c115850004c030900460011904110104480400520950007045c07000040032a1500102d00c040c101c800403210041c0400080e200d01001161049c802444030081707540383c050f59662540b050101508240c0c0c040000c0b4030364508104006480d9031032903d000503110980a003103980d880306495800d46041c80e0f264100440d80302c00300f01c150b0002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 646199415 1250 646198165 646198181
    0x1314010f02070e07030903020a020d0c140609060306220509060f090c0919110315120d0e010e040e0a05010603110a14040510170c0a06050a0c030f0e1003 67
    0xa40ca01801100100c8140c0c0d5480b40d038820030031407044100c0080c03490342c4a0743c050b48215101c4e10640340e240b8155000146080c2c4a4801039654801702d017020001819140b100071145002070b541ea90912003804005038080c040144a54001c1000c2c44240c141b00c11090281c0100c1041c20348104094100b203d01e140c0c2d109411200702c000c4107001008256120030004446200341300081140c060b0b07544e4800d6034504207002c0500e5800c019240d440044d1140e0f0018055841510640d940320302d031865030320030072003a4404244e03007000540202c01c0703584800d9404580c151085000382008480010040e0103d4003c2010b9191303000c242c025018841c2c00c02c0740c190030032000c4a0140d03654400601c0c60b00c0400c000030005224222464001b660100c4480c00c107600320075803140e0881410258a6a102458501a040845070440c04d82000380c402030181713007050101e40a0a00303443c0c40d50510050180203407409488500c041c0078010104400383c4460f100d2030500e4040b000242c001c07884161040d074040c026203540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 646200665 1250 646199415 646199417
    0x9051314130b0c09100c060219030e280b0402030c0d050a11030c0f0904060605040c050a02060705040b04030b04062903010e0d0801031401090206040f06030b0901180f02131401 77
    0x10b00850b0710300d40e41000390f0320400b600a00c3c4105d6000d40b404203541c2101034075030490704190244450b00b5100c10000c6070300324400303241c2c4021803031801d002030781801d101c611003218146840460f01e09003c03443d02c58104001580c080080c0030a0b80f80ea00000f0b1922013030080b40c3e075001841c5200b1004011303010903040720140c85800b1120b03050002400701529405c101e249260807100c1d0a403410251b00d000e80081360054080c1100192050315030740414281c1c0e0031448588080750000400c0c1102960400641d40d10032032034540340e801e0900304180700c04180319910025000801240c041003c2c003e40340d006280d01c072700c0440a001603c0340190180086012102e01d60b1007546805403907000da00703010031346d40c0220009545c1c20070070360308556402005405c40c3c44a00302c10f658403601d240c0140c079190010300140c502c1d038040e0a0303102d1412f40010107407004e82050500404c1d806c00100120032900b1211400c1c0b501c0d081021544d901580c2143d07000b40502c05606900b100f0032440012100c0361100d18604160003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 646201915 1250 646200665 646200683
    0x90603041a0a0606020c010e0d0f0321150302060a0509100809010e03040e0601110703240605220507030906020f03041a040b071b050f0f100902010905131413 69
    0x100d18910b0100d030031501c00e21001d60401c00d00640290b105281800c45610000e094083c0d24605d0744480403c0e021802044010510100140b8201841c03817468600c4011003071014090030a0300a9003216900240c80001d006050218100000c0740c0244165481c0e180050304031110419800802040702c030080d2044a115442c01c007501408610100444003501c0501c001c1e000e546e26a07000458010102c3c01c0001c04601075108040f002402808824403409418644c0304030407010591800304489a692019108031400c540c004044c007840804003c014004100025055807144801d802a08107000001c1680e0f01c00100302d0300b044080000303140114011565110900c280c08001c0b1a007443c261006402c0d01c07a003c001030710461080700200b4807012010120311a01e6490368485c0d00c0c0c20204100d108a940200d140a20f01b1082004241740e0b20840d00418081b011a4ad000030780001a940100b501a0170140c85010b078510171394001008a0301071800310401c51802205115158081c40c0013100c0080f5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 646203165 1250 646201915 646201921
    0xc031104050105042912060301141e07090f062106060c0f11092406210603010615180909080906090f120705031e0d14090603041a 57
    0x2022415030301990010b860390b80c41c02d41031280c00311850441d10004084030041440005485c00214040d0200e0310140b81c178090642041d801b0107082d0786120703454a050846000c01c10200700c110001d041e00010300303008120015101d0110444810150741c004184508026200140d0658000504d80c03624525021a080c0d4607c1d100249045e02c9440c0706800004104881040c041000880001c200910810140b812011080007007210408112990405071000070202c0c02c3c2228444100704902c0001c680b4245402c144540c08840300c071303034200030300c8c4401c03206400200561400d500c418080c092031b14042c10005820b000050001444243c0e005d6455944130000407811a01c0c0110303100aa440354109080040090620030260009080c2c95400104448030028540380c011a03410b4100000d4064401e003814941403501d807c8402c1e00c0207008548000c503107018044082403100c0700e05c00520745480e0403550aa8144428000c180900741c0c000c0d4004103200c10014000d40741404628448002c0256035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 646204415 1250 646203165 646203191
    0x18010c060c090801060806130215070b040b0405010c090b0f071103030706020c0715050708090102032107030c020f0c0d050304091104050901090e070306050c04090518161a0306010c05100c03 83
    0x358040e54040411300b00c048c507100061602c2500c0380d00b5054801c08003402c01042c0d0b1219401c040e0255410b0b29850b480340280b0003031120a0003508844011420860341c0d05203454000c3c0c0242c89102000f4800348008a80700003004140d00072111208070081c2202d486062504206000b5401540c2080c910701c0b41c40e00001e501c0d210103941c02417402180d19810f09003c1c2c6900c605156510000c695411800108409442e6030b00c29000302e041e04549501c03801f09894512000b80c1201c1e1031441c501c055503c96194500203510008091112100984a110900711a03181c1035144d40240e4002c0b406990606044030005030036a80680704035602240e1078242030341d84021540480d4064900c898281d0071000c014404182190010303600984c01542d400c0ca416a1516808105c0d002596100a00d00300d806802c0e0700c0110070005038441ca09403c0480100c2c91a00004c4440d5125007240040000f00200000e5026070090070924007a94001e800d440c14038801c00f8041004201c5012010080f901e80f43e1911001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 646205665 1250 646204415 646204423
    0x105220506011a091011070801021204140705030d03020d050114130c05091005030a0f0501210303020d0515030708120901210e100e01090818010c060c0908010608 71
    0x9640110281c00941d0030480301e50003418074402c00d800524010003208a03140c076400614018210280e6800f041c1042074284503081200c1580010307440d0380103205d1603020360380e0b0341c03503017038021350b1010300242151080743c03103241000d0665021907418013842081c842c1c41c942680040111030008082041940e80302c80040e0120300310001450742140c500e4048032810145940441d49100480c10442d041a2400340000c1c110f2a07641402000500c001c003d00c04c6000369406041c424054489040c081c5606182c04403811052122403581c58240003983c800505021b541100c081a00ea500180302a142402880d44425481c1d2010350191055910004003000c002c200c0400c0a400c030030205142c0880070700111861002000141c1a00700c0e2131000c00036108151007600c44000441014080000140c7c05060458115140601107a414004800c001449410480c5e80e031100e20180101c0214000c401210362072081c081c018485868145440d5440b6041a00b100071500c206000380409501d03203480e80e0312 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 646206915 1250 646205665 646205731
    0xb0405070e0403210b270f070f181a0a0e030f0d0f11010e0c01080717060105280206060f06120106050c0a0803010b04050a090e0d0e04090209090105 65
    0xd450796180c1d040c651416401c1c21200f28001e101240c3d5042000000c0c1188035000007140d04a121400784144498006c4505607001c41c0e05200c140052420840c0501125030b107414040401c4051100400703003a039280c00c5100505003050713001e03016070040003403003000b64099082d400105810a4080c101480c0000d60142000e604c1c50140100c2117800742c0036204091219035000078480c4011b40d0310311050003480f500f445440e5000003013080e1103090001520310540500f88c041080300078405068110300301d40b0301c3d6070810020300c2e040e95200c451122004d0200c5c0f0403031000c1002c0303641e00d1079550120750000b00317030b4010b000450391240f04640f0401000702500c9203044651101c092100104940350045002e00806403240060391850713845079075101d680341e0090b0495103181c2c101007002c2c0807600f00100141c02400d10714030104940b006505400c3c2d618290307c070810040007056010138a091316170b50009409250b002c3d01b0b81c4800e04244581601038007084860010b0b00408880041d850060b8100f5150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 646208165 1250 646206915 646206917
    0xb03040f021f0e10140c0303041b08070e0c0c030c0a0c0f050d0f05030c0304030311060a143106060302041a1305060a03020a031a0901020307120b1201090b0405070e0403 74
    0x90b00e05032010521000100594801042c03140e0005480c2c4503417103403002402c410b4007100c040c642e80e1500d0f140000542d100c03108440790b402d99240781031084210014400c01a02c40490340c4051540d80e115410101703120b0304000010780d02010034403034102a00050040c01052048050034034544d00c500024400004a201d519445210303d2882d20104a8240340801902d00600503a0725080e5100c4001c0e1866119a00440024041c030f40d5840c3c0d158001d021240c0c00c1200141d0a2010031125084c20540c5400500380200d000c210b1404a500c00310140340841602ca003141d00d824080c505814003000404041c40181c1c0210308080b40b02201041d40200f900c018480113201d80d1550203106990340080000400080d00211807503000b00141e920340450100a40c8215100e0260040f100b400c0070b0b07414030103002110a40e006109000e585a0404040307001c0b0540b075440080d4001201c1c00081541a4040c142d808551810820100344030054940b10310550140703080b68402580c6402c2e4106080301102d01038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 646209415 1250 646208165 646208177
    0x70308010608093c030304050c1f0e030a060509010605040f060f0e10030506010905041a0103022803150c110303070e04020d02072f0a03080d0509070b03040f021f 71
    0x1000e0a84010341c108100c8290b4411041d5400500410a800007040041c00085e40f0100c10001042810802d00b0350040e001c0d260f02d15841c00d5000d151409941c003041447c14410040503a102c05e4500b003200d1410b40e6002182031141d03013402c03030707100c0e00801c0107004035409142010861103134010306009610445180c5203074030610b249443c14103031405001808010440d490302c500000803984c20081203000e0951220300040c40d0916203003066030040400015803a5025038401000940d40b0860310606130300100c03102d0245d1101c8040185449012500700504841a50300c840713020001c154401c0050010580b110b6030440d89010780d0b25039a0004035003002c0051840404401c02c0d0802c1c0d006081d10fa261036501506020842d0340c3c1941d000d100b00960038a03e8400c1c0030314010400b50441c000c5c9500f100380d03080603d03242181c0302d0b00302c240720315913180c50555116070100e420001c04000c00e500500b07554441c83e031a070a145c81c1c0042080061982a8030a8280c41c4522803944900303031001540c02c043d074540c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 646210665 1250 646209415 646209433
    0x504060608160b0a08090321060a051e220912091a09040911180f060d1109060a210b0a020a020d0309051c0314010f0501050d0e1f0207030801060809 65
    0x2150303501c0008106d0070709400280f16081420382d055120410b22544107220542e540b4040090112000c182d42c07200780314032000b00c1c08000000f01c00c2d01e00d0408a10035180481207071410901c072061424910010303161030389440031400500c60300340007a00301e070100c81d0303550118a41e440c40901c3d901501d0003042400081d0411909003039140561204035802d100b0240c07500301d0012007002540f800000402510700308076030070400ca007000f0200c0402ea80700c4011035030403030300307071590340f2a242400381d85a1600c0c040c080d0017020175615521800504003e03d40500140269802c0e000e04801c2011050001c55040c41820041601c02d030850003591114061540103090400c13030f401045000d0700c0e100070203880500a12449801102415038081e0b80c1d0b1700700da10003242c06245002e1203810404140c0c0040c0036040c00d03440c18003c1d680c2c442c0803030ba0082c19020300421034202d00c06000c0c1c2001102d80f059100f03541c40c1c41050010101c035402a00c4410f00a4844c9081a039840d5000d8a031640100d584c100c07550000b00354 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 646211915 1250 646210665 646210667
    0x9050d05061027051306061815060207030f060e01110d050a0203040f020f0109080118030e060408070e041103060109090303050603010b03030f0d3c11030a020703120504060608160b0a 80
    0x840c952000304c0b8882c1209241e440d89808084a810750021260b00032614541c02c01c500c4540100300503903100340344000c3c3d00c0e49004802500d944042c003000304440813b440ca00240000364000649107a40e04008205600280d40100101d511514600203840d05000004009207100d20989100d10b81003100810f0a40aa600700110f1200461003d81442501d52000c501a102449800100030f101d445080c80c4805505014110312514152203100d10401c00c0144007100021070040704450302044c1120981d101d62401d107400c4072028004039014442c400000500211035082131600c14040d807010880e503202e050505081e21008682150164400c000c81401001424000c1954081a440006081c03402001060102041182d0100400c0c0d00b1b1b044081c2c0040300035861b41c0016100d040800407502040c07220359203400010140941e2560202d50501070501440b500150a40c40d034070304000380e28203482c00000400741801140c13018030400c0303610052021403864540a981c0ca4110f1a804c2c0004084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 646213165 1250 646211915 646211921
    0x105011b08030615070b090706020f12040501180b0705030306150901020a0803070504050a0e0601030507050a090506071401022a030f03062e050d0c08060f04090309050d05061027 78
    0x204840c1c44c01030802005000c18191031500b030180000390081c111140c5003030002454088481803283c0d02ea00203105618006030352104072801c440003824034071181070031803c0c003070b060600b40d6204044600f4001010030411201000640c402d401c211441aa59002483c09800c103000740e10350907016034011a4514089000003010f19840402c5e850a9841c1035141c1002c00c281c0c0e01c05030300800d100202041805078660f014020550b00640074036001d4205000c1c07020080103001c140c424540602000a916070034001c1001c88030940341183e00c000e650342e00590b046a24082401b40d4185040b0040001e280c0c0e8812303020048501c2507042e00c14041c15a25080c4c20015410030b4000c3d215900341540310b00c40c0b01041594100c156492154031407603100c80302542c1800030382d805032810034200082c06003001001d80d1500a0002120801e4070002a00c28540c0380603941d26000c0d41000c0d51200140160100700071001030b00e24890701410017402d81140d0b9a4441401d415160030500b45005603140f04420122642d40c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 646214415 1250 646213165 646213189
    0xa110a030f0605220b0d020a060e03011104060c020307060503070c0305090f0d030c0615121202120c0a060f050408040509090316032a0210030f02071a0105011b080306 73
    0x550025185036510001000c88160b5502c4e408084608020984002ca480c070551000003019142607182e0742041d0700081022520b40203000501141c0000c2c0002510254421084000c0c0c01690b02c0da1151140400380400c48074100480c030038824140045a070a00c2402602c0c043e0301981c03039801c80784035281e030255000c6e080074810303940152500c3c1440f03d0316950220080c07580b41c000d40700d001d00304100341408019603164540c00c2641080c1000e042103810549900c404101da045002c005042100c43c1e82241032a540302c1244480322404502e54800d09001f10748002e80c50720070b410401c080c4c0150000881038420440c3d014080031424041003000d030030001c0e441c03607000e410300081d20300e0517400c901d114006c04030300301007940080d6000a140003200e402a550080501c1c1086411102a025600190701074800c1d9180c3c03400c040e02c949030002c000420381c050f0ba071065030010030420309841c01c0c0c20041c02c80200f480b5080c005201411034004040071440110403041d0085070381ca2550356004c0610509907841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 646215665 1250 646214415 646214441
    0x606040915060308091306060c02100309051f06061403010b0a02150a0f0e030316030c030e0a0b0a06051e0f06070f1b1413090f02030604050d080a110a03 67
    0x194181021030701c288102d5018520802a4a89881952092000802072070048000300c501d00039081c0300b055002000c0c820080c0d4100c40500c4001403890084000e000c1e01c58004100344105192400c0301c0c86442d01e2201e49100010082007400d54030401114040c0e8003207101e50942c0002c00040c805c0402c80802018116550300464215000240c80e443d880700d000c85520500ca80e451405c42c0d07102000707010700d180c1030585200450550501064002859604a82c20400c1c166200607413001e0500a4100309102041d0f10b050fa04100c032030382881c890001088070f80080300d514040c03020035075141c40d081c454000e01070041281440c1e501e00e000d02203810131004802e81c0c0702e03005004010020b1031088082e04190b104110710840455803501d00490340070300303070042c46010202030422039030303038407010300d600c1c4564244100403844c05103508000d9940300314000041c0d0540140c2041000348207000901b00c02c003108076940e0410a82c3c51444020443ea00900d010b00c81c031008020b520b900c5482604004c0c580c0e024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 646216915 1250 646215665 646215683
    0x30c0c032a0b0f2a1c0e0106060c11090c040b03100e0108030c060105091504021e0a0f0906050a050316020127050105060a03020f0904060e03070c170f06060409 70
    0x10303181d002820b8000c541c1d46041000900c10403a4030000c0c080048075404810040c998180c501c614084c0450064440142e5407441c440c04078054880d2942040504040300c0000704411516610b00418031401070314195418881000200450306103c8a21441082603c00d0780b800c05081000c080e420790f10180181030700b0a28850082800c0d6140310301c603402032003a140116a0303800030f15105818201c2c16484079209002031410401488003145d0180c07020041160b0040c0da42c3c8140d00c0d201301d501150700c0f440080e424080b960030480f0790400a170300340d0b1107480d48500507850f5a84d4001c484910070100f1080020f03000b4030105030707160000750701e0640d40c400c54000820000314680e841e00108292849920710800a11502c0d0144007080c03040383d80101040d40c40c41c10050564001c200c1001d68500384500600a1074001000e025442d4000069800c040302660303540c0311907040032a0442e4003401000c4040f04138002220804800099600d02e80140030041c2040d641d65108000003000841c506403183c0b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 646218165 1250 646216915 646216997
    0x18100516030201090209280e060a0b0d05030a0315080d0c03030e0f060c180d0515040816050a1406040c0e1803130602010b030d050d09020a030209070f030c0c03 70
    0x41c1e40211180b08520480b1803418481d200d04ca47d030104168400d03c01c072458a482c8450306c41200125005038048000500030901d1400701d4082160b1304c000f201c014000d0b000114000e07507075507403580103450070010301c3ca1036a00e165140d0b242035440b111080100400705801d80c1107400024060381001e00309107903100641e0728149403800000c1c2030800c1184d401d503c003040000c031628036910400c0e44501c5e044040c4d903d160203040d50794132941d95007802c0410700c951078000320000702040120802c803a0440a070f801c04454202661a01c0c41c0d60300d6504200300d4503e1850001e0f92500380002030b07800d10564000b06030b6001300c0c0c5005101c522003c406031501006c11540603070004c801800b0001080711007400c658121312185080b00090840384044140f911030307003041e50f123994220b0303000e01035444080c0f0000000410303044920003e0680045944025041080c01040140842c2c014440540c6d58103191014055500010001c603180c20841d40c004010038100742032042200b90790b441c0340781b10704010391690720454 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 646219415 1250 646218165 646218169
    0x30c01020a0e371d0907060c051e07080a03091409060d060b010201060801020f03010f120201020d030b0a0f0602030a120b0303040e0414150711030f16030207030b0c181005160302010902 81
    0x5030318514103a1300d0b50181000e102e100799040215030b00500040c038025032500d40c03a0faa480e49a00015002803c2912414100200c160062140c40000e0812070210341e050f04043c540a0300c00c1c9441d100310b07041202442c19013200c0b8201140850310641d8020f040924404940d500d540c000c1c102e20314090304541da00e880100d0902d2091004081070941c03050306980ba5072404040251074203464020303035501ca80d00d4000c0030040c2d0300054103840d04413040c1000301c2c0e4461054003203000c0503e80c0e8040803008034501c03000140150088014000c036001959221401040703550443c3c1941d0400420942684c0100410442c160540d9030b101d8005110319100d0f000e41c2400b0068034a012480300100b40e00c002c030b800034440041d0f040817042102c050810099030502e02a451145142d028480c06203408608501207841058424010301c409107a2201d6050b10a080500c518030041e0421100300c000070a80e2203001002d40b4200d691902051030baa56128a0400c0440086c4a00000307440200e0035076407900940c500613 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 646220665 1250 646219415 646219439
    0x100609050402390105180d05030a150e07030c0c03020309061c020c01021b06090601060e28051c080708090a0f060512130308012105030c01020a0e37 65
    0x1070070b9150310315482e04031907542413070848101600c000d00a03030481004140307050010402d10610f5005061498595640c030140300090104820701c4110840e0880c0003042c00000941c41e540035009907502007009070b00e200c02c103035940c2c5075115024000d64414804102c0d031b0b14000008041c1209811540340349032078054218400da0704424844481d6940118010014800d038480054000702c40781e0052901e4180042c009449038410301031a410400b0790307044401561071380e00b01c51013a4116060318400c07024502c4c038452031105d41c1e03018191181c8203c1c0d407841001002d032210707005580d402140c010320f81034080d175440310380781d0040c101d19411032058000012800018000a0014a0280c4039a030ba15484c40358030449091008000c98050b0342d4601840011175402540181583d51005d6804041c0201a46401005803e004000d0251100042d42d0100031810340241021480541703407046002644030070421412541c410302130301c0f000108440c05501d65030810388680009814440340141d03445042032044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 646221915 1250 646220665 646220737
    0xc12421504082a03060f010e040f150605040c02030f12090f030403060603050106050a080309040903031b03060815161d0901030305070b060a06051606270b100609050402 74
    0x100c5019001440a18401400b0b601445401113015081c14070b00114054054070741030144040445000000400f004400c41e0f070340e4081c0341c11502d100344003c5c818840401420b000d00500c0e001d181001c10509559000109550b543d51074206203906100007856080c11100d0000c24210042c0b28540c3c0e202218801400108051800307980045092415403c100d429101a0390019024049148040003880008403d445850b00b003143d0204040c036060a0480150022a4529461441050309a0002ea4150380720008441d060700a8800d001110f002c00341c80d1080880f6101c210000b100c8000380340501c91442d22820080484040032041051000b007100403c0036001140441d0000494a0502400e6a009984460125840e2000e01d0030441c0c000d00a0240c1c1c0e01845213040514a410100222a000484001a1034821115540900b041c9189405400c0c005650100c3c9900204064125200800003645c0345601c0e490708481ca0181400002e6000302c0c0d5816003161a010f0115400c03e10700d554480d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 646223021 1106 646221915 646221943
    0x1e06060f041509020d061a12070f120204030c051903021012020f070b01061d0312070302010e1c090605031501080c1242150408 56
    0x310303000c5581c10060006002142174543c120581e4014000c4071a24428441815044c1ca45020346102e800c0000c0c80800910000815042c0a8402140390000901d407451460012210080c101d8016405c2241d0300f5001c440204114501643d07412a289061550308514a246500051003507401045100620504030766034080d850306c0d541074a000542e0070400d00d54444082c5001c08580000b4054000403c04040c5822041c5d4200041c025207044080d0080c1150189200300050396003210b0300032800c5648941c1d105058880c03e0249551202592241d20500e540d44800a40207524680140d02080414801c114031044500300c0c0202c040300038200711a841d00c2d0034804584d9403107002500b012884c80c00c0c00380f0030034450881009403a101c0d00c0d0b00142000800c81b0030500c1c82500100721540982c1e1a030302404940c9803008410780d00da241c00e05030900d441d944407180d03424079440410242d = true := by decide +kernel

theorem cover : BRFrame.Cov 646043165 646223021 := by
  have h0 := BRFrame.cov_init 646043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 646043165 ≤ n) (h2 : n < 646223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
