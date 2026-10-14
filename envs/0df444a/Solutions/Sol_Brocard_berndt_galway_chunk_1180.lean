-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1180
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:38:07.553101+00:00
-- url     : https://prove2.me/submissions/7a57799a-3c69-485d-8f0b-0e69c44ae2a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 212050359 ≤ n < 212230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 212051609 1250 212050359 212050361
    0xa0503010e0a09112e0f0206060901080706052107050405190302031e120309010c0206150f100e090702390d080c030304080405010816172d0426040306 66
    0x1140e2662480040c440c201c00110084100004d40c4000d1074030f0380346c1d000d0300c4880300031f107032110041865110b01812001002401e90201300c00059800c1440d1242c0c0d6600100c950482c865107890900c01c000400104014800c0d610101800507075100f21078071403550988440c4c0c1c0c0c52061160101a40c950480c0c4501c040c14080da290f00e180e0b102e4400180c40b94006003000c91007068004440d001c420340d4440e02c1f460050355040c4101caa2020000f110810035025010204e041812400a8980103001525500031060700660342e49000000003080400395103840039009403501d280300b62040d8401140650004c028500e41d4050b00c0c03040d0034100ca0500300c5d001d10204900c0c20012402602e9100d010441c80c400402c06200842c03285005078800c50f90340c0e103004001406410700410007844c2c80c201c150103804450b030048924280842010105050361140b60640a07900030011a02d060052001c03041d2220300c03080d2000d144a00d002e400300303075080c44041c0749203100d4216000712014503440411040c40003a0303103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 212052859 1250 212051609 212051629
    0x1110f151902271809010b09060307080d03110702030f07030c060f08060d0c03050d09050307050f0f0415050607060e0d0507050a14100e031305040b0a0e130204020a0503010e0a0911 79
    0x4010b02140022003c003c0c1c5400000f01900c06890703503515001f00360481d09011b65070300d420240940080c604146000030b43c41c0c85990700c800682c00c160310303050995100c0c03000390b050302c440350380060589003040b100e820415075421242c0310468074010704080c0011400d02030a0100e00d281c3c00c81d1a07911095440d00c2c100b12680f00401d404850f9101d4450001c00407440c06c200c0d0703a050504984035092283c1c100000c1603d4100c1e10392269200f482d20b64841c0c0c0581d21100c0030312103020b02c2a04d010036521681d0500e80b040c20711a0b0425a000400415000240a83d42c5c11400f8800342180a4a5084c40f509030211511312070481d0103030141d4000400400003c1d0040f0b00300040140b0305050380c094240b092060004c0d80d11a100c0c7d04c14a074404160b07041507142e404030f480d0040000b220108804005940492181c0001e40b0800d480d00141e1800a200505181c40040c12141e0080c030455480303159100260554000380200e203500f218440009604054a03c101c1e00340c15040360f0f101c04103001d17000c07c2203d4801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 212054109 1250 212052859 212052937
    0x5030105180a060b030903070611040609050d020d060f0902040b040e03030c03041704031203050601080f1602150a0903080106020604030816051909181a01110f151902 73
    0x107a140d03070006000e0000d001450041840724003030b503580e4234a0305081059881c04030881c040c1c8541044100066904003460780c4c201c680035a285c002d00420b0740001940300c80070000c05030545080c0500d80c528407080b544852050f83c0b0841701080341c000c504040c0811038602c18400f0515600810104079030360305130005075070f10510421114103c0490354280e4412a0031070760040b03034200410850140d000350036004a0740e104c0c0003072a29080b0f81c03800c1002011150405802490b01042c100e00f2210114402d00407a0f8099000c403084000740d00303011006034028412a00140c002034802000815040d1010800314081d50309503844000b41d4072420200510b88954401360740501004200e64104e8000d40f136a48000d20300e01342c94001002d0304e0242d104030208800215100130b41c4c43d12041ca010301d9500c09810486040c00e19241c40c01040c0010400d1418a0f0107200304850320440f4846d00c010041401e44034407940a00150b62074611029184006038060405070a92240155055410303010404500d038860304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 212055359 1250 212054109 212054111
    0x10e01030632010303080f100b0a09050301090c080f120d0209041815050901021e0c071d09100c0203030615090a08010f18031b060204050603010902030f0705030105180a 74
    0x888008201400c80c8a903081e10070030142d800c0108145030304900e1070782d84040c0003064142e0131b02d00b400e850015860315005180080f040403031681c18a43c4240c00200103050040d00030021568242001c0c11a034a0903c01e01c034042c410007400381407107800460a42e03201302c292460203040001443d02080603400c07000c000d580082e615400307014010062696400581d0041c41903032905140941e00e2810b5500040110045078010000e50001043d014000300c02400000095900c035450060010b04000342035100c001d841160300248980e5440050520740122450412208201e1940d50181c003519640303600c0e103000d40c00130b0001a4160600300581c0b05d50201d001c28880c1b03420010b00024050030500c2c0c002c224141e540310100060500c583c8540c00e5212150940440c21206542c0c1c001c10341c408da19102451414203041c02010040d898041c0c0300900401008a904d070340c1c41d06aa0300c000c1d0411107111080f940e5440115000c2c90240c001c0b64142c8202502d40c0c3d001c20759541807202d8a8001400b0b0768026 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 212056609 1250 212055359 212055401
    0xf030b130c0309030206010f0503150c0c0106030818100c0b1302100e150c061602010603051203040b0a1104090207031107080607080c1206040506060903010906060f0e010e010306 78
    0x5664544100c0d60005101c2c2c90001e503030103080c180245842c0058011441040004000b80443d035000906000b0301005c544109003e5694010b0100c60b9004181d510382603582091004810440c02d40c0c040c00c640301a10f4410560b401c21b01c01009001c044140001000c1107415266902041840c00c00704d9104003c101c000c126014180d001c5805440001d0784030740002c1c500414442e05240c83c803517030b01405411608103030030498442d950a44550024204001d80c41c121002c4a001c0b6000f900000020340d0000c09907a000c0010480e01603896000b1075007104c0035032a400002d80210220300c1400c0a08a0800010f41010f04000380d0100a50124105400307202c1c0e901030500304030004200010240c4050030284c0744500303000340003411000c1e000d01494030701541400003902c0030030b001000550020045401055170f4841a0101c3d8052192946c05a055420900d602c0e0034083c0c1500110200c1c2d84800104c103420b42e858031074212814003030182c014202416001000410b5043c0c115184000707645070010f1903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 212057859 1250 212056609 212056639
    0x50d03032307080a0612080f0c0a240b030303100302060a0905060318070501080c03071b0821010f080c0904020103060e0406050103170921100f0e0d020a030f030b 71
    0x701590407242c2c140061080410048484882e0041d400103000d10320000017142d19176075614115000702c0400c60822007000c20a68000b04081003c022040c0d00b00400a52040740c40222400e001e0000803d81240c5040020100e07881c10000200d901c02c0418003d100314840c1540d00b000000d6218840102c02c0040c0c1d050701150941d41c840085008845880302112092100b0031141d0400e1859030143d0306200104082003103040f0a032088950040c6e031441d040d80d1111039a0001110300f001e061001e4034010300480c103003810102c50f000c444c4511050600528841c1c1ea200058000c280707042c0a400c06e5608801e400098904106424540180c414140070544945078540c501c150030f41150b0646115454200405c12305c100f0081c1c81c410400001d0303901e4541107100001c10071708021012208961207034200a6401c201c0144604035200b642c811043c07100d188042c3c12840a441b0308205003140d400b0303103101000580d00004204404a906403078000303c1050541c000d400070000b004c0015006594800300800c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 212059109 1250 212057859 212057921
    0x310b030102040909020301050c07032307060f050906090d0c030813021f031a09060603060415060314090102121603020d06090920030309041119090503060a06050d0303 73
    0x150003544000204e054450040609480f009070a0400c080d03420000304010a50149000c014619824040c001c0081d884545920030720070714001401e51072402c030042c9034041643e0003440c0540740c0310b803c441058070751400c19500d5907038182200c401b14000315201c900203070003503514980c0038110884101c103803421600450404103098161617030340040e0b00054080507800d4810001945084008400c20a41100200c0d4440f1000360031a88102e00100000720603645a82000c4015554040010466951000701801512410200d164403030b224000160300e411051090740c1c100003c20100251940b81e409201c2c092030500d51048d000c0680821180304214450b02039000189580384d00082c2c246801e082c05040501c40c8407a0700d0394907e8980c0b180e280f540c2c00105030380400c0000c42d80001d0380c8a054461048a11500c0301c50102542da5252081c041e0350411b4411341203c1040e0207a544a9551809a41c12603155008042d4000100311814011a10035031043e210894040c4028540f0100c45545035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 212060359 1250 212059109 212059117
    0x1602120a0c0c03080408010c090603150e0405010b0d060203010612050405070501180e0c09010e031f020315030a061a060a0207140604030812040302010c031838040201080105310b030102 81
    0x110960b07445100e90704001c1e034400c01c08001000c840c44d0030004cd441080c002101107545100e00c00b4040300305d2000c03806100080d07111200c2c100000340307450030507200c5281005c065002441850040340e01300c056124860464080c86120f95032240207080010304000c010350700e43d281e50700a49909410384202107030b10080c503052180142c801c20301c06a260300c0e8000004110090001c8540d020350841c0c0c030b500751900c10103900400c41c20703d040c40150326545d0311140300140d66046040c0e1603042c419500e442041c0000c1d17520020b41d00889078502c1e0381620452080c8955481003144c86401644103090801c0f62110f0b107080580140c400900341464250f03680c82c0c640058206100a030380d4034058078144000c00d40c0920445004810034201071105030404100d00c00c103040c51031030203000c0e01c94658002121600d007010703000c05203019070000c40b019800d5244c00303030354030408690403404202084008541d80c0b41240c2c503002811501200344244120040140d1800e10400c414101041d48500064042c1d03a4203002034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 212061609 1250 212060359 212060369
    0x50c030a06061e05030615040e0d0302120f040b13170301061817071a09030303090601140906060d020c0a050f0a0201140306091b070503121602120a0c0c030804 70
    0x452110300f840b009102c007804031401505000c18400f0100f082d91004907905074010102964087c040d003480700410040d003007a4070402c081d405401c07a03411181d601640606945058191003c40030750b1409601d02c00c85100f0365000e0300f00c690442c0041c0f003045c000d1414120403031243c040704122454a0219080c581c2081e0010400f0404e2240d0031503410740d80000d86402400032007a229541624801d009482d1201402a6203007098900e0390440180b0076903040340c0301c0540c0075040342c0c1e83c0d00e0039482e030b02c0d140d81d8280640325003110800ca01d5501c601e820820a401244000d1400d4a4800d13072003401d078001d50090044101500881d2141400700700c040c0154400d10400348017030040e168042c80014009410031582c0c500941080c014840340f81c4030b801e000c2d40c0c0030f13810034100070103013a002252805a00540f0300c024403e1100046411002500403072550190038400381c111012002c4c4a016619004c400d003084c0710b0b9090601c0354001071446241c851007030f640565080c0f01c3c450703103d446da13040580c41a042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 212062859 1250 212061609 212061611
    0x90c120f010503010e06060109060c03200c1203040b030f04030c0501060b190201150509061906051e09370b090321030610140a0f0914011b050c030a06 66
    0x4001c01d0074207000f2005d00700402c60241141d07182c00000030f841991580240820405014903020400d0f004e000f62040d540d020409000f12039035841d041555550b00707014994000c860742e024849605c2000810b03241640c00c4c056140381145c2d1410f404501400f0020b10075020845803484500c08141c0a100310009840301201c0329a41d203401004070444048420001c60440e03240203100f40c80c2401c070402c46416a8000c07a9040c00e16150750000410580304000101e814101c0d4040014559400030001c01281e2449082400351404101d9016814026005882d81041c2c000070500c1503200307114035000d8002e1807030606100030042c80c041102882259007000c070030704100141d03600941c541000340445580c24490b4100740707101c2c0401d05903213502019100b18010307416019150681c50160411404100324411040e4032040c121000502804030008800040307120420045618600034208800000f41030b103e000000a10804141e10381c10302000c05e0b00c8901030f10f4038500d82c994050128030850307800b0b410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 212064109 1250 212062859 212062861
    0xd0507050108061801090902180106021605010804050309040914030f030109060b0903070b090402040909150501080606010c03050c0304030b010f08010609090f0201030c170c040819020f090c120f 85
    0x150440c0c070b003c2c041c42e1064800c440c0d0022582180c065850542da559440892840f525201096405010204507441c150342e100003c80c2241d40082c012051031600780c1b2a45c1c01c5640c4400546a5810aa4000d009900108070b040900c0c106a0000c2c540d0610404021658418480e025411600321500b2a441c0140000040211180ca402050090000c800000b89000000d000181c1d56806501c40d03e160b070f20300495100d0740342d80c89605442c000c00c0d1140f014412000c55140c61080d00c0081000030035440d00d800000716070b441e00042c0f064888c66040e150b500c100c60385034509407401d4100ea035070058188070400c804070005100c2ea02450080101070800c0e4019801c0005040c2501c9641c2c011003441460401c0b0f03400800e000c41d000d401207540a00380020340009140c1d00300c403050301c100782030080c400c4903c00b407060b6444182c00810440d10107200303590034501290080c1d4501e40c0c4d0000080d502408140a048581c98095811600403412034202468400403642e52043e000088602c900130110144c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 212065359 1250 212064109 212064119
    0x70602010b01080a060b070209070504120b011d150f031c020601180506010203250c03200f03030d051e040f12020606090a050a060302040216060e03030c0f090f0d0507 73
    0xf82d000d130400352004041c410142020180c800303500560300041e1040107480c0100c4e900d14021421100900070083d9120720f001000c0c205104150428450f0000c1c00180d8201140001c507400d02141c0221100c641598114a840302045111400c4103e659890b011700080f0702114101401681000a041c0c2c000d80070710b62614900b10f03462090001044149c600301400c000c580d83e400320894901000718200901c40c1c0002103507840502d1508a001003c4211820001c0b00b070081d500495040070060700149406001d030b03c4203021840800d12103054043e442480400050203554106542c84441000021800030300000c0380724803030340d050b1003e42d1f500318442402400d00c40000f1064400e034050780002d101900b403103004035202e40c4004105020144d40e07000404c070080c10303a4201400540c2c0040041d5280e60201540303c0c1d0b540c0b8480022282c0d80c0c90204140b00854010080d20300c82c0d2000300045003003030a060302c811700d00c2e40000d224590001d1552100c150580e20030a481040c039001d07000070480d01d0f080c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 212066609 1250 212065359 212065367
    0x310030506010803190810090c080f01080c0a0515090a030b040312050106080403030f060504020a051c09211727060c070602070f02060412110d0b01030b06030a05070602010b01 77
    0x41c0c100c0c0c07030140c02c1003001015800c0d84907010302d5461098030700303440e0341d54030307e600703d410604c181d040700076042d05100032070300e0842c0c0c480c6181d80100e2030a114241c0a903070b100032299a40c04609810b0390010036068042260b4507118010b40b02003c4554426031500c1480c00c001180c826031034104403600350309d2009002c06d042c1c0c0550b41c450102c204180410665040c000080c06940d00100b0041c101038507403402d9102c50100d900080000c04024100f9500d4086421b4081c00903000b406ca12003409540044006500c01140640c10180d84c00c40d50180c00104003407510a05610300081c1482400808801c105188505002992180300c54100c04004007282510317041c032070440012015540e074050420700406040c81c3d000c5440a1740e00c00c0700140d640446e40342c0303410900381e043c1020350304c24004280041c501c2d00d911021100075124451014440315044100040103000c0c81010701014046001480060308400500d50005402021501c24042964605c0e00d00b80454208030f0041c0d459032410720f41c035608 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 212067859 1250 212066609 212066611
    0xf18020c01021b0f010606081503012d0b09040b06010c050f120c06090a1e17030901021b03131203020f0a030203040801060b1c050c0f16020a0e06101101020f0310030506 74
    0x50b240091241b0340ca0800c00400940c00542503110001e410940d040b0035603000d601c01e0428081d001ba0f188604404081014070707109468650000321390030805011118686000e40922072640403840c0421502d40100446034045d000c807084801d44510100c02c003191384200300003881c206114404030f540301c803450b5445080040c043c104075240d0b4000030341d0000096004250001042d0074494544960b14941458160175018044100004000009000b07580c8010740040009010700c6481c0d07044028811065907803441150280303030300914608020320410300e14800740c0c424a0301078411100040400c000941c14140d42040440160f4000034040101001c01e014210081192b000481c0c1080800a150100c640744086040f8526a40f080007410200d5600e0544030440594100c0301c0e100c0600071020f0044001800d8103921406050b10000350b9503c51020403481180041c141c0070a050044209594001d60000b40482035502800350004858014001d503110b03a00d4456014800c624505215040100c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 212069109 1250 212067859 212067883
    0x6130f0b041b081c0f02150916060f090b0d020903100b09060a05010c1101020a05030d05100e04020612070e1e0a051c0f02010e09041104060b040f18020c01021b 70
    0x211001020b40c4a60360022034580e106042000d40d10080c29402c80c10107c2a14103400001c182c07800380300c4412400141c008502d010034120021150300c41900348c0c0c9003551011141c00050b11085c0c280b21208004000c0c08103203590041c054104410000001d041c0003a4189030070400d0b9858151101600c2c00c0c4200a8101509a42d8403c441d03080100090195402d040040d1040703103000819025070b442004880c0010b508101901e441d801010344000152030103440300d403140903294501050644a00f40c086000303680c000c00aa02e45520b40d0071080321381c000100040d080c030850800d28069500c032000c0c0d230b42c3c9414a8803001200246494104090f0180d107400507400740f003440100140d001000240f0b6401c0540003480c4410340741d49440101c60042540d5055070300590604288000c000c101540b002040208070740512582d6281c007061482409103224102c40030004c080108443c030100c2802c4400c055190f80d000d89005000c040d9942a40d001c00358400841015007600100040b080c052504080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 212070359 1250 212069109 212069113
    0x50901051308160504110f070f050303130516150c0c0e07050702150702011b0501180804091b140c010b0a030305040f060305090615010224150307030506130f0b041b08 73
    0xc80c506c040c800140c090f072071400109140000f00c00d010300c4400c040400c2a42e90003000c032562850701e00019002e820240c18116004c2c40740b011860750280e00040c4000030b44441504c8000c00b280703c02e01c1255143d40050741a1000d81e19800c01080b41c0c1d006a001600c0b0b10202d40301c40340d485c082441409402074281e804208900b0060100b0001070381c0c001c80f0710040c075030032001810f2008492b04269004215114030040a80070b121040300030815001d01420898540d01410007070490808071602411008800300c0780007820824110310020914009007525080c000000696000c0d0600811400416900150007084010400b004050020102c01010f0f20103840c1c140858208820266aa020041c0002c64a01c58a40682c070050744200404010014032000c0c5d0828090f0030192500c84140076201030324000c1c61861014042c0c00c1c000b86980850b64400020105944c508031000d5001040100480b00c00a1034041c003804210201c1d912805540121251403001d20756501c1c115203810280c1c0120401e0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 212071609 1250 212070359 212070371
    0xf0d0305130b310e04150e06070c080c0f03030406021b0706020304090903030b090f0403080105010e03060a151205062a0d0f0b041109150c0607050901051308160504 72
    0x160024400107002400054203a01803440c0307440062100b441e8503000042d400c0001d0003048244904101300701d0181c1b10307140d020001d039040f4070300f142e0f26020100e078040040703040000b664000074003281c02024624061000d8445a440500d038880c150350054400751091b940225643d01a43c0240e580d540b0f100703109074004c0069070702e4500040d480b40034511904098940da06000b01c1071500941082114400050201c119407401229256518100303913025400141c0030400402d0300d500505041d400701400400500712680d03130a503450041e000f4a2a00c28811101c1240000c003640c80e81d940e4605103219101071301040c40c02903800c1c0d00a0703c3c0ea00c40030300400c1c52420300380744072060b200880d15032340400000400c0280381a000000074018407440180c00618040ca1080310070114000f802c440d6004940c0a25004540c0311141007030301520102010340d07002240400c0300300340520300419490b007040c1001c90408002080d0038000d0036543c1e00070801c0390002e602c007440c0458030034001005850300712410440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 212072859 1250 212071609 212071627
    0x60a051e0f0108040f08030901020909040303090512090105070b09071203021b010806060f0c0c0a0602030405180108150a090203010c112103060105090a0801020a0216080a051504020f0d0305130b 85
    0x2d03801c101c07000a00440000404140c23100c030290116290b8460142c8003c03068141413400030014407641d403060750070303024106080c81e0280c018401c403208000b05035112424002e443c1c951410700400034100c030f016440703501e40008550000e05140440640680c0241c503e4020008000300140a00481e40b030410901600b040003070380c1c620303040d0b0344c1c8081c0f405031540c1c950341d0790410030b45071000c5034010340da020044290004a030390340040104241c500c21f84003440e22003440000c3e0b1070301150030b01500303000750400b1041180d00da4101104a0b0300c1040783e00082203800303068005c24212107040f010040005e021901c0e04030004820021548080c0191781200307001c081d160724601c420300020303140714108040040c007803509030344800404004d00344400c021559540041d03c045e6503680200c6c000d080d6128407140000312003c01060440303d02e900040039003c0401c46000184181000900c1264462141030490700c2c1a103074003940e040c001e0702c40d4417960b07603960007020f0030b0011841c4c035402184184400c00c82424 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 212074109 1250 212072859 212072873
    0xa0e090307030815032d030315010e152d2110080708031308031201030623090106090e010c14031b120a0f02031e060a051e0f010804 58
    0x203070340c1500e010300064440c01c1001a20500c6054003035410f100d4010076401301e03445858080598030740d1003902d4074003003079044030640c407070000300ca40309031042441c05440b2a95005544803142e0282c0186803e010800c0c0000c0d00c1c0701074000d164550b0300c0e000008682000820032512030381000c1d0348200410305154202ca001241001140b5401040c500244041080c000201510101400613042a2107003551074882d4107a0302d8100750080d012102400c100020328140200031501038401e90010050a81c0c2951a464003400c14541c04001c054010460312400003a51030045000728074400010a000d072074482c23074a0560340c0002883c41030382d14090509220b19040342040481c2c044181429489907603010a03400411880c40c00304042c4040020800440c00a01242c1071040c0181d03202004042851183c080490004a0300b8041030012800142c84400340c1d400e1440d440a8010007008185c3c0d00c40010460070400c42c01324000e11038240c01c5d42400c0e4904040b400407000000c3c0b0704040b00d85070a8681c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 212075359 1250 212074109 212074117
    0x6050304081615020a030207021503010e011502030409091110080c18040b06040312171605070203012a140705030405100c1a040204150b040506130504090602090a0e0903 74
    0x4564800701d00d200c48200400c04411030700d86103c5100c115200c0c451498041c2c040d41c0040b50480c030903240c18490020b0382100d60156416105500c02c1112141c3c00c4c50001c4032488003144100003544014400051009464003510a80d244078821000c251600034040c8007150041c084884140501041001051800c03441a00c080e0b9024401f5201c00c103040801140c001c01092030a107820990010700441403019074141000302010541d04e24509982444200070b02c00015035100c2c00e5070038440d02c1504040d100308042c1440c10700060002803406900e1002e00da01000c8605803030003041603c03d010f41090b401000f0300b1500081c1c10b90340b03840c1c1211039654540300e1056004903486030017417252040e4650300c207960020300301e45d00810240441e2515419807010440841c2c04070300c624107040e025100808145040c408481094160506041c00c2808109442e00607803001404002c4c4440006919503642c0140902d6501132140160b80d44003040074003881d1503413500810318240001d01840300c8140000304507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 212076609 1250 212075359 212075377
    0x7180b0d2018040506011a0306060301121e030e01020705040b030d0305071e050414040c02061801020c0102030c040f05060a0e06181018080109020108161b1b0605030408 74
    0x1180003162141d00098190462101c2d0404464072502000100103002420030b0680b018010b42140c0c009260003510100d100071140b00360498400c0c801044035040b18004005081c0c810322032504506e000b900b0400204100460650001d5141540300b646540c06011550281c41d00741e40900c0400f21305130105e6a500c0d1480d005104060b580c3d400100c0d223600c40c00c87c1d40b04030005906110039500e8205801421500180280b400e41d8007013480404551402d80301d08601c4008980140c0110303903400940c60341102103602044041d5401300900e400c0790800784000c2d442a00401705281d01d40e828001c101d81c1d00092500241d000d4941004290b5500e03400041c0c194940d181150b9903641c0310b064058240d00005440180d5070480710704607000581e150400c000c07000181814894640c0280e0700c1c04c1203401d0b41d10103140640441c680b0ba0204d41c41c000d00c210091225092400c00c50700140303056480341c0d10107c4405007954a0100c80948600080045441500030b1605240c89410b508007900e444020307200e0a425 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 212077859 1250 212076609 212076653
    0x110102120318031306050a1719090303020f0c0601030c083904020d02030402040510050d020415171c1d0618060d02120a020708090108100807180b0d 65
    0xb40003000c4410022600505450b250b41012195207a01c0500181c1002e10781c1c03804609401c5070081c1044142c4003061191100740e2210f510380d12070012203001455418030503007c05400f0484c0365690001480140150f42941000b03001311761460510350042440d07a0000003081c1c0000483c01c0100c4540c000008280080d440300c41c00c00c5e0701307080344406081900c0b6510740d00b003800880c6507c000038480d409544154002d036018090f51380c1c0c44000c096207074903900500742d001e00c0c400003031409418103900030512441540080034101d51192400039415103400344d400c000e541300324424003403036842036103034081c450990500c449400d01882a20b0000c64120419600520001c1290800002388034202e0504500103046195500b6880701c1e0000654041c905080448007180b000c02c920388903610031115070a40141010b070401c1c0c040c02c011907a2000c00307404004e500052090128015409002d4030004210522003400045134495503501a41c44015045100d00220221040414218201c845101c428011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 212079109 1250 212077859 212077891
    0xe0a080721032f01050a05070e030a050601091104030b13020102190308070804062a0f0203071203020f040e0a0203040b010e070c030f11100c0e0d110d0f050a03020a1101021203 77
    0x1089500c49507588003e4440d801e0000780720715a40039a000500030100307541c410b1210341c0e0040525a42c2c1c3c3e00d0310801401d952000c0b004100140702540030f81008407200c44154a441d940b61904548840141c9030400d00c100280c0074241150f804104204054480e540c000c0044003807500d001c0e1024500070203030310902101d4400107040203a540c0c002c2c003609207482100700086000e0801e107c202d030a4a14075502007082e0741900a10540000b068074aa00d07404207072207106000182084010f0b402112403850000780c244004281840264041d070700c92401d15400513280e290034184001d9281042e800584a0341c07503841400004c543c0944000075442e090f0503c100c026801000031119a10100d22591130b50003512100320b040c0d04140c0050585030380c1c0382e4504400c503401208000c2c100c0b4003403a008100c4c080c4c1748045005030a1801601d040345000b289180c05000e2903854072420014542c00c05ca00603005080442d080085d243e400500107202031006050300003060080103014803000d407502d420f550303980c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 212080359 1250 212079109 212079167
    0x61e0f0e07030b130e0f030408060112030e030f0303040303050a0b01232505060c0a091a30101208030a06050d0f1e210e0a08072103 58
    0x341103a000c240c0f02414446a40080740201d000401124840080754003600c654180d0621000059030b0031b450481d4060007180e40b800c1c0320b0120ba00207010b01102480700d075203010400c0f640c1c2444030705000390824010b0356580c50549801811038038000c04081030285001c0e600c04d002c0c2d83c0a1440c1202660b020300c1030000c409401503142c2c6902804444c02441101d04007090359843c030090824504038071030422103040d81c0742d2040448803406422008000100010070420881c0200c040004e01407100132440791400c0300d2080c24000c0c95072844c0080c1941500410b4a0030360500c4411007550082c6207114030441d240c10701d540342d01e82c0d01000c40080d00411020001c258101031503840070004142c02803642d12040c4661500007552084e0742000d842450704a00c01c8445071140c1700c82d4200742507006005a20000c10492020b49140180c0184001c01c02c51130b042c8800c9480302d544040207040c00c04001c08015180c4001c0c0d80c0c01c0100c000c402c000700c260000c602e0700046c1d00145a0b0785e0440e408000d4003035079a144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 212081609 1250 212080359 212080361
    0x703050a0603080c0c12190b07030212010b1c0b060d022203060506090901050f01030b180109080d1a06040e090f0a0b060111030702150c010e0a0501061e0f0e0703 71
    0xd5080030f0500e10000901814030707480040c5031610710303c040d07030740c40c002080b00f0a5280e01c43d07942000a15410f04001c8040c80001c00c0480308640c80880d60400604180035059244448030702600302e19449400050340400c01d070313000c40c0120012012000d060060900282c0030800a015820603a40d0072034012400700c20010600c0750b201c0000f101946403c0006a807400c0c40030160100307071201c0e4015104c0b0404540e8070303281070049501c2403248610314500c0c0e07460361b540c50b280001c0041018038140100b203664240aa420300070f084d40e0074003820072642c0790b500004c11a012106a482c0c19900e00e03002542d6940e0035240c11040e00c00311440d2100041c3cad07983d00c2c070350b030541054140c0f039220701280641c105010030400040520380c0234940a0342d0341050011007070456940c9104006019500c091050704161040c0844401418400ca04034008585d00041120461511400400485550b51182d1041c000244000400141034100e50410600140b03000280300707046e02140266202d4141c03d0340040d180b0350003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 212082859 1250 212081609 212081621
    0x1030c0909120e0612090721210e2808010e07120f0507090504060605060304030e091f06111501060f110703140a060b030f07090b120105010e1803120703050a 69
    0x402c848a5625050b40100d0f140d87c500d020b074080850404600924101e2064003681850b03500c201c80c11150901c180c02c0f038a48580444030502001036815401840da02c0302d207a8801490704c0540c054141e42000100b1018080098200000c240c0c54103005840301c070000560002154800e5005807001e0f4514200000803c0082d44041d2440c4100c2e040010920055400144514040c1004001003a01c03041000710750b100c00e88000d0300083c010201c0302c1c1240b82129070740760020408824807246107031411622941081d01d900c0040407030742000d5050030481c81405062201810400101a55070504201401030490038942c41e0820440d0101e1b00d500e000100148006980c1180104001100a4040039030311064040c044802074200002d01041c0e040000ea04407103020a0301c041c003045801d0107504e500034540700d8501a0700659019035115410420b10a0901800140721807107901e10742180c2c0c00007a005880c0d91242c11350310420448103e00c0c08088c0301c541040319860081000c2d2200041346019003070b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 212084109 1250 212082859 212082877
    0x9010e190312091703100b040303080a020c070305120903060901050f0c07030504091a0301140f1b041d07021603050d03021b010e0102030603150c0406050903190b01030c0909120e06 79
    0x241c800c1c00c2130254440594403414110075588541607c800c0c1d40880b41c0154400140814110404110b41088a0300a0300d142c6d0300d098116448503075240c0340c0529140c441d00c4a4150b003400060581c0460409120507540012420020f10050420313548244003135900901d01c00078200080b2322941007601c16000c540052a01107414001c1c120700e003011681031200248010310a40c40c1c01c0c5041e0000501d1040c4504c5042d141031107407880d588481100c02140340c0b00c4240340149404000c00b280d4013084458100b840c65611444007014a000749000e45000401125100301d10b4886a040000520002d8403841d485ca4600c1e001d40c07140007030b0304410340348041c05880700b50700e508142500264113015405140304010480c21a9040490031805c100140400d03a079a07610007208002c180600c80c0a04000c2144030009411105130701414080f010f9084030b156800c03613444400300d004200380140403042201812400c1410040c140310303a0388000c142c0042c07010a00901000441001d04c03580c906007a00d02c0b02c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 212085359 1250 212084109 212084123
    0xa020a1707050a0f030c0804291003020a0515090d1703040311070501110a17070f050a030f050c0a060507020f10020c0729030402060d0608030309010e19031209 70
    0x20400650207000c68121144030f1001801d403a964400f064130a002c1c142118040f61100480d0b5141c0303450301d0003e150000060f0400748003d0381d402c092a440400501d20402d0300c518500c0206055104104510500c0d5018070f20a00c000540040000080030880382d030007000711214494640305241949a12008400c008403a001c003008002c141900700d40424074400340942511000750b10b840064404100c08074481e29103506c5500000c000803101059060380070840201e4609008040d03841071842c80d400f03041114107070841d58842c0304154008190710b0b403071000c6090107414804000615503840d0b0840030050716490302d40002c500554001d0000718510307282d24094828003001074104202960110042c0399040c41103940c001001e40b0520070b10042c491000c449940c00600107100c084071904007400681c0d0052040181c90260741c04c0703104280007400700700b01071900ca14000310003d0031070305980090211a004221155403201103282070710300d503941c141068004014030400c420020680100020152 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 212086609 1250 212085359 212085361
    0x70c06090f060e07061d2b03120e06040314031503010507170f04080708030c0c2a010c0203070911070b010602070f08030a02100203040303150308030703060509040b0a020a17 76
    0xb105140d04403040440601045884007607490500300ea0362181d04044502c0d0144401b02914146801144494102850300c042c0c0600c851754001c4081d140b00c00e02003100824140c6a610300107a1381c40c0110800f5043d403001410140c9802d88000d400340c460020410040a400000182110b2148030960f07002030700035000f0002407810713480240c0900c105000030040b0320040c20014040d445c817040111f1286034000955810b00700b26030703243c0781c1c1c9030405043e2800d044028001250b8081c01080780c0c07428502407102040300030540c00d00c0340112160102d01c0034104406c4252150140c0c40c0050b211007215117000c0000380d00a03030702c80e0840c0c250283d20b03030040c900001c45c40001202a40010214281d412104401d00c9183c2e070b0745000c40d0b03a845044e020780b0158100100f0b508803000c1070b42c0510791150103400c005c10040080b200607890641c13207400440b4403180c040240b11223194107201d40b0018140a4510003c01e044c42d480710002844010040d480e440e400051b8180020710070198640c030080d20418148403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 212087859 1250 212086609 212086613
    0x6030308060f0603130204090314190806030c0f0108060406050604150e0105120109051e0a050702061503100213050904060902030d050702090610030e0d050301080d0305010806070c06090f 82
    0x460203480591240c100302d00500e2691910904076400b070540301a881103800200e07828400a0541c2090a800740f0604040748071031503498000422503030a030710707292040300d8400610117000458050029406948480355641c0310383c840020903804150242091603d039a56640068017410361a007041e0b8020340d000c28001070300c410300182c00c103010f55180c88a00c0c100b40d410300115510702030380b007140c108905e03242d00400c600c426603071049070412000e501907018060401c11074070800c1425100050312564410800c0581c90303042c0452500002c101c020b11160300e0010001a907900421400d4000043e40010024100101c09088000801000c0d0000d40349162a080010007042c07400410307800ba02840320100952881141102d40140e802091440703551120000e00080e00c11800c541000c2c0b598602ca95400741004021812982d6000d0f9a40355507507051551041c10075a021148206050600300180108840402c40ca03034051258504003a500c0c081e41011005003485c1d0401400d8110001c1c15801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 212089109 1250 212087859 212087867
    0x60b040803040f0b0f030114060403080f1b1606080a0b1009060305060402070209150102392b080906030f0628210506100602070905010501020703060b040f060303 71
    0x70803a9000d24143d90020713030750813258641d84540d802884660303000300010b1000820030070720b0300d007403000160056040c0354407a910b668155110f0312a0400111000c907403400c070b400c0301414503034192100f800074084001c1481e514046652180c021401070000e0f400008400d0040e940c8800001440248400e0811401e03204c080d020720b000c0d0140340002030420000581c2800d2500071102c2883d4090400070556403000352901c91380d003481920714110b00504403880241603040501c0c1444038650b803036007103011426180b5403035040c0e00c080f6014040e10004203440c4904502c242190740c1204410201d680f40780c01403802c0c441900c40e01e68469407005020050100795410340f45198452181a105061034500d940309402004000b0b01d04904402c0d40200c0501915402d02010341c4041d070010300a0301c403004141e6400c1d042407421074440b820b4950f2840200040ca43c100800e40041010a404110035418400001c0d1140440c2c04050900c3e81c5030040c2310100e803505d0348404480d0b0000f074020014542c413454010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 212090359 1250 212089109 212089117
    0x10c0c06050c071203090501030b0d1406091e03030103030c051203041a1e0114040f020c0a110603220309030b07020106090b040204080c0415051c0302150f06040f060b040803 76
    0x4400d105072500494130010108000d124035405441c1c100c0c10303c0c5004011800352012001d101d0700414940c140b000016008c91540442d0400307800130341040e1a003140800c0c0761a980110703070a48001306d00c0c9a900c0d0b04074044101e0381940d0b00f51400103107200b51824414507210500c100e00c0d0f100caa00004101c18001c44100c00340400d480c1e54100125500c1c5d038902070b9501c5080711a418500c0c80701e40010403001110206008100c803000d04045818820604100102d07049902c254005070808035030032081000e0500c00c5146607808441e07807411800e0250b0041d800c0401d9030340c2c103890005400c0e401e000f40360069150000840e449003494020780b5100d030000b40038103503510a40c00ba1900b8204000e000c0e103000c0c026101501d0860000f0b0505140d41d10400014204116030b0310b1440700190320128460b01d51019100098100513103c2c1103d5880349802854100c20884d4041603044010074000b090710200010382d00620211001300700c1411090f5103000400d0700f54000c02c8542800100001e0041004c00072f4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 212091609 1250 212090359 212090377
    0x20a080a06141510030c0207080a0606080d090e01030b04080d05040f150501140f040e160e0901050c22090c020c13020903031b07030b0103080403020f030d0203090f010c0c0605 77
    0x200c801d036111070703a0203801524a02243c5903c0180c120300d61342400e10980c4401c031102003510413507a200342d459000c2c60a146e8811030aa070140e03140d402c140450101040101c40c9510745d803512440311480c149070068420418000102008940000324050141030800c1d03400811a18900300500d00301450103400c80801c107030040f0750044000d1f420070300c401308902c502030403a500b0f01c0080f00da6202142c00c106550300000c1185a01c5503403611050b00c150720030060304032056400c103612401c103400c0080a40304d03200000c10f002c881307038104401c20204440304000c0c0d8032101c01c01d10300c040039400312400a03400700303c440c0c00040120386000074550120360300140700c4d80c41d10b8041c0d070240c0415400300740c540140e02c1110421500366000300305c00104c05558040750320303c8100306019a020070340c990381c44412010782130307100b6a80340d000440c041c015450b001140f0071074520200d0043c4400b2039a49006522070092400940c424090204144801d034003a0720fa44221952003034080c00c03043c1e102c60001d4003c2d0446142 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 212092859 1250 212091609 212091641
    0xb030105030c04052e0e09070e09070f09020d0b090703050a0c05120411030a060c030b0f030619020d0e03031306060e070504092a0c05010b01020a0201090e04020a080a06 74
    0x114115003890f201d01d90043d103004201c0702c1c0946178200b800e88003000442d200032500740c2900000a0005210582c607005401d50700240c0860b510340880b0004402015005418603040000200800900221800c0440d91010310141c1c48003440d96603403004044006c40389070001d20403000c100c441541940440d200304074000e0101310003044100c040311a0301944049520030700e807420203c0c010030b403440510020544000c04603000c060750350b41d50307800b59a00f0b290000040f0780c956604034001d00d0712030344c40b042d4203a06500410392450a50001c00a89481c00c1044018660000b0300c14109007203600701c03402d4001c1c2d04040700e542c2d0400400102c1280003000c0c003921103030320b48540860600801d0000500618684d0b56150405040000400c0104419111403491500001070040007084802203a8000c802e26200d41010041d94144507007950303409580b860440d00031446110050303070170a003e0b1058400c1e070403000c00070750b6541c4045103082c80c56800c15281403040a0f102010440c2e2600300740000727460804 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 212094109 1250 212092859 212092873
    0x30c041422090c1202150f070807030c0209060103140708090f010e07091404080406031802090f0f010807050d0305070203010e07180c0f08060d0201170109020d0b060403080f0a0c08040b03010503 85
    0x119007009010100710082d1b00808000388008440060300241010340540d601c2c00e4500003295503455095800801e0071004146c02c01000320552034000c044560014003802c091084401d0040121584a80189540e040c030181402140440740100034289a00819000800c0f04005c03515103160349081d44e01c01c401c40641031180941c03041d100da0100c540101c1d4030034290360500b400d040090b000341c40308c1220384004801c074004690240e500c184029004d6858060450064140b042017036248070b41c141c00507034041e400200200300380c1d1076030001d54080c19003600e085901e6100c9480024050f0513068034241151090003008201040c40c000103500e5038411030700401800020145c25a070f401808003400e004640060000f607210701380000c04802c8640b05240030780c0840c0c03410b03100c2900000b0030307000083c803a035002c14241d58030300481c8102070030300400b02d40381418185981c1d104041e0b0320454265040518001c503210303800c6401400c44212240c1d11218941c1c40d9500d554052403540c000348941480313881415 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 212095359 1250 212094109 212094119
    0x1d0f010c1b381305060408071b120201031506020d0c0611030109020901090e060a050409110a0b030a272402070609290609090307140c04050705030c041422090c 70
    0xc049445913022000e030645540b95122042140c000d06020b032a103a494a0304022130b410324143c0d010142c0a002440300b00c0440f0f5000060803180345d41000c040c0c0380e126000900c5216000234004003a0704091800d03495001d1145806000340590200b40f0500030f80c088001301d9001a240c01400c005c00c001c0e65280c060a64494848000580a545507600700404135014807070340c102908450101e6014611001c0401c4408003c03c0000150340e0140b40440c0010051200301c0c403c0780a98042409410601900c4003c00e5100c1d010400d40000000d00c00001c1001e0b0a071806401c8908101e03016819008640758009400c004004e80f0104200300d45608205150380c050b0807400d00c09111203681c04181d9180c0f51740b544240200040041c001040f80d110900021001654084d500c0b031a0141130009400c011510b40d00303001c1595005000d210502c8824010064002400001d442c1242c09150b01c00129200581c0483e10148440010b0880350f190003000441d0b090003500a60030851042c0e01e0106e02503660 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 212096609 1250 212095359 212095381
    0xc122511101d04020a1403040b070305100605030a0504050f06010e01031505071e02120a030e011b211d0d020606030115120203101d0f010c1b38 63
    0x1000e8142c80150303002ea0b80d0240b8105640500b4004660f818032100071076800a1550960300119411601d43c81300c20200042c0310380c90b00405400032a60258144200d003041006030031400014094900c2c1c82c0c2c0e82c800202132101c1000103080800204050301c2e420b5855441d0a2a101000d002c156000d5401c04449030324503201d07100e07103803158049641c5d00980d40707644050380c2070400d2140d01c04002c5100d603004010842c1090744c0240f60148154500141c14040301004a080d214207140900318272403c481e26400e4560000211180c000c0380680c082c550a000003c0c041c0181030340708401c44026400005076000580c0020b018000402d5a022113005541d10f00406080e03a2505086051540076031808104078003401321040009407005098070411000c100000c822641031030300151600b6a541c104902d1143c0a002246402a9550080c0015203c40c1000361a01d200d0350551941010304001c02c074144014140c09030100c0c1107520101150040c00c101e16030051000700c00c1c814000c007046002c42c440c1084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 212097859 1250 212096609 212096627
    0x91b0b0d0b0f0f09130803130201030e030405030d1407050d0302091801050a06030e0c03060702010603020a0e070815220605180108060411030a140114010b0c12251110 73
    0x400351441d40b9403c0040c0011000050032050b915080c0d81502c00015080c2d0024622480d1007013101800c2217858000101a9050880004030b15041084248101d03180400c560018461600f04500c505803030440b014071a10801c000540b06019440c0c091040c10307030503001480c10007000c81e042890740740c4621100d080408284281c42e4060140c0500708401c2d80207411400ca290140c1c816a50103801c0700b0003090a2010485903000144d550703610500441c500070114401400128400360f02c10b280c0080044c0911001800e0720010800f51001115950b83d0b03110300c00d0301d0039000e450004102204a001101900e035600031240318107e6080200080340b48020b00b18102c41001000f840662146d81740c0d03600c02000c0d040c40c590140160742d0703031034081602c5d283ca00400b0040b1100010305800f8185910f9050101a001038040103010070401041d48000280f041c0f58032405c8201c0743d500c10b0740d03403071061419081100d0580080044038400f024020200000c011907041990030320030310900124200c4402803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 212099109 1250 212097859 212097889
    0x30102030f180102090d0f021002120d020d061214300307110303010305060916062327150306130c02211b010c0909091b0b0d0b 56
    0x107041c0000030302140d01070120700102c451035030005103440c0701c280200d601c0303041c0100241c50541403c10385800714101510140ea030f628161019124003441c0c0d0040524900c6000c980600d910380102c3c100345c5500d420fa100b0401400b0036090301800e130207149846140341008040220040c019440c41c0c4107441502c49045014082010388110501104101000e8540014003070a0402603c85401011100c0820040d40607502540003440149803401c031140c03504400c543c0e44108482e200108200c00c5c0c1c0c000a800e0b0b4080c03204420322227032034603243c2125890b0103044c3e03201d105569500c681c018682e8610300004d52082003500c0c030b401ca8010517001260244030507140c558100980441108404815900221091000e44143c07140c04005078002041c00c040c40d19005d8101400041075628844032100ea0b40011854000900006100060203405854648200d1266640750041c14080010107003034045055662082c00c40c80c00e840780011030003a0802c400c00b00300d0501d444441103441c80c2098201046a03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 212100359 1250 212099109 212099131
    0xe06010b07032d020c1e04020f040801090b18011406060315030102160312140c0c070b030c0d0e070602070911040506040b0a0206070309110d0609050105040605060a06080135010204030c090b03010203 87
    0x940207080c031000b98009e10418024480038017000c2170000c401c0c0210740a103406404000d811b8107144e00346d40b080c25002d1ba0180e040303a1411020618803030240c01ca0643c483d1045982540f13a0f0b0b00e406811030101d40e00c40d003c1d6415403001030001c2880b0a4050fa0030802d6003e981c60a4119440c60032401c12961180d034102c22050021b030006411001200090071021800c030b0565070b040d0307a00e03c40084c103500140d0301c0c1100c01c0400308854400f0255407046503200c0b800d0000401c40d082c58194083c3d115000d0340a00d103005c0351076400706480004681e0480c0e00410028081c25500ca50720450b003500c90b0412405100180034407404620101c5c824003c1c2900e290308004d544582141e603e0401c044040c108800302c401503183d80c0d45901240081c8210340c070a5014460100f09880c01800b004020307000d542100c0144081c0318018002c01000c141841c103000c131000101030ba0308440c461845500088544407074240d41c00001c003c808c06c03100c0209001102c1d0000800e0055005410416090340412a4414104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 212101609 1250 212100359 212100409
    0xc0201020f19050c0709090b070305150405060415090c08060a03080d0510030602070c18091a04020105070b0915150f0f0609131e0e06010b07032d020c 66
    0x550b40b03110808110300068182246402c1c000c01c901070810300b40f980b10541c440d56890b04d5606101d10001d6083d07100146140422981c540300c0003860143d02c640100d2400356030750710300052564843d41e00c00366a10f8001740305244c050755269220005000043c20080c009984140030440300d081110740c02003079130b9010004900780810580d144002300300041c0b41c4003a00820042c0000800c5042c401030600500419401095506040500000f00b0f000b01114110600e0300c01e01401140f4041d9401c0c540c0441a00d04401d5a00c40f400129240c0c068084081c103912a420140031507403500048018101e4007000410f02603540d0030b42024a4144020f60842d00015111803002c000e151015809020600040ca60303070070200403130042140403200d83c0619410310741ea444100507001d011002c90300404180c2200b44500f20400c4c061944a06040c400e10070b440401142b4501014042c40740b864110401e041481c0d03216148d5802c05d10111500c61200d800b6002d030510352903036810201e2a049003099820400781c0c0c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 212102859 1250 212101609 212101627
    0xc040c0816030f0f380a03150e0f16060e0105190c061a040b0f061209030909042019120503070c03030c1b0e0721060f090c0201020f 58
    0x7070f00400d50304041c4503903900d0600c0001855841040c12410996500002d514450380c40c1172016001486007030040006400500103641c1e07001e4082d010f496001d00100b2541104105140c05014180250000c0c1e01070b4074424000c1c80790000b40280b03401208007008444c155900c0040e140c1c4010800da46001070000c118040812075200d001c10710b40646407824003441f88041d00d84030126606802d40300801184c59014900ea85000c2c0144c83c02018100ca511a4400290002030102d1166101ca4852038888030700044520805000780d402c000b10107440621549414a000803480d40d8a4910b500c840c0c101e919428071a08000c80c0641c81080c8d5406100f081a00b0407560f140e003e00c10000c1118241700402880b00081c8916000c3e00046100ba20b814520b0001454102082012140007501400700e050080140012140342150400c0c0c03c1e04020326000d8400ea403800c03501c245120885500d40c00d0080000b41040b00340c0311002220a094010440014094822400d0b0f2041c81c0c1c00e8200d800044c404000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 212104109 1250 212102859 212102861
    0x5010507020105091c03030c090905010b07060b011407110411070203151f030813060507052e090f11030706020a110a03050d180e0103030c031101020d0e0c040c081603 73
    0x18a8000034050300b01783e4160b15000700d0741951000101d00181c1c60320000c042107a004040540544000c80c0203104941c10000145101d00850b00064507141d1514800105a4050600c03210044807011190f0390315541030030b00c09480c2860358495809a8503220000d0b514000e0351042d1480076900030080e00c62078a203640c40d4013000d0000b83ca1490807464020441503a20b0543c081c0c040114441d654032510b07104020468503075116141e10281c04c5c070204019440010b1400309a800c916008940075104240d10360f15040c580f811b4038840a24450300e00b0358600d052140703208036602258494030a2440c00c1108a00b80350f00c2e000d0700d119070000360344002c00c035000007150120030000ca44000b4100c100303d55070343c2d2101c0d4038007a5010002000308450b6040704404070303c6804240b010b000f000301d12030525450b40d41c0081540e20128800340c2000107040c024008034400b03404540401c00d81c21400c3c0040503002c031140b501d410440070071900c120709c1c019124441b80c0c043c9614500c035a9151418080002d0307111810740c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 212105359 1250 212104109 212104117
    0x9090a050c0c0d0206010504050105010809060c0c0a140604060c03060b0906030411061210060f17090a050d360509101a190e031b030f01020a03020c0709050105010507020105 76
    0x80d25a107010300015010303840c1041541140d0141394020440781d4901001e0004640c0181c1085041280b844100500c034200086c3c0a82c0007551542003a035990f80401503203041503c0c0d440010001c1400c000703076401c11400054102d001d81d0190b8001c124184030361800368110744461182c44c828190501441c0b0300b901e05080078580c498069040080c0a0b03042400050140e03111403030b259145c0750001c0034440301e4507103105004040d200c00e00745550312000301e25000d4440c01c00541c0c81c00710b410300c040009964007810302841107000ea00c6030031140e0055407040c028050f0104820340100c819124040a014035600c12a05440c050903000c054400780e0034603042c0400444001c01c010b1003002603a0300040c0501c2003a9031000e030048100242d40d182d5402d902000c10003d0503042c2e00c1c040003d507840c004920350f004110720a041410100d0980c140d05048040b07410102188a4400360354070100704222025099001003803a00e5200e016185034a40302c07050302044503003c0c025140040c006120340001035024038010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 212106609 1250 212105359 212105371
    0xd0e100b010e12010b0d0506010608070c050303011205030c0f01021902151617090c09250819060b0705120a0504051e030607030c080601210c050906040f0608010b09090a05 75
    0x100d680c00d0303400003150102c3c03070340441290347d5880400100311a540c005e0810b13411070301c0c610b018041c0310b030f0300e07218141d60340410700511300c040c0c1d2103001940401c00100201c608010706201564801e404050a440c002e400504e40c64100701013210348008407510204032a08002d4085040d01090345078043c000d01e80c51034241481c018840c070901c00f0100c11804400940c42130300340400600101403484103101200070050908418944014903102c03043c11800c803c1d100070400c1c0e103042010740e0340b0150301d00304c460031151509025034500380001c660001000002d180e030138014000c89091031581100f4500511480f95268001081403105001600d4000d1142400464680d031054052215200190910300251000c00203e965840381d4000150003240320380c1e00c510242442402c0010081c1514071010086800000b19607545407840300303150140d020707903088003009400d01e07445070745400024460f2046da010b0f013004907520200000e04001e03560300f11046940c029012582c15250101c400c0082c140107480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 212107859 1250 212106609 212106611
    0x6020d0e070b09040f06080a200406030302150702070303020616030b06030c0901090906210503040305190b012403020904061e090e0309010509100e060d0e100b010e1201 74
    0x3154010340d041003120003034400d41c0009540e4240c3c0004020841d1201d030412901d01c1d040c24010031510381d0201e000d20750542c118110b500300e0f0200111100c4c0d1040700d10b060307590242c0740c914040f044c0340c2e000485544021089503d4807083e226040c003170380d031112070b03120050050b4401c00005403450b41504110280c280c0301e040104800502d0400145550000c60301c1d9002c1c080c010500a03003030360b40f00403c0f500034180c0e20010003c0a0401c0f0f0907614070309064000b6140200000a040e003002000c0080700c1c01942c0100070f403894007850301020a506050b40000b5a514420500040703515100000c0d0169075841130042182c812001f24400d130042d4220341e4005038815550203000440e60b1001c903600d610400152242501c00d410042c054084521007a5051840c0d441070019010b02c0e600103003251018141190f141c000e101030540304a80780041e03d00ad207600504082000f407002082908828465440c034800c1c0c4071481c2025100e00d086900204800b4005150015403004505150300503010801c07034100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 212109109 1250 212107859 212107871
    0x60913051006030332030105010c0c0801020d1b0f20030d0507110f03160f080409060e0f150d080f0c16030c0f060c0b060a080a060b03011b020a06020d 66
    0x100090480d0615401980400c0d05c030245c0c0050a25041010211007500881e0f0401034040302070300e001580014007881d4140810841d080c0305011101c04104002c091410095688103072560005014145140b648240d1840e00c0d08100c10480c014500a60310540307954031580d035007040780403888040e43c4c2d03500007400c280010405d20071421518021684034050755102c680343c00880580c01d6151616607005401c0941082c04905074150440d003241010071b4000c070881d0004030207410080440d1186611200d0f0b00c81ca840400100f002d80c1c0d031440f51048281e02c6e50004996a003901010340740d840307902180c4d44810004500d10008001d400500101084a90b0f40d03410b00fa0307188619032400c082c800d130001101d034104004008104d40030300e00001400000300010092071400b4005017840c00b5005008209820040015100b070703c49107038081c01000713440206c5200600d85e06082000380407020700d070380c0654280201e550b0111025010907080710b071598024541c000440c2c0303c82000790001c0043c0e00e0841c1e00c1d11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 212110359 1250 212109109 212109133
    0x20405010f180216060c030e0c0604180b031c020105010f2705101205030408010e030a02030d0903051233010507030c110d080c010e0610090f0b09010f03020103050f06091305 76
    0x1100320300c0e80c4046e50b10f00083e881500340f40b0b0b03407a0504550501c0c3c40f070102044140954450800b40304200c007c240c1c3c0225280c0ca41100103414881444c0e048050341e8040c1400b41d40150381500058121140f01e5110003003640c503044002c0f0240c04038504541042c13100700300380040401c69800300790300c01900c00740f420764141c64034207003002a10703d24800e58050348041014081e03030314284554100701c81c44200940c6010450200651240a10b45440c02d8140d0703607100600c10300d405141100d0780b694000310091503503d003900300882c4241d000140f141000c44040154120906104c140c420301d04016180c0e80e0030f10f40700d907400302da050324084811135444000c00049412912100703a921b06032445820070588420400c0350f00c07400c5a2055985174842c2d03105030300f072010001031004c8180950301d00c00d0f408542c002e072108409000d0720141548980100c440c200000d000b84c001c3c4004002e892007640c09104581350721400b2110b851040e580c05034040300e2400451100c9a03a01044044240300d1000c0d40e4901e0109 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 212111609 1250 212110359 212110361
    0xb0301020c010209090f1006050c03130b030117071a070c15020a0312050106080a09031701090b01030c021506060a09080114010f081c030f020d18020405010f18021606 73
    0x1010940304143e402140d0360300185420030303510b6806030042d5a00d402c00d25044a400c02c0848039449007400303010000031864029803050084035031900d4070944400c420303969880c00c41c040b54000d21420b040d038131032090021400300c008100e440484250f180101c00c0d841540b8511080350f44800400c58000f0240d00c1c0000e8542c6070b4500c0010107481503009440c4071056030401030103140c4031215040c02d4a1500005210213030b0000920707908000c0d8001d0000d2100c04a18083e1203561100003011110501c0d000002170f01882608511070245003a602803142d400000c4c000c2e80d03944030b01c1c800d810180c0c0c21007000402500f0551f02618800d151407804d8406150740c0ca08240c01c584020903001d40142d4040010b100d04d151809103840241300001c01403161162040c8143c0c036110060f88240300b01a00d0340501d02048520342c055424820306007004210101c40140400c001612030036080f80141e09010001400d540c0352070300d02c0d08440350060704139500c1d40654400c030000d5002c5507402400d41d41d00490007004c42d1782 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 212112859 1250 212111609 212111617
    0x10e070f1a030403020a0314070605040506040215120a0903050913020c01050c03040503030708090c030f1b0103230907120b04060605060c0d0e06041d1603180809040b030102 76
    0x800d140440986051101298040086400c00c40310800e040080c00002507001802e4020303290185011003000403030b428030440c10700c01d202020701498101010302007403000202c1c1c2240190b208684010781b1040c1103854048034042c050032011a80e060380009242e1700f4441d04079800103442403030300c54a041880000955000c03540c2c0e030485c209a901007000030340e100c024460030340c01c4045100c0c01d6065103015510581e0b24400244080100f14032040071480e416400c00c1110b006e01c0009081d1030440441d0401159105c400205a80c02144140100c0350b40e5400b910403a6a400580d441c803034050f8094001d05212103002422801e49445500300c0014450512600041082c1c400c0540c0b102c02d08043c2019025150300d508054401d83c001c0100c0036101a0003c0d05c416480c0540c145030b500c06d064100018100d0142c5da11902e40f205014105403101c4d03c80100031071044030081150680325010a00840454107400607507654001c1010250000c01d0300000901034412000340042861f24005010a09a0704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 212114109 1250 212112859 212112869
    0x913171e040f0b03060a05120c060c1f090206041502121801030f0501050a09090f050a060c0807110601170307021f0207050f090705030c120103110f0108070917010e07 73
    0x803001c01c05100110360101c6280090040c094801d046090003800651001c0c4144161440fa50b00c40308020740e208030601401107000b100421240d02ca1840950644e00c50380c10000303945441c42c50f070490108000741d40c410030311260f8001d003100d070826041c0300040055610b003440160540c8100b0104030201a2000018400c4103036024268007484081c1c000507050308c42411104070120b0030440144480e465500030501103c220100108140700315007402880c1822000d40606680106da100b10244071940d0003c0c4400005681c4640c82035440c2c0b0012039081c010f5140e4200c05400400041080c416189007840e070000d500c0041c0e074a842129400500c07111600001006550503002c640324a5640511507078000f0b100580702d900d0321130708071030015080d0070005000c20f060020200125908509850544881031040d000c0c0e490956182c0c18105038038000341c2d1000341f0078030b8141c2481c2142d500c900d407060301520f100c0c0c5410400c54206044a4904042e45522480300e650311010480ca26408021f845c000b08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 212115359 1250 212114109 212114167
    0x40b030f1c09090506031c2c0306010b07050d050d06080f0105010e070302090102190c030c0e0402040606050906070b0415090b1503010902060f03040f0b04080c0606091317 75
    0x40300d00601a0400e000b41e0301c40b900407440c21040100d039803000301d0311582c0c03000d112182408802910344117440140ca0700000007100b0340000c0341102141d80d0701100307003d02c20f4214100e030300681c1d0b40c1e40341c3c0045100300800100180c002080b0300007901d01420140c20511035003103000c00c140b5111400c0500c0c10f6030748892840b55170f4440b4010000500142040740d08034203d031600790f25003000382002030b545181c5221070300b41c10001d0032013a10a1008030f8028401460b40440c41c2d45000369184041c1040783d0003610180d1040385007160010311140124125020440080c1095082c1034842e00d07005060718009006030341c1a84036128048a0782c0b2188510801d1500c0341c0e1104a142c10320a075080f002001c04100c40d8080c1e03140402040c051317500c0e50241c803a040c0320320758156541d51f9985400f615080c0780b008000c2c40700d46d4a0007400104004400a820040c0c0c0f100304542695580008028000e681561b86c0381d40400b00210390408203086400104400c0c51040b030300340c90128500c0406148000010501c02d200c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 212116609 1250 212115359 212115403
    0x5030a06090f050712051005220903020d02060601051602100e040509070f0f050a0b0d180803040b10030b070c02120601080708060a060602120309010b040c020610080a0c05040b030f 79
    0xd402c40c0303400e91440310017002045645040e8580100540560180310f00c01d40340581a07501e150300300300518607002c0b0f03100020701096040b4500a9a03c88402e00042c000d800740c80c002600c00d5104070290341c0518802041d80741101526002c3c080440d603056001810072007407040a042c1d40e1610300405000d500700c900101201c0f4584440c115415a09030842c0e403449260380001c006035620410703031005658049403d641d0340d130700d00c82e4628002c06a410b02c8901440480010500744803001015606c264001e4415400d40e94030281400f08028081c080206100c030f850011495840c410034141c2003003031001e013084841507801ca92281c5002c40036407200910b0b6000201c1840040002d1040e103400501c0140140711850801c00701940707940d41907101c0245210302000080c80060300b5004007080d000054010405c1c000700d0103000303483d00f0f0103d400c0700400c4050700380001d041d600003510b00301d407a8200303c00d681007904100421010b00405050580d0520481d0b600c90342414081c01415a0403180e600081c400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 212117859 1250 212116609 212116621
    0x90103090503270a090506090406052a030106030609021c1a180a0605030a0f030309020a0b130f17030708030a1d070801050606190c06022b0605060c03070305030a06090f05 75
    0x4640c41c2174012259560502d01400500e4582050349504682d100d20082416074070703592803d10b0090704000c0d9464803640c4040b0429540006001141622003540d01801545c0d110045242644962560350000312400118100d88034501e0348002c04c90000c01481c085412465030001f40076904456403a0400c0034464140611001e652058200915098011707080401040d02e4090b04600306481c003509141d02c50150000310b540313920007040500300203440307580c41e03507440201651400d960340510185840b103d80b011901c8909640f4200c0c101814000035450440e880d5510307011500060030710150700c2d40754005400c99018030403010b052816500c0003000250f00e080c00640c250f94000d000c590194104004461481414024202030724a090030101480c1550380303814002846154002c5c91614840d03c280300e544010f0f409070089010628505212b059100d40c00c001a5100b06110f805450340100b00e0f2000103401900956440403240c4000209c03a6a1505200e044c0c4809150780c1c9078150b9902c08100c2c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 212119109 1250 212117859 212117869
    0x90d030527060d0b0102071a0309061510030b0a050301060e0906010f050603070305181e120a020c09130c03060c08090d14160606080a05100c0509010309050327 70
    0x4192000c9128603000107901d940802c005120b00403c040c031441d11014201c1003a4020041c5500812145600034500600a410441160410340780c005d454000c440129442d031b641c5003080e140480006000c0003c0010134a0182d0061518110946c1c101c070105100081681d403c1c4640c8008200a5001e60302516100d840c40342440b00581040541002901c018070a940300c000541c1d034420384500300044c8540701c0081400040160a000002c81c2c0319a09241000c1c8060f01400e0a039020014210b03075a40341d41800ba94050b004070940000183d001195a400910b01901d8141d081541c607001c0411100c2540c0f1500003062141d0016142251582001400c00f81d0105055611828680180040c4540c08074002c2440081d1110041080c0d0046001c000082001500d1140b65a0049040240994510025440b00c6408109845e1400b56601011655185009660380c00f01940c0d1110301d400b1800700154014601c0300380950b0a0b11013032002170980392800d1003041441c6c2500304000034000581041203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 212120359 1250 212119109 212119147
    0xc02031005040c1512020c0a06050a06050307060201020f070f0c08010207060507270e07050d02030103050601050f0a0f05060304030923040c0f0804020402030411030a0303141006020d030908090d0305 87
    0xa003148648180d81c91490f50017100028003507054400540d44400c1d09290324900102000042c0c81d00d842d003800c0c030000213090b40c0200201c3d00c0603026144490342e154803d0b800c0380590b011807180008104035050026001c2006881514418511915103e480d0100e036400c98000a0707044841c0c507961803d01200700d030070104080300c01315140340c400724002c040c0445910788030a80c4108011240304c000490082401802920400748443e58211740ba5a540c1c01c0590741d91500b841f8182c010100d0104245e0f042c1025041070050301c51400c00102100c0c544400d112007580010300075400c0102d0b0041c04a0444225165480394550301c0610a01144560042208448203640707480305005540765143d640941000840e5801380c1c046034010784aa0b078906025038604031000d00c650303150007882801000c00d40c06a11000c40484c18403100a41e580e21101c04a1303828010b80200304c050307032000120302102d030700ca5040401c3c0688900310301c0b81481040ea0200790007403418401100403d502151400c80b502c9a50592 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 212121609 1250 212120359 212120369
    0x2001020306152107090b070c0509060a03021e0f28060801080c0d1712010314030a0e091305120714011a060a020f030a1707020d120c0c02031005040c 65
    0x21454143c42d009421480c40703020403025080c901c0000065100d0380251050801001e00000f42c5a45214510f80380e07074000c0160142600c5a114600822910b00701580e4810a890b406041080754074040c94040031200303108091160700960390a11f40016845051503840c403902d911280380040003080c0c910420100058100c2c10800010b04010002e141000504980c24641916040009001c904100171072105015118000030340018200c810206002d043c03504a0740244000c0039910512802585c491188041e0500041d40c26140c0107543d1900110440d00a5403801007842c280310a81e41e91400d041131444183d65580c1c0201d009010301c2001340710b106003980c20100070010400c40090910710b000038201e5a5000b01e001046034940d240c000c00101c900301e0440c808032900d503464031300000c000e5008a00400003800a40000c500d5680c000a480e007001c140700d4980702645004a02580d00815600c2031807002c00100303e41c614056241400700e4045852001c1c000304141c17900e410a01c110050507440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 212122859 1250 212121609 212121649
    0x10b030a0308071b0812010816060504090c12290d1a0426180402130b180406090509070f0609030b1005041a151201030209072001020306 60
    0x38040060ba0040d041c40d07100b14142042100307120081c403858003000280700028400e1000164213901543c00c1000e4034129102c00c01110803402404c4907200c11440544261008504180801d01a10265030004095918940b0b01240075a0700840b000043d2401440380080c895030f80140c803508001202c1100c1090b0b041a00e02c200003107030719901d030081102103a81120880620300049010000c0881d1014108844030303200410b00b800c941441c0559500c5441da0b414025034000e442d101e01c0c10580242c894041014002c04400e601e0060007881e1503000342d40300c149074402d0995041c03a559030ba01c107500c0502140c610000781860503680c1d1a2500c1901d410540990885004c1002516400070f11f0b030080c0c0e0f5001440742043c0c2c0f11202d00640c9036441d9040298020704100b89828403641505a00f281c4080840e40d000c9444c00740203241c0c106104000080441802c0c07c00180094244040b141c0c2c0c0140b6280f4010408841d078100c0220300341070080da09809650000f051106038940100303000c594200c00345c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 212124109 1250 212122859 212122873
    0x103020913090c0902091c030219030e01020c040c08070c020105041a03010302040609090f110a120503120708240d08040605030108012304031116080d11060103030903020d051603060e010b03 83
    0x10000d0700c2a8400f501c8005502c0c41f01000f1010907200780005901340e0420b4011042c102c400e854080e00340310301554250b0052040348100000c40c502400b618000c0010341e2102c00d02525007c0c1c0845541d0086d00091b8144501000001191807101c00c0c40b44003034400d041545d44030f504500c10001524169803100c04101d044c80f040e80302185c0e13a0b20b0308444030b40d40441c200349803038110004100420481d6110541071420154071409100011006000142001c060038040d95503200c01a145444241d402a402c0e007400e4101c03003d0b000e00742840600400c2c00809480c80140707550340b400c1e89030b8400e0300041300091011004010307244090040300041280c0046410b2100100201002081d000910140403c8a0301d185a1030b074030b8081c068403c00d07584000e00b454806454a007001d90340e405d085020b9002a064071241400c1c0746011a1a5058a50650b5010503051864003041851454100140e4240c020700c0710349000c0300000c0c00c2803001103100300340100b50700d10402100b60846090003c6140a900400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 212125359 1250 212124109 212124127
    0x1c02070b04210c05031603050c090f070522060903170304112b0503090a0e0402030a06150b2109160e0c04030506090a170f0a0e0103020913090c0902 65
    0xb1100e8540e4050403000e900a102c0242052185640d09601141d014044c0380c4502c000d84c000300460078144ca020b00211040c80c500701050006c0503900300c6071007603048618404681c5451082e401411035002e150243c0300c44200400301484078280b00d60004010038001c041c10070401545a8018070070f125400e00707240c1545070035115040030960305d81c030b035910403040c0d82c42003103810100600c0342050781d400800310900d03a1801d2802ca03680303500c600d81051190309c0c0070f0000205e001049240c1c51085a01401804c2009020345c1c5070390141c22805080001100d2805000c42e52282e104080c0944606441c80c02884c00a00300d01c9400380d2201904207003142d0003071100d54128494201805003290003036030555203240e4907810188101c4c0030350b0b0801421802800c0038806000381c0025a14080c50050782a0098188403109032070451080c00340c180131440c1d00344000c41d6181c2c001c0749094151003042c14003618150402c00054010124000c00340442d503075030620142480300b0300c50914058030b442da204519003a029 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 212126609 1250 212125359 212125379
    0x6120308070906090e18011418032b061208030604202a121c0504120309060b060403080c06010609052103070c0b04060809010207081210081c02070b04 66
    0x24042c18085d4400140401d05006000d452550300c000745500802c0f01d600c500c070400c10f2841003a02d2211740c2c0804a5007500380c2400110132102100704c1d140421156a104a416035030309500c041c0da1401403561080d0000380781204c00d4040c6c5205200c0c922441c0e8030314114042104407240700310000c0404081c0c1a07601c4c2c00b80c141c00100d80f1488680301c0d002b002c40074242e210390003594400706007802601a14130100d0050340d400004d0010901071000351048800c40b10031a400700c49007118003800340f1440070034154a00713010740e010b03021190090501080151440b400301d4084c2d0711030b078000c54464900151032074061a0030700003107000d415185050310706e261030305000400e10082e40b2041d419082240e44605500f45040040318811a801900703c0509680c0740d4076410b20340c020b48a43d50201e00000c002980d103c0b01842125200c070781c4410b469092180c41031080d00803410080c20049000d4000a0105410504201002c202400c001007540d0b100a5010000e040652230340c4000316200341404184100504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 212127859 1250 212126609 212126627
    0x18010c0c0b01052215050112050606040e09010b0a0e060102010f0e37030e030607020105060d33060501090b090d12140c0105040201141303170d06120308070906 70
    0x1040365004107405000301c0703940103078030041c0284002174540400d0141c0c0040c2020802e04440c07090b01c03483c0e01d01100e00c0c000003d550003203800c0c640c0035200700300500254034140001d5410170401c0b400081c800000ea0f000c5466810a9046049031985c020108035242d030303090140165a02d0403001c02d00c0012202282265a02d00c10751010841806040740002841301c00030f8650440b021754426100410310504002c0c4c0541181c03c6114000e0007000c0000c0c409500500502e80500ca000e41200c92901040e1950150b083c2840c1b0805100168a42b0107210440307140200c5045150034140011071078074190014055a825501407803100c03805000102403603466040304144127811041c0c5501002e042c04088502548512010300303c6000031688840700e1805501c0f0741e225902c00c0e283c0707244001400c0d00d00345240c05443c28800b050a40b000050000a2220100003a0310500c0368046040040c2203d01d0005c1e281c1d1600100700d045211001c0c0d000340f503485440182c00c0701c42c5041000081e820303e01c0c01022508 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 212129109 1250 212127859 212127869
    0x605120f0a0b060f04050c030f161d0409060c080115140f2206111b06090114040504090609060605010e0102030d230901020c0c0301060b160606080618010c0c0b01 71
    0x102c0000d24103131030303480042070300c03c900030010007440c031301140d6101d0160003d80d40d21202c150b4840c00100b0310071440282e270300188056105c000507048455401140d01c4000650107410544480440700003d14600911001c0c4d807243c4c441018541c1003004400c21074051401c0c2904000c1c80a07242c05a0030008012554840c4212021a0b0b07146030380070004855210001c82d01c5400c140e1090001750761540400c80b14010082102074600d0b40d08890b44281e010b5122282c400c2c0c0c406401c100d80011036006196107281507410040290400d9641d83c0000c00300e817101d05058139402e49803450780003042107a200360b00142409082c41d56121128000007560b81c015040000300f0940e0f10690a18414461071301d603060020352441c650310714a00004982e020f50059002004c0c503100301c03011454030b842e06016800903144070011140c00c0502e241c21180b03166800440075074449503981720200e110380d802e005440c424202c600c3c00c032507810410020207085a03504e00607442041078a4021100040303520b00d903581190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 212130359 1250 212129109 212129123
    0x14030a09060b041118060c070305061522051005040c020a02010806060f0301170705130c0315050603280204030506010609060c0203030405060309011b110c041a04020a0c080c010605120f0a 82
    0x1719000010846c80c2c0b16000a0440d00d20555034004100a400510a8072448001407031854840005007441400c01104402502110a101c002a4019184e5014030b0b441000d048040951a5440d00400c0488020701b01c5100160092050038056580100c0000d070001000d452007451300240300300d90a0240018015002c01070651444190010000c000300d034003400000300040d045000f5550840010316a214440e80800c1c24101c41300381d211012090f01049070000b03000d0601e560703607507410603184c1d500410005468a0002e00005446c1d4000d1000d4006144a1f200501d4154103141b00640072048a0b4400c0c803c0201800c4810010b88000c03058901b140e0058901d0398a90b140d050f50103014040644644460002c02c03c042d20030300364400307100940e540e801c0303054034840e141c442d092005440c0302000c03000f03003c04070502c21120303801c081c3d004041c000a24513108140d04885c0d0f490600740d5102c102503445582d101d0748103110520f401c6058803004c08545005140c06042442d8854a90140d010090100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 212131609 1250 212130359 212130397
    0x20a30090e1b0c030a05090906060c100b030f16060e0907090311011b05100e03090d020d05030c070b0a02060606090102100b15120406050f0609041214030a09060b0411 73
    0xa00140025500c843d40000c0aa0740c0b2640990301c010180d030040d41e1031500c6081d441c00031803110305060080351034948844c4060301c8468842100200034246900305150181700d4240581d000c3d150901654120b40044119907005a2820b98002c120980c0111064454002d0303805110000d504403500404490784452504180502c040041e1174aa189403008d01507181c012000038100400402e11a0301d00128034410031100c0344240b062a030b01c1c0039002d4204e8001c0781000340c160161625200c0d0b22034061042085916080d201490b56040c003409510002c1d41440c0030543c034000e2034050002543c8100e0031b82d6214100425480000e603107441c03c2c208101c030280c0d41d0144003070035251040580c50401c0340c82c0380c1030340e64400c0e00c08035000700c2411107065560918082c00700e0030078580740d9105400313400010807051403a101c98440034843c8041440040902003800000500106000e020398032404492400003603c031428107000301a40e121100369072046190818450307101d09100c0a4032482c0302070009118103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 212132859 1250 212131609 212131651
    0x120a03080901060b0f0d11031003020616020d150e150a02090a0305030a090f1d07050d02070c06090311150f0d0902030307060b0112060602030316020a30090e 69
    0x40583c1d0300034907100da0000544c0e14150b005403006104001841104114102c9880d402862500003030350b41c0001121084810005890702c035000d4658815012400840c031141b607400102076921400b070440d603400840307603030400c0d1185920916a501112601820002c00c0100c0404181800100386000556000c41d40130400d48441e0701c004084e65001040303d0381c540552a02071b240141074414448210318401c400314001500c0d004c0c45202c1081d1582140050f15203101c180e07615042800104009039003482020041050070945100600742d64940d006a28194140031021072a1050301602514141160b100020300c03901c11610035095004445840e00d40303500766400640202400a945840045501310074064280d000c0b850f151400d0300c501401c041c0c0412501c2c19a00782d4803c0c1c01c056001400010a8452000780c851100310341d51050b202c800c1840d60703980b05c045041400d4003403220981c01c1d0414082c00104800d00c030001c283c0c10300c0c8030601e141c0384142c98020b100410071001d03915140c01c540c02d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 212134109 1250 212132859 212132861
    0x71707300609140304141c083a0c0203070302060a0513050f0c040e07031e08160b040b0901021201150c0b01140a0e010b0a030e030906040603050411120a03080901 71
    0x141c2d240d407201d0308045401c120340041c0c0c0d4075007007400b1700e06032900c0c956121082403501040c20000f003c9044000302d08920281c50b65807450700540012880108100d600c0700c10300084a102c0b03502941003250a41502808003080030495240b00e00d01010b5600c2040980d01003a0000303422f9a02c001010b10200e099a107a0703508031204200400024060b22500240c540481404207024900080540382013282140d04540c41e03071789200a2001501d2030080801d003100d0040074403840e044003801540050328280086898071400d281002c400e445034403101080c0800c001964036001d40040d4500025824507824650311203014406115070318101c102c2ca101c100d1164010380d1821101d58101030000322640c0c2d903030f201402c1e80d070807246814480c0c4203c80c0c02180100002d505603060707904404c070326805c040349507805400501c25007100c0c03d20b0784024450003107240e981070002d0000e00b2483d903011035181003070b19000d50340c0ca003510f041d42d00c01c0840d1407000b0721070343c0b000030210002c0c0d816181c1554a6210082558 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 212135359 1250 212134109 212134121
    0x60903110f151b0c1804030e01020319080406050a05150d060b030f0f0f0d090b0d09020a0807060909090308042d08041503060513110405030717073006 66
    0x100003002c040703650000c08241c80c80480229030440140c0c0c08a0000108022255040e44040c0440183c1c1d54041400b01348600151130324800d060045a240100890f551064400080b2201001030031040810042003110700031240c0081c1d25880134400d60a280901400070300500b0b80142c001d001d410006403d2142d1504500c62806016007625000303403241c000151207041540160315a4480c100ca88030001000240004040200f40d44401107a03040a807070301140c2e80542c0e4038002c40d039103405046000d071b56011181c600810500d001045014130f020005000c01d6807030b078000420a440e054464000c03035007007410386a000d81c1c03244009201c069034102452007200381401081e00c43c800480c07900704000041c0000e105840d1004503481801c00c141d0011001d440160051642015015200444022603500070a00e419550894036017455254004a858010070394801013005070322003045803900006000300e2014103900e5800d04000148038607528440c810211a550f0010710348860300e001c2c0001c030b51002c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 212136609 1250 212135359 212135389
    0x6050f09010311041409070807020c0904031101060b0a11030705030a08100906142b02060307030e0102030c0403061404170f0c06090c040501061d1504050303070606060306060903110f 80
    0x95138849440d582c2d00032030340014a038114025045000882d4115001c0c2820611440f155030081410b600354005002d24400301500842c2404408900311003107107803e0140d80081c0c0351a001c0d0549500c02000003c040400082103c0a6030308208103000100d0b0011084401c090624184041c3c0c0340c41e45c201d00c1146400c42c0d8045101c6a28200c0003140c103e80030402c0c0020341c142103c01c6001c0c0c900c98840344884040c4201d1078800661500110401070410801031070b445552410005401d0460500316400d82c0d000302c9010a5003200090240f040007094445c00c10780b800104600b14152400d40d8550440c4405414101c40c00400410025080c42c007030380442d110003090b08103555940c100a079031940c1d140c500c2241648114142000400c8030fa1180c204410002281d080d5030440700c03561010701610114410320351607040001c100210b40c1e43c40400003440300a01c103100c00164a803030940018121515034000fa82000310201c0c040002c03601c4d02441d814014411944141c041c0e0756a000500c903078020b0170603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 212137859 1250 212136609 212136641
    0x60f0d141f0f05010b0c06070309050c03030c061806041203020706060f06020303060a1a1e04030605010e0702010509010605100509030c1009030204180f1211060c04140102010606050f090103 83
    0x881c44184500341c02c1400582c05031502440309988452002015000b45085007600b68401000105254442c1e00305000803405042a10030703081c000303404241168002c0786542c40c01c1e84000140503a0000c841c00c0c40b407808000b040648034034149a950148100e6140c00540101500810083c052103066445000100501f00301200d07465a01e580c041e4132600100c032014403503881141d00050640c006440180c502e03000a40c11450074400d90442e1200c242200341800100500740f00c04030005040d4403030580a01000c5400540314a4903450003420f4407001040303011542d04003c02040b04c2d84400c07000501264041c200940c5400010f00464030741640d80003070036800762a2134609040650000f6100064034026102071101d4200380211845682d07511600409505ca60440c1d00041a1000310201203a00c0310b1600502481103103002d00d1515130306032a00e0003071240c0098104101e62140420582c2e50301d0a00007884060700c1c04a024019000740380c202d120b9040d0000c0d04140300c4c0c1c82503100c51030712540c2c410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 212139109 1250 212137859 212137903
    0x6040b2d0303070b071b030207051905060a0c120507020a030b0612010c05030603071e0302040b0d050a05010c0914090106030203090309130c020c030303151005250308060f0d14 77
    0x400301c0d00040300345c446802140031201203058600054107904c14841d0190010719199103040e081c410901180950507080c0c2503a0100407885603107031401000d2490403a511500d0010143c2002081c010351703110a001031040401003040161520703c85907040b00d8026005105941c0c0300b0012a80d0424010a00c0c1c03165407070115801c0c502900300d00554003410b000d40891304200d444008a010035030501045040345102c42100b0401490182c021040e8440040c00301c10880300789640c3d00d40f81000702e0008031402d07512024225012070b0300c20040390041076400446961201050085101d800d010b019440405800100088200004100700c9010716805043c0c4e141d60340c4010003000003401030060344070050184d4844010f4925000007903038020020050700d00061842001007100d100c12184900d270178030405010900034040c0141c81804c08400541c03200c0001c1441c0c1c034000f0314941005001e03e00c41c110f554481401e03621410040f01c691584000003404800c0c440c1c03802ca144c82000c40c240003403003440344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 212140359 1250 212139109 212139113
    0x30f0207050109030e03210c03090303030901050a110306060d0906061706062403010b07020429090c030c0f0306040908040f060f1e0c0c0e010f080606040b2d030307 72
    0x5440000803a004c0e555400c0498002010503880c5c011f10a50761a100345c40801e8145080c107440c1c01000030b45925002c5074a041502402b0a0440e04102c1d40e080c507696559003008401c0029004d48401110a20781e01c52461400c034000a10501540c503444106580d611a00700800045034410406011082503080040c2d0288901c10b171f071004100c2d0700074040c0718012220368000c001300c40703524000100344050a08603030070712509241d650080c40c001d0340d209840b403858000e5000c00407034040380e00d0002001141181000e4090100c0328501602d1300026020030410440c541031400c003500c1d20640d615000da9501e4481000040280044ac0800741140000180004200356034804680c12186203856102940d26071007015120840e44101203c904018525408811442103140d0550180302c0e00e01441c0131500c841010241000980007544a40103548042c0003002c0d0810503103921500c1142d083c41200210800b054401315811000c102011002010001c0400da1180b01001d0000103802c59031924054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 212141609 1250 212140359 212140361
    0x402070812040f06020d2a020c0d030201060b040603060504181203020c0a08040602060402030f0a03081303030f0c05130e04080f030c070f0302070509060609180903040f030605070305280b01030f02070501 89
    0x82c0c014101070051041f00003030329640d0030f600d0100c55260050207001c00c01a0500810079644d1800b201107560325a00803030301300d1000e005807014044a6074001160b80c18041400f040311003201401ba0203250488008001400c210a903940055213850f0141e11070415003031161828140da10003d14590b0045008540142d0025070184143d000314125640240742c103411a0b1100c07580c00780074000440c00400074210b02d42a6141d80e115600c079180000d0920f918543d608111400c00c4861000a40006a804e6045c03a1008180b4080c15440c400da440c03a00301540e80c2d03045072007107402041a40c240800051030b1650200b050f82d4080c1d8211405140c800035600c1c0094445125000b041e21400c03c03000801c406003413040070b48080050140024411320752171248200760040c000c211208e03a02c0304010100c1c07100001140407004504c01e55011585042260340030f002e903200101440000c40011801c02500c88641440401d02e1002d4070001401d15081e00040740604120494040000c0c00060368400308181 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 212142859 1250 212141609 212141621
    0x20309070b1c110a0e1005030a0506010507020d05070f060212090f0d0209010b28200106051002030c0625030504020a0e27060c0a111510060206060402070812040f06020d 74
    0x1035680e0b40281d074217000402c203c01182102403c000382c03090000134440704003548000d80040d8141800c40c14a006907002680700c1c00411012940d039085032104120585500110170080d003035600240004802c000c1d03000f0300d58014140c100e07101d061420291b00054403115503180300c554028014035000d40c0c480b100c000712907129142c1c5000481c070070808100501c0704180c0a803050081ca680701d1701c40c03150503403d14140a05441c11101075560301c80300000d09a0b640e81391707401000da007030b0007554039921180209420709130018204404240c440c41e0880402106520f42480700031907040000d11500d940c00070038940226134212003c8058980305101404655040101000550540301548404a1402c003074803000c003034506208181040c003d00b000b0a0081c01c10320348030301e449000c490490040d1580c0402049040d01c01d106c0295036540300b80001c9a040c0849a40020141d6007989031001964030b00001d0b2280300d0364650444a407001103400c0008241d43d082c80706400840540d241d4501b20400e1004001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 212144109 1250 212142859 212142877
    0x215120106021f0c0504060513181a09090a080c030f132d050609030309060a08070f020a020306160c020307090f0f2f070602031303090504020309070b1c11 68
    0x910a607140c484015004044d0032007460b44c2e80e01d007001d1038a0020784403600031110400050700ba110011406101c60044202c1c110080500400d814030300510f040900480d0b108840d015070130410070805c40e0030000802036460366010303036103d65484040e401e10b429406104038000c290b03040051420b0300645280e80d40002d0b14028642901c1140f03218502032048120700700110f585140c004400c0000749000340103001041c4018007560710b00030a4a00040540d44642754a0004ca200b52050218490b07014502d07000982c01e0740014003c06695400080e40c07a80002c2c40c0c0f104950340d10419018092107040c0d0012240c1d0302400321410507854450003800b8069010034000d21034944494403004103128000c007030640d0f400c00d00c5004401070441810400b21510036103a491341808102101c0014094401144209540f040c400300036001490000c00400b419400a44254010300522110650108800301100e500600040d40c4924031446110081c403150b404034282498540f0220422803400e000b050000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 212145359 1250 212144109 212144143
    0x50706080c031003060b0a08010212040c0501090303140a17040507080d020a170c0a0213060939260114030d02060c07020d02040606120e0606010c021512010602 70
    0x541c4012007441107001c01c036032141e40e40300b80c0c0004002040040e8081d507040c48000d400c8800054640c400300382a80e01040c2d00495200e541c80402041c40000d40402e001303403009282035402c80d469500d000346101592040c004407081d0016101000c5401051118101021440260341070320f01810103d4440005109201c064095405826841d51000c500c0000041d80440ea0301607441c0780d482c1252140e006000c60300c0b050300c20100701c4070240c5d44012080c04582071011000c18850300301032481c41544c1652404100c0e0b0b620a4503a040001070400c1001340444c3d030a4910840c0c3c01096400b12201c08000c10140c000840e03000c3e00c0d080500c1140c04544c141d071b1383c1d41e01c0d24030304031005005e040d51000600b403120b0050300b00d1004214454800402030401d680001e10f07982d20540190001422649141e102c7c201007a502c407440ca0702062203004424010007044054105440d0070340001e40f4003804810005d10881502010181c00f810110964401c4804555424415a1120b0020707603509650004010b13030b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 212146609 1250 212145359 212145361
    0x102010c03151211030109080706060f05090a020931050f0105060a1d040c03061e081e0a050a05010617061501080405010212090304090b0603060a03120207030f05070608 74
    0x554064054001824075107012898034a2424414020f9080302c0c0904984140e0040310803466640e00340540c01100f80640c0105550709160b18000703080320324541c041c1844440030b0100704905d0b61203507021a485800c9c160096900e0070684000b805500060306008450341260100503a44030400b07074100500d00e1034001c104420348404a8002d00148248a03556208008001e0781d001c840c072840607103c000c05900040117003050524001130554000343c05103000255106010040c00111040e0030081d000010a0707140e000b403e147c40d4a8843c5003a00306c0304100c40803403494403101d01d0100001008203030020b050743c084180c20316040d0301818140c4100300c0b4801d000d10200000800128031940504005501c0d00c0340506001c00550b40c4c000020400d132015503007072003080c1442c084980ca0034030030480310000d1740d940e90600031560704962801d00500d000390014030801c1030b10344641e40104166074004440082e1401140f408070f1802c4140e0308010980e041a0a1000070000c000420100341d81850701ca6044da = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 212147859 1250 212146609 212146631
    0x507091503020c0d05070f0c0e070806060c120310120602090306061806090408040b0a0e03071208030a0b06070c0f1a16141606020a060c0f020312060d02040507050702010201 76
    0x2c2e4098081c2d07401a41c1c00292002c81980d0055005080c01c1c3e00c035981000d17001c08a07448501c002d61607680104015800d000c00c02c8401c990010032594020400c940c0117003800030f02d400b0f0035506d0b1500d1b01d07400a240c07030020100d100e400780a17000000030f141034030b080120582c00d481e00001a4128108a60007481070300d000c584107291413410804d0800c2406c65102003aa201030402100110150090f150b0607001c000208520292000074055a802500e403401001d084209251034401141c1c40864008040b41e11040051a0b6000301c0e40c000c640c014000c55040c18803000640ea5104030030004206c0c00c42071600003050500a80ca11f8216000c0c124032051058013040340304058400c40fa0385035442043d00c9414000a0401c003105078a40c5910b00841e40150224540705400e1816030b044440545c5c8400e001c0c1c400c00001e070044843c115101e04e8040d011064a0f0350196aa000b81800c01030307003140b103800241454035050b90075250903400900078000780c10030b07002c09049544030003004c0c1d0043d4205005c03911 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 212149109 1250 212147859 212147861
    0x130b09032e05060a03120c0302120a090b091f090e07081306051e0a06030b0c040f12080708030a06060e0d0c05060c01020c0f0d0f08090303060105070311010507091503 73
    0xca8504080032a07019200c4500028000c09000308015400075100300007002240b2255034460150b43d00742c450031111403403814040d00e4240186800c0b400c4500c03c21200c014294415070180031908004515501c0b4030045000030400d90610118035909036022860110303c0e640312000400302d421011586100b034680070300403524040c049070f02d410340c00010b4002c480062034540c41039500070307130006880541c007801d407034400300c2e6200a40c1e0780c81c80c0340c0d111441482440607100c10286c10004800c7d400d0f2400f072070030300344039003104561180d10f2080c000c0c00511801e000003002114540b80d0700c14031a9650f807030000345000042515020b1000018541d0310304841d50f040c080e01c03043c5800e4008500200540c980001c014660b0300c44561088595000c0c00500e00800c420002300048941d02c1c0054090203003030710303030081c40300501100c9802007040c0780052010508000c812a0340041c400e207010342da6000325080c10755591040c41c07a020050f602c0e000401c01d0f43c9603c1341c618010707075600c6d91441c0b09500c00454110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 212150359 1250 212149109 212149153
    0x30403110307031403060d020a0b03060f0301091e03020a0503030f0f011d04150b19140105030f07142b0e010b06220503030f0703030b09090616020102130b0903 70
    0x4000c100304182042c150413024028640c00740c0000c0207882e802c4c2ca2540402e0080c0040d0b4040e1a045102005202561500082451318500203500811040d11181ca801c1e415030100002c1128030441e80300d240c4141842801940b90054001045030313901c2c1040601c1c90303001c1008441d00c0607141000d00c0081540361641100360b891070008401ca280949868550700c81001030710710b80380d0220b070391803100310040d44807031596955640015204440c0a880c2c51441403440ba001d0358018104901041003100d282c9100841d107810140f00d141c0b0861416003010484241e21400b41d500400b1403007801d41750740c0400c031490303410078181032200305102034240302a03150f0136100b02c1c00400d584883c2c103100e8101c140001449000c4140000d15010488990300e5010a085a0040034030f07030b10a541c001507400905405004212003204103440d101c00340d140108202d625214043c16400580c200044a40b00452003501034500c400e5202e03c41500059940712004010b61007091414001c1c0181004a4410084c0311918 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 212151609 1250 212150359 212150363
    0x80601090803070b07020c0d0302014515050a0507090603021c0203060613030b0708010e060a06180503070f052107032307060302031806061c050f0f03030403110307 72
    0x40d03080070f400765100c08840d24001c1aa00c00c5100d080e8455885a8841c042d1040c0b61f4001e0300005001656442d800302d000384008c5030a00801c00400f4021107440981421104400e5040c3c503003603a9090915280203000c080d0b0f40c2c00a1014101400e01046ea44a980014040c4ea5903840341c551451b40e921303056060f4017502504080051700200c9030500442240c0080d64010340c000c0c0765929200b218842da0f03492201d19002a103500108604104110f07802c40304090161a802c000d00030716203008000100c1200140c066001085070307110b0310300014200c008400d0042c12000382502c10f426142c4e00448501501481024850506100611400041d556030644030a920b0009407504d50700f5510b400c568201d821403001c0000f50400e50101100500340100000303407603960f801503543e0400304000250b100c051480c000d0650080d0050000d00d584400c10245520a28426071800d08007508180e0b0034002e00007203082c407a000c0d0180712060310034007000852103244640c48104d895114920712641c3ca000700140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 212152859 1250 212151609 212151613
    0x6090602090f030a050d0f05070213060e070306080d030f0b100206061c0b070507080c070e0106030b0105031317091e031c09030201030203361c1707052101060806010908 74
    0x128a0302c244100c4e003401202000c0c1c1048d03071410381c0f55400700305807010088080b0305050780d54500340b101210300c251498000f05c15140a124840c100100303540c550007502141c105055031101c59006202c07043d00f04942400004001e02000d20780760102070340320501150402c0c0b080003151a0201040040d05940c9030440d003102d403100b00d56851705001e881725403001e03005985503d4184000c07112454200107a1010704207000705030206502d8400c02030240c0d4900740380340d418404140204807002101114031907619411003622580c10703001d4650115280314003503803e82c1140b80d4440307007100403440f090700640368407040d0101c6e94076070220500320310301070040040b000000302c40900c104059807082d00955000800c04458442003050440141c0480f040a06082d46444803c144544460bc05201d155191103500c850a00d24400b41e08008160803c4c680d0400b00203202c40c804244100d01c6001954158502406c094240f032466080449600009110b1140042c0f0002c0c0001c1c0d09522944029089441c8840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 212154109 1250 212152859 212152873
    0x90603060e0f04020111060901090210090602031c1107110a05030102040803040603090302010f05090624010f200303010b0d0507090e04020f0102010915020d060e06030319050706090602090f030a05 86
    0x980c0d0303003160402500c1130781001724866090580c80000d104142c040c00d00d080001400d244644140124501851224014042c050904100c1590084201c8500030607854200000c81510041c0000810000056040c0c020002c20358804011101400b180c01010403981d591145a0710010036090344680d0003080b65a070004d00080040d0b40c040c0d000f821210340711340004513a2540200d00001252000c69503501513500110902107100a109145810a6024200c1c1142d0001020000c0d001d07099020100381040b081e08403049070185a1702e000b00751000a07105032030307913542d40f1104800140c110000c100b111616003400320760075500440701da1040f00c540b01c069000a40e59030f000c104c5000240d6075010706554844241c54002880400d040501c400040c1c3c0041e101e0800c905c1d4601200c2064103c4000101014103000180e03400009580c6000c1c9240b144014010005404542038041c1c40001400c0505108070101040180d80140c0300c24041a940b00a49070f0f5044105580c9084081c00600190030a103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 212155359 1250 212154109 212154121
    0x1505240a0905030d050d050708091e03040f0603270f0303020d2a02010c03180221060103231b0405090f03030a2a080a020319140601090603060e 63
    0x282000e4411030400c440704640c0c841c0401d08100641c007401000401c00250008030b0301e854482c05800021a01d07001d1100d10386032120550b01c0d80084035012600c00e100b0070310040c09200b042224041d00366064106811aa00c65014020b072210030b144500e9030a140c1031010900c0080d040ba00581c0d50400a0660b032602291415402503010310101d03054203448003940c280c00d40b480062a07498148024440600e20380448000303003140c20703900501040500701013a600d031220109120007041501100c0420541400d00c0d0750007a210f004440025850052400000a0000404101a00d028841241d1941003140004503444007111404103a079032400c00510b408505055000c00c1c1d00c604030808a82000651030543c03851500120789840081b0345555000d8580141d07150000301c1e1030031009099260429898015050f81002440545a95804030004035400c4008104424003000c12030104101e03440410a00d120140c210388250200f0110100080c9451080c0306400483c2c00343c3d952040151101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 212156609 1250 212155359 212155429
    0xe010305060a030204050f04060b190b0d180f0501140108030714010b06040905040611090d0308040609021302070c05060f0a050c011d0a0302070506070f0618060f1505 73
    0x34158542240c88000c0110040c0c03610b206e007030301949580e4502d0b001c515007443c002e0266205100814041d030741b00f151a035a00c43e5155004016100d50700c41958032400721402400041c484880c0046281c0841d0f00d085d4244414a4944803440c1c0c001c00c003d0107040480d04a820000c1000c0c89010349a40c8200084004034000810310520902d041c40041030f0b07802c0030380c0081c5642d003003504106402d40c0c4c0c0b14240302c1042803d03c0794004450070500b10300e08158601f00000c21626001d000a414404801d0000d000c000240d449501c5039a8000c00301403d071030984200e60025008041c0c00c440c00700300d140010130b451030008180c820b20914a1002032030001c803034400304c1d02c98000608240c9035641743c00c4600b280940d0620000e5071007940c40c004020b92000390030002d26000c001e0b40454001c500800000c004201c0250421040541000010034108140307401403240351442500501490300c0c01050316849256070700300c2030903003e014031011680e50700e034020004400040040c1043d07009840300000d84101c42 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 212157859 1250 212156609 212156611
    0x7090317031012051606050a0201061e03020108040f0b011401080906010e0c0d06050d0809030d0306052b06050c0c07050f310212010e07301e090b0c0a0e010305 70
    0xf05001780c0390740003243d45200c010704006400a8010800114055102d26424450303140100744003441045210001c61121512460900010b8104204c2e000060140020308005036500c940c0964035208669484240c1c100c0d0040c4c015880b40024a4000855458000082c50f01e05072140342c0c8142d0344a40300c0040d00146548640b021300445501d80340d00040903515801c01c03a5005000b03505040d07441d81c046d410541000c102031074120606240002c10702282e01d44001e5034007004d0346840c0031036110030303c42e110305600e080c1408014001401e103410400142900c1010300107402d04601203514036a12281000b9002d83c48048190300401e02c1c0101c81c0300c010f07000c006a805286070300c4034805d00c0d00c1042c8403001641e0040d0101955191110b00411040342940b030380f02d920800a25200300d4040d50040f00390300454640070313041e82140d05074036842c02410660340a00034103020b0b62600d07000381d60045482c0700a010b10f610143ca50081c8580003550400d514421903000340010395a43c254401910010742c02000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 212159109 1250 212157859 212157863
    0x30b0a080a150203070c02030a1104050f010b0702040209040605040c0e03100c05090603070e0904050a1e150e1618061d0a27060b10030c051204020609060307090317031012 75
    0x2241c01400025803000d00069031600c0c01000ac20001c10442d90920065420140c080400c1d10050f1004000e140001001c1e104010350445025940d07100500006014200070740280394050b1911440e0700d1040e800940e51200d200c42a000e94808140c4030507894121020f00745203001245003040804007605e00714009580c030103ea802c02d560100701d020f0105000b05812a801c582603400301c10340e10240315200e0000042882c1c0c51100780c50074181a80d42001040c20383c2e000d0b1800e0b503110341007420440c10504c1000720920104408029203955101002e00d01c40700e0040b65010342e407801402103130700111100a1345400131281841581034403108407000040040000c0080c005010050603002c02405030740460909005440104040e4166800c1003100350450750000d080c545040300780901c450304403080c1c83d14000e02403001e80c01a5100e0000c00c980c0d00c60070f00c1081d84840004200800107802c04540c0c07058078080c6101d4140f402403201a030380240300580b1540003218500d036003009604202c0303101d182c0750380c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 212160359 1250 212159109 212159117
    0x109110303040f180e0102210112030c030309050c060f070c0807050d0b040314070c080c09060918070f06090305061305060a02090607020d0c1401080114090601020715030b0a080a15020307 82
    0x1106032076186c0c01ca81103030500b501038501b00800d14225030500090b19016007080042801206500d5034003600c04444908008c040c56120000079044c001c09005404c080d0602078481035840b0790304015402264003000b1f044078111364100c2c01040e0070000007405019103802070155070a04c51303503032551291071400a20440401c14060807001e00001b01c0d41c06040d4980c46800c0102c0000d003800071241c2082e08002ca10341c000e480c084108204c3e030341c43c0c1c00055004203c900030313441500c000c000d415040008a800074824440051800503540e640103842104a1340142d054420540310008020440b80d40004098000d40c0048041080e400865000b030020540050409203005002c1c3e02080c50541207420940d0b1108021302e0422080802e4041e60300400320900e03100050703605061980005074000207015000354603440000d0b043ea4000c01940015045003d107070750404105c00001000380c24040c02160250406800001356454002034a10040340c0c05080b843ca01d0100d011003030000e41004001800300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 212161609 1250 212160359 212160371
    0xf070302150c0a0303060317120601030e07031b08060c030405031c060302120d020f011415150d0f0c030207031e0e12030316020606100806060f03090109110303040f18 73
    0x121104101041c038481c80f917240420303002d103903040c8001e2209155001c4604400c04000b000400c0400d01800c6034000400d007000500404024a034902c1c00e034a540001340800c3e607018214075000e12140c0120211007007502182d2990340c07004c0ca501302c140402d45000b001d942c0184103101241c01900c2114404031540c07900050306664a8001a507a92149204c0d802d080d085000100700c225814040300e14001e00100081c05500003c07a040b24181100900c4849017549500c0f0000e1a90f682003c1c860071017803204201900c2d542c1401c03d410081c900070f8a030600e0350b07181038004241e01d402030081d191025055241c140c0054400c4208811421104507060100a1801c10321040c82e0340e803500c2e241c41e0150220085840c1c0c40c0600030520554404e040400c159800101007000320703500e44085c45101512881d04281e2030b218003011030154000c42250b642c444502004010103001f0540c01a40c050340907244007080009001e05043d20383c4618000c03c03140c0111004240014894074501408850183c1c0d000149 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 212162859 1250 212161609 212161627
    0x9050906100609180f05010303030f1a1e040f02030408030f15060703120b03100f2a1407020a03120e090403270509070314010801060503061909051e0f0f07030215 71
    0x4450090b001180428bd0b00e002c88800c95829114041c0050445000e10095118420000b00412209002c10000c51034001d503002c2640c81c1ea400044074425200360030340d22070038a4a04041c0d160403c44104c00c80740c00c410009501d9030307860948101c4413040981003515110460314212058600d03602010b051030b82b60310290300c80b91401c2045e01c0c002e2031142d2000810320742001a840c25500c0c603070580041030300e403940e0301d005203040700940c8400c041c1182000c00559408a014000d540074000000e5488149040000140016000c076a4506021690383e4444c50389450204504014256000740006c1e518801548031101c81040800e030040316213070b0103240d00740e42c1c0380010381034401110764200007a16070410703a030403460f01181d40b4050f060040082c0203c9040802107591414010049401e00041800329001804a0361212108640100540705180c00c2c07e04050000200d4101095031031180090102203004003042110100c047c0c84d0161500c80d2540d000c100048000504159640d20b0400141c1c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 212164109 1250 212162859 212162861
    0x111b0c0f0111013b031306210f06030303240e0c04030807081206241c020a17060406050a03081b060703050601020c040506010f08040c0f09050906100609180f 69
    0x2c0801c0d0b038039110943c401050040130081e800e9140300c8000d64000d000244282d21030300030782c4c815038400389441c0100b200c082820281008411040c8007081d031416418035400d441c1508050180e9010791002d201d02c9001e504d100888101c00700740f25800c2240840280001c01184545907005a1020342580c1441d4132038a17000c0c920340c40201d08a540c070500144a600b040d807a03078407090303000d802207a0130309460503103107681703194200c00341c0820303034011000201107a058150601420361402d4246003152611031290300501060420070301c02904188002c0054001e2405001c4c0d142075a40140180e88070f40d18599448010381c009038170024550f0544011581c460340c08004180c8160560364001c200c2c0c1c1440400641043e443e202501d002c0e0342441c04000d451b036009901480408424a0002415034550034a1044525290000200c2204201e0009541000d5800c0940503a400384159880c41c0c0b0303043c1c00288112803030f00c1000007003500d000081041c0001166100d203034542d03507040031401d8a1031300440c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 212165359 1250 212164109 212164151
    0x1c0507090b0d150e010806010b0a0507060204080f061b0a05090d1a0f010603090308010b030703060504020a0c0209060d051c05040f180e0f030412060b04111b0c0f011101 74
    0x600465a90707010b00140b01e40c00c14004000c180418642800754181001b66441d408140100c1c0d0340174100041c0c50151078811411203003680d0300b0002c21900d503501c4140c13480d12550082c00500940c441d11001c2203946d9900014010158881d03105145070425842d0140d510b9048250016840455100e240f00070850740380f500740680d01d404140740e0311031500d20340e06030200c00d060b00401c0405250039503480000c1d030010285419240c3c0a00306070746030303590030b5000c401601440d00600d030424008684145516044003450030280d10882c0c1d06403a40d88d81c10140584141a8003000c0d080340d00054100840181d038000700b5452031164585a803500791501a010304002003580450040039074400c100e510030801f4411006808001805891171460780c550842d540e015601070000c00007500840c003402c001c1254400510130360040c0c0140414058030700340a20640191104481940040d80f084005900109000204000007011850202c41c0a030044500c5a080c2003640c645659850310b440861601d00160 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 212166609 1250 212165359 212165377
    0x11090901032301050705090f22050a1107170912010e0a03110c0108191d061503030301120b04110301090609050d020d050301030f050c0d050c10051c0507090b 69
    0x41600010010003500c450002c003201c0c0b4a9260106000b030090380b00040b914900000c0310315070754a0000c1d20000d40e405030700c10031030002d08031000064001c0c0500d81c0c000c0707807203460034600401203614031408024461094110050a28882072014405500341030003070a404040038041d20750905d004d000d000d084036603001030000d641d4041190b04080591058485048006a0000d007403c0340303a00001030011100070381200307821001c0440a41d6210700a0b0b010807444c600c1040c2501c1c60b185065610781e05d0f00740603035942c211084441d200c0401d901f000008c49040306c0e145e1002142c0c00c6040d407612015404c0181007103914001c210881e090b03550382406544901802280b00054040041c40e00500e060741f540c64803400c0d500482030b864100764001060728110303500840c80040c000f409181c09402d04151a1495902603c904040301c140980045d0704980c0f11000c0d5118040402043d1065909003d405ea8070384c4905120350300e615008001d074100580046035402c00fa88295101c074000b6003642c002c5424 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 212167859 1250 212166609 212166623
    0x118090f0804030203010b040b06070f1b030c030c080105091c02070b0a1d040510060c020303090907090608070201020f031f0308043503160c0b1603021509030901031109090103 77
    0x200740f00f5440d003813146580a11040360108140d01042011404500440c0c0d00039000750b801c222043c080c054407841080003110300031411070747e4603100c1c88c000d80420250301013550340da03081071004600b12105202e80e40c040c134104401045200c00c204e0b00318000890341c918900441c0a541c5001505c100810b0141408180c40d455103600a002c0d8a07041e0522546040018801ea0501e410f00c0241c1801007154030694002c1c4c03a140c1400001380c00800e14522032443c0c426041002503041282c4c0c0e503440400c40040d11400e40e43d0008503117446600324241d00464402500d54201000800d48201c84921802c0040d00d51110500e102643c0b0b45802029030400d0740403001011040280134480080369103070640c004805040102c2c0c0852170314200d070340c900540108101c03036102c902107101070246040700540144031b070350440c0c0d550750040058a4000a2941c0d001c80141c4150074244d2042c4800a07149403158454000450400d04140011030140c4040c00381184c9055040045204980728500c1e400d001e075001b820 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 212169109 1250 212167859 212167867
    0x50703060f0b1212030c1608030403111006150c030314070201021e07050a02010305100b0a0e011d031c0e0904061b02031c0f0b03030a02010b150f030118090f08 70
    0x24450101000038000b01c05030410307110382d5030304c541d680d0950760005000300e20540c6800c08202c46034011500361502821034400403040201b05a030061200c100204140f082ea103090042481c03c905132941c80c0a069280000d0701d0b9420112446070040000e164000c3c6070108620b141500004012202507a41030010703500090894210b500b1019902ea01484000f1014682101a203e09403a20340c1413000a04050701ea90100e04103900b0101d0719005820050441941c500d00c515002e0840081502014003280c002100d413109110b128010038640000500503143d140c18801c0100d080000e003150760000e00c500101c0f0081c0a44461011610440c0300d1480080e0442e45070001e20310802c4840c11001c21940f08003d00e400000002800c0c40340e2075001000411040c0201c81038402078082d50319001d4043c400481c80c0a8070701ea054001548244050b1019034880310302d40002c01203442220305100c034007041040108400018000e40032000c6804210004501c41d2990f01d04420b0450807505485030701001c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 212170359 1250 212169109 212169131
    0x510111b1c0b06030f15061302040f0e040201030b1c240608031209030415030905011103071229090405120403050a0303050a182012010e1203061c050703060f 69
    0xb003840040000d44001b03007104c02120b6a521a00d003030007040c542c09041000170410302245503405507805040350341c42c03407164580c40741814120b1000c02c0710141e0000b81000280300440c1000c0a51603660041c89245140c021110780300c690821203100c0d0b40000d050544c1200030f503400ba4510400c03004e840a0006140d6450103000000340184010744032018540040104011888a5049071680c44545040125000500d420320600504032040c41c12650032000040002e15075000381c0c0c56404026441c420040200180c40d82804091610a250091110501c00205c60300d00003c0c41a4014410000c440aa04d40c18180b4411500550304c00c0b22640c3c01400b003001059010b0040c0360f801654228200501407c1030144c48640d015020064074407207500c050100d121010381d44402c0000d030080d0152082881002000d4003e01e90460b0903100390146040c03070001412643c04030380c000c280007842c00d0050340381002c0c0801082c0d40142c2c1200c10384030311100040004c10500501c0c1c1e454103c1000020150110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 212171609 1250 212170359 212170363
    0x130203010b090f0105090c1e04170601030b0a0e0109151514030d0f0e0916120504020a14061b030d0e0307170f0903070902040510111b1c0b0603 63
    0x41d112a01c01d860314400c2106014000e40c01c0c50450b10f088600c0c44e1991540d64003c00a403254806000820340d41c0001c110244003603200410032503c1e00403140c00d020103e035114544444d402e0000800c0d003006100410b400203e160081c280304551640006400142903840f50b142c19950b6143d103d407282c071102261900304140e00710f0001051610400310b14101c0010000e5219000e036050701061009040c0741101540c0b0400b81ca014400c0007421513080c031b00305a0070304003c5107000e1004c3c90028605050b52414007105004481c010b0341d010740103070f02c0035013041d040c420f00d40040c10050343c001c5828003503c4120f19004403008d4002d00340300051681d0759039a496035400c1d1020280706034003580c01000407000103800c1001506c61602d51000094407420029518542c511950710929411700c544107022a0031006940100215841204c0801d4806000d000541e010040305568541c0754000f211243e042c040340d0351020313091240040500c40745414010380c5000d001507000702600c1400d041d0080003003038101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 212172859 1250 212171609 212171621
    0x160e0604111305150d05040b0402100311040314011e061d090c0108070201060803070606090b0d0206040905070c230d0e031b0a05030109141207020607060c0903060513020301 76
    0x19840480c039020007034405101c005498800da40c01340a00c150301d000c040c428003003a990080300c00c1c04107011a003820b06180c1100e20098505900c190700c040000b281c06406842918850791101c554541482c1c91500c80d107001c1c02c8003400c526903035500d851185900031004040d2045440c01024001071a130700b449010b01c00c0004014003c02d501c2c500100307210300d030400020703103011900003441d02c0d250fa540c461074228050485540a0768040c4404104081080800d40090b8180c40c0c2940080054600c44010440f642c0700441d006034002504203c03d00480a403604219440300060800f100705e0030361640d901145850400074a251444540e000384603507101404440c03506902403400c03019100303e10f000a0307141c4128101c2604807081c1c8030401f0040d03440c1d006800c4010714000b0020001c0c005a410085a480d6507500801410300031444203c50b0390720f68030260384039250090481e50801001e6510f940c010405c01c400f030010711078200000030001d503079030040500c60100e0030f00c1e031303001c1135228070600d425502c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 212174109 1250 212172859 212172881
    0x60b06030f0c0306030f060a0b01110a030806060f0903060109020a0201050a06031e02011b0302030915030702060c0f070c061d090f0a1808041d0112030f030c02160e0604 74
    0x21003041400316408070640410703041165010302590f20744501c00017a03d0450848071a6a050141c1d10400c50644251b6005031201442a02e98080c034010344001c49480b000000300050101d0003240104050b420124050f04058002410070b0b440c2551303074000a0b00d0103209038030180102d9000281c4121040e821301990360000f29406085c8041407c659500c41c4002d110800d50480c0c0754400d504900b5a849559590301580000001185130891400c0082d101d03400b0041c035900607000b00305050a06440074045074030030314056002d02442e48441c07150428550010392118a0301038103010090101d100820803000400054407103040c00c1a10007040300242845006103840303031a0500c1081001c1c00c022207e40d52080228100064210184072490440503140d000541000340c040750115140110a103028600c0030366030b9442d1007580e40d034000342c0300031541c00800034002084507145010442c0207821001004e243c50065481d01080d0039241d501451041c0d11015641c01e00e0800e102207410107125414400f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 212175359 1250 212174109 212174119
    0x607030f05060f0f1302220501020d02060c03070c080c06010e0c04060c060c03480e04110c030a0203030115090608130606050d080304200f09101a07060b 67
    0x442d001e000180c9510380010690b0080215005041d5a59179040852120542e40c50046460b29032005180400c900c80603150b5072151241c410120341c540c00040c0c02d03074106085500400441d6501480c0b00700c00d4001800700d0050150740010b031b00004646a010b05512407600c40100460741c50001b0050380b451015001c00a4010100814008198085184150580c11420108110001c588218000d22034141d52501a081c4281000c900c001a14406d0440c54a000f8030006003c8031074a4984500c80c2048001d00860300000542e061410203802004540b481c48941d1402c04071000c0000382103500c94151000140c20000050180c004110101d00b4606400d00d4400e20381410310340e01030000000139182c0f10300554418444000c205003500030b84081d0901614000504495240c60314140c7c01c141e8085484030054619181801d0044449445003140186a0301d0b490f5111030921000d00409004480400d100c000c001c03d0402c805000041e804960b05d80c213076038840150a02504561009410f54894 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 212176609 1250 212175359 212175361
    0x91305070c06051008011d010c02070e340906090b070c0618030c0e1501080903030a0e0f0313030213051603050604090f03051b01140f060a08010e0607030f05 69
    0x4503a00140341c030342581e0b0007940002c844e118408902120291580306000d07a43c2440725210010320b44400501500c001c190080c041c0700610032050340c55010034015400b82c104800300140f122000690458045e07103407841e50800290324a084810010468a442e1010440101040082550107445103006080e4061490705040c0d440e6103100440c103035407081804108520002050300d010140380c42004543c05107003617807070564501c98810410011a03190241e002d59000030070240d401011094400d030a607001a600c2c41e0380d440c1c0c01c070000700350306072070a00c1601c198541020700c200100010013503c2c1114044000407440c42c410400000181010b00342c44a00349000e0040c00307201c031041908410801c1c1400314403a41c6e100b0100b00204000c100c041c01100d00141124103058221b002009501e402c1c1c1c15141c00b808010b1143c50030707142c40c04504410b0009140005a248200011460300108002c00c080348280c0da41740d074542074816614206000e6040b400503c804103415209060040c18a10340612903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 212177859 1250 212176609 212176621
    0x8070b040305060411030f070801090b0a0e0a030f020c0a080106170d021c050702030a1a07030e0c0907030b030d050306010305071d011202130e01090f1803120f020f091305 75
    0xc0c0d010140005103e0002840f00c0d042640e018003807e9000c24a9104940386107985245060207070900b0003040d82c001c880200030402d4540c56014003800b00310100000d0810700c01030340e0115488c2c0d48a522002c1140a0b80d01205120f5480c4003041c40100304c00c1001080041c01e10304040882640f0314003003900e56010740707000859660041b4040101205190030400444040ba034151100c2c4903100c0005d42c0f500a5120362030400280c0c2d076403151030f95800c514018a40d0340301d0307409604550000c8500c1030076501000c407144c02032034840c80069111a0518021070380990390710210340f91154900d40d80c404280c002c020016607580c0341c4500c6038031056525003201449100b00258109140d80a40c40c0d0400c04a03058140200025170100c0d466481109400b0035642e80e03031024042c40c40310a0140d02d850b24140042041607407510700491000f0350445108428541d0590760540b45940300e8000c1d00d10480d142c1680c90351b24590f07031001d80f10500601c040c0956402070b40701048225030480c800c0c1e00040c0d1814040c009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 212179109 1250 212177859 212177863
    0x50312071a070e12010906050f0601210605030a140c010c0c152a14010905030f0d0b060d02030105090a0606121a370b030604320108070b040305 63
    0x80311480004030240c240ca40d08002c41e5008803070b005a07a04900340c8132080d45003140550050300e8050003010f0801180d110401c4031240910141d070301e103002550400304801d02403a0510049010542c800002925541d2000031a0800003911010781d10100000c08011600009000c80c40c0e104009181c5003201025503600c951b0782a002340a10080c50700d1201024503028054041c01c0c12405188500000c0310f00d00c102c02c0351200101b68000c540d4084c0b0741da8807188900d0705014030742c0c5482e400030186061200c2d00b04c6881c246e412100e40e0030300b9a5101d040003080c80d11004002c001c2c0c1c0e080e04a0140e561360400d8240101c081e00a828921910301d41801040b286910420040071500c446501141d0003a00308100c4001a104081304c507800704c134411064215000c69098480742c00301d020602d5010441d0340c030700d2412502c1c00d44112510340b441040010240d180a9200000c074400205045030710207401d1103610b0a2001c400e00d80788807a20500014007140343c04000c81070050043c410813074601411a643c843d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 212180359 1250 212179109 212179133
    0xa02030402060711062a070503060c0301090b01021501080102090f100e0f181806070c0308151f080709050a05012102092806030902090414011509020405031207 70
    0x213850020901ca03101e40540d16801100e214500300900f610049041c480c074560100b01300f2000803060300c10001d00052600780450308070320031610a14054103507864821084090294100400d0460240280c0c030741c812120038084501078094100010b840301c1940052200f00159601350511441e0801300b0144d80e079070b1100c013440000005490713181c0035000081c08242100c01491105180452000400000840014414950043c1d0604840340c0e91901502524019404000500021185000240c0000003400110030942000d0100c01004d108251881c0c003108018441000080246040c04040350b4041c410703001814040725641205890301c00040d100e031410a400b402e03102ca50710384080540c10f0540c1610300d001405865a4110100d6001d01203806907002c1004000d0b424401c00441c080c3d00c640301341100958003510587c11b644654440c83c0c2a0511450341005039922a0400c0300c0044607000a032004044410b40581ca4a090804040c02d001058002d0200c0d044e05100e035801107142c41c1222 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 212181609 1250 212180359 212180363
    0xa0302060d0b011e0309020907050705030a0302070314030a091b08190c1d01030b0a050c090405060a1e1a0c0304230301020a0e0306070c12050a1e170a020304020607 72
    0x1c01c0311811006948940707a41c2200c84c2c61a803200a5030b505140c050b000b0904d0103100319400d40060340c03542030540d032500640d42c01800030341c8203008080d400b50007a070040121030701034108160316404404100b003803540308071071054889032951010010441080800b01c01c0d42007041c2d16082460820400583d50905100306002d001c40700041d030002c0c014101c1403400508401d0070f144051165190f90305808100a100032502191944006007070300d54140300d914003844080100038603000540f404c00001e440041d181c076078089201c1c000005c220302d08601c2044c4034051404403280ca00d180103845003a5079000d2508502c520000c00c50210034010100445080da21800d0742001c021b00b07042070541d10080600c0f00c1c4d0340c0541c03000800c1d12210b608040446100c1e00100c1c210750640d615118111142038030864010701c0400001d602c1550f46020f20007820203804a4038082842018241e4503007000c0d11040052008a042c04005940c401c0c019800386034030004801082d855418980d0114060784505200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 212182859 1250 212181609 212181611
    0x11a090a0c11010203010303020c01090603020a05030f04020120010c020f1506060307090f091b111218090c0c161202010f0314150a08010603030801030f0206040b270a0302060d 77
    0x1c01094034041c40b02d01e1121a5441d0003103490b5a12454003a41d04d14000c626180420418200000c1c2c0e644a4000c07100c044265503221415034a0320800303181140405441241032100c0d925981c080c940141710194100d0340c00100116001c410303508003905002004001035000e8001d280c0c101c0d001108404a190860f9054442d075590f0394502d0f1088a81c1d002513000700d4191896003a001540c00c02c1d9400c550094014101848041c0d0a8010700380d03103801c213012841100fa04060720303008001c5107440107840358042d842c001c05111040040052003c00040b0741007990342c0710100c0c100f10b661f03e0070040b403a00103c200900e28445403e00604103e140c0c00c01c4c1e002410000c4c0c5c0046c4518903481798004005500880d513003514142840e6540003c7c8004403903c8a01891000c0c0d00002d000b030341401900c003126016100c40402d80d007146c03600c1102e00d408c501e003071760014070410000404030a03c00c0104100c01030026410402101d90411560006403010442e00c140c0400c0d50510241c0e9923817085075140c01260070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 212184109 1250 212182859 212182871
    0x6060e01260a0b1206060a0b040608070c02031c05120c0301030f0b060303071205030a050907060c06020f07021005130b04140906030109050726010c05220905100503011a090a 76
    0x240b10405055607203a003680140d0940200076100d04c0014000d40511003c03100401c103030fa10380c025804507000da441807200003158a000f0403240c50040c4410f44452b80050300352041020030101246001000b00d080c1130000d8400115190701e80c1e8460a19030b0010800240c1d949113501d540c460f43d0703508004400142540f00c40401040080c1e80420460300c4266000c0612202e1101043d405800da41084610a4445081c000042c9102c1e0300861040252030260f1100c49201105132508002900009981200d280c0c0803c442000b41e9601c80034a4401e103d140d984560340d4003201d24620305032040d40d001c0426010240010700c0082c0b0141c00180e4441420780c4c5481c4941d4602c13002901502d118200500180103030800030500d03e044140308205e07400080082a810340600d9580350803a0000e800c3c41d000180c0500c151021b059000e0089200400c45600400d0f1040d04d03284250200c0ba003d6410841a203c008030400c0756013401e01607101c141020224251070140460b0215980c5603005292036004c85c0d40d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 212185359 1250 212184109 212184121
    0x20705010f0314010f090c020c1c170c240408070b0c070f050d09081504030f050f03270109021305100e0f041713141c03020106060e0126 60
    0x10f4040003000481c509280c0f515696145a80541c0c48507010301380111f800d110140c10b00c9400044d02103456500549100300c050780d800c030503518110441600307d0f0344010b10255440207002e050090f0182e881c24201500c2020403000c0490104203045001483c060800d80c100004074080801313a07243d1a41000c9982496500e40318400c109100f0384e080100f050407041000000c4c000300140380c0741c0d003030103c2d200e0b1131145480b000e685590321010510200d00502d034600050020b071080ca000c1d40c0200746814054140060b102d0186055042180d100481b0141c1074070301c0340b11003c4000b82c602d0924501d0000c0010300a141c021540030303016640d482c03074540c0c2c4400c0803941544e11000254003c00244554000c00d046c07801c251050000c041d10280c5183c1c907402c00803c001c0c107000d0120b40e10000d07441200c01d049858248581c140d19240002c10754443c40083d01d810b0f1001c202c454810005100b5030001590a0801c1000741c080512903906034100180244500f001c2502000616424140b62803850071565901c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 212186609 1250 212185359 212185361
    0xe070806070504050423040c03060609090c05042403080901080a02040e0711160605030f07031116060b06070506071404060e011b0807050d0906080420180915010801060501020705010f03 81
    0x8070b4186c0381122101001c10045c0a5148611400d0703a01c9500d041c4409035583c000c003000d840e503140c8003030701d102103c4c0810811440c08d0703808903040100300aa5841c590505043c20208401103520a82d221480060002119a4403d402c9640400040811810300c2d04003425401d00c900010503150074801031050051241d4410070601b24102e101001e4103000310307200c12004000341c00a650110201024501246281d07000f4000c030799000d01d00d0b00d90b140c1000e42203942110605594030054a10740d907540b40c1d4080c0e130385490780142003250150000b005681002c080052580408007125401d4100903c024000542c0c00001d0002d650400d20300080c8094502007409050200540010940c0130001007034010803c1c003145140929245440750070310341d036459a0540314007600300d40041602102041c400000d42c810100a000c544000c2c2c003003012005c1140b420385840e2415103941c14542d21021180051101100d2150701422078030300280105850a80007039510101c40c0038940c140000440394040840c46 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 212187859 1250 212186609 212186651
    0x1a070203070e070c2001020c0904081204030e030613080409021315030e070e0f01030b0c0d050709091a030601030305031b0a03020702010e0f030a030e1309060e0708060705040504 78
    0x81e4010900c3c182000040c110700c102c04030803905c0050310000c0c03211100311500400c1c242c42043c1c000d001d41d10501800c200d4036800042040310561000d00a828444a6038460385218a20944400003104414000c061a2060080040380781c400480b200d400001d14140a583c205c2d100b0100158549889110b040506030302c0b60010006e4089008100903425855003244911040303901c1030741d0705c040c2c83e034180718812030307049481808107460400100000703064501a240c0c04201c840025041c41c1100c0880c2007a1081900c40d6030001d10901c109106200c0301f031142c1501c400407031900c0091103001d000402c1d01c7e4401440040d050100100000b400c810150a91118100c4202003044e5294540c07030001e030080d0402c0380c01341d0014600d001c540f041410a00b622072009440100100901003066504682c05410b480500d41c0021142d01642941034641c040c815a9500c12180440c00c0400c050074207242c015654460b440703e078801d200381305000d134003e011038060f0b80c81a100403a00084003490382141c01a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 212189109 1250 212187859 212187869
    0x6090e160f09081b18010b16030e090a0515030d0206060f0f0303030703020301080d031812120603052a090f10030209010e0702060105060903070b07060e0102030103030914010503011a07020307 84
    0x744e808500c050444081150310080c80441c0c030020310b440302c4040c60b01025000d010b0b40d403045030100b001100000561001441b02407080c641144c4840c1144042003545da1b06503081c0c00c009481d00b052100f1145603071400800018150002c0c80b10030030070280250b98610241049028003600c4100b040280c0303541101c0b00400c0405001c40b80d82c0e0505200090080d4000d22a1b0030060281c4124210a548603008291202c80d0254025001d8036564850442c005030b0850003005002800c0041e401107107050060344020740c050304c0605071410440912a990314005e00d90184600349091070441c0c01d507104880344d600035203406040d01c0c2c1d070740d1074415079800941260030195225141a000140c07184001c1001e9206000d503034240da010b40d90710028884980901c01146c2d80c96000814107000e01d070030410241402501620007c15050300181045007240e00a030425000a90b000b141400b03254610a814250360000307190040c0f1311b6140496003400a000c2c0b01005041400002d0810195a010080ea2010301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 212190359 1250 212189109 212189113
    0x10f030f060914190b2d030106090b090c040b030103150902040504060203091603030518040906060801090209070518040c0e040c031a0108041509140a0305030106090e160f0908 77
    0x1400f4041401541101102e8a9504041000d041640f0018600649120540150114418034210551a002520342807160310501c1200085802d10360b4090003424000c040034030000442603003001c01e02100c1000100140f031603200803c0100076460b681c0080b00e04681d04400c89903038131604070b4190f80280a61071000f81d405800d000a000501929500440c041c0000d43c040380c041c180c0024451003010003030321000d808030b101802143c41011554180d0520004014070000301019580e4980c0c089840baa000000c46070354805401c411030600c0c840f0990016954103000341000c202032a544a05600d0a0038240170329110100651260702410303070114000801003051062510310a0010b0041c01c80780c0c420184051070a01d00e043d20f50155220304e0185070481d6900350085000e41c0c2c0c1d440900000b100454542c548840d910524080520891410600c65034807070799203514010700142024080e42141480b0040001840b50903114007401c8401a03489041507070301600944001d640c8003000c1d5200b08554 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 212191609 1250 212190359 212190371
    0x3040306060b19020606130b0102072c010803030118091e060e0c060906071b03020a03030206100b0a0f0e0105270306070c020a06050d110a030920010f030f0609 70
    0x4501a4005006400e82441d0f211a81c0c5030b696500303d9a4407029a9915081000400702051400c920b40003005114018012030300041e5a031402e92090400c1c040201c850000844032203e03600030b610700346500410400c00103500b19410101a0400030060b44241c4907411303503402a01e0204842e1680b2401050241300d85c03503200b8503080c28040083c1c81003000b2040c0f58010820700811a182110540d5549400503007118148285581c90340d045074960b1059140002c48001c4c0007005a540e40c0f80742015506c0380e8081c0400e800c0c0401080600602d5400400c0c1143c414020403c8142d841407410b0700300d210038504900162900c0c0d0058030706204040c00c4800766541d1103c000e1a0511550705d86c0b600000c20741c00c68410307568111044030b1034035203000000e60088440104008040c0b0800140c45010004000018105d028001004541e80101d4104000c6515881207005100c680c000c4480380c00c0c5401203012201c222040020b208104114203807092542e030703080824400500d82d0000002d84034460003000300c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 212192859 1250 212191609 212191619
    0x50d080705150705090d0203031b0312090c06270402041211040207081b01180c06020d02060f0109020d0e030327160b030403110a210e1c03020304030606 67
    0x2240e20032203050751984910700e110b01d044410042e105225400d595140c0341401c002e5020846020b40703c0e81c2c1680d0522061256503c058041d459200b02c08042000030f65592840802c661030710704006021007c0794101400c0c0101507200c5404403856909208078560f403112000c1c40200700d0340c0c000f13201c03179400620201c1d002c506511021001d002150007400e40c00500c848a03010070040c2e200740d07c4001c0c6140d60134410b442c07880060300c0f4041003107401d20740049083c400c90a2064504421008260b900c20906041040100d4040c04844513030401031001e000c00c0d103451650504064010301c0303000012a40082c811820155076404074038082011003d8943c0d9041c050081c0d1095a620588a10041c1e0046444c2a2000000841c079440700940c060418002d460305010203182e0300000d00075006e00c803842c02d20b418440e405002800c2d07901d101c3c60388090800c038840c048074070140c1056041014489443c0603000543d40304520800c0f010040003000d40041a40d203030072400c6004550000344218200140411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 212194109 1250 212192859 212192873
    0x809011803120e011a0f03030d11070308010603090c03110a05060705011406060406020703021e06210c0c070506030406150801200301120b1b0c1b090601020d030213050d 74
    0x7101444541d4203110386540020054229560104465a00440ea071500da40c42d040441d80c06c07140c41340050960f800c2101021010b029501c642203040f4914800080003000c01d030300310310001e0160503186020444020340307590300c41300e43d0414040940b10601c600c0b8000d00540e611103408002d428041c240c2780d00d428903031a10740e01030000c400b1050b503200c0344540065514105002a113003103036501d42c010300c02c251441d001d00900700302904544a8100d0a94000e031241e40b03c501c0208000c1c64160f51a4140035070f00301d03480c01c407400d010b00316503640b20040040d46450280051040140c40040340da543d601e8a86150580003004040800e200d2002c4410b0002660281903001507060000d070101e9680b84169803000d819140f00901410010090b803071100c401040030080080c0c2e010600c804520075400700c04071402000e030058080040c0d80c0d442942482052036864000605c801020b5980c24420b06013000040d40b10707403034a141e800c04c1603404190000f542200c640d2140040c00007401c108080703806030410366 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 212195359 1250 212194109 212194127
    0xb040605031b0301060e0601080403081005150c0c060313061a0d0c06080f040b01060e0411030a02071104090b04080a1e122004120f021c0b070306150809011803 70
    0x500c00d5203451710000f6040400c2c01c0203445600160744005540e40d89030307030641c0c400c00054a02c00074a4200307503012031180c03a080165609400d1480b90b6980307c8426075012440c000e5403c1401d402524144180300c00840e0603200420813a40c010004900c66904000045100f0403110241c1c2d4040b002c084803109001da5502400c0a6500c183e842e059981d84541129480c01000e8078002c0c00d18010070700403c00309209480c110401d071700091021800b002042c4034056240c01c15030b069018607500060314810060b1001c004111200c0584007030142c211a0303118690502c80c024005021000001034030406148a4106046501108020380042c1c011041000344503103030307201d0883c0c000e03854401068079800010003801c90380c001c810845450141009480d4150b05600841119048101e000b014016601c4100000901403021a07140c160710240c180003019000142041d42030615005060103140b520340c1c4801c4d0b0401450800103942d49450701d55a00528408950055240180d01c81ca07080690251402c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 212196609 1250 212195359 212195413
    0x609020301031e08040e18010e0c01110a0b040303090f0b012c0402090106120608010f0e0c1203040303200303090c030c011407021212071101300b04060503 68
    0xa804840c000c2c0c502c03a581d030201c08081e01d01340f800d120030012200b000203015448503004001c40030000c210315815083d6816003641c000a50000c420f0741046582c080081d000100c06107000300f200122a486035245504060000350405450701d491200703219601d984106030340d9004030921465030355501d1a00c6d80d4031a461800a04040091802c44050400030955011301e4006080c10301c640d180075003d40b42c41081201e01c0c5e003619159040000c1e803040c02c0c441c0c81d5202090f22800b240d00801d001590b41031008004e002449041000000d0320021000001d440959034941450320102030b800340e034111a06004481d4940710f21000082101d107400128238071510740307015011604000415030043d120904160f4610103900414400325002d0b28062480c20b041d0381c00003041d200c8803051030380c050f40c455116440c15541100c8983d020750255034000e0401204004e050724100c000d0b038944074491118080d004242c8003060702c0303a285012940d02d40c4d01c501c009000041c2160940c241c0b04650004088500d010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 212197859 1250 212196609 212196623
    0x304031a1f180911040e0708060901110a0e032803080603010612020603150904050a05060114061603032903060f0717100302060d020304060c0201112b060902030103 72
    0x180c016460880061001030740c0e600d44150382c1c1000000300c40401440a55800d54282801d010b2140103a00c1d140f00300c400c3c01ca9140040d051550a003115240382c810050b112544076890b08400207147d00600041c0c801e40156490f0010800803140000303880c01480e0300301d41c910107001c0174402524200382c3c0c0c050341c01d0500c280c644001c036a07280001c2508982c59480b500c0c5c1c8503403ca072280310042c50014021980b0108422101b038002c044007001c62003540302224212919804a261b14051280801c20607004281a40d041c11201c0480404202d0700c1c0111082e005e0506a9421800d04150003600401e1144030700103091808070a203001c05540d48003141a09500a00a0b41c011926a010b2990014821070f19921054042c010f00e1507000d1a04000800101c1c04900705e560200050b41e40400504424007411000f47c0c882c1064100f8100300c591100101082d6850b10140c40b101082c1c180944440607103100780c804040c0180d00c041010082140d801c1e11000d40b6210000c58481c055078084c5041e05c0c0940c82c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 212199109 1250 212197859 212197891
    0x803041401021b011409061303050a14010c0f050a030e10051905091207020a0b031e071701060f12021c0e0a031e0c051506100f090b0c0304031a 63
    0x1d1003154900d0300d85550f40c0051900103503480100150341c0108034440024100500d00031069000707500c0ba0314035810448a0b504150024018440351484198240000100812103540700b280c010b8500b400004804040c0100410800740c0c086c020303885241030841e220160f40000000d9410103000f04000c49103e10081e80401044400011501c138480c49401004010644a42c0c00e480403600343c0c02442c0100d902c4442400c000c9824641d2002460060303403201e03400c0e0508840c5000208903940020900302c1000040c0840c04110a00904803504607113403410490000d08400004461000d00c406850381d00d03500001d03224030b4105c070161018070031044521080159001034441140c540c3e64406c4050001100300002a5040e6000b1003641c44083c41c90030700c01016440c540d40d1030f0500c210000d20f41580c074100d004100c42810301ca8201d15a0a4007443e1510200c610008080c19802043c022181c4030b020215103c1c480160030012140615048000500f0b0020900801600c5041c12113680130f04540c3d200c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 212200359 1250 212199109 212199133
    0x140430121206210618060c140a080f07020115060e030d050a1d030c0405040605060406050103050c0a110a080412050d0504050a0504090f08130509060603100302090c04080304140102 79
    0x1100c2c1500b603071040088190b03081d60f0541a18641c4072107000c16501595105070400394030031034038103403428144515030100e0b120820300e4000e8094110321240d010fa8030130800200c2d0130143e0154a099000d03815400c0c10310513031203240003240100b412440358481400401e002042d041c0c1c010060980701e1070100d040b140440341c03c441c115803500490314028041841944045e0310300c018180d011868078401380c11100500001c0b400942515001d84082c0c0729541d40e9070a104d4241482e00a10029150a003028031140c1003100012000d4884d1303580c00801c0060402d5503000000d028403075084034541210140d07031501d495480c2a403040c000000210fa5920962828250f5140500c09550072664001c04094011f031421080c44090a00041d00321007106142c0c0e0311320001080a000f400c0c944642d89000b0f06c0f280d040c1070070301c8030010f030207446d09108610901c1041301d81160000203000340d0307074140c51142860b01d900503808454020b90304a03080900020134080340d45109882c0c201c10305c0b5426800c56200316414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 212201609 1250 212200359 212200361
    0xf0606210e0d0f0c05010f0218030106080c04092f0306010915060521010602010204060215040f02060a0203120a02070606120c03030e06040503070305060603010c1404301212 76
    0x141681081604110080e580841c02005095803241d1a030030503010108045e910a4215400208802c000c56404035038103623034541540e154005114154000c000850034008000e9542c0e0311845202d10858494000104120101c40c0030540c081a01100c02d401900b95110316580322410300c40746010340701d4079000040c4c8524500a16002c1c403038074400c0340078580c00d0060132035186c0d2008900070103002001050100056851401c5402007800d54001a143c0f42004c400a0408044030781c0d1503486400740081c440452040d510003002154100ca42e030b5550480b21400340e0446c000e041c403281d100ca40c11010495200070640081050764494241046040e40341c07030f180d02034034a1580c00504207400300081800080e0282c00764001c00b550040006042c90750314030029150042c42c0d00129615004a0240201400c0900035406032101a0074207001008500503441c246000da442100c00c85480f90031110703d210f01c04030407095408151615061500307000d0408030412401d41480c1d00004100d800718824082c41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 212202859 1250 212201609 212201621
    0x106080c030f060d020105190f0f050a0203030114040e031803060a1e0f0b030a080c010b060405130b0f1804140d0e1e03030309061b0a0e060304060f060621 68
    0x2c02c440800780c1c07102810b1002c400a441000c0f41400800c02c08108085003031211544850416a26070717102e089080c0740180b0340301344020120240310342401f201c00010b8022007a40d054507a01c0c0c1c10015800c11410005024084480100003a070000140c2c40f00c9009403501c010455002c16001c45a0945a0034941c0c401c8a030403900889030815000003c01c44900d042d040000140111000403600c8400c0c9030009082500802c002c0300c0d0300d880043c1d15201c00c0c00038040c0c0c1051210850b0303241e051070314042c0400d02c0b41521205e050300782692560300a41e556a1001085c0780d032107018210790036280e0031610b210303600501900c0c256240d42100842c587d50007000924000c004041d40c0d07422803640c0104045c8807003d0f0403c9040008042800321030322558600304040d5100301e800c0c200800315814484681c803800c020762184d15418440c03c200072040160445c804503100c2c54107440c0d0fa0b070707260b6030750600da0300400c05158401c81260901d440050055400074261f05151184483d00c00100b400a00300011109 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 212204109 1250 212202859 212202871
    0x8030c1e120c03060a21031d010207050907030e0613030e0406180f0e0105040b040b010b07031403130f26030103020d0f0f1a01150203210709030510050106080c03 71
    0x201e40340c001405510107401075904031034040d0031031460700d803503800d40c83c803007080c00c3c6001511103034280d101014503911008004101044012000d112490b03000002d40303800c0e8900800b4060f03815030010030b26a520a40c4620f102c0ba60007000c0d20084e050428140d00d109880c201c055001400c100c4182419162910030701d01107030f06d16041481e0020010700410701808860b1030194032a581c031117915045007001c0c003506101d248603105c80403180c41c0c1880c040e0100003040e0801164282c0034406000080d4000f08585025030080b030321356480780c0c0c512000810502c0d0a5030010008201c01e01c0480c1040090101010303020149400804c0d2000311960303045842c00309100180d072100290b4034200100d01280f46c40a01d450043c2c541c281d90300e80d0703515440d01c00c58054011090741c1c00600010801009005948503032a41e182c4040c501c1c101d41c154000c2681c1101c0239203c1e50b0003007440c0109241034024444400210307809010b4814050207682c03a40d000b080709101c1c2c40c1c0451a030100245040b0f825800f01c030301c142 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 212205359 1250 212204109 212204137
    0x1020f0d0f032307030c02010207170d050f0103150203062b030f0c0206090409020d020a0305070e06120a0209091e1e0d1205150a0806091b011b0c0308030c1e 69
    0x1075950700c4d086010349210014141595403c209800200d4500c8902014041c119485142d03145001b0742400b007160001007448203041d90200040c40022a00060050700844400340581c59841d0305d000500f044d0421003407810000004844103032080c06242510100a00076191a9102d043c0c20509440c04002c51000950140d0304100302e0703499241650003400c400303001600103104000030381e0100389180b4181d0415101a03111a1041003408450307001c0c0d942c17100c4150340311900c2c0c0300b103540465540c4400c607900a118540d03010005108007000c11a000312050883e440d1030351080001c1075180c81c0c0d00c0b5011580c4441001c0e14502941d03080004001d0091407481d0f8070300e100c802e40700180070002e0102503c42c012f0183c6221482075103070f03034100c1d41c074020b0a002da01800b00c41c10041040b501e005406010701c910003a59414140590ba08518000e0b0042c00380040421805424036010145900c1034100a11040012041c00104008000a03041604c2c1070000084087d82072040070081d8010800810042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 212206609 1250 212205359 212205361
    0x10e0d0312060506030702070314013804110d06050307060f1407050a030e13110d0906020702030102030f071701080309121006061817100b01020f0d0f0323 68
    0x20310851110104440d0070200090040d100d02c0014101d40c070a0303581c07500681c848417043c01445100c154007140c0714138001c000c005014803044411400d20f080c540f042500f500340300e0a6010f240e49070000c2d01c58440010b004201c4103110451000302ea400800d504004180b520318045010f00b00050007105890044d00e8910000c07107040b1003202d1201c8412048401c0c5c440070f0002e0000110200102c0d50003611076120300d10410604c0341401354040c4030039241600f090910020356050440f0340f08646028540c150042003800c20350402101070320422100030b4040d84000204a20084540035223070042c00d06950303007c1402d401d290060003108084c0541e5120760030800442c28945000c00a065034101503409640c083c14000c840701d8212000c903403040c13000c40c20340d5203c1076144095a0b8030002411854081c0c540c2100300c6121143da40c10400544803442e945c54070b2036806a07000700042903500c0382e4081165145908a00014100c2414100c0100030038109000240704011031501c41c0c1c01100e1004a200203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 212207859 1250 212206609 212206613
    0x2150c1006050d0b1b0703170708060117070c0f08030f0c1201090b0a0306020a02060106090b0c06010927030f020607050a02061302060408011a0f06122a03090607030605010e0d 77
    0xb03080c070702502010340b1140c015030f0309082884880181c40c1b080c1c0a61a42001440e4120b04c03103c40950082040d400c218000080000c61303a0088184064003040b42c82560455036002000d030350b006080301010b041a02e071401750398104070784000152320078002c0c40100446a00c4079102c0c0c1280707003d864088440d1045a80040c040307111035600c0415000002002c041656569031226022a400310611100503048100103000b030a030052000401403010861003860b0410700040c2e140c817000180a41028240c0780c8800750405225007090001840102440d00134088440c54040e15201c00b018201001d80200030000d2045800361069600312500c9401602c01c61307a801c41880000000710310100e0b8020b5040c0804104520244241100c1c203000484948089a005080040712a9400242d40c4100e00802c500d2407220400b03545983c00202c0310482c1402d410f41d054120b02d07900700e40040114115404010814400310004070a40182003c2c1c50400019444800441c1c0c02003007001003c2c0c015980c0070714000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 212209109 1250 212207859 212207873
    0xa030f02030102070b16181203030b0402090414010305010b04020316050a110709091401060f230d06050103030e180601050a020f010e030309060f07080103030e03010902150c1006050d 80
    0x921544000d00051802d1050707a60452100c41c140c4140282e074804104450740305401240000b15940c10602043c160391604045c4e1021240e441d00040415803241d600c030303410351150f40640c0c40081c1c00802c00e000b104220b500d49400c8800900c420b49541d0300b400f0100b40181094422a03000e400030300c0d10145081d0140c40144c40030b034408540c0e4020400401801c8115600501c600c101078284542c0c003045030107007818003041c1044111481d00c03813a40340040401400320390007200000c840700c40e00f000011418848041103d0192003100d950010001c900c50000c000c00b65003c81d068903c81d0b11503400f8405a071003800f0f03c920071403110318000007140d00880c2c09580201e020303204900081c411940781d040e4800883e4203448596250a20750f030701c084203100346090280069680011109086503051030200c4005100c0030040c400034042c0200c0541182140c1ca0a4111011b21074025045408207d03801560518560003070181c1000d45c007a0780080741e140c0c04071340a400104c403002440c0d03105040140e11651 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 212210359 1250 212209109 212209133
    0x1608040512180a0816062105040302070909050303070807031a0105030c0c03040902191e0806121b03010605030307051e150106050304030801060801050310090302120c0a11010903020a03 81
    0xd0b40b000308801d6280c0541d20356001c034001d0a41034010b03080d00c1c0c4a0444400c180c06194001c0028041081e0403c1f420440581d09601c102040c401e000c902510349042c00e90034000641c00ca074603100e041031904828030030000004c501680c0c590303403020f207187d031015030440480345040407030040700e10712154400d141d6100300301468000d112000c1103407529460b00f010519640c040d900c100ca10640100748880c00448010741440034005600304400000ca500480451000d5000300a07020f200c1640b0124006445005c4081c0311910302c00c007280c0d44070100c0407180b00310000c0f20038528401c0d030038800007064605000c030550361001e42c04001800540d803112486207041408a48001131031180c0380669060302ea0548002c0e00074000c41e151241da90509040c0205103001c143c005006102c41c000040180c2c0d200050501c00c500d003195030000e65002d10b03140403030a1503400c2038503045150340032610781141c0002003940300410307200781e10345080320003201c0040d0313032180b0140720280d8484680d100800c045100e580181d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 212211609 1250 212210359 212210377
    0x20d0c03230408010e06100b04050303070602030c0d0e01051b0426011b05070615030c0b03060d0203060115090906140d05010b0306151002120913090c0e1608040512 72
    0x52802d003030b01c4243d020b085036041c1009244e181d1043c070a0000724545103c0390f02c0a020700c42c0940d132a00e03040c10042a40c074401e4a038000e100503030010020780d03000c07101000ea0f1409018603105001c0410f8921403980031307240c20340e45000c032030070000304c0703115100000d8003140c08a41c000821480360100c40600605032519602034103646540714800c500181e82c1301d1803107200b4801d4644482c0d0710342c030050170038400b12010844d88201d001c070b03410018004101420003070021910403122150340c9544000100c0e0361905000c1d00290544241e000200e0036000c110071000c101d5105036076046c10341d81e4601ea5002554924447c02d080030103464244441c43c1844a03640a10901450010486e03038888000310b480c2c91012603d038046200c030700e000c010140c0b81510000380302200c0e62006016901c509507815002c0e2051442e032910550700203ca0701e40307803642d98108040f400e8000d2981640c099035100f403420700a2044812820300244000f5404600b400b40c003000f801150004014800b00d610005111440e034010058 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 212212859 1250 212211609 212211677
    0x20c0d0201021e01050f091908160b0405010e0f0106031110110304150e0409030f08090c0306010b0d0506030f0a02091b16050f010209132f0901020d0c03 67
    0x100f501081d40b11a006103039002100002036149007000004030710403400741580e951a00110b0f500c0601c41c00407141c0b10b443d140c000c01d480365181c40c144042c5031903411410005044102d042c08202c28020103600880032400c694041d980034034003c004440c203c840c81e0000515060f0b141d44c2c1002036007040700c0c259004e48028200030040d84000d003241c41c0346402c250b02200104402c02c0d808410940e1010094a0320541501d0500200e452030342c01812080c01c0b03044030303c2082031035400580301c1c010411244842d8180a4180e420b2541c50304c0d00344103154803014001141d0390810011524904000410351200c100d13a4001d080704450a80c03c0107036122000c1d09000b190b02100d180340f84124190402008600222407100102175954a00b181c03e26039a00d02044032644180070303110103500c68210442002c4583d842c000b90004c102101006d03a148607850b41c2131120061034001c800c946000005000711030090b02102c8001c48070390012070302d28070304400040010f2001383c189a03080140b020941000308641d02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 212214109 1250 212212859 212212873
    0xc030d021b15070e01030204180902221d0a03080406110910111006080703020f0d0503070c1a040605070b0417030702011505030a0203071a0405041a040e0d020c0d020102 74
    0x1401e46000e00044040108101d1881804405a00946182d00a01c42030030103604141c070b81458900d01c03021000da20072810751240441400c5643e0035200841c0c4025118040140d80581c10a5038010440e805076034003000702c2c1d10004040460000750002e2001ea00d662142c0c82035980c0d95500c00502100a6950207082050010340a9542e41c0e08220307100c1c410940e990704112240f0321406213800b010300500d001c02c500e820018040740340301003000340540ba0160f45200040058001050f80302d01603120251540c01b0101d2034200f040b013104490400c0301c02c44080404011003449003503049100d544150000b0402c200001c0001541401410f42c0c041c0c00340006074100445107404072120341c421121b920040c0d42d41d030300c0380c0c4405620169a801605007a401000300310102d90100b0750f5402580a003a14079040c800700540d800c80468100c80c041c0102400900c28050200d280003980714040241034429400d18564107041d080c006108001c11016074010800c41400e0821310520458024041c1d04502440c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 212215359 1250 212214109 212214157
    0x20a0324091a130314090604091406100f02030706050402032d10060b07080c1c05070311010507080a0b040608030309060105030715050307030c03020706150f0501050c030d02 76
    0xc403503021400d000e030784007103440b140c00d00031010440d0703000b4120000c0d03604608504012907032003c240d02480b80f0f110780041c1e82d40600030002e130300c90286610050740300d030410b00c059450002a000702c03030013114160703001304100c211031100390b462000c0d1400d00d0005a0052000e0808141c00d0f0300120307081400681615200140302003024010500e500a048000c3e030100d89104141c0d400700140051603024207410400541400b555401c0741c0700b0404040e108450100c1c1c0c403803000c0d00a00083d400c2d0a5100800140502018800b40032900f00030004d801080186070301003e04003060007924410700b05650b480301c0980d1400c54041c01032604020403900306a071960046010342040000794051105a0001d000a40c5020101b5140c130034260001d2074101100031507280c030503400800b82da4000d5540d00340810318180e0784104500900905401034880e5003455170b101c00800d0203003c1300013655503200d00c0700c003030139269001520b681c4150040c9071134650081000600500705940902101c2c40c182400b41c42c010548 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 212216609 1250 212215359 212215361
    0xc0720150a2c01090b0d140708091b1c030e2701050607170c0a21030605040e0705040b0a0e180c100e191a040e090307020a0324 56
    0x120101c00494180d24492901c050750140502e5040c0b25548065201d1401d5030000307000d1410380c800d01e5071440e00800d00d0091140b55070081c0c0c40382c8020003121021480d19541c010041c2c0015507040312540242100c110380341c46031000c5903c10000c040c104800c1c41d504141035226210714941c0075400c1151000c1d040703e80341d0f14440c1c2e0035401e100f00190090307502c2604981859524042e44828440e0604001e0200021642c02588040003c0300300c000303803a00054030000b030400311140d500500c04000e00c4440c103074150000349800c50004907a82c0030402e440c1c41d0f40c01d00c0115000600511440c0d1b0005c48108518a01034001d06c0c1014030241071110002e40d034800c0c1d01040503068071044c21584603518001900e010070000c7c410303000702c1203945c3c500c091000c40300034100320700b006805406086c6159108440c01140301c003440042402d2100307400c0010140c680482c0c0f0790840c3c0511241c69002001055048500005943c0b60070b80040000024130f1869644c05000e601d00c0303060708110a62030003145070318851 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 212217859 1250 212216609 212216617
    0x3061f0c0b10080709052a0705101d0106050307180b0402030a06060f020705011e021f02030604150e0c03131401020d0501061e050c0a08030406090302060c072015 71
    0x11040c0b0860855003020510340c1040c4183d0041055685041c0030420a030b9200b0710000c0c580c0c00103c981031140c40c807840d10407103175200d400c40282451240d0f030503249100340c82e41e01101c685040c0c0690300601502c000011800d807045031240d241e155004903824041090300d0043d021402d10000000550325000e580407400b0398000701c4d42c80041941d612000c200b62030704017020319000099440a040b0050805002074101c901e00003504000080c150300181e201402000000200c07030f002002c5410f0210ae0f144681d0207544110fa0060080d0f042480c22085401d20703c0208058850b41c0d414407250b0390b60505c241016800007000050190116404040450f50700d0700300020407650b80780096940d4080c55507900c252101a4020381c00c01501030301c0100d05403000b021118415400d4034050b03a032011a050a2464804510005041c0042c000b05002c10800c443d03000c0322519219809a5070b0079607c07000341da42603000c1c200018100b03180141c5480c2219075032859043c01104000c040d002000440380c01a461604 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 212219109 1250 212217859 212217871
    0x11030d14010504060f0602030406200105040f02120a0803041b0509010902040f05090402060a120f0f05011505070206040e1f0b0a09090b01090902030a1b0507150203061f0c0b 76
    0x44800042c0b1039400c2500620300500340007950700c0607491030040025528811032040c00b0411048400844c010006107074001c00490b0028002d00c03141c1000d00b040b5000c144040c904a2041c02203040300804207034007107800ea02a640246000b4216030300ca4442215200eaa10141e26903405140d1020549a0719209010b001c1d119100c80103803150b0034071842c0300f0502c004c1e400041c41040c401c0c3c200401070340e0f002c049a01c4500e891605240300014081c031074014101d240d003c0c190b02818201d0303551991070107031702080c12075407100d134203140d2158041c1d000e448612400a02a401c2801003201b0f0055050b00840160000c0c28075246450151104132000081e020f160409110841d00268200e40c0039031284103a400f41090b103208200081800c2c001801c400c10f81c0c810031410315004000144184202c1d40020000c4840d040c061310044128a1f004004d40d0004100301e4178014000301c00c50092107988240d0784140c401804482070600c0c0811548185802640c50104101c48012184001000402e80c14003603a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 212220359 1250 212219109 212219141
    0x509030c120f0105091b061c11070506010b0304030c0b09100f060501170907150c050f01090b0a060b030411060c0109050c0112050c030a020f0712020c0f030d0f11030d 73
    0x420b4280c125007510005851508294041c448060502d802c1006000c0380b000704582030f50740c991410850b080411a100022118903181106030445120520005c006075480750050b10701503031302c0d0b461200181c041994050001800c159a4000003060a1042c0d40c1015240c012907241c54641414481a1208415503406c600d840714010061035070054005c025030b01d141500000036141c4241c00340d60b114464419a0661003105906031800c1c0e0285d0300c211301854010060720130700c05007040214080c1c6800001122010740050004901c000305100d030300c05a4200c5803950703265464940b15441c00402181d01598810020011041038041c01d2142d041e61911600140c0a40707030101e0300140c00d1a03030310501948014200030410440c208034008413a07200341d10040c0143c8400851100340018003d013800103000b14615052005851340002d00f50484020403140101c4212810007415202c1c0d440703c0786040460801e40b4001046400745810f004006c400004981c24401c440f44028162100804044161 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 212221609 1250 212220359 212220373
    0x50112020a080c0306061c020d050601060f080c19050f07150c022b090807060503010819020907030b01230711030304032003070b0307020c100f050a0509030c12 70
    0x14101158804002d00c0801c01900c1e0310740c00c40d40800e8a07203000604180c894000d08a0b41c5039101810250540341c660040c0540c1c01c10a003038075003141e583c0002e010743c2e400310f010041010300a900c2822403074400c640112205040003480d50010120200214222003400418004180c80c00c4145015200150184224003240d10440c1542e20441c3c41103030411007107400c060142c091101304a8a08180c0c490144210001042119802c4580e1b5246030840c1c03080b40215000001e140b0382c410060360588801c0c5003174640080815045081e820312560303009400954590000b244207000e507204900c41e40040c100f4801701003d050348940001070040d00c0c1098141d02158540c03d001c001d8961540c0c1e040198025842c090654031448500f500240d2030b000030310581001c8602c1c40c2c509000210040801020750798030790500b844060b458408c60414a80500008012a5600e51007580a81c4c0c0d00c035a25100d280c0b0748400d58004035550f40c441d00f0199058492103440c0282911800d918402d0306420038050461 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 212222859 1250 212221609 212221613
    0x151e1209150603030906090f03240103030318030c081b0f010c090e06091909063303030509120705030d03140109060515090d060603030203030714030c070611040801050112 75
    0x1072914054a40c1d4001e51051180405071384421003101c425000071a012403c21003203400003490300c4240d81d0041000c11180003001104016907807030170306a0740700752814051000c828000402c600240740e17011340020847c00140c000304c0c0e00c0400800c580c9010514078040280c0c1d42e0007040c41c08450030b8644032580c0d0340b44000a862988410082c0c0a400000c220410904101340042d42101000d000e0160341c000030241702c00f4149159111786240d50f800a02440360709007443d24460030441001e445407400c404440301025000d882c203080c1c01500d41c1a25607904003e10001400007100d0f039a00c500c4020b2103120b902103500c2d90100b282071102100c0307a5010400c000c01000003c514401a84410348441c1400c809011546c1c2c2c144403082510900100b050703c44868100041c2c004280410151809160000100c14140e010005500c5030915440b2890142c1c08207200c2404d51104444141da200d8041c0406000a8070a810a44a134441445d0b42c9042c162540f54041c00c69400707078009040d6203440c018200c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 212224109 1250 212222859 212222893
    0xa030302070812031308160b010e0a0e060702070e0712090b01060e12100f0212100501020105060d110607050f0f0102040609150f0c0501060812030a0b151e1209 70
    0x3c481d00c100f052800d50428411a10603031400e50740040140c903000c5040018000e03400f807803081c4c3c83d41103030b2119420750303440c14200c2d035a60064813400d1004d424220420003c0100240b603030300900c4e444e4014003600d40350200c19883e89801034014401c00002c8080309445100c60301514519a014000360510b40d45009006071042c0b01025980c1e01403225161401d0303001e840840c0b254115042100d011801120080b408802440f4440c3c40d20040003c010070300c21041041d60102064130000e030000c10282c2c0b9034408004075803000c2d0000414006203804a5031080c1000d801810440d41300700300302c03103d4060603441365003401d8840e12880016940841c08111040e8002c0518000b0800846047e90017012840001c0c5640300344512902408160105442000f500f541b0030401040c060058640100c04003980301c000ba8029200402a542012800a02440c00034095071800095039515450300c031a00e405440311070000c09018499030701c02c3c860b410440e1203a20384c0d98852011240034099107182d41403d25 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 212225359 1250 212224109 212224123
    0x313201503150114032202060a030b030c060316110c03030c0a03020606043c0203010b120a060f050d050109050115150305010b0405040e01060504020a03050f0a0e0c09070e0a0303020708 81
    0x40c1003200100c00505056040343c11290890392007421b610388480c6000c9038508a01402d40025002040024000c010355030680c8480d200000c104c1c2902c4c070442c215000c002081c0000c1d1064140411030f4500754030514081c08007000d820205074241d03019890f6410006c1e08541082c82e51070407a4100c01184820540c0c1440500e603c22422201008030510043d040005c04480401045038848142801e66a248d18001c3d04110460301d0390040d503a96031a50040121034100f40c0000391961510302c041a00411540608030688078035984000c2c81e6450102007005c0000c0426095a40355600d02700324010403020300490b0344074900c55034458056854202800c4900c01c412003914101442d10006000c3c0600c0d460840d01105c82c211008a00c110b030b80c1d0086401010b0343d13400716500901c00211100e41e1a00740d042144500000e02030082655550300c11002661688018a42280c2001d20a00c00c6450540d944940051172031a000e09000309080c0440c91049d0550010b8004d41d014010400075030200301b04003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 212226609 1250 212225359 212225401
    0x5060f0705070503030105010c0213090606090c0903080304030c0f140705010815011d04020c0601140f0108160305040c03020409060902030d0903050303010504050c190908070b0313201503 82
    0x181d071900ea1541c0303941d5141d01041c0075440c1048190004a8290b658440c2065502003036054200301070051890040d00400940c415450054103100e00c400c034960050a84808407500140c480d403841d038541d9001ca8107005007610480d8502c00d03014094010504203207409003120043d400406c042802c041c001341c00f5000c018a070b90701110381c5002145c0b050340c3c8604c20800c8074001940050000c0c0c0901c0018000c0c1c0101c003200c41c85c034401c2d00c000140324400c083c6200f030b00180a0f2040801c0081d840011503480b2012540c0200b141d03c90290101654480d50102c1d078480e0240c903421042544a0b40000e054910070b1005852007900c45001780d007945001d0000d07132212011400d01880091441d0740d050b03102e000504c06c052041da50b941c00207400c000c2820844030030f41d03520108801c44074800301c005840880c550017107460a100744c0c500810030b944072000722800b40c6540000003100054079503401301001c88a0003440b0b460101e12090075260748403c00c030a550001803000050f10f070b103001d040d05008030020082c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 212227859 1250 212226609 212226617
    0xb04060b040e03070b0603010e010c1e050406020601140307032111010b0a050904020a050a0b04170106051f09050a12050c0901050d23030f1b010903140a03110705060f07 74
    0x340c980e941d4400404c41d030f0025070080401142d540c03690002401001d2030707440b58489500304090850f265a010300e04001b0b40030014614514414400011a00b5005500540703001d030f4090801070202040301401131080d0700c001070840f50003035140c3e51100c00f1090308801c415203d9803641c4800306240d410096000035515520020415142e90400003040d42c0045d10400d4007c8004401250070340d2102141c0e1070207081c019005a010550350f401c4520301c0d600c14440d48070501c0700d0441c43c003041030060089030221075000300024034401100c0c80401f0303003140400c580001d02514900000d40d40e264014031000230201400c000c1002c4a1ba42000e90070610b003400c5591203118042e00500c031656601c02402c42c1a50840708003250005a0400d58203242a10f9180d0600da100c0402c40c400b0003c840001040009000c0414926480050345503a080c0da1045030001c02154035030502d615007880460180c02e0040303443ca00407556450014400040d5030102005480503008102003210b80d66902802da60080d4092038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 212229109 1250 212227859 212227871
    0x70b1611070b0702040b0907080f0a0b01080c030705120108030c15090303220c080a020f010806011e05091906081609050d080705101b020706020a11010203040803070b04060b04 77
    0x3421515240c590084035090040400ca4806644070360b4400310711002d014101030b145007031548020f011204103d90800c1c6d000e10410003d1541001800303100d0545a06031640011621002007154454000806030410003806002602041e072510200b140241003480c091581c03070702400705840c14414260451000300a5000074001e141200108885e0301025400c4045590a600c1c00361100107540ca0102826411030180c020441d0745004c00d43d055801d00c212520605080c81500640e0f80105c1103880c2808940c1010381c213212000c5800320090a641c651030003c0c5001c40c1400004c1500541c2a0b0f19014260441002d00245420250082d00031a00b01d04516007444140b60007054182607024147c02a45498880d1082000100a440010f236116040c0c82a05401c1206c4000604804695940001c0307034a06800c9042d0001c18003101b5a465075000c1c069170282c607100d964202c00600f950904507c400c010008400d5800c2c40900700191060109503110b0416060007000d80300c082c0b14007486140b03402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 212230215 1106 212229109 212229137
    0x40809030f030d0f230603070f060c02090702060105221104031103120a0c060209150304080403120e010e0d050c06040803120123011b0206070b16 64
    0x246080050032042074260b025581c10205820300d402082020000c4070205010f0f05d0750000000d42160803240d9a01d030700c100d420041e41e01c1071300021281d914590071860301c00e6207541c0060062008284550501d000550315244040d1070304030f0f0b105410a805601c15854001c00d041c0050840c54544850343c1b030608141806112208610a001b6586580c0d24200c0e00c502380c070104000c076900e034441e0f0b04050307072000002d41c0682a031f2684501142c4100c5411010703400214400d03440740b12505d07100d0785035280000302c00f22090100428460420034800700d90b644400d00a4480104031008108004503092940c208090300c880240c0200340040e010400102c00402000b80d0310381c80c2286136150381d980c46d003110b003003004940691407060b00880c02c0700c00358404c072001042e0400c60710300040c98180560000d41c940c3d000b010b085540600304010051580122498850904003d00340108056410 = true := by decide +kernel

theorem cover : BRFrame.Cov 212050359 212230215 := by
  have h0 := BRFrame.cov_init 212050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 212050359 ≤ n) (h2 : n < 212230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
