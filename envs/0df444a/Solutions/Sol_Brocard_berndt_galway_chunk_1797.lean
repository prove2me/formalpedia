-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1797
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:42:41.811002+00:00
-- url     : https://prove2.me/submissions/df7fd74a-b3e3-4c6c-ab1d-3e2fb70c2449

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 323021582 ≤ n < 323201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 323022832 1250 323021582 323021593
    0x70b2107081303030f0f0f140c0f120a180b04030e0d0201050304150e030a0806030d0908030a120f0504050105060a0501080115050903030c0307030909050f0708040602070c0305010c020f 81
    0x1003154101400c640c0601d0814010104501190090340710400540c0302c12400315603a00c039411800141d1f002501030000c52a595540c290180041c011815000103983c41402d103040d0f0ba519000c117107801420815100003100b0b80204102c500c0a034041d4070141820480050866501d05141510171022a42540800c000f00c2031a859032a2040b5011011035058640c036003551901d890f800304010b90841d81551702613640d820500a040104098450044540c0e00e400852400c4400d0500b094a512500d00a000201c1030900c5418801300588401003010b25081c903a0f00420f04102c00586002c07880302e0101c0d0b141c4010b1006010741074110341e20a800035128902c0c1281e0300d03030045410f83e80c00d2190504401c1c1d044900030556125200030041c0ca000201246c0c101003002c0240e50071a407001c0f00480108425440810100244d801071550086240202c21214030340300704060000c0c5402000204840d0340000c00710702704903414400754051500715008000c0c841c0b100c2d0010f50b40742c020440092261090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 323024082 1250 323022832 323022841
    0x1120b0d03092907031107031401200405010e0d0303090b1510081009090512041d0109140406050a090606230a0305120705070b0f03150301020c060103020111070b21 72
    0xa4a0014000501d0b1030b0743c0d0700c1c0120545003200d000b18028043c406502030040008007091000400094140c40040006104000743d0a1800c0d124607501e071101c1c0c0e03001d041c4810001a03801c2245078070321407130640d81d0701c0c9038090314903044004101d40ca5004207000d00a6061203200c440303804200110210a1712a001b0741410204241c4040404881d15209040b141109010394607958000550480c4900112001014040c0c00c80300d40707420540107150010140f185100c0250325420245006004181007007100e03003001c05800800000050000c1c150725110000f06804000c0780d404429416046441013000c42e841d500300c100320900c140a042e207920703280821b9190614180031490f007280e92141c02010031820006000300c0941000900b52043d00402e100000c00c000c2070001000b001d005d5040b019038a00d8445408030b018000c1550b440d020380c0c4184062074505400190103030540e50242041d0206004000245140161541240d6040c0801292103610244001d455150704001c2505a655950b030703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 323025332 1250 323024082 323024129
    0x61707051017150a05030a0c1401110f03030405010b10020a06020a11100903120e030702040b06090904031e030c0f1116030b0402130c12023603060a0c0e01120b0d0309 73
    0x240380c0010700b943c081c0f02070030040700e00001c080b00300a42041c10704240681504bc509801c0c124400e00300f03841900000200020030000f03102c0c03001d5018040700c2e00740d844510310000070754a040c00c0c600140141e600091003d504c600603002d4480c0386c882d00c0100c1d20039000c80040400901000c640440206034050044420b65210703008a202006606001314100007464003004054050540c0c041c0d00a8810400034180340c0b01e00700003502c900e01a0f11100c0151a8100610f2a40b6040c01c002c041050314004a141c18542c2c0000d00c003200488502d441503080c0091b6204a0414060302400300042ea4950800010043d03240c800360f2082d4022103508034010161031580041e5542c2900c3c4c040041d281c1c80c551f25500710250301821034141c400c42d6101f0f4000c00406852502c112002c1500d8032541e5491403804540350402c45030354410308a0105200c0c0c0c6581e00c3c00905007041e101a1241403081115182500d0703c072381d6012400180006155842002150402a0107960240900c200c00c2d150205030500f000c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 323026582 1250 323025332 323025343
    0x10c02160b0a08130209041a070e0904240516030e030f03040f1406130209180c010c030201091713080d0903060b0402130b030901061707051017150a0503 67
    0x1098140d10928000807940b084900d988000e10680c40724010315040409070300c0d541e20680c800d42c81460100707800b507503d0b02e00c81040eaa00814040c10085900c05139850782d00c4e40340d030542d089640641c5581c02d02c50010003904000f0386000984803003614050802c4450404550284015134075a01d040101d0300c815503084d0340342d100e900511200c444d41080414006990b05e075002d0a01401a02180d0034211121415800c5c0303c030650340b080fa0042c07201012801e40c44e2a10100d5044140343c041c5003e140603000d0740c1070702c036103040d01a94140b281b80600042858001e42100188580c40100d4440c03280e00c0c10101b5020f0381221100e01d812200d4040f0210f540107001412040030300d900d454040a10b4039654851003c0c044001e10541c0064007402102d210305a050500c1015100c0f00002c00d03100c0c60803040c100d0840d22a42d0100715111400741a10094000204800040c0e40095925803982c4981c40416203c10004800041c448001141000a0074088220154000400700c483c2911a42c1c0d9004055840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 323027832 1250 323026582 323026589
    0x80d0e101a011701032a0603060603050c030f01063e070b030c04050609010903120201051f0b16061b0512010b04150e01090b04030606140604150516021002010c0216 72
    0x35084a030051010071b181c68002450403d0101501c500780b240300b80344c16100d00442e0700800202e500e804090082a4150042d0b0394084001041e260075494203a216089904041c4116400c0c001451982c9800203000e54001c64003003084071812000401010050314203131180341507c00340340180100842d055400b403003201d004000c072212440c14035003010100002c0d9802300564505000e201e040c00000500b4085481000708002d03000002c0368a00441c2e840310791002403d0454000304440c2c0c007400710310b40388400c0d51502a101003001606104506e000c40043c03583d40700c0c0003003d040c6c40030340c241d803154020f00500900c1341ca000c4400b41e50741c0c0da0710240d02902550250a030003e03010030071400c03540e00c181c41c0003490400502d0f041728400c1c2d07144c2e07100340290b1040c2c1040d42c800c0d813070702c10510200c690162105000310b820307518186003919003203001403041c41e1103c08038200040010070342e04191401040300c004a4005004403501d407502ca501900910030494041c3c050b0040807201d20a03103200c000d800303085 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 323029082 1250 323027832 323027867
    0x4210501061520031303123005060a1d0a0c090312080402011718010e120301050904050a0204060e160c11040e070e0a0606090807050d080d0e101a01 65
    0x443c9041c83d01035100c00f0000072041c1c4611040c46900300b0302c8a802c5040004500a07803541241080116005002e480801c0c1d10100001c4141c503000c2c0070f4901421000361041c00b90030700040310b80303841001030b92210542c0c1c8140405054840c4601c0044c2c0500b0f40c01e401555488408c004441ca034103400d40380ca824620000d007500030441d102054140c0100d0640354042d205140c50305030410800006d0319082000d891942040440303909000800000f48a007049181d000c100a00c0e8540c4561882a2141f005020300d0b0300852102d000300d4108082040201d425503402082071096039180c80890900e18012144000c000324810852404035000d000144681e5070403842c1060b140b952801070002401c208100b100300d52050040000d0b00c500800311090007600c02c40c82c0420014038000008220b540d4541040006810003c0204075a0b40c035035802403034603507020390306545030940801c1c0da800030284680ea0181c207000302c1d840d820702d040ea690b1052000740209000041c1c0100000b004541d8000d800801d07024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 323030332 1250 323029082 323029097
    0x1b1410050a020309030d110c03030309190c120b0601031d0c10111204030201030c050301210201090302060a03060906060509280b0403080d061a0d0b010203042105010615 74
    0x48452051009040055075801104e04c0e00c142c00e00400e00c0e140281c0c00c1d601c001541000c40300000d440c2444445d805e01012001103003913007081a2955103c1c51045200881c072400006c001c8104039480711048020302c02c00d10800c00c0c0031007d0900c00101181110550f0005e403030111400c1c0c1d0003003a4064105000c20307070001051401a041e051241043c80b40c0021020301003141403c00104200700115880c01c1c140d03c0c95251920b140d4400542500e03154051402440005c0c001406000e0080c52072402a08400c82403038a0000c0070300042e145c401c5140c0012f5001000003400b21034054168000b8421501c800c481003124a9540008981d24028058172a0b4000c94a002014042800b1008640c1c80304400004188256980d100e1554540c81540105d4030030601140c0c1c18010340c124402e040061888a04000060191030301512192150300303084181d40d5030710650200c0e40e034400c1003500c01600d21310003880155510040e040e19030b00711810048609609100022034140075002400003081c802d612081e9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 323031582 1250 323030332 323030359
    0x2040f050109240e0d060609050c030919030c08030108061008060912090a050a1d0a0504032705040608010902120703021503070c022d0907080c0f040f031b14 69
    0x4840f840e401200b0800c000c0701c030101030040c1d070720031014000e010720607030000802c00d2521480320107807030b0000e040d400c2545040c0200598020007240c600d500d42e409498000800c4004c3c0760542c0c03092451030000d45101e001000101c1c0404002804600030400c0c0001540403650359061079030303201c10440d50003070300342c0010641c2150a1400d0019000000000300714402d11503d4101245401c282c0e540400d00c3c01030f400d5100032220140e80d0003280c021120010a102c18a000d4030098100c1c0000310042c110350300c0302c8070351504c44850f841110016040003882400080d03990f05000f40038288038401030b40300b40290418901e05050002d10f2104403580544034094140c00d00c15907180c203410080c280024018507107051001a503800308015241c2010a14200406010000c08612599100f4003280078101341c20510105035000701e04150322200c1e1a1210360703569044080520340340100c0d80300811490340b840c008000c0011131801d07810a088080d81c20403140d562090300300c0141c41c0c01101a500003c007080d111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 323032832 1250 323031582 323031629
    0xc07061706192601020a022107020319050a0203010504050f0124060f052512050748060e0303030132120d0206090a02010504092007030302040f050109 66
    0x741ca2082c10031007642c4003c0040c030b5420f0036a40940301102c0140c0281e0070714982161030340010001c940050440d1400e01c000340c0d000c00da540d1342d408881e03082c4075040c0100700d0130007100b04030905c2441e0b4060000d1001707042c0740c80d0580d518009502d1140c2c4a500700400c0001180905a015600e180356550841e001c1d45480c005aa00d011181d2840c02041810000e070b40d400680d4002c003017142c0601d500c0c9640494110300f800440c03600041c1c40401009020031001300801d080f019409414036000040701c02490a40002c24800842208001c005002c1600c2c800da00d0b0304280490001c880d104d40314981e4001c3c0302810941c4a02c4240645c400b101d51700800b5640442105003c180450102c552204820356007400240070609580284d03245540401c800e11003199040c04260b4000380700c200105441d0500c1e40c0040d100340143e01600007804d50780c03014004c0c0000f885100b07541642d86402e00700c2d80d490690030000c020794001d00074821460100f03880001d995205180210442c5c900b40324544c096041040e24 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 323034082 1250 323032832 323032859
    0x31b06160b150a150503041407090e0319020c030601030609060f020d0c090501050301140607050c0904030c06061e14120714010909090206041502030c0706170619 71
    0xc4640068510186400240c40c5941c4a009022a0a51001040b02d11040010705112504060403800103031144101245e04002540d0308142e2202c03640c1c05a4182c3c014451a21099a1001c15858184020b110701110044002c04001a811034094040240c241060380c0c0c480c0140d66050b00341d4032640041021401a07480400c015102da040403a0300c8566004020590f0004444424003582d9174203000340d55030300140604020542070819a0135503242440440b00359181c40844e43c06483d0000d0703244d00b040f000780022248ca00d0018002c0c40d41c0c2c1414100281003c440403401c0350f2031441c10702c1c0803c10541c03448070b50600f806918600f032100782c01c00c0711005410300007a490b60313000007030314840f9000d064080c040403000d480725500d800c8500c2c002c400010310a080d2a4400703200301d0310b04408440543c98410403a01603421224144010102031a401c92851056441c40141da008522011a403076500018618004000100d200415221002000344044102030f8000004841035020442503106c1d288 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 323035332 1250 323034082 323034097
    0x90402100c0b0c040509070e09130f0c0e041205030103081605161701060609080c060a170405060412020102090310150302120706030e07150c061820031b06 68
    0x1d1031081c104081d516401050010754104012000c00b04040c003442c20075041e40c1d41e000d4854078007800b2050000001c00e000300c00140c444c02c2074058089020081c443c50446400070146d0040382c04010940d82c01c1c0a0500a00c00d507011610070f2004101103140c640704000f41c0f030599400c003000d02c1ca801c550a03c0d40c801c41010741d404032040e0265541d010101c5491510782d034010301d26111500d04410b100b0b50902c2c2116096085941400b041c10001d000028000480300c039544d000781c4d1003640da400402420b80b01a03002d04110307443d0710340500800003080400701d14280900d100341d9465105040190040c0d09038000c1c03103180ca801d588013081c001440640da4000e00b2041e0451211165115101d0b008101c034010000c2c454103050740080c07820419a54140700d501240d40301b041c0582071380c41c1468400c015041e01c80d2040710420584100c0c00b02808a0f13980a034070140b0100181015603541490300520341192850a5401108801e075203400d0341c1800300d221400102100350a114010b202400c11050707401010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 323036582 1250 323035332 323035337
    0x40506040e06040b090c010c0507121110020a020418031b02010e03010c03140c03010f0306020c03090a140a17100513060603051b01030603030905011101270209060303040509040210 79
    0x45001ea11401071080c1800349004041ca502146040407030280707031041001c4040c1c1004000079041e408038001054160a5401d20100a01d01107050f090034182400b0554202c2d5001114494440e201500009c84c0d104080c4203450520400741c02081d000c610344402c00380070700840c3c0c065909104d1103090301c03072042c41a481410300c1c0d1040b55440012130700f1034900007000400f190380c81110081325001c0350882c1d540980f0000c8400d1866041011a6490784850701c0010180354021460602c03030903007031050300c00d44840030f004080c0303580d901e0f00290144484000d0841c040d0308000004501d40004018a42046401c5c800030054000300207496001800c0050540301081c9c034664002c00045c071a8040e500c011030180d40180501001041030252644545007100c0c14185080c000b040040e41000102c0d04460f42420f1030341072803c0200d1010701400f0002e11441210100e070340000070707a102c0001c00c082628000e4460305140d50340c00c0d0038180e0303a11642c002c9541c0218820000703001460018a42c41c0640c0461 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 323037832 1250 323036582 323036591
    0x1303020a0501020a090e0a0c05070b220c090f05040203070513021315110303070804121724041503060c110f0703030f021c0e01030e06090705041407090504050604 71
    0x40e01c07201d003280c0015546000083c0a010708101d460440769407960440e520716400c0219404800b07025106119088000f04120742ca003000034211947c00384004403100c416840c00800340301c603103086100b02c803840c040d03012464a1702d51408000075807485918440c41d40a0b000700f072050f08110810421110b2810701482c11a000c11103039081d000180e82600003030414a18603c46800800800f8250b80b822403e60700c0070340d2084c41006003166101103034940040c0c0200307030003415203c1d1040c05c4521904040c0358408903601e07241480140f80482d140f2114a090320540000901d0418003000240c0f922252401d0200c58002400c0c4040b800d40e90010244000c02d0a00f10300504200c50b5050070201c680c1c403000c3c0b164100720010002d03d07412002061401c1e2482c07000e0900303042208003806244440f000c0c7c040c200802c502e0104400c0e4003e40c4034041c002e40400c102d031880e1802d0540e0942c2c590035801402c0c0650305010010b1a284100702841c0c0c000c50860700e40412940c100018040104401005142e04c50b84a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 323039082 1250 323037832 323037853
    0xc0d03110115030804060305010503030f0f0d09080c07050f01210c05071b14010305010803030415023c040b04060503040f080f0711030303090a0209060d1e1704050603130302 76
    0x1030004000443c412601136440d1850140040c0c1200c01c141c0c000c90082e0420895404845d030300310221071884080c00c594503110042c02d9401c0c00200f41c11030303004260f0700c40024072003c21900054283c00b110000c44603401142401d03001110304001d600b000070044001d10b940b1039400725040e005004690600e24001303040020702e0b1940c00b407a2542500c1d44440e480d00407000e0041004100403404a181c00b03090a010030f501d440115607403440003d00140c071481c02e01005100203500c540403103449519015055841044038a0341000d40c1e060480840b091000d21018540444515400da400f150790303100015017014a030404c20345480d40000d01c202e59007001080741500044031200540041e280840c10300340c58a50600d0404001d403d00d0840b030f4801d500174802c0101140c000225014000c0e0f05442642c400d13141d600c0402e05181d020341d0001c043d00328200c5001e47d00114203145000e4103003c1e110465003401003828440301c0707100d140685500000201b0001d4141d0014808855601b07100384101c0f2004d442 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 323040332 1250 323039082 323039111
    0x8010b180a0e06073902010302070609170c19050706080c040e1509070c120e0607020603010909031407030926100605040b01050c1915111b0c0d031101 66
    0x10100d030207001107014a12018004a5039600c445c1d8044250001c1c1c018600385484081814140011700134100350f00003d2040030030041d604210b0045031b1105520344078054200c4141000e0b000052a540140700d0303180d000307c2c480c6a0303032190402180c001010b4000d0b6410450202c4020000420305607078103004101c000b03a4003108030035441c070444010114003000c5055108000a544020303110000300b000d00100f010201c4d1400358a0040d41000f070074000c1110b208030340811442e00420001035804070010000060050054000c000c416200b541c8543c082d420004907001140180303070780940020000a02444118011a5080b08151410381001d551080d1000020302e04034207241c1c3d100d0001d807601400c000608243c00f50020243d400d00340141000c0d501c24050b50340e04110385d104400540c8210b035042c24880d000c405440c50f1101f40006010900e0402c00c8202c0036480b0001010010001e0319059581001c04a43c00c007810100a001c0b500e51f500c140c40880705511040406c40103950307200c21a844601 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 323041582 1250 323040332 323040343
    0x60b210c070b251e020a0b0f070c020d081201050909060f0705070b1014030a1e2406180209030a020f0604050409050604170301080303070c05010204092408010b180a0e 73
    0x25a1903030399071414242095030f005821034460800040d9802240d04000240051502c10307485071441507820b99990709c00b0000c864280900c54040c2d0081620440c0300288210300005001e20f100b00e001401603641e83e0700c144918400c0403243d018141e00080003060f10b581070303c001c071070f0001c80c1d03494171605258840e100c0c03c4c0d001d4016a40012882d0200400700004882d01081011004d005c8001e00000e06864071044400c001d00a4124410103403440394200300075036100602405080700c1600710b001007200c1a0080102010b000d0112404180e65000c84c0c040024003c44040c0c0780050090a10105198280b01d680720017556500d82c482400d02c40890a51078030f20038000b83c3d50141c0d008050303a041a040418030800f020000e840b070b45000300018030a5110000481c3d0f042034861509050100320303420682d00900907a0014100507007030501110b000c9400c3c0000b601130340318445105508643d103080f12400ca4060840b07094002100f0072600030b003002c841c241c0a50110741006d0101c0c1d2045000641030420307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 323042832 1250 323041582 323041651
    0x510020d0c0c230f01080601270f06080a05090109021003052809030813210c0b010e0405010b1e120a0501020304080a022a0d031101060b210c070b 64
    0xd07000760340207900f10700c1c188980004840081c20400720034141a00000c0c04030140300515008401170781048081c968003280e101d03006001d160301d0501d403a61280c0e40146940d4042d1503045500d424231011940c0c000d0188503140d9101d6000b805980200700c0001d06602401000b0039541034509409003103c0107001010b0802c900040c0d8182c00140420170b80b030040d286a0303000d4550440c0c16014000b20b8002492900d45003000707484906c2c0e44440a85e89003089803802c1d107001c0c0c0144a048408000a414801ea00d1203a02442c800d90007408042c1e128400c0c4170303000c0c01c41031802d14201c800c040011004e090480003544249014416a810203030741e9120182680d00680d4126802c04001540700c0301154184805006c51843c000c003180403c002d19000c0350950000043c170380c842c101505000c800c041c042d0703d1113060000b0b218028080265601801e4284d40c1110b041842d14400d04c1e842020541c8911207503a110394101c00ca01401d0603866201c59083d50b1009001318001030b0850403801d030403402074001041c071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 323044082 1250 323042832 323042879
    0x606070c0306151a030106270f0509060603040515190908030a0608030309150a020c1506010228110301090813031a01061709250806010510020d0c0c 65
    0x115405443c800c0c2d10100d03d6114a02e1480100c890360050312003d0201e90444000b0726020f088680f207882000d414401741041408180400480001e1441c254818802240c20444a0600d13954500047c4084c52100701d40042842d0460b0351a80902d0260480740e61f000302c100049400625007641052046400c007110550f0107100200c1001045103940c010040500081d0000d5800c505050081c103585141c8248000d0040480074001540061b0395415100c0e8407018a041344c0800e242c40d955039400240645c1e10900501582c042c5012f24a06009902c001c1d114042002d0b03042504c0c1e44605140340b040000440e415522440d0354004645100042d00c045100f00384400149480e42c40c060b1500d00410402d25026004c041c010000c2039003107840000080b40368008816035690b042695410507403440032019423002501282d034840100c0c49903103025980400200c4100381d0700c4a080112100c200c880c0800107902500b44ac1344418441c0c3d4401008070303c5103070482c1156440d503a01d000a003112490360f100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 323045332 1250 323044082 323044091
    0x1401020703030f0501090b0a153b0a06270b0307020d171b0912190c0f0509010501050a050f0d290a171009050a03090605030118050606070c0306 63
    0x5880d41c0074440ca5004001c444000c000000d003180101d40843e20314410240d40d0302c00340c40f55000450150007585402000c01c02c9110101c10044140301809411818078032b4581003821200da02c2e07040c0102464241c1e03180d511601150341c0f185601c0d24500440a61100800c2c00d41c0400240506084000d5406034410b60060036503502a5280140108008001940482e5460bc107000c09150040c140c040110701007203d0a0351108181c02081c041780d1180d5000440380308940c1c500071101c2107101c00714185880344501014050740d45a070700c038021a96004880c1d0000b03c040041000d5806640104070720200c0d0309005091075a8003c0c40c14694101000c6d005da02500d448040c03041d448040040b01c50321000e54403242c1c589242d08003180c5408283c0c090034071121196900040642410002004800401038042c0413100151400c280c403041440d80807000300352004408100070b8003c4041e00d060ba105800710300d120f4401701c0c910f01c0142002900c221342002003048140d000c00c10b2404c01c2c0307000d180584404038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 323046582 1250 323045332 323045351
    0x1090501050118060b03060d032006070e092719052b0c020f0a081212010e07020a0b0601030e030a0c110d0807080903191103060a0212040f140102070303 67
    0xc0c20100e550b030f00c0c90400c3c5454002e005055150040d6034201e103081d00c910140c400c803468282e070f070b020302c0c000308041e040281c10102254110001e800b600c6400380341d80c0c0e1204102610180280504c040d141d072250751540070881c03510b4800d81c004440402041400b2a4507810602c2c5402881700290101030703410f40c100c0291340c80540100103050880100c07d45030300109009102c0d0080c50344e104048001d1042c466095810b90b26525415103001621000d025101040b140c1c002c0b1441c190b20940100500d80c045d9000080c0c01100c070083c03130b88130303400c160040c01c020001d5a55a1910040051150b41496903442c6084046142003004d001680c48c2c03901c4942e10416a41080390350702c4251504113100701083c186180000c2d000c0750544000680c45154185c03104501c00c0041d042c074845078203004107980c030080c00c603060010040540640c25015025a0441d8903125406030603403240250345051981442e010500050341c0b03082481245e4016001c0500014164400e6030070b9038401c0070280c0020786c0760f13420070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 323047832 1250 323046582 323046599
    0xa030219060201050f0609060f120322060e010203070b09070e1501230702040509010b031617070605090607020f04020310030c0b03040f08030702010b0301021b01050604090c150e03010905010501 85
    0x5980111081c0300c110303500e16002001410b1f8040050180c0d001c2c0407030611007001c0e502d4503685046252840c81c141c0740c8540c0ca00422580321000c5040c0044018500100014154012400044401c406901540c580011629800a00314024122420621814400003149071034201d846008596800700f154032681d20304001800b00f030114400b0542c4080800c0d101a203242550120352100340d040e640410b490340c8040685004100c58141e503a00360040004000418203000784120940e610802080440040300c01c1070303a915000c0e0300905000c18810881110540703024805410b005200506c0f207071b603545d04113002c00c050707030411340313010b40200f48204051082140058507003001d0714070b8642d100d00318586074413501d03000000d100000d001413100002040c49035200307400c07a58400b1805402951380d40070f54000303110000340c0d401c0c40d940e8551804011450614041c0500c0072204d0300142020847c0b03080c440ca42001d409800210002c1c004e2044991042d901d00380151031801340520000280b03980341181e01c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 323049082 1250 323047832 323047841
    0x1e16060909140903301f06080c0301090902060715020306030106060c02031207030207030c030b0f060f0114090102011401090b01030507170411060c01021909091a0f0a030219060201 79
    0x40c002c1e045520020040481800070645810300c1c070403a0640c40201440c598801824140103102e0201c505040410045540103040a400c4800048902203041e540c1c0d20126054003055828032035080040004000300c8415801000500f4001407001d0301d02062035030f400c503030b8040350500880b810742c010040100710301d028403030f160003450a801c2c51010b020f466030010303032104440d11030480c40040204007001414401c0044401a42d1311a031902e00071034590401c1080c5e02e1007254440311020a1800160881c00d05540300000f82070180c40707040c00c2206000d1a0030458102410300b43c1190343e40c445070080c00c41d80401d124003c0070200b1002418a15550004050321401011002032045071000400c8020741102c545500c1500b0040c008414055080001c00c60311502c000c40d00298000304030020307004c508034900304200085441e080380d815a2101a641a18444001c08513480101d440156aa0800c20b441010000b0020174402c20542c40383d0002e90a4202d06249072400c5800907028481a9024441d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 323050332 1250 323049082 323049101
    0x1b0d050919030806121204090f06170c101b0f05060601030b090a0908040e0f0601020d02070612051003060207030906020c190504020705011506111501081e16060909 72
    0x600245107016610041d201100191203207004c1c4040c5460384a00d02c4042c010030103a5800e4001c019659075941031000068140c3d21600711000c0e00e804000a8100d50041c920090350680c00080c1a5246210342006250300b42d5110f22424044072510800c5050140d020300100107200300c1d8106003400090408915101006100c03a05141c80d1020b80e80c007682e101101142d02021030400454403403003e241034000f0340115400105100700da2014001352038016000c1d603104040a034201c1d55119001101261303110701c1032160201140c51002c9920445026810042c1d03c1496426050b00700c617aa5962001280d00094007500020b8080c0e000748a91517040c8000240703100112141c031900001344040ea24906c0c1c151185511407a030009040041000a40004620f05d155141ca642e000da0f03035007030180c940c009114480744c841c0604010781c03040401a4440340e069410312002498124a0290078440000351134454401500c200000c001c82e0305900144200900a1a920102801d2078641d80707106642e480d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 323051582 1250 323050332 323050363
    0x20709140903041e08030a05122a18090106030608100605032815050702010c030e07030b060109030b1e070203071a0a0216060903020f160501081b0d0509 67
    0xa05100241900100f500d081c0c1d40e2445031414004081c040810304150b4a80c0580f105004c0803030740f1500d6030341000152051404d0400001d070310381e442e131001018681c19050302103610b11076100c14520b4450480c010703080c1c507040e10190002c09107484000942c41d210980c00100041d803108003c2c41001400d20080a500009a070188101403c043c00a41c4445405a00001d04095413098503244401e40440c07500c80c0d0341081e07a501d401c10284040101a1a045078294055803c0015095815101c0c1c07240105a945800c05072048601315a1200b0030440090212030400c021400040f02080340002c666014041040013104200980b01c0740c003010000080c07001c401c0d0741041c80040045084551b00c4441d600e0009481001a41c40190b290000c1c003c0c001c521844058510154003044070690000750f0b058041e808603408141c0903662160741d032140d901000d21401211000708455405244101d0304a00542904585251520f0303901600350003810840813000c4d21107060081610060054001c60b50546 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 323052832 1250 323051582 323051621
    0x9210a1109040b040b040c0504020c010e19020f1e150904051b030a1113030501020913050412080903070818010f09080c060c0f0a0503070615050f01030f0e010c020709 73
    0x1a2500c05a03404024805410031880c90001000c002400c7d90400180500500c00c540f288803600c8200d00900360320310f60040e24451008641c84100b0300d580000c030710650080007015a105c0b907006204482899103500c40701c54400700d0640035165102c2d0100c04103098092002c0d510340c0b40303e004010581d1000761045007485510010018290407540449510010042011440c1008031100c09441d10960806811030490b001c0d02004004d010340090100060071107400209200814090049032801d5400403c403a9030607404c05080e034043d51740c103940900c0740ca0540f801c0510603261800c00394010407411750401000d40b120240da68004000c0d641c401110f144c5a81c1c890305008069035542e41101890344144804510301410130000c008107031100e103000e02a10304200e414601241d5a80040e00202c03032850070000d122521881459410701250001400c00d0007900764a03006500034100c4100724442c1c2c0741c44613611030f402c1409000f901000741940c0d0042c5030b540c0c0b4080010044901c4903081c00d0148218 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 323054082 1250 323052832 323052841
    0x1005241b12090904140a0212010204140402090a05120109060213091415040908130605030105010807020a020d0204090218040c1a0928090f150905061509210a1109 71
    0xa2140e0740f5130180d070141150301d02034070044240b4038140318128001c2d8400341040400d8020003064000c0c0c0110341015095200f03100c0401c040200740d0041507110307900603074868070030421458200e10900c05000e01c41e000003540d404a8071101d0980e48418032030012a20321080401c00e000e541d208188500f60b2161181d0003600308511074a008c1405c89180354403e03a00d80540106208586007103803a0714001042070030800c1c0d66000003402c03d0700244100d50114681400003a0a180085a002407040d402020040d203a505582008001e240151041c5e8208143e805802d100e1122140300034012401890000642480c261160300031081c2c0e085051080c24040c0f21096032610307144400c01202c400083c0c40d420030600b021622814144990091240c98240071641d84c0509040e40021380f20621403c04128440d1285005419500240ea0094000514108030750a0310b41c18400303408485001407111220111502c01c3c1c0c0c030741c0d5030080310314600f580205d02c07480100111401055800c1a003590038031901c1c50b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 323055332 1250 323054082 323054089
    0x30e010c020f040e1e010603060b030a2105040b0d0b1504030f0f02040b0613030b060109290405061305040f050c0711030a1205130e1005241b1209 64
    0xc1e0000240625120000b40da03a190042c0100d845e40700c2d01507403104030b0000c151903050180000f884141c80760791900c00e0402d200d09001c40e071014034907009440c00740400281c00354000c6002c100d0b1510b004000041c080410100306443c01011200c005001c040b548000e00e0f0200851a1494001180b01d40401c1004100085000c58001c41d0703243c10000651001c03060b80003281c0070b0709800328441d61140300014030b41c02055910240800344c0e405200ca100542e501c032001074030b1080702c90103a481401e0000347c8180340003002d15080c0140c207000009944c102641c86000c174240e50002600c24542a1032000144410b00f000d108521030000170460500c5070782442c4510200c14851103401401c881c035950217036155034408011101580b640500840c2001c01e031300000400981021040341140000d8030320000c0c00e03401a10505001c3d803202e549001c0348034500720420490100070030b0701c0700384110a80750351092140c3d00310241c00b42191900b1140300c0041a4030b4034509068440c1c804400580e400e1040c001c9544 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 323056582 1250 323055332 323055349
    0x91202012301140d0507030609080301090501050f0f0906011107080309010315060e0d03030b09011d070e03060c1308060c0406090e07020312040501021b0318090f0723040f03030e010c02 81
    0x100f096559040b03c2226041a905068a50308050803581c2000003400801c50030740001d504aa074107a00412260340c07100100b010301002c03508815440351035030750360304010314110b90042d4100805042900c0c042c40c207000102c0c1414100c0d440518590000b0030245015605801400300104110b800014000e040c440701502d011546040a402000c80300e000784109800b03a0700c010780189000f00340915a69490b1100c1c0900181c1c280c0c0f1804501500300410021402401440c411034070080103400650743c1d00323070041400c6d000b900c0900710a99002400281c909028403005004602e0180895525810700e80c015001400552080903080c07402810031902ca81d01105075809100d9200107070030b00780c0729030500602a0190150b980c5811403040045000c141c070000c01000038111031081c000004c2175440c2003100c15102118040d845000c91b1000400c080d104610480707280e500007100d41010f425000c400c000c140c1140c0c10041110445c84000d00a25800242116501501340f030246940800f0f680441c001c2c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 323057832 1250 323056582 323056619
    0x2c0f0a03170903160e01030c050612010b03060609040204090501061103040303091401030204050301141503010207050601151e020d022b0c02150a120b0402270103091202012301 77
    0x3010041081c00b039580c1d00740040300c581102404011151a100d182c0c000c0028401c3c0b10848450440e120300040301d08288040d202e11043c640e0310881c82d68a85040c060680e4401004198030807030401000e011599140301410190548440c0081d0940c140342020f00504203406000c440c40d48240000c10010b6480403890042d10450000300c0d040f0041200141c020740138075001b10342d2550801d1155030340c100300705004ea03124880182404100e031018206060807442002406045604444010b003c41020340c85034800c02c0c1110303e000342301c4003e10034046240c3c55800e05200c005802c4040c1c016040c59041050f140c0003804038209003040880468a801c290607500740b03081c10310070600d03c0c3d0400e660b59103030140d1039519080d440a98984078040001c05202850024404aa2816000303402c0e82c203051080d6442c0310144880000c0f5548010344200803441c11908060402d40c560720290700088002c000c0c0410700c5459000480d001c1d034144040024103150424071100782681c440108140703645c903581c50045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 323059082 1250 323057832 323057873
    0x1d0108010f290f040e03191d0f0a080304181a0f0f0411030907030611070f0215040b0a110c03150a02180a060915020c0603010302102c0f0a03 62
    0x203000c1d0710b0042051070802c8004942c1c00351401d1442c140403000840100900c0d18804007144c1d004024a5091317414801d50355026541c18216010b80803d41480d0750b05264040d0010300030303240c1039a500c181e1461a8000c0c2c100320f600c0990f004191003a0b44040c020325401c120101c4400c1c0080c2c0400010072904503020f1304552192164400c004070301d448aa1107000702d264004402a968a40816007550b520124401103c0203844d0030b8000d00d41c945950241d511f49a402500c00d14034410580800000031154851340300c802000f0040017489180a4006050815240c3c0f41c40100c401005030362401c06481c1c00c42c850185d0840c410103282d00900d442405d0388481b11240046c0c460000303107100308200790084e0030303550409040b400116656801980d07440481d081c01d02c142d4142204000100c2e02d42c60342c8407106401c075505000610040c0740518541c0d034150030a16190104ca080700c1250704240014410404080c10b02c0e00c1d0404450038103816412007228290303146484e480c6541d5500c01502c3c1d00e001c52901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 323060332 1250 323059082 323059151
    0x50c0a0b1c0f0e01090302060603190804090b15070507180504110103020310050405040c0837030c021003050a0b0102010903080a2003010608161d1201061d0108010f 72
    0x10821141d02903c4032402660082042d1802c0345001380d5100020b031070807440ba201d54141c1070620700d0031842c1d411a80b81d02c0a07504c1c3c00e1600d0000e107800035003100c868280d0b1061542418240c5102444003420409000303500820fa02d40c6003281c40300f0601c20360f906101d002814242080041592504601c10b1001c0c02c0ca00141d40343c1d914039550049940030740080340c2c07103070a00c4280401d000e40180880b0a03a150401030742e00c00c070308202d035280d20b1071240204180b0408a000e111240e00d81032100446045020b030510342800452a800951340707001c81400070f030120790b0300d030240445030304584525003020400303000030065840740b80c402502001f0000d0003030403041d4071045103000c1d440c80034030900644640085003607101d5071a200058401001110940c50400f41d6071820148603100d04805040000c1da202d01907417581602c0b0500035034803000c2d0441200d5648444000410398004a890315104081c130b64040f0065043c110060300307449260205031000390901020000c0f004446d2403031790340c64080001c0c010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 323061582 1250 323060332 323060351
    0x40e162c13020f0f0c0c120703080304020406150305040311061b160f0b07080f0613020c1608030d1b0912150930050319090c03050c0a0b1c 61
    0x10181c40303840803c611026000c10180c000d0700501014010041d064029141c814801205109520050072030204036944154001c0010555480046070000d001500110f5200d13110903145014011010034040041c1e9600c003008185680110810010019807021780300070f042084100808012806452415540010704e05144071f41040e500f840740342e88602850b2000180f0b040c41e80f140c0500f140c501300071582c4140080e00c02d5804809071403107003c0c010b140450300b00c89103504600a401c40b0f0421090343c410391101c004804600800b40d00141601002541c0d40c45580f9541c2d001c1da0400c1d540004021a0340c0840c080c102e8006440b0402c0d42c3d004007051120510604148620303150300c1c3c4a00e2aa24a0404070740140030242142464900104103c203203003482c0c030380c0d840c0c0c03071504110b008000080007440810b220300650008200d07200b480490101d400c019646032036039003807215841258168010f140851070b41c10240700220041100810080c10447d001350303000c40030020781d6030b9a941075030355001e0741 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 323062832 1250 323061582 323061619
    0x1e060806131404050a14010207020d03140c0601080717070e040201030c180902070606050105090102100c020a050303090d0f11030403030302030622090c0b09030a17040e162c 76
    0x1482002c46000c0c000c000b9007414141161110f1480340141e40302600050018810036050085810f4568082c00c1a05501c1030b86d1001c0b0f49444000c0104001204200036419455004010a40c0a0146d00b00907000319417501085002205008000d491a900300e25001c0114a5001f68503d50140e028280070540c00c0c2600b034101c40301d42850303500c40c1810b040040701043c48145da50107007400910400041003165100c01c0152160300801e120140180d00c02c030f0452165113401c0d0040441e9403a0b500441d818548140c0d0788034251b4000f100d21006560240c001d100e02d15a000030b03880c490940724205280010142c1045540f00d12542c0806824540c0000100e8625180c030032090343c080d8400c445070781c84d5103a000e146801030408144140d60364080c401d00030130080c0c0e1100440300294402001009003c3c07407544c0c0d1810700c0c05401d42540e4040300500001070b0103100702c0d0203240b103a82104c040745021b940810f005803031100e14400c2206980ad01c6080251041601c0720034222450b0308076044483c1ca070139807200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 323064082 1250 323062832 323062841
    0xc140a0804121709092e1409011212030504150e0c041103071b0c150203030f1f0308090f03030d0213170a080f130f1e06080613 56
    0x102800800540001c41a0320303015800c2d901c91007074410200140b00d000210440b4001c50002c2540804038001041c41540038402c400c082e180e0243c00b0071491803005e13802e01e01001c0c403603018098040f6410340035850381c90a150990301404e00000d469803a2025a20342c604e034402610403d4082c1030b5900085000e200c032100340000e2446100c0d0091004006160709961100c003032100317a42c02a41024800f034185c2c2c0030681a03c0c464411540c5501d40d0002ca004803610440c0c18100648450710303140800f040011101d46100c031006e1454000350ba8034104440303580d0420344018070850791b481120302c071048505910442c880859030055480c43e00e072500340c0300203221500c3c8845003942c140310000318601d2101150f0060708190742e401d03965030019131303680c0d0104401646840c3c000c21550408001d290025459101074000340b4854103800e0300b45047c400c40c074001200c89030804a00c04500400c10080450401c0100c0d000581c2022050007080c60100058100c010203040da40c0305030a6070040b049442071942c80b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 323065332 1250 323064082 323064103
    0x303010e130c050a0f05030f0c101d0904030c1401050c07060b0424090b0105071a07120501030b010f08030a0c061a1504090b030a051b010c060c020d0e01030902010c14 73
    0x5035188455a40c0000d2984001c1c5c0c1c401d440c024081d84155807a000000700b0200c40105021340640305040740860216416096610008484541c500710714035251a40d0320190f114074031035103c5281c2c80101c1d040c440c00c3e04241c1010880541e0500c0c040101c0206410195240140d000201003000d9020b100080c1c082c00703244400c1003444d081401d8410b040e51000d00f0450484410240410001d68840011102886060780244c082041c10f03040c01d2a0304036220240d40e106d07016103001001e40410344032001c01e540003039100340c0d08000c500005104000028044034010311901000354a401c4d403080e0054842502000090682a0355042c100c080c02d42800900d001540000c00b2400c3c0340c1011305003890b81d90000c0c02400c400900c0e0580031050750500203021401d09030032070014040b00a04000303c002d0b502c01800b8003410000360160200c005040c0e8090007038019140e80151142c031524440c01000145400c0806d410141072103070420150342c200080c0100320742c2045e0300034005490b6203d0549030080c800c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 323066582 1250 323065332 323065339
    0x1060e040c180209060d1a01020a02030c0607060b0913030813020d0f030302040909050102031501050a090b0913020c03070b07031a0f060c0f1b0a0b1c0905070b09010801080303010e130c05 82
    0x10408a03902070347c0e200305512000385074140d80d000c031401c004903560b00742414000c0d0160f0081001c4401840d1a00140100074850039001c1111f40a000104140c23001c159510b4031071081c09001c00003056003002b04158400d01c12000c0048000b596000070384580310100c805448800f10440381418107100b0780444000d045401c8040c0030704c841a01d0094000e50044030095031200e651003036440740d50b108408940c02071044d955105e4046060229880b03940e88500201a80400710350041907040f8080c0c00903041142d001c1004d0350703c66010f42400002e0314802407040c001c141c41d000150120301c080402e01221440140d980308840149000030450714031409060b0880b502c038082c0a458004800166000c000001e1044100030810780350a01030f014a00303004000031841c0902a244100440105210007c03d03201e1010680000c2501e40c1e60500d0030603040080c04110026440c2039650308a0407050041c680c480086107107614107625403d83c8840a4403112a280c00070342e01a080c852141004005041c004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 323067832 1250 323066582 323066587
    0x20f12070b0417060106080414150106090603051b0a03020c070b0c0309130b060306090402011806030209100e060702190e01060f03050708100e27060901060e040c18020906 75
    0x1000601e6090b04144144808004104412045203c020519504072105a1101d1060382c481d56146805104190850344a9100700f40c4488081c45011320070b44d00a00c2076483d0407400d10308144000b4143d4100810030b411000c201550040d13001342540c00c8030328079600c0389401030300c40c000614142c0c1410308992000c1c020140c0801c0d4104501c201000400b140035040b1401421065000c030003600341c807100c450b026440501400000c019050520105602c140305150030303900305048041d80d0b802580f0035007000b000070383d02044140d4541045001c45140c05920308205c9502651940050024850460000d0103070203644131043c101c86e2080c09210180050100040240d0384a0741c0007461409050381c150002824840400d0003940140e00440c0502054a1020441400e107034000700d12070b0f0302600a95509160307541032910700a9400701044131000e14405456181412200c660a40750542c000b0070031004204117101c001041110a00101c174441456003c1c81d48142c030615000340203200300c1c5900200300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 323069082 1250 323067832 323067839
    0x30e0c030f010c09051504180204120c171618020403020a0b030702060f041203091e200a081507020109020a09020a0306080d0c1103030c1c02060705030c07020f1207 72
    0x19002214407210f10b41d940d064a0f0ba49004215600141c031581c0118584100424444241d205080184d4813100303a00141c0340640c3d601c0d00d942c0c2d01407001c1d800d03a05480e440b1010f102c10100001c1c1d03c000c1202d0f49008119040c2c0c070360b140b494010954840c01c4019000700c1c540248542058040e10700031500140052245075952440c0303945944202d038050300500030b600c00a042071514280141c02944c00051403000c41c5055a01940100080c40056039015581051201c0c4084000741d41d11801c1c0c411241c10b40383d400f04e8406540010810108039201e524000400d11401c000003511801000c01898120000e0f01ca00b03100b80e0040c070f0507010203900020032000c0810714004503002000d4100c0346540420820b40d4854800e078440f00100360180020310980c2886001c80d401003102480104002c040e80d01d0210340c52078891078100c0c038280000c05480c1c0d4a02e035003420354041c8002a841131207400d005144d0b20301807401003001e2291640003885003200013a00043d54541400c1c08990180460886908644 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 323070332 1250 323069082 323069113
    0x250203121606050f010f051c0204020d0f0b03011a09070e150c0d140f0f0c01020c1f020301030209130303091704090e01020c0d1b05030a0518030a02030a03030e0c03 72
    0x241c00300c1c00d071425800e00c80400c1d4040c0900105074101d4202070fa103001110708002c03c105030b40b40d1108045000c0d820710700b009005656544010b088012046500103200c1c021006c03040103844100c000301d03100c1c4e40f403d80e8160701c5c09528000042150400c48800e503540c0d48d08803095035044104084203410085440f10200e00c51500c1e4010000346041008071445010841c2040311460103d00308540500b106020228599100030003511000d00010304603400d101d600071a40e030890700a0f915228190f801101c5040002d094800b1b0101c0d0344e200c4e02e030154030b19030458004c41c40c800300c0600104105a281181c1c0c0081c98072a43c040c44030181c0c400c00c1d000d03030107041101030b40b0140c1081c05003581907440c1808444041c0814800c490b56604140040c0c680d400c0401c0b825114a010b214a400140380100d58220002d4000d20080c40b0040c40e603241d071502d5020f410000d420440c4400d1039103000768011079900d40940c0c0c0019407003540c10703814503001c00d070000c0c0c2c00b03c00c80c00c000000d814a0b40502c00e010101d00d0b0b024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 323071582 1250 323070332 323070367
    0x503070f050d09050316030303020f0c10050f07050f030106080c091c0b06220f1808040f0e01060e0d02010e030a0302030408060c040b0a050a0e270a0225020312 70
    0x80c0583d0b584500e86803104100360311b640005402e00b000c050300c00400c10002c2d00903000303041d200090f42551403c0402c85001d140c00e15050f892501081c60361402000f2006441488040c0c10941c0c0d460014141070b10000e503000c1d075100600600052000c04000203c1c8200c44a007220381c001005800f55040d614038001d4440404e4000c1c0b0200c4900080200051107428000b100031113041c841c0b007042c04c0300d00507400d046000b4008030132144d00080d1155259400d01320303001a002c040f10300c10803500e640e40c1d00e802d9182d0138884d8290002c08100307034101c2c0100895980107440a41e40c20342103d00140100c0325200581ea10141d040c00c40ba018000d00003030806141e008405481101c07882d03001c1c0c0e60a40c0c1d4842000c82c6910940c016032000000910480d80781502c108080c00e5210311030300303100d44070184000c005104000a20080d640704c4801c0c0f280c0015a40a00c1c00903600484542c03070035418199040c0d6400a020054042107682c0003810741a4004d660701001024000407038890380341d5450010100c074900c5074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 323072832 1250 323071582 323071603
    0x270515030403020d0e060706150306050c0a080703020909010b090f09090703060f09050601060c0f0501060b0307022505010e0f040501140306180a17090a0801150b030c03010e040503070f05 82
    0x5008004204052500811041c5c143d00001049246030642c10354540004000401c10300050204400011001421600c1840d00800c0c81441917038941d2501d4000400003040100b0002c20140103210000300742d01c40003980740c152a030340002c5039140c1c6c0841c4d01051300d84803e40c6065034440008801c3c440412800700d040c4d002d890103204240042c10300b02d03121703000b0703201001e10082c00c9500500041010328412094454041e00c15050b04035045402e4684900752541c9400c00d04031620004240010107804105202811a06010401c03070070083c0304c0d110841c21868400c990600400640311980c50760349111419a2040080c810060303540c4800d001a07a2440078038a103030280c414040403070070741e0814881000b0201c000700010700042180f03503101b161885407810340454510f002c3c8048003041d40c0707180711400900141000042e214040300380000001d40a540450034603c1c080080c0282c0750500c204030380c1501c0c49109240480c2d140e03440d00d18a0f51164540140850380e40c0401401081004601902c40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 323074082 1250 323072832 323072837
    0x406031b0f0506040e060111030a08060f1212090402221d09030913020403051b0103060906180b0a0e190501050405010608041b050a06020a21270515030403 68
    0xa060300d4240e21591540705000d442e0340b007002840200700b100c48850940341c0c440010315000c800c5000f0f13034040b185990040456080460000c00c10090305090aa056607031003201251481035105c00075000302e031510105403c414211000264140707058485804440c01eaa074042031868640080c440c1511b0505054000c5040e029184400d06c00c07140805e1051902401094014500e007a45d128100220380d000c02e848050b00503000c0c40000040351017400b20b0052180940344206c0c044655078001000c44145030000b2525618058050101619124403180542c02c4501d00151751080351000a0f50f020481d44003d020800c004200041103000d410910103820030b403c01844180d032603c0402069030b00074041c0c0000108503400041c007142c07a0f880300c40c0c0e800e40045454800d841d101c00c040303004603105801200c09179000061810400c010440b0b07001006840c500c41046150b1a014000d01d03003004240803189802c07141c840c0c14070442e401c0c18084010b20000704011b29500003a210b100841c1c0045500364003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 323075332 1250 323074082 323074133
    0xf010f0c0b15181503030403021507020a0f060c14010501150507210f02010e06011215150801090219030812070504231e090112060905030c010204080d0507050604120509040603 77
    0x4c050030300009031020b0700e80c002c004620b007900e000c100c01001d422828050364000032400c400500004800031502c040d007a990b41e101c400d000181069000d076455034a4042a41c0c1c5014010400b009040c1c00c80908040302e4640940e8494140c2808050003110b82c91401207101003c1e40803070f05a4100c1340d21130b10200c21303400903c01254a443c1003a2074400911034001a0108110740400040e151003001802d1104c0001c0004d04c4803680340d13000c0540340c0310341240d030250703540701440c1056180041811032800e404400d040324031415640ca080319401360030000005051480701003114640900181c1d0081c4c81207030003284c00d58522000000c2035400284055000e0203611011940e40d50480f1001080400d02401c80382d0aa441d01d0002022425000d03c1510f07100e5070754012100044082c00140554a80000056241c5040c904a10f003800d59038801c5134144001084980005070780414459130054001e04d6040100703102c0b5009440510582e1441c40d40186810300200400400c0700f043c0f254400154003200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 323076582 1250 323075332 323075371
    0xf14031e010905010b0301050409081c020d0f02190c1e051e0c0d03140918060f0102150c130302060a030609050a09030219050312010807050f010f0c0b1518 68
    0xb4101c602c00e01504181c4c2400f00010300803030074543c00030703140c2c035100e020510305d02480e102503100c0c0c3e401d140c000000c015800140c00c41c41c070156806000b01c0074400801c11460040130000348610070341a80c400c2814030803800403140912912000407040040e6000006071441318500d001c0b912503980000340f03440c00d9540201010003010000340d2a0007000040c0c03544004c000240c03001e40700118500601c01d0319002c200411041c940f2001c2103001141d4a0450250480c00d24a00b00300022074040d03591070440d84504a09034424010208458011041031012580e4002c086e0200d00103404541000e500a0b10020b05c407070319a941136015408461041e4410041034445508800a6079001123001e80168008070701902c44082c441d8000705a9440b41d001c50f80383c1074000c0c020b0000d8184c26440127529030072041c02080301c0e00b080c030408600c4003024a802e036045140e00d074028103015070700d01c40900030712058000076864198140d005050000020046282c4200c05c0b424900707441030844505904030221164034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 323077832 1250 323076582 323076599
    0x6190305030d0608012304020d060e0d0206100e0705160512072102010b010207050925110c101205070212190908060103050604080a020111040b0301050907080609070f14031e01 77
    0x486c1c00741d001e421040f00e80700ca07002c0024600300c1c4001a1070241e942d9031080a284420050250b920005030058591031900704160303088001c082d0b1003804910064002c105100b83d01034220780043c02080c00d0a407090070f080c00c2c918034081080038000001c0c80005110030920414802d80040d0180c1d440c4884c0d80c0c0820544100e00b81c601400b003003405648028000c2c040e524188103095808034140c0c4814560340701030005119602d03801c02c500c1000c21051305580903812024044903011040079103006141c4101010000d2240700100c00300c0d900640d031140481caa0a10034072080d04107011082c001a16000189030301d500700c915245030b80002c07407503e100000302183d012030407a040341d4010703028066a6a0f00d8599042c2c5600400005c8110755842d80c03080807001c1c120f8007510182016055290310f0350b040c0b905212216101902c80f0042c00402d030700f0081e440e690004103e52080e6140b0b046683d0450300d04040d04c1c14044000a0181c0360001310821030308901c3c0310012201c007440050245071590780c42104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 323079082 1250 323077832 323077871
    0x30f0d0510080c06090301020d0516022404030c080d0c030e1009110f01020f0708060115080610031e1b080105010c050a11150d150501030b03030306190305030d060801 73
    0x22403800e0340003d02001007500d04003002d80320700d45026002503d0900040000c038121001140c4190880d007000c0802c00c2125810444014145852000310410500d1300c54150400100100001d040003901c0b072540c0204000707a000e49040d0540d00b1030138001c20f05e801d9000742c0030f8a08200c008240e813003140f801c4079403c174150080c003003155001085d074140307006482c0034801d40001010401c0c1c154811007074442c102e0282080314000411000c80070740025410282c040310801d240310300e031000300304140051018030741d582c12034038031041c41a04000503542038500350810790382510986a0401841c014580170203444400319070030001410343d542a0160380b00c0d0010b6418014506001d00300d40d210001042c00201c9600340742060320f800802c18403000604040041c40c039405601854603c0340c54001a4008aa031141c0e5600a0301c02428140900302e10000403959034000188458810140c06109410f4559913500400103580c201085d43c3e580c41075611081c02401c458411202c940d131a00b00e01d2241107031103c08 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 323080332 1250 323079082 323079089
    0x607200415180b1210020315011d0405070306150306050f03160e0903190f11070b1c02070c030b071d0603010905040317071d04020c2a03030f0d0510 65
    0x20340d04104056003240c4001015140103c5401c031114012101540c0d00070000800e00160203800940d80c1d150003401b0804a003203016000b810710022030810309101d44128860310301070805440c00101a80c80c000110b02401c1180d0181090300403904000388905e5060f0800429144140c5c0e0745040c04c0b03c200203160382e0b4440c0c250113840a03071602030203000181908200b142c104000104507400c200400307004000c0d001020100501180030301c407640d00c1007500524108148040480a00756240c41c020000443c0e2084c024034000a00343d940c24901e0001d0b441e41035901207034000217001070841d245d20303000e54904400c0e03400401207104020511100e20306204500f01844e0050043e03415646070410f240094a0b000d0b100700c00340502c41801400f18000d0b1a9040d1040c0659035503a001e8004e03102400c0135060600044a020f00d00400c1404024400010b14420110b00761620104428034004e260f0140700b2000c81940d81404001020802010140d01520761901144400c220603110f6911041d00b030072042c030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 323081582 1250 323080332 323080349
    0xc11060916050d030201060302061305040b0d020f010509010306081606090b030603030703080910090803060a052b150e0c040b030a0215180d12020d020d08150607200415 74
    0xa00740294100600c03c070000e64444e00012803403d4903a030004907290448002d2180500c1400010840b514181c010702d201b085c001d6034248034003503250b004a60700440c0d070b0b001c49050210020305010b05034800d0303001100829034139068841c4c494001f02018085070352880b40e180016202031020628140c043c086901941c402002545040401d079401e4540722001424400e250040d000c0011007890366024081200d0701c10021140e80e451b2500400441c00030701d40205004841d940c00090341c450004c451031030702c0e480b1451103050303204051420050303100d01156003400c4181018803030000d41100141d0070041d00303411282840810500c0c0140b5581e0001d07544003a5219003100e680c0c000300c2e0308440040414807481c800031040303101190041240e1421008040742d02610855a02c03100613414081c030b044c2e110281c405009146c440350002444040041c6ca41702a003400911003411603515901150809540075100c142425040e00402c4040d0b11000800c60003075003080c0a40550040318030200d07041c4c40070352 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 323082832 1250 323081582 323081623
    0x140601060903030f030b03030307020f01050108070f05041d031602010311090112050c0c0a05070f060929070b090c030c1f030902040609020c100f020702090a0b040f0c110609 76
    0x60f101240c83c141d280300c504050581e51503040d019510180300131480f400c8550010500d10b0900214642101c070305a01c01002d40d04402401d0141120010700441211800c54002c9942c100c0082810000000d1540d0b40c001b03480001400c1310004610884000c10380e000762010000e81d0030481c6000e034544200181580000d1407401002e4259a040c1d00081e0411003502081c0d08042c041d032242032602c0c0360307503000342d507954014a8104030b1841c2030001c038400f80c403507441c200380810303e8000310212086950901600c00b2491652402080e04603406489140390000c2030105903042101000d0388900b5020010f030f000f409499214085418030101000c01c40a4002c0711704409440000e08900510840404a90190303c60a00013900e69060010b84007080c0302b00080c000c04d0200d24440400c485210341c0001d0000c3c0180190409a038902101c10741c481d1094001280b03003024200001e005003180145100c0b8249007540411100d6405804204444aaa0102c50654460720002590340380d0a031400864082070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 323084082 1250 323082832 323082839
    0x6150603060918030c01021b010903020a14011113080c01030b010806100c0b090127050a020409030315090b011701050307170a15051005091b03130f0b041406010609 72
    0xd000600c0e8043d007401c8500c0110030003280d400e41142d001d01c128403100d039008691503100d042074100c0300419005c3c030341c0200484452075902948480a240021344032246a40303161810f09802c0d08440c0f49051200c41655440310312401c640c901d202940034410070351060b00704469455000344240d20001105842e224510f0b61782ca4104040364010144940810a8507422800012402c0d8891401440c9410022544558102d0790003110300101c041065111180d00169010602c0401c0f040039840e01a10003141c2820f02e400c003035002d4041e41ea44500d100030300da00002603815696014001440c826079a041d9110080c5802c400030304000c2c01400d0349604030b40c3d41009289405011610200345580940c2c0c031406c226110740d49022212204014a10b0b200c808116440440b07544800c0078250458942e2910304000c1012203c4c034030000007520b43c0200000c0400c00b040c11000710048a40da1001815003510b4462612120310705042c2c40480d40b5030114031940294031000305059040e2400d559901007068238 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 323085332 1250 323084082 323084089
    0x19080703090b0f0a0908030c0702010e010f080c31050301050c0c190501110a0e09130317040201180b070c09090201081501180321051926070c050615060306 68
    0x360464004c3c41e602c100420004100d0b030040e41c03048009002c003d031180300e0b60002504022a0400e600d04021007d0400c2320345503040018150400d40d900785103900c1c1e101c0d881c4074240841c80680c0101110801101440b01c220030403007070100340c1c0d01c107500901c000d40700d0010410083c0604120001c107500b05c851549007a51203070f80d04052a5010b2000030803043c48108594201c0e0303011082d000001801070250190b40d0518060543c0c1080c1908241642d84c003003928010100c20140c0e072201540180d5101140c00c1d60310617568441c2c502ca46484451020795690000425580000412501a4541540010b40e42c2980c498820529010386405d0981d9a48120500100a510010b01e050041c0d40e81c005210804615500014601c207c113803200010180450561902d84091603d08100302081280c075110455480c80180c8251800c28011010482d900419900c403009031140e4540000c50400040d15404090403c035180108181c0d6400d88a220f01c100a118548801e9500950100045201410b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 323086582 1250 323085332 323085361
    0xa17090d08090a09090c1d0c040302100212030c04060e0303160f1e061e060501090b0912030f1c02030702030406111504030f030b192919080703090b 65
    0xa00042002c4510b51301d400001c0c0441c0c1000800b5140103141160900c10f202c1510302042664210214404441c9031400031703130415101d00d00000b4003413105030201204c0580208441c3c0101c080c12161181c8030318206000c911250002d00c208000210b642c500e03042c1e941404001c540b03800041c0d26070090009650b82b40c0310310901840d581144c0c402100350940342207000c00301100708035611070280403c0505611000c04801f5403a614449407842c50300500300728907a00300424034100c40d140030345207031500285000200c0b0760307040c0c0c07030540c0036070200007140ca00c091080c00080198a032a500c0c0c2d52861404201c1d203602701e01040703810328050791003040103002840c00340d406240801c0000c812544411ba41460100c0600c10564088010540807040420065054000e8810164050705d520708214010060301814003079902c10548c038488440b07219201c104000c550b54104100b40182666298242a2076400100e504600880000c20003408102801d00c42d000f10f115039500305423501d110341c543c0c803000800d16 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 323087832 1250 323086582 323086597
    0x909030a051b0f0706031a1012020c012a050301060806060d06030210080a0b0d050a0f05011d0c09070318061509090c030204060602060c0a1b020607050a17090d08 71
    0x1141000c0b40001c88035001c120b4260302e1401c0d80d001d000038a151902c05420340d071b0b02c0300038000f840030711400e0044a40c07601c00300184600054503090700151510702d40c850091003096200400d9508200100c0d0b00d441d81d111107417800704040320720f00b0109002903104a03924082030194000182840c00826154a014005000d000d662060001144c940c6c950005801e00166400500032070141c0c403c1102e62640d40c4110b4001c5da80660300a24000a00d0340c032240c8a040788078005180c450200c604100f804003d500400321400044105580c401d003400120765214006031015100b603121000140f4094820302440340c1c1008210140e8044105030359620001e0000640755664170b1416080000360100640100300c1c40c64001d031106c41820f400c0d40103200603107900340c010000350340c40314060003468070f1350b00100c5000c2d1905140c8400e4000002c0c511605030711807180e0103940a840820a002400700200b10301c07030011320a2000c00184030600072044264010010742c07991094905004001140c1c0c00002803504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 323089082 1250 323087832 323087857
    0x3090105160c181508030a020a030311040e07020a0b070c11090402010c0501050106030f1a0102060424020d020909071706010c0507090603120207080604020a0510050705060705180909030a05 83
    0x50700e4030b4400c20310343c140401a0710314080351546103100b00d024001a103400503050000240d4680b40140c0406565415851b0307009080503640c0c40600004000c142c00c2d64081c1078485404d090074100311100075600d098150341640d01e25845808503903214016214110070960104250405401e104100111100b004000341c2c1440342580b01d21001860030b00c103080c081d25003514002003070340c0768000d00412208410240d03503203503603c2010740300c15a070006540d84e40305902052641d0185100d0407503000d80d0711803880d00341802e4004900d4140144580d0040c0c851500306407480e40c0195580c40c011514451507501c01d501414003000403441c0d5511800240da101350140341140c0c1c0069039400c1030811200b095106035590f00741520180003140c0d0602c0500000c11000e0b008003640e04103030f00000c010034028496217102c1c0e4403003d0b25081007400b600684105036004019a007151404c0000a0000da00001011344412041c0c28030240c64a0482c44481c0646001700003141007159440040d1419400404c03075101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 323090332 1250 323089082 323089103
    0x807020a050703050f240f1b030a0f0f0c0e10020106170a02180f01060e01110303100801050a0207031707110a03050a02060a0e0c0108151816020309010516 68
    0x440c4080003008011807094008120b15034171000d0381c50070400704003481d801042c111503403840ea01420b41c1c0792a4000e81801080d540715280d078001e0481c003480011260307002d110040200320600b10305034814040f201d40000103002c1014003081507000c0398082100d680101e00f51444210542c1040c421086c07880340340c0d0000003407164039940311442c1210508803000031a481810140114140b1902d4545901d400700100c010750b003017104c0600e8145d0414040c120812003100001000390784201d6207503c0170001c03101643c0e9a418044000f4840f0002401891800d40c2401c1c0450b051028520840d03051907010382c0e0b01e07500c03800040c551a010030390150581c42082501c2010b080380007030620010131038038425101c255907490911000f034140603008100340c0c41c0e070707140030320300070b2060804902180e00803801d28001c2c0d525070740c0e0b2a050b0130580340c0c0059541c200e46504d459203205001c1d0b0640c280508980e0076500381d02240c000c2c04995078070401086500054043c0b222401e40302795100011401d9208040001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 323091582 1250 323090332 323090353
    0x3040b060105130e15010306030215030405011104080a0303061403030d0b040204050301062309040201080a0c021c0216051c17040306050408041e23010c020d030c0b07090510080702 79
    0x182a25084e0080d8042a40610900c41401da018a148400c4030003070074107110b203d155800203519000099890106100c0010004040120a60007200c1e810401213040f500c59403104012940d542d64007408a01003440d200c0081a001d00050804481c514010001e620b0204c0020b000000340c01b590f80c80c1900103030280008211598207001700c04c094064418410b42400085126041803c041001c0c9801142240140000341c0da105016a40c003261032000420b0324400312100300e140502482590100620041d0100c4a0907400700c0c01c40302010172400c030b8010083d101d50803c08501d00b07621138007081e80ca0340180413001900f100780c03c41800e0b94521080341416501e40b6010f05aa0b802c42e421244514005000d00071403c03207003480e14411030340b80000c8507520304000e00418040c01c45290803450704604005028540e00ca034000c0c00c1825070280c1401504081460060800340811404a0790958031000055540381b00300c040404032080184a440c0c0c81d140010113690b070400182a807800c5010710305404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 323092832 1250 323091582 323091607
    0x9020a05180402011e020a0303020f1b0705012601090c02070f09050609090a030e061b0a06091101050a0c0206092e020f03211503120a0e0a050603040b060105 69
    0x14914038401070090750281c50144001042002d9800d007a49280001011005c0038540c0080c0c103804c00c07a41400c0040e40c5081e650b00c40c01c000d003e42d442c150305c1104c442c4004070300c00d0703000300b1000210382c020380314080403122001c4400e549202c480c43d40d41e0450000c400410141a89801c000044c0b0298019558082e46604800f01c880c0d55079040440607503143c8040c400907040c469006a4022203e40141500711300560b8010b00000ca00c1c00c98a12502c0049030005400403040e0410b08240d08100441720114510314003034000d040e1a00c1c0540c3d107528002507152842d406030301110070445492352002100100d5900700b0000b50002020b030b5800841003102c0c6d141c680c0d801c1c0c2c9032200c041c030800c945590000360590002d141041800c103000780744e00f0a0184011004180358a80d00d03410003600c1c00206076498800000c01c0c4105034000035814820401d4440350510444002d002d0761100c0d507504501d044001d41070040805003071180c280c0250742003000030302058210714610b801c450705240061420320b000050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 323094082 1250 323092832 323092849
    0x3070c050f0109050c1f030b03010e1f14060904060c02191103010609020406120914010c09062a2604060504080709060308030c031b070b0105180108070909020a05 71
    0x2500210b81d9620321200601501300001e03070603904110360101d480c02c1806030410042002500308000c1c182c64001e0052941e03029007000102c481c1d62001c0b47c2080c03507045090503040c000e40c011040071313510b46a0030900285542410501c9000d01130324002d500e0f15560ba800d401024006062005c40c0034003641040680c1e00c51a20006940c014104000b286208104041c2140c039507600c413400702c501c10041004042d800185e0390300f40c036030445000101c564060030050300d510359400ca10446c87d4a0080f41c001215088010345050703d515941c1c040015858510062410000700003490f03075482c1601d1014002000000001c084070140116080b041b035000a84003210380264000307601060010030184801d10003004840028100c00905010340303880c5448400305403201402c2c40c59441030000c002101c000c2c20440a01c032025400700044d0fa40c40c41400c04240c0181e0030b0203000d10039000125204203250190701c2050603101603038040c100a520708100c071401840392010072a0094000c9900140c9645c80414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 323095332 1250 323094082 323094103
    0x105030702071a07020102010510080c0607060b09010b070c14090c2208060a151a090303070b0f040b060910050f030c1f0305060604060e01030c0915020d0e0a0e060603070c05 76
    0xf0040d4a50140d440060309650000f04244800325480c942084800400a03460b44503040943d01180c1d95405401c140740a0501038440c60f809c404010b000140c0ca500c404000c0007910300032002c0c28903103038464091820307040300800003503030000013440440c0f02c65180c400101440401d003010300344ca01410801102003081541d00c02542a000f0204114640025015020061014101d80c0d225103080000701c156a4400340c500c44103003500171840101c907803010401c1340c3c542030b0001e841d081546411518041031107001c660481d04c00c1c1000022501d0f034106411494094079500c002104558180b40038810082d441c01807003517040c8540315141455464105a640202000802e402220b050040c00034050310805030445000d003e041104205050b40302c1c80d90780305082c0c2440d001c01c02e2070071340000311260161a08911070303903102d00c0c0303103141102e80005500240c05c030991100344000000d031041007452441c2c0e10030382c5081c03413940740098003d203800d5004540c42003031070030142da80c0405a02c0b810b02e448000c92 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 323096582 1250 323095332 323095379
    0x91003060f180b090709150e0c0c0a2a05060d050406181401050705070f030f120c0e03100501050d060203060d05030301270218010c050f010203100e130c05010503070207 74
    0x203044c4200c0761001e1103080007070411013400b44490782c0082c1082074001900c4c41401107903c401d001180c0702d215890111104080c3c11421508103aa060502060444c081d8401d064044c060307800c19140006916007003402c4070002491103081192160402014190040c82196000c0d81e811441c0c12245010041c00b84440c01484245054801105140d086410107420001400000d00c002d01c00201e0316001e002100da13051400c209111850350701a0391201e01d0420078000b080c10b01c81b25000c4140e2001c442400e00ba01241191204002540d1150440d003003801520f4120b5501601c030404100f594004503003000300500901540c0a850f1546825a002038200c404441c50f0380c0046018001010a05203032000c40311404c40c908640c030354440c14444607200c07215040c028112019414060140481c1c0b5240c84442c000359500d1424000d8080d085142e801070005203901d010109013070381c001c1d030b40802220b40d00c00304039202c55081400540c0c0c150802403d0301d007107108804010520340785010710280842c5010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 323097832 1250 323096582 323096603
    0x30f0705060105040902030303071803050303010b0a0f030b0303041e12050c090114092805040b09010c021c0c02120106030506042001020a020105090102030c06130201030b091003060f18 81
    0x914005003441d070180d10007403080c3c1c2040e41c40800b50740d01104403900100d036410704000a0300d0360201d1403ea040d0035800a403007400040f00026140e14190000c2c0000c4c11140d440341d400c44551001034040719540d1031340c02e40582c400e21013444000e07910059a0204210a1154075041e6580c035111003041d0b142d03110450b10b540001c10110450f0601010550141003248245402410702601003030310000014600b9651120031400c0142248c0a1290b0185e00c8844400074415882d050070050445c29003074503150302c51344c641100644014808140d01ca0751225244140251180d8200102c40b038002c21807007641c0c004c1d002106100e103820248221001184104081c240e240340070300b0b100ca40a1007c0c02c41e400700101007140d8541d00d81e070100320400043c2d82420403989466078180102d01d140203071140341d100c1d4410082400325070041e81f038501903104e01c01d03682840800e0005050003030012060714a03401c1e41a03804d40c1813000401c0ca03003100e00c4601c08180005441072159980a580d041142e030141c403840500d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 323099082 1250 323097832 323097847
    0x90109021201060801061706040902040504030807020c0a03050601150e060c06040606090209060d1a061305030f0a17091909050a150506040b0f040302031203012d091508030f 76
    0x40d00700c0c0c010505424105110342c940540078041399014a6110300e000f4006000590f40d07075559010583c4990041d1041000385854503020b0000d01003035a0540140c030891045d60b10034034051818005a03503016016040703e9203010031074610602c400e0481001d011000c031503e031032a2581da020302546040c5000424050800b030618108480c3c0c00d0704442e030304030b00400041046440718011036022903682500002d8440c100c0000d00b201d40d0310340010f503a00c0800060242d0002c040d00440e00140d4400b1416941e40100780c0000c81d648600c0c1c0c0340010000580d503010002d4031041c0101600035020050408090194140c80f500200c51aa41002414503078920500c04070b041184103d5030130050a071494081c0d40d00300400109a4001d6111b101280d0340c0008024a400002c02c095134003c0d68050101e030303c2e00d4900405814590802d020711a1071030954113440002400c2481e104502d0711003105031086242c2000743c100b026040703441c50050454019980011040c40400003000700c80400300e406070300d0f0f400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 323100332 1250 323099082 323099107
    0x14091209120f0a060f06030206040b03060a050a0902120109151e0f2706080303010909170a09031704050d031202120f01150206060609060310171f150911040509010902 73
    0x48005d10f02485880c201c41840103840f14421a000e41e02800c1040d07440750b48200c00034280c5145900030f41c1d00581d200600013504041c80d005860303042e040340310320f081d9aa00c0d645c0d00000c583da410725401d141741402e14104400300c008891200c0707640300c0041d20f50042c1d0301c80034200e90026150340300000380850220745040c1884101c2000001000a407010b11002d032501c0c0840303650340418041d8121050f80d801141b001c105008000650b00c8052007001368130b941c821200680300300070380e01c01904c0c0c0404003408143d1031180381003124165480104003480f414070300e45040300d45c5158400d9002a0075070820100c147d081514171014814003003600a10125810038035040a42e54030750f1300c554103540c400f00500c170207070392a4000c0c2c44803041c058442c50344940c0d0303a4000c030070090342561010161190400c0318041d0b40c107020510302c02e0020148403120744019001b242c030003141c045112960000303440b0345082c081540c80d03401c801e1154954030100c9082545500018a0034542a8007801d90280d0000f4841d10491 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 323101582 1250 323100332 323100341
    0x409051009181511090409050c0301060b03100e04060f0921050f03180a0804061d180403030905100c1106010b1c0c030f0507050c0114091209120f0a06 66
    0x2102c0c00b401150340182c0c3e81c07022a5240520820880340d521010110baa4a110a0554985000060084c040a01c880c1850760b221660484038601950074100d0105003810500101ca008051070150100c800e450704020284038240900304486054441d038000310201021300030500c2c82401800804010200400c4400c0800c542c0341441e000c1c800f0904c0440d0010300310a080d41e90100e00310182e001424001e41005080024000b4000c1c1502e2010401107101030344280c0d8110b08080700703d10021044400c00c02c224a0741e8010f4065900005c04c800010000b070710a0b040504424402d400710341118100540c61804c0d0f880d5152a2000541c0800075207a40d00000c02000c1e0062400200c540d11701780d60724110080e041004060b10003407507190003a9030040b0303100350b00c0381c201d09170100010401410415001451035120580c005915820b01910107260f0850227021402141c800000b00310032956101541c0743c0d42c2198200c1070344042c50302d0207075840400138010340316580400c0015244040c0145006000c55 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 323102832 1250 323101582 323101601
    0x218060901090c0f23131518180f0204090b0f04020408060606130801020301060801060e091005150903060c0307120c120924020a1202120604020c030409051009 70
    0x25007018041c0003115040640c038040034000c5c2c58030051510070103075500345641c10240003694950000818102d0b02030303001180c2e000c0d00d48610504802154400044400d002c032000010603400b01d004082142c10034042122400410103400810013020800b03a450890b001a406101c1194039190740480c84d203041c000d8820344400440d021410142000c8809035941c0009021900500b000101c00ca840390001c08411700800d070740030081d90f036507841740b50040146200388520030200382d0713030030000c500351402c10015481450360342440782c1c00c1860401000241006c1d00240e0240b6a81001005455141448054400c1d60303503213003003940c9042c400c2004080da06c603d8004516030b442d085410781c607180e00000100141c2420803010400ca151170604014131455080810f001e030300404203a20010310360740c0180ca0110b00f01d07114484c9140e24581903405a1050240308110306403620b0010b6032510b019405000c810380c1035000c0343c0c1410307240c1c802c0a0441d8001c0d6041c0d4000c180e581010481d10700b1501966829 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 323104082 1250 323102832 323102849
    0xa020d09030c140d050d0903020901150807050d1805070e09070e0105010e13090302060412030b01020c1e060d1506030b3d080f012c040204090218060901 67
    0x100d14503181d610a030340b00c901030382003885002c10401c00c0e680c0e214a40050301a030407200381c82894952030300141440115110482c010800d178400040d980c0140e403032240d04c1038a0394a0b8001190f1322884203c0c0e00f41c2c407181c2d5200119585000d00303c8041e044a01611400d0301c40c00040604c6403d080052400e008014a0740d1155440080203200e2282413a05081c1160400e080801c81003400e180020001003d042c10559520710701116036050540c001200780c01903010315060030b60390050400480c141c500012031240903038060742401e01c1e03900f825a02e20402c410320a11740f1440c0820b01e000522581d010000b000c910940716401c18038415898580745008000c1c49c2410404401c98038007254442c11600c030f584014411801100f44c1401c3c14080e0401d24407030140100b41e003036600c0007000e4102c5a050b25005010082c040c00800e511480c075140c007990200041803c0044140d5104603403010348020000c070b0300140c45041d010300503147c0304001e200080140000303140918060081c072000010583c000c144 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 323105332 1250 323104082 323104097
    0x11809020940021207050307030b030105130b1b0f131e0501050702221e0b060301033c05010509060402091302030f160807060f09091a030f030a020d 65
    0x502c0702c40250061096800300c0c034840320200b04860b01c84024007950080c0d4489200000401440c40ea0250040d4030411280d24100954882e80c4145403c071001201c09414136405140004003164070603140c10740c440d075105411000681c3c0c901e0b00b10080d030003100070203454031008919920034105580d0200045c2c140741580b180200020345540c42103040901c00d15044c800001001015501c80540c1c02c0303144550303e038003117072000d640c881c00c0b030b00a120110114080c0000c5000307801c04107402e8040c91945090040c076590859096440783d0407507074255004000a86a80b550a81c2c40016811025070401c921110105019034941000d90a50b10f004204410a401000030440140c2d1a0958a07400c903c0748100c44044010601c046454400700e0484060f1901c5854414108070003412a9142500d15080a8441d1203554444c1981c1504a114021001c03440011040c0290111544001d21640650300003818214060340428200004520901120b400000d604002c05804200402c0707038812500d08043d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 323106582 1250 323105332 323105389
    0x706030615020a1203020c03070203010e0c19030206070201080705070b0910060b09010f0f030b0414090c1e040c03090803240f0a0909030302040b0c0a02090f07080609060118090209 79
    0x40d01084d20f05514050550104600012032003c00a0300c8586a0140007003007180000c0030710035928022491341e64030440441209001032103860010300b08036035000d04254104003465005403200b180003043d08041020601003000442c05055202d8010b04804005d4030002001084003000d840280d0000c1a84a90420036607041d81d0340200029203100040c9402c0c0c0707a5404144040300507124001444d50b1090810100442c2201250080fa005002500841d1a01f01e02c09040c40284070035000102c4022000701e00b00c20351400c00d50816140040c0500d800501d418040d581c040c40d44d0030541c0d000703c5609140e40c81005140d100251401c10ba401114013078440ca043c0340000e103030b15405000740788201d920b6a483c070b01018080d4041d0740240449507c040e40b684820110155150b400510980c0300d0b0059a01203010000501e480c107028100325607440100c2d07600c21090013108980035201d18104840041071640304144550142c01a1105403009690303007810750b00304074119000c008200c128484032070484 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 323107832 1250 323106582 323106593
    0x2040302130614130e030409330e0901150303051209061003030507060612050d08010b070b040b0709080624121509010f0204090e010c110601060e030109050706030615020a 75
    0x24490f89003c440840c42000c0c0e40d13200501601640d009018a844007150106a20050fa0455a0001078290701306042d0449100d024000c540c00109150b80141006400d00c000907100b01d01d980d10103500d800210b6240c208000701e407078004540d807099001443c04a464540b44441c080b50316000043d5000604060030405c0300450000010706c001024880e0008481d020005260040c000605011520341959034641c2045612840c056108000040c40000041142c1250106a40c00c9540181c020241550b03190340d0304500220140200f42400388503080050318003000c10131a4800c051191f60300d84003c40e000310070020300d4400011300d80706144500241000b100c00044600c06602489442805a2210591240109030002c24601303030b13030b0000130003099502039031b0480c0304444480c20081140010052f01207550510204002a0300d40040700100f1000703226218220401c4001000004c2450711030740c509140c501103920180200b42c0307c5c00f08201141c08101042a40d503218000b03000100c00c1c541d1007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 323109082 1250 323107832 323107859
    0xc060e030a0201021903110a240612060f0e160f05030c03030304060c11060405161202030c090a0b0a03050106050108070f02060a09030504050d110306010801110906090103110409020403021306 84
    0x10440710000c0b0300c01740c05141c410001403042c20b21140583e032aa1825040c050035080e8610680c4d891806035007042e910200d0648141000ca819481404801d0030959856002800242c0a000c20f4103850b1284441448400e001e805501e0a0b0041c6e1a08560700c0c000803001c00398110740c886d074800e1700b000c07440721010745000c81241d40c090381c00000000c1318154040d042c0c0c1d5070180c080c450242072007200d04000400000150701060b05072100e44105219981c0c1514000c540c0481800a4040d049142038901d2030038038006098111104200104414502101040700c14141e070f4426034103603466400400c91340d60401c040b281c001c5030341e1410034030000e008400690b0742d82c0050320f420b41c01941c400c03124040c0f40c850001d8030081d26004003191100d449904100340711003403022082d4413900030040009108c0d00305105200507000001e0324170b801c0c002c001c0100726540c0c200641403811f050302d81d916503014000417401803000c1c003001440161610700310300502480081401400040911b00706080c80304500102d013 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 323110332 1250 323109082 323109103
    0x80411010e03030f0904090803010806041a0103110405090f0d0201020d15061b051e01050a050f06010c0b06030a0f03020a120c020604092d0606120207030f0c0602040b070c060e030a020102 82
    0x1c41c540d05d0007034a000c10000c10003120003070310351070b0f0110000ca11000c000c28014010740c021895003901e01544c210340701000c2420300c0000e214481420000c019401c01d40c101e00e5116000c4d500751402e80c0b412048040c01d1901c401c4204005035400195000404000d115403000481c0d03071002180d04a060080140001c140f46040c1f50741c0e128028140400c0040030403614260b40260799071010070039036840740180600004d461943c5590309000004a407803100047c0c00c2e1003044140d4a40380d0381449515804444200942002c0e05401000300031004101c1038041121164071a600400d54403009040c94111b03043c4840a0204208207840003c0c007582d01c1c1015134040d5a50103a0026103481d00d400301c4000089a0b4004a43c00e050060f0701c031070303ca18951703c078008172440742e11044461880c03512001c04034400c140f001800f0030205040b030b6403000e204448001d522449414010301d000d031500d0945a40d41c200481c103c51060290030203200403039200c01140c50301311040d0002d1019a0362580040e480b15180350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 323111582 1250 323110332 323110357
    0x71401050403031d150403230d05071a040302031314030c0f010c061a0109080c100804020d1b050a050303130e130c0b1207081506030a020d0c080411010e0303 69
    0x540c5004804034020140c1020f8018005c1400d0f05221881c0c4003035070000d00c02511010203004003c40303d001549500180c81070200050017820039403010030754150b0000201591504000b0307200114080200314420300480c001d0b001540c94200740e2804076540c02940d0031a0070418401c1d41501a151400a50040c0d0070000b1211080c008600e80012299150501405460641050544206131900b245820403480b0b0a07a1100002900c95001c0c0e0b965a04014803d60441d0000031020541842003040c01e8005200410520708005180c440d0b00c10042110025109c01071407010402203481c041e80c5980c0104010b03005103003400c003030030310080301d04080c1d01c92000300441c01030000d6140b114445c49040f105503c03080040d001510f4640e18145a0051030000c42a0f0540708041000da60081002900c90348265203403541e4514000184842900083c3c51010b030280c0900c04210b04640c24014001d01c0c040a659a070024605810608000c03401142c800e414030444d803400080b162400300c102d0f00940802c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 323112832 1250 323111582 323111597
    0xe030304110d0302061317071101030f180204090303090506040b10380d0e1b15031302181515250f02030105101706010f031b081b0307140105040303 65
    0x1424601d0080b03481c40071f040c00800000039850108101803146490000742a6810030001e0700c45e010050440b03040840c901001c40300905058010310b40398100380e0005100b4078010407503103550703514689030484c107603030403680e40308103500f04020004041c4802c0020207212007040b14151300248244150514649494000210a0071003485e0462601c12505c1c626000c200400001815403c4070307865205d000d1071504da05180c550040e0951034010b01107500e444921b641d19240d919155a544c07168590703110100e8000c1c00f81003c03c1241201c2c4a42c0038494001441020184000141005030400c100e041d0102040414060744000101844002099080102c0303c0700b01c5540038108100c8a500003c0025410360030082003010882d00c2c103000320101e40400085040788411907603541e4582d0700034010f184003180c1c03903070382003000c1112501c541c00c24046401851180c2a20780c0512800e00c4422045110b090010074400540b5050422681c00280303490381e40c060344242410002480d911072440080c0800420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 323114082 1250 323112832 323112871
    0x30c01111e040e060108100f2d0506040537030302212505030703020f160815070e0a15140301210c08010501090506040b03032d0702040e030304110d030206 68
    0x1081c0d06800707040d80e504142c059549d11401d99401c0c902c0048185203040140240d145400d042040d17000aa441c000c25440c00d2909013814081c1181002852049807a88014290504d1422000c901e42030030115030441d4441342103040191620f881c080d41d0150856190110107844101c00b000d4034250040e801003441001d07420071351006e01c42c1c3c201ca00034185020000d0000100350f000552800d8442c03100094130071003040400030880111540c40303802ca03941c120982c0107013103c0200180e00c1d031040c01d90400c07035641041c54001c0303423403100300f40c00c400c480b050441d100d5203540c1d4005a5003480c4040309102a49158149200da00d0716200840c070600c03c54800300d950400300480400e8660180011200070002c5603500c0c10362002034081034403020b005602c2e04020101c1400e02000316031031290721000c050000000e0349000726991b407500580d0311694030207001490041c0c1d00c0d8014408030000c070600450b100d003850b081194229211001040c45020940003040009402140c0590302c0052a034420408826 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 323115332 1250 323114082 323114101
    0xa050702130c0207050d1205031008011b08180a020603070302090607030305041a070e0931020901080106060f050d090204060806091510050f03030c01111e040e060108 73
    0x54140095210000e1a60700c001d80c0d40507406400c00a00503401c440c1010740d100d061121212020303101829002804012007212806a0003e5410500c2004245109641d48072000c0c00c545241c940c00b03001d01400c0000c4c0741c040d030f8840d5049400007052002d01842c112072491040c2d41d4415618001d0003640040001020075000b5030540781a010003409450307484219140080c01017070100c80031119007541407102201e14000d104e582d48980d02075101c0d6642015820200400b00f0001803d144d4000101c00c0b0501c9400d420340b105000f065150201020741400c0c0c1c0c41081840b00301604070700d801ea0324090003001070551005200d035811155080c01a41d0360071031450707030010f082c4d00180650032508200001a5210700001c00c1031040311017005070760008009048044c5841070998001002c84a0354605104034a0103000002001d0b00040440340f03440b8411043c2401e4901d040c1c9018080000401c0421210810520700d41e05151184407007031500e804c06c0300c08004c01c18040c0c2801e0400c100500020010700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 323116582 1250 323115332 323115337
    0x90509100906080d0201140c090d050f0304080c030c100f12060306090b0406052a090607120513120c1202040207060504060e010b0d0c09050714041401031b140a05 71
    0x7122620030b006440d210b044250781d503601140c07400c3c0150b1a01d0b50f003a00079861144144e0045030500c1d40c032403501c0f2641c0100154007440d11020b80b01d0f400b40000d41ca20040003000108000c1c03a00402411407071100008250400c03001742005401400403914420245031f0001450095550509040804c001b00c2d4078080b0040c0b43e9034000414180c0b0f000d1024052080f81c00481e445548583e40c107000c01d54940e0003144000320b480000d042e04503860800c2c64200783e118800380282c400007a00c42407c2c0142c0e515401d40c004203460721000480c170b001607200c041280c48010140a07107280807a40a142510760342e016080d18451044240b030250041c40801159581e404a4980a0700224240803504041c20504018075280400d03d9166107051345080030390401082d035640c450b8101000c0d0810a1900083c03c010346002040701c402c10040f0350004000014102c0504064402c07490b04081850042002408807803500d229501d205207101d03003400360241d01a4103130b00d881d41035158070350700e41d4000300f81a00e00d030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 323117832 1250 323116582 323116589
    0x1707080a06050138091c11030606010c11040c03060b0a02070512010b0a030b040f1703090111090d0f1704030602030a0612080a270b0309010b01030c09050910 69
    0x501480000c0014018107400143c1070383c006040d40f00c110000c407101c0c00d910525280d030342d42c0d00300841800750b0010480c10780504032803000617100448407400080c0d4520124403500040f507464494070030006d41810100300702c550000c02820a2a40ca980c55100c02890003840c02005204980700c410000318581700390403003802021410703c00c2c0d49810314140c000e03440361090700601c0d001d5103040301c00c0500401c05004400321542c014240e64034140c115100c000c00c2c0d0b40000e005640d8100410010400940b0001c40d41c08103100003803400382c503420401c00150a441168006644c0c101c004c0c0700542c95030317950444d010001c9038800000a1304003250724013080d038001c002c624405d404101090000c14441140c004622845941c40d040240540340d0860100d9903580380005003080c04203000c1d0804003401412600030b0031210301100000c242e032408a44071002803c0d0801400d921010040c07000c00002401281400242401d0500990541c880003cbc00912180728692046055401041d40045500981c4014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 323119082 1250 323117832 323117849
    0x15100b0a03020a020f0106050d031b08031306050a1a1215101703070302030406050d0e0613111210091e050f07080c090a0209040b1002010c02010c0908071707 69
    0x318042110050000e40003003104802500500311185d900703079410300c5800300f9500020942031980a507070f10304807000d444000c0c0d01214404545500008281d1038406107115003070107003004804c8075551a02400340c07040500450f01c0305003000c01000344400b109058011120007682c0310384070402010081407510100c0035148040c040d002e02844482800c64480701c00340d650313201420320f1541c9803c020ba0743d83d20a000b80500141c00a21092156500c81c00080c844850062004150504070740c031402d040640a40d102c12110800308440c0c010440406224400010121002c520400b4441d0030551212640c0206000c0503564540c18020040d1210415060715115100101c01099034a4141e80e100302d054200200d600c00c490740014480300004a808030410058041450303a1a002c4600700650040400703e68032603191f0354a104203803541500f0b84c09c0c110315030340081221400c880c00a42103803c1107100008104d4a044c0c01c0c01628400500082140c4c00c9250540b0b00201d0558260708140003a0004643c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 323120332 1250 323119082 323119087
    0x8070b060103140a0e120f0d020a1107120212061005100203040e090708070e19090c0315061e060813110a060f030c0e0d0b090c060d06032315100b 64
    0x100c41100c0e520101917141d0f420201e885030414550200c0c194054800036100441d01084040c050f10226000350103c40424280781800040103074140d8103002454210410654604414409620f0421203444915603400050059402d04401d480d900d140103004244c00b42e04600030740002580308000b241d00a1009034240b0500e4105950355584031240f0f072084407414806e07443c01040040310301d0031540c0107080052424458024030114000030b040e03800e03c1983e90103140301c00000480c51603101204d5a031340f003c8000582d54100020703145000d00d40c2c000704d20780480303104041c007401d904010240d412044a400c1440045218a0004000c0386001c240325004805000001449030700321855010244a0707842c00d1120b540c00308000c6510304114110f0070f6029410350b44000108908610058000d040101a19a5000d03520f002c20211b50080407002251607941030104203028854403241a0914030b80d042802480300c41c02090365a01d0402c60608100484a01107034080542868640040844098042c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 323121582 1250 323120332 323120341
    0x1704030803040209060108091b0a170c03010f06120807170a0c050c0d03050a08180303160e0405010302060306060c030c0a080301090c0e062b0906022508070b06010314 73
    0x54140c205aa0480c0113900c0d203004030700350358002c03011070b0301c1017a80718014801c4403a410700710070311409800c01081d003100b01e2140200340b18084240102c45d0b685a80300503c600300c0132a061500711600007220400284c6098018414200074840d1a9400341c0c10440c2c1c80c0c0c0780e81d10303410309103001d8103075411758120140c0004026402c190020800041c840c01881660159021002409040c901c102d1f0010b00050702045050144c0b805074a140b5004513248540881d54000c241071103295910030307140c001c440580c0e4203140d640c00307901042c4044c910105940621155245901180c6c1c40d000203410b05100d110089503140c1c0d807002c2001030315890351155044501964041c10706a9041d4400e00035602c1650821030f000000d84e0080500011480003d0302183c5031201c0045100b000a8102003010b4408400704040d00a001c481d00440c10024000c0d400107941d001c00b00701c40064003100300294406024040b441c803020417140c20a940c2d1f41f54001c0c050000316650000100c000340f18140c084030307840c2c0e642c13010300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 323122832 1250 323121582 323121593
    0x309040e190609021206090c06030919081e090d08161212050703020313060b010215040605070f0906050403020118180b040b010e0904110d0209040317010f0e070c170403 74
    0x3c5410a000740c980b94010340a0400c01d94943c80200c480f0aa05c0c0d0045d00340808604001004552103600a07098034030342414a1554100340628900580e603100340851082041032032202103060591290820619002004011902c04103482d50081c04c000d03c04a0b07925a0140c0b40d000c240c28583d0b001950080308030700d42c10003500c04030b50b4a115030001482c20f000611094001d1080b00e00404140d0f000c04040c040316601c960241a654403c141180110342068052450224101d13000f1845684c02096910b4401c4c0c00030100100b0f00305031820009107840400c0901e410500719019a43c0a00c0d000c02d41c8111074015104a40c09503120041800c40c00b121503c404030745a02c00c140280c0c00316001d209641400004441e038201080081d940205144041800034042c010030703101442000d4009810303010b081d00002c0c612542140c0640208105140360b443d044080c010442c094072125080050395410884070400045005000c10144036590f4040c906000c841051545420b0049042607a10350302c1e072424 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 323124082 1250 323122832 323122841
    0x1140906160305010506090d0606050604091d060c0412110d060c02070902090a09050a0e0604050a060c02190312090c0825141e03030307080f0a0e0309040e1906 70
    0xd078801d000d0390220300601c1600c240155412240002c0c207003424246218200085d403c0e8000e0200c0312582d07911000900c0c0d460704c00181c0010040c62400240059102a45101080d1030b0290400c0b41c0d001142000003682c64042664240c0d44040a21100440a8600b1401c03030710460260640c41001000c00408000598110005481c0b080c1d094401e6195107125610076406808450341e401b848105061000d036113164060303540403407091000305484a00100f56400c00200741c03800e0b200c58101150940502c034550088a880000920007023160440f8001081c5109805100040400407044a18016180150042c1103c240c104062070300081e0341d90b490750742d01c000041d414242140c40b4041c4000e9190b10039004421182000400d1052000b10310800214842d1030141c42501c44118808a00715207081010314865400d6842e0103005040000f42004400001800702e070320503003441507101ca00b26011090f078001d143d09071008620074401190240c240322484485040d20034000098405102d040d411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 323125332 1250 323124082 323124091
    0x21914070e061305010e16020304150302090a06020a030f03090201020a020316090e06041e0804170a0b01230126090d110a05030406081e04150c05070506130501140906 73
    0x260b043c0ca0280c0803d10b003003510024821641043c0706000001e03ca00711b00070031200e00c40300301d10580e0314260301c4800641da4a030003159100c00203640410310f2220740c140308045d0809041140005e00380031000d41d400410f21516502503404060700e0f0884142107900030402030041660040558103902420007000801c0e040501c07640c3c03202414007c84030030340980403811501842c1c006041d82e0348a0f00c01c1c211501003443c1c000d0225000f03034041200051001040020600c1c2c901d000000d41584407060408030000361040e00034140b05846000e8582802034003491245a2038007c0c00d2000300b41c41210465000707480d580d50041c0f250100d00e020482d00110200740f140c1c0c098000c4e00c070201074080c00c80d44541c0d6141c003403000601a40c0104420b22169004100d299408075030007140c100c1c55003032000c19420050080d6002c45070550760b14011556550107000e070503240101031810908010300c030b80b10f195036414041c000d4100000424071120a0150a401441c0381d81031101000c0c510742481700e0010b0b0784801c1240c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 323126582 1250 323125332 323125339
    0x10504050610060504090518030307020f0c0f180405030903010e1011160813050604091b030b060a08040f02060a11070b03041a0601090e0115030506030d021914070e06 73
    0x5001070180c038800103112042c3d9045030784641c2400d00305401d0ba4010100603107142d414031041203a4860307140c8108020b500c42c82c041d6000c0c0c030741c80740e208030315030f02c0c00c400c040a43d07100d0150200044543c1d201c00300202e114198400e80b0740300a4a03030741451410342c803650690030f416500302410362480c200300140d18240650300c40130410007020020040b421a0285d51a018640008000500b01144554029000e40c8000e200d42605c1c0641d01d500003841c13940a43d00240040e91940c140407000e03890303007072012024009810244400300c62080010b515100314a000014040042c0109090004603002204a241c0c0a06181c0c4d48500102d4060400402c001011106125115010840d0401c42060300c0c02168041044c0651840031084210442801000b490401801d502e000515000ca210054024014644550141007101c507000b016104014242c6000f07900c2000d5a00c22250b0001d00d1010402e00c4000c1103ca02d5a0b604d0400300324034120302503405c41c2c460f5442c04030b14203c13441466070048504a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 323127832 1250 323126582 323126593
    0xf0b0c0c12030f1305010b091006031a0604051201110f0909091f0c051201180b1203041214010606090e0f0f0402061c0f060303090509040807081605060901050405 71
    0x141d16880c0d00c41101c0d485400f0b011140815080c0c8046981000c860344624000f1a8410308440840c0c54501c01307e8801c10a0100a1000c2103220f405200d0038031480c030034103140106018241c0124010748900e00c1080d004925030b5048030f100c0a801c4d0f200d00580c400807001580c0c2d45002ba030455010b904102c20291081d03c2e0710010420030000050441c810b01002d0400c0d03d40940c4501c8007100a200d590001c0040c4001000800c01d034070340080565002c0c0400ca000444e0700032001c040002111052142140580b906056101c400c1600005440c03c41c0c200d440d413103100c840c8628002c0e941c1070314201e0162203036007003040115000d5002050402999801c52032080c0c1607880e48000600c070103003035602c003119070182408a00581030450003800103003400e40200c80c4000e03511500b541100c1c1400f13001c40e400303a0350340c0040c02096888000740c3c000703041c1111140c4040c107046c0c8800b0701c648600030b0000d2965a0000340140b00c880070070030013000c258000c002e4130850310f090f5500a01a1408585c00c490364000d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 323129082 1250 323127832 323127853
    0xc0503070f0e040b042a061d2404180e010506060f0d050403051908011a0c0d0e0a090203010b0901030f0c140d0212012402010b0108070302070f0b0c0c 66
    0x2030007085089aa500c600c10700c860b183c54441203c0b40c4405881920041d1074071014203000300e03105030803210071a841c0b20828210384c902040103000c941e0b150700c14a072020000d9140300265a40b40c1c0c43c21440e0007624100100005a00060b4583d441281d100c0301c030817000100094401055680544450061000240a01e035621020461144500030f90400c40c040c060001f507152501d82d0b4046648588241003141c43d001511218900c1c0303032000c24001002410820040c48200068005102a4440101d80909200b80d000d10103480b0100d0644c0c400c20094101e011185680d1b41100340002003131409411540c030350b11210300005c50b03406802100d011900b001490b1f22002414443c3e001d104105540f0110301c0d90038210f81e14040c0d880101030b900010b0b004e1280c102881326a80070107000340f0600410390940c42c02100804d04a43c07040e181d04040d6490030100c84002c0e604046d827940e103d0041d2400584da040249013054240b85400c001401d0348140380304112092006a0041c4641c1c02104201c68800d1403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 323130332 1250 323129082 323129099
    0x103051b0306060a03110f220e1204171029150301050f130c17070801050d140f070f0614090a120203100c050306010915090302010f02010b0303070c050307 68
    0x7400c3d1201c6810000c030400800105a0345103480d0341c3d200000f041080044c6140c1c0014100c04541103080c80b0803800419101c140c44010710900e20052a0640500b21100030b00c51860307818041d910443e00000074400a201c044002404400d500c003078210710810230449050300c130b488040c1c80c041200d1160200d40368503050a1800300d0000032035901080071680f85070b090006104d0042100110030350000603503440c601d507500050203054201009503480340070300712101b100718260b45c0000e805442402003440c0140700a48070702c01440c6a01d60081a04008070460651003460a100021001c40c180110b43c000718040341214080c03c01c440a0360307a000d0f201808006000f02c41d101b20f010455100400003410040203100b00c1d01c2e0207200380024181c6200c41e00764985802a1200070032184006600041080040c2d81c000c40844080c1c01310301c035107291441829501070543e00e44c40c040a81481400280004e40301d00c00d400c04401c03520080d090b282ca84d8014540841070b00510700130700f842401007001c04102500d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 323131582 1250 323130332 323130343
    0x3020d0f020a050723060c010515060f040306091103030309160609140d0215030108010c0801090c0e0d1b0308030124090b0f07080a121104060c0303150e0103051b03 72
    0x140c0000280036501d2170302007500c2d00952038508640740400c042c0840060b41d66000b0181c8007007086d44001103980e1030b024030f40d03181078000c1419043c400ca0303060180c524100030700c105990070b40e540708070006051041810111404000307400d00c42e80c941b0002040200c8400c011034002c0d47d5000000f41d2111203915114250351000c01401818409045000800c0c4146000d03e08021001d002901810760381c0c1d1031504c80e00c1c1c1d96000341c05c1402c650791100480000f06500500c043c1c0140144901000b8054030120000d22910b1041066403080d10350850301c4050110b515101008c032207401c805043c40d00d51f2480c000f01d49170400d2084606031400c40c00148241e403030b140d50a5840840c02c0d5194065203041c040309003160307040a1041704401d6805d000110004960200902d01c02e4981d0319244511444d04ac04082a00c250b010302e5508038005120170050260004a02076a03286c0c10b007404944502080703588854044907170b0107508440400400001400804106060500340f030340704400c25414440d05156884 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 323132832 1250 323131582 323131603
    0x203123301020d03091502030403020708060c13060e0f120a1407030c031b030c09050612010c0e0409110901031112190609081902070609050d0c0504050603100903020d0f02 75
    0x50304924050340080e413281d071008a241703100d02108074110101c84040c1c4100c1c2c20465088016a000c802c0610032814104030040e448492182014500308808100403200c2d03a442c817409041c02030700701c0f00031015034407070011001c02c00016002c074001c04030390460b09554120501003541c00d44c84009111300c0c100000f11701c01d42680e402c0a500000d40e40b941d03545003116001c0c1240744d0030701001d03004040002100008010001d00700000b004c141070030f2080420a05201d201652032160b890f00081d440807603000f030050202c2080445002070205d00c1801c0c82c21280508428071a030090500001204108001f8030700400f081d070689500401c050316840d4150380e880303c45000b000c949100e0140f0400903c8a800030f0515500c41c0c0304031030402c064800c500880f141138841e5a40581c0150340203005103503100b04214010941114501515203040d142d1035444000d80c040c5074000d0352208001540c030b0b1410410341c1d119100841e802c0040b0505401d0007920b0b18404000e0070000340d00580c040a40c00d10000e11480d14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 323134082 1250 323132832 323132837
    0x30a030f090609081e03071a011a1206100201090501020d020706051f050d0c1d04020909070e0a0c052209230f0703060503070617090102071208070203123301 69
    0x2003a40141c17902d004c000008002c07403210710003005030000154820401d5203400c080708044002c0c0d9410242546c1c0e2040d1030554442c4400c1003841404118020003910681280b4141c030903211074030311044100e0250849400150030380d03000041e0440100e40725401080420300901e01001184c4032849000d40384600c62031100070500d2404018455450404084081f4511030702013082c103982d9451080c060314103543d40250040d86a4000c03c0190b051240b14a41e01014403000303401d140e0300304243c003038620314068000d1005030b9407a10f500648601510858440c20b000311040000c58100c21080f00f454000c074010a03400508044400a6503a42c403525504658505010b007000b0b036550351100348610070000d09150805132168030001e82a1400d210340d4004c0d042c02c0d55040820401d4030344140c2c059401811103811603104200b01d82c0483e0841c912134510f02d00074900030b00e49450341c48003280356025000480715000105e4080c04500c00006180f24200c07807404d46614100013424510013200f5a660744200d01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 323135332 1250 323134082 323134093
    0x1c0207080403060c05040f08010b0f010801080a0b0405030c030424030506090f19050a0b0301050f010e061009090501121b03020109140a080d0e1e0109090c0509030a030f09060908 78
    0x3c500380c0001800c814203240050520b03681e046540c0c0e03620100e500c112110b075542e40a11609040c02c000161410100703003056025940342c080060342e83c101002000e05580c07600c201090400500b8000c0780d0010400c882140d84840d2542d4540110345c1c0361030706801d117030f040e45031802c1c2c0014082e01031944035000007080000c00ba03031003448260038408010a00382c01d046000085040c01012803060500600c01c0e4040091160800002d060840e5006410b2400c80011311004001244241014a901500a03182ea150005100300c0980e9590455000005c006081c40c0c0003241e00550380b0070071010b2500415000740b0040c0c130f5401d40324502220307020180c0081c11181060004421009107403c00d00405072041c5e50b41951600c0007800e104480e16400300140d4401c02002040c034001c00c4028504800c0100701c40940c00090000c0c1500c501c0384030356581692034000d0200581c1c0941e0035521490006000d899610030989070051001502d04c00c0c200c00b2404059011481c10b228851910546115400500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 323136582 1250 323135332 323135339
    0x304060c020d051501090f091104021c3b0d0f0c0501091a0c04151b020d05060f070908070b0c071e0501140306010203030f090c0d081c02070804 63
    0x1580459000c905981240c6400090740c00540704010000786404c801e00c1144865040c08841801d540e005042089000d00741004080407400300304210811302070441c0c1c016920144240f484005072140b400d00300d182031818400d4240c0608100c00300080b200503901e024218200c007510000c843c0350441c07e81d40309600c5001080c104078050429a02c56035064105460026560b6803103d0954004040071a4208044602511020820a1503980024010394070302e05150509950460510350600740404110f81c22180050032075090301404a101e8010b4031041c10b900d014203105a82d08030a9407190b141e403084170001088640306000c0e00c803d81e54400040c0c0035091410700f00e104543c0201d02c50344160300400c000001c004044202c01500000c000c8080110b00e8607180015000e032040b0f14001880d564204104001c907a8040112644486946403064507602e030000e80510b0303c0f440805464200d50078000410501c03c80c203010300752003141c54480328000002040ca030703000c1c1c0c010703204004c2c4100f60510051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 323137832 1250 323136582 323136587
    0x12062103020f12040f05010c0224040b040b1306090b04090e1c020709061202010c020d030c05030a090e090c0a03030828020403020301050a140115141909080f030406 72
    0x200201806441103915008030011018240b4000184203008000c00140400c003000004014000034802400c045000c07040790f8001c62006201028035119802c210b4500d0580600f200042e60040e1503091b80c1d890b00d43d41c0b07400c80c8c44a582c0c0044040700c0c44030a60000003841a2048004000340e03200d40801a04191420150744060550300102e000d8a0140600e541c4410503566042040a601540108059440c0032020000c5441540003072084141088441d00544d0308001f55081d03055060754410b4850700f060130200c40100c00c6060090040c000001c0720300c49035501017000313801d850300d001d4610001d869076131000303070b940007468000c0d600141c1449080002c40e000e070800640c0040401d0304d100f140382c40540012180c1c0124084d8400c1554046000d0096003002d1041d19400703d8480001c00ca16980c010344016103000512900d0210240303900d805a481d84034070801d18025a0360f005850301c0b020f0811203448004039124540c0c002900403a0001410100010b49030030070281c0c3c1015501e8242054400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 323139082 1250 323137832 323137889
    0x20120715060513110918070924050901020a060f05090d02010e061305071203050301030b0a021e03060a030b01151103031509101203110d0504080c0405100b070c061206 73
    0x4101150501000360552900750091009050724041b0007814038103d08003401c050b00a8001c015201c1d08a218144c802d42440050b407185162410b0003610307000f4060040b80741069200f001452036062070701040380c85480d0307004180181c0c0c1080aa8101d4a1840c1d01203089520031100c1d100641d01840c0802c0c1e4040098031511a068007036825281640d4642c59001d4600002c540124000344000004009000000515503080450714506502d032410784a0b004e010040400c92006d9100000400700d100c0d540ca00d281200255070200041d042d540e50751b001c00c5d0140500e000b000c00454540411403010050101c1164410754440d1607055131302403844240b05028600a1060046840d8003130f000c01d0010300c4084808400340700340e03a011401404080c8082c14400b1040511041c000d007400180300003000403134041c5c0700320020340c1c0014050341e079a001c001d41c01c1c203103501250400c10b000a603c0300f0310502140c01070030348041751200091504503160901c2200c8483c41404000b01124180e0501c0201314046d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 323140332 1250 323139082 323139101
    0xf021216020307080601030f0308060103141b13030809030c03070501050f180d06020a0905030d02100b130905161d040f03020c04020a09060e090108030a20120715060513 74
    0x1c4882440d114408203140280c2038000f0b0754295451023200d0304059001c0c17051507000c0c401b031a041c40258942c00c400b011800e07014040003464469541d06405c030006c80d105440c1d031008181d000c1d110082c0d6070300304110300340d10801c0503600078090303040c1011181c240025268101c0b00d041e91003501e01117007030643c0c401540000c1d0040c1510016030740100a5075850b02e803404038460280400590316864840040c142d0103850780030318005c3d04010302c0c00325516000f01da00e601c3c40404600108004540000003074500701e00e01000c04105240c5800c04052110000d00c9812400c68901200030aa8850400c440300100d110504021244142c00143c0003070000d044144d8058464011192042c555400207016a0050101400007984170342003017109551080705c8004505003654031481c0b035410000020388a10544044c0c9050003103040a48072300c0d86800380003030312061800c000d4039400398070a2002d000d6075200039030944099058401e0003102105910403031040700d50082c02c0a00f18120032aa00b17014020046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 323141582 1250 323140332 323140339
    0x6060804170c120c0c040b01020309040e07080a0503030f0c0c0c010c08160b060f0405042015030c0a0e0612071202040806040501020304022803020d02040204080d030b010f02121602 79
    0x914419042c0800980c800310780080241c0c2e07203d04244042614020b4200f0701035100354248108100103980202c1104ea18600542d00400e642204038011803405050790b00c414900d1040c0420781050001c088091401a030300d499400c03241c0e49420881c880103000c1c6036564482d41d0441110f05a6940c010003244c01c9440c0b107105210708045208820800100414400f9981861100f01b00160380c6410081c40b0000c03182140e0400180c20580c462444920401514041c130585c5000c54106545d41c510a40c054489104601642c92600a0f11392086400070705610003c035507450003184ea146004815984c10080300b6241c102e00742c0d5100c9017140d01c2d500d811880781c0d90b90f0b420400803825041c2800540d10803030040c0000b503981d04203403041c0310004101d001860540303054400304000131a210380390041100d4046802020311035681c00050000d100325800010a841100346400c642a0942c1249d20658401d80780d4a05210900781d05a8075440d580c0c1740c894100e80104034041c02e544400342c40e103580c0c60014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 323142832 1250 323141582 323141587
    0x60e01031203020a2f1212040b040c05210d11030703200102131d01030c0612020d14041205031018060306020a0917030f04150309290a0606080417 64
    0x1584202c14540450810340c4080c030280c904d00c1d8042400c00482d45544d44000c3c40520f0307d50782e0200c0300f81016002d00f0080903005503501103402e000c070100b40417000d86002401400c20481038200e12010f0310740502003c00c18015001c0120b42e6501525041d1a41511980910f113454825030341250042c0c4a01e801e6090703500c48101c0712980c04424401340031052030540034030050b0750804441c0d621200031920038103071010030701e00140300003241b00f10a9412195941845c0004140d11039181d006802140f2003109150710704015607034407003c400445401203014000111101941a40454141c4022550440c48480203e400c0080010301c00c144008800e1b10031000600c01d4481d03a4240680e440001100c0010f101c1c07a400380100b003540300802c07188008180096107418404040500b02e401680318101c50b00d46442c1d8110764aa000b500400e80650b8485003d454042e589802c110250001040301024000307040300107070450350681b080c0d000740e84068413002c004e07585958800c000007952000310410080103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 323144082 1250 323142832 323142857
    0x111030a091b080307030908010501060f08040c03020904060b101715030309030109082203150b01110105090d0e030a0b0402061b07060203040329011701150810060e01031203020a 78
    0xa03810b030780203003a04102850f0b480404c0c1c1030081140714283c12003c8164900f5004004090300128498011161418009a40d50b514202840c3c40034450780301070342082d0003100700702c20400d0030341c0246a0180100c42c174408a020b1000121004400003c42c018803c0d1800042125081c0601a0000394100102140c2c60548030390042400e480f41781c1d104444007030011540c0a484607034181c100e04514110881c0700841455038861441c03115054442850b00c50340c8014400484e4854481c00e480103030134170028000c5040003c04182e5502605a904000503460035190300a07150101e00035100540005030b4600c0c2e511160204680c0f80e220310500c1c407001c460391041c00c903841c506000000c0240304a4000d10f4846143d410140d041401c95502420400706a40c1c40f08100340d1940c04450540c2c010444504480781d1041040f030050044250b00201c10410f0301c80040c0c4030800241d419580e801d12103007440805d80c0d611818800c2c0c01b00780002440140d8040004034030621960144c00000e0407407900d03d000b810f5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 323145332 1250 323144082 323144123
    0x90f06030f030714150403121a030115060201060501030209150313050706020a053d020f0c03040f0503010507050f0a030b0a1205070b0c070314010b03011e05090111030a09 75
    0x400032045584d02401c0b650b0354248841840304205102c08595032980e0707440c003543c0080c486029a540d00e400a60b40c1c81e42c620182c3d1007400b1403002032401900270840301c400b1101c1107240404a101d80c000642c208000031407907500c240240c0c0c600a40c0501452440c0c802340d10724040c0c64100604600038012003900c150045601005800000c04440d005072603200a10304026041c0f03201500f13a4a00071103442c0c08054900c03002055210705001d603100c4070210140c090503480c007a100b00c001c3d2503080e910108680244002c0070009000f186c1c02c010071400c085a445092509a800450702c04000c11004e1109000c9420440010300360140075260028100c84032078005604200650030060004c82c901307404400b041002c1051030b000d408124055818003600d1040306560385c04c0c0c0e003c002c06502c00001030710540c2109400400743d6081c002c0c001e0111440c1c0e101c1180c0080c1180701140c041c9030078080410240031041c401c0d18101901200381d145140e0b100c24200000d055400400c490803e884004c600b02001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 323146582 1250 323145332 323145337
    0x1905060313020a0f03060608061006081008060a0b040506040c170408070b27070312050c0a0606060206060a090c05030112110904031806092d090c050d0f0902090f06030f03 75
    0x11326403d2120a0608600300300c8100c0345c0580101c2802e40c4004103004c81190505d0071a000c55041d45005401c43e41c0f40409007180302280da016654611400d401d006410500d40c0010500240650302048941e490908000554031003164100101c3d00c1010ba600548808100440e405170040a100d880c040c3c1580d039610306400c04803510101030700364140c031502e501086a01400003443d404000c0c6902d031305603210007041c0c03a1140242c0701071100000d080c451005c000e00c40d0700c0c0e149802c51000c00100d035448901030f4a134041122010321401c00d545020450030807500c81c408000c2c2c41540da1038116800c1c88400c4d19481c2c4e81003001e0b9854100b07c00006095660703103030710306d1046c2d229a940c034000c04486984060b080790790750030131002d1101510ac188040f10b401000d0209548810341e900c440000e440c5500d600d40000d03034214001003410070480f451b0660308480242600d9030514000c0014031580800c0404072411260000e600984403004140041d6102005907041000203050303600600301c021880d0f1655 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 323147832 1250 323146582 323146589
    0x61e07050a0b22021302180307090b031204080d08060d05030703030c081501020c0621040305030603101e110c03040e04060e0601061b0f120305090c1905060313020a 72
    0x304011001c1160440c440c030035515500c9403d50148000c9401607001a0042c0c0e04403102010860740800d000109078205411207590710300c0681500c44450b05c580381080642101c16026019224041c5919550090300c800c82e001c40d04410068004001c90f4801184c48440180c0300507440305007211000c0200b607041c401488000c0c0301ea00c0c006803051703140001a0031801d00030324418200c1c3e003803503100c1041d980104540d041140c0881e0202d80d545103c00000450801c8c240d1210f942e081c80500308420590400002c1d030140320304500300e0f4002e00c8401c2045040c0c0d035181030144480020400e10700c2103144d6030b802108015070244041418108500700301d9103550803e5000311030140000080c0400c2c0016071103031b8503110381d82401910942d81420401b0f0a62159407201c052100701e200031000510030303814042600d89a1203c0714410061a58900402512060310311140500861180704428505008200300d01828170030200c0300741c0d02d03080400c145034000801201400078240001c0006a4500100c400078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 323149082 1250 323147832 323147843
    0x1517040f050a150e010e160e041a09030a1107050a1e0b030a0b0112050c090d080405150912060402011b140102071a0109060f0b0705031b010c03150302061e07050a 71
    0x50701401c844c084c2540e402c41c0004569400c0b11002902014200a46605a440c1c1400300107550f01e0f9407400181031103028103c90141045002441800080800140105500366071640c40064211100c191907900c1c2d8820751f0760112100c441000150803c1c0701d0300f83c1c0150075413518003016903104082070541e8011540019002d945400440341507070080a41c3c05005140c030303002c104a11b8886642c0c045842590350241c4104903255100c01000004e81c22a030180801400b802c0406070a050401ca4940084030f80c24801d0007a40300b00c541c5600000389091040d901652641814048200004400510503100380d9004080c544940d0442c4001d000031301c41184141904990100707010322030400179006800c620321541c204030b42005540035040c83c0000355a0b02c1e820071603a40006103800c034076620401d0704151001440702404015640306500c0001802c1c640d8a06000703038850700641511a090038003000358448030900c0b4044400c60309084804c0c20f0341c2140b2001c0c0c5020500e440d80c07441c060590004494 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 323150332 1250 323149082 323149091
    0xb16140c0d0c061b120806120102070506100803030f16120e030702010f0203031603020904181b09021e0d06080303010b031012081204030320041517040f050a15 70
    0x264802d01310311032052043c0c0c0b003021111166442c48400d1898056031400c000250740412016614800d004089036105802190fa5845600c2d02a8403a0300c00c50fa034802c01d000b0020005407610000c030840b4030170442e41c01602001c0d51000b00004880c00c80e004c101d410085040c81172a0f80c84c480d84612450404204000c50311004036100060a4006052100045420074410b00050345c2c041208950034100d036040250301d540b00354010900030010805070310312426000000d1020b004501e049602d291006d820080340c49503c814080c400c2c0c1c8240c00607030102001802020010280038000b4040300c1980f078202050040e500c0c00c40c1440c0d9002038101a494403800010b008203007040c4075083e0000c085000d80844041910385481c103140c003600030013940143e540b500140400d4801d601072041601c080052503602d0f401c4e00340410b00c0ea00240a4078a100c65a5404401c201d0f00541d030104240da0f080b1501600c40d561542d60850280305e054084510748641500c0f81c00140780158200811f40c0558000203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 323151582 1250 323150332 323150339
    0x530011107122d050706181505130602130e0103080c0c1503160e03100c030f0b0603040210020c04020708120f1605090a050402070803010503070b16140c0d0c 69
    0x96080114031040302071040280d4035010a0b0010403900b54109558030703e4209034600c801050740c00d403144180007480781d8640b2041c070b1601c1c454810b000504601510b090b11301250b21102007400c440d020307901c06c540400016943c10004042c2d40003032a00f081d6100c1c82c041c0c07071982d4542400d422a02a00200e40070721000c942030741d02074010420301c3c1c1038100c00c41d10310308241800c00800000d484094250f800180002a81e4030405000b640a618645006011104100c0740d10b03c0c038000614040141e000024140011206103202c0e5003e000c6440000030701031895a100c0380e0030071500c0c000b403d02c40301c290b002c1d00c00c920007076039035501c0500441030240c51071a50b039022038110a002c05500034480c7d071007503064505201040c440780c603141e8129101c50034482e607a5074030703640001c1441142da40303c05d601034000900b04041040c42800f45048450640c102d90710030342c071000100702d81d00a05600c00c000f040b4000404000c1601d2041404100d0411002d480700098503e010886810788008141c601820100040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 323152832 1250 323151582 323151593
    0xc04090c110d02061e010609090f150b090111010e0309010c03110303190c1719180c0312050a0e0d0c0306051e010614090f030c09041b0603060530011107 67
    0x714842c11740e45031034111640c10004081c086018a00404410665961781c4200400a030790004203100401c0201000040d030f640c1a49107107622003a8400d0000382d802c80301c01d0407110140a04801c400b0300c3c4014605204451004440b01c0c414100242d0401400da6003500340140305100460050040443c02c11440c46440074034416607880006d01c2c001c001448a030210341c40101c404503074105000882e20204103000004000c050b0110401004801c94000e06110410512108580c1240d00c561081104a1140c80bc1620310703001d140400000700c2c448e0000507449181c40d25915228502c1a14603410746612500e4175821204212100001c07004408031105100b0500b110301d034010302103403074411040e0100300c0c080c40c501c2c010420254011001c01700d44040945e014828200c41403130103001980507141c28149041544240410341118051542c004109288a40621020365901404c3d00074040381c444010001282221a0400f1124941d001c008501400303011b40914412450130140d1a0b80850521 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 323154082 1250 323152832 323152861
    0x108010c05031317090a0b090f0301060e07030f1d01020913060b0d02130321080c12150f060a031a040b0a05101b060c020f060c04090c110d0206 63
    0x22003041c400184100019445961548240c407940314075491010f0405101c1d00da41c50142d5000141d008040910100300c1007600c0c006404100d204079813500400c09410103050881e0941d02445030060200400188c0d014000d030004040314429480020b0503680c2464000c072500903181086c01240d40000f03111809284c0764085600002c0c1c5404100300103480d00c90564400d02c070b541c45003c07649402003416111040400844030041d9000b501d8034080402042c5080b13000607a55214002245494010540c100b0b01941900c50410400001040b1502d806515000c1032a01201c680d0344044586050202901d4030300240c10800019200490f04810b03240044000c072108049107800f461a00415101d50380d20f0204481c02c0300c1003039440c000743d60601042203810346503154020803014241c0511104018540c1e004c7c03011107603da400c0e91205185140f58a4580c4010346100c81d01510034041400101143d90100740c007400582170020030b90b01848512405c0034040ea0310040944c001400304403a801c00c0d60750 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 323155332 1250 323154082 323154101
    0x6030c020706050418060f0e011d0402090a0504061e0c0e03010902030a030806030a080427020a200a1401050117030c0d03150305060a0c0f0509010c0209101805010801 73
    0x81c0005508000000b0554015846080841c81220341050145010359000c0c00c040c080400c0241803280d1607a40f06e9001040078800c00d401a03032894044071200815407a918000c56000f055060151a0011218041c20014200b42c9002d6510359806159001208000b050a114510089807031201e03000050711108048421b5806641041c602c500165130101d094a4410742c14140310b4003e88409000c0703403074501141c900500035100000c000c81c400044014030514500354594a0071050b405603084c0003070303000318147c14011520050550783c001e240042000c40c219940703411140703100c2d42c586a4140c4100480901c5a150b552800140200003075080b481d03210700401d400840c5001d40001e4003035925513030790010304105503481c00041132001c800310301d03600196001000c6510600b0400005c90042440c140305c000411008032754251132030300600903075082000503107401004083d66020300030b44602c000c0c0f8011800d401d039030b40030680421420714a41c0c8840311354000121907041241250031942501c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 323156582 1250 323155332 323155337
    0x7020f01090c0b030703020910110601090c0509090a0e030706020c06090c03070b09011e030e010b0a051c1401050f01080d020102132105070621020306030312090c041506030c 76
    0xa0320100400c80380c007848011604001203c5030b407985c580d00200c009001e01211154081c040c9400d030700d4402d40c012813859001010070140e07002030341c5c1c41c680360040300d900d11141e0000c5002408004050314040502e164018000d0002244180c48a8401400c5500c0100304840c09580810b29841ca58002c0280355804042c5000412510712a000000d81c2e17003a0310710032020301a100003001580d691003007451030148c1c8214510100c58460701d000103400307090000d035103500350b618100d151b00705854114001d6044950192002c0c0700b5207000541c00c0d1011000000603142d03050142c8800080d03810034414a4422042c81b00380e00603035410b119040e8107100c201003580045a0043c00380300340074000710604008403000c9080711002c46410012240103c8e4844101500d14001c407003000403007c0c0c102040500d07502590081030285030840320a0812408296007031a0164000c0c080b0312408145150f940340c1001920049906103008180040c0c15203600b014038403802c02c0c0d01c2108104070b5805d0300071010041500d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 323157832 1250 323156582 323156591
    0x915020a020a12022b080709051c03181d0a090209220219051908060406050718091a01170f060a0b0309010603031407030504050f0a120b07020f01 64
    0x2410080d5500c0420401a1449036a240758642c1107008010300740001d441040501141d00c04c1405c1600d2200300c0d00040300c04503203c240010646807054108005a4400500c882443e40f040440c00d0b5a4800d9800114180700c8245e520f1000307142110880c070020303d40c440e01012041c001c0481780c031602c1c00207001c2d2000070307081128140047c1d44e05003049a216101c181e1654035420801c0c109034407005194800b94116010040c0c600000800030b4480c03040c3e8400f0381d4900c0088400c901d02d10511006442185c5554011350042400900690800ca030003c14a20788614900c1812401c0191159598469880c1c00d40e10000700548548400c2441490381e0242006150040c80c2c0c0ca40c0740c0e000c074009140310600b00800d800550300c2e075075181c100c8024041d2090240e40381c1c0b030b0180c20760307008011900003500130030340d810070804175888680121182c3c90f60558485007814606002c1c030006003808200030340e01004240000c5040751030030099803100750241004010900b1300e00006401c00543d4800b004041c0d060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 323159082 1250 323157832 323157847
    0x15080f0106210f06020409020c06040308160c1101020123090706080408090f1c0b040c0e040515090102161121030a05090303040e010f090c021605010e030705060a03091502 75
    0xc411040c0b00e080d0002106024520949004002440f458118494607440800c2c07400001c031000900c40d00c00c034425160881c80d07449503a403d581e045201200301000440d40404100014103640011400c004180004181000103134010504001e030300004102c1030b0003180410000800c1081250020151824264075500b0252901e0121307104581046026100740c40043e945625040798410803500c0c00285044044507a15050903d0390f01075070b00740e0702c0340c01400c1c01049043c00200094000c550013001818840d00c8400450302d000c80003491240c00355403c3c414a40705010aa0a80b5030491095011100360010081000509000c0c0580340d05184040010640524000800c5030000d0744182001a292030400000030b1031442641c01c0000f80714200400007681c01030090300c003415244486c00078418200c0d600002c0741e0340c088001c90848540080b10701040395502542e00c040e0007440c09415250090b0300c0e10081040f60f4404584400001d82d07900d0698144480310005450350b00320190298034040c04c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 323160332 1250 323159082 323159129
    0x180f0f030216031211250509090c0a0e0705070506010603051f050112091b080607110109051f090b070e18190b0d1e060606081e0a15080f0106 62
    0x50007081201030000300b96805c814418200b001148514080c003050250544101841e1003118580c07003154007030848a000f0889000011440940c50407000d0f29021003a4070b848400b084544019100e101880b80070071403000454021300506010300600e40300400d0342d09002c4103044480c0c41c41041c00c0711026100106204503a40016600a03c081020700865039840500700200455521012201d076185c100350001400b0f0004125503109a0203034035541c441d0f080403002c040c00e0703c914a900521640101c2c0c6032000c0206016407a000340c400c408000603115026036140790160006803599008140c2c5815800d02c1c1e0b00c0c000810080c58104413404882d1402c00c501c10b000082035101c0c00c0c0c5625615540d82c407502c2c0c1c607582c2c0d208010075000f05100c3e02d920140031050803a082c4030f01c42558280c3c1800703008a10a0b00a003080c42c01100b051b0041c4540100e044d4050001c08000742c40c00e0b440c81c0e1154400d107420501c2054850142c500500034040076450000c0c00b80c01c54004c0c1c0c0c004608d8461300007401c2034000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 323161582 1250 323160332 323160353
    0x3150605090c03190507020325020109061b0206030c16030206010503120a08010b0304061b0f030b0d030f031e11090301061d240d0f02031002090f0103180f0f03021603 73
    0x4c03101303c01107001d440e2074000341e0541c042c80000301c881940b000da6146542c807100780c140c40c00900030b0700d078890b4481d121701c1c040b5104603412107510b101c1d0f004c1034480401800d01c2ca0085504c00008822542000030704400c0782248520103009400580c000390045c40103180030320400b80d40d2481c0c070040a2502002c0100940701e40b44c144a0952148000300c00034007401001d811501c1d01c400341391a03455051b222520701416410804c01d48100003803805a40988c203042a031003648190703400d0b440302da0806041802c120003801000314070103980c0c0c03100505291803100340d000b4808a85200302c10315440700b031042c080c10300311101580300d00c403412440791002c43e54201040c050303031300300940d807013400301c070319120801450442040304900d5006420454900107000807080c9150b03040b807084042d14004940c1c1140d0030141c1c003520324055400001d5000c80c840d0341d800381c1d01103e02c00c000c66441e40340c580402d490382c147c2c0040818003038607844c0b0000566010154140000480440b00f200c00703114050540d261201c148 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 323162832 1250 323161582 323161621
    0x60403232a040915020708041701090314030a060911120606030402010f050d0e03040e0414010c05090d0203070e0a050709080f0a08071a010906050a0603051306020a0903150605090c03 80
    0x119070302c3c4500000d000c02c046030101200c50340d0405550326041d500e0441101c0c0d21034456207000d018600c00b40d15050b4818041c8042007a01542d40c0101c4620602c00070003a50b1002d4184400152340d10000150361906006040c040c4c0750300e0800da6100d448141820080c02402009284103002c108100300041c0e801441280c0500d4080c0f500e10b4403982d07098000d1004100c10b81c540300842c8004100080c164845c2d091140c03140e4400d0b034611190030b12101000f826502c101c10300b100490000c0c007a1798480e0404090102a2600081c2203d440959603034103000c0c2c884068440702501619401017103c0300780c00010410080480900901c40e0700c440c000123036151000c6000040c0720047c001902010300c404c0d1001c050080e036040c1c90505c3c155030341d188803a00800c602e100e240d01841ca1400700240321030181c810705100b124003989482000c1e52540d5840025070101040d01c00b442016000480440e410a000c84091090300c00c0001c0e5090500041046005d0000c1030181c1030a410000c100c6500450781e408101c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 323164082 1250 323162832 323162839
    0x102120f0322140109150207030906030e0114040506010608061806010e0a0e0907031b06050409180b040305040914040206070b04031b08030a0513021e060403232a 71
    0x15115036051000940c408640103000c980030105043c824030b9065101c0030b400e0380304040b044092241207009006900401e80050702003422480e080240070300a402107100c1d85098000020080c3e0900342d00191504141c03410f0356143d20148c0140b080540000c2c8194014008880e40c15a280c00c002c00b20141000042c000d03410041d0300c0c0d548908a4031a09401005400180c0544c0d015140040b50140da401062200740c465000028a003110781d0b4000007202d00b03580303091341d0b194540790518010030094000c0c1050918000e281840050214050105580c0500c0c0309a075015036031072806217801e09039040e08104000c405d400341c042c0401a5a04012619441d901022442496586003070513508040350035171700320a2280c4c0c40380c02800c1110160055200e144501420020390310f40018810055080080081d001000c2e40320b1102d08500b855840e0b40040c0707008109920340b03501ca82d5400f10301190718061400c00000d0310110100d59200b403091004c902c4076403e54400c0741d044084042110f10070303226603134007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 323165332 1250 323164082 323164111
    0x303030109110403080c1b040b01140708040803030c0414040506060a1d090901020904293304090506032a04020706020c07031407030c090b190806060102120f03 70
    0x4005500400e83e00110f4001600a484001c3d1502050321010240b44012006100c0c0180d000d540c5044d11900070a010103a4408400899540d00302c1505d0740182d1059130204030521001441c001e007000114802d81c4810b0480d500c962602c02d48480701080c104d1100d101d18205030400a0380d1b11070340c0603601940040d1400340c40c0c100c2e5580c10401000c0803040100d0700065818100700701d10780150014481054143c40c1000f90a0780c1c0c0b00038440e0502d031121172084907c4140311040043c03512030310b441510b482c03568404d182d030700d2061300c9140780c4090801008600c00020508020707260062003038903032004080e4003401c5019030b007882c1500c1080070441c02030b83c000c10b000d01c2120540c80d2541904c1400d030b40300d1030856440c8503418071107a59462500c41117420624119800d10564800b0075060201c2e60300012812086003017065070703c040c01039031051a401085290181a4a102182c408402806505c1c00b6100508200000a0800a04110800c64140200728080e031805980301160b6002500c140d1412 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 323166582 1250 323165332 323165351
    0xa050d0203180f1c051e0a0203030405060307021501060c0b09061303030c05090306010b071101021902041802030616020706050c0304090903021f021815030f09032208010b01020c0303030109 83
    0x5900c8500810300410480d20307242c1e00000c01c10300064081d40b8500d20161402d900070392124144d03485a000d00300a400d5000bc0c84104260308142e0003442d080030300c900581d80740c0c850030000d86081a100364084000207603e28000810f10911690003900602081c0161800b40780c41c11105901c803400c208000e04150b5112142c0b20881e02c9501914682800241a6411941d403005219a542c10100059412000c241c0f481c0300650700025400009224400005075166015001c000c018020700324809080c0180f00c07028030041e601031100a100f0040e910881581511540f0001d28010b200d41022041c400100104041d901d0000306a4040341d200c3c00707012880b1481ca00d000c078101213200b192800480c030301e0b0061501503581c64000d48401348a0742880002522850101700200c400c03810350960f59030003003000c2040c2c0d0068143d0103502440b550220307440c0c1074103200b0981055000c049420812461402c050062030341c00c3c018040c000b10244010501c01c0c0042c000652170348018410341c101940e0315070410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 323167832 1250 323166582 323166589
    0x302030909330105040f06020a020f0109061b020402070221100e0727060f0e070804020901090c09030203030d020c12090907050c010b10210e06060d05010f05090a050d0203180f 77
    0x85d806000d41a990000480d0394400281d5140300c030f02e07402c0744a141d4001e080920b65100b403604408680096990303103400340c11405090751401c004007040c0e80164003040500096150074160300104051421980c0c89204035100590812203041c9581040505000350060341da180011140165100726001052511040c0b440700c046240300c40e10540210b04208001400103a8161443c086400304e5091051755596a01c0848180b401228000d502142c290018014054990320910301112682040704480e601e039000a4038503007000d140c070140c0b15000a10b489583d4024410350070004d05448a4a08080700800007940b028001840c404c1048400b0942c20340c1907009401101c201710000d060101c1d0743e10038071070081c112019441042c3d000b502e00203071200418201e102e0452420f11440c0071b001c0304d44034107082022840c815041560159200c0000e03541103046441464002c1040100a040c4c882c0d40745442400c0014401420045d90801c0c4501000c0e440300402d52210140b08484c03ea0f90b216418002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 323169082 1250 323167832 323167837
    0x5120106030605041b14090c0a0c05150117010b0904110a0b0a0503040309062105060120010207141603030f0c320d12050a020403050a0302030909330105 67
    0xd01040d09050501041c0318517030303a991680a85e0049041441d40e243c030303100c030703d00c0711480c150390f03004940311000482d058041805440100440d02d092000039503103486092901d80d440b83c509000b0046a0010819443c507405d14595040202d40240400740c1c401300024111080100301a101c83c5610780b0007001d96841102c050040c0506241e416110414854028005c0d0000c4600703d011841c0000013151447c015030111f06c980c490960503ca00c100039900c0d400251001410a5042c40785007100c40424020030810443c0b0413140034001604c0d2111420031480599000c0602c1901d030f003002d00d660822641340304c110f00940c0d40505210081d803240700d81c2143e103245010006450b100758843c042c40c95a20186080000030302c00b0000480c003138442080c041c7c90791055100500802c0d5009045220305603203402083d4840c45103180117061594948406d400e110304e140040f001a000018980600e141201d610307600304100b481001003030901d02c07c151120070100561420481c2c20b410420100b030784140304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 323170332 1250 323169082 323169089
    0xc05180f031f0b0904020d02130b0409050f0d05070c09020f07060218041d0a03080603010e1903030606030b06030402040e160f031a0c03061207050409080d0b0f0a05120106 75
    0x8a94001030651004201c600301c0b0030440c04407a040090ba40b405180c21360100d4090b036002404410f5001c0d40303500300b1941c90046180c00303d485460382144440c84e9910701c94007003114050b60103000e083c00c04186203810101d10414900c12300c5014400304020881d01d481d04020749a40040c010f030386107903040b00301106000300c000080c8000e000007400c6084d50076010074010400c000351014484450300c0800d410031000c0350007400700f140d800742005002091182040c03070f4100300090000508402036006441c10f001201c1503442d510784403180305404056042c41000010051403500300800c1e0400400140f2600c400350010384900c0d16480c1c2e00d45008024049640e040c0450071488003165500d2079007000864103840152041450078090300010051b0001c41481101c2c05001586035544003000c001900103400d8002e441440f52400c0460300752141d202d00f00d256405416940e881e0b81f6030b04481015250050251409020190400f01e965200c0c10542d100b601c0e02115250f01740e00b514a500d5004141660 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 323171582 1250 323170332 323170339
    0xc0f0715180b0603060c090f0d170304030f0201020306010c0201030207050c090f0a1109030d0807020f030a02060f0a14040209070c1a04120507050d05090a090212190c05180f 76
    0x846108002100c1501c00c850944108030704042070380d80f00c0030940c0350481191900c0c000b450402245100b40380c07800b4000c0550744020543c0c001d004403916801c00d00a400c103941c2c001031000105020a25412008200400d18280300941ca0342c034201d00001e0082c10b0103400203060640114081040000034816442d485901525110084c0f5015150000cc20030035a003103040b20f440c00c12000018003200049030b810010244c000c00c482100d02c00122022840100003a08600075603401c886013000c140003d0403c1200340d4010000f80c1008403040301c03080d02c040d10102501d4a48102201605050741c240c541c403a804031104a4103903075107042909d03100700e10703074004045454070030381910b41603142c1d00a0350041d401284010f030416891081134079107100f6010003400720b5100302d490800c500e101784001c0c801d44d40090460a861951100000181d80120a151941300402410001544100700c10841d02078841d00701401608644d180140c02031094400c2070851808071858040192989154011503a1029 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 323172832 1250 323171582 323171591
    0x33f030901053d121209050607080318010204120c050a15080f0a02130303020106090507050c0a08030a14160e01090f090207060b09091510150c0609120e01080a050c0f0715 75
    0xa103802144400d05501c6500850b102c01d20201e61f0341030a000340c41c8815806082c0c0c6d451511744042c0c2804450001e50200346943d000c0000ac07414600030504240614440d02d07503035100504020400c1b04070841030b0040e81e103001580340101c441c140d206141941007100031800c1d00c60f54035000219000f92090030101c0c1d20603414800000105617055000c00200c0e2311a11007000741e500da0700b0089440e4400d0b402d03e40d54950003a16284080b41c0b404009540200c001013001505500c3e000458800034822108007800060324240d0141141e00b00e03602c40f06511003448c200389924140f848502d000c800c039014aa8041c1d42c0031a20700d042195603030004070080b0006201034103516085154503627411808200c2000b403000000451440809840000d040d03821000850100d6030320034504a442444062060358100d1311034190001007900f08648085045140d95016030b5803107110009001080003a10009003185008200064046d1034010f482e032503010481441d40e0f80c4040d08029440c030410384001ca1000303141 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 323174082 1250 323172832 323172869
    0x20705060a02100e0a1208070e0a0b19020c0102030421050f0d021902030c0d03032307030e0312040b0402010c06060806011403030702033f030901053d 66
    0x5503c95210b800000b051044100000e04140c6540102500a0a0103221900c40d50700c50b02800308540c1c4901c2c5072070b00420342050000014208071071540644458007000030528114005881d00c18803441d103900060505011080c0005e64a1145104d1414014210841107610030141c0018441d110f4001d8119442540c6184d00c40380c440800c8803088026204030303488000c001c1d122036200c2903526002800361104016000c140312400008203012400c06640e004010b04d040a0189454201140040c1d042d1880c5055417000e41107030710039004510503600601840d54000096607880e80d00903401060b03050306407103038401a81c00103a1000024041c1d410440d002c180e0820004985040b103d5032171014480520741d0040c075449104500d8040d4050b08005210003142040e00030f5402000002c8107408001030003100e130045002818400c01061000000038030001c89024020320342c11182c1252003403444401e1910007101c0e404d12039600003041c418001d1024059000e0007151000709010b04103508080710 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 323175332 1250 323174082 323174087
    0x8040b1e090601140306041a07111903180f0506071103060109051f0605030609102c0a0e0312220503091306050105070201050c07030c1206270b07020705060a 69
    0xc013401035041d43da0030741c181c80e441c41c60001074090103507420500714482d01e103440046086030768004210400307000e44082e40d101c0d4080b0402c240d540c0380d8511424103000c5c001c1d61500400c40e801006016000c509a070300706020b102c0d80c031b611140403102e08554241c1c0d500700928043d10801c105c10748080d410f014060000924134041c1d00000d1103204841511010403c0e4a44032a401c4012070240b000025014400181241010742c405030b0072070300c4c1c220600d0780c09664100300100c5100d0014a40e05c01c0a1000041c0c2d98030098031002500401c2e00c12081c071a4100c140b06d15541c81c0552040b0740340301c4403100080780300901c104203850140080300c076651000040314203001d5030782d0f48101046030155a200d246000b14036124400c0d10107032141692064540000382c2c0044855410803201d0100d20f00030003078008001517140036008001c0040911940070300307541d810854210f5485041030030b80c0e88810380d40e000b0081305140046031a594000d921801d6a220752a04900c0d002d01608a40e030000d1300052070b002000c2c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 323176582 1250 323175332 323175343
    0xb0901050c10140115020a0c0e1b0a2a05060c1602040218010e01030c08010b0f271311040501260703050907060c050d030e030c070f090e0604020108040b1e09 69
    0x148000005c445101d120035007207a07100d41d103400242c0341007100181801864107040f00d00c0c6c1c00103404001c201140f0204c8040260030761212495602050f0610700340710503005603d990700380032241c2c2400850740c1d4899458443d01d03080c00600d05d0700c2c000c100281c0180d4501074122125501c47d0007500454640400000044001031107450042c0400ea200150034040e40c8640580c0e00041c1072130b6100700a5910302010079105070840c4903054071143c0d0602200e44040d06408081e441801c00382d4201d1b840c152144140300c0c01a0401070224050350500341e000c1c80c1c80d409902160200e6500b0729280011558103112492042c1d10401c0b0600b500f2400e034180076500b81d00d500b20754014903154003a2600c20f0f41d03400094a010000b0140100340d80c00c034520401805000f94030841000e6142415645403a00d1048454203020031600706032446541c56070180300720000341c4a0740080c011105d00902860034941c0018005060080001b0300e840044800900611001c01d8140218440445140b02c141003c00d920354407503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 323177832 1250 323176582 323176589
    0x509041412070b0a0f0e0a0605070c020910050a0608011d040c0b03070206060a050a060206011a091002061603022a010f060311040c030902130b0a0302060706090308100b0901050c101401 81
    0x1504060b0401140c60051207401b020410190040c4401302440c0d03100c00140c00028618828410000203501c056110030411718801c414060350707514900d04200030041800c815400800401a0000050010f04080e9401c4413a00c080841904119074541c03908400e500d0f0240c00c100e28807a00401071190554001800d940260803c480780041c50f6122401e00126021a10a11005a01000040003407002608e080c23901011082040341c035080c01c100c0030460041d40c2d29003880060384260100701e2945c3d103907001030807103400e6450194a0a40c0084803441148815010811007984003d55008512000d40c49844004004032080c416540d490511104002815240e14001d606080c29800031600c80d21807241d140d0f9008000c0d5034580030302c0303000b10001c0c00005580f54021800c9007000c009642e683d00603007581841628085049041440c000700b903020080c01701980750354000d505100044141041d520060000e00e015900d401c1d810b80c0e400d1a102042083c02c424500c3d040e410154100340034a0141078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 323179082 1250 323177832 323177851
    0x1b070c0603090503040b040e0f15151c0c0c030e0307060c0b07030603060f0b030c06030103050303010e041104061202100201060b040b0c070e0403030608060c040b030432160f0509041412070b 83
    0x2707941c034082c195207524503030741d01160701c004122040302450410001400298110303c00c1c900000c4100c074507610842e40e2a810100200300c408070610205941300d1201030101c01c0c241d003d0a21146040300c050000c03040903400900c04910b02c000a4802c511035032000005517000f9206004e401a001420302c02040d85030400da020340604412100b20303007410b0048034101c80d400030007185168a840710b00c250344da8018001301c544101075200b260072559140038000c068100072400c44070306a800d104100c5005d00b480c40d240156410300a0401c4030a0300074068504580c0a80d101c0c43d6038058051502d820040309411406a2121000c00c0c0710034154590311400907203210208640094031101e911880c5805280715101c0b89074001c00000340081c0c3d910000500300790a1061024a0340d400c20710040d04208071003500075483c3d0141c1a00014015031031200c400803c07180d84404042c60400020071000c2c00003c0026040f4103501d40749000907441001036480c0c05d003480d5816621554149000080030307900b500d00000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 323180332 1250 323179082 323179111
    0x607060b04090c05120f030417030d02040e2e050f010203070b09060f0c1c1d03071103070f0506030a0b030a02030f0a03021002031501032d02031b070c0603090503040b040e 75
    0x21050004446ca081d000ca000110708092074518100c001c2d034003501c01d011907400103100c22001140140090005000e00301010f048601d01201c0c01052030005d52030072551100c0e6200c250710640d242d00840300580d8070903034400e503000c0f2035113005038514030940c40024010300b060381c100000e6803070202d03840e80200008030095078a5155540b0112540c0100a03400c0910b81051100c1500f00c2c8051344126500820400d5225100c1940940740d421600122000d6884804644945003146070030300c4081c01800500301c030110481d00740300c0031802038080240340b900050356680c003811a0703650400911075615402011102c420328050780d02c0e501d0300c5204800710094400d00c42000f4401903580240c0b48071b0102d801070094a0340038003004401800c0840c03205008420210210400ca054500c1103154000d00148003680d80c9c18025102098070503050003500ca80c2c0414004e0b50002178005d04110100c03600c0e41b5000c0b50420340340c145242984201e03401015400740c00034002540e440c109500612480302c0141051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 323181582 1250 323180332 323180359
    0x1e05030d0809150403030f0c0216050103020315190323151b07140102210c040303050f03041103010207141905030f0c010f020705150c090f0607060b04090c05 69
    0x81c0c0e00c1c1c205448240302a00100d440801a10b03d840155510901919010900c065140c4d0300404403202ca081007401a0080c20540ba01008800a003800619003031808600c0c0d4a402d062040b192400d107042c20f031080700c04203505240000d160320064065034020b00f030300e0040c0110540310f06980c030745400040d0300e80c0240101c1c10140c0c0150034480f0f114a0040607180f884852184602800b503100306001c845001c001140380e10714102c24070280c40210120010a44200c01d0f09528900c4800014507800e000340c020041480001d500205544140003080303174a81d140d0702c0d545800360418040e40c00c410340541c80815000240510070f9080700310817007030b01d082d142c0d8000d18811084680b00e0450010b86a9030041003001d15034807500c0003c002424044000041000b0003181d02c60981e07011103c288e46541c8036580040c032100c0d0488000e0340101358004090f162014403000718034540b000b80c50040c812500412080d0510481d6040440f42141c001d00c100081010382c50074848c48595802014040c1c100c0c00c9504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 323182832 1250 323181582 323181587
    0x91b12070b180901170c13020d2f0301080c010e01020a0b0c070c0e0439030b1b03090d03090f060e0f06060f010c0209041110121a1f091e05030d 63
    0x440d000280704010b05400c40d44682801f20f42c1c4034075100010510307400c100c20908281c282c481c0403642d03508079900b016044a00306095800d0004001c1005821300700700f00401002c000003580408061003800e003811845c1024005030700701111814068140070801d020084001100e600800819106601180b1440d07225094088002c00843c2c001307040c08840054403c00481000c00105251001c0c049041c9049904c210b4541c50f80f21940100c1d0040e20000510103183d40d40c40075904e040300e090b1043d90440c50a00d901945d070700085116001172543d2405500b0601961002c0c00050f0380c0c004200340700002d81085075590341c0c4854256121a800307640301140291078030080320740f581c010594602a06110035020000c07180400f4008440400c3c0c8504010003d80700c0c8980c5200b4044151520302c03c04907558019403e641c00e490300781150125501d1000f415540b00019003149541c03070702010440740090841a901d55000d0740101c81d403074214148910101c800c0380200f0054940c15400da481c42a00358006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 323184082 1250 323182832 323182859
    0x1d0d0f030c0806190f260604022d0619080907180506040906110403030f0203030c03070e040b12010204090f05130f030302120106030501050306091b12070b180901 71
    0x15000042520740440d43d6843e00000751081d500214050345541503540380d01403c0795245501201d4680007044a846040c0f0310640c0b440ea2500f0200e014142da89080d5000542010114100c121402c80300c401e11101d441d000b403640c0d40d0700030010b815140d0381e0040d540707003030070803003a01260f100007442e880c001650303c0002183c543e0888890100c0c0e00044040c0743c02c00030262500900e8035400a90b2101d4030004201640142c0741103c148041403650303141103003002000c0b80c1240031074105550040042c0301c84400e0140460f0345c00070241c5010401a603a1038002005080303a0751b4202e0f801841c0c01700c1140b029034190300400888a079110b04025800c82d04152038251601141d4280303800021003017400c04282d241150b42e0801d0b21038074005107407244840c01c2d0400b0800c281c0000000035610801440541410011030b600000300742c000340342e00c65000840340824000c5840035809425001a1000704480411502001c2c001a0a02645544100c00000c1801424484442c0b054010f1800003030b0a0310320101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 323185332 1250 323184082 323184101
    0x2040e0c0a17010e0307060b090f010602060402040203040203010b10051c050412030203041a01080723280905040602032707030605040c0308030403030f1a0918011d0d0f03 75
    0x406040038039000341124103520010302e41c15255280c850402c40c480701400205407442c815180007038042c400c5800d100e00144000d00762402512400c005000094001803441e80c01641203c01590fa03542c0c0b4030110340904a00d4111a03003090682403012401904500601000402d00102a440204201c40c0d107043e2181920003510314800b000701c5c0d060840c401e800a42e40b01d40180712884041e8032004241a030b02100741d01c90307004d0740c000302c03030a00074903c82c1d5036074a02071101c0c801c0040400c18458001034448407905030281303030100040c04c07041c4290380c80c0c0080001800401c004208918041c2441000307540111b40700088100076400c3d92100c00303201c1d001c1d05c6070141c0c5840100200c071b0859892900901c80034109481c003d039501000000144003600039032041d4440e07500071400200d409411801d54080c2500d441c0d1285100d21030b040c2d1615018011603004441c901c080b1445a030345a0348500600040001c20300688911000812104d00000e541036620b2076980c804a15491201c011421a5800c50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 323186582 1250 323185332 323185339
    0x109030507260409021e09011e0318060902090705040806040602090f0a06050d0b0f0f01030b06070203010c110f0714090603100f0b01030510030314030a1401060c02040e0c 75
    0x124140129800e007000321014001400c21403900312444040b0a0760f80c0055002480107900003482007801e0800d0080042c14505280c005c5040508644c001f0b0000c54140f0810050b9170796000c00303030880c14800e81101c03848130115500070081513040e0030440041e007683c038426400b400f6288089001984500204d0f402c40c1c07980c0010781038944807039454034042d40c480100c151340440204000380c5a80e5800362040b004050588566036600f40500c1601c0540c0c90900240c3e214811704115444c4984400400048400007441e0000305684540300051140c00307078000180d0198681484d0820b00354021a00c20101f19812003188c1c4a82c0c038001d02c0a81d108198041c0401030001da0031001054101050745c0e43d002207004050314100e2041d401544112220044031010949d150b0000d0b88455815208403500a03030702c1e500a5003518251307240588040c000c1c02e01070746801c200100007545042180e111445651203d218200d075542d60b81c10081140c6d0b5060b600740d1080e4600340e00e00c8050f403c0010040d00b040b04c0076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 323187832 1250 323186582 323186587
    0x1106040605031815010f080d020703050c0f04110301030f1a0709050d030507140106140a0b2d070f1401050f0610050c1023010803031b041d07030b0301090305 69
    0x8203014861020072443c540300390310070b100240c05052074980059000e48511316110800d1481d0003049440c14038146550b0041d900100018008150007040300100101d0036699042980d84400200b0000d1505441c0c0c0081240044004000c10000b03000801548e80200361588824100c9600d440980509403072041c0851441c44040109051511003255581e00034201141020b8081e101d0841502c030503060f0b0348160359288820310103024002c01c5044400c0058505240b00e80c1040b61031f94842c81840034902d007041d4456131641841581c00c00105602642d41102503e41d4100e1030100c00c60b944d820800c85000541340754603052040b051055500c1201070309101c07901e0703482e4201403054500203500b00c141000303000c1010404032901003150f21600b00202e440042e03603100c1546a100c13000c41c481d0540981d007402d1001000040c800205507074000c2407810b090300300d030781d0361030700718441c0d0b224940c800411541d20014030a081e0059070301e6a4449d4683d505c0c03d000001c031160402d42241d45044004000c10001e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 323189082 1250 323187832 323187841
    0x30a060b0f0102071809060222032d06020306060c0304060207052103030a09061d06060307050603070915090905160306150f11010f090f03020706090f1206090b0c07110604060503 78
    0xd58016081042c064480140f40104c500003404411b5140c0110581003516440108200190400160bc09400c0300d8400d11210214003284907000e0500b00c005403c094001c008584650307912000c640084035031400716035a5660381d10000c2e444142500c10540304050044132600b960035100c0721041550322000c040c40ca10790f0354400d031400409002c18265509035441c00040c0340580e4920842050950820003418103103048401c143c50b210a5800c4540900c0c0c090013401541707504008900b0903504116000c80c13580300c0d40c0307008941111056014500b20b9003000240401c052051130081c1d1401c503a69800d104040c1c503074042c2d101d031600300021100011400e00882e86080c0c82001000303000d0315248000b0a000d8070209030401a14010030041e103a0a2103030310040c0800d501040440001c01040c10004203007843c00446203001840c0c1d1065660300501c0e45440c3c800c0118a40c841c2e8070003507001d4280038145c200220b07064200d03007040200b202d25152200c1d0078234807031800b00161011a15140c0e90710b451a5079 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 323190332 1250 323189082 323189129
    0x10f030311010605090108010b1309050a030c05100f0e0c0d03050405010e01121104061d01022d0d0503060f0a0e0103300807080a0515060307020309030a060b0f010207 73
    0x15071440c11809560794400070071140d4450009500a121a000126005550f4404c200c140015160b50350650b82c94105c01134001813021880f100c10603050f0500c040c0007600c6041240c101034810710380300152460400a4140040a6480f900300b03030110800b120391009002c03061000d0911400005804545d040c80104420341c030840710180e00c401d041c505806020b500300b403044160f41c0444210706001c200800e052060340d03485130301070070405116040c0031a014446c10010b915102c0440211a94681219016101048010b0008144480350302140c421042003d00181316800035110b07107100d00403480ca0443c0700c0c988400c040090715000707110b00741903034615520440001304d40401004110307200c04c200100070708500b0f00074020034980d807642c000da880e1080c801401d24000030500c200303851410303051143d80070070700b01044c058001c00d582c401c0d982e4803800c0051b4a14010400e8a980c184a41d80360714040103c0740d0001c0100c40410744840214264400069880e1160303070064008040b112030fa070040d00e61 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 323191582 1250 323190332 323190347
    0xe01080712020d020c16031a042d02030f2b050d020a14030a0603032006151216080106090c0519050f03130515090a03050711060a12060509010f0303 65
    0x900203c010715020800e07821078140b24032100c04241200301c00c0b408000307008d286000c8038161800703110400c2d4646800e03a01c140501a4000c00c04442a441d13500b1440c00860350310301000f1640d00102280c84403e4a00801c80d5582144040130040300310340d150319980800342c0408500204044e4649071300b00a44403103500300039003064a100d002c04c03000e07041421400369048021805100588004a03c0a0650130092303c00e02d961003506a15080c42d00d80c1100c132000200340d5940241001800c282c00c03109a400040c00c2d05400703c101c01c01c0f8000d6004041003100f004c40700008450100e4001c2c0031255031852480c085589101d000400b25004008100d400c11040c24610302044d128141030f402d086210b10b107407105401c03c86110000a4228000c2e209114040005541c1645060182411490450784458991aa0110040c1448804150042082013160303405c0407407070000e030190344c0715460004000e04604a41800041461400c00086610304141200034161100700b840c800c101d51844d507080364000e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 323192832 1250 323191582 323191597
    0x4020102160e0406140702190510060609060e0607020f061c05090106091a010801150903080f03220c06181a032202061207030e071401020f060f0103140a060c08070e0108071202 77
    0x5001cae4004400c1030b22600d110b010041c002c195103440d007075070a20380c2c081d02020f801b0214038418801480b60a005a035480728480d41c1c044180c98290300c60b44460321940e120203960303020040940c00c19042003440101580480300f114940641403203611913840e4101000001058140c1c00502c1e160014003081c00042500e4140e8200e40c542941d80039602c1e2246000c035081410284500c3d0000000d00c802469003004540b106240d010305422100040c3d0f54500024101d8446c6105115207034042d1880c0300040e2464500402c901d001c0001000038044200c6810b074421900301c2065808a15010074280e00d49500c5110300740d014200d54a0603010803c41032101c3d0340240404101610b444030107482c6001880110b0007040c55084180450002500190406640d1228107800c1d511032010480d1400c00384040c01d0440e0b400c0720f0b0304000104106000e600300341403020060265401d00c12075000c5583d0105400d44a4000341c5c3d9610050001c0000440c0d4400064034841c0008444c000c410103841105e80c001c0081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 323194082 1250 323192832 323192843
    0x204030c17120c07060e09190b04060b120103031e05030c090a080a0f020103051b04051002190309150807121d1005090105010b03060d060504020102160e040614070219 73
    0x4003020b80c590428254011030100714180c102003410001c10b40c1020881910744000c5403480307070380e1500a680402003100d01824801c200c0d00c07138124286a0b1103585c022005000c0410000340d44010100400c50910340a1100f2400503107212a5412004152054035040c90419920b440c07954403100c0a03401e40b0f4000c9017410ba84070780d1211000070201010003200380355501c14501c26a00305441d000140c2114030080007030b2416604000301d008207001000403602620750440e44803c48078000c3d04200c2c82d0060300e09001a43d440d030312640b0014181c11459110881c0d42c086e00516000001700403c0320b5452003586c7d00d4000c54089041008420040c0d04048210340c0d1103900c0c80d400040b8801c3c40340c41e04080c80c142119840e43e407814041605020301845000d00209106c1903d142032040102e02075020782900a081280e03500041821a03200703010240c00c2900000020b01c4864641000c100101f2060703408803000780c6001d104441c40c180ba00480c0d03111b03403190b40142035070101c0049810001c10041c00304540 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 323195332 1250 323194082 323194093
    0x30924070c081009120804230c040b09070903021c0b010e04151e020304062a02100902030d1404050607080d0e01200a122f03010302130e01090f030e0102100204030c17 73
    0x240c48d00c261481201c101c80580080c8406090a403c1c4000c0b61200854207010300c194000b00801640c02505e00011603074181c0e0b00e0742d85038042598240400c104018000e150040fa14000940d1a1181c50441d000394041c102c0d40d0040c021004100084401d100424520300d103504894641c2d00c220b56000d90360181c002c020100341400d82060181e10007019941c04c40172044c0c00407c466200f641003240e01c1071000c80f139104100184881d00001e42c0c0704141c5500c0410021a548001c50034a40300701034900808018000c151545118034045901e1b400400800302c0180c5444000740310800b0502071007041070030004032180e082c0f0800b0750000007036101e1901c0f841070040500550004030400d10601000940000d1007480649500c0c40300402d0300e00c0c613800641c611301d0030300051004d81c8da030201d42c0c070640d80010400107040c140f942d03055026091441d006003081c48880b03510020302da00200310042d0701130245d00b070b1080703034010107452070490145010103010101001802c0c42598050308100c41e0702400c3d001160b6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 323196582 1250 323195332 323195363
    0x10e06040c110709020307030b1203030a1d1b04051509150a0b0315030610080c091021031206030309140a03140a02030601090c02030924070c081009120804 68
    0x510f8002c00c0da20040b422680041040f842c1e942c1407003050840e480854042c000d07402c03280c81c0e0329980e000c00703071012820710b95030001d050b0703d004404602c01d4030895510070303200921180d403d202c05000c2c0680180c1c3c050307420140080c0000d11020000004030500030880740c1681c0b45c002102000c2c1e104004040c3e00064008400b00301c142e0b001002d144200020001c042480c80c104041c5800c0110282481c0404071604070180030130030000c20151615442916651616543c00344030140c544030940c00b5141e8402c074080e5444410a291144021003806a100e81a4000d101c440000c2211614070025001a0403500203101c00d4aa1400041c40460024040780410343c403500c0d00c64000701108101030595000c00c1140c01141824031656004084203842005a403200e00006500e030f200300b60701c03203101e0301200c8592500418820350000015458540b1151240c0c141d1070303d080e10300d010b0b0280a0451180c0010780b040030034079028011602d0781c0b0010440d24400010801d50f60391202038021030f100c0b9441c0c201035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 323197832 1250 323196582 323196617
    0x1215250f0306090e060105040b0a0b12060f150705011506021203040602040f1502120306060304080304050a1b092a050f04050402070c030308131707150207030f0206010e010e06040c 79
    0x4541861040c0c016000c2c46d40741c00100011500d4007a8901c0c003503101ca04040140501074016100b01c00c04a2421600c01d07500e400000301e24071072a1041c0d5a0006240c0c1c44504031541c403401906041c1d2003040200030000c500c0d41700c605080c07111b220709001603125088401c46c412011014540191007540c0c0541003940310050324155161030340100c40900005081845616410402d5460701d040c421401d0703145003480804034001d4800100080d041d00b0001001ca000c200003000781021480d080040005410b0b1482c40c0f00060a030148102e142e828104088031400c25450340300030059001e4169400d520703001e642400d98094210710762070300c1821001d100000351600c0742e000410300d1a01c0303980303a0004c00d410351501420229000d403407000103d640682210010341003d41d0301e0145041d8480035511070050307103019001d41c03601846503100380d800481c41400301034102445192034986502502c15070303a242c44454000311000d201e8080c103148044081441824140c1c49603600724190f161600f150194084103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 323199082 1250 323197832 323197841
    0x27150a0b0f1b150f1b1602100315051516021503070302071a04030f1206030c03140f030307051210080615041d0705100c021215250f030609 61
    0x20109030050240c0343d10070803000140c20341c0075040460009a07400e203c42040402503003104d4600528100041640fa4912102001c20040c1d0f801040240440460761008001d0f15401e120302408685441d408680f52a04241e030581c00600c84021a00306035130480800d062460414050b6008461000c8010710761142200075446422661000f507a11121460025200c080b0034036000c0b290044542400b001a5022032200240030142c40c0001000004400c21f80007064503501c01441d40c14040000001c1006185062041c44110019202910784103140c480d01c900c8111403000014400700540c0302c0013443c4010450b0405418544017a1007a1074012080c548442034030000701c01511003a01003124501030051001102d280c0c10300440b0340480f2034499690340e6050044c580324014001301c00001c14441d003c105001600240b040f880c030100c4502c0a40c90304008408015910010800100400c2c0169024500070304000102804a8220401260402d0b02101c58604043e221113000401d050140034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 323200332 1250 323199082 323199127
    0x102281a01080a29040f080f0705010615020102130e070509040507020616092916120807030902061815030108071404090b07080703020927150a0b0f 65
    0x20407020841d81811035107402005404c0c00c075254a150900884500c0420b4560081d0b030100b0040c103590b4407444c3c100042d000e51841103084100100e04e660502c43d05400c40c0c812200d10100005012907021022400c0c0e1043c20200b0340c040f20951030400c0000100c200c8203500164078600715060001810008041d10320a88085005910010600c100c85902820070100c000843c01c1584805207400403482c2c0e0020490100c4100d200a1006042c4c1541c0c0b800c00c5484c2600643c01503444c51000e4034100003012000c5041400041104000500d0140248111004203800400c0142050b40c1583e00101d40d41c841501d441d01714031030b242030340c0c03d0f0814100918081c00708800070313040b030504003c0401440c45901414500c00e6050840c200003280d0000074040d000f003814600f0690954447c007080d0064811204e4880d005104480750101544408504400010120240809039140c000303c072041d0403c4030031802c0c5e119100800400c511200d000042940c07444030b5882e5070800d40c9910380d0494088801c0b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 323201438 1106 323200332 323200349
    0x402031b0a0b0703110601080a050c090402040207020d06021908061305041b0e01090c0513140d050307060e12180f060c030307020d030b0102281a01 65
    0xd011000e8807070000b000d9a510007610300108804c4904071030003030071b003d524000b007a820000f04000c603120340c2010080210107a07020400680380e9000d0002c036401542000144010f858914041300440e0282400580b1616010904c010f05001542c2000c20800a44208580f07961202282c504445001e4000515681c40d40780c4150030000b0501a400c5802c590078000807910310112180d8180c649408051004985c0f0344130980b41401643c400760701c80e0139002d009006120b844040242010002005200501183c0d1107103810756020a409440c40da44400d003111058038200444c2540d015044402071a09181d400b40d0f285030041c940752039100e2650f504032040956146001e440b44030f11000c2c280c965a00306400040e40d9500f08880d21004681040c0200030070b58004240340d4980d40b07041e1084086040d480e40c000f119103030134440840782e88510510446038607111001840c0608070301e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 323021582 323201438 := by
  have h0 := BRFrame.cov_init 323021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 323021582 ≤ n) (h2 : n < 323201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
