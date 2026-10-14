-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2931
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:47.153371+00:00
-- url     : https://prove2.me/submissions/29ca70ee-5320-4be3-ba0f-4f527191dc1f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 526978417 ≤ n < 527158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 526979667 1250 526978417 526978421
    0xc010609020310050604080a020f0d0209040f0605130c03021201021303080a0e120c040911030709020d0b030c0a0b0723030306030c0f0a03021306150504242a0204021c 73
    0x41c21007110510b11b0145000305260f80c0b01d01c5800000d0250484080b81f0066507110020802030680181c130031a480c0c9001c2c6045902c8036141e000c11143c19142c800480c40d1100d400903420380e0305038070000d0340300900e055130204581c034504030003c400159020441609002d88454014005500c20100c6070744940d52240c02410300d003040c9200c03500030604004002d0040310b000500940072401071360b001a0b03071030082c1008400300c0d00404509815214041c80098485503d9004101010101070100810180e4004068070341e524911119440078141c0d20501c64118240c004180c2c0911540303184c91030341c030046042e802c41820007940b403401e80c00c08410006107080611241c00c10810440e0030318602c9410000103079513000540006402900704001080d001c40695200f50090002011030143c036150340e00000302940d019015180c80c00296100704041500c1100324030f6100501c3d84c40e011074020030041300c0c10541c000c60703030303407105000c1310f8541c0c1c4016807142d100501d141c1e4013021428805003861001102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 526980917 1250 526979667 526979669
    0x190b0a0f060f06080a020a050301090209030c040e0d02070b04050d12020102071a0a0510050901120305090d050106080f210708190e01030e0a12080903120f06040f0e0c150c010609020310 81
    0xa1754010440d820078541e1103000c61307065400300c141c01622014244082898081d00100d034a41051401e20b0030741c1113050014590114601c96803c03200a00d17211a00e00c4000d0017540704261b08000d52294103400500080c06000314060544001070800c85103494040c10400d81880408400c00400c0601040d0807180c00384642c0f0a121100d04070201c2d14040100702c1d0364030144109651140c08140c500c0c101403041c0100e8400c2d07000245908d403540b600b401d2441c002c0009218101c81441401a42c0350100c2000c81c0d41071808111172560581101901024030705a440407504468051080110698406540f07001c4030400310140c0d03030491039164070000542145c1010b050f00305154030a83e00030300020030704083c1046176151450f10748180d890b142000d92950107412000d1040d1402d0f60704000316460031140c660b1244c10125030a00c03030344542c0100d02040382c4140c014502c89070030911810b81c80d401e05020100030000601c1c406440c2001000c941c0303003150f0702e90704070410498000080c03050102d0f0b4140484 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 526982167 1250 526980917 526980931
    0x3190f021c050a0504121104050612061302010e03030d0e0d0e0a050d021206070c020112090302210409140a0605182202090c0304050f190b0a0f060f0608 67
    0x41041c409158540c0810034992a08400b04840021002e16040c46803003520024078030481e014003170007000c1c80c0c522420984140340d24010f5107000b00051461800c03884503400b030f40c148406800180c0310742240e0000341d035400005030b041c001841517454094404100030300808554910000f185101d80280e0350501100003500d60402803480d46000c0c841e6a07407400c0108030342c02103520900ca00c1031440807650409640e040d4078000d000d00f07001c02c20100d80121407041400c1c804da81c1c480400030300e19002d0301111141c60300038006034000c1c9403a41da0041c047c890b41281155081c8214206030b518140d070411340e402403010032000320000003448448a032a010718005010b040362001340e860140030303503402c1c41080203091507211000540402140c03240d1124515003281c01074514519480d01180d90382059206403000c0700c0520480300e80304100b6601003026280702d11101c40102010400d40c50707003814281c0c007910084096541d000c3c550340030f28540c07003000c00034099002e40c140c94900d81140a008010010084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 526983417 1250 526982167 526982173
    0x601140408030f0c0c0604060f02011410030f02010e0618120120070c0506130e0f010e0a0207020604090603050c120105060609040e030919090606090503060a0203071103190f02 77
    0x188000d21001c02612512900400400c0d240c00c80e10034200d1812145c0110540c20810016022071030a031b0100240d030260585400910910300c0c02c41ca0604c200e13108880001104e1041c0c0024800101c41003081e001c858014940b622081d00d192000034803e0340140182107502d1885142d52015060200c0c0e00c0c404031103544001c00c0012400411000b005440400c54000c42d80000780707540402c0320181d2150043c1001502594507910880074a00e03a1610340d028a01060040d080001e0030903005d0222203040e508103e24219440c2c80c2d59078404042d4000d02e2049034031110038040401d10038203502c036010086001d440140603044000c402d0000c0d411a5031031040d80707079040208001041e00d868044482908042d10005145441c00044a0a500a85030000d034840e8108540900d4040314050a10503a84c0c00e070000c00401d03940302000d4031444120311805030903401400004000d1001d40d406558030030143d090601c00c468807098241c3c199801800780d8224540a03420401d00380b68408000b500400c4c140c002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 526984667 1250 526983417 526983419
    0x6020102090303120606070c0b0a03050105060715020d021b01050f071716050d0c03060302040f09110402070807080f1c05010b1204080919090b0d030c06020307030b0d0b06011404 78
    0x441e0301d92064100f804d540c0c500c00300c00320b81180c5480044070302d02d40e04100d01009084c2c9800c0c3c60072095100c0301e846000a070030130001203a245014022201c24541c00441450b103602d036060a5000b0790072070028120050b50078020464003000c50714001180701075010002075a032601d086032100d0507002071f2410007089144056694442d00110503242c1002e0b000c01c1031941c40304480320484031403040d2010114094244045842d100350150402d20640e4800c079001c1c0700d5220740c0000d002c102c4940440c06031050500304012007607030a10b64001c100c9280203010b0180742c210103445030704075940300821050130b030280000d03d03d41c2c5061050b54007400700c1d092a0140300c103501d0300400c01550f0042031400500a0a640086001c01c42c4910494000701c3c8090721004803d0b03111140c00c1c0d8403e042d4031410a1590910004121340e28004040c007640d5607240d1500d01c1cbc03c41141d00c42c000250801412102030560344c807580059980c80001800050748541d138015502d18241c00014042510711100344500c01c02804 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 526985917 1250 526984667 526984669
    0x90204030803010920040806090d020d14090a0824010e0c0403120207090510080f0705010816030e10091509080d18020603090321010605040b18190f0602010209 70
    0x4100da044621200700450305e981d008201c45500c3c0c0b00400021820800081c00051134903010449502c174501650541d001c45070715075000e980f03e00340c55254a001411802640d1180d02250700500300030840078080720002901d40c2d400903d4040601450540300000a070364104202010380c4140c050001c00d1454540d608005150307036050f000d1404003d1140c00f82c0860340b22458402c210100080040203030500090503c08241c0004244500420310305010f008020302c000d210004e84501103e034183d41c1c0c003083e59a4030325058410030351006000105521403200302143d017002c10a11308541000803000030070540c0341c903042c024000c2d01d0b45c0c0c0103001810b2600c1c06010a6a0105448080c004680e000c100850180340c0081000200c03400254007035404001e015076040008050040d045180803030312072807140d11070f0030130503034609100d05000184108814090060441c019100d08400021851081501880080c02004c04900300340a00100c500c010003d80320051520720090000b0b000851a00c40d0b000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 526987167 1250 526985917 526985933
    0x1518031903020a0e130204151b0f03110f01020a09060c0b1b0c030418060807030b010b0d1815060f0e040f081c0f0c080903120c0d02070b060a09020403 66
    0x4500340092650100d03031020898065919048040d1008020031031808403448054000c0d0010700401c800e02c001841a086070701e0084468111004c80311040e03100080647d0b40f80d014422090b5001c43c100000306054600b800805c101c5400e180342058005030b15003400c414000c0c40801154040f03810040070031040b0002c01c41c50042660001c2192614040104000c0303015420f612451107001d00d288400580001d0000e00500d01051001904000f88001550703824030669400941c000541140201401000300700308007401001c00340c0b802800031541401e0300400e83c0c010806408151204540c903c0141201a4103100c0c29016001982c83c0c071030a2810701544044209006000070034441000c8036081c2480600e006460f15900403101c2c084842d001031411030301412104031450402401c00701c200d683d05001d0740c0600d118000c17000046041260701140d095181c1f0000d0528240004c0812104480340028001080c81c0c5000e41e024000c00d0410780140010060715902842900b4070501051001035048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 526988417 1250 526987167 526987207
    0x1050c030415184e0b0c040b0307080406060314030304060516020d05070203100518010b06030c0702010e012102040305060c040807061227020f0f0603010620151803 72
    0x10840c20184c10741d44204841000ca40203520001d40c0e10601000c21103030500d0a61200428800c2c132000300c50352a01514440c0600590140e121602000c4c000104914410070200754031901800011440f03e0740d0b500d80c04881d1201610591290f08004108428440c56004071a044100900442c072401c1ca1408001d40b1030b002e400240041241c00206c11040d560704024110000d40d01c40000c104508148041203462604103c00c00215400c01000241c646000d0058074490b035102e4445500d0800c0f141d0046030014020221030b818060040c0712240c98910100e45850401420750005940d107003181499454494001c0900100140c1000284038255000c94410200c03403150401583c03511280f2003400c0a000d24180e96040c0580d502c00c1d400440c540040044038590007030b10030760702954050040c041100410300314a504000c0070401000b8040c403504820b06010560031080c1103452444641c0340c2410b61111403c40d0340030480c0180f040e09900030604954065108006501e001d14641c5054400800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 526989667 1250 526988417 526988459
    0x60f04030918090c080601030c060e090402040506030a0c080c03101a01030e030d0e1c0309020904021504080102070c051c0c03031206080a0f060c140403020f01050c03041518 76
    0x508140c0c15282c5070b0b103070420620198043c80c01d4910f50345440b61140d44803402d11064524605030034000440c44d02840254820b003d0152540169540e685c003071001414014000e01d4051041700b01285c04102d5590340d44d0041e004042c0034229014030a002c051038050012690341000c2d1810b803488075191501e4240700c00e800820700300494041001c1052070704600500700b40b8a0b1882c01c1040c803022011000c41c59009010707880900203032245002c80214100d5140c00750094002d03072110003140252a08051214803032245000d580e01e02a03e03004030500ba41c01588049035007500c501014440742c1b622044034100045500d00f01000a40d851702d601d84107601c24440a000d2040c480c1e89001c266165801c0200078243c1002182e4000806191a8944041100c400c0d5107252500f800420010302c201c807168102041110901d06050454081210a024030b0700e10750306100c3e0400c03081e8004c1030305101906c01800c6412200306d1201601c400030740030f40c00b00050301d904400611014840481e1111196480c40c0d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 526990917 1250 526989667 526989689
    0x60b1216170f0a0c0303030c0305060618120102070c05130e1f1d030307110c0a060e06090901230607020a15020f010218032401060f21020c060f040309 66
    0x704074005003018081c4001815074042c0040303c40c1804060342c01641103030f01c01c6d5020007560750051400c40407a101942c0d0594009402c01c0708000d000c0c0d80c1700002d80d0b1080b006142210310f004c41c0303a0050032607015060898074259900350400183c9004040c06840040900080c050381c900003001e00e448222010f41902044a80d0554181d00d600d02d602c4070244e5a03480011500520b40000500d640b500304032001000601d0000110388114408070b101c40041402800c0d000c582424960151160b0080c541d01c81d401c00e40c00d011804040e660013594500905103a280050380291244107413107054001034849000310b00400c0010b00585501e05d00740111444030201a01688101004a0506411407108000c0c0d43c00803034542070350882c0900c1500b00c0901102100d40047c07904100340070421030082040744110310f0100411400340280301e1002050314900c3c00316140494242c01505032328940d4080555140e01186402e444c00c004c1254a42101c414120b0300b04924007943d004080304210300030100c00395 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 526992167 1250 526990917 526990949
    0x7030b190f020d0902190605190509040912020f01050f06060a0e182208040b090a08030a0906030507032d0e011b23040515090d060b1216 60
    0x410380d1002044103580d910655403003500f60b642401503c020b03803099200788a00101100246801c40071801240c07510303218141080ea03d80c5041010000c4000d02d8424498100540d2040e6a501c0c23003203120451050004080e0b601403000001c1c504156100b054246030314010034429903420181040341e1144c012101c140e0b0310a07240000301e03030000c0d400c69440d81040c000702403021803000d6003610314442c1c0c10000720207070140c01303452640014009400d4013400c11a001c0205001c0110040000c000000e409010a40302a40d0307600c80510f541d0110118100040c2200c5041c0300e402d500d0b000d0a9080b920f02d01d014003401284500c02c03c00002100c2c25a80c00001409684034040010b801269100d848900200000020f80c00542c110039168861076000640380201540204680014500405070f10058141883d0504060091601103a04c0126500c0da0600480392070b40e41e200f1000500e075210780c40100b00210004280031520361140032400c2550007040030807094855441c51801181d03c0d40707120011031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 526993417 1250 526992167 526992211
    0x1030f150e010609060206190902060702090a0926221a1206010f0e01030c12180213050403020d140904020d0f05010906150e040b0a0807061202040e1303022803090807030b 75
    0x41e10030543c000303402904ed6010840c4203d580c2d4024601c1d10300030006220006501107010180d40701f80000c0c290005001c0c420401d0442c600c2d500144a040040c01520382c403074a84d0301c4602c1410160007201000240000c0e80e500e400c240b003009a070407007800e082404901c150305a001d01340c1842020b405040543d00e2100b04055841040c500c580050090001c2110406400c60801c00031142a01680a440c12880594201802c0c2c400d5912460300350f4041d141000381c4000882d41c0307a50701c40566050060500503a14603640e01d20003403860801440780000c1000d0000c904e0000c2d10300590054a00c146007500030030602da01d03500624600c00340c03031900d50072036012180004d000f0718245101d03d070032412486011a10000000d038403c280d0709151211030220031000b485006074455401015040c011187c08612011001c0c03100501151080c01900c8400c40d07150140340c03040c2c040342e0340e10030b40d4040c0c0d440390018503800c00603840151034244040c14044d07095485095003442c010382003100fa41c0001031040c0a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 526994667 1250 526993417 526993429
    0xc0a09120c09020c1e0c1509150325030e010b01181703070614040515040f170903060a050106110f070b0c030c06161b020f01030f150e010609060206190902 68
    0x1203c03c2d800d6a0f040d690105c000342550b80d9009100140181c0c0304992500c03210826106407010914020a102c000108280c1c9041c1a81c1018001c4000040000c0603444490081c004040c040d14180e41c0002c4c41d14045540039007135035040504181484041b8603030307082003a001c0d004101626250040395000c80742c5071894034034510690300043c0c91249000e1907140c018000d20107145c0603501600c03c40d0610030321440340310034000d0180e400030285802103400400040482d2454440c001d201001c0b075052000503004070341044022500030700e1050352080140f00841e000040c0b10f090041d003000401d00306210700c800c01e0740c4e40c00c9070040c0c522510b000309181313142410030022100b03148201e80a540160422000c80700210300c0c001126030120300403041458425107010755544c9041e400600509040c1c4400005400038040c4a0081403000e03280e002d02025407004d0f0780d64400611004510030311640c0340c480020041c00194006e0800c5400c400c003484001055115a0001086042c0000517424200e2001400b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 526995917 1250 526994667 526994683
    0xe010207030c15020606010801060509100318231b12191a070c02031f0f0e0303041b052202040e0a020c12040f0e09010b030102030c0a09120c09020c 65
    0x865501034401081c181c030414076030f101c4150181c0032205680c44813001915040000d0049000080081c0030301079051a0104611840300b1072410001000740da0005031680c0321100450585240e400340c4805e60b0506850b90174030b030b40900d8080140000701408040c20500e982603001c2540308203201001048496014040f95082d060803092680803022207141c840c0300c084c640e04050608650810004281c0760041140d100e205600401411207070281950060170f442401801b566025610040340c4c503124041e10500d190100080000c0d44c492a0038a0480328a041103038070140c1c580b58840041045488500c100ca03c0040d0f03881e1341145e079110400540009000700e40c82241401520400c1c4100c40001d039004104510160060303036080100c0e04200c1c6641d20a82c817802c4a042181c40080011401968480f130b00301c1881c81c0040f0321041900006800da8206881c01980214005145c1c01e405802c0a21500141012008101c0c12600d80e1241d110907200c9200e610307000c5400240e422480002400480 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 526997167 1250 526995917 526995923
    0xb1621020d24050a0f0b030709030210021b0a14011101092f0d0c050418080301090b0909010e0703061112091f020c0a060b06040f1d0f0f04030e01020703 67
    0x40010b0341401e102003401c0c42003070800048121010b0200c0c5070300b00700141400361100281049060351600c10710f031400394401042d000c200882c1c80c0010006940e029603104803005241e0061030101d4011019003440340e000c00f42c4074841c0b51149401c110021403200c602c480c089090806808000e4080c2c0c400b8090508000000c003829210190030503651520412030508068071800100000004800d04c0400c00890700c02500c0740416003800c10441c0707402d4104101c0c00404600710607010344240da800c41c050b002030300541d4110751212502d81a0307080c800350340c0f0343c4481c01e08000d1010501250100703488800ea0302001e85032a4070380c2500714481e00d150084407034032070b038002d00000c091800010481d1228021039010003603010341040c014104405009030351a0f500d0fa040034040903e080da9840380144913821105812810a00c8001000f035164200c190040c01c0104414206650170035558004c18070080c06860150000e00c1030000700101c01241907030184e4141000800c80d1034010041c0e207003641c203070310003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 526998417 1250 526997167 526997171
    0x911040c140d1b030b0d200402030103060e06100b070308041a090f06130c0b280504030501060b0705100f0f060801020c010e06061305040809060c0a0b1621020d 70
    0xd2900804507900900b0b02103c0041601d881e40502401203081d00c80130800700e548219880c0e02d9501142e10790035442c04100001da03001c0d500824080c045820380e002680180c82e066a40c810118191809110540e80000c0b515195041c03641814046041c49c01148409410840e078440058108000c05540217000b07604205202c0c2c10386803c2e04201d42d160030861605000c0d0041d50085540081025194070380f0661224402909a00b800038408041d000011038000c40782080c10b9000110303256414050030305c500740e40c5a40c1d483e81075003051400e48041c0d07032044e02c03000320411101c80131400116044d20314100081c0081031141000360500084e00c0f02e1801c0c21105440c040e0f000a4090056004140d51440d1400034010100310585141d1219811a0410313003081004885918404260307008541c443e10030941e03142400c02c4d43c4085a41500f1884425140d5840003510506001a150f0b40c640d100000e0b2044861301801342e01c0c000d003007200207401e03081c0c80c2000380c000407040180354041c0d4010103a44203003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 526999667 1250 526998417 526998427
    0x40c030207110d210c02132f070b450a1505061906020106061107140108070215040803061806030c0d0f061a130c0c080a0c0c0806010f090911040c14 65
    0x19120041c80c4486000552044119082c0f40300202050798a0340e240601d500282001040d40b5612b405040003426040101140c44001d00901c1d2a120040d0941411343d081c0150b4043e150107503002d0318840c070325200055010000d80400035000741510740c1d115a102c000410b060319035002180410150f10035030104424003880c042401030b03055000f80210b598070303070b40c0e41c01f95881692810380b5002e80303000d89104482072181c0c08003107502403403c094104e56070344100d840c00d01c850060160840317810356049400c190700005100c0d19141c040c0d101d8120360030707900a64266080c100b00003551141c01d0f540c0940945159043c41c03017030051100d8024085a00098144052602042e61341303111011380182c0751140969400c0703501000e4503440f490000c2d4100e519007600600340c82d2294242174002d203881d40c080106800d03044000070742c440c81c034100a00c00003004241d15414002a10340501c99a0081c440e280e103007030142404100050001154400300345c900140c41c0d24180000c40d140d0917079141359049200c001074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 527000917 1250 526999667 526999699
    0x15091c03020312040308150402120609060d0501020a0c020405061c240f0501030201030c0503100308031005100c060e120904051008030a0f17010302011d0609040c030207110d210c02 79
    0x11401e00c114500303038900c490047c3d505c00704000c0f805080c1c100c85140c0e940d000015040d0510804150308817000406001e10315100d80d030341e00d0991381f0100d41c5c0c0000880c1d11b80c51000b14106401216000142140e404082e19240000504105006c40025162502c500031f6a61100d024000c0744680c043ca603401403101300e5244070030300040d050a20080340000d01e00085403040502c81c1041d00c0c003480307000544004551454075400c003241c00c0580700324194004080005034a84d541c0c407103008842d1603600d80d000f803204141460b008580c6002c0368103989070044034040800b40705400441e070054100702c40002d05900c07514008147c41c5202d400c28101440001440f010b0b1940162000d8907034401d55481021414030404201b0f00072600303100c002e0110303031400394958990a4000c501101c03450043c02c03450500750741600080c01c0c4c40042500d0070229034009110001d01407584221900218150f6849810340b0081e0381d030302060b28032480008200308544528403402c03440358852200c0103800400020304144909 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 527002167 1250 527000917 527000927
    0x9021203160b180304090c0e040c030c1112071b0824010801110f0714061503010f0203280603020607200102010b011b02041e020915091c030203120403 66
    0x818140c480c180d4500005079024060416100d01030189000355080c00e24200c1d88401a110404181c0280310140c441210191990b11131000240c0f1150b40c08510ce4484c107402a0202c1040760389070354035070001c840301014003040c01c0480b41c17056403109030215000400d0044060301412500413849602402d800c2514005a000d4114041070704038803200c8080e6030b03603600182260481a090f400201c024040d0906140000e00030f003146074050551040c802c1603144109081007401c481980f0701c2e60840120162500b030911503a03250304486102140745007084030f00001140708251494100840f020380c11f07141d40b040d41e00104025a805010541c032402c042c40d211080e1251940c02018030044141c9180303403503105004a410001042c1c568411100c84140c2c0008081c0c0955002c0e0b0b0019110310b031b01e0b0303061800303981c00104214076078100584a043c24020081e0880d501100d4040400090101d075006a50709981c1102401203040d022400034058030301a800d5005681003201a154044200030501d9001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 527003417 1250 527002167 527002207
    0x20d02042903010501020a1202160f060f08060a030b06031504151b0801181103090d02010606141c0e01021204020103060b120a0209041e230112030309021203 69
    0x580740d550384600101002824002445101e005900a05a00020801201803040740e211144161400503100c1c000c1900340014541c081d10002034892020810030390f100c05031107109112440e0902c41804c040c000201030807002c2c0005025800e0010220f8242d59007048402400103c0300c09500c203524013400d044c0601d650110014000c0c600f01041d500503005504c050074500e08081c0c41e8800c1a90920070006840c40400100c445001d540702d0340c8041000b0220b0103140b0500f10800104080400300c0002400d54850b58084c03418002200300c0f10144403607030401d44181170f005442c40301c2003046050614001c1d128a03602c0ea00c0c154800100400400d0350080000c0c0b05a000381c0b401d10419507120b281100c2d92003540e10310044a10400040740d1040c029400070000d001c802080451100081000711a424148100313005c0035582d545154100f82915a6410707800c558880c0804121750f00d008800c44101561050080c10503540c0d8511808558800d1864011214544101c9455502c0e501c0c411050081c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 527004667 1250 527003417 527003459
    0x4030309020f060712120e0a0c0518060901031b150c05010506061801030513021207030b0601020a2310020d0c020120091c0501050c04050f042a03020d0204 68
    0xb190300e4071514100b07003080390300c1e00754899202508403054120403240c1c102c8001c24891010780380c08800d03490b070004100c441c1c00c8600030f54045500714684002c009100345540c0307004200d44142810000c659841d60040c84c11130303400c00c800d6410139254001c0040003480540059460440702001401e043d40d2044825400ca88201c00070015078640004018040c0100501e82d031850b43d2002122110703501c42d411090f003000d941d0f400000c1141543e0300299200c1e40642d405403465009071800c10a0007220704030150000c0c000e001401d0303907400c00e0311010000810360f40e94503403000e40403502d542d0350b1000b040104031b0045441c000315214490449207a02601c4200110300041d07007040c082d0341452207541c03816482d21109407002860400310000b80500c42044890000d081c1d90740d509820003080081c003e1502c51100c00640541da03908050400603030030515a01d181c0186e160442e40c0240e500781d05443c050030340c400700300c40f01d034851040c80c11800b9200307076541d0503551800414001102218140b2040401034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 527005917 1250 527004667 527004679
    0xc07150b010e0d02060306010e0a0504050a020703081503060103030c080d050c1e030609041205040b0c01020a1e0f0509040b0310050901060b070c09090807050115050a05240c150403030902 82
    0x10b44042002441040800069444101040800e0f02903005001004481c08040c182c0076079240d585000504a820442e00d03d404140c001922030100b6030301842242d406640518901c1c0f100360500082680c59405000040520080b40055428002c1c0402911f26070180349000f0b03c45450840c41000c455004441600060080007801203419072591044e64032900e000b8201e01580d94498440003007810701c1c00992000d0140400c4082a901d00da03400405040014200150340c424804030020302e403030100001900700e0407038a031b070308640550701000e0340d0b006800502c2c10365261020400020001c006000c3d9960303042c85110540d0039100140d80115200394150002042501e954840d892030354032844a0052426a521100717114000c106d038030207801c59000b8101c55003811141c0d0740301402c486c1c480b600b40d228860a54401c201500c0c040c24041c006e000f0940300310f4030500214100194001002e42030246880c0042511000b0b01c00801c00c2003203a00803000580081d042c1810043c00814110380c090340951 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 527007167 1250 527005917 527005937
    0x6240807050607020d110d0318060305070e010e210f010609020301150503040c09020313020a0506130e0c0702030106060908070b041419030203010516080a05011a030c07150b01 77
    0x400229092045074005440e0034645400c503820403142c00d21074402125180003a2011101c01e4035407904494000d4840d444a110000e48600042c013055000d071b020200300b41c1040100112a43d100125031840b50084c00c15618855036100050050a010703051322407481c40d040582081c40030001000740d808042d4070000c0000a44928042081c0e1009001c1c03a01c0b12082c40d00d540e640144150300956011340a2424250f070b958456031344800703a900a030b030340103a440c404400082c150326082c1c49840061200321419407a01c81004011b00d15a8810710443c01581c0d10400042c8100425000b00c8050030360040081000b00e84805001c1c080f010140222080341c0f151040215207455140d08440554450810813100c0b901e1400c10800d1880202c0072906a0b10006a000001601e09025150050398120201c0c00d100141d01d6000b00742e010300900780e12409081100400c510803090170317510000324044990303c1c0c0d65a15800c0c2c1500610031400000c2c401c041400c80600c552023982d03c03184079503009a8840c5440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 527008417 1250 527007167 527007179
    0x3030f0901090e01080a03141615150302090a0c02010e030d150f0e04120509040c0503060102121602090915090105061206270c06040312270504020d090624 68
    0x600405d0181c161658040c050210100e400755100701100b00a54070420b103880c1c20f8800102141c0034585049920714134202022400d20014010360f04105800c1e20400c910510307540000b400c100000c2d192601d06541d84940f0640c031031003900001c00503a01981229641c80c401a003104c01007015003100c851011415002041c20002d144208084071070341c03034640c00c4075117072601c0b406030f254280d00ca03440c244101040940e926480d0741c081c0203001060fa0b212561a803828400281c1130882815100790ba010041041c0304040e5204054802055010360380f40c100399171110126440c0c5410080c4032104902e81c18104052404c05412403885800c041e07c0409041e0090310101e940c58509581c01040b80f80101d6820b1540c8a4803181540020502c83c1201c141c0d606160204100f58030075041502c8048101d03998420700e54004074441144000640d1216403c440c88401c2101002c0c1c03800742510440e000200b009003daa55040b00070143e40201c030803c801a40810210314492002c00d000a00c81611a000205 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 527009667 1250 527008417 527008439
    0x60c0702090f16031a030f0721030507140c09090604050d0c0206031807150302180118090b0a0b0a17070e03071404111c0b03120d1a03030f090109 64
    0x7030000702c803c2045014019801d07005400340404c00e45402c0c44580600c400e680d0100802015100c09201600103036040c039030381d040307100400091008001c1420100368002a0310104440b02c25800442052a10b15030402e80d504114042c08040e41c00821041800340c120004a03031580940e1054049500404401c00282e60a150450020358000410b0002403540341d80d08150181d58403400c1c080d10611900d035103030400c1e11a801c80a101c0081d5010035a41c411041e6194030040d90002420a916038a40144150071020b00038001c0a40854032604401201d84a0380170020142c05507645903900c6040840c0020114901c1542c580400c00c003d1004c610001d01032010300d114800042c0c00740034014140303100c10010203484045243c005964100d298500042903000d046118241403400c20130304d410588030015103204403c031303038400e0b00304500c280780d615007040450381801c149800100c0c1d221410400300c6110b140c072003d4180c150100089586c01000200000d0007048426220302401c2c030345070301130700c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 527010917 1250 527009667 527009671
    0x5090117010b0a12021917030405030c0d05030403080f0c0703110306240f0105070501020a0f0f17060f01170708060406090204050a03060203060a03053003091e010608060c0702090f 79
    0x640c3d0b581300c0d2104e001d8200b0a001030122000c10480b0600c050f581e4080c4c501007100500d0159151708003107401d1081d0300d02440b03010400f600868543c014004161100c1e910303482284030041154000003004480d280c00d90094801c64480d0f102902c031500c0d940e04101e8040010f50102038400c0c0280c10000c1e6502e803d20030101e01e0001c0024a0741c1860200c3c03030500c8050a000045541881024004400095400d0004207207054036640c402102c3c0c6100c0e580034240848590481050000c2030307640c804a541d9540d1490b520a0088031400d45205084005850581407410342c00309008140c41003005154000d12068061682564104140c0e41c1e1003070700000324081d60040b81d0303200d110101e080000c12050740146810140090a0150240e581d0f51901c0c5000b015881c0c101e03240c042603138059140c14a240c09020080100d0207032502d14a40030482c141c4949041001c01c030455510f044810400c9803d40c0a0006452480111070f42e82c1000001c0c0c5044e6044075504034031405460001910b00002c81c280c2034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 527012167 1250 527010917 527010929
    0x114010608090709020904020715020714240709170106060e0118050609010311071406060631090c030e0c0105040612110d18050f0d0203040b0f0405090117010b0a 71
    0x1082d0181403004450107076003e80c0520764841c2d004d20559000c140744031036000c0340c01e2b60844c00580d1000140740c80403020f810400e401c2203d810007500b6204524010020203c00544242d00d1802e9a80d40e410aa44a041c50303002014100f0810380801e040d064154060b0058a0903038a440203038044540c01143c52030803110316003101c401c03500410420340c240f00014001c1e514050401113907100e00c42407840c3d91908004015500c59004205020010b01d0a000654201d0380c20b4035414500010301c0c00d1680d01d041c42880303020750140d00130441c440090138280f600024054488003071010410300b003c018080c11070350250070441c2c02088080b002ca5030127182110708942e21522507259640d4009a00c02c02020300d0030401d1401c1504000da440300100e18441c410032141c1d01c6003010000310075424064945040d82211030125442401000701c0c440c0c000080e80c00300d41550a500e50781d00c1c41d040d2131040c0c40c00385030b2040e500001c00314000302d0103810f48480000042e1420000700f02c008a20b0782040518011b40c8103407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 527013417 1250 527012167 527012173
    0x8070b0406030509070504020c0d14040b03070806192715060c0501060305030409060315111803151005010206100f090c03090203060c0d0c030608060a02030702070f08011401060809 79
    0x10007000d4000e820580c3e0080b0007405641ca075607074500201e01603a1007040101103c1e00b0199103140c1d0b95401401080d2200c4142c05090b0501c0d040c081020000e2101501300400e002544c2c0016415a51301c2ca800d503541001c82030040041070341c503a1250b510b04403243c2c900340100c170568074420341c0510320702c11059003440d0a98140c2c00d9900d003140a607100e080c06042540c0e207540f1210b012022550400050000307001e0040c00180300c624600b0065244a145000071007014100306504031510404025180040703803240540000c0c40c506400280b4200e00d06105440c4111104108045421642400003c41c2e000780c0a6031aa69580070b0042c100c008280580e0300c8151200d4010300400078182d003ea40044810b050009600d0300d590002483c007407048a48501140c0006020142020a8080c4191410f000c0c01e0512045040011080c0c03945030060500d00c0d40c6501000043c1014801c114490007010401c0385051b05c9912125454007034030304448100c1e41c08091100026809104101b0306105801d11005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 527014667 1250 527013417 527013419
    0x71d0306010911120403020607030501051008040816140304080d1b1203090501050f041e0c170a02060d050a1d0a030c030909060b13080a020a1208040e0c031008070b04 73
    0x107440200f491039403407000c0f09404e0001c401c4050480d0b0700b050196004e90000c103104e203041940103058176030503005113008201c400024042e0700e0300140b009801643c801d007150b031540c2c0d01b80e000c403000c1094244040c144403020b03200350118032000300c0103105481103413003583c1030064410010b40d034118030058a10002e80b48000b005000c12050b101c00c032200c0c141c600d0b0120703000c0710303079100c4c1c07801c0d00c00503142c00100401c03c0c001d1008012413000e2101204a0f92a2412030071000780c0c45030001e0303039461301c1010b40c0c0900a004001c00d854003849050007441e4001c001c15120140400308400400d421210208102c0c580388901c140916040060880e2640b040c2c010140c0e40c400380d078100e640707820389182207040c4403c0b411f0228036490035015103c09044140740f0543c4400426801d003192500c1c03944103400701d0300034032000d4016890b811003410582d074841c1000c4a01c0d03a807030315203006248039507402000b080940c2414008420b44410040d405100a1110fa408141e2200b031101e4503010248104000e113202000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 527015917 1250 527014667 527014679
    0x90a14040605121506150301080c011112090603150406061d090c0912010605041e230c25032007061b020d0210080106110f0309010507110d050105071d030601 69
    0x4081507001744041c0a220304890400c28440c82500281c000c0b008981000071203080c0b65074840c10303184040840000400507100e600c201030307203144210203455024110001c002032400c01c8048000c00c580038042c000700220b5507511001090700315820407100514020081c500d101d8502008c0c074502a1031fa41049501d4080d4040c1080340d882407424500d403040d501d4000c0003865550380e22602e800308242c035100843e42c0600400000031600c10080c4040a50743c10b01290107200c2070308864540c440d842c2032030150780742d01d282007a010303219922018241984145241604140c0e00003050754400510402e0704501c0c0920284580d19003c1c54010200040e6100000641c02c40e041d141400c6640d001500700403202c0180e40101e070017044c0c01d100d65000b02d40128010484c8a5021984150165000d4007800000d20101907103503c0c9d10079501d420703040280114068041c42110400c08034040002003528403401c01c18a0a2400307400102d91480200d444c000e4507003006400c0b907000c020304801c0203003d0304143c1c3c2410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 527017167 1250 527015917 527015953
    0x3091002040e0604021c1a0f010c0c060c03091a04050a080307120302030a0608030301090b2713030302121306050a06060c02090705160501020408070f081b0105090a1404060512 77
    0x750898071550409441e00040c001c0d107c0c1400750000701e03504404e40d2800105201401400308400b90400000c1c1d10b010f030110b004814524280c402c0e0b89406c0d401901da0303042c101e6011881d03401040c0445e001582d01401714480c3c8000300300b1108140c0d100307005103a0700c20a00d500ca000e90fa10180c05511031040c2e0001d0f59100394029075105456140024145480b110400e1554000340c000c02d41440e035844850b4114540001440f90048440c1040075610820451000c200e21025019280220318422150109400707a015140e003090411032105840c83c15401e1420400000e5509481c09860000440c21b4503059001e0319056802c3e41d01c6284000c1b0720381c0c0c28094038042c004c150104119060001050409c040000001014081c000258036241040700c0a410b0003450f500a00d20802800320801c0200c2c03010031051071684002c146040041584001038a0b184503078030940c0c0e030040301380001140d8009114150002140f003039800b00000c41c0c0364014041070441802601d041d59019507501b203411841c0c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 527018417 1250 527017167 527017177
    0x709020403031d030709060605041d010807090f0b0d030509010327030509030f01150e0919030c020f03070618050603042f0415051c0209060d03111203091002040e060402 74
    0x82c0c02c07500705c195204d000504503806a00582c0001d4800101006021a4a48050300308814143d0226041d454816080c0e80d41c45203203d074115840e11002d081000309013651124084190180005031a010f051800400a5000039146408246410b40042a10241664451203d80184c07044400d402180d1420703a219001401c1540e4544510300d481a9001001c0c020500311a0040501144141c18054407003105a0024494003080e84018240b40c021b0011144403583c26405041c01d031049015800810366070134441028035094410352100103112644030a40b0a400c0301c0703a003c820300180c0c8540410000d0720050741e0240512880070351100244503124040511038010340c43d00f04c401c21a82d00420161403410802c001d115494030800c0019003425000441c0b24034242901594401d83c1d035000421102010f40454003d501c04c120407000c26029000a81302c1c941d0082c00c6074508081a0300d5006141d0040342d282409004000e000c0202d214203000340d6040d508080100c103102c1c0d48407003d0000035000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 527019667 1250 527018417 527018419
    0x110c0f0a0b04080102070c0b03060a09232508040c0303031104090903203d090605060406080613110409060c030c230304060b0607140f0709020403031d 66
    0x240c46001515000d080c004000030803102001584680c0b0354207200c08850a01d6002c1c110300c1100b0000c1010550f203503400103065988440000441d1030070030740b000c0c80210944400d081034401704028004828501c40320040c9071594406e071072448842464086500082c203880051480d201c0043c01d0001901a40000c0b02012514081c01d0605607180600400d6034041340301940860031824030114403801c450441c030140d00d090002013400c04401e52910a10039200c10000302103109010688401800c030300d1001e41020401030091015000c5428103c3c0203280594005200350f281c064001540c0c03c0209815219820104404295012640b1403440d10030a015460394450b40e50130309038000400031310501c0c5950708155000a03181c000c01d00080d213440c0c1040d22001d0f8403420741c1082184405540c048aa100d60b0041000c00c8201480340440d0302c600074910020024503113a0300b90020440c00140e5201030201000490380016625140142240306501010b40001c228186881800021168204c40210 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 527020917 1250 527019667 527019679
    0x702510a0e0a1403100e0a150e030703091d060108070c0f0c030312050c18010302072607030e0906060304020f010c05010e0114010807050121060e07030219110c0f 71
    0x1111100042c8110115040030480d0703040614a400c0a00b410000d103500c20603000000c1110040391045039603103000a000040c9498001030102910343e4594108a03416510304007169220700807880c001d05244224060000c14080841d400b008900244041c2401070906844200f143d4540d840119500c160a20301522540089050b41001030075805880380210301a036594840b0041030b900b440141c50010b4422070b54004c00344141c1280b100c5c5104143c61825013402d0050356410189441400b0000c00110640b0384d908581081d613801c864070008241c91480303641e800025841200400c82400c0c02520650b800c04010300019005013083c0584034903040b01414101c2403249503980305402e403101c2180041c0c42c3c1c0d454591400e0b0480305128a1070140250601820449040800007030911041c451554001d00c100050380d00402d405600404c09441c0c680401c40c018903190703030090085d40c081c00c91103c85144c4240c0d140b00c03040c494a50070300c0030700d00a4060000c00c001c071000c1000c4514180052580a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 527022167 1250 527020917 527020937
    0x30114091b071a0603010c120903110f0c03210702040209060d09051b01020c030307030f14040303050406080a0e0a0b07020f03130521070b0304080702510a 68
    0x4075007020380740c454402c90070200d41100349210600310400107080c050003a030400118a041c00d800c0074940b01014515000047c01515034101160701816040c0c0f0000c06000e101102030403800045244243c01409804039046880c3c0760641c0a00c405d440c68042e1aa08024000d090052a00da0010a0340c1d040007000b1504061a01c20b168084a01580342116903038050365660208003210070800c0744000c8240080c28514120b803000c25260311031b9000003010410b01c4544000028024072188401c0289400050b858503184d15001e4203560080c040c4c1700120310044001180c4441c2801002d00b49401030307000e0700303440460740e4a2607031540c0054496001d6009107109010700305000c2001c0e180310a80003040c0c0c0510751070503062055080018107684800364040d401a4185800020310808440080450954a544a040412841c043c00d400258028440f03100458818100100c00f4440201034822200c44d5102d50101e40014070200000c401c0d190b05010f8210030354100c0b078082c0a061402e0b0505132020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 527023417 1250 527022167 527022211
    0x807121802090f04021003060302030309190f062606180a110c070317090616050a0204020706021903060f0302060721050304050d09030c030206160c0b0406020f0303011409 75
    0x45080b00c070024010540f01c01c010a41c90108008031994a1a0404200c11030454010a0704c7c0c2c03103408a014080c8001480d4010002905200c540051010944c140c0c9510b4541c1d80083c86181e000c0900b0140d9200c01004444040340340c50320303601407000108144408800c2880300722b030303c041c000d02c0c040c902659520180d000254020042074a51030441c09440040c0c21454080350340c0790700c06504040400c017130080e00615145c0204440004c1ca40d0603480d0041031482c9007091600c62160070081d000703070000c11808100201c80e00549541039100c86180300213402410210308507035561241005180303101c00c08202504150000b845154001d1001c803840a900d842c103002e10012000f1b440000410000c200001e0000900481256000c54070703140310b12a00c1c54072a24548007107800702900c110303000203690008020f00e81c00942c456502c04110b17005c213a40c40c1c885400d030344c00511074400540a0f000400e24414008011217040ea0303210310907140c0d009802418008400d40c01051544507800c04040c02c410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 527024667 1250 527023417 527023429
    0x60e0601080f0601120804050d17190815150f0f0705030712090e01050915041a0a0504050108030f0915071211032703031b070906060807121802 63
    0x181001e00000c01001801c14902454450305a0000b203040d9290f6401e5400941c0c118111822103404845000d81c60f81d6604000c0032014000040307000344000090404c0680c800000c807101c0884282d00c4003481c07541c0d07840040386c3c140545c980c80c039480000008400491407c00c005409030a46d101415800d01c0350038801131205510040301903c1662011812104201c0407150403440600325240c001141850000360b12051141805030318031945016001420b032100340c0c0550101020024024064012500241d000203810404407034040c40c21450089482c3c1000d00506040310403503002580741c00d0074201600e090f508191132955100c4c01e070b0250083c41e07882407406008010b01840102c0803250f01c81c81c025081c000da855502100c0e4009000220038071011242c1b01982c3c0a4440c11031f1102400a00000d086205035500c0031166281da200542c7c0d0000001507000c2510301c0c0d460100800ca880e00b20688011070211a100f0004800e0722030014401460380060300d01c03086002e54128000919400601 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 527025917 1250 527024667 527024669
    0x7020d08181002030a061e12080d15030b01061701030f030509130605190e060103051513020904152601020d06080309011206052110090818010f08040f060e0601 70
    0xb4207940c0100910854030030520a2200404100300d0900554001e6100324074030a0f0f10b03200340503030005042908418000c654003200d007480030082040041640d04001040c03050b641c2c1c0000c1e0390100b609800403801c02d0040c41d941c000102c1884034003c2d9030b8a15078070715489107101c250031401c00c07005004d690310035292448000001c001c023034000305825040c4000e01240450100701c4c0d0791981e000023001c00084035822515500141c080c0b902107210b41d0703508108004141c4203071240d608000490443e20300040c0c0c03036010301a007400c00c40b012301c60b190f410400d0f100744801e40d0103444800300c04070624102c21101c820150112510a100150030007000505982c200c42070765000748c0325904006419500c0b036a000c6014501c01c040030608000841c20180400c02d1940e0110950041801c120140c140300a4104184642021305290602040700b052800c0101c42d00241079000071504c0c0840050011743c01a43c0d000d4114031030f6529041c5c80d581d640c50322407641c4220b243c161109591440790244c65801400454 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 527027167 1250 527025917 527025943
    0x403080c0a0317070921080a05070c0506181e061303020f0109060f0509061204050a0b010902030906060418050d0503070f1806030e070e0109050604110307020d0818 72
    0x1c01c52140c0c5050160000b44541c5154948404503000c001250741c205022005850501d006650400d903d0000039501c5000030300040c0c1095004104807640c1da51010040040303d100d08a040522680e40c03050140b00e018081485c951040944066402402c040d00d01d012015841c0384035080708403c2c07001041e416408490020080b010b402814815410300c2c1d200081e1814081c40c010507060319140340204840700400c22581040300004021030583c2c1c8840c00e6401104070130403040c81034107152030308568440d45004c0c225042c0000e10700000e9018000d00c02e49115485640190415595010400c0014511f0501c203040d9446090004400300c0c02c00c00169610304c405480315540c03418049400b83c04400c47c05481400c1003c01c40702c5118020384070b00040111032540c2804541c040c600040b140c100003039034000c4928440b4400c0002100c4800341c0003d4010402550b01300540503080040c04050300c42210f0354409a80b012101015542c81100c019501c44a4450352109007800c00030109d0408540007062 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 527028417 1250 527027167 527027173
    0x303040512032517160308100b1c0518030304230f010c120606140f0403081204060c09140d0c1d060a090905120a0905131b0e13110403080c 61
    0x8400700300511101c0c00301c3e400d107000041c0c24000c00545e82c80100b0a0500000d0070481c003240030942d8200c8165580024004040429484440742c005031000c1030074402d02d40145600702400708441f0414401c0ca8207a1124440155103140c0d00c40d00d0340d5160f8818840c100e45444000d94441c00d010030144640300e0303402e004a00107d0014600c0c440200f444071442c040340f41740c134900641007000a8118840418603034801c0140c54944800011451a90243d80c5c07001d42030300400541002c05551a00e02640704911441040041a0310703c00e00310f4540c44a80540450f2403190b01c980c85891401c03409803034103980306001080c8003945481c0941c2482c0c01d821100503494540d50248521450207500460140c40010340401400215841d19640c49015202c28540791000040d5800d189105d2031068000c1c00015007207135004400000030300010180000d1903440d030300a004140c541103208400b6420014802441c070040020922a004000d00100c1400c1c0044101003000200280c4414090f000103901075000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 527029667 1250 527028417 527028487
    0x1215111306121d0705090606070204090318080304060503150409211b051504030e04140403030c230d06050907050309070807120b0619081608010902030304051203 71
    0x100e00183d8203110080d40c000640a60710321100140015910100d600440341c0880c0c5031107090125a4078860814041e4000341090019014182c01907444030310f07416444821030000b6a9031500036104c2c000c81c040e02d00014000c00210303c242800d40d405140c520300081000500e00c103142d40b440f250402c88a810840742c00280e505070680b981150000164070019610610044401e984079610f4020580981d00000180000300341403510a00221118034000390003000300b840312104440b030903035044801304d00203030514102c1c916061040c5000c48040345201d0038245409040030f41041c0c5500290700040085940b100002003070383d81c0106c0c140c0107220030789a541e074a06101c800f0908000f4141c001080503840b5000811451880240b02c2c4240da81022501c0752075142c00c0700080d03155018075102e051520340c000b004a510000810000401448030710074440c2255a002c81c1c0c4d0a03242e031104060f5041e0403d000c10030890910358107103284034428409903072a11a215405000c41341400b03518250348078602c15 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 527030917 1250 527029667 527029697
    0x4060c09050a05060d0903120e07090b0d0c180f021c0c0507050705060d020f0c0f010605030106081005070519030c0212032401120207030309050105011215111306 71
    0x4855014000c19901c0c0480c2c0d5090030b011400303e11450384542003040c0c0e1901440240341c0b0a1207003040c03500b9090030030311005402c00d904039640c00c598018400c1452802c0c083c0000d41c82c04010684070154000e140048482ca440450001e6494585860314442e441d040c260700056a00d10081070318000c0915101040004401e030503003140c40070040d007002e2000800200c07001c01c000261b03441c00c4074400c0320101ea42d03581070030300c1d04041d006000f561400400081200c40c1c541e000032640e9008040c0c681c000b000806c1d52002014261111881748114681029810341c1c07809500c1d82009500280b030341449031415060a2141060704440c10032503000a5603241b03010082070b030501580303c810760002102030031420400780245c0400206420070404404800c0003040690186280511100d981e1008640300c00040c20094054803c0d148201d1f029480e100010030b500c103148401102031a0440566822011228404c100621a004810b12000710521824011844030035481c409041c41341c2e01e80d40c172154810 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 527032167 1250 527030917 527030927
    0x1119050607020703150209010306031401022d0904090203010207020a0e0702060a0c050301050d030c06060b07050118030507150b090703061d061c0611070803090706020c03030316020c0904060c 84
    0x1d800c04003150010358003040810b40304410800030314107541e8016a60350340d820041c1c0003403080740c1c80189140303444c446968070713030406501078240711004401307440420300c82003248400b941112540501c006405c0c000e0403c90304180d8032403001d152016000614000716a0006540d00c80c0070741c003e403040c044080c1000b503629414003800d90084000a070511410310803030ba001c1c1060105011300307400303100440b401030281840f510050010742e812032010450151500b03120a1160b000c0c01082d80c1c59821b06118010704c2c20010203400c00c06415949982c01c0140c10340e5403a00300e0a5105103d11110744412004405544800b6058085c041039100058040e14207001c90300c40d085c5411040c1681035010003000807a840303058910003802c543c07030411505010f841c80e1130030042600301e01040c210b0310045524400c0080d044001c501403010701e0115404280c0d070f508100e9403184000c55842c0c06801c28400709914044000d0014504421230054590018407038000c1030199000300d4007501c110b6151301d80d500d09030f5045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 527033417 1250 527032167 527032171
    0x21e0a1a031605031e06280521060f040f05010f02070209130f1211031611190b03040819020c01080606121515040801150609150f11190506 61
    0x241803030344c02c501e008042d05200041445c0da00160744030320b8000402960360b03020994042c0c04840c0c0d0302544004442c458481e443d4003402068091100450f410507460040003061403503500c203170000d005954845040410864001d0000c4a1407040c0500c0b02c400584280241c0e03e81020800006894420900410004001c090402c1c100c01042441000215000008812406400c0540701c070402c00c0003a01282c01d1801c0f0104440c5500000c1442d403810001d038a1118407460040a680318500998410070480002c0c00314401c0021800d0b00d0b0800c85440322802565020b402800c03014100004081e030f617220740c920003806c000160040c1042c2c003810360700683c206030001c000fa1002d5003080c4070001c80c1603441a01400060441d0000c40e99070303c0c25628103088075451400d840c03105032140c0d91407403d039000c0c2450040b460300c0062810700100e001c5110365403040072116404180101142c1c0c3e1401907468a40b6058903404000341c281040300031050800c09142c40020f500c1981030407000ca81043c40c02c0c4180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 527034667 1250 527033417 527033461
    0xe04020a0206060907180f051806010804410111090d0b06030109120504080105070302091806150c030705010f2a18060306051c021e0a1a03 61
    0x106000a031030003640050010382c01081950041019181e007807040c2d500c00d030354480150301c0f540482da0119803c45401901801c442c000d860b8001442c03080f0003414904201100e1050020740d80c0c000040201d5101e2400035052600765401d0b1003002400000f40d01c3c00101c0c0b21218445840c40c41900340b0721002480b64100351001210200c0c2007a04502c000340031490245405030a00300c215000c111583e03001c0d40041c4620b54404e19141e034074841200003401d5034101e031140305115482c10001030070b818040d008403441210002c1441383e680400300003482c11260045c0940390020410880d4a001462000017442d101010100031a16418240b07855800c0d0360f0341c440c1e24103803d03007000c03a01100000603041e400c84094601c503416000b611111012207207060f00e8a0030042c409003d010000d015605544040e00f610400c2d0b0b03111159091007040c1089104946070000d40258606210b41060107581506510b05279000303106002842e61207041c108007426144104903403803000001e0200c80c071444840c905080031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 527035917 1250 527034667 527034671
    0x40804152111030a0f1b170106030606050a0c031b0302070503070b16021002030f070c0e1339032a0b2704020d1d150109090f080a0509010e04 62
    0x500060b9842503001c09040c01507400e4403141c0c80402c103070898008000480c5002801940741082100040890a0400c204a0403025503000800c45074030a000d00010303540180c40d00c070b19100564508540f0f04030442000c4e42005004070030140075030b030402000c2c2c22950090340200855030420342058103000140c0e00c050090002004151404584200c0800c0040e4046642007004101c1490030303030640c4900403100e080c84000050f94000c000c1510b848405440050812004982d0350680b46071400b01c103610080d0110070201c00540c0d01400c01424050700e00ca1000351a40c0607900884045040d103110341084480646c00c403070b4000164407158030000d1140c02814a03a082c103251111440d035910407005c4035000c20403443c01c4015081c640002040c0440e1001c5c008540d42d030710345001d107030091010b00781d01c1060001d4140010039100000696444030600a50710383d045920780640c105c000d0001c04030413a003024004031003801056500e4080c00d1103100a8883c070713507284c910100040c103002450121602c224 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 527037167 1250 527035917 527035931
    0x18210105092d01152903060105070f060b1201090b060109030f0b0408070b09031201090c050a031e021c0f06060c0602070f050706030207020405060306090d05030408041521 75
    0x48200040100110641801020a01c1820182ca809440121644d0102580708200041c110281c00390740460039000903044040021401d41568681c0700588045000603000d02c00354001c00c030401ca05242c02c5208a1001841444a2011071070b00c0041040b041000e0355221000010700c0401940c580d8005400d103850042c1500f1170381c9064491202d040050043e000550002d01045a2881260b401ca03401481c0c1001c0391a01010a41e5254003001d03a2807202d0045d603000040202e01c1d405a0040143e007900d409060480740340c01240101100c04852202c10010441080400700c148020644c400180d0a04c0402000156481c002d443d444049414024500b030400c00c078040d80455454a070307a0f0310841c0581d49403130b1802d2000c1103040c0e200024059004030840040c18540540c002e050061080e5030501290b80c0340000c25440d59030466400089400c404c41100c801d030300c101c0095078000c0c4501d41080c102521440142c0f6004010710f9400f000c90141075201e9103103604020300c01c0070350a40303400c10b21000b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 527038417 1250 527037167 527037193
    0xc060c050f0d0816020c1e03010c0e1c02010e060f0301030b100b0304111f0815090c0d0e0f0a0506010303090e16030f110c100608211821010509 63
    0x103400001d1804525400f0081040e4496101b0b102000500c500101003520f28490200b07442403080c03020304003521079071814100204807802200d5810018078002c06865512150555585040c081c0c04012810000c0390b20403142c1f10780d02d040203010710580314101c6903103070341c110301e090013200d08040d0003044145110707801000b12031000022a40d01079404420541c0687c00c2c0d40104040c902d061601c80c0d0b410844215500c041c1e94090b800c54403400c0d05501141c0d0010201c1c044c00027900e01901c50041004081100400035041a0000c0c4044030a9108070b4824101490f500da003426090308046945400c42d0004109040d441000b40c006040c40046042031400d1088d50708001800101d05c45081c191130300e10602d41a05140e110100c5a0b002170a45617480791502e40c59a244c084074440121814a4808040f402c81c100080c0003441c40f03c6000c50045c54040c140030701105410441d944ca100120703000822251380c0320100380307031a031005e9450721007416401c8404503400d60ba001006002039911115480140c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 527039667 1250 527038417 527038427
    0x9090f0614090c1e12060a1b05070605090312011502100c20030c0729130b16080a23030601170402150307210603021e04090c060c050f0d 60
    0x140c440215480c103542c4d10b2041503418220740c031410240d4441c8464403502400c0344c0200b400f611404d4001c10411403400c2141152101c0e1105110120011380140b22403000a611a80807980005201049a04100c14507901100200382600155400540d800c00310001a40400c0b4103611000012002d1010303801e640402003511000900258104d030340d45840554020042c01264a001c0743d681c103560070f051315411881c1c5440007000707030104a003622aa28181c964560002c0c0c51920002080701c0030070b90b10700186181203810032020450107042d0804400006881c040c010552104140c8540d40d0299910400800e82c031505060100228020030400465a921200201d2007180117400d0b003103a900c5a00105520220001e01d482210703000105000b02c1580056507040b0810030600c03800010050404c011040e25181d21000b5005405580e021500380c034600c1d44500300280c081c04c006440401501c540964054607842000816001c05005040c080e050020416500710040200004080000b0040c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 527040917 1250 527039667 527039683
    0x21060901060e0a050417030a0c0e06120106180f0f0503010524040905190606030c15080f09011503060b0f2d03030c1203160305090c0f01020709090f061409 68
    0x503c0554a00c0058100200b180c200b180000e043c40c3d13010303103900e4071040c45402030092040a4000c40e00d002031540e51031605004440e0441200111103015900e00401503c03802078911a0102c8131120005c04035100c2c510040e042c00410089190005452a2030141030071201c01502504072281000300c2003440d40c809004a9030300c0c0c5015031700020b14065504241e428220007000010035a40e080c8484024480650022000c3c0d82c05800003282c0b01b903640c00390a0640c004104842c01003180000001c10700502c005009a205004c840041089000d100c4401001c4581740c00899065584001442c0c06003403401c0c402446070001d43d0708420300c50301440e89184c0e0b0070b0700e8503144403002c4e4204090301103901e044c010b5504509028086031206810800c807403c65400407201440040b1481020035255072082c000c00d405803107500d025060a50454091103c41c800c501006030642c4104c0c140001c100031035200c0e03420001d01030300810600d1205442e1035015598001c00f00c1d0800c01c92041405850308000c14608 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 527042167 1250 527040917 527040931
    0x1e0216020f1302070803150916031a030a05070609090b010c02040b04060b0c0601180c0c02010e300d02010207120c0c051206060420121521060901060e 66
    0x10503140c4800002692002c011007003007800364004656582007042050246000d81c0c00319403040740c40c1703c9190a00181d00000c498221601c1d01c5080324801303160295201051806509101010083c40c490119140846035a0200c9042e80300900070481c6613030024904028050b03204e401c0c411201d00c440000c141030244100030344150b03950314900d8000e070f44a9005d00010458130911948a41c2c0108165841c0d803030900c145c00d8070401001154041040c1c9200320342a50144c1c1d2982c040115554004540c003503800b0030181d4218145054103d0f0880048114000d9812005640c205d842502e400f8981044804070300041503a0043c03001400182030388600700784032407440c5001080c6c86107504164a103e043c0358010360f0001c070f1200540c000031602041c903d11a01041c1c80500c003407070752003125120b05038402e07a001000070414420300f0003042006200c242c0100c51a4a0b100440e16844002980014042041a500d08050320380d04a071038800c3c0416540306c907818000700070507403401448040130000101a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 527043417 1250 527042167 527042179
    0x10f02120306130903020a031d0907080402030a02041b2303011701090b040c030218010b09040c03092a0b030c0306060715090c0807121a18101e021602 66
    0x440e180c460f2800041a520080401e11800b0780b0703420040c2d250404000150001800381c0841040c3c42000484200403c4000e01781c1c5885644901c400c071502c000141c000c0760b260054004500141c0d40d40d02460b0700811200e0303d0b21401c0b00351030901078400448034009001c40c001403480320081c480d03010150380c11942840554101c401854103001d00505007000024200508a01400300744160341d400d400541e4420307104082c0700c0e405d000150021400034881c070601c8540811100032070742040d0304003078001c1c5045c5c00c02081e45862039680c20884d58501c4c3d680600c01100d21184402600c6003a107a00c010031003040c50703a2560826110780c41041c40001c0510307000300c000151580401c440780c0460b1003d0349000e48100410030315031922190b411300c140320b0a1041c0c828080e020420f1780c06910000c280395403103200d090815205010080702d4420081c0803489040041a1040d0303501818072402074101e0800b200010072000e141046403400ca007109080214030320500c03002541c0038100003032548440c1c040700d030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 527044667 1250 527043417 527043421
    0x414040b03061f08060709061412240901081506120606062b05091e07090b120d020307051507121e02040305010f0f0207030c0b09010b040c0c020f010f021203 69
    0x3c0f10b45203201680001503904c20f131420040f000303130300c01d94407001d581c00d640e00c0000480c50b0080c1206140151200b0f070200360307152000300d105c00045c5002070164001d00302c0d01e08846102c1c440020401c40c02640407034265002402100282640010115440b000c00c0305d28104090504100b180e8561004000740e016480000f05e03403104840c104031100b4010011350140310100b480344440005090213403914420f511468015080360105881c82488409500c1e0050001c1440d01030103a01800c21400b1140d0820500e4183c2c284180c070500032240080300680040d640c42c1060b00d000d502d808071040308205981c10f60004d108510b5440001182003207001900450194540b11442d110300702c01c00c44209500c0e1001030f00004000d8103421092980c40c440c0001c1086816010301d01c002d0348203c0000400040502240e6000190161580798108800200000b00086941d0120b82120b00b80d0540c40c010804a024000c118602003031803600c65002071a00e12954542180082d64411884410240c10400840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 527045917 1250 527044667 527044711
    0x90a030f0c0602070609020a15020c041a03030f03040c05060906040902130504240b041a0c120f07140c030d030903030b100302070311010605101409040504080414040b0306 75
    0x12058072464100d40b08658980711483d00400504804008a0090b03070311000004190700d0742805150b40440780d40103807807045106020040108010940007140e011200c0d07600c001a102040502601c6d0003040300d20341d0764142800e16805e01101e40c2c4c450303842002c04004020203511100269400c0300e2005402684400090004044000c500e410068009182101d403100c01c440b240321040b003000d41c4001800c0015183c1b50102018480c60003050743e000c0f0345080810722500d20300300510030b40342d403403080d950f05510321244140a9440030105588c090710202d202c50501c2032400801c5c5501d802d110051940565003408a6154411090724206241c2d40d0441c0d141418040e401800c2d6030200104100c84038800e111000d4025000900154000f5100002c1c001c880034051051000380ca00003400800101050305045402c030000d1281c0b1401660180200641c503102c40c0030345405580325542c1702d600c40e41002460b0284c0d6840c810078a210b1801e0692520380303038901003401034000349072411030120902c501c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 527047167 1250 527045917 527045927
    0x102c01140918070e15040617040b1602030c0d1d0301140f0a0b0603041b0f030302071e21030f020c0f120304120303051005060a02061f0f03030302040503060c03090a030f 74
    0x20580c6800004403217894400fa480280103200340d44a5465010242d1131560f40020300c821704a8005001c2034030440070504c2d28004090850081c04184100c030b150004a2075414100600f207503c0c00041880c01c03138421a0400800104a00c1c1c000c154001c10030105072070565024118007a04014440b0b10b41c00106114130043d801c04095080090916652800c140c90000352410742c041d4075a02600c09201d0120b0200b1080ca02501180d4265004040180c00c100c1e000c002c1c202c034072805a4020101c948002031402140207048a800e00e4450f00c010481004d040181c42c0910201c90001150082c42d9810030654950200f01003000c000c0d11608880541107a4040ca144115005802c07620800c4140800305541a08800d10481c030b400c0c220606155520148135460140c5240b10340581c00040c0016174048480c03168448080f1607640d81100c40c1d03903403c10030030707203200a4006500280d0009400d10850408001c0e140d0402c0340f03404040d02d1440c042c5505d0b51916200079000f000c0140d90080f968004e4410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 527048417 1250 527047167 527047187
    0x31d040b041401031e0503072009010308120a1e150803040e150306070c0206030702010615030603030e0a03030c0201051e0301180c0e0f102c0114091807 67
    0xa482005403a0750000d82e003100305024441164090a4094401c0c10341083c22005071715240d2010055080000e01d1751091803403510402a8003410102210004c007584c3ca00074464020341c040c0342c01a9403007822034001c1d103102400401c0b0041d41070070283d43d11140700506003522a681c0365030702d00040040704002d00b03041241403980802d01d0361101040208450145071026802542c00f40419200c40da00d500a150300d0b00000c4a00c02c2c0030450203021000941007810095503c032a5070301c0005181c0c2e031030782d200d8090b06642030741d03140000340d60349000e104240d00451410501c250844040c0c04075841c42d90000e2501907008402410820042169052250703000d10b84202d10400030710307280c2c9a684820400c4041c040d2249898000ca0030920310158090040303849004100003d40400100b9600f03a040c0400c9000701d8000b141045001d4400d817550800303d8200040c4003c2d5003941003e5a220f0400050000890042000c402d40d0104903190702c2e5954400880d02c050b900c03a00031b8030b180d80c41c240291803402c66 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 527049667 1250 527048417 527048419
    0x10501091802130603020a091d0609060409020409050319090f050607151107021e0f0603070e09150f1804030831020a06110c061b100915020304031d040b 67
    0x1090f0100740706030190040c210147c01507aa07100707241e07524640814040d0f08244464070090310300d400b1440d1424503a0b42158040b0340500302107824443c95000c41e0449007500c400392119000401c051403d07207079010422072881040c1ca40403400b6420204040345003015440b4a40c03060400244c2d005c200000101c0140007080a80401c000e110002824104a03030721110040f8031455400041c1c8408400303402105811600160610460b04c0d1841c00b030086640c4003401c0c1c1d45c24060f075100e161955640b20000503200721424022495151008801e02011034002c0017202e209144207548204020764401d4142e5100c0d41515010560b40c80e0341110707c2d020181414001003c600c0000241c064055218030316415910a40304100f0781652030f0720441d0318543c0d18050800c0c0360891f2100a616107040b80182031a50440840140b084584440131442c01c04a6002c80d2011078445459800703012001040c4007a100209106602e5450190307002080c00c03a131000c417190b042106009440707403071b220f6038810159204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 527050917 1250 527049667 527049697
    0x307020f0402072909120a1d0102010e0a0f060506011715010c0b07050307020f0303010605090402030c0f040e0a06081518070305030a090825030b19020d23010501091802 74
    0x39018018130b20f0f80d81150811200c0c4596850301c000c10b401c11003141e4214134140d40b80303258448111044030810b1814a4110304540d00c407070044510032424007484881910400c40c050740303d840b81c5805825903800400d03071414400c3e400c0c2c00d6000448810381c40d82e4040100308041d65054150320041c1c980a0401d2000350140c0702034410002d0254002c40103501500c00e0382c003140c000b0940443d1090740c1c1e01c030074094030700003c40610520029043c641c02a40e0003410b10f0040c1d508083c01c00c080c181c5103400a500c07000c010750810b0103202d519181842200701030a10310001c2d102e105081d080071540d5a80140400902c110006d140040da8001404040040c6901a0a0b81d685100d100c030002e1158149005400c03440c01048200e541d852144082403944024a0803580b0145113551108008070758001c140d04050801c10600070390110040c0700400c0307220005880002c0c60070b00c0801d0203503d5111220340c45500c0d607013040140441c1c0e8000340380c5002c4540c00c8481050001002a121020303000d03002c0510b207244 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 527052167 1250 527050917 527050973
    0x150a0918090c0b071103010b330c25030803060f010c0f0c1517010b0f041706040c0905041a130c0e040212030310060507020103060b07030306090605030307020f040207 73
    0x1c1d011402071134028081c88031002c03004042d8040508845140c010303154003500d150342508040049006c880c911445202c0c100700b00305104400e00701243c0c00040c1140c1304c0e802441d0407018428114002e0840c041c0e403101e070500c581d0b085a4031217100d4400904520711501c24210130003800c2c1c0c0300c0c00c080500198082d00e020000c0105151402c40048540a0301d941d42c03050b211000c0e90944540442d9907d040d10151005260740382c24198001c982c80305020902c0003408001c003203603d40d10004e2095010561000400c03080c80c0c01d05200c00c0c02c62440d000040710305d0804040c400410710f40543d042244032005220044c5489140100c42c6010b110240209250240c04001802443d80d4081c6840380d40265013041842406849441d00c900c03045031030040303c00060400744070f110311a101034418544181000101c41e81c03142d5003030003175404c40d61003100000d40720302c024044800c10b400b40000401c0c05400450074490681d0003d24070504040c01980596804944982449480c0f52021140007120f041c83c82d0b07403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 527053417 1250 527052167 527052179
    0xe0a12030e040f09050309060a020f0f0304060206070c03050a0e1306090e0c0415090c1202071101110705011205100e04080a1107031a06011103030108030702150a0918090c 75
    0x602a440c901c148101d10301800540040500d0042401c007582c0400994680708070213013001a150001042282180308103000d00710b446008020841210381100000e40e1514a001e01c002d18000c0000d0088013000150081d820009800c081550100d00e0076003407943d6418030400c0461041b00b41446c08480440c104980024924181d5101f04d01880248040d5207240c1040300900c070545192740c20180c00e034192458100004c0246034002030b40d050032880e200c202042104c051100742d80142c003086c0c90910340d000030f6005668001104680228103403020f481c0d46460000040c042440e82422a90500e4484001a000120403042c00d0050b0070300c00c8803244c00d4102810284220380240e0102004200c40d60080300710140c0c00141e2030101c0360301c030714011b5440c2541d10b000c411501d805405d26051201900380c610700303001e0900145010340240030085803103030810700400000c80000c11481240c00c0c806c0201205160b440f0302c865055845071945041d801e0107064042d0000e15004102800c81c80680c2401300b14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 527054667 1250 527053417 527053427
    0x9070824191509060b090d080a020f1b040e0607090b090103020d140714042102030c03070e06030c09010308120c12090601051516030e03030c0f07170f0601060e0a1203 73
    0x80d01d8501404100c0c845c0c0720241c0c112070b8410085880d0340052a26403110002c0d8480f0002c0c4400390b4a441070303c020040314240309103800d60f030311941e1196840c044040381c00d41c201841500d0107481d00c10010103d03401c100c81c020340458030900403408844030018903100b40d6401b9804039510328402d52420800c0400480080e99a02c4040d2107040004106500c00701074107948405903003e0f910300030807907901815401660001c91030f0020b000c070382501401c0d0901410756130510001008000c40440c0d41c14074504038017010b050800a00005210764203940c01840410001426140c03c1694030804403a10340b01c444103113040740101d1442030040345200303003001540d18000c0b0b1101c6c12501c041d1005403100702d000210004900810240c220150170300104100824441c010359690100702806483c0ba141c031040203281803001201d241c00c000d038000e0b6000c000a4061044994520249402600701c02d00c920302c0f955102c070010300c1400200920302e044c0000e190b54584500300185044500035200c01518500580 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 527055917 1250 527054667 527054669
    0xa0c0e04030306080a050c041e151a0a0801050d020f10050c0c0a030809010f090506070f05250b090613060206090c061c02030a020c010203010e090708241915 69
    0x70010f8106100099009000182d280c010741d4030401400e02c50400034240001408010711001c8440d18001d0400d8074000144554001e5130103450104070400c0c1040000480c5049020140b4014a0100929440d882d1700220140c15503404458007040e40072540005800791001c1d030b104c10760298403445070b80c0c0d106800c0f000504502c1ca824042d100300002483c2003110940c0c107440081c050900030000d034241c0e0b61103207402800e2134000703040400c1c9442e1074001050700340d00103a00072205107005903485010301000b0494808101c000301840348038a1b11002409071051024403400010f2540815402c4036a65400b050320f101c0305107a80041440c40e52460003d59950040e10107900074001d01c54607140b2420302104a1307011801301001c561b2a40100b00c0720200035440203040404003a401d2100360401e0368280010360003421540da010b0003130304186450600703010250f030040e803181c0d103e40350000381d1141207030a2540220705000c0415035541c0303c24100a0300404074641c200414508928038074950120801c5030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 527057167 1250 527055917 527055923
    0xe060c09060d021606020c07210b01090b120f10060905160f030b18011833080f01021e070f0b270304060906180504150816030b1e06010f020a0c0e04 65
    0x192704503114094001c05840040c101801d8440740b9001808107581c140c002603080c41000c0c00405c005920380c0212402c00c44482032500858000103080e48210340c0c28080c3c40042c0901d00b400f0061400c06041040c54009403294a03410b11030100707490304070207000b9840140414406407413119408903025541003440e809002e4000808410000000c1c000301511070042d0024119400021903005404031482843c080c1a105054910070140810f0480c014401114000654030002d81c0701d000700700d041841c1c504591400440c00700c0610a28001c2000417000813421354020b003442440307032500b0340c5250960b92506241440310388168403c40d20703224000000e00c111407050781c440244540b5207504650302e0a40c0c06088140403c6041b040c0514645030f4440401000c03440c0088003240d542c0d0402504001c11f00c600c0316034500d8821010003d0000c03044400e60b00401e0700d1030310280300105018145d907c0c100645004c2c10080800c0c0780b04030041c001c11408101c5a00018030510166035402c1000658000701e0f0b0403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 527058417 1250 527057167 527057189
    0xb01020a0c15030c0e0a14060c01021209010b1210020315180601030e0106030b181e030403020406090203010e150f03070305031810050319060b030108010e060c09060d021606020c07 79
    0x10300700c6600c502e0b1118007102c1700624048040d49410300d14052402c4d0048031641c80242040401c048100901c01045c422440c41507041207440d0040301d1a00711819010301501805007501524180034020989020780031100900507180c0c1c1300c506d4450004500100b6664008180c040c2c02c201c041d00d48c81c00390f4480d040903a0207100030180d18140ea4240d4040b0300c4020030004080001c640c1e40046c00c507103240c600d2140340031a00d0f841012450220555450700ca0302c9050341000405105608081c012040074085420f800c1d4510f51401208600204000b40f4003420f4418480e07071010b050b90390710790000c003c000c004c00721036402d80c80b03040441d02c83e4450320701c0400b81c0c1090b0341d840b001410001c04602c07045440780c45160442c0d075624601c209004031a01030034240380d91035002081201001025502800403540006240c4446100c0ca80c90700ca005400c11072050300510414903036a4403401190b070303440004030780540c84802210258007083c09409005018900100c1e0349105030800103103800449680d9052 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 527059667 1250 527058417 527058431
    0x3140f27100302041401050c0a06020729010311010f030e030a2601061704060e0105130501150506030c070503070602221502152d0a0b010e0a03060b01020a0c1503 71
    0x41542241300700d00c81d044000c6000c80e03001c10958041c1d8040c00900071907900780c1d49440c03040d980c0e1104a0380034480071034542a01c044080803410034013002c8510142500d5040d03005504548820a081842c203261904006600c0181e0305020322a400c03810007060254112500c50091002c0605100030301001a54413507094000c80c151100c449006034100c40181c0c0b00e40786018001001980144801001516480c0d220510809006000d1086e2072255000e81c80346084502d2600e0160f0130748414400089454645060502c46a0745e1042126089602c001551340e0b175620500c2c0880c1140511f50303010b0855440030880044d1446224948402030031201d000c59519a200c4401101501100d0345800060780300c6003c104840e54142070907504050321051940035240000040640c0107500201c5540300d225502c144141c598090148000d44c7d03c01342001c80082050b0710129072610054031000d0310781601c440700b0305200d9009001d24a031060301310301040300080d03c030f0f03490150601c0e45003d120002483c1102e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 527060917 1250 527059667 527059699
    0x110d0c030509120f090622060e1e1503280b03120c07060c11031b09130203060f0a14150901050409021c061b0908070f0303140f27 57
    0x4211010004c11902c0c0d42d080055a2040c00301c1034006041c5d28144890500d100e0316030705400c42d906401020199948101c80a401044c403034101d81e80800d811505801c0d03880107100e80c3c4c4500404070724142c014049900d039075607a69040744441520400000c00d509040c810712907c03095070005850395a040d021500c0c151001d000b084600d12500002e502c603600b020708141300303441c890400301414500609030a240b0f40031010001c0e0a0007000d00c40d0b030b01000001448042c0342d0400728503107588001d00c2d00d07a48102007011740200c1c1d03d82000402e4519460328070320025005000c640d000f105c504044006ca403160f07141c0320003d4030302101c800507600e1090000000006131032525018100c1c004c0c1c0e01501880090881901011a2001c040403c82d041500c0e40303070444050500d1150440e052a80d0356030009490319242c1c80c1030034100990001f01020502200500209801160b100ba441d402040b45030359841070040c800500d0300420b02101d0750700059884480e245101c0c000d1340c6002210442d4140500c0c40604 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 527062167 1250 527060917 527060953
    0x21100e0115090614190e040807081c060e0105010f030e19050a06110a120c02010e030a09050406080105060105070201080a1506030204170a031d0105070b09070e0a0e0c04110d0c030509 80
    0x2400d400c2070102117001d0040c1c400480f41190802c2c400e9010300d0030240d02d60303120049a085040c9505900f2000240c0000564143c06000c00070a40845c25001c2941003000092541030040090b40034107840d0961015400e200f000b4540d006190005d01502844a514041340c031785040030b90a03207016003000014891380002c18112a0710f20810b48840f204542e20801a03005400310071000c5040d0b56a9a940021034801070004100e0501700c0d5031440340141c00c060800048070002d070000b03580b030307890402003000c503982017000c448400d602403e02d1201c0c1c0e038030250300002a0981c81e202d50021109010f00190071a016000341080d40c580d0b40c8543d00e280c050303040b400c0c2d4a031500380024001035003604006001c02c100000342d145440741807411034a4080d19499100380c0541c03d0300c03200541c3d8040c001c1003005a1505401c0c4d50822611802070000040906210355600400d00e540c9101d641d550040050b5410041d04403116660049018403050b03a2050010700100320071917103003815000711028220004400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 527063417 1250 527062167 527062189
    0x10209101d011101241701020412020d0503131d070c020a05190f0b070c0b0a050909070c0b090114060d0b0408030604060f030c0521100e0115090614 65
    0x81e91000d2010a529001156007a0b521201d41c1e005558400e400204040360b0743da046600d080088141452a04d400084d424a240b21101e081242e44184000c2c4460340d0318561540c0d10540490304c040d10002503080140c1103108050719500400020000002c41d10148154940610a01c500c902e0030355554000a88000c01103220003580040001c40900042c5040607440034412551503a0901d056195072040326150400e0300030035050303100230130b030303502000b2074020164050030701454041d080c10701c0400b0240150013800030b811b12480303030704d000103040c90321648140700c006821951000b6141400209203008000c50b1042c4c114800c48940080c07881d09203c01c3c10030800364040d0000e0102e03900d0345c070380081c1904041c00d001d034082e840320350028441d441d90041501840c0640ac0c2818220301e00400c00542225901011502c001007400704038800f400802c1c0b032071801e0a0008081002808c002ca07040c014500c07440e40d88030309031101401080203009036110405441c41100745502168a45080201c054030b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 527064667 1250 527063417 527063447
    0x70305061c050c0d05010f0603080405190b0a1101020f0a0c1a07020d0c140607110601050d1106092d0a170a03110c090c0d05070f05031f03050f01020910 67
    0xf2102e00308525051035440603d03030324000c00001940020181c0c0d010b05442c0242d00c10303501300b080030400340030b245016150f40118014102520003594900481c04229000c4c000b151000e001c000c00e11420010001e40485070039a030040c07a660f81d02e051040c0d003d403050404440584502160341508400c61803510329140c042c064030380091072441c01d2960126030300c2000e5003040320000038182c0704180c181d404006a60040d400746d02c030020b0b03404001e40d9103032600005910181c0314034468651a004101d00c00700440030075009441180c0e6030b284d00d001154030316800c4050310301400e01042c0a0340c0b49180b00214a103008c0b00490f000c0d40116510640e12040d4101d0342000300c1035400c0301c50141c0000703004180b007103c03142055040c0c039080c0f80c1c803200280845c4001c07103005440c45000110203a6180c003500c6603030382c04022401d00300d040b580289001022408002d1145080b014860311200303140c0085907101e0f004540c040b0884000301d0701d42c02c000d8043d40082030224010b1541652824186005420000003050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 527065917 1250 527064667 527064673
    0xe01030509070902070c0e0114090f070f140913290604050907120203040302102a030203090a0203010204090e0601121e1e030201140106090f09050606040806070305061c05 75
    0x41040f90720b00080d032040c002100e0540011310006150505110b84034028039007800242d011048840c1801092074000f041c0074030903202d000c1040328664100e280c01c501c00846181010300c400a000c0401401e100d40110140c0c40b60340c450361511140c0ba1900281000c01802d40d034581010080504010701388803070b01c240c3d50300020a100034016400d06e900c031164064594038214001c060302044800490380207507401d50058100c100c600e00404c0039401529a44090160740310200c075200c1d003003070320000741407103c4100309074001020a4400f4003c020001c41550010021540e40d683d0f89403041c01030811006c5150a0301a1360000102c0d8007004d48502021500982940c0000c0207500c0d212144621050f8101c50360041d043c40799171004603030340f00710310a80e10980000a4910212280b800e658105903c4035007004102c40c414400141c03031007d030784120f505690003c58107841e0300002508134051600400c00d94802c40040080c1540d00d0381006004480c01d03102c0200c5101120f121b1882404c1d250f81c080e00e954 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 527067167 1250 527065917 527065919
    0x1206130e06041b080a151b180506180d060b1c05010c0503070f0c020103090f1a0c0901020a020d0c15090f0902070b130309090c020f010e06060312030a091704060e0103050907 76
    0x999003030150651a55207a0000502d5003040f4424107c400c0d01008000c00510b6240b03000d80c0c0e4040c0840d003c07019101c12900c0504088014501d080240100d02903107010b5140805a2020404903800400584100406203590405003d900740e0000348100000d6030319600307000d4220b07120350050040f01e000c2c0506949a06100500d944e0684814204a0307080341056500e8001101051130a55881d07070280c45601066110f00031281d9800d00d0040143c001c11000d00e04202c05032190380c0001c1c4012201d1741c1035681800e4004142804260b0459a0f4000d120082c1408001156580d0140202083d00c58080700182071030380f1046400100e000d901001007005010401107440d1842c00d200d002c181d40d00c01d19049030700c41c0d21800c2c62800d5584001d01213015901c15441d046201c2c13428051b004101c00201c0062885241020000c1d03a0741806401035109004004003080300412203070049404260040b00348000d00cfc070204000aa640c6c018480c240003d1004030610000d58424050766000b8140140209111 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 527068417 1250 527067167 527067173
    0x16030503041512050c040501080f010b0d27080a08100503101d07080609070608060d020405041e0308100509090601050f010e0d2303030108031206130e06041b080a 71
    0x2c5020785150030601c000c90140b102483d80300c0c0a4144030300c80120381c2613201c03071400c1e0026102d0300001e4250110f4903001001440b1a00b4003800355a902d207402d940210781d0306411400c0301d629000c000c85d001950001c814442c1d003400f10140042c0000d0a40b5640c109440d59541c0b07032010200b5180c0145581a000047da050880d4007a0304181c0d00d031081c42c0300d01c03000e00415894051401d0120343c00740030785800c100100f1030001003d002c8400146140c0c00c2c15041031620000242e18101e078900000d1040b0350ba1808a0140302c42c02581c1c28107800e2448103080b4507441818064208081110345050000c408000403540f030402806517401140244000d02e0140d00340380c2003299500784d10a0303680c10062410301c6012259114001d03120342c04e00980d01c45510303032050760384542202c50046400301107500030401000420000002c90300401500d0303c0c8a02d542c0c84150000304010450341c0ca1441441c2072880c030121031180070030014000c0b40f085030b078101144034810705013941c0d6419224103c0150000a108004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 527069667 1250 527068417 527068439
    0x9010e0f0c1b100f0c0509061c0b0603090f10020c0a02040c0e150409050703090503040e0a06170f0c090610050313140a050f011103060616080412051603050304 70
    0xa589008550a06000d211140e01c0e40b400001d80194040c05460f807040200c281e2040c4a12072402d03006207002490000300d400030800380d1203a900d00040140800550440074125948020304ac3c0038000d10050f0380303003007a501a9507500d1a02065000a00070008000964004d42c402ca4032205a007101501e03101c80c0d9174003048010860a00c1000500004101a0780160b5880c101c40042002c3c440300241c64908046d4940200c0314006c0c840f20034145030101e004042400002524125600f089802d041c41d40c0c4d1003034140c0900b11a07400342c281c40480780c0e4a403084c0d440c08506c08603603454560441d02c51024107010003082c001c080e1a00e035008601d02d920b04803007512910003143c0c8965400c0b200f41c0507010964540c0d0140f450580d10356210303044442c1c100c0800505128080d4481e903118003e000602040404450707903c8042c00e403911414000450020290b00c000a27150b007103410030178154843d9a155040d0303100c0a45050229007901858100c0400c01c10074025180039a9041001035052900b4100421301c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 527070917 1250 527069667 527069677
    0x4120f020a051f0311040f0e220b1504060b0a0c0303021201080a0201080c0c2a0301060305070603150e04060c0c0b071205071e3b09010e0f0c 62
    0x280140881c00041455140c004400041074030803020040328080c031040003004c40e071800c891004c14030810001007112050300b003190000e40c1e00d002003458141c2c070358082c1c01c02c103201d440510500c41101c007078440052010101c41d4510450604c2c04090440ca5800c0c10001191341c1402000e01c0ea403000d0201c0014184243d4962070000d12900380145040481c8a110481382d02c26489800c1780d038051a2080115640105466046aa81c00c0e01600f8030360b0303040c0c41c0c0b511b5548181c50a44410041c0450004240140e0701c0e04034201e501a0003000099240e00301180c664016004510110313040c0150800e105c0f1140f0025000c80e020f40c08080b400f6240d41c0d6404024100300d4050204200490307100d40040340003147d0550041d00070391101f82d0108121401c40c0280d80d4020316890a10198684191a0700070341d00700a01c1085203403901d4041c1101365101c255156503880c0410000040b402400302c11950303d0301001403201d500302d903941b800e130f83d03121402001004100c400800b260703840404076260000c00400b0701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 527072167 1250 527070917 527070919
    0x102480a1806051504050a0501051204060b010c02040f050703050711030313020f09090601050f061912110f03091b06070602031032010f0c080304050f0d02031e04120f02 74
    0x120b01c0395a01e034002010071103160003001803600b0024007000031f480c00e40b580b00014407003030a20b281064840c04500c420040010000782a958480e44c120529071300c580b1a900c040307035004200f04600c2141a0510f00240001c64103c404a8071300800318000600a4020b142381c803444800551441c0c1c2c5003028482c00484e1104101e0f0001d02010051410f542d60b040d542c3c2c403a41d2000002d080350740c0b60208202e680701d15040b4003801400708200040743c1c954102c0d46643c1d51459070509054507110070900d10300030184034840000345030000c501c40d00080001c0c80114059044c0104607505000003071040468030100d0110280e01140030043c10000075529009103070f00c002e004078001c000d140d558911a0691940440c203401807500d11140c11800003031190759042403242841d11400c40e162001014020b80d0322804090164480132000804000c4100581d20400c00c2c00f0094401c012040c1801030340d20b402c40c1800e840c4441c001c9440c0340032507011500340d4045802d00c11a40b035210003180c0390725418601e60101a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 527073417 1250 527072167 527072171
    0x30c0d0f0f090b0406050a05010b070f02030a02032e0e150a0b091314010b24090a060903150c21020c070f1703040302090f060102480a18 60
    0x592101e601520401c0022800b503510300c4014034151a01d0011503100030503464125107001c005000e42c060000980750425804694040e071046a40002807030000d21000086d414810386541010702c1d12020884050305401200d000c49003a24400d101040c1c07039152460382c006600c83c2081c03e5050310050401a0009040701c4000303802190000410b0328a076003240d05002008400b003081c803c01c0005c1c4400402403500ca4002c100680078a00026041c03e64480c03c1d00e014080400d07810b0721050302000b11900701da001025410007035a80d004c0546425518841a10700b180c04810300102e00006010340c3c8840c401980d1100c0380e20031103404584d0486044c4480c1603541ea82840101060601005658090300b00345000d00030180c6040c0ca0980b001034811010722050300f050004000584a2110440d0840140702d0101a03072703030b50140101e107040c040002d0380e282c40c0403900c00c0029015540d5654030311030300302100a9861802c0c0d02001c118070281460030341d41040e9680402c200b411045018815400001540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 527074667 1250 527073417 527073431
    0x7030c141213150c020907031404120f0206070c0b04080c0322151b080c07060e0a0501140d0c1b051b0d02010801181e050901060506030c0d0f 62
    0x16152094540c806a01c0840004810041c0344103001600d0003807424142429140c00c0d8100c0c000d04600030550024001e001c070401041c070880c020f401c0444d50036038810300d00d5140e05c2c107403d00c403055598420300c0f06d01040c20510048021440403c003a0322881d00b139190748004454a0b501c0e0600044018011303a10f0020038044545915000c1c0028401034001191221245030440198024040f9591040c032000e540101a084240c0d04103618401a4120001e08940c5140c1820680c0c16846104007440c42c0c1c2c0201480894195008001400d8000040e00d004112540b20401900d8286c0682960f03071102205000f001c155440a8010091740710491410040100c1101c8144980c8640d82c041224503801441a5031643d0032001050b40014404441d580b66004040d00040c0041c44180a0100c40c03842c50718201a1030312050300320718580c4005004c0511162040801d800043c001906c0e445065402c0000002d800e00e00541601d002c0c1084050041c80c000700d810164008007441c45542100030748a0342 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 527075917 1250 527074667 527074703
    0x30f05031201090c0207080601140103051308040803040617130210120612050f1606121118041503080f090111070f080f0601030f110301020d0504050304080706031107030c 75
    0x81c5103000f0980c4000124180b0f031480006410024103803c95001030b8810801000010303074a0401046025082c200080c460b154030b01003213003040302000050441b03032000800044a40d00000200102c3c0d5180e522120300462041240006003015644414a1805400d04801510304100d1900310031441d81000000442c01c83e2618081d01d4041e4018900300d03020400d00310500109102180180100c03034042c000c596180404146241194056002003150b0035100c6407450581c0d034800303076500e00c0d1041e0703080d00c940300e0301d100c0c0f611004400310b818003650400640d000c40180b100c0c00c1d031003544d6116080c9401c004c42d44100f14003641105216030b04105215941c1484c40ba800e000c1103000e0801010510709041c01c200b407003417810400440074034484d031001c0010004a1107071107166042c680c1c4401015038200c0883c001a01a0003070301680c04c5841d00c0c0c0405c3c041003200010091049034400741c00d90384480e659887c03d40c00c40b01400e600404090041150a0000344503401050f80c16211344610344010034414 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 527077167 1250 527075917 527075947
    0x1115010b0d090203070906081e07170a0b0c070c0e1003020f03010f0608030703111c140c061008010506040209061605010e0d09031110021005150d03020703020f010e0307030f0503 78
    0x64814401ba9648032824400404103221188400c0210104100c1c41108008250340d60400f610500c0305001ca524440e80022800b48441c600780c9410010300c001c2410708844000340d9a010040031035100a0103400010154420111240300300228002d80e14800c1c996000d01040d51000d081c0d280d0b155586140300c07101800710f40300e040301411070403008503180d0b80b507490301038621003108142100c2ca0f4080c0424030060070080b52414010141e0b0300d003e00c4862070310a00f0f0308450040c50184d1500e40903590400410b0a6480304000840e03140c0320080c400d6840728000c0c40101d00c1006846500003004202818003100c0e0890140c02003840b4034000a00c0c41d06c0c50304128140b101c0c03482040d0020b40707401c07030800c2401904203007495404411103a05001000c000d03000303540d030b103c90b4050046090302e0f040051031016083c00034000c1d100c00640147c440790707154030740252904c0031400120300c18820079010640d25440b80d80610490b0401034020001ca9046807034515100c0039046044480384001c01000b90040184 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 527078417 1250 527077167 527077169
    0x81b04110a0224040b0c0c010b10050306030709060f0b0702030f060708090705010f05180f130603050f1c050706021e0702011707021915020301030b071115010b0d09020307 75
    0x3541c050030407076190711001190542414203005403403c0d41e070103010110700030609603604041c0a1881540e00c0d0044000399000d01500300800d5841040220440c0c10950084011440340c5001c4054411b0140c035070245500b101c2986c05184001580c1d514103000020916004104850004041701e0402400c0d40200d486c044003101c10100150030300080c800e000030700f08091006010242440d02c814504c40e54014590b00a80f41c581044110720340442d03070651144220403041c048040c011a0905003418131803c040d048901c0100d95601c0340b05217054a00c24041a0000c1d580152030b03010f00b440c00c04407411240b9411584094940c2e581c20003034003100150800c1094000f10740355411503106c810500016004903840d80c4a000301840c03100800520640c0400c0e04000c10f0480b41000b401d141d003e040001a406551810103010307840000040144401140d07013134410a215502c50f80502c005800140d1180025a03440750008003480040c00020802c03406401088180000000d0514054001034504005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 527079667 1250 527078417 527078437
    0x1e0203011b02070510090305191406090f1933020a020d08091b04231e1e0a0b1c030309170c0604020f04090b0a0501061701081b0411 58
    0x5420410480c01d005043c40c8178041d0b41e04000d10103d01d107842d074030b4070b8903035244148600340c50071006c00041111803c4070340c1c8a10407800c100c5486140150707000355101e50580941d143c500c0b81882d550050004003192820341540200b0b401c0c40c052034200d40d04062000b00b0409844810400c9641364554410320142c26446441c0e401810482400c680142120344007404bc442c0350f4214071005000344e4850003e04204000682c0c00040950001602071000c000c1d5400c8500d442807020144a00c0440034003529481a140c0c0c0e00207142c64440002601c803013040340c28400180c85a040000362600204e03800b483d103842001d4101001c2a003180b1048205c2504503008034003103070352405c542d014040482d1a0700901903407105294500002c940e40540d413103c005000911604241d80c0000b210785a50b0000d40d842c0385d0041011000341448041d48020300002d0203060002015142062803c0049105070303412601014090241c42d24010343c9001c040c0d0109040d1908242c8500741030700c0d80d1540704000d00354020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 527080917 1250 527079667 527079673
    0x303040201031109060910091d010e0901060509041e0803160806010302030c04050d060f061d070e0d030c030908030c07050f03010207020a0608151302040617041e0203011b02 76
    0x2805100140840300c01100980380368105020541440e00d60400b04c91001004072116400d203103050500302d41d58019034022901d0040701c80904440d4481140300c19040c0c60414003103002c45d645202c62300c0e00f00d070024403600c0d42c000108e40115021807204041a402c142c08103200d03004010310364541c0180386d8011303181ca400385c041803200448126441000d45401c4003003468103500c1e504000400308442e00880c003030603205e1140035170f103a0200170490b031010b049100c00c04824003840ea0389415110401c0c20024071603d210a0907000101c02c940b0580c02031050703030b01c020000c2d070407800075403811500c94444103070444c1403004415010640b00380400103000c60b0ba005a0080c4013182c104410f00540d802d0a07407850727029070b005101901c0141e6032000e640f8203880c00b6107010f43c8290303203507031b0300202031181088600c0c1c00101034440d00c400d140c4590000c2082e50075588a00d407050380d04d11a6000c11900c2220007030081da05015012542406032650040740300d000400206071121a01c3e881300c0000300c11100784026038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 527082167 1250 527080917 527080921
    0x3150a110f0910020a0209062101050c0c070905040201050d0c1106041104060b1e0901180e0a0606080603100f0908120108071208040b030c220905010f2402031b0303 72
    0xc54001d8441034803140344c1c4050034030a807540d80864124280500520310410500c1100c448004c002e4641c403034020b141400a0117903040160401000d0b030302400c808842402100404100014540038140c092503040c0c0d01d2500e801c0d8804880c0300185410f03080d190400c2002d000340b8000300c804000d00b0380114000c0741506c0e01c808002c8108001c40381d156002419540c4144510f809440f01112810350b0f1040c4292084e0390b90840a0049030004210b400010300f182141074040740e91382e000d0035003901c038017000e0307508101c41d60f1500c0c13060301c01081c1111203590540c01610240d0700880c094000540d174117100200030811046590301d80c0250307000580f540c1d90946404004100d202d00030002213000741400300c1c01310840360594403501a284228050788860071400800b1a0340207031001c04603803550302d06610900310181d0121629100707603003500c16800760b03d0418001080ca601031140000071030310500d4510401403212940d449208424010040a50100b032010780341420800301c0280d47c0101c3c40020b1a035034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 527083417 1250 527082167 527082169
    0x3130f0303060509250c0203120309010605030a0f03020115030f0f080f0d0504060501050d1a070909020f030901061e1214010504030203120a051e040c030c0b090406050f03150a110f09 80
    0x82e11750340a0841000480c14003800582c8011803000e203084015805140d5aa88842e0701c140501020380c02560944241d00c10344080c807101c810030f0390301903200364028400c0d66154504200b80c10203602025103521015500d030000654104400e007107080c0314005d01c07414009110410802604807415000c1215111800c00003004914810240174003411925002d440c01103032198001050720072405079186000d07a000c10301d07460040c00300c9402803071242419550b840c0d030301541c0240360f0000d0b20250620341c00c114000c02c003c5c00c4107a601d40f05440c0c100018030018603103425801c101c1a60310040d82c4240c100341210f103800d082801454031840c013030340007159903010900402c510990000c01310448640f9100501007440711203092082d81c4480240b41d0034068565090100034000140d000034080f8068050004814a600010f80100341080b04c040050566400c140007501035160b400b40d41c180c203e041c40c40c0001c40320402e0160082d1080c0c5002480c80342000c086402c0d0307402688040c0d1101c2d0045227400e05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 527084667 1250 527083417 527083471
    0xf03041115040819170f040806190b0a0308180f04020a0f170c04180227010207050102010615080907030605090c2b080a0c02190f080303130f0303060509 67
    0x2100100061002c000c09a110382017401c00038804008128000145000e600c01280d003900c010b4041002030b101c2c0383c140b0802c000040740180b290711440600b481181046880d01400c0401105e0300b001441e40740841c520181d8407194100d8070081d0f40015031510040c402d071107510207172440e059152100b1030f40341d160b650050411100c2d8402e2030001c215000400c110302d008081543c1c03c450f4072400200c140c43c0707114050000b074001c8044d40121031114001100c440f45801c030904c628200d0070f8090f100e8444c1c64900481c2a01c01a014008051000c1c0411350610b9100d41183c1768003010b483c0954150644913901c0b4816580300b9180740785241d0045a04555510b0700d011b020300d550400303000d42d0031150343c00340283e04080c4820601904032000401c0d4001e8a50094110380c510590040210340e10141c5e03070440b02903a0780c66001c4d803074207007e030003a0214055000204490148010319000000c00007183c0d55044110780b2900114201620359100142e1a00c8030885c55000341d441c101800720700321024600b076203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 527085917 1250 527084667 527084683
    0x4030f05070503070305030414010c15090c080d0e0f0102120309030301090f1b080c041e090509070501080f04020102100e101a060f07020406050d0f030906020c060f030411150408 78
    0x880f94110b01000c20018200000700e9040b5a030612001c219440c20780010703a4032210b84207018220a403034055038400c00c24550710030f0850310304c81d05c44030000c9138031841c2403903a8104148010012a03403255000c0000d1400e480c0c045141c0c0390500c111100d501206500c10b0042c0c005450b0036903681e2010006001d050a14000d1880f95010020100600940f075081140b010015946001c00d1016285c00301e040e080c0a50100d401034401c49164100b8184030001000841406100d080c42d03051811000c9a000b00d404180349013181c0050751800115283c00d84500c03008040648100d0640c13045030340d1890360107018010080340c1e498203809020440302c00005c1c001543c80b02402a200f001d51000c8420251fa074040030740b61000503d01c040b58480f0400d2000c100181120f8001c294400c40403414502000701990310701d46401d2090b41c03600501640d51101366071f07070754160034145d501c0031050000c4a40b800025004d103030b10034007594641c010030058070081128188466410421003a00150500c803a05041001706 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 527087167 1250 527085917 527085919
    0x15070311090a03061a19060e0a08031902010b0a03031d010f080a0b13050c130e07050a12090c08060105030d02071a0f220e060f03060f0907030804030f050705 69
    0x9450315000c60000ba054075001e01004214030f0303031201ea28500e5140200c45600d045030103014980340c0b5003113030b50701c1030a00c5a0b4443c140006200010851803400c1440c0e0410071114070400071030034214101c0e041c12402004805030005c56594681c821080d40c1c03400c102500850080e02c504000b80c584408600d400020010414180503112a80880c40ea910205403580300d080e00e90700003500251000000d64170004c82c800b40c00110b0800d418042043c040748018000305200301004410580c4c4d80000c3c0809a604840910200e00180302c07001d1410702418403641810750000c0d00154040c02030f80d44180146031500710782c1c066804040140b1050900b0420100c203422075000800f1a946044001c1407540a000341d40103500c0340211308040301006940c02c0c1c60150441c0c4512406041a208841d042c50b0058803400c0c1d1103140c0300001c41c03034608012041490310100039005d003885640f2803001c810152006000c1d400c00344250303031000012400110140025600c84c0340c070f40c100c0d00311a0911914048440d0002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 527088417 1250 527087167 527087201
    0x2030c0d0b01110d14070c0308090f030d080c0706090f0f020f01030e1c11070602030c1c0203070f051905031c050115120209040504050f06011a0403060b0303070203150703 75
    0x310310341940018403403141240615002c6590840240800c040c0d0064500082c880c44101601202704560300c0040c0a0f41c42080d220f050b1019000802c05980d0b400d0075103000086401c1002048481d6120310080030058095100414000d4081d540e1040ca07100864040d281c000c0d100c0c2070042185801000030f01150024039040c4590104000f03400d40b07507a100c210b071449800300340c0d083c2c1007440c0c061000b09500c00074800507510080d60303504006c1d40320350208040000a00600e01a0311230200704111050f6198104d030300850401884c0c2eaa1041a0240d00e8000d880a1080094000d4882c0020b610f0340c0003d44243c0145444012100da240b5446904805c0302110a04090060200a0105c1140f803007413001392a0402e200404400031b40e0003807196401d20341d000341c20a000c10085c4040010054411070202003280d83d660b80c0c920341600112420310480b42611410081000403500315000700d841c8442c020140e030b15007800b590020f403a002c03200450202445644080010f4a9010301c00c18866801e03804003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 527089667 1250 527088417 527088437
    0xe041505060f240c0a0c0501021605010f031d03040f0905070e150d1a1906020c210727140408032802180103021e03130602030c0d0b01 59
    0xb48034081c502c1c11090160280c10002c0d44510455460005038803051002a0355603600401c5503911048400f00c251809000880e001949510008106100c10543c01c1d400c41440d08100c01101c01c9085d040610303041541741d401013140300216054030013201600710011075440c3c0c82d0424011888110750b01c815034580c6054108a0f04681207520300c0d050fa98110f8030118480040c0300590b0550003141c01001c9628038020641107818a00548040030300f0b400ca40c0505a4040e0071000c03181c060b80d9004000050b003184104540c5828a4030005650140246600040201c01708040e0b01d001d1103903000c0411111301d81d00d014002c040c04c08c00141c482146800520022100a80303e110121020704001c005030b0001002520340c2c2822406c0c2d440e28000085801c0000d400100e03450042c0d0815061410f00d40707501c008000c10b0398000c0c0b080300c56000c1c4035440b1080b80694014040c01641006180b0380980011034080d000007030452006601c030b40b81c11a1810345a44d10190848100c980c21380f802c905100700001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 527090917 1250 527089667 527089669
    0x1209060e03070b0a0e06040807060305040212010510030809030f03031f05090106050909190c181e05060307020102090a03120e0406030b0402090a020415050903061e07031503020a0e04150506 83
    0xf0440d24400b6450801c01825200710002c00c4003407045a10100f110700420002088880e0300d40c1000f40624001c441e8003000862500300c8900303c89040e42d081a41c0071401c2d034200005250100500008800103050b0b83c881c04551606a013580e1048a000c1013000707005040c0c0481006204e21701019041c140c4d441c501c6076042c99405081403040c12003080c842c20700900007403103003108001e20a094421011003845030300d400510140400c500307000038030071450b001c03031011404148103440745840c040d84840f1100d00c40e2404003401a10782c80070f44950119502000b0040301038171601464001140301d04036420302d0f4444124010541d80504607034610070390801d0000c0020981d020700154000b50101c0340b400c41da8603180c0240c1c00030720403a0700982000100585038107520350010040d1900b080154181d8495540340800610010301d0801c0652610b041540030900c07140c0719601c15004c04c03c00c40b000030082c6403a50000b40b4080700c00e500c4018042d41c520100820001140700b091944440130b40140b0480c1803242c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 527092167 1250 527090917 527090939
    0xf020414090711150c090d0b04110915010c1415040308100b07110307030c1404050f041211120318160303021e0a08030a061502030702030d08040f1209060e0307 70
    0x2180c0d009042c6078800105031546044000c42c0e0002c0e000800c900c64000031460446c8200740d08941c00d43e401040840ad6409600b0290b010a20402c1c07042c1181014002003401501c0200c90104207485651074000030703540701001000301e01ea5152001c94640cbd1a03280501d03009100d480c00910451181d00e8a00003003165046a005a4510039400040301c0d00386d800b1880824a0050103900141a0350282c50000501001845071500802d0b425682030129a9500360003081c144001d4400400c0108081908404d0900c1620310070031b04005074007680c0981546a8600c0201d070826a403400e4161300c4000c4041d505002048400c807642c01c480540700c0c0003455910065226200451201a00f81c0b081764510745105050140c59000c540c0200d601e42c99041c8206440000c01440c020f071a441000d66109049503400001500c030202e60040007813542c0d00c04810115441e40c400340088400840ba071040c4400103c400c042512004159625106641c0c5040401004005113940d081e019400103c010b1104c21072035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 527093417 1250 527092167 527092183
    0x3170a0218090415060b04180b0d02010809030409090b0a05070c0510020a09080a0609020f010c1509020a05030a060b09130b01140d1401151a1902010f020414090711 72
    0x101d0b6195041d0303540e401c000c004500700c03c600040082ca04000812400c800501030404d0710080d4243c4406220901c2ca10300864045007036003031f4054407501c21907005621032846140c2c4800d207801900c0c20a60b5036070200060300d0303254104489070f8405204228031040580710f441d03800300039032034000141005602c4841d100e2002d4114445840e8001681115582c002c030240e0b4010b0100344111140020300c0d0800c80c0c02444000030880c8121402400481651703c90901c1d060010b070003180481d201d02048810100814180708120303040030040c0c4e80000d007607034184014030303802d03000c1d1a0203e40c1e43c10280070400205402042c60300c0d0302982c00006030100d2071030741083e415034110150f0805042108800507500107001d06004112418036a1085034956040d040810a07581c1c0110b10b540b04c5031194903840e0b64400c0108000700880c010300443e0560a206062a031300310340d941c000040e5464240d800201640d0090b00114041e03c0b55100885c25410a041c0080e80032410303140061f03804001020280e04e803020f03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 527094667 1250 527093417 527093419
    0x60501050f0a051c21170109050f130c1d16030c02033709180b010f0e01030f110405010219020d0f05030904050403090603050a0c080a020d0209060703170a0218 70
    0x4800d850410821504a1040c6000b1002c0680c030802c690650000d010f001076919204c90050001c0c00010407043c90700070750340a4a01e1442e03030ae07050b07500c1204207983c07451007031007e41d1035040201c0006a8030803081030164211a0384c001c00821841c001a0800d54264201c1d82642018074007840e03c0c401c40d0740032041d507841ca41125842c0084c0c01c070209403002107120b0000c1002c10000c005201003240d5421031086001c807016500d07a41c1800222070300c0c4008a0700e9100e4024081041500060440c6118503015200c00205040001301e003d1510030381800c4600c151000c280708a4005002e000540e0108180c0e200120f84a07132504c054480342c1d02158007041034a0004159401c158a0041048024003da904252014008210501d401c0c10000c004070000c0c403071040440d10b8040403c006444030b00800503910035a455000c115201c15913240021340c4041c14203890103034280904041030351144010b000542c000ea0310440b0b00a90a625011580300c050103030310260348100848400840346000b00021444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 527095917 1250 527094667 527094709
    0x60607050c0307090203040210020d1b0812070f2c0d21020610050303070f2004090c031205130b0d1103090d0905030f070e041e060501050f0a05 63
    0x4614980985002004155564035010b00c3c4808204294030780d000d58420f90084038210151040040141e0f200c1561000d160002801502071480c203400300e18002a0a03071040b41d5540c6881822401d05894000582d22840028824030800c10001c1e440101d41065080e0008224000d0404c062445111030201603043d0050400100900a2102210780e540c03c1c0c418404606050401e10303e0029280d07007045842e05400003a00703a010819082c00800d84210640c0503140204017185900c884070a9020b22603182180c10380814079424584880c000c01d0401d602c594402408036045150140d400614000c5907010894284040c4158425551036132044484c0d004006942d1112088860040c20040d0780781041510000f00348401340d600020030314036071047ca07516031055a84400416032202c1f9200011140c0758400d40301032041500410100d40c105120b00e2101130030047c0c802810300c140c4002c000540e140c1d60784d50010445400e00e40c22210b14a0401c9030080b48503400d20000174000d0411a0001210344 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 527097167 1250 527095917 527095927
    0xf010b060d09030216171c050a031518200306011202030a090606080d1d010e012a0c080c010c240b1c110a050f12070312050406170f0606 60
    0x15000b40301d600161501d407988407485c1034070b030752014080c0f17440c40c0a500034070b22880c185030820224510301c3c61049005591001c1c506140e821040b0b018141d682d0107582e8800c495840000d000a420700d2140d000540341e100400e00195602034000c0c0010301140303000d4110010410884240c1e442145c419100c20361030001600e0b500e038803001300020071140c3d0004114519020001c01d09480c0001c441102190542e200154101101ea0090142403501486408164012400241076001e00f00b0128502240d02011074030310001480b046101c0100002a14903400c558000d00101209001d0354030303c054282800c00106225a60741102119640d404555034480050b207030010104030780200702010401495460301d81e214000019108010510031210300b07a1006207070b001402d000010784100c80e001020b22400e403200c030040c0b1800c809001c0200001d4081d1200c04000a002e4105401c00180c0d290fa55076111030410314003601428265142100c030350078540810822640000180c2c0c0e0000c400d481d119251 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 527098417 1250 527097167 527097173
    0x40e090102120c0c0c2d01020109150b0108010b09010206010306050702010e0a060506210712051501420f03270b011203080403140c0a030c0201020f010b060d09 70
    0x203000302d07220544082c0c05107042c809541e12540290040a0300c01c81643c1c405e010890030800310800100c01d58140c0e041c0010388060742024200b0701e040b040418000400d650130fa070344d2002c200031142107003203115980c2c5d13184094446d640404090302400722001c2c982d1034141007800107940c03040140f100074200c64503000010202c0d8800e40240b409400080100ea021407054500748014150440d081402800ca0710040c200705a4242c0340000c4042400028055035410040000d640c070019540a4443e8410101080c01c3c24001800c150b008004244070707928046224800d04580e0151443c0b40f5180d04c04c000010b1b00068032030f688003059410203040107481d0a40c4060154044c00d10000340300c50f201401400519802c82030b11074803800344d2092142e603046a032a40041628000d00d202e0190000d02c103d000500081c2c080c010308000b44c80e6401041d07050038a42c0070a180361011011040380040e0820090204650f010030a510700071001000030700c240e0f00490f0100d03081d4040c0780c02d2000c110b92111084800c6c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 527099667 1250 527098417 527098421
    0x140a060c260a02070e0a27030201140a0905060a0c1205060a1d340309030302121602010e1c0c060254060706060b1603080109090206040e0901 62
    0x28051401c0300540c650621440180d15080d42d442040b04040b0340400140840050f8801d4240b0300c0000c041c204408041d04444ca8a0041c800f142241550359443c980403907030782d0300781e4040d1082c54154400f00c2d242e01c4a141c00b6041040c0544058445400c18007603a08072ba41150321082062081903000401740e4440b00020000324980d0b0050b03183c09429680d0512003000c0d01c030700e1403203074480c00d40039009030340107022480d05900303100ea001201c00d05c082c50940d1031314441e0304181d075042e0192070702505103001c13003044810001064030400410507000204c500c00a40a0161206e0740c80a10040d142007164004c120180c81c154400c00802c002c1c0b099032180c2001625410343e403001924401180e81000750710000301c4000442c500d0b0340e040160070300740340c10780c01c09031000840a41c1c000d180405800680c9828841c098114400480340386485036004074891282034040c00c2c404003007540d50f1160565034100903180307560681103100000c0c144030a13580561210710445003254143c25079030030203550314006240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 527100917 1250 527099667 527099723
    0x4a09071406120123130f14040210050a02010209060a030c1214062806030903120504080d050a1b05030601030b0301090206030c0a0207080f070510030b0904030e010c0501060b0301140a060c 82
    0x540403024000700c17410071030154440380d07441002d924104101c0c546080c010b044c0300400c4500039808234503c1d00080800d403052021303003145441400098103103ca0307203000881355003296281900003951154660007195100c7c100f0701402c10300c90710400142c0d40984445ca01010000d141c039016140c81602210169000b10943c0c003215900814050704a0310750100402130003048000354000780700d41001d40d2000b000ca00c80c513400b85601c00e84003850f111289803150701902c0c0043c13541110319a600014542c410140743c0e40291582566601c9940781350842c009001c0b245084000b5000381e00d4500c45c0f80058071084116500700540e1000162200c0755040120b01d0701046400403240c500410b080820310480c0010100c090705d01c1100c0045200d80d00000c22000c43d840d255901d40d100c0941000f050101c0d008580301824104185404c801e04902c070345486007958059405000040c0e4008010050700e409074a24101c0e0352421154004401d01d0420010322212000001605001014a14a001a4001015034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 527102167 1250 527100917 527100919
    0xa02190b0f03010806010611150c04090203070801081006030215180d0302031206181302040615020c0406050f030601060e0a0e0406050603074a09071406120123 70
    0x799903141d1040074410303036002072060512911503c000070035424060318040d01c0c5400e43c4002000c103900982940f030710300d0001600111407918104400f060700c0b8100c5c001184101042d49815000c1e501d4002e0051412140c50003c49415241c07160078001a42c80d00d5015001c1c1100d00c0106450712490352800c0c0c1d00c040c0182d891980a2a403ca130601016008070180c100f81d47c02c0304822809956000c00d0012040e050022110581c084000081103580302d00105a40a0b0002d000002d64036280c2e030507180c041400d40c100f50003682c880400d11059183c00c2c01900e0180c581a60003c48001d101c03804640d84d2034040c01040244103865080a0b0180c0b5052910341c020150380411884a0809003003801c02444e0a488080c001d0041c2c020202d00d00f00f0410f054243c0c40c0f04c42c5920000340300082d02140d403214035654241d0f02c020040302109080451031403624000e20f9190081c00045d407600b10307820250323252910914042c04050082000d60b444014505045440040c80d1400845061800c1e00c40364090f08d0303c403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 527103417 1250 527102167 527102189
    0x9040e0109051015320307061110090503030c0304030e0d0803180f030315040e0a1112120405010f020f1e010c03050f04020d031103030f07140c0a0219 66
    0x2428070000107104440f80043d0343d0108001c4102d05035601d450820341c001c1d010400401001541200340f04061800301441241d015481c00568900190038081980d01480c002566420119413460052000c140030000b081000c1240d00c50070750300c10351240030041103c141c8200200014003414004e00301d8940000b002400103022103594070300891582c000381e808070812200160781d1b21008500149181c000d08c2d60030700640c10765442e607400d903500031080070700d03150465111408190590001c0259880e40d030305c44e000030400350100b90280086030300c0e0588943c803139510030481d4682c0c0f94500c01c100c5066500038a0881002030f540300007030346860503c00d111100c0d80b0950324200b8150740d8450581300c2c074111440080c0184d4603610030482c00e64009540c04400108039030049001880c2c0603180802e8a4803d00342607000c1c180510b2001d0440d041141c0c08070403213400c41c0404c07060540c003040da0600e00c6140550a400c03e12201c4000703544a104490090140c1100c47d5041445070031140b10030000d0543c0441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 527104667 1250 527103417 527103431
    0xc13050603150a1506110705060f120115080c04140906120d0206060411040605030a091103060115030b0a1d09030d18020906030d0c080306010c1401051006020f1209040e01 75
    0xc180081c03510758494000e4144481020170698410060740034800a0003008001041c103010030010540e0144000c000c0d58002000190359109000680d240205560800c0c454040e0360020090040b940050500840b03c8007040180b0014110448145140e00180c560b0711b146e64418020901100b842c020980d4944507107030125452a5001644a10030740e41079034244042550a41e10207100c0c020743c054080815002d200103512812180d00410882c0d005071000c1c01d46140920200b81842000e0304a00485035002480c132080175050300907086400001d87c0c4030404185010003400c1c8011003000503000c1e1245000c081185500300b00256070141038468400c001d10008048190035422070070030200d0040c0d0710000040e549250101c0c000f0440c10315510b8500b0070818035621410f403540700070f011905100c4d8441424022642c200c00985581900000009043c00c0801c000d03447c0fa05150300034001c56020000316580c1140219241c80c80c100e0070b000c00d0340c59160b007100090281802c100c00f66007940c80c21013 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 527105917 1250 527104667 527104681
    0x10c0e041116060f15260d020d0c0206040512030a0801050f01090303120f0c09030b090c030a030f05040e04030302121812090a05060c070f080a05030901270306020a110c1305060315 79
    0x100c444501e048506c02c003820032084400c20f0307848403901d198000243e0400001400350303600442c139040701144014a9149003030b0300d607000601124005c0395051156807000c503945c403000790000d01190140c8400c4807440381651009000078104074180c0002420000358904000c0b41071466000144a18071490703007801b040420307030801060700c0c2c5070344402d6400820301c80c00f18802100203e82207410940c0a0060010b5002d940c074140d400c00d0741507070b1400812a0400001410800311070903c0c0c0900c0c840d641c090798820600c85400103c0c0350250501d000070340003c0e0300f40071010780000c43c0008800c0b0f846070141c9500159000034040c51044e0300480c2c00c01000545045c0110700800c65006840e5050803641b41c0c1d580390409244e4a1142c034000900c0d50b441000103000942c0038503400c040311042ca400c00e044c40c04d89440b039409150850350041716155004140100d405801c102e00b02d500001410003800c030b11421600280503100c2014251941683d5000410f8041d00c040c0440c02c0800c03940c1b1022040390034514 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 527107167 1250 527105917 527105939
    0xf0207060f1a01090f030b0702150106080a1d0703060e030906030a0c1124150d03020c09070e0d11040603170307020d0e061902030c010c0e041116060f15 67
    0xd0b02c55003402d945040b440c640c02240d02c401640d028080140c00d85046590f80040c10102804541c1588150b404441122441c005000e010742003d43e2140864200b00304d061043d10050400c038090914841401031001c3c1c00003941c2e10480c0d03048100415506540005542503204204a6a81101002040200d2842d05800202a2280700d9660303013a502c94030801c10303480d6171500800c0e0240080140ca10300d09854100138494010a4643e0702041c0d0004a0b00003640e410306400c4100d0141c0c10050030074003245001c450080c1e2101603400d10070324900750500043d03a01004003c00800b6056600c1d828143c98449910000203154419141480d1918210303c0100f9508101c40301c90051268000c030501242c4100010402c04c50081c00d0682008031080c81c0401080001c2c102508500c001d000e001c04144003402000c00c00c0003203880d4201c000c80c11100b80400e4030302c0c0741e050411010007080442c1d244420309205e24025070308800002103403000800071502a25074446078a40d83c01c941400851a05642 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 527108417 1250 527107167 527107181
    0x1e22090303200a0207031101030f051302010822030309050a050a0308040506011202103207051c020a02010804030c0219090b030d050a11240f010906050604090f0207060f 74
    0x2040400b40c0c024030003050070481d100780007003500103800c0640108000b4280c03800d43d45000d40141000300c0c440000e41151070454408450000d1070510180c41d0724103558000d100203800c080c0c0c010003500401d4420381002546001e004008041541d04d1004805000007807007099403003544101500c15803081e6040c0184220350a6905884074000c010000811200d09002114020743c007030811b020355494050241c2c0c441801012104408511800160b151420500881ca11f41d0030400c011380c580100e818007500d0840d403000400d4029403000400ba00841d000a98646241e41c240303004101d641c0c60345011100c00c2c2a0b1a07009401003840440705140200c425923440c02d80d10000c5041150994020403d50b60300b1005d407104010860030020780c45403621404850501c0b071000c0049032510f00d2194071000c0c2032007609820a01d903030301d04000e00103040c404040260040c90403040500506d400c1c6030010307102d84140c0c440c400c5000d540d500180a4480c1c160140c4907501e4000c2c404102c000107440d0128054920 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 527109667 1250 527108417 527108441
    0x191b050c07091503052a060c160801022508030c0a090f0f031236050303030f01142d01110d030b1918020315100c0309051e22090303 58
    0xe113070180c4a100014180928201061580c101482c40006d82402440c4d0303c402d0b400c00c03960040800c00b1910b01b107220b101400500600e000141c0e5003c00b0500102c0b1303007240b50100c100b410f0030503411001003520601a69080516178035032995950081100361103203d000c4c1c0c8206040703840751030002130000e40000c1c0101100e000b500c014603000d41800c000c562400c92078088221103200a0041c80d0320207901c0880c0701504d09401900001c0d29292400245990401c4800b20300c07184030305005004d0b410941c4101d040c03680040d60001d0b2802041410311440500344040042c0103802800056050303031059105c3c800e003a1503401510406080300c04014041c141d410b0305180201c0700c0c0020f020240c5059041c42c0121481140d5100c0c085413503980c6100654000f1300340c942e5128207031070300c2c925540d10b0850340700514600352590716028040d4680070300b0000071503114070b00c50740c9000b540c0602d00510717000c012100c0908550000c3d14848440c065240c1e06083ea0418040e14a0110b0020405070983d00440c10400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 527110917 1250 527109667 527109673
    0x40302091602070f050108040303111c051014030a0609031403130b060105090114030405160e09010c0e010503060904030c05100b03070b0703020a08250803191b050c0709150305 77
    0x2d01c0300c42004044c003a034400c681c00220014009808a846544204640012580040d150401c5a8207210a1f00c1e0004c404005056507182400faa84564018100c000e1503103144000d0020504000251500c41380c150241400751101c01c1c03081010f11a1102ba80d1030031401140135140d04014980d542d002e0016a421120402038001081c02c0e0f40c0906c099601101d0142c0d45e41c1a000c04407841c9111a07000034104481501c10303128407543c603209500d030003409455840311400091812407055400e481c216001c80090010360703102d8240d0740c1d9110080707030b45c049029540c1c410151100e00e13080b10490f20f0341c840034180340120181c11043c0c0205800007070615804504691040342c9507001c80300d017072050020040144e400035580e000007036403c4000e0802480c1601d221410060020f00c07006210b140f03054100c40d41070b400410800c0701303a11400d000a0501c207040342000590170307035940c5180840005664a003030007000b04503003030451810030211000d44110a418428489901c4142075814400e0100b11440c1c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 527112167 1250 527110917 527110919
    0x50a0b0f0609060f0f011215090c0210291201050907360e0a0c03050109063e070501180203070b0a0e01030c121401031401020903070e0c04030209160207 67
    0xc1303029003a42d4101c100050400324000c6040005455030781008a500d008075403502c08030710002850390310100c01492000700108144030491402070400d444014070308801840d1919280303001c46510b810b001c0a481500e28502c542c04808005010441c0c106812105503080004011410301c01007a00021030300344029085405200d035000b400c44802603d05258007a4079554000c4080341d179900b06403441100c030ba055494054154a514003038402a800c140c1d0f50369100c1c2604030030054188291500c0b0b8036100b4100c48260b48102c0c003005003d40380240e40741c04070398030000741030b99140403402c6030845540b0500070084081aa07030004092010308006a1090140c160001204000b1a0490b100803000c4d03901e008604010400544c010960100d49000304071114481803503945070391140440159081070244d0007985149001d0300c001d101c0742408079030f0707900601a0000f5a00d0004140c000c2d01e0044911545950b68120aa0319074011548040d61100d000400c0c81990854001210402180c0354240c910315 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 527113417 1250 527112167 527112169
    0x1621060f090908030a0f1d21091305040302010b0a140f122130070219020103090f050a3801170f1e0708010c0912050a0b0f060906 57
    0x80b900311030003030008041080000d4080f48158820104c0080f04800040d01c19100e00601030500600203c645007544510702d01100809603103400003800c1c0ca5141d0686c581415900030402050030340130640d010300e444401143c2003500079080303070042c0c56010341020001c980e2136151030444107072122001c1c0600b001340c9001d891424085000b8801d818280010070400b40800380a1030310340481c402c100c12584040c0540201012030401c0084125092020501215076100460388145409005802954045014805007040f5070310308512641d024240040c00e040f20b4140030307a0f209040e03140103040e4001c40929208206056100800300300030310110020300d903005880e20400760b03040340c50301c0c07190540500100501d51803040c100340411100d106407480e0340b200340c0203103240091168542d00641400344505610010400c4403400502ca024001d0128101e065805020b0394098010f10960101c0010301f2420b02108118900d0301c1c80d0301402150b0503180444005103c201d0659000c0d220700d4001c0007181003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 527114667 1250 527113417 527113421
    0x100c020109150510030209151c061a0306070f090308070f1a01080c060307110d0e0f010c120c05070e0403050912160b03070c06050f07020708060f1621060f09 69
    0x410740c04140d14075081c0303085400b00301c882c0c7c0c0003d0040040340500d0f0380b031003115212075141d0b41c1e2500c1f4502046c49040132a00c5c040c001e44400400340e10700254591810103543e80d00107561500043c0a0800690790808030108841c003c000744c01c01b134404035001441c40c04022520700c480c2c580134014500c28510070404040b20001c0748081c450b049171a400094500d80a150a2009540004d410f00f407080b01150351f1480d01e400d00e091010f195000c242c1000c4d144039541840ca4882001c2c61003441c203d40c41848a540d00d801d0b000074200c081d41007207980c11743c41e0100b00040101c5409022221440342080c5080d05d00240f003a40481c030000d0255482d500d0454001e0000140b00b2441484180310003035907400d0103c00b02054200070115070402c840c402001c80412030a1149601030f0b18540e1000001c1c0c5462000a4900b4025902414a6510040400002d03c0d810161117802140707007080c4241da840710400403280d158140e0f6800b0b4000b08185c51010740001d20340d0060003251142023540403616a903040c0c00d01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 527115917 1250 527114667 527114671
    0x93c03030112080904090b0a05010f0501030b090a0c020c0d080d0609090f02010804080405100806030d0503072a06020307020a0302010b0a05100e060403121115040317040302100c0201091505 83
    0x2c010b2a010860b0001800050140c4078091000e000080d64803855140c82a00d01019101c0344112a900e000500c0411901405000580300078202401000a26000f0171840300009000c2c1c1070307244c1d44904841c1c17001d200344040c000a0500030000c0d601a09241000640380d80021802d21030f46141c0540040d00814a0241d104500e0b0010522002e54440b0740040d0b51081008104580e0102d00300000302e4180d40700c810614030040b030b80c0e40d200e45903d80340301454544480780c0300c0d1406202c0c0600420410540c041d00d407001d1000d9143c0012403902000b800d00c0c201448601c4010481800402006041580000c20604160081d4001d02035195080144240403041e80181234003c1440b03000c490a181c001c07a11520202c00c094052490309070b40740c590265015403d4900d01c0058510152802200130800490380d840802840c00046805e0664025069102043c1004840b650110018041c98002d000307043d540b140e03c8c0018070021281d00c500038020100c0102c2150100700e40080e1a0304002c80e841858 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 527117167 1250 527115917 527115929
    0x1f02060114060d0506010309201c020a3b06031005010e0c0c120d0c18060c0f06020705010c1e020304050906041d010f050a11090d02040203093c030301 66
    0xb514182158412030060a0000c01003814151108a80030000d01c00305984482d40104511034442010b4801c00c02008406440959203100502c02c20880135a40701c04c40d80d003c94118080c680040311428559010b80160700300b1243c03241e6200102000d40b12a59541d461042004500360344100081d4820102140e80a004e808810103c00c00090140d90b0a000100a07600e480001c654007440070701c40c1c5060f9a4000100700503c41c1d150840307041c3d156048800401140688000c0c0e086131401c01000a114015101c000740c0b40c7c441620200052010320343c1201c6031242c00500a002e0380b10354101c050003441071800a61082d00101c1c0c00e0f00c409902c08010b03941038030320040004c04191100e808000c040c2c24a102914901c81101c11103400c1080248181020315035035200221315454446d502c503040f5400d0164000c8410030401480c00d440d5111f44103030440b030f50b04840c0180c5036203d04031001d18208150309120300000048c180d0018100100c000045843d03408800c148410b1400c10b89151a030000388100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 527118417 1250 527117167 527117179
    0xb040609020a0e011803170a0201110708220513060602190c14010212040e06010207060903020303162603040c1a07080c0316060c110105151e1f02060114 67
    0xa10950300c01c0c5079408050755003000d0881411b81340d071254a41650b54264290342071800081300e904007502070090070001081c007280141800c900352540e500e107224441850134200b11107070003c040c03000100c620101030f0401500c2081d0095142c2c8070070f0003c1c5460f0084c0381c098031454117544120b00300c81500a80250380400d40c0e0040c10b1400c01d01c4405110b00351426410750103008004c804003652140600011300007406040c60a00b0120006030400c1c00c00d400907810009003110900142e1000030889443e80025107040c4001121402d2034103203407005501144501500c4428481481c501402860280d4024003100f29005d81d1035000314030780c420040e00c13904e21460030701407840458000c901501d100030510f02a0782c42c0ca17119205a03004000d41d172604442840c7d0300e1545015841d1301071790403178030300c03010030001c01c01418451800ba40840b54643d0040c03041801c0c50103205117a5400e2014041120041c3c034000c13a080420481407100c690640b04680140701c1d070300001a0813421220241c0310244d0140c44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 527119667 1250 527118417 527118437
    0xf1118150a0e060706020a09440a121d1918020d06030b0708070807121e09060203040b090703020f0f030c030d0203031005060915091c060b040609020a 66
    0x544208055000982d0f100200340038500104400340020546c146ca04d0b81c1da28032450500c00410392201c1e5041300e165040c0501c2100c01028400390403010074002d80d20843e90403101c0380f02d90340c81c0743c50940d100080540c090f10f1000c42c0110b40007003c2e00c42085107440c01250344150b550a1005103511104120401a400780c070800400d09080d03845410b4070302c1d28a0240c0b40c5502c5c90400c0c025a180c3e40c2c400c451500d0345808021102c1d90040c8070310741151092808090302c0c10724010080c4207841203080b01c146280e6030b500c01c0d22607100510a680c0c8a490000c0280300b40e00d01410044004d4000b11803da6140000c0700c001340d154800400c0000039203600400c10b0804080c004140888256410401c580500c1080c0c0500007a507000c100200504001d5401180c2d00d01d010b9202107014000f60303001a000f00c40c2489119401e60b030b0900e80d05c0710b40d0408054140c40d0341f05840010700c4060003410380071854808480030001d220035504640c81d12441602c05110140d514840a4100e100b0b503001400000c0c0c140304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 527120917 1250 527119667 527119687
    0x209040e1b0d021201090308180303040c15050c070f030507050a0807063905011808121b030a090c0b04031110030b0310020d0606090b0403150f111815 66
    0x11010890b5030015003032000032140094081d00b150a07108041d0b01042e4035104102110991032038400302c0c1d031980c40280d811410103540f100b2a05a840c040c0b04201c0d400020501c404900c0340c0150b84602d031140d07048803007965442d2803606046030980001e48040c05038840116450410b1118001128440700c01081120700e000c10881d980c00048002d8880c1c50101c500c500d94030000d400700d80100c0c000050808081c442c1030718000f0b0031902e01d5081e40907003030400c440d8240455600015200e514100080e03440d05a901d400c2c03610401410304c20b0404400202005010a0704110781c4008003041c49081d00c0d43d80c10ba2900942c20f403c3c05284801441e458810b50104954145032600031400d140c3c07800d010401c0303074045000a040000d111103203030a0710344c040380341700e881540b5014400c003c106508140c01174500704081818940310f07500001e04004a2070003480440c01d4181c0c42407004920004003004041d024440301c00303c07640541c3c002c03200340030b2101010001d031501000c2d000c0049404280c5501c9c10403450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 527122167 1250 527120917 527120929
    0xc030f0a0f091a060f030706021b0619050c0d05030f0705090f04060b070b0c07080f0c070e010f1404110a0e040207150905070b030f240a08010209040e1b 67
    0x1129101c6581d00c80841c0d030b00080c0b807407001c01403030004000c01680d2407030400240004a9510302c80c42c1e03c81d41c005041000055000700b1000820354140014103602030200010076200d105200e05000d1300ea10345101c040d2080d60210150000200d000d09898a0310f070b008004441e03501080c1c50001180c403e040201c1c4155002e44000c3c0068040a44583c580640040010b02142d04a81c451003c030315000a0340801c00486180d5191721220084402d0700380711841e192070700c482c06000007808a008000604074111b2004204581c018100b40c00300c404690784a00c494a1490994440c02c41c0c032401c00700100c19989004c0c02040044a400e200d000d0802c03c90400849141029105198000380e0801c4a500421000c140e08110b60034903001c041031007845440d01c6450a105680b025200c08024018048400c0300c01c01c20b00d40004000f015032030581d030318540e603e142a00e070100150b40010003120010340c03510103401810103c001100d0070005030540d5907000e0744403451100b001901c242c0f240254003082c5006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 527123417 1250 527122167 527122181
    0xf0801060e0108090a060c030b03010c0809030702040506120601060e011106070f081f24050a0c06020d06050301050703050105030705030d20011e0b030d0e0d0303050712140402090c030f0a 82
    0x1390382264203112584e10b070101156400042c07000042d4032003600038040e00f402d005141c200541761600c40140d24140079929224024484000d100d43d40f2100030640658540300a00c41001054080d02c10b513595844005d800e040d41886614003040000d1290f0b5080e01e0081035091043e00c868940d020310b0482c0200441c1e0202d401004840f07510128104080000c1d0f100071b00301d000c0c10b241340c01070708101c041c0d40c8055046a481d91114040007400c1013409070302c07a03004000840349640f0840143e180d0100e849084e0140409130004c41d055840c1501700541c260385600581d048903130540a80e0b4510b5110f6040c50340f94444092011b0104084403424110034000004989910144a0002036030038041005164000940e007082801c440e1601090b01e000d103424040340b0340c1d07001070f420454842041c0c00d02103404c0441c0303540f000e01415907600015501c1d50050301d04e81f000c0d0410103c00c02c2241e507940e00004084405980581c09440305600040401480c4001c17039000340200700d08815580e640031545d9002d400c0e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 527124667 1250 527123417 527123431
    0x901030504021201090516080c0a060e0307091112011a18041b0503011706070e04020c07051216050607050303040b0903070b25140a03020f070218070f0801060e0108 72
    0x40180f6120803503d080c07261000d1207100e00302429a20b503090b002c14640020a411003a031076001003601031060345d40c80700854115010350400303003030041d810705c00242050b60035480902d0300c500f00560b040c40100e0303c0000b0a01c140e44414503070143c2c2d0321620889294112904441d030b80103000c109006010004c640000e22414005001050310080181b9054006c8400e0510f480480d00120061040c10100c6102d80c4031481140300620b9140f500e503800500e00e2220404845c01580c1c009101c0b01c003041700748040c0000d0080030300301410800c00300d03000ca607075480c0d00400380c60803015000d80464241b07070103001c54003c0c07030b0044021808d41d03e03076468201c10303440060301d04c14051104120840001d401c0803841d41c4950310100c0300308102e00c41c1d41059590100058415403c03c02c880300300342c8501e00f22a058a0b0fa42602d07140050b1140c001c8400401d0600c510200694000d0004020605608803440c20303501c940700c141d40f02c0c03240c859404403c1c0ca9804080c0180c00c00b1504803140384090f03520074940742d0b9201003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 527125917 1250 527124667 527124679
    0xd02070210050c0609060601080c03090c1005090a080303010b041a0c0a0b1b130e06061b0a05120c0a080307120f0b09011a04090b030f1203060901090b06090103050402 73
    0x20540c0d0020381040385584818001c14000318602c440d40307400b03000031070f071180d1004060589458410002010840000c0c04920100c4011001c20594181000400621900a0401d00440c0582030003d09039400c03240c40c15101d100e1011010a08800c0441a0b9048035440d01801d81440d04101c0c200301c208581c4000504583c40138404040036550400030002842d0046004080504100300009000041900c2c0200c44070410042c84070b10f000245441c10442d581e801c04d00040d41c41303003000500380c0d101c0d04554003018580d0000b03d01250801080c41046144200304907468030410110803002806801c0b10150756410042416021803040300c000c6920400516000d130101e116200f00504540380c0e0913401ca030131079a441d4550407a091103050070b400b400c05100e410706003900d00107200d001ba21841c050700316403949455100d4443d440c2000258650401d02e030554031803140440040d070443d041100c90920482d003060001814041e64480e0265000c4003074078807490300d94008015406040080d10407038200d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 527127167 1250 527125917 527125927
    0x718080105191d10181a090c011704020405071e05040906270b03010225050d020309030a03181d070f14040e040f0501020a0c0b06041a211b010f0f02070603020d02 71
    0x1c0c00985080c407071001e0003c04442031f0070304040780362500d001c0d0741c00c45040c42900d480d14a40d11080400040e0b009604441c0401c5036030355110f0840b0310511800300140e0f0b03144406e58140c034007078000c3c4c0540291242040104070203641d402d00d04014150a070300c40050300801d880d40381d090420302d400800503071310054000751070110040e240c0ea100328a401081081400d41088602c20072a040c03000d41181e8825100940c1050340e20000280c503030402a1004041c007205440d18900442d0340403401c0000c00842002004481c500c00c020131940308115008800503001c5407428100c680510ba2015410343c0b0031804600b4a410220031100c140b902820644061112001100c0010f03000d00062801d41c20716500c550312440c02c1d2030301d60a0a400a0011889582014080303a90781e01e02c6401060107202c21202c0241c503000f00488100340320f412400d461020b00904200200d40500540c2e05c41045000707a0301c0c51801152a00101c541a0320040d8040c0181c01101003007000b0f030300c41c1e00a0800c050400c1c400510300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 527128417 1250 527127167 527127173
    0x10506150d181a07080c04051309080c2b0203040320030d0509010f030204080634020a020f09040302060c03150d0b0f06100203030718080105191d1018 66
    0xc034009001242c070302c004011003d24503002c412102e03400c800103091804a90400320103c00041c020741c014140034100714039001c0103c0120360400940c994015031813903980c400b0303221290303100c0d01c10a0703c002c411420380c2c40500489140d080d08100c040f01d20b90246007480d09558401c8012240700e503114010440403418100300c1d0b6020300c40482030365111744625588010721400074210003000c42c3d15100307052043c001007140c90b00c0400c900d580504140d040c090080070001094281c0300751b1008480001170b4102d54098010340000d00b04030228000c40d560300c910301e00f82c3c0800c101075104440040042e0080c42c0469500c50411010315044942511281c0030740c0030490110300118440c00c800c0c0c0e41207041200b441281c83c41007210035040030080e01d004110303d11198001e99039200c0503040801300480200046481882200140c0242c401103000f40301c0350a1690300d5480551004a036013400340d02d0240345040918080c01c40442d00111030b0040c0003c900003022080c01411851129140721104e01003807000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 527129667 1250 527128417 527128451
    0x130f06021e19021c0c0809010215041b090507270b0a08100801020a300501030b040506090304050a0501050304061b02030c010c0203130302040e0109061a030609010506150d 75
    0x4049032810030b00304100c8500c8002840c1c501c0b62030711100d0a44050720b00c10308056012250703603140c0782c0110f511036031441040c00417454105d982d030f884010340034000141f00410004202c4202c41d0042d40d100c01d00c0c9203441e11089000c542c1c080d00c8407030109100c0340e000600c0f1004070840f200c0303010340c000700c0c03850b030550320b007162201588140c0200001030700b03070410010f0301700d041c1100788040c3c0900d90086081a000c00d0380035008403281e03a000440035048407400c180c000d28164a55004003241501070004d940e6034031f40100a640c041d5400c90b068050100001c103545e40000a840446000800c0c52840c1407800b401503e0750750014205680442d1a0004d08121441c00d010030300d0280d81d0755008540e030340d01034030a40703003100e4506000100b150010011504000800082d030b4007901d8040b10001008135154460600400f40342d400100300c64201402502c1882030211204c030f80d50001d8041d50701603560700741c51a0803a042241d005600081c506058100c0c80c051300003030113031070020000006015541d4150045 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 527130917 1250 527129667 527129677
    0xc1c0309031e06060b2b0906060902072a15030e0f0c0a1703040611031902031e0c060a05092406010f030c090306020c03040b03010b12130f06021e 64
    0x1c0300601c2e00301d5910812807a4402c110042c030405009a00303140c140d50040c440040c01e400d6070701010342c042e1981c00c5041d035150311600c41c07660700400400990750388200d258065084040b0568420403c0700c0d003104c68602170042c00c280d4012204031204102e00300105080002d102400c14420144d48113148074904004001226180d09400000c0006800c0b1004101c6907807040d801809042a02d0440c5d0400800008213413401d8070410f0810b86230300031500761b1245c9540269440d80c80d9611410034000c80d8660080002c1c000b44080b103404007050b940d8050003002c14030851041c22034a620400018102000950200d43c01242c29410349d041000100d50001d01c1c020203204c1250040f103c50284501c668000e4580c8030780c01c170b40e81014030465003250300142070701c955071001804444e000038020b0050710b020300449028155140e4107d03240c0d611050403200d80e8004800702c24284d4081008540710b5401c03605c0801003183d20990101030303154180d075004060b401c04a843c41000c0e205062014458500d000541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 527132167 1250 527130917 527130953
    0x111305040c18140a1d0609041703040b1605040e060409080f0f03071706031b04110c0a1412030c0913050103060b18010503100e10020304030c03020d020c1c030903 71
    0xc1144007100342045030141309944410741d600140802945103001180300103038807010881d0302d12a00d90700e500308814030301c4e80e1050071070341440008104000c106041c84c4c1320340140c4403003410302c0c039004040340e003550188100c2c003440c1240f0811900088485c50560070400026104020160030078540c0c00e280320a42d000440c00410081c0c0c00f0081100080d0701c480e401100351000c180d000ea49040400c04280c40780c040b450803503070441c0ca80c5801e04542e150b5401000080c0c40c02c5406540d51180c1006c103c5d19800c600700202c40703494002c032842460080c001a8080402c80e10240c103441d6442d0003034a46200c0d804094240e8000d00800c1e52034100c1030b82881054001c42c02808086030902643c420424034070700c59105880840d180f03000600198400040301e480041c012440014008122010f80c0d03d041103c0303c0c10080c050000042008165000c0b407850300d8180b00e40c08680400304d40c0142a038843c0c4156180c160465442c00705103440000d10072a03941c11034081c2c1086200c01e510303901d4601045110b02c00314 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 527133417 1250 527132167 527132189
    0x4030f0e0f0a180e030f0c120f1621090807080304060f051806030a02042c0c070302031303030e18070503061c061d0c03030301030203120304171903111305040c18 71
    0x1902d5003200380a035141000b01040502e20701900044010012b02aa081c1d40e4000303040c21948004001400d0b5220044a442d2010a1203d091145004200d0b0359540240010b034000d51000041c1c6440000588081d2000780e2111540150038200c2220960482d00f900d08040b5070396200c2126648072080154002c0708607000140e40c485c10b05501801d03040117050147d05040000001250f2990505007264103d101520300300c0e611242c3d410128030314040c00304440020300012100004041c0c00010b0a05c0c24036096441c0c40d0003001120080140860480e04200410001c04c00500185095400b0031001a44600ca03080400d103507450348000c8410748100710a6101d542070000c580200c0800144140c01c90403002503203150b05580c0841e85070300c0707500741c40300c180c440100100703042008080c40d00421106080080d40c6540d03204079088071141d42c40408a000ca40380000d07001e550ba600b40112030340c42450b4650340300a2881c01c0244801000840c24081c10010a85501100f07d604945070000402c00c594071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 527134667 1250 527133417 527133427
    0xc0905090f0a050c160506070e010f020a02091009050a020a0807091406281107050d08040e04020d081c050f040506040f15020403061a0609090c160b04030f0e0f0a180e030f 75
    0x302800001c031500402d818002f28004084030703240d00240c2120400d9060b102d00d050703511400290480c0c00025005903003c14240020804c0106140e409840042c41315510504d59840d840c00580d600551030091070b000c00c407409a1300444c1c2c01c2800040917114100c078081850100000440055445240000e00020b00c44480304142280c0411000e005400115030340051000030382c1d03c00101c1c0c40b65204210317175080c1c04000501555140040c001d121074020039290340e51904003c0996141e000c400440444c11300e40004603081c00e900d0b00c6601d00c81c035030100c01000640c643e030b11880d0900074000700407144405201e40034200701e8558005040154440d080129151800c0c2e011024080b0760b528000d409040207108a400f15503c8000040c0c0040300c4401c541c1d942c003902d95604106000195010b0500101041031000b015400020b05961041556500d501c03502c03040d00700301900d114401055406140707014144000e00245140007120b110710480050350b403500380c8515046070080c590040e020b44011035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 527135917 1250 527134667 527134681
    0x1a0a050f25140705060f071107060e1201060f060c0b0f1302010f020106080714100c120f0e030f0a120201020408032b0603060c0905090f0a050c160506 66
    0xc0c0e040310600900580008240700080d10440c440c1d18000100301d94070701d0b0154000e41860403a04140d82210660f2514603168400c0b40384014180c0740c0d94001000320840c042003440c08200d0100f950215a0b9043d03030502000c00700b0101114200241e050b95590f89070005035000c81e402410300415585e20391030343d41c00761401e015450090060268480c0d502c1402000303441c0a258812401d0f59509003060101100d0b1024100d00501140d0088100c92280d182c01041b8944206901385030b4910460700c420190001c030782d00b1115105640c90003000e40c081a05032441d110300581218a20b4041c48c50300b8164420607a00003442e00c480e145810806030080840441805004250084102c0c1c5600003589014901010305075203205182c20340d8946014803480212211707909100d103000c60402c0d03001b030010a8503030802c200104200c10380744010903018900011141010604144111104036502840d50f80318203402c0b000d400b0042810f040400200090903519081018442e245401a00102124a0580 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 527137167 1250 527135917 527135941
    0x51b060108151b0c0f03030a0915020901120e010e010501090c1e080a020703030b060309010b09061008010506130b070303090b0f04051c230712170705071a0a05 70
    0x1840c0c0b0610381a4020802490741d01004141a00c24480c03003240380d50303008a1546034103005403030214241c2070000105104001c08980c0000c1142e500030408440c88a40030840c9404a11031004040d0101e514850b000491021030b9000008864018001180c4501ca400c50749003100c2c8241c100d11021640d5000b56583d0b194016035074612003080080c4000702c500314036005081c00c1d0004001c0b100702a000035044041620076006a80d03102c0028001907101d0805109403800f0b0303c3d00d02c0c0766902402180c000500b1515000b0010380301e802564840400f00d900700801e225032035000d4039141c4403c0000700c20001c0c186c9640750081c01858026071340020300102d68034240d4940080540013620a120483c00d100108001080032064540410040d48001403510701c10703122826580075443e2100160000100300504d1103004100c6284200c810001060001105032440070701c4140c00c15220580c100002c2041d40200010100b0783d0250f01c0c2c0303001905442c050125118401c0764950407158482c000d01c00079409103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 527138417 1250 527137167 527137183
    0x1d180a0b01180203070504210b07020a030f030c0c080c0f1f0c02070302010806010c031812050c0406080717121b010b090c0306010f090f090e061b19051b060108 70
    0x42c50194954185814010803030300960107050300d03518403c08440074080d0010f40c3ca843e03899100d02d11100a19150304007a4071030706500800c0d0302290700401e10610320b5110348100e03d4010440e071258005910305448008082d00514050209071140446840d10400d040021485100e40e0b40885c986032001d100410f400d070703100318a000066500c590401d000607a040040d007a4014420320305150040f0382810100d0300424280b0001081c204ea0200100e100464543da02140a000340111291404041c0910040301c1042c070650b42e068002034418011041c90700a070901100200c0200c03040540700c02102c8510f83d001d40555503004070f204040401280c001c5c003c4c64a649012038898201b032500501700c03c10b0384801401c40d410424900b49110659001c3e0110070041c241354200c110740740d82c8401c90040108002c0031725550a11038000065a0520340d8401c4002e101c1c4105e45890610000c1a00c2d50100c403183c0c1110020b001043c411074941c0c00d075445400811008240080840d545040207290401c444e03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 527139667 1250 527138417 527138459
    0x7301205010b0d050a02130605030928080a050c06010801060f090c0e04020a03020c0f07031b0f18020408012f041410021c0e191d180a0b01 61
    0x30a40104030240c10341003611503000741d16a02040555a101c0c1c190001d10034105002103000c500709010070031a9100c1c1c0654440c03106135085070848904045911701c811032140d0080641ea42541c040000102c890000e489582041c2c1401170a04004400c05030411601f40c02400c03a5079501c0008002d5200202548001800701c2c84080043c0d121600c0000d140003208468035004640004050310042e101e941150520103001047c2d40444c200c00f4011500c03005188000e458054200407000903000c1c1414240003100d285e4214056014a090980102c0340003000b070039155a6030071f000c0041c42400078018a50845074075031501141c480c001414003800406055001d40e0041d0611060140480800c04420144001c07101c0ca520703881c40c1d00f8200c0c07504040810100740d80305299010685945c110221900e8124200c4502042c0744a04100107915001d178418002d103034007800809001808400d0840c0e4120180700c80e40f0809070f60318410300e2300c2d101c550301c421144812000d00401a00002c90540080102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 527140917 1250 527139667 527139671
    0xa020307090b01080a0e1906090212030a1209020a03120809160605040e04020a0f08030d0b0316031e0206270a0b09101806030204030b101a073012 64
    0x12002c40020f2000200805d82000590364a00780c50340703072400b0460301c00504c1d115a920007154170f05180102c05001c8200d422406080d941e9003080c4001c1011066444040469a40d0261b0744540074030f0381c000d46046041a600114886000f1001c680e070b108600c80341d40c9581d103030400c0d1804d01c8003001e49000c00c408416640c11131025418810b55522104580440d50107500d441c0c40ca495074000500ca4080c107611100c0315070802040010781c518040b0282c002c0404180e4100144a10042815140c071030390f42a54400c04000780c803e200007807001300d00c030000e52041c3c810401140c4030395010840e1a4009400a83c00b84900c9012441d2174240c10004800f8003c00e440b5003580d5031414442c9449401400b03c050f10031340150b2600b2000500c507114006c42029500884100642c1d41c3d40042e000790301a000941d1441111400a84003009000c2c2141c1100d400d4181c684005040880031042a0000d1004031010b240400710100c0d6407655844120303250821080350100900a6100649140b56601c3d043d441c0c54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 527142167 1250 527140917 527140931
    0x60a0501030804120305040b13060906050403020f04050a0f051f060c12200114010306051503060412030f0e06010e070212091e0603041101081e011509080f0a02030709 73
    0x282e50074090b1004c4501c03802104101100c1894152410b024503040f03030303d6402000c42d04070010010540c40000705c0ea00c03074403072070060b80c0c8402e4116214440c0c2d01010390410404100204542002c5d44910380c0800c48000014500d04030300c4141c01695419500d0189015030365043c10000c003d06582c000060100303080c00f0030384101554550004142da0202d0300e041c03001c18040d9034104142c0008030350f1008a00e8008204001d41d083d001c640c0900e081c041611401d18010020b184c81001100101100300014004c0c1103e543e10354980d104101407407102c00406480340c0102e1403600c41d9010b030759201401e0401901172503042070084000c0c0d8030000c250b00c08540c00b5100c01c85060462130219040107605441c1c12480c0b2048080145040c0000d280752900010008200024422410f00281c3c8000099940840c07076128502d4212001c3da03029500c0c0f82d240712010041120710114032900c10220424108a440a907881820f24102a440d102c04e40e11600000c5040d011807506116000103004051400c02c408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 527143417 1250 527142167 527142173
    0x30d02030a1403090f07060302031e04030c0b0627040b130b010e060315010915050a1d18060106092c0720030a050901180614070c090207080a02060a050103 68
    0x80b107101e0115181c151400000b1400e124414444407605c5002d880445d0030556480320001e00075441281c01d41d11166a8600c0070f011050020403c60003203400da42c0c0d8040401064441a9108001410650780510354007000b075a44520755007089201440e00010302240e00c0c05007419004d4190041c10b82c5a56141c0702281c000258079500c075941500d0310003824403225910007006c01c1c50803911409603000900d004000045982c002d410400e05425940404001a59107209100701140d040c058901011010303406503140415484003964070040d0303a0214140d828601410b0b60400301d0030303001080000c0c500e403410b03c08a15110200c50100011048081d00f40d01e943c0c4d010542c030034010b0500000c001c041070241c0044203002d45000c1407403000b101a2a603459540801615580c80118240e020901012141d080c065041041500711445a1a0901b07000210034a010396680300c90000c80c0c51100000000c02d4030203062015012142c03007003807456174072112028068940f00e0014464000f41d42020014800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 527144667 1250 527143417 527143427
    0x102040e0112050a060f02041401140d020d020f0412020a0b0c0c010c030c021914010519180b03040609060501140d08030a271406151c020d11030d02030a 67
    0x1180c244400c200035009440c0ba1050814103607a00160002e800e001806c940d4a01c140c0c010800c07180c1210322144411000070045d541040303000141c444030319051080360f03020b02c0503400822090504500c014541210702c07076a200e4540083e0010031a00e13041080c5401107082140f0400060b00c144d070401401c0c524000001580c80c06007003003c904002d204115442018090a9500f032895070050803034540f00c0c10104513501d51526881394090401c07125070680229409403045031000045541040000160900c2c2030703483c08120002184003458100c80010003a10500156009070321400c00411034003142c1c10110305440b01a003128100d43c3c18100030f501035549050001d0a401d5010100d59101c3e0741d0030218400402c0140b50740c054903035072000f20103049040340720084280e52161f824502030007a05200d403503552004a0302442c984501003025030882c0b8003a150813a01d000760011080d40320000c4d40c042024410b500e07000301d03103000414408513104e180030f00c806204105603100540c205608008003c0c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 527145917 1250 527144667 527144669
    0x1107030c06090602160312030f090b040b010501030b0109091a060a03051504060608240a030506013b060607140c01090806100308070c0b030f040b090106152f0d0e030102040e01 77
    0x2c4518018104074407098089e401041408240e00c000f00181d180d103081c2040f503888210340456003280b40e04004202c643c020311603045503510696070080035a04200b0f50b18020910701039103a2036201c8808850050390740d05001003140703020701c0d40d000c81d107414200d5040c2c00c5d8980e904240303882241425418400194000541648030300504120345117a2a4025070700d2814880c91503042d00711000c800d011081c4a0001204c034100d4869040e580c00042c00c500c040c0d0300420020561281080c0c05a00c0308010505581b1103641240c8000c140e54036200095480c0c0045002100c40c10343c50740c0103680744600b650303006581c402c02010701e14050205460041c80d0031103100040c2c00014091400481d1040502140e1035142025002014042c0d80e0307800c003104907031040b68003142c040314100390309000075882703641c10b000c0c80f0221041c541101011003405ca100f51014000741e40d94580714051020160149032005802a048034883d00203040f41c0e000e11b200040004030382c1c80242e80240e00402041001c0000c2014482c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 527147167 1250 527145917 527145923
    0x1403030c07110f03030a0e01080a02030405030a2010090b370603060608070f140a090c020a050d0509240901200706080a18030e04020a1107030c060906021603 69
    0x140c0791584000005032400b141c400f950740c140c0f0001c2903400c003845c0c1203a0b02e500107030400d032030720041a62021650340691208503001051504184150424203000e26000031681c42464121110303100000201894441d1a04900200341d48800f90030f42401040e40010360469041c40040e403605a00d100202d05000c0c400240018005079002a00d4030b40800d544032401855003e08144070083d80c4000c503540c1e0700158060600741b000813271400640749200344043d03104044040c11020340180ba0000001c010b24403210102c0550203012806000904d0a000d02800260940c48540e00d83c14500c0601c85188240742007035603098110316234080340d4684802031b100d444d242481c060204140403d04000c00c141602d41892461140351408111180c0140507580b08207203c2ca03080004c108024060044050f240002402003400005509160b04081e0010100d40c203050030b01e200b401541244d09032900070164025108180c0030348040c020035a1080e004070051016100801414900a60080703468a09110013 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 527148417 1250 527147167 527147183
    0xd0911040b0a061b0203030708040f0f1809030e12010c030c020706022104081f0c031a120c031e0106050109031a04051011070b01080712230105090a1403030c07 70
    0x451215029200e42c1003080d0b0317000d02500d4407040740b0702c0c00c9102c0380c10900540342c1c1400c0491000c106008500440c600b02c81660340c00d071216514100c040380041503004402c0e4100000da0a070012035468480c0c26041412420300001504030807124010708540c080d104040440d001240104140d0383e00045034901206e00303100c4401c4801c0d40807115080b0b4403d591024031507000d006030703100500c03807040c0b800402060300340c4040c072550040e694128202c41c3c18440b1464100c1141c01301810360f0030408901e8100030b81060807106000f4001c03001a00d00070f900b00c0301c4461407096031200d10103040207004000080c0001e007441c420703803402c507910447d5110a440180440621090000301400350410a00410103000b840800c00c01011820300e01c0e26603c040801e4a1172000c502c000a40381c400007445808840480f41000390307101e041e941fa171150030980d000b20340003554084c00f0418260000c3c0f1419001c4e00602c4010700051003a4a091001144406040b400f0b070f03002802041000714603002202d03107a0b90300901c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 527149667 1250 527148417 527148437
    0x306020313020405040c1706040c0611070504020d1d010b0603040807060204031a04060e0607120e16141f0e010e122505031b010e03030409020d0911040b0a06 69
    0x100786406900418060b500c113040200784820b1042c01d4031150191020202c04103184c1c402030502d42c1e910082540c00502ca880700c0102040b280d40328404c0f00300e440d0180c006640c800395482c00010203a80040c2c045000443d40d1b03a0003015912000c400c1c3c4640c100820009215461070b07040000ea00e40030040018017000780020f00f220401c0410742c1100d01459010f4940aa140031044c60080144000c039802c0b0f40b09440c000ca0007108540004800344280d91343d603100440c0c1440100128041c002c0c0c0c04080c030070340c4140b840e9540303003400110b040406050300a10460a0036070050030002d040d02c0a0480030022402e002c90b110400f40d01040d002d0100c0000e0070f18144445500700411600d40d00300c240c3c2a4180034150351080000c01d0030441c03101e030520002c44004040e0b00c44003011786446401580900c2881080901010343d4000d00c0d0341c00300e00d50010256800d1a031707507000090680e441213090481040e5106444820485d400344c41011201085d501007011581d01c10208003044160f000b0001407100240c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 527150917 1250 527149667 527149681
    0xb01180821070b0403080114060712050c07080304170c15032205100e06071704060f060e010807061b02010e090c1606020c060601210e01022104020301110c0703060203 73
    0x2200c0b207566002001e4000e51030603040c001c080348800e010f1003141203601c10302c0c809149010302c180e0701c0464011520709840c00340e0b4541a101c13603104031513148040c020440d00082d045c4080c40a003000b802070380c0401c1e40614100904074106062500458801d0000c8107002001845070810f0342d0b480485042c1d01d2900c1c191042c580b00144203640d100800c54490314200512218458020000380c3e0903101c11142c0c20b0703d4030882034a21003025503609000c4d40c804000030303001c00e0107604040b0081c4c2c420100096102d49800c11064100000d8101d00d4007a0b1240d1000c0000795401840101341c1d10400b295480005800e9000070203d00a245446100e1071180e40418a0141c2410840b09100391f0240803044400091030884042c0d04401c800074010302035500003942e5540507a0300c00e00815248408441401343c40800706004061000d5000195035082c4403410010301ca80c50542c1e0b0310030740000d46c0718103880c040c41010b094841075200c41a81d030b402440307696102200010b005003070320344c4070401503281e981d000d07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 527152167 1250 527150917 527150983
    0x20301060219170c0123011809060204050d0c150315060e12100e07050f091812071406060d030203090d06020f0304060203011d09070501030b01021c030b011808 70
    0x21000c09a00e403c0021034800e48101540b00200e001011401100b45001900404c010101c09115004441c544400c020340c00c42c0e0150301944541d803245800600b403076240c5022401610035590f040b1032840350700d40e0900019128a005c41e00c0220a89814020a40410105601034060341f25180c01e21040c03500c521156540c0a034105050b400c003030102d80070348464541c0d42000d001d1058803880036001e030820100e81401c003441d000c003200c080a01003100ac4d80742c00c00c501540100f508400c446038000d5020800c0120722800080400b41d0140c1150303d241d8240118450400340f02801e5903201f0307440c1400d01b02c0000d4011041d1111090119000d4065104a040240113132144100344a42c4000000810040181903070207181030701c002c0b501d0003035585c00c00b0942608592041e200440242d003c0c0c1001c102c0317581301e031f002001d03c010180b05803003099003041c0c815003440e003082e489003001c652141e10f10105c1d564401122210b24400d455140982460040c0349900c0d1410074144810041000840c0928840c0740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 527153417 1250 527152167 527152193
    0x302010b1e0a03020d0321050a060e04050a081c0207030503060a06030504020a0303080a0f09080a140414090a140f0a0e1501170102040b07030801050a06050c030313230703020a060201020301060219 86
    0x70980da40c808075440480003000700f108449d030b908281e180071404114461984202031040e035015000300300d0280c194807441c10940006102001480c228064950500003078006014518030a4681d13584078181401007200144144c2c0100b401c240c0390800300400b6030f8903071652804903501803c003d5629161703070b00c1e400043e10504044502150802d101c2c142000035810092002c6802c9540380080911110703001491441a0b11511401c042200c500c003460346030800e191078000801c0c41c00040c41d042840441e06200100700d400600c0b0080d40c00401500310140c7c01058a1040041d000d054120701c201c08014401c030040c055482c102003003c6160b000f184007541124007410490030b03a19151074035450008c0c4500000d004544c010740301080c001a55038018400c0e50300001d140e1000d9030465480c50074160f848400f0040503216001c018078040300310b641524800740102410380242001505500502c07150f80c800350301c0303101103a1040004110255002ca00000400c0c1616005001607440b1b0030050104c0c414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 527154667 1250 527153417 527153447
    0x5090d02061b1608070e04111c14061b070b0603120c06150103050c0403120e15090301050606090d140a020a090b03061303020304150507050105040302010b1e0a03020d03 74
    0x90914002a40b410004000300030941d02c408036810652100d030415250300b410f104948000310300d90003050008444c8907001a21030000b8010b98019580420907403645241d00006a86028880c801012900001e205140d0701003600c00c80324840400039101c40c942803084a034041c0c00c40503507070081041542d040c4011280141121007894482e2550900f0036202c41c8141d4210101180c8100d4a41d205e50090181b544980c0e052000c0c58241855078a07410300c95200c2d80c900c0005c111070100840c05170f60321b0034031805986140020305a00c80d40054141401c64602400d071314421075080c81185083c0d40c0b0560641841c0c3da01001401d41e02400503d01450041c410310002d5009403811030220b07464060707910000c0c0c034400440c11685a520f800300800c801c185000005001030b0000c1100f80003498401b14000c002020514085181c1080c07500d030142120400d640480c010f07510b44840c01c541c1d150401009808030710342100c0b2910700440708002050540c50740303c000d0240b03410186200030716020380101407400d19 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 527155917 1250 527154667 527154697
    0xa0e061c0f05030919080613030509090109061401080c090d030c1205070c06231812010207020f0603010b120a02160b07020d020a0309050d0c030c0f2405090d0206 71
    0x104601d802c0d5202e4000014090142210b8954001c401d4494242c49089442080180499031500b00c0b0200c1403038a00b010036414000c040004106a4940e000018002d0400150001c1d03881c0c202200d15209001038401e0504101c203060038041000000d20450b600d04004960f000141c0b490317481c1c02e548000944a011b44034944840c546170201c5d0b0024000d0100c00d1203541043c1c0380d5911070505441400c1424565010000080f00001d00e0100780c1c3c0c010850981c10b01e40b07000302c0043c1100011207014241d100b1140036500400e80c0d40440c2090091902e00400c116500d90a40d03042080608990042803500d956055141d00401c4401e495941118100340706400c2011844105080071440f08609035030703500041c4658485101520b1001c5411182c055260356001c00700e80c0b41408220a07490750300f10585502041410020004040000c2080209004190442800d01d0003000c92000d07020f41c0e41d20f00100740b008401d020b80d183d00c4801c580e003610049841c04151704560020034068000c07060040c01120b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 527157167 1250 527155917 527155943
    0x6031a060f1318150f0b0a0828020c060601050705120d090c0806061e0d02010e18010314161208030a1104090207050f0102071a090f0304060504090b0a0e061c 69
    0x560f90b8000108803120006100d880c29a58401c0140c0039a00d841000e0180e581070102d8818a8465030895800c280c841c0c0703a00340c01080040a042c0401ea095414400c0c4540c0010200e500020602201ea401102428140e00708201d41d102c681d00d610101d0f407507840003040021518140c1c50564061228143c20000411181d42c40f111000d07680d90061b10f8040c460020142e1145039419110241d0030074880180c03480300c0c0114680d0041d00c2c07440351038141c66072001014848440140603c11168000c5004540b21650342100c0c0201e2400d041c88030601280c9241c003001c00b80507114071a0f0b0850000e9a109002030f03500e0fa40c07680d0327040027012180072541e01d80500244c00960008160094003402d401003054035000b040203d0542c1c00c038480c8c2103004040d2107412404500d207100c4211080d41c002c5110f42034607004030180080b54210361090f0810350100b1004a400d1056580c1d80c07007502400070040e0350304000c0d142060340708401d420004010700c0c42282c0c00d2200401112508025a25051744a1041400700c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 527158273 1106 527157167 527157209
    0x309050c0d0c17030c0d0f08010b0403050616051309020c010b0603040b07050f190f0e09040302100507201b030a030c0305090a1e06031a060f13 63
    0x1d40000e004a140c005da00340403842000d00d060303540d0f54400c100c110f80902650010b0f0030103100c9000512043c000030b000000c001c0c0c0c02002400c0d084000001c2440201d426110782c07d4034011070580481c0014032440150060b04441c034110f0000e000c40c490303100c140315042c0411a0040e180c46a5440803c40e101c1c0900001c0c40c501c4502c45200f483d088459011881c2040c1c3e0244100000c0c03146182c56191b183e01412003c10001e0484011190b81025140250f4804d801c002078010705543c1e80118502038011000d00303c10400710388e01043d5000d20612480c0d01d4041e201103608a02c000900007403454079011600582007949525624100c50640d20102c41d01d03040004e0040d00821880c4020690382c0d954880300100c01100c410342c10125082c12401825160f03c048603000c0160714032422042503584509a07941c0381c400e0307001c403925410302010b070040f028815480a9440d00100d1300d00c50b92 = true := by decide +kernel

theorem cover : BRFrame.Cov 526978417 527158273 := by
  have h0 := BRFrame.cov_init 526978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 526978417 ≤ n) (h2 : n < 527158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
