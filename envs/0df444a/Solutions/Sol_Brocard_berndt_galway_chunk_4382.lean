-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4382
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:26:25.828131+00:00
-- url     : https://prove2.me/submissions/0e6b822d-c5ce-4e9c-a03c-d760ddcbe1af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 787949640 ≤ n < 788129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 787950890 1250 787949640 787949647
    0x16031110060834060804020d080408100608030a021915052502062a1905130e090601030f020402120a0507021005130807031806020c152d041a 62
    0x1030181d012041240100f826240421503105860f0910000901c0340404026520020909555030740301402c4603142d200321040e60345c0f50380d07080c015200d08414010740c0b00c2c54509200003580b800f0100c22580c508ad502e0740507005881c54035406c0300c03c80c240254141e404411460814103055154483d0034040e4500c0b90040c0180c140003076544417070082c58204101190001400c1c05200f610940b4404030700411402045030f4800381041302611405061524400ca032000ca16402800d50041c1c01040180a034104c5078007616110711200d000c644086c0c0d0f0004540e4002d0004001169518010b00c5001c1e100401c098604001d001e50794100d048141c07280420b0b181d48a0070721241d150108522060a003002c10107106c5880d24610000c800401c0810250052000241d00c0d820584244018501c400c80c028004242c0703600e03800d00079038800e03003243c0e11405894101d5a507502e04142801381c540d00f141c0c0400766110b451045040c54801c24016803101401d8105000120b05006100e2130710702d6045404030350a48 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 787952140 1250 787950890 787950913
    0x3033504020f240a0c0c17070b07050303061302220f051e0d08040f0b040905070305010e0402130605060d050a0b040b06180a1a03070f020102160311100608 68
    0xc02c002d1149240e00c90410604019100208100c52601e20509502610745407103103d0001d582800e900000148032050202012a080101408085c00c0d12610b00880e5009910351284030b0044c407846001414a601c01e10015116261070300d645414454410000340c10041210180a21030681c1394131131065080c0e042c400d1041c9000c074420712000b0102103402000354844004403940310396642202c14040d4000d6009003050100c4201220004d02682a03544045070395418000c0c5146c0280c09100100ba081401240e00d403803090194a05071681428820400d03160740c1e00f04502042101755440106803280c100141c1036031004098012072030004800319251820310075034411292000e006a104500d00100c03c1541c2c0c0b41e1400740e80400911810500801c40b4440008481100d1390744240e090702c80310010405520402005180a0f200d15100c0d501607202c4000c00780c1c282d001e02c4070238684650310824030307001003031044492000100d180c1d8240c80080c664400c411f41640c06907001510a503101040401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 787953390 1250 787952140 787952149
    0x10b0d1424150a0b0703080606070f0c060e060304030f18090c030209040f0e0c1201110f2a100f0f020f0705060a050709050d03020c0d0b0a1a0a0303350402 68
    0x80054011200540c3d240c4c01c0404407140c0e401400c03005801c0041142c0003030714980f00c900442d50010382190364055181c0c91403900c87d0522949002d020002003028083c001541400d00c140c0340110b034540c0b508a40040302c15030481e11109001c2680040054501d80001c84080c6445007280b0078172181e501590304d01500003404169041c4520b0040154a4000010f4603d4404600d8240b59201120054410300d40e4090680c0540038144000e4a08440081d000018040040c000c0110054003482140d5044200a516021031a4003c2204868000c2c4503103c900104503444500c4040480d90005100304810f0b1108040303801000320b55080c5c510005444c070a001c010020b1945c0410034060030b210502d02088001c016401e107100e19402100c2d1f030080c0343c003094001d1001c0a11018050301000b400001802c0203081140142e64410095251004020100003030b07403400214480058010403c030f6244d503904036803903e031800420090081d005190440210180303070440425981c04021902c0342031600401c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 787954640 1250 787953390 787953421
    0x90a0f031e020703050c0f0315130c08030306150a05041e0303092106020912010f05061f140a020c0907020601150c03021c141b070503010b0d1424 64
    0x4000750741c8844400c000165000601607004941561f01030303900003640c80402e240034102c100c40442005038070104500c0d100e0824001c0500707400b8007a40900160703201e1615440c0e00c020f550700c6d608020041ea0510001c03144a00420301c0ea8600d140440c681503890308402c0300440103511028540d000b000080042c5a80840b601e4090640130340180300c0c0d8100020280b42c1701d1940c001c02840c4070740110b14611075940740c044142d03413409018001d110403039448178007030000c12080b50b1440c8240440c0303080380c400d8164201c1c80a20100c1d20303190079020161154044000f50480c0000340214400d1040d5070354191a1041428000d100e05c1d0000c100c1c41d4107008080e110300c12100744120400070b440100001180c0d0010700c1d00100d070302115110a4035080d00308100d900020150395502c0a010005205540103070b003d1450b07002e9035144040d1004107444404050a0301c603403400c01c036800154500184045000c000d145105500c1c11b400700ea000d0325442010f01c0c014125800900d5008162000b00406d5082ea602c05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 787955890 1250 787954640 787954697
    0x203041a0903061306110c0c03101503080f07020d0f0618020a05060a11010e0c0a0f0b031803040e0406020a230f0c0a14071a03011409090a0f03 63
    0x2941400c1001c0080381e83c1c3c0340010840c0f21201d100c00690b0f014010654044090703001040e034290303940c0c6040090580d5603a142523107030b030003481900c45815440c00780703100300e4043e41c00c0554210411f5296880d0200581c10090303012821074020048003006985110320900c490b4442c0100e44400000d40c1030030070455005031005588090000c0390036006aa0711f10414080d60000c49499845442c1c8500c11908052444044800c03503182103075800656600003a48020340104859000450307840e40701001e800c10711840780d418440c90900228040e840c40d0034074041d21103868000c0b030b428103a4408140e0420442610240d4170554001910301700d071544461a0f10945000c0700401c90744520001c1500c00034071584210807001da0001c1001554542c06020000c0300350341122400020000c1e008290362502000c2c41034081185c2e41000c6088075908080540b81228507422581c9400c07000441405a140c50040030800319000b0b0001e400009040d000c2450a518001d6507446c40381801c28020614000b075000e039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 787957140 1250 787955890 787955939
    0x8090606010804060203090109060e0303060312040803090d1e080409050a020327070b0c0319020f0a061e0207050f19020f04110c0a030302120c0c060a1d030406020304 73
    0x3081041c1e40c0120304030742c005600440060b07591b901d1014180c0100b519420003000345081650a10070b134032000028500a40c4101c081d918580c801c80c49242d01c43c031891140c851541c0080c0480b899500e054400f50480b41e0007016424108000e645080c41c401c500c0300d50442c1c540310045814403081000d4400c080d40720a841c1e400314510704047d080b000342c8550040718001c0c1d0407020224488098014000d0310001c00c1640c2c50f072511000c03a14841a180d4000d00078401d00d00211070444020300d80b000550380c80744010038000c0d220050161b2103a901030a1020b902559400e4518080d01e004c00081c0f000b00039090041024041030b41c0d02c0030300f00d41804007035050580380b1f0440090500260340c900e0550b0f229028100d038000341d10340c18400c60307d8840c001c1e4852201607000303a500c05018560550000d24510040780070342c010503603c00c189080c1c9800340c0006081650300003030010310124803a6000d024010380c02d20441009001c1c0301c20142ca940d01c81e810081c010303040072500300104040d04001d107454500c41034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 787958390 1250 787957140 787957153
    0x71b2307060804202206080f060f0a052502010209060f0d060509221a04030c0c120b0c0a030b03070f09050114030d050f0d0227030d120b03030c1006060809 68
    0x280000d003150400c5405c0c0214410790f100703161882c10ba50340840b0051a41e170342500c0319a401e0341c03886074a404080390340c0306000c1c0308900022075030303001e600c1003500c25205405074606403402c01400091219507081a00150365080041e50700c659142c001070400e4080d21400c20f41c0c2d81103000456000da0702c040e8002401040807100f4003510604a00300007081c003800040c4e15200c0030290820140c0070300d8150340b20318100c990100f488103065001c040b000d040e50044916046d215a15403a240b03d492500d01d010384103261880c0030a0321664948028036509800303290100350030407031400007402c00e0456802090141c0200c8010021000140540c40c01040e0800480c65486c0c6000c001c131ba02c81080d28070060130004c001900d002608140420380d0b8000f69503000440d211241580d00582101c81340d00841144580075440100038a4001190482c1e2451595012010b04042d001701001e4820281e482e9413500050140300c1ca050005c010201400204050206540f4580360000d0b01c004409400e0003102c1d00001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 787959640 1250 787958390 787958453
    0x30402040f05070f0c0206040b03070e18060d08071a0903031005060405060d1104090603050a1709010e011b0b090706111b0d02061b0d08071b2307060804 67
    0x7135072403800c0e8045400d00840c0c0c09110300c0018564469908607062a09006c42070080d41341e4004802c80ba000c105131884641c0502c14480002001c80c100da54a6004551507503840c0092484009090b03001c0c8a1560300a90410040e01d44403845000c81d200b140700d80c40401000140707403008844400404e806e82d145460706007000c7c00f003101481540030300c00c0d1650b00c5107240e248490815003120001e04072400c040103015100e148c071507114188040e003030351118004207040d1889454003045070012081615499030601e80b15006584207194a0207004450041c0700c400408188001c01c442c0c4502054406410b81c9414540d0140c40f014030b00d5041c0040d948105002260141d6100e01c00034034250880788a9802c900a200045451041c001e21080301c118441c10711540f0f443c00606107101d40301d20789500d1426a6036400840d8505128107840d1a842d006028500104818100c240014400d0a104a800d6601c0c0d868092602c03003942d02c00d000003090f900400c810720510362105c01c00848603038141c514071081d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 787960890 1250 787959640 787959647
    0x121305300f0909092a150a17040503070303052d0910020a080406050c0304050a0b100f0e06031203061806030a0b1e070f0909150816030b150604150207050411030402040f0507 76
    0x70004840f020120001f021a0164000c0400c11218030b030080802016103014900303d503c9070003c5c107003140800c1c10300c8045038225215503413041d198a0382d03a0440525003a04078030840c214201402c2c82072580109081c012580c1303d140020000380301240c584940f00d0400f0304c0c0c1b000071108010502e009160080c824000010001f040344421580c10208450040d16a0840c1d07000030340290344001e00101002d880010040c2a22801c0c9114407800c9090f1081b680c0041030107600c501c0219505640401d1542d0701050403111b040e641600104041c04590030907146a50320460010300343c8215140407007c2e0b60080c1c8083c003501d081c651141c000c2c9400c5410030760040002d0302c48081c501581c00042d03261814480c00102c0b441c0518010211881113500210b01e11140c0300110710035000503a540c8032040b0000b00c1e10048001000c0d0a51009403c085c034040c80c0410041010142301001c0045014a410008859481f4001c0324050303415503134240d036a0f0409104000407036140402c41070703101d0b05110801204540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 787962140 1250 787960890 787960909
    0x90c1d0f010b19091e171219021f06050a080109230a0605040c140613030323071a06040504050604020906030102121305300f0909092a 59
    0x60b03200f04070f039a44003083c0985005045030800181ca1406664440045417481c601008072851521710403400d90815030415110510080c4151880750104060107102080d4006040403102c0b42c815a5541c2c00c442d499480d94082c1d450500b101c3c607840b0181401149450000c08004003204402000281c4a41d95490000280d284052510840c40c80c0c2003240500d00f0310003415a40e910a50800c9a85001c1c41c29415002c0c89010300e040002481d0840040d905041d0102d0702156081c0403000d510b58a107640c01c927413203a03048546400031014180200e0705640040007612099108001d41103199455807112a009000102194421821f01c400e120100754042086900250140c0e02d500c0d50340d803110040b0340a481203248048264103000100641c49071035401e40d50740301e8031400540c1c1401001104400040c610780d054214202d1481e0301c01c0141c102c1c110300900e400b40c000000c8500300001c01c00000c03103c04080329003454a41042020f9035070f6444e407218aa042032402010811900741c0d00005c42c14186 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 787963390 1250 787962140 787962157
    0x5010323150a05040305070501180c050109050102030d0e0c0a080123060d151d01050411030d02150a0b0603010618150215190507051306080c0306040c03090c1d0f010b 73
    0x15034803c045018140300da822140c901d500400248481030101da1984400e61098105498411540c5804203080d03200e040c218048801c1640154100040111608024258401d404100340711f0301c68034542a4540550311002489a680001011040ca036065182c103088132685086181c130107000c004031541c1ea0f6800100c196049960690f040c3c02c90b008030b030300a000d03640c511890710342c201503c00f200040540040303125900c504411810440e10109050303803104a0b0140401507000044526103180e0201d101650000d81c031100810180411804507603507034004e80203400040c148501880d0500c0720032080c80000c1a40c10755901d101c40d800b4100035102c4002140314540c0b000c1e9034011650100c51074484440c0144160340402080c02c1c102c801800c81e6118001550003940250400111760b4055045c6501c02d42071840031074a15503420003007100600c55900700901b819514240000171036000c080b00c0340548200895800301101c0c4030561207070002c0080050000c0d00c80300c001030001004d480d09a61a11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 787964640 1250 787963390 787963411
    0x60504090507140309030a030b09040c2108040b04210209150a590c0d0c03020915030402060708070c0b07050312090a0210210501032315 60
    0x15102c01c18201c808004212070004a480701000b80503880601200400042d4401c1c3c03010041d080b500400c0c4507200404403800b510102d10258104200160400c1843d11400c48420303082100d2103030790711403e030b54020750001460320b0408982400400c01401000b02d00844180c886803c0c006141e00003409140000c3c0400040d95107600402da00f52903602c0c1c5c00015149058042d46040080000344100b03065501884204504640a03134064105d450700120320400c03510240762030144600d00c4601c000002a0100d158010304008071090205103105101c2c500166507009a640c140c6a800c11050f078100c000341d0b1b410320a08109100c016903529045a41e46980041000d441d61458108003d0415456010046100000420000300326002c002004030040038244081d6680720304010070760340c0c210400003c0d00007044c4001523400d14003480c401c0032030010440150381060009901d000c1038810071707401100c51440402d407070030118207000a0504401c8046005000b0f02c0ba19131810000f42002400280e135030b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 787965890 1250 787964640 787964651
    0x601210b060702040f0c0f090806151203120114060c0705190b030907030201170402090a0509030d38030a1103281103010e0a0618050618010b0a06050409 67
    0x10354036000c0603100000d4004100b00148070744041c03000f0160564460030320000703c1900c0845140d901900c468016215208002d107280d58640070048448040240d1171980103000004401e810401000186a010004060004954540081c4018444101803024401c80040c0000b103a01d400014019007202c104803a44c0d403186255060b00341d21203c1940107480c80c01030000410241c0d00c0c0010700d41048030b00c01c0e07035105c0400d2040c91031050019001d8030001e40c00341800001c034861361400e0300000d8101c0024010340b80f41030b0100c949401129403030320005a45c0302c602240101c41d034010080030300703800d01102e006d40401c1082c080001d49410003000300424241c1c00d00301649458a0803c03209040a00d007851104484402490340d01c104e800d50202190200c81860074185c0604040c01050001d0001034000c0c0040b500759540d210107002c0c50000c2141038412900c0a50200b0300400c21240101c4507120a1250034a00c40a25420b5401c1000b03e540a6042c681081290b07aa00c00704880072246001d000190 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 787967140 1250 787965890 787965911
    0xc010614030d140712050c07060207050a0506181c0209101a1b0102030a0209030d030605061602030f1002120a06080703151404050304080c031f020c150c0301060305060121 75
    0x1640d0140d6140a402001088029030002c0c3c1c000c40103000e01d11f0740c8001c84500d0707680e6010407a507640442c05200d8210401c05006c000d54244007020707041c0d000d03456079240c200100580c0821100035481c0b4118041d0b50404000c0b90a5042500c0d45e242c02441c2020050f1106c0c1c24201e5100c805080c54034441e0307c441c000207001c8a514a9020b68034144402400295924200305d0322541c00780d0040c5010320300c60f0242e150504015802071180c4400c840c0003910050a105070403084e50078000340c0700b000303036018091062008012001440016240a5030ba040183c41d071031a4410041201c000404c00c003105442c1540500580344001200821a6409030019000030841060a00036124503100c0b142030709040400d11042180c0440a4400d540303222044450441200c0200341c3d1340e211400c040304108024803d0a59030b1502070f0000e0405072642421100f06c0528421084003055048806066183c0040010f10a2590501609811203800d20701540300421103d407100103a0b904c4200f80140e01d686251001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 787968390 1250 787967140 787967177
    0x206160201050c0106091a01030903020d08100b0d02030f060303130b1809150108090102040e13020a05030a110406060c082a07030605160302071e0510050c0c010614030d 74
    0x40c83c45203518000d002440c0d80306221405003000f0100c801124110b40c8628406510900c40e0714103c075010b034010700c071941d0380c0c40c0203039142d82000c1c00300102c0d40003440380812a50940d20081c125041022401a0340e40781c408422060400701a20316886500200302003c1060011000031042d60038580640d0fa840d0560100c85020b8000075905a03081110340e4100440c401481c51410149542a25004030076a00c0602003801c0784540d0164030b443c071100d00045403000c812416000a024070180004a0054480d000240741411154048401c010b042080000b0380c1030502070f1100403c0b9a060410503440103a0310142c4500a10004040a11031509400e013640110000810001280d8082d10500ca80701d044c182c0c090300c0300310786812a400d41120740383d80003071191007241c1c0c0c21504084103403140c0c40b46425035000034030002000d0b2030b140301d0010100450601480780038015002c0c000f0181d83c410301030340b01e9800c2d0780c50740e48100d503103500502d0390903201e40f8003240070880d0700418500410481241c81990 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 787969640 1250 787968390 787968397
    0x7090204060f14093102031608181f0b03030406080a1a04020c0f07080a03022a03100b180c0306060903010905030a090303090b041d071e0f0e0904020616020105 70
    0x4a03401460310690240310544641340000d20326521195001d042d40d20b0003010103a2005840a510522302441c18070015841076410541200791102c054449044541d41d040c5003c540c02c0030f6110000400c9250b05581060f846200d151010035006141003510f4003402828040d0300a103038030165a2288034608640b20100c00c1080c034080000e01c00c43d12458881e8a466a95203403065400790743c80761100c00f00e246400041d10655055059006181c803244041040c24402241d0317044107454918008030280741c0c1d90038410851445015040014009182e00810074681c1e40284030807203241940b0305003c0c0b44210762048941c090001e44150b0f031354411003008a80100b0190720054034a00022412588442d44078140c07200300e07402a03483c0005903460b1002e20080740f0645c4582100b0030300390803c40c14290881c4c0c0580c1d52101c3d090070f0540b091444200ca170b55610034484280d000180202c5400c40705c40e504000491b0102c03005850346103a5103041d50106141d88a0740c0b01c1d0070b0081400e07105e0310f811a0301c43d0045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 787970890 1250 787969640 787969657
    0xe040b041b09090605030a1e0507271e0c020f013b03091903080c0610120c05090604150b070b010e1302040c050f070506010807090204060f14 62
    0x8200c0308220154008507025204501000902003140000b1003481d18041c15084d20340003806400c500c4080d030786486c4014410100e020081d140c020302d18001c164240000f600808100102c48400c980c04420480e5000c1281030b026801441d0250003000c0e01c032005484900c80e541d8640014114507007102c1607250a4640c010700242f03600344001e04042520211302183c440411030070340000629280f0900d00a0f00c407444244590303920900025181c0c1c0703000c0c518aa50ba02d2244e0345420215169260884140e001c2a85808503a10043c1400302000901c0032940080407071000303840032040107680b100c861000034032a0904c64400704001c0391040c2e545a102c00c131005c1c25505842c4171550380d0001c1c2e01d100c2d0808501514001c2100e00000b920140d00c2c1d0340d0b244503a5000346017606481041c0c0c2000000c00c450056507040101c180010018207540c03d0003005424010001005a0b40c5000f99480ca0301c0c141c6d400c001c51840c018402040040d4004100000640c4139050000d0020400614031143e806401c55 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 787972140 1250 787970890 787970899
    0x10302130f0302100203091005070218010603050402031606020c060c28170702131e1503061a0916050d1514150409090510050103110108090714010e040b 67
    0xc002880003410603412046074400d403280341d850619048160303100d01895405503001601b80d1680c411282c800c2e00200040c03840141a100354084c036048451545d10709810000110381e81c1c4c420b010a602d010400d81d244028000528550181010002500e501589100501400011a0001c0c156a0911070140405054800c0903000280c15040041500800e141501d4155000c044603502640f804102c41c005034010344194603a0313044001c08001016611803600202e16150288026040a4090012040030740c11655550b43d045090442c03c40300d030300d10204264443e889103880aa2200454103510085080c1e65400d01c040444054500e40308958207154017a1030040240c04001600c4002320903202003180f0040345100c00424801d0b071214440080303411400a010400c49000c1c81c0d00f105801d94400c00507100582c507201984000d4031001c1e04103d800052142c40300500e035034442c170402d0307201c01000c000381200c603c0d05105e215441241c4c45e07510704000156a40440c0340d10703aa0002e1806860242 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 787973390 1250 787972140 787972177
    0x2040905040b04030f03051006050f0903121926061522270c090b131a071101030507050c060709050910081005040f080c0c040c050307020d0806010302 66
    0xb07450b2221880807101140802d0207a16040f05041c801e02c9100e2050295850000c0018140031050b00c603034200d031140003040d40c010000304240f910188454080c15003c0d00c50075441d00030031203202c00016071003450641004007140250040b45010a42d16402812b95101070381c46460301c00200e040c4c1c416950a2220303141c030000d46400102040107690b00c500e003200034144078884d1550764505402c00c082c1c194001e10480641d114041580c01c1d0320044110030141041ca904680c2c400c1500910b4202172818850b607041401d040050701c512070f0261004805803204545408515500c0f40303400740c1004030541c10144e035100007542c0e040c090400c0b90036022050003103814614245500518500c2c0c0c0e0300407280603962a1020841d02d03411b40720b200301501c000d42d002c1d214080d841820741000f031200900640384100b020164002256440d40100031070005580513140420b100e80c240400c0e00c00c0c00720f010040150410812004030340c0802c5d07400182410385420501070300ca0000403006801044c125450607041034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 787974640 1250 787973390 787973393
    0x221012d172811090f0a0f0209190e060103090308191404121d0a090e0102070611220b0315150a09081905030f0d0e030304060b04051303020705060d0204090504 70
    0x100045662621510419402090700824404c02400907103100c510000320344041000003076140c0001d481c031000b50f80c006091280180000e080c88204264000011b050040709001c8041c3c00c05a00f0b80c0410f082c282840001750b01d0b5802000d4040050181004e00c4901400c0e052032806034002055400204403844071608007814442d1304001031401c400d0101e084003e440c05090a00080100d0104006005401071441e1100c5032020705190350444446550030491107001982c0380c03089a098209034a042034442e5005229102e10281001c50141c402401352000c100e94844107089a03405080c4403420038031700d0a460041841d00c01c645c02c0d548100700020456014865118500310200c0b440941204c80c0c09071201e1510071000e0740d40c40c014107107810812002c3c0c08109100700400a02c40c0c01000000d1180158422905540050303501707d440644890000095107840e029444d0001c4588252920410306c0d0b036000303591041e0070310880303018440c0400c00d40c00507070880e4142c40080000704424842c500d810b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 787975890 1250 787974640 787974703
    0x140d060f0518090303070f17040b091209030a1101030b041407090e0603070303032301090605040c1d011d0a03050c090c030f07050304060221012d17 65
    0x81c050341c1c0c020100e000d581c081145000d0031280c02842a9400b40d451074071121001c8500f9501220a07a06102800f10403084c0381c41403400c1148554001c100110072414900000303814929040c0f10100325100c140905120b035035010540c0b91041340d010092249445400e00103801030b100c500c011581c010300e0502004412684448603520400296039009140c0786c85007461405900e05669060709588007620500c00a4080d03840fa40d140204190303c003144204500000041d031800b6003040d840c254403182c1c10042800c15000b4240d076840e2900707002c640c00c2082161410714010b82049141001034411503003003021a10b1061040d2804042d01900b801602e0341445503030ac1c82c2d11407016000345040000220405804015a1701481c5000c03030941250321050402c80d041c3c0c001500c10b8810603401c20030410400c001e900c410803010400201252150301d041c00b405a090000e0130b40010707140528501c83c1900054081d24026a40307400b401d81040081d83e48540d14104d42e030180408803400c0ca014204500b6503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 787977140 1250 787975890 787975919
    0x6190816140703031803030e01050903070b0f060402040b0304050c0f10051909080f070f0e0c07121b0f0b2a0f090a0806150d031b0201020a0512120f0610140d06 70
    0x25010000d0185803104842503988dc89603420182000701124046208803020401e082d0300b008000300b01500b4141c451a94550940c8150313002c4130f441d0301c0196403800307074100210340c018801802c55941b10440883c060240c80c0e0702c160701803032a08450b90401c141285021300c180c0006485001c0c1210f1031000003401031903440c0e4dd41d000cbe01c10540c100b28070000e4251301d00340c10300703104441d640800c03070030104166200790085a0115960b01071080030403040c403100e02c1d8101403c4480e0b0080303031040c01c03401c2d540c10010a10390018003640b4484003990a0b01c0200f03c0300009051748070982441c0a907a44180344007925aa001d801c02c1c5c0e9a21030b240700710005044800140322401440500035108041c040a010000b913000a0840103002c41c900404035841e8400528950194500600640e9020819a604c0301c2c10042e84504514100502240e0701c8454a1041040ca40c010441c03030708101c080c01c1c0100000c1c00c020703000b51760904111503821550881007905003500e500a02105040c00740c1925950389a41c3c284 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 787978390 1250 787977140 787977161
    0x803031e070c12052d07020904290103030f0806060406180308030108060105130605010f2a120f03180b0414070b03010924170c0619081614070303180303 67
    0x203541c450105c1160f41100110207030081c100000760302d490081e50a1000e01000184142c401042c4400380c2d004002d612003030195090040c221111443d8113602e0058a40d550f81440002040008002c0100325291601141c0903030760786041240c2c0c94026243e0b45401da1020390130041c95070790040000202a0b03400209103050b030310b08507554070085111924034021906140715460004010f9000c05203403d014005403551150401030380c0c3c11002101c070080c41e4076100e03003d040b00c0500c1815805149164050442c0b203000310745103010300c051007a240035000b03401f00c140310107480d44840348003081c10800805d4000c0000206401618a115900c800074562a00248214400c135410700303440413642a01174440c503216550304e40200d850281010105605040c3c40d0400c058035204513542040303d69a41710240c8a021203041d1748003990440740304c008043e603802074007020820703c280500c06052070b00241c1d844016030750143d40540310102030501b1400f52801031b2450080d84070807074515060582c1500000c4041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 787979640 1250 787978390 787978417
    0xd051005070507170901270503061012080c03120a05040203191a07020316151a0109140316060507020a06090821130f09060803031e070c1205 62
    0x2580c504805495502c2000b000500c0000c084c1ca2280302c1d4240c48003d0800ca010616003c907083c946044d047c002540c59949038029136080c448100118030f0708204040d0300400301d018412002d4504400d18580007410440100580404200105008010820740e00f08103020340c891102c42c1441d109110051900340c4041c2e0203406809506129001810403040301c00341c1c0700a01404000442c0b05d00a01c0301005005101103002c100280c0c1040c41c44105500c0429004c0c100c190406814103070010100c820303a0ac0184010303008244c0f4440c2c50717030b0000c1011b0122018240e807000c0110390b0301c0000c0d0504140240712088103058020100707009070b00c0005031110078030a071070340f07500c054850400b60745404e40d0740709404141d40144140380041c000d403164881400b0310301c854241010442081190900c489030003803070301408911020849900709018000c01403145001035032944c1032404407030b81340555030003a440e9101c0f00c03034021850315441840807400706078009241035010014000000c3c82680054850100c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 787980890 1250 787979640 787979651
    0xc0106090203070804030e030a080f0d0b040e032a010501030c1d01210309080715022b0c0219180606020708060127050c0721091a090d0510 61
    0x552503034402c80e80640d46a403540d52160390341340d504035290380c0341140040d058000d541e04040040c0d4420098402c0d01030302c828143c4c651001e0344001007240c18101105e8031580c1031540c40e1802440c0402102e1008100380d1154002c1945854071800550f03505108802c9586880c00002c10b00010700081c2040d201400c00344805000c0d0498400c484420a004400241d610988003100744003c10007010b1344580300c2d0403c0b00410b42c0c0e52101c81d04005255012260309054402c2c1e0868065050025021a20b080c81039200c01140c1004140c204000c0d61548409025010140c2815540e0b1030004000341010414080d080035210f11079441071001808440e965139040c07140204151340041207010944484030018070b010703842c0a100c4001c07a00c4400c0d202403a098072000b52070b10006280500784c0704102c24140d640e03541602c1e10304100e0314081c0d0758070f402401915001410680340c0c0414104201d0300340c2c0d0550003034202c0e9800a10418411007c81a41c80000d400ba40d404105000c944a18000c2c64508200300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 787982140 1250 787980890 787980899
    0xa05130905040b0105060c0c040f140106080411060702011713020f0303120435030603210d0f290f03070e07050304051e060a050606040612022d0c0106 66
    0x16580300b5540105030942820041c00a8105500600160038414007150030326500305012404450400f00308518442c0c8030030b000044c00c402c6040203030040c80c903880e00c01c41e81d107084d03101e030003175201e60007600c0348103c50015202e000c0d60320078000788100e02004401d00700e0307a003841d642008214050b0070080b40100c4154050110601e4044150f501e0301a054044102a46d00e40e5a030b03080500c1410b00b0548002d1803034030030000c8125051510655842d0344281c1903901e04100c0101850610310391000c0425901c0b00440b00c0c0c8040c0100151000501640e00c04509001c42c80c0741c01c030203403410708254850500e2050b10f94820100c50084c01001c51030958542d0b942c0b00007030041c140c0750381690080c00150a205c10100d010203200704011a489809401039418994161582d80e04840c0848054041a8003820501c50005210309c03038180c100038100e505030300d410304c0d190001d0042c90710640b030180d0f1180d001c50f904400007a41d502c45a2240c00307825164075603454840812107a50403140481002d580380c03100204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 787983390 1250 787982140 787982159
    0xa02010608010209030a0222090f0615051e01021513420e0601060f08180c13020f070305040f1202010516020f0301050702010209040c0c0c06080c0f0a0513 68
    0xa500302c0028025010402440d020701c0b28264104944038030054449242d008d2543c0148184010184142d01500e000c0200313080000903110040b0101440c0e00302d828040200d07984400184403035000c1e59040502400c14840140e041201d05080000500b00311008c001d5a44500864400d00500c40c01782c1c402412054058940d07054600d40072444c2842c071030070f80001c240044070f0b2040090102c0c050b000c9000200c486100b0f060030b4003a070205c00454144070001e6419074000201d103510510929101103e860b204041d181d03201900100075003c1c402d08007a5111244c01601210000007050001c50f5407098035140c010003075441886803048107480103102003008140c81160701c3c10560140d5850f401c10030303107648115800019080032a4041140890520213860030300500b41700d0903958000584a403501420701c03099498818a850401040d45041c4000070702d4550602d0540304145032034411580d070f075600c444103442a41d010000345640403403540000382c0d00400428042d5070104810b2085540c590f84174 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 787984640 1250 787983390 787983397
    0xe15040c15080405030405040e0a1208010504141005190503120a11030c0a1506260d0f020618070b0c03032211010e04110c0703060b010503040308130f0c0801020a020106080102 77
    0xf08203410401041112389060340001012100d11403d490f041074540c0e403038103144840c0c02000d4002c00c462400400c41490907114140c0f07016803082c00d5010b00e240191964800400c540a0540303c2e200614800b03000241e60b620200180c100a400c40d0550311100d00080c0030354009104107000299041c00011003070f6804415282c0e040315410052040343c0c0e8590701d80805504190440c001280d0310540012035000d0340c0107a0701e05003680041444103105405480e401c01d00800c0e81201440300350304081c602c1c558001104e170342c480000d9621003c85411080300e641003c1107a0b00282d105280829100340750000032000f580148000e0304200a04d8200e9503015400b81e045410140003182c101c2d50510b490f5000e0340c0351511400e40101b00141d040761304085a003480d0880e00f901c0c142644050310500400c400f034440d45003002802d003000c41c1540303060364008245181c0200003140c0200703002c00070002c02c00060303d03c00482e584864020001307515040614002e401c48170034030005600f172280014076005d061089 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 787985890 1250 787984640 787984643
    0xf09030f19030c02010201020d05011214060c1b0c04020705100c0912030810050307080f012913090602030408030a0c091802090109080102130305160b040303030e15040c150804 77
    0x1c07103421a03075841c01d45010a20344001d9045d9502080310303040310b0780540300c0d440c040c10080202001407a02824043e001008480c081d80a981c401028002c410b41044199400140e1418a66041c0d21403507100301d04105540c0d1140c1d4202e4004035100701040008580307050700c0160002c0420001c0c0340c2880c12034440700c0c40e110310446000000005008244650222035001200c180150107460f900c2007c28542000c580c4040402d41240000c60300b241c20030b0103905486950030b0b0040009406408803681002e41c20310340148207403c0c00b02e86c0141810960848514903400c62000c40d00c9181078240140c40c0d07403040300c905500b00c1c40e2445c008800c5d402011913009864141e4600000050316840f01c0d802903000c4c01e0058180b0030600340018020f2030900040c000a8034400750441c1c01891454000e00c1c1c40204c034580312010041c0d000910401cac00e44002d850440e5014a004500a001c2c07602850030512038203401c40c4680c020000300024460303180c0a1404413110f00b1078041c602851100101c070722a405440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 787987140 1250 787985890 787985923
    0x7030507320d020402071202030c1212060f010c05030a030912050c0c01030f06240206010f150309030e130c1101020702010804260703030b0a0906032105040b0f09030f 73
    0x1c100c180d0500d2003640d020244054401032400340c0c152203846843c0042c1400000681c4009081200f8510620002507148050360f82c140c10000060040040c1c458000d1019001c5c1803668030408090380308807003004043d500602502c1c0d817681c08007402000b5080c410070580d00203c0304688912803a102c1c2c402c8400d204201e5010700410303046140110060a0b0010100d4034841d1121004a02d020a12020615414016544800c4045010300c06400c161059100341d10079400c140c0100441001104028403045144c40c002034402d40e94502610340c401540001078010f0b01d8413500700715200440c2e026a0411816446000481c210740f204e8a00780c5c030402c030700240042e6000000c1000182180703c9441420504101d407a140b40c2c04002c00901900184025030000c0e4444441c158a41003050a84029058401003449150b00b1a00c4c2d03818080f405440c03818200e040d0100c0f917840c1ca8803c40640300038001e03511800755141010404d603034003500420300c41c0303100e4000c9003500b0f221013400152910a9040810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 787988390 1250 787987140 787987229
    0x6060117190911120105240a030602031f03140f0102040518100503010c021510032103060b13050117040b0106121404290f062107030507 60
    0x405405406105000c031000b00c0c10f10b10404066680110600341d100308200002003d14005d0007205040c0d01507200382181c0c1100f840300205588540c014401900d40040c0701580c1c2c0d0305c1e40011a801c82100070306512101240100c0070081140d00e4034841c4040100d0700423210101c0c03001400c24201d1041d4842c15a0181d1803014100c0030030380b01d0f2681540001d0240320148078540c0c0350f003c6070075250000d4070749005810011030380140381026804190040412030101900a013180d030303130240c070743c03d00601c0102c400030340a030001200748250031031009031070018440e90b02c4403440c0010b148081054006c1034085401488194071115540c2c0e0007600c10340d0402c1d00300c4d03601d07460f04405540b4000c914414040080d00c59038040403942c412074500b801a803054507601d40c0c490b100740800c00b440000210900c031003000d80080c031041d1440b10754403030f8000104031920300305100d4250340c0c44100121044001514065100c002003031080102d0f0320310032540300800d003032100703c2401590b80c0034004201c06c2080f601e0702e01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 787989640 1250 787988390 787988431
    0x907060f0302041503090c081902042406020706020c0405160c02060d02070c030c0b1801030c110708010e16180b0a03080c0c010f030608060c0906071406060117 70
    0x2920203a5520015050062400391200c000c0507003803030070005040119032104444e10400240420040040c200d4001402810190703052030401742004001c003034440c0303840781554072807a806620b28400101d644084041003e5441c400a034441c071961181d040540038000081140c0d0a03d0f0160512070a0b02c0d41c000700d4801100f10054503c100355103410f80c0c12000a100180ca00c08452005000460282c10400c1c41146185403011503480c1ea6040020120024803030803903941d4000700210b074542030908000c02c014074032260031150300a20081c268814460302c0c1e170000c3c2030801940096841d00100e003d803900040b03104806100b450351449107154601d10203c0c81c07810300900c0ea2000c811342070300401b008a45556a01d0304a40e0350804195a81a50859560021a980c1103c020f891003032071801c1c00e00c569440c1c0030300385403a8800206600440e8070300091401c01070703442008407031034280d010315070070175841102c176440351355500444020307020842510b1044180440009101d12446481c00070080c0600d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 787990890 1250 787989640 787989647
    0xf1603020607080a1724040902010507060e01020c030d1a0105030c030103060b030c041b0e010e030705011d1f09050315010b0a02011401180605040b18040f0f030e18090706 75
    0x75001382c13810801090752600c1240043d034100d5006504290001e5803141c80151000c0d2014641003509120b949031061503030050340c100c01030b074020035044807000034211084c002060181c82410300b070100c2c9003c0041d4400c0100d41642c0100c0825004c0b4a04655121441005458900c42510003c92060f02440104000381e40c0b03400c14001c41c0405001d0380c0c903103c0d0b00c2000c98148d0b0380301744100c0d422914854011404035884070f035040c0141001d00c0c0180e44125030801098a5002d0b41c010a810084010881000030a103500702c1d01601d0000340622170785411090140c206800441e8076000060007110000403a0b14000541a80285214081c80e910b0703440c1c1501c01c0126842810750005554031a00c40808100040700c0003030003031401211110404082003541c00482da059017105104e149800c00b00b2a140d1500c90114031500d04420414035035403114180303e076001c00f01c40c02c0203000c1100030080310b0400d07912080c1444000c2080e503003006e000c0f0010401e410450400c488560b4181d0000d0810441c4620 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 787992140 1250 787990890 787990897
    0x15021308012c0f0303070807021c12090812013002010203090f24041827030c06050403051c0203041a0a14090a0201020705060a090603050a0b10020f160302060708 71
    0x81480485040007243c007001801c44d00120360030f40c0030074000f2082250444d014040c000b816190701d080c070707110380140440c00340642a4078200e0410342540d486141c420010400c00704c0e03401031074400d1001c0c0c8540e901c040d080003800c09400a45100102500300d016110403240f40c2050040d4160091030502c02648140f00181004d2000700d81d0080304d8580c44180041200103992030042d03641a269652030a00811090100b012028404164941030005e20381a120301007280c071100c843c0b18000c2031040d543c101242c0403000712034003400d107030b141c00148001c1541040040c103280141c1207480c1c0c8101010740220040780000ca801504c0500c66244012440c8559105d09600c04001c030f900284400002002a28640044400b40709951143c1144001d40d03804105910090208845c01d51510400c281e0040418510303210319070030b0641321804a845d83d64550400440f400c40940340414a02441c6802503862050b0f0040e0525400350b50107a0412a80c040130003010340350007402c041c1c580380042c2d61b401010751 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 787993390 1250 787992140 787992221
    0x3091c230a14070f0b060a08030f0a180e01090606080112060c11100b0a050307060f08070903150b01030506090106090323010608060403030e01060f140301091502130801 74
    0xc000856010600000c40107040d901d070185031900341800541c517004881c1d11014000d01d1083e880c400c010415506c0000c1146c0e2802d0602112503143c3c07404046c10ba908000011042807003100d1403401003164030b45d20107001d0491b20010800d003c01a6a05019107800c1000c0c09002412000081402c011885076040800000217600d0009040b0804007900c604210b860b00f000407129484040607600c1c0d150401e0218083c01040303000c0c0551610341740014056001400d0307000203000841d00002c070410f014102180085810000152141d4814030441d07004081c0003c1c018040303454680030503014200070304400e060310386030303119030b09514156181c404050840c1200c1c40342807441449880d400c40401e004820041c017000b0000c1c200d074182482d01a082e1090707050f0911640e1f01d8000300300720020024412100b25000c0d8140410111100e1b0701080c05030150203c00303420120301c04031251b54070820794002d02081104030f1801402c19250084a0300782c0d88210841c0b200250b0000c5c01403200c0c12035285201068 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 787994640 1250 787993390 787993397
    0x15070e010c1b0807081b030604030c050c1504060f030605220204180603170313141c0f02010b090105030c040203091603120f02010e0703081e03091c230a 67
    0x2c1c09049414202c149580c00051590700500c800b0001e21108100910f040030380c10b200e50740c12032450030100f952081c00510150401442210780310134040280090b4800580c01740030300100c142d007a0710b02c0035a50b2040c403642d000140444044a20148684100015640000d1005005400c085c0742c84c0355801c0310340844540c03150300300000a000800541184000351611401244051660070685038030b4940e02600c40c6a9841042000801e80d8803898050045034482003146070300454000603807401ca0700340d1a203080d500310190460809a0010b800b0608102d0f40d034020700c031a641e0311040c410301420038850203815900c800141003992410341c0146134002e43d240d0480d90307505c111110b0b11b0300c0710241c0c0d882503c0031450010299a16a4040c51a118108850009110b5000410801a5540c0103444094103140c3e000c1105091a4500c8150b0341802d2054040291070b0708046400940b2040c0f8280c80386c042e0b40c16448000411402003548504406154072180401d40c04001c05440913030001d411401003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 787995890 1250 787994640 787994663
    0x290a0525081b09120a0302061003050c043b07090c0509060a03020f0a0305040c09142e140423131506030b0f06060405060d23041415070e010c 62
    0x45403100d80261003084011002045c0008203414082c0c00d22501034404440328814680a10101e40001001c405801c025100000d41c0c82c52100c0060b5504400c82861080f91020340011002e610284c000300031100c0081c0c161600300e40d036a840141112260180c1102080b000d0003856a9840e200028008041050401610f050004820038400e9800341c9414000b207640c420903c020301c6004045407015100c0c002c4204403400c02d000380003a00e0303900105540d049907130080010b440c0d0008851060542444203804007201500d991180d00744801081d40d4500407441d01700c26000c850160080c403d1310040a00c3d0510103a00d80003e40301c80450440c105a400910f21001015006100e01c9448000c5000320901015030a16455040244201800061240005000c103000b2941c0300000c9602190401000040c200819600102d0382c2244034124103142210310104024442d410a28003401042e660079124540707101c070403101c101c4800341c81100000300c11040402895000c1e0303421801150060705400382 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 787997140 1250 787995890 787995907
    0xc0e010c1103030906070c0611120403060b0a05090a02041e35030307030e010c09080d05091c111c0305040b0c010e010c0504050a0e0f04290a0525081b 66
    0x2104d520006003128650040d40d020404236a011110130600034072400500403c5203050f1007491180201e003c003515040d65000c0c4420650f4444641400030500034000b81c10f40c0c40e181c4510310094116200c1c02181064184400211a41c070b0400c02003540c0d0a5401c5c180c0b004c0c2a81d00c3c080003d040001d800c4808416207113030030700f100020405144505901e41d03000c01c80503a1284100d095501014481c800d01020301070a101d403d002050184405d40705141503a2101000300c000f480c83c045001c0104140c0311504006024840103421050082e1400c2c0c51007680c0c8640560341d105803003031540d4054005582444140401c0c0c100100501c104184040042004001c0c1810389007101d02030440d000100e000000d040090703003400707100100281702e0403800c0555803a000203490400c83d00248020006040c03640c0030076071880304903580b280c3c2c440402880b032018a8400070110080106035480c8541c015000d00300e403c224820011520b1445099450a00545031060750a842081e5a05002c605200c01e0103403e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 787998390 1250 787997140 787997149
    0x50601110a0c1d19110702060705100608030c03070206030408070605090d120c080c0c01090b011728030f110a0605041e050d0e03010b040f0902040c0e010c11030309 72
    0x100700c0e0058208400312440c000a0150700d0541c0d810448124030b1550070442920303403000010007070040300100814030b266040040300c128451001c00a40c01140400e5000c24810001680c16542c020301c04100052611480d101e50389001f5070580c0c9510742e000b0000c180041c00c0c0034010b19001881a521503041c003e040c2d40700003e0710800c55298005501c4000406542e50f40105046008600c102c820421030b09440c0c40101070600c0200003080c41403000550200c10502503000214090f004005d4103103658443c00810055014002e0060641c892801c001c0350351980814a00c00f48406100c0000e2088642e9405480010307000107200b040c0078170380c82004d2000800b1300c28424040d10a8500103802d181c5450824904c081c00d60004c030320704040010050000b107000a040814552900f000809003500c040000d0142210391141500581004241b00031403480c0d07003203000c503a41300303e4050103118407001c0101c03640341d52401001c0c00902c05212a40205240485444003501e0240030f903441d260014000c00d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 787999640 1250 787998390 787998403
    0x5040504030302030708070e0d0f0c090e030316021609051e0a020a020f010605060306090a0e010f090203010b04051909050705181b0901090e060f0a06110c090c070605060111 76
    0x54020070380000801200f554000b1b05c440d0301070f100b401e04a40620442020600301030301440f000b0440fa401c0750017001482411009000188601802403110a01b00c02002d13860350400e03201442401c0115141d000300c0c038004114800c00701c0d034004440380e01350300d08807004000e002c025001022007100000750789030280385d04041b140f04d0403070100090303030b030300805c10009240c43c88a94982c0c0645e49801070601c0595510011a904090210358100a80e100c0c0140c0c1b0006108140f66209291300c0c002101c070403240241c2103034400c903000310000c2156903585000c0c001600d008464140d0406682c0400001101080d030116411b540a6021189206e80700c101003400c90325841d105101c2910031108021040381503804a0307000a074600841400c1170780c1e001c006000e0500501928070441c0c00070000581d035844800400000300c20080c00146115541d0501410300c1008c0c0e5030f002c005009180445200381031210f0f8042c082d1203c40d604a00c0c2107410f85a00004103800b0782554100103000f051220110800c0010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 788000890 1250 787999640 787999643
    0xc2a0a05070f0902090d3c0201030c0305090c040e010207080301030b1005013011120108010c020a030e04090201050f0d05010e131a18160e06040e0a030c0c05040504 72
    0x204841810304602c56082040c5501c1810603a0041101401c0c94481180c1407800f581d02041c00ca40410342078200d54a101100c4e8080300112400c0e2003140040c500c2400c200103401e000381c804001c24042803808505030b802c02c8694081c5580414180301d0a8141603201804400d1070800043c2015800d030303101d034030700d03802a8415030300d6045000502080340d440000141c0140002d08104030014140642500d0481c06c55a9810749011114900465890145c00c45540f541c01d418403290758034403801003109612000c0c0100320b070310b622f030006200c1e8150000501e6203200d034054550568401c0081c0800002e44800002241040401c0c01258601c114050140c000755a5410001c40c0c0d81d030524891000c2500000c08244080c0391a48442c00464587c070303000c080703460950004460999484283c035040c240c00111a4056114210070703007103000010405002a2245541c2070109500c880080205075031000c44441e00c290400810040080d008411030104680314001c1800307600d80d1500001c0c200e44040f40d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 788002140 1250 788000890 788000893
    0xa110a02010b0a0e01050a03060203040f0204020406120c021b130204240311030408030610210b1c050d0f020f01063c21050a0f0b0c030c2a0a05 63
    0x42c042c0b515241c206400a080400e80544142d80342c07200060110030749110151081d640000444c0034040f1407a0314007652900540700f9540d561343c0340d400074029519010382072026480c0100d1264400c0c40411100c05003c40128900ca00c0319820041040302c40104c0a421141a400c0000250400b20000b026460301c000e414000c0b11288034500c042c0940300102e0010f20048401c2040000158048082d40d801c0481501c0390080c030412841c1c10348140303a0304070b107580a040c1d0149204030702a0b07980d040640c00820923101c56113000420503101c9043c44452400901ca034010039000c440c042d01c507199403021850184103d0390884050a03c05003100c0813900004842c00580c0038a01070030451000842c030080c0007005000e0f1208034001d01c008040014040c03012591004e508803140807a8840f42d4500c600d0b007000039500a141c03240380032200e0f21000c0c10120b0701c000c2d8080008101d00820000e0303d00c1141158111468035803001503001100b07071580111004000000e000804006003003001c44040d9113f81e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 788003390 1250 788002140 788002151
    0x31c03020d09021519050406020703120203120109021b010b0303030601050918040609140313090b0406090e060106020f120304020f0d0f03020c0f121009021c03020c091602060f0a110a0201 82
    0x22060f8172030301308403154103000782000f04100d81d030341c0090780004907178024446484464056004a013140306000c101c1202620716000824171801c81e600400585034461103401002501142d442e00741c034000d01005526400c1800000c0b00355000f00000d08110b000140080f860096002090150580a0710305507840c0c5e03501d4017040300700107411160360f4150304100e00035400c04286d119000c1e015080ea000f0b000a5648030031000c6120b44503a0800000b800a0f20f10601c42c0489074246e0b540d0f10142486034000600c14403141c0e0f030385405c0220301c42000d58034400300a0300e0f540c0c40d07409021054602010340c3d03801241800c00c1001080c14800020042d5100707a02074040e6580950030051081e0314000400d00c55103080000101c2d40c0c100040400249402c044007040ca08100e00004142400108852000c00781c084000300405501181100b907815046512200580b0340c0101c04900310340c00000140964015404142c0302c03102e00c00810f038006264075020404000d08820f1030340c0c941000c0715580c0580c0d10341c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 788004640 1250 788003390 788003407
    0x641030f01090506100c140708030c070e070504090b0a0506190e030d02071e03050d18060c2312130303091d060d03050d0c0c11031c03020d090215 64
    0xd0300418014000403200303005509000c00040c02d03440d61117510500303200340c44080c541084441c80c0d554020900740c0c0c090700d519940e40c91030f0759126071082e03090403020700500801140c0d50181c056894003403201c699a05007840e0410300d4020090141100e203681c0103109401c00a0a0346c0c40100520711403803422440751b00c00c4c88000020f0107c4510000e500c1c400c0c1c0010201441a690002e42c0d4412940410100c4109080d2200c1000e12020b145d0005003090184107040644984c0103128802c201900d0001d0100b6256504000c80f40c00040e43c00080460700321001d80400a0391500380840068442c106441810040070252516603000c0c0c8504004070040c000b00304241070700045408001c1c04440c540010040300081820003448006050700d1240030000d00040916106070181d80e45035000800420525420ba82c0282000c43c01c02e0007142e0400e0361458a90041c2270200703802d0448034601410680c1030b4141034040e0083d4018a0f0360505069a4900d14009a55264000070b9010420024a5502c07500b5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 788005890 1250 788004640 788004661
    0x51c0c090615030504020303090f0f1c0b010b041d0403030213080f0d142203240507031a0105090d050610090c1704080d0912030e16064103 61
    0x10700070b101c400c0c5840c2104100151302e02008444140c2401c0761001c8204a102000602c101c800881041e0054102c0004800210328254035400715030260520f064141c0e0703142091100351085025407004104001194840c409101d500340b50810312a003400360034000f547c070490144051a501035521a80b00406050185070f040c4000700142c07000b8034201e0014007040c01414103c0c42a07000070302c0742c5005011270001c40e03034412414902860f440603c066400e0008010100190401c01514044520f828081100540244100036000d0348002d4018440c1d600312005540980141d41000e030420308800401000070410300510303100d050903c0041c070f8250b0a150120301103c000130b042c1c0050114a0501071010202c0c0051140e00c254000d0076182d4030400703440b17003101500004030000d00450900c80e0030f0400355056040164021504402c507441d20101c000d07011409102071159101007248800004d9003c0002803d0300c00402d00c5840f00112000c060300000c4552140d5030480210324000310070711420703806 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 788007140 1250 788005890 788005919
    0x60302030c1b0109140a110f010219050303040b060607150e030412060623030304090b13020d090b0702120d050901020c03221202060a0f0215010605040f1a04051c0c0906 74
    0x100d00010114491b140c3e68000412509100c4184900b040900b4100142c0c800c0101d54000d13020004c0d41e420008103441c04507a00d8101b80c40481b45440094001030250905c0420b40c0c04e15600a00c10741e05018420b8507035001401032219420f2240401c1101007601d914a110b56003505120390f000080707251030110200040855441d0b0149002800035912000b590b000094606440c40d4400c0042e1240100002665030800e0256010085002150000015641c1d601400500d405016810605c1c1e54502c0700b20b0700c0f514441e590a004000500101005040580c131595000c000c043c00113113031004c40020ba91468101c0040102c0c5400700c0042c10740280030b689069801004a491515400c52441d40094664010950440d003007215203042400c0451003009480350400034080d01c1200303541c42d00001802e03940113020708003400081400c0020324036145e400c0d0b000c070091425003050030507007050f0400c160000400078480340241c07101500000b196aa5004000074441114002001850403a0280030f100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 788008390 1250 788007140 788007173
    0x80c030c07080610030b1003021e120a02090a091a01090b150a120c0e1f030b120705010f02030c011b110d020a03030b04230f130c060302030c1b0109 65
    0x30024402c1c01407841d04444144c1c00c1c0d950040d0185181c0e41ca0504444e102401580f01951005000c140036441360000300004200a10580354250141020040070759660a8048000c1d0002001da001903003901d000d901074858940316010146041c9050180003078004400c2c1c01c43c400c080ea5513036081e031451a0038100a4601210030000c58144070b0800800303403102c02e00045000c0c0a076100d042409020303108100b0700c91807810080c494810903140f10403080c8030700340e0704525001080c50709407121550301e0001140003000c481e40004188186c100750045400201d00362851065100601281c104088207004030042035080040750b020135640d0318001031130b03058000364107441d580180c3c00c002e8200d903021490207180c541605000c00c0d1441030b100440c000700004020040700944c0868400020601c03801d200740940940e4510a07855182c54411406000b02c820008041c40080c03502000b071346001c0c1d00a03642c4030790116889410036070035515071500fa0a48000d510750380d0350746443e040104007110540c8507244 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 788009640 1250 788008390 788008393
    0x50f0901030f03080c040504020705010b100309020a032a030b06031c0215101d041407060504211a061f020a0f020d08070c09050604020a0e010302070609080c030c0708 73
    0xd500d59121100000c03904500907040025101c0000c107042030000890340140130143c01156147c072182800c0f4000d1403408a00b51003a0a440090a0014803074040d120600c4c0c0c000f010054070760300c0c5503901c000c0e0f4206a42c0d04c07580e800702e51070b001c00b40b41c3c1a4105400210300070b50904840d0f11300781003010300b89101ea0f69005407160140040c1488103a002500c0d1040c400c1346480210541c98140d1624018401a4014400f2244600e910107054542401da41d014070702c50352800c0c003140300080c40a07895103000c1c091040020401d0004004078010580042d4200110480c650892640744d05c803603d6022800d000d00142e50a10418000581007003c2068070642d080c07508100034146a44000b9100c05280602a02c1048a0b0900d24250340d580b0f21036694190348410034903510700d428901810745051520589045a00c1e040008086040c940200c9000396070680e034004640c030340d0704010340007508107443c2030b22419554180640002c41d034600030600955203200a6844848010110345440095080b0841e1b5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 788010890 1250 788009640 788009659
    0x2d07080903251a0106020c120a0f1e120f020c030d0815061b0123060609040504081215030c04150e1b0406050405010822080d020f0d06050f 61
    0x1081482104802c0309420003200c0c005404203041c0400b030b1850545044501c000311000000d80c490b00000d0f2612080c4e42a110044e442242c000b40726159001c052028000e01492403440340003481c4d03207270b40d018420f60301000760300512025107a00703d81508113000b560100d00384421902440360100001284018210014007120b62480401810b00d5005014144602d0140896680e1580c0e6071040e2200c25000940007005820000c0718903000e800107030310306116503490022423074140c41030010740d074420710340648038910f4a00540300b8072004140050044d41c110000303100031041e0320030078075105005040102c5610144d40c02c1d03030200340c00c000e0701c43c001d036210381d140a9603070300c615509a9500e82124404884d903061a07885011010620243e681c0f6201c41e81c40006001c0341c200d1300074010b40242e44080c0d840c0079072036552003c030003c10403006000603440c41441800034009007045008050b0000c1021300542070984694414804c0d030087c070030400f40591128020722440c2000e05041080b100109c074445078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 788012140 1250 788010890 788010907
    0x204080303070e0409050c010e06070516060f050304120804170307020c01030621020d05161701143d060c120c030c06200d020a020d020f0c0103052d07080903 69
    0x91f941c04090301e490622001068a01c8a947d8060540f0381d0150040e0a50f2010001c01000c3c08507640503001e8100445ea0344400303c4400b40c81501502e208a910481c0d0490030740391843c00350790649000740300711082825058580200d4000f400518000c0380e41d0340080001503440340004d82a95079940040016020003900003030100c02010302101c4503601a581c203030700d112403400d1241c10300319204066100700a140400007260262060a001681c40c000c00030800f50130300c815040030070070050315266030400101c10019107a4541c1030a010f0390450b01d44418043e0a03e45124094108c07443d48400d0100345d52405800a00007541c02c400c94501030742ca00b00d108140d131030380e01900c241c0b45a5006401c841e0703a00001944680741c10791501c1c0d981403d031001c6890790040d040e2000650b01c0840f88c20010f01402150140e001c0c0000741115a0441c102c01070204e0305260801103000380801800000506034907210000c240d00ca0002821544060303d0010100c0d1500f0540174082c040003400d9006180e208000010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 788013390 1250 788012140 788012143
    0x16080f07050420030606040308070c0806130b16090314071a03010b030c03090c131e060b03011e050405070c05071e2105061501021203092d010204080303070e040905 72
    0x11000352040350007a101d0303c0f03480c0411264010780d00001c9c214800010700b0301c2400000c212100841e41d074807046903081d6560f001500d10b0040d540800400850054002c80d5640e0002610a4070300100d41c58003000e420b03a80d88481041850f5601d0303042490b00070403030078444000104c01d100b0100341a09000340c0b4551526640032494400240501310000d404401f00740b8070307001880259198000200604604840358240030000c00c039204010400010142107803448080718050001103070411401c032802c607845c05c00303100c0403620ba00702e0a0034000b18080010a00e9504d038450302d40100200d96510031951403034901030f85083e0040e085001846040e40003240c1401000410b0350940710101d40034001518000c41c180c1c2d280300e078518000c00a0007130b141000310703142d004a44030b28604026402c030742d51040345043e0b640844c4025580c5d0074031a00011103003030754202c0190724a0f00c4241b50700700d106240c00003161402d00b21303009904080c055800c0041882643c0d54021070007d0388100c2290100700c01d2016682d0036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 788014640 1250 788013390 788013431
    0x3090c040b061b0106090e0604020307090c0c0f0b0f1e190e1504060b06180616050f070905062b05010b130207050105180d1116080f070504 61
    0x5a200e641c840c0c0000516880d00320a5404103007941c801c1d80e6070b44031010303001c0d03020304004d008003440c040c6000c0301503d64140010741c0c90b0117160007070003500301e89061142c814080c05c1a02c40a205121b140215034001a0ba150b031440003086c0180d02451150400400038090380c2000341c11204031408a2110103001400c034505a60400031a0040040c00e216210b600030240117804001402c1d40560510310008000349a50b852086225032401c21041960800704002c90140c9681c402000351000403140781424110010000c10000c100b58240c0341ca400e80d03620346428014041980582c1100c002041041d440b80506600f1040460b04488441222099081d036490081410022451200342d00c0e010b0000c29848032401400140c00360000007121262840a9400414225110340c030f8640000d2110b4541400c949108940d8405400c6548040f001250520744094804415009000880c1101005002a5801801d181000c1d11480e500c0790032660511344140c4c0311034021400c02844420035000030782c02 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 788015890 1250 788014640 788014663
    0x2090616050f0109122f03090f06040f0324020a020307060506031506010305040311030c0c03070f051c03050d1802093601151d0a1104031112151b0309 66
    0x1025520548400c18146c01d20303807064508084004904202c01401000501ca042c03001c1c1d51502d501407048051106e907101e10720130300d076030315516010600c00280325000131075101c00c03094104c224505150580388208c0c5e000d8140240540d100080f5801040094003a0344e51010040300076150707212240841440c041c2c00141a20b0406607540300050030107002e4040c0c042c00000540441c0d40740c0104110840c2d1302e034260104144a44103801d40000d14aa003080c190007600e0307010f0034011401200381140c0340890780360902141444024060908801c0303161140c0e1844504105040010040038010700c00d1a08015243c50303108440c00040c1452003040c4281c141041c0d84021311040e0411008502c1c90040407180120300d04017201000006441d10710460203104406116140280383e06c86510312000c654a0005182d01010144020004104404000c00385950081c00b41019106202152810b01c05040084000f100c0740a080c0002c82c202d0310806442421509551451814840c0c559a544c407100e505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 788017140 1250 788015890 788015897
    0x71206020307031b050307021509100209060c01050a050a0b100c1202071d0109060b03010f050603063c010507030914010e1207060f05090f0d0602090616050f010912 72
    0x22840030392180c3e00c13007854200014a501103c0d5110180281a030b032068400c03400500c643e0b04205900c0300101d80031801040c850004104100c03103500f00301c001c2d4104440c1c295200344207011507c00310200780115403055484c41c200113518540103807507030102c030801031203c4d0049040341c02010089410450005135650401a6035040a08100c4101d1404500b0b40090015040305032480050000081c2c0030360507100c000c0c50501101d515090103c1c03140c0024420b030440102040003c009034200702000351340200001d491a06406111010340d1400d80c14400500c018158140041c594400c1d401c0085c1580d4809107410f41c41c0a044d914000e004d0b840301e000350408580e10383d00300310042e80908112004180041c04112070244600000b41d100c2c142407241c000491000105036106034070039021500318450041010f4920182501407024084401c41c1c201c90705507080140400ca69241d1000e800f0b503200250f00300503440244d141c001e00300100794a0500c4140e0600410800003407070080d000780048428038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 788018390 1250 788017140 788017147
    0x30203060603071409060a0c0b090c1309030905150901030e07051503130b0f010807140603070f030609020c070302130e0309061602090f1e04120e030c090106020d1107120602 76
    0x249041110f11804c1040f5501410004201f80d00030303001400c095145000741c007a041103070f03288600136841c3c0d900c40d94000c3c6d101c600c10701c042d80d15640c154440b0144500130314252410321348a4012602c03044d120881c010b260240403070303100c0d513a41e8503008480801c82900054181d051908c4085440c2c2c41d00380c0c00f01300c02c100002c000074140303000c5040c44020701500a02d1115a03810b00d03a05680c0565400c1c0170345482805240000314210310f41e4a2040e40c0c00101804061450341c4208080b18140082102c00c810541c4448000078502c01030300290810503c41c01c00352031001c2c6188104204248204070880210b403c0c808004000c0300003105580d0780340c0064030303c01d50b10000180d01c0d0b44001800c8800941c800301403424002c0232030311249000d2148280300d08400d100b62030b0f81c3c811003490900303c1e00100154210891103100d0740c03086550100b182000340480e00380d840718500148260307200340c00500041c4c0c852152141901d900c5003499095400020107061007904020314100a00300305a0050007242c1c000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 788019640 1250 788018390 788018417
    0x712030302090301020708030609010e191a0a03060609060e01080a14070306061508070e0f10170a0b040b01050f070204090c0e090a02030c01050405091302210c01030c03020306060307 80
    0x790100d82020744020021950b45505240c1204580c0064858900034010741c4004603102c49080d080d82e000c0c011210700b2803440194110035001400321150080b41d04003070306050041070b4441d40152400755200c1c24001c40c4440c101014001240c489034410b100d6521154010015080041807003042c0607089a107c440401041c042070303145c1541c0c1d51009020b2841c11200240076803846da07041062074102eaa0f90901611801030858400140301c0206034003491040002d40c1500d008850304001003035500b0220881840c05580301d5403a8011140444159103920002955280c18844d800c038291090a1083c200801e000d100c429900a680000b4040d5503200510010300451039211002402500d55949041c90000001601c601450008074003030720407002d0000f13140d8002d0007132350f043d20790180110170f072030b92107a03c42c10b00130b8a44d00301640c02080c0c0c0502d40b11410290101d400010340e0303150003400e005040000060403591005040381c205481401170040c40c1c3e0701c4000300ca030020b207141707003025054904 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 788020890 1250 788019640 788019647
    0x1e0b060a0f051e0a080d0e0609060d2c0a050d090612051003120e041118061602061b060115090e04030e100f080a050403020a120c0203070b04170f071203 67
    0x61051103640701c4c0385501c0c0000e0007600028040741640380d039525840c20351818010721859008214403540e000c6024001e00004410343d42c000551106002054401002c1c40c0300100e217548800c2d01003901d01e0304503002e65818007400b00121002d55030340340350004241d03150400081040310b0840c1082c40b901e881d070011451700310400c01d00c03001550b0400c1c5401c0589d8168007000d0114050011201e0146d41800302109684500505544200c000745204a03d8460300d0020098103a01c0360003407140001712641c225002d41c448c4005400340340488500c100c803e017080340a1601d042416802036000190010306881c400380c0c80003601048a40180c0c58810300d0311a490305480d8507443e2104560070048007100810110303417042c29060b000c10b00d509c0e140341c40d4480d45004000d40305d04450140160740102e1a85001640103202c0800d4185c15141c444503885980d40002e081c40d403103600081c8802c4020406003e50483c208200d001581408028462180301e4206140c841c0005d110b541c00e241ca00000b00402d0500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 788022140 1250 788020890 788020939
    0xa1203061e05012a0813090b03060610050d060b0f090307090b030a030e131b030c020316080306010c050d03061703070201090e0727080114070504050910031e0b060a0f05 74
    0x910030b580c9602c41c103950b449540405a00d105080e4968141b10014040d820b022483d5406684cbc058034140d0901a0304000faa4640d00c0058400300160b6190300004011a00002424a20a26049a40d82c4604d404205840d004c9981c120102c03003441c2c40e8103041650342c002881011a6818204080712a2242c03001405e201e10341c00e07445203800d040101682410000c3c84000e041405152803c05c01006d03222012641d9000c0d105000300e6070041168880d0110b4501c4028550003001450004040340f400d40d282414611103003186408039851303000038481c5000c1d526204117020b11100045090224a8000070700481c0d103441394259110301480072400700c900c525507101c4c1c40c00c0000c0c260001010f504007111b101d2034440c40307058069407800354415156120403a440b17000d005103603502401c2034104010031000c540050442404d070f6150300e00003c0003400d00104a600c809465072042054a40c9050000d885a00140300511a0f109000188642c1d402c1441c410203031581541c000403691508602c0410301503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 788023390 1250 788022140 788022143
    0x613050f06091309050715050f030a1d0c010e0103021813020c0a05060f010506040b0f090a0e01091406090105011209020a27060e0f130201020a1203061e05012a 70
    0x1245459508404441e0f13410007041c691146084036441c5507a02a03130082d149503500300c034001071400c016103d07130781c941c1c1c002850b0402c81d406c8002401a40201d21843e0b1481100004003035a0419108041150b070800c2110304880b400f82015454800d0051805090000d0305044030b1191580c1000c0d0300011100b03038141ca6409003400c0030ac076402d40640c10115030300c6074110b4140c80d820341c028002140c2400c0060a480403100f22282450030800104030b002d00d0390308122542504003402e007000088030480c220700140240704221000808000d210fa00e201101c1c4010700b11030040b80410010843c99a001c0840004c680c450900001c04111a1002503009141276100301441019502024940c62188480c4800349110364820021242d6940d1079004001c0200c0c0c0b0480c915500700009924400003c1d22049091300c140f055520041311542d602e80d812882e0144400040d0362a038062119122560341315a44c000a581e004005038070f0301000a00300700d10000d444c0c0680500d16003c0c0e05000341041c0500009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 788024640 1250 788023390 788023399
    0xb190c1b03022d061f05010819021305030c0a08061b0408070609080d02161716090e01110306150915033d031b080316050105060613050f0609 62
    0xfa00c2030310381a000800e48072039076503007400b8603004070345000ba4400025101c042565a041406441d050055880e03000003044510400c0c049042c9030f0711420703a40700411107210b4220510601906000c10b16207012860b908440c09450702d00d405000a01c40060501e6004104800113016065510004407035401540c0c0b04c0212885000d0011400a0700907800c03c2c1a965560100c0d03c1800b062201280c0d2904400c505098002804178140f201c03a107400d000709059000e0b0402c5410840f0952417001600c3c2007503101d601101c0e40d9a65200443c107003030051980d80284c440145066007401000111032124480d21101c48410000c3c0090030b6031206010813545800c40d41c01030740c60b440e201d006240103420300440c1106810a1a41a0303103103125800c0700300c4150b5081c007450711085003543d07101c1d02499481c502007100d10f1800b49000406010800003413051010344c0603c040d0704001842d2450035518080c00d13540c440d00c01441040440056a41503004841d4201d640c7c2c4403003008480440c100340b20307011499400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 788025890 1250 788024640 788024683
    0x1215090c0d06081c02151303030504031b0b0702060115092606070c15020c03180637020c01020604030302071703071112032205190b190c1b0302 63
    0xd60b84408040f41310303d800c0c1e4090700c00400d01d0002c092141e0104031203008490010300340130004a442075101580c410b101c0d0619841c03804c0c0c522920f0b070144850031030071980d00b0091000c00002ca981408801c0c01400c03201c2c0c1640300281d100c1400b6042ca03485004409817000c00080310608032400c0d680403580b4910f1a020380c1d406040585009200751034502c02a60340e00c0204c0314a20641000e8400c4600c41c48060015509103500b0841403040c85020b0001503501100c14407002001042041d104010b03016008000312511607000b030f0002160b1088411581590031145011560b40d80128620764016414900160788013000d241c0244588001084952150400301c00c0007852500201000007101e0204101c031080c42021950344e0203171108480c400003c00010101c0944031050b120340e141d03032074821026100513030700405905403500340c90f0000f5511061024280100300d0742044000d4051002080709000401d20744002911603000100000031601508021200b0725109010142125415001c520700c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 788027140 1250 788025890 788025913
    0x6061e1507050303090d050a0813030c060f02090102250b0c01090512040501021b061611090421170402120c040509010c0e0103062907050f031215090c0d0608 69
    0x43d00e800482d2010701600c40c0620340c1640a02500960310082401d0340c9010095451080824185140b40b00480034007807000444000a00b460040c8103240031b40c0c0d4801030f211886440020715020008960481c1c40340301401e6a0040c15403a003141041d51011a10603a54070b107585091030052140c2c52003d04580140f01d84000304071b00758030007041111026801c540c1d00c10400340100001703183c208015640070705c080080440110742400d0400e43c0398021074642e41b50085e40004a500504100c504a0340c043d40c91248454180041e0141c414007082450044074105e1400541c8008001c0584040d03c11000c860340044038000801c04d0724030504003c1c10901917410015039003806489072803d01d5010030000001507507154407034072a01040b46c00c20030014503882048401c840e100990325400d815410000c0081d0f1001c99801c1040241c004003280041d0b03600c404d401e81e40301c5a40e80140000a03d81742c1c04003054081e80c1c134200f1158105545440442e40e84000d035200ea802002e45600c890541c1c0654074140d0ba = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 788028390 1250 788027140 788027143
    0x522090f05011e020306130c0c0804080c01091706061e12030307080c160803042f031002090a0b0901022113090c082e030312060b030c04030602130b03161106061e150705 74
    0x1004030400e0b00c481c03820075100d061010c091151a80350408503440306c000103203940b070450b040a41000b122482e83d80d83c840c0240116002d5184100d000c112030b480042803088942c0c2c01030310244d100704004140d608044441403040ca0007440c190340580348060200c0030a00348410824101d203005034500146c81a900d910714281e001030407070b10b04944240940e0141c0b5881581c64000c40d03040c0d0800500c0c2500d2281892215825908280b0310203045128880c44607070201240080e410860000c1041d03252141e0100c144103c00d005580c00100f0418101b1032a17106403600080782e10741244014616042d040008000285c140741100e03a1078075110701180d4008141500040001b07040341c40106c0034883e0030b0322141e0720040e5110035601543c885104000400100701ca0307501400e40807880080e03100540b0740c0c0d04428111600295420781e400d00159488002d51904182000c80422130320000d40802d1138079000040c1d4250748400d10b108101d485030072005003030b03a94001d0821209000d2041c1505c90043c3d08009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 788029640 1250 788028390 788028403
    0x60b03071106060103022a010e0d050c07050f060a051b071d060f0105071203110a050a020f0a020619030f020304030305100b040522090f05011e020306130c0c080408 72
    0x169950003802c002c81c1c095482802150165030f1001e0441815410011444030724040d56400300059550340c0014005070b00c002d00c05011200756941d9400d84554916083c3c07401d051082c1e010910a0540342c0b95010f903611b6680c1501e0001409085c103d49800840d108220070072001c22680610303000300240400c140c0c5041e01c1900109030a8504003100347d550030244690880c40210b1140401c005005010005112000700c1e119428186000304000c0600d219030b88030ba130060076038140811004144020700540c100848103455485000601c42c100700b90700130640500c42c0a680a802445046041115a000c0d410050082c2c3c00301004658a280a041c01001071100b5600301d80c60210014000507404042002e4030305640c00180307400c01000e450490043c6424061218501c40c940b0b030742454001c1070308048008101270240002140c1518801c85031101e5500c04030003c11040c0c41030083c440300d901c5807803000d528000582400200d01e2030461080e101610042c0d00205480030020380801e51030f4010030503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 788030890 1250 788029640 788029667
    0x71d03011b1112030f22080901080f130809060f030a15150251131a220807030906170402040b06040b0a1824080a060b0307 54
    0x3071440c0080c000b0040b0f40c41e80034010382021800030074008541204c5c40015840d4020300003082800364800c1a8440011190b060501070b42c280101180020f410358105030301a80c00101c0c20344542040c40c01c0c254180710407001c4c100140000c00040360303403c415240c40d401c07506050440604180c581c5450142e88020740380408a45100ca00740742c03000501e54010303d0040882601540152034610381c0900d83e902402c0c0714040c0d5882803441c486550303070452014a20350086d00100c406001c40200607903e645110f00024101d080510a540c4400000c100614080d00c0f8055041d20b418034145c440000340c104540640070368511107044000994108030340d600041131003a1103034031480c0c4629607940f002c0e00d94940800b904117401120f1340008006150580c400000442d00818903070a283d100c4801c01300e5900400c4484020900448055010803000b943c0c03400105515204800d401c02d4a60b6445024102442075106024100002c611500015008140540003c1148a4880c9490500184008596a503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 788032140 1250 788030890 788030897
    0x13051c11030d0605040e15040807150603140705011806050708090319031713081318020a08061002030f0a091503022502060a1b021806100314071d03011b 67
    0x41a080120b40441c5d0747e4010700207810645010394907500d80f03c60b140d000e9001200d81080420320200320b80d00070700c2400003950281040f51107180d1031404840c9040040e4100c94140071400301e456030380c0800740d180041030300c0840c40c3c02900c07903185203080c9409000fa43e0380180c0c1805901003400d480c0c0460000600c40c680203985481c00d04002450b28942514140c8912490b0f13049a0045008074241100805c1e81080803244030080e51756400568005020400501d0340c40768000a1180c0d000790701001180c0c00984c04c458154002d070050a02a603a4480d20210720407c00c0d010070f4650340c680c043c50b0710400804d01c4080d41c2c0c1d2900c40c42c900040081d4024011031200350600052a107804100140b8221026800b50681c0e24201d0000e1041d590307030541c1c4003000071a112062031000140c41f412811390010040c0b46507040c25062a40c00c00184403102c440c56000c15223064810000303160340300842900005542000b03600b8105480b05080c41e00700e40064142c0540c2080c2c035500c5900381904d480f141c8541d5070713903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 788033390 1250 788032140 788032151
    0xa0b011706010603020406020c150c1006090e0304140415030f062a140309010207020604090501060e0111062419051504060212090402040e04030203030403030513051c11030d060504 79
    0x10f05a0807401240200c500590100784030740460f08001503a03008512000703c0321410100d040030a10b2400e4031320104081c4c03d980350b280c204081d03e80e0380559851108114003950400382003014841d40ca9034a0b007611881161502085018640c0c071140940c040d6401c0000e0048035a11404c00c600070b007104110000c1c00d621180c444410400c80201032640240c22540c52142002c60000d1095140e0400b030030300300581d5405c000c0302005a44890040000f011003403808200c0e58540600a004d044880320700c0703070611102ca1410000d140000c02e86503400100c503950944070b068031114a00d640010181c1840d00708240c42034495040c0034861aa40c100c5030304541104411044d484900d40c1806140320700000740e401307000107801565900d0003604403050050f10040c1000d55800e440c600e4030b04166425000f5800000900c0b05040d418050613900c110011030300310805c0180c0d503600381d8810213446800000300100207003040c41440b0700c0d1005141076405c801c594a8512280243d402051544541c51042d80b400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 788034640 1250 788033390 788033399
    0x304020f01080106050703110c0402040602010e01060b13150c02090c1b070b04091109182202060405060705161508091b0603090c0a0b03011404050103080910020a0b01170601 76
    0x120020b40c140c42e03884c0e90b0365061801c0b40d40d06507214482290804414003a13040404815126407002d00004e041550011541c1c9000010381030844113203030080c0e01c240008100500141d490300602c81c04542800d0881c080101c941c1e13108581d00d00440d10020350080b4000d05001140d048680501048a1200910104c06220b9918295241e41c40c3c07040703802d010703424401005103110a5009a6111001100c032034685a941c0d40001c42004408450409503d540c000b400f04026070340343c070742001c42880900c800d5090016000076495004078480c5512903c000038081040080500c001c0da2030b0a20603000e6842161610071480d280840d0700f02041c00200c0800004181c4840020150b569044450402d0034aa1500060050940c002090640030784201c1c001c2c402c1c0c5444004081000700303881d006131610b9506102d0b19000d07031040205c1107403081e03003003c0040c004107186408032442071901300c0b00381420a5000c0c000341c0c02d0003012170010b04100c0382140002500701c15800d80d401807000f80401c0d5042c580c0c0302c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 788035890 1250 788034640 788034647
    0xa0302091f082d1303080c04050109030f0816050705010e0306041505070c050604030806040e0d2703080304052506080c090409060515190308090d14060702030304020f01 74
    0x440c078000c000100a01c1c0401d8944103654a4048040032040702a10342c01d5110303070b901d60410b42c1a54440090001e801041d0309240d400510076410860308100f0600e4149024002800c03c1003602018200c0e803621500101003111540c1110301c2134004074480741d01c81002c1c0c108591608101c0c454540400d400c84526071a80c600400e5843c4140e40c03044600b42c49a0340b0160380d000030403005141c8414404415490004100c04100c00c520640c0710307540e490303504d00d003072014081a28100710303440c60940d0001d0101005c09801640c140300800e100740342800c80304030041a0341e4600505500c05849041c001080c04140040440c1d10090800744092283e8904004040e140f0001c090740b007484001652840494800508140184115032006101040c400256100d6204070340040e41c140304004012156820982490b45044a0310103001102c44070181c80c548502089206013a94540709580041088042019540ca591040341500c004c0341c0040c03030540c0300a5170341d60003a10280e1086400c4584400720790321 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 788037140 1250 788035890 788035939
    0x1905011101061211010207080303090304030c0e070804030f12110403050706050f04142b0201080a0c022d03071a0c03040213020d0e1b150a0207120c0b0a030209 70
    0x2c0c8186400070704205a103420000c5443c00c51307003e045001d08540012201c40400240d80035001401c083d681e80d601c0c3d031915a410100030f42c0301c0e042144a1f07208000b0501c1c0c0107841ba0f0f51140c1c042c203080e0345080410408884030303080d81800c03c3c801d9152014284d440442c3d2170282c4190fa101e1003c581d211903d50070180c840d0300510264080541c800c00c010701c041d043c04907100c0c42e8804041e20078885003034a8a10f0482c074041500e501c1010105421222041d5039001005542040f62041c04108000700c0b404025140c1c1600300341c4215088180d60780c6241c0040f03005520110908910a9a441305840d00d80701151400309803241e56080341ca14003140b2800c2001301160301540c0e00a0520007548070012412019410030b8520318130315551150b9000c0709800a00030300134401a11100030b20380410100030050f617880485900c160454081c000e80380031a800040140079900c00000c2001d01e540c803450150300408003a00100504013000c14840c100340c1d0160040c060300402104c000d202d01c500704502c18250766 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 788038390 1250 788037140 788037149
    0x90309080f1c0c0c0b0306040507030e030301090c020a05031801020f070e01180902030615180f0c09061b01020307110d14030a200d0e0a0f060f0605190501110106 71
    0x10081c80710110380c0001206281c2c1c4100341420094440c00840e115003114030034540c0800a4600c2c00000c01c80b0515281c031506500c404203081c1044401d20048a00ea80da02050050040c9643e071800d0078400d05000300034000380140d001d000c07280c0d110014a4170b0004201c44911190143c401e4406100700c1c142c0104503e010307141a104038501c641e01c1c2941045e090080d840203168010382c2c0ba420341000d62028461a4418403e070061011802d10351070a1155401900c0024010b06018106103e80c111312600c000f900135034503407900c07500c54103080005596803040c03e06034410000320319110705160b00103402641c803500d105c2d02c0b20840a2640d281903034449180802020020312924090100311038848095500b005009100099031010b0a0310b280b0b4040881c0607101c074140c030204040340b901d112801048003082c032940141c606011240c3d1655244201c150740100300b2038698000050400c080d5108500800004050b080300c4801c170070b0082c1040710075000b580e001800900b47c103895854140180421103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 788039640 1250 788038390 788038393
    0x30c0605191802012a061a18010f06051606050703020f0403060905070f06120f060819060f060815040f02090c0a0215150402070206040f03031e1b06020306041d01090309080f 76
    0x41c0250340c0e80740002d00000c0e074613880b20100c012107c240350f02c03590a407415043c0800445007055041010349140c00040d46d101c030080100800555084000303440320044825032224002c00c8549801c08140c3c0139001d4104c070040003030b0000c600001406920303080700d0071482c02403007541c0002c0c3c1c486080c400c4003030050240302c0110b00110b00381100c1c141c01c3e038051040e14000e10f2000540035118152581049050000080754540401c0080d052140c1031056104144c501d1104100c160301c2d1020b4140c5400041145040601720314000030244075180c214060441c0c1c1c0141820000e06c0d0a000c411441d40001c030104c1c0042c460780703a040301808040110180120100d689230243c2da100c4104001c081e40c05580200d0b00040d0512001644d0703500e80d104200a18481e444801c240d444c0724224085840040e448074040108030b10b13010306880120000111202e82004002d6aa641d60001240c06000d01442104040b5080e0702d9a1407151010340c0000c5100b8840c0e540c4000d032642d20010b5603a2810303544481040c1c1e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 788040890 1250 788039640 788039717
    0x130602030f07021e030609011d0f0616031e05070f0e0f121509061e040b0613020705070311010e010806091611030a030c030b030a030c060519180201 65
    0x36141144c10110320880703e00603449440980c4001c2070405400362090001a034590048682d2501d090161400b0300341c104004004030b405119829560740b00c054820b11103681040307100c0d07409070b209400c5400f24503207504602c1e080040805141004040860303640c80000c0c480c0742d08041e00c1d48280c604044480b0010049034820702a00c0410111100d42d6044400314807901c4c0c400c102d0920061041c6104002a6024000a1500d1b6511100c40c001403c1d2a50b0242a044100800540710a0f20540c01840586811000c61359030741144000b8454660090468030869000008110060503851000c007801e0340d65401100c00480150340000058a5035640607644a0020710a07814005e00441e5250303a5240c015004a681c2d00343e1411030b03100182d40800a520384d20000d2001c4c1c0c040c066142048800d03001022100303c50b1b00e00902003148003030300908003500c68000c030b2440b4004940600c20f41920034010001c040c40302000d894104c2d54244203e01040d90f000c0040c817152144a14410104640c0e94610034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 788042140 1250 788040890 788040893
    0x1060f0c020f011101140a0608061308120402010c02120106210203060406050720030903070f080a110f042c12070b07031d1011040518040611030903130602030f07 71
    0xd082070032201d110204d41d0381c1c2c0c1b4580d00640c40441481e0040c221003070006032150400305218280f500080405480c50600c41c3c0450002d03000c074049a1b84083c1d0300e080f90301c007a01c0300c0c80100c0c0c2d01d00c10b194001c0e5210580c420514216001984110b04654030030901c0105001a44085c40c51500f641002a6148c1c12000000340840c3c299040950700504174601a0300d2440380c00c01c1d0910440340402d42c3e10147d400030074140f0b40d0342010011031015002c0c0c108041038040c0b03851402a62194442c8008000045450343c0d41d64644a0030003841300e084008005024140c90780c821400b0783c80020984508028800310282442100031a0008034140b91035900e528000c10f94680c0c80d648003018200000b0156150194407807445e0306440360001103045000740401c580c9298001c000c0d1814a03940c1802103000b04420803081d50340c0785106d1a00d01c01840380c091545e40301c0c14400020200a800050101c000100b003142c21349002c0014103071002d141c003420015944544040341d580c000c040c80900e006104101c03180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 788043390 1250 788042140 788042147
    0x11d010c0e1302040e10080f0a0f0f1703010902130f0501230904051302120d080a0f02040f03060b030d030501120b091c02012918131a01060f0c020f01 66
    0x10154031070802604d0301355a84a90000303541d04807660806196441d00c04d0000300c1c03090000701c43d50401c8000601401d003a0341c94005400d260714000030040411b0f810244100f0410150407a048254428030b1a04e070342e075440030000658091120808103840c554800702d43d0803100040c08058500694a04102d400000c0c2ca00d5080ca44c0d0820f52480d0340c40510601e80c090382c881c05028412800d034222640304034842d20612000c0503c2e50325800f0581c2180c2005040194844e80003a403008901c00085003001c014074240d0024840c503080010110b400080100601c071298020b0b00c7d00280c282d04446e60180c2c8000d0480c11614203000d0032007520800004880450b201240300c0341c0000100d426100034140300714480000c1a5602e0803400076075125030000c0e4403030410000350b018044c00000d0300050401a000001c9003030000140e80c0ca5206481c1000c81c1500f104111480350143c0d0020310701c96130a150300340903508988248900c1002070300b402c81c482c1c180c0307102d140442245603004c0e010040040c2490010b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 788044640 1250 788043390 788043409
    0x1206010603090510051906050d03080c130306050103050a12140306150c15190b03060406090303140c070c050a0503031803101d01050603030c030301031709060705011d010c0e 76
    0x2c0c0c4043c1309088481c0c201c59030601c101c81c003841e100ca102c911581c43c501e001c002516900c0c0d104c0d0b440b514410805c480403e40101610798042498043d0a41d505000e2a41103800360041d04084c09161805002104000c000118911040e015010103101103458000869100582c00c80c030502e83c040500c00300710350341814000031032180c007003088450504003080c0c9002d141007811550045143d90383c10911820810340b0b040140c0c0098600e0003404007a0800380801d03560140540f0084c0301750341e140c040d00241442641300b10320103c04040d016420b802d0606141419030481030b800d032400041c02c60002818a0032840d880c0c1129806409903091020040c1d0001c0d90f8290b804d907807500750184003241e0748141d44d40c0c0f181001c000035400d010082d460081c0d0400c0e0841d48010704041c044d6004002503100800f00000703480c11a0f80c80034810048885109401000303001d88840c0725041034020408200700001900305003402070300c8074014848142c0802c400c0b401c0e1703040da8980c0d001041000d910009607003080f4055 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 788045890 1250 788044640 788044643
    0x90606070f031206031e02041b1d03071d070206101a130803030901060e010e0c1218010f141506270a060c03080f0c030c0a0c02030f061005120601060309 67
    0x110136a80744c540403000100004034440e8003065100c8401140b0302481018820880c20004100d15005101c020742180034900410819250700741d4007003201d030780410401000d0003401c148426090140528030000010a5030f070b01015020703000c0009e501d070015604800c100c83d070000821290300310714078452019502900305052400c000304404500c01c2e000b0401180184540000012050324103c007102c00c10b0410707081018540d10410907c10b405802c40140e808000380907400c101d49032207410000652141c03000182c0015402d00d000e1035000500b5501c0122840c00f0ba114090303023595522107000a10f42e4080710b440d840102403044002441240b40d11b8002040742807181c00b00c1d5aa900002803d080c4c059014000103482010020101544985515001008000c0c3da40540c1410001d80b9030f1401300410b040500c031004942c100205104690146c02e058001e8140c40c3c80c6528048c8950300d503170f000c651003a01d2203001d50002400703041a1070340b903842080110242826900702a0124040e0050010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 788047140 1250 788045890 788045927
    0xa1d030d090f0819060902120a0b180309090c09130f051b091828050915040302071a07020402070c060201060b0702090406091b1d01151205071b11090606070f03 70
    0x120300707502d0041002900300351800ad00d40710042c0d1420401031403401a15080015007034006012035a19070b1940601c0b26000b03841040540d8076800d95402040420741c03840043d0a20a0410b246c45011505c142d00c014040c0901e20385000a024052a42801601c517801415810052800303801140c030098840c0a83c00c58658004114503141c2d054a2500702030405a07201c04c5150740700b051040c1004d04201038100d003010141810018580394074082c0d1502e106100e0030b01420010009074040c5106013080f40d000b036500400440d102d4406043c004900811409100055031900601080b650520f80a450000f6402000381185079a182d45540c00340c420104104c03000f001c0e01c82052400f02102c55020b000d0041450246008942d82401000041c0180c0c041100400703003020700c00c2c1c2036030301402c4821050700c030110104060702c84080c100c0b07100840e4000c841160103103190003810446224100391070b0402c220358400b500d4803030a0400525224860b00106000c004440f8400020300800c000468024180d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 788048390 1250 788047140 788047159
    0x1b0a0c020a06030c1d040609020703080610020d080c03101229130204020906070501110706050609010f090b0f04110c06060906102d0c0312110a1d030d090f0819060902 73
    0x41034805980001c0b000f10081010041000a1703420443b184100f602c000740b00404003100d0002015082c841c000d170426078503540010000340803d0040d03250f0b50040044a440d28202540341c1410703c00e48400921a119100c00000c80201c000590200c440c0a0310021003181c0d1404a16801c01c070081d8000c2c0030058110710b0601c0800c2c045a420302c610040380907403201d12941d03580c0900c0c00c10116240145580d12910f21035005200c00c0340c1c95122a411b45200000005041c40004005030841000070039103a400360802c0e480e441800f00c4c05000e40f10004543c3c0c00c0306d8080c0c54030b00c10019035a00c22108642c00402074440e03c45d002e4800c0c038802c10011540e00e03051034a603403202c21a23032858104094007408036080300110410984d00403c100d101c007602c04401c00035002000d03443c04c141c0c8506121032080104200315100d421961802e07403000c03c00020112400c180c2c5125014100c060603116441008400420010f445000402c1c155a903420040c01d132101e866840d0745250082403000c00036a00080d00301c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 788049640 1250 788048390 788048399
    0x50c210415031b1b0204090f021002030304050a0201050c0109021002010e190f02100909020c0a110405070f1107050402040f24080403081801050a050613060812031b0a0c020a06030c1d0406 82
    0x1f07200b554403440c001d100b10a180c4005006002c039403c41c4111103803c540c401c00c100008910301041950b03100d542441c2141ea01c48030181d8003409070012090103540075513070442003043c1d2501544811076580b603d20a0b02c29a001545024031078052020b0003401c951180c4e1051001444e1103041000c060040b814481401d9845100791001c0707801151244c3c0c41c550241c805903041c040b00d04519640003004036818046454204002080744034240452014040200741a0142c050140510303006450007420454640c1d5503004d40e0511072106100b952030b00904070b210b500110b0680d0120b601d61751000e4458403500d40342c40c0d4044030107e900070070101c880d440c403c504c90580d020a00480c1c0c0541500d041c0801c0e68242142008101c101c111640112107192000c2000400d2001c06c0b040410b15411a44548079590286090b92104004070845821b540005030f01c80980d41002c03205045030b000392038020101da02c5da20290b04444a8a40b08030205216007082001d0001d803100204221001031700c04900a50348 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 788050890 1250 788049640 788049649
    0x806010603090308061c0b1b0d0b0a051005030c0d090804170706050910031109060c061006080f060d03020f06150405060607080406050c210415031b1b02 67
    0xe80003800000d0710307000390320141603100814941040044a40038403010f25600518403211904030024000f01c0c130031000848510140c4183d014040c2c40c0200d0310343d9914540320300e03001030440142d0144180100907002c1201d0901012095030344100392038040c510344401b404d4186139002001045502034844005000040320302340035000071711192040080040700d5960a9040103400d403c03441c10407006002040d0a13503119000d94240018a0400049040801c1c0b42551180b091410f1a5040310000840d4a412240012a140700e004a00d1055010340d40703d04003110440001d82d1280502e404200102e401881d040d4102000c440c82070048881d50850300304581c1c01c00c90100c171248815050b9000d08c01050a290140c198008400c40e4a5440e2090701d56841c6000d02460240508109010032035607160101000701200e0990203a0700c103403411620142482d1a94001c1c02444a0300010a400768041d900a000d6070400800703255125901420510003110b005814130720f08191083c0080a00015894 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 788052140 1250 788050890 788050903
    0x80307060f0b0d110d020105070611071e0203030307031116080306011d0d0f020604081618050f011518090504060e0604030210050c0c0105190c0e03120a02010608 71
    0x10549001c10200380703855400089034a0606002e02030b4010789200e00005000c035010344800321044a94101055103400102c03040d01072604000c100300d1500305003120403200f01010b4800c45101d20038021407101d00086442500c0050000290150301c10700202c0c4c8428025001003101c0c00d12000c840741000708140580405401001302551420300000920050756808118a0307114420402d00802500d0b844001c10482040c00d00098420351406000c00c1c01c41d0745540031030b0300904405048802202c9002c64112031102d003885903400d0701e070350000d00c00307120006401050b11070400044140c032141e103030034440b100140c0484213600c05c000440075585024030440302d010740a000440c0c00003500303140ca403500070300f00c400c80401c0b0003465008200f00300000740e0000c3c480304650b4034800702140c207880c2c180c0071000034064504c0004c0c15509010811042d400041c05500107032008660502071503400c038006450071012981c02d9600b41d000f40d100c00310840c0d504402014810603d10001840d00d0741c1e00155414660f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 788053390 1250 788052140 788052143
    0x90a1e0501030b0610090306020307020c030d0e010201050f0105100309020f04020703031b17011a040f120309051203040501050738010b03010510110a0506101a040b031807080307 78
    0x95803400144240200440b41991215003550280300c00c03c03140c20068120302d413611000300155000800a05094802c0c011344010690140c1100e0080c13000b41d03c0a42114881c0140500543c80c200001342200d8801400030704807000a00081d41140c1415411000342072209026a00000e0300c24108000303071564401403101c01e000b507070002401c000a01d0600300c1520036095501c204035001940542848004105a04480d00200c454044070070b10000d80a43d80a140d200c0c2414150384100054140c040300914140349210f0b90b10506002c0e2103004101c3d181c05156054505544140410700003540194001c0141c01d0003400b0255404240244900402110020340000c040800003075125940e5091107081c0076051040440e0f08540c140b8000c510300c0308009451904215407802041b200720000d201c01c030b80c20b98010007500e940f40313401d4002e80d200b2001c074403501485862a603400c440040c00381058a0503200016a8149540c40c0c03030200000301e40011030481d045020301c6100103100e4200308000c20086 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 788054640 1250 788053390 788053451
    0x21603060b0301060b0c0115090203100e04261b0d08152803150219050a1806081905100b030612030301090b181306050702030d0e0a260405090a 63
    0x8c03020360036040c5200300e89038400c0d0310940c0148103009202a4242d46d000645e100383d00c20003207a44d0f03141040e103141924004a900508608540a17400c035440c10300a10031800003441900481d688403140e15640d0f079090820100180c031007008118131100c0d50011001e503140080c20050004002c960b0070310503001c10495020b0140200c9402c00070000711520201411560030403c6040a000d21301e14102168000507200400c41e000403403180150040004641c0740c40c0640002c010030f5121580a40745a01c1541d2b85030702406914581c072510400c0c2e000c0c40d8811880410355100d450700d0700b46540384a40014000076806400003400caa01210104081d50007800d49442c0415145090740038817000c4c48a0218442d50010000b080051103800340c1c078200070305980f2120024840d514240100d00314085c10745444051818031551002c3d0201c00501d0410f080d0180712201429032241d2101c5d82980c102c4110b8114400b02480300700801c0c6845201c25603c150480c102103001081c40c4040d082e55808501d50f40c50380c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 788055890 1250 788054640 788054651
    0x170c0a06111201061103032a180108091b131b0207030201170603150c0408010c11151303111204030f0b150102100e0c120a03020607021603060b0301060b0c01 69
    0x4502c10001554010042d07402d0010103002602245501e0380300042500201e440c00c2601407140e000840209031951000041c040d40358810852043c07103550071034050318005401e00700031507400640407910307950100503100c40e4040c510400040c4455076011024200045030348113041118070007254081540d0f02c5181e8090201141184005021200e01c01d803a40074658800082080b20b032000079030a9003460f0003600c000301a9940001418280c410f6030480300495090144854440d074205440c0040780b0840c40070b4030784110b040c802c4d44000c11800c440b1f15044240001541340400d02503000c00010030b00c01c0041d01c44c6004800f0800d0070301da01031347c0104d03211200c030140d0a082c03041c003840075a0424245007049000e07c40700c000003962400650500d1198a50342c06401440001c01c00c100005031202501200113080442401078451024140a070050701407180000e071100d00c0440c10307514800014080140c043d08584442d001807052000302038041d9644c1c0c20106140d0350b1203006e03050581d804000403e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 788057140 1250 788055890 788055907
    0xa050715180b071b18060914070206271902011d03060703020d0b0d030203120a0b030a031116030821040b0606090102120a0503010f12170c0a0611 64
    0x410101e6119410030209840c42404045610401c4520554100b03000715104c00000860000034889940401184840c00c3d20829005940341c0100b0101c07a6064004c010030700350f803000c180c03141500720782040050b00500b0020700c000315169412055903240981081c50409014940da10303044140c00c42051524608194104540c0e201511031680d910190301c14401030b8098002c01d46d100d40207004e100902d072f00402d07003030108011035000344080a0010851446485d050502a44036800500d1518920a24500042c44044070b40135070424008042c0040180c0302d03564408030b5030300c0d80760409071845001d60140d400b41003c5181800024500035807045548000c6070480001d0102c80c5003e000c0b50400c0c40e81048003054000c00e4180c0d01c004143c03000d036030f1441c0303202c0101d0a04812614400c046403010400103440d55100e0051810303a20811400040310352202030860700c000e100c0e0b80c000c100c50007900000c144035071a44050168003124804641002c8000d40c0c81d40155240040040210314010410b0756 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 788058390 1250 788057140 788057147
    0x71e0b01170c040e0109081206120319050304080403020d03020c040507090b0301030f02180a1e1e090201021f020c070512030708070302030909010305010212090c1806030a050715 78
    0x28014401c004421111401801c0c1c0c064407000d054908030710440c2c0d10541c03541c002d0820342150080613030140e211340d9a842a01d1001c0001340c0103440d01402034111030b1014201400010484201e4030703441c00440e0940c010038004444981c4010011501c40d0014403002005071a0b08030f021880a1007500981560b805050920003102c074020709010401c46101d008102c00303299281100d0540e07030085803a8101e0040760004c20b111198032a480c10f6280115000c10408035107551004803904075840050444070789070310003c020745030140d242c0305880d036641031850550f03e520340c00200751500c1070040d55036501c00070a10708100c02d9118610b40020350001442401103505101c03d1014090032146264030042c0502010340d00d01030018001c25940c2e0008509007418001c006132020040024020310301903840b8641103000c5d410503140f5013844014100416802c030004900d1407045880a040258040d010040c41da01804014001c04c0e0580600700c061008502c050206a003e0054030700b1062401c0b0344480002c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 788059640 1250 788058390 788058413
    0xc082e080a05010f0605010e0d06020408031902100212010608130b09160812040e0a0e061302010e0406181104090e0606120304060c030e010203090a0e070e01050702060409090503071e 80
    0xa81c10039217066000d1100b82c0e00038481d500544010b4840c4450580503280c028000e1242e1b410200003488041a20500c00100c40b000703029443d001d9003a00c009070390b6820300c0d105034014000b000c85041c000c00010f00449104a045941c000c003003c030280301040745616044486201a100c03858139400481e0321001d43c0030380d4026280104180300c0280210201602082424003542c01506020000b440100307038a0300c0a034101c8c072134140d80d800035145281001285200e0181d14654120302052604121105614281c444c0800322076020024004095034200180010224040c420390600018000490744c00c0661054260701647c000c0148240d040100402c85807502801c4054220350040105200283c2c4c008080c43e0102d44c1410880718081c030700d000503030542c0140c20300300c0e400000c054000101800707401003690280081e600c6150304c000340ea200456040c4101203029400c410208001c00102c002a80f224168078011800e80741081102da55410a060b54800f1183d425000c0c1c90100e01408400d0015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 788060890 1250 788059640 788059661
    0x100503030c07060f020a05010606080106300f0e01090f020306240f0d050604051e012306041d060f062e180f0e0108010c082e080a0501 59
    0x840c104400d0110a9985180341c3c09030008000c07a40100300c003654020054002d1b0154080002d100c02078807a103000740391090034443e080008006030410f444425141d0703403544550720030409892030589540d03c00f0014116041c03400b030f001c50b40d960f40c00851a5080c814580706900c25404240303a0022030040528100000c0c042d4904c018140315000380d03070344060b03207a114110019a41814002001400280301620303490000c3c1c01b50044404100421102103000c0034024100d0403c0000c902003650030320b080b903400411007800c4443c210460b0040301106190f0355400030f0003d01c007180084400181003101c20b42800543c0b0994002c01c24401c0e607180000942d580158107a41c6007043c41c15a050000ca91a0a81000781c2000070100c1040c0003103101b01c9118010480507201d08620315981e440078200261a4410040c01c07144040022490401c103004d0401400b203c2e6840110070740703c5151400310343c10505941c55100d01041003042100156410740b90041064001500c000c00880c148203003074800343d010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 788062140 1250 788060890 788060893
    0x201260118022506020f0a08040309060806063c180904020f04020901090512070305060115050a110307050d0e0907210209012606031002041a030a140f100503 69
    0x2c0010141080300d840c40300c01900009012072200031304100000b807183c1d898140b089100014541c21240d002000349003d03902c01c0d9078455500359034a10803120144151040c80c0d01000800040000c04100c031503c03036100c1001041c00c4a1f0080d402d4086074040041100240210ac1c081030300d011140002901031102e91043e18144210b20780b81c1c0c00510b8114801c42c81030b11469012070000c03816486000b403034003d403c0c00f40c44440312305280e5101c903595000921080350548960000401c00a014900c01c0d6001c241c3ca480c1c035400c1a013130690549103402c1c070221014651000340b02c05400300703000704440a03040c0ca064880340001c41c041e000303008101000411450a00910200c0d0a80b003410b00d4607148140e103001c42c0010303140c21003400101c6e0741c5051200301078603404000b15240b09200c2c02c983e400e402508200e00300c40146c2c0401a903041a0300861145a000b480f840b01c1e41c80540154a0040d40e0021044000164928170311814212821040e02c602d0640000c5408012289011030a800e0282c18200d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 788063390 1250 788062140 788062147
    0x608011d0603030702010f0512040602040801060f120209040302120706020a1103072f09010320151210080102120601021e060a0f09050307080a02010f140f04020126011802 75
    0x41c0802c0d5280310700503009040128520002504512074000e8424680c0e03a0000f44480341402c0c05c0032006034100b4020b44200b03501c1c09000156030010f0350207440440d04025051040451350b40c0802c80214001001601076000d0070111011030310071040140b5100c0d108071030050301c900586100400451180c2140070541d03004014841c04100486030b584410944480042d0b58904100120408140406a20317070300300003114000300c02c002a501c0c280180809183c0e0b09440ca40680040281901c05074440c800c402c01d04110740038116694054075540410503101005642c0da1303403929a822a8170180c241c1c18049601c0c82440803e607418032142c49140140d0041d2290130780344500702a11104090304890b2420382d507400c610740c49030298206110913900201136a403162040d0070506069400407100400552a001415203c06120310a603426800c0b10500c14a02c0e0742c0d056114900e0001c041e00c2a410710071521160105c0c01141d0a10300490100710f044a0b40c1c55150200701c44407903400b11181d014890061 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 788064640 1250 788063390 788063401
    0x70b030115022119030b1c0b060108071706010309140a0c05240d0905120409050109020304170304050f070f080f030304030522030b070804210f0509190608011d 70
    0xa05444d024050f01040c100c1e0002d00c0a01a40140807110081d90003162000304046034529400504103410300400d5007a15a0f6500f400465030230704221000070118074800d1b0030600c120b0306c5d4500603034802010304000036002e020b03803039000d0040740c807241c02002da5003c45a37420400150103032443c000e10b02030f40e1003e0b481030380400402805000300300f2103100c1031021032506650200c0c4d40110502980107000d80700600d04403144003010390300c01d004241c6035a041800004000c1c2c007a02c202e81c802ca0700880b8101c120640b4101d40c1007107500150060b03030584901d94464031580414400e0200a0513411142c0005030301d021451410901e400740a0001c50f0024000c010200e03070010300f00c4100c0011024145d0680d08070310400203521245400141224211008202005070007180c0140242e0160254000f02e80980e00c4045201c0d60f00c0d900007000442c2c202020f14042e00440140001c90f40050a00d6442d401803030f0030f000074488550040c400205403600400581e20095612120034040e241802070b45d1800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 788065890 1250 788064640 788064703
    0xc0a03021c03030915021209061b0a030b0a080304080c092a1c0213140a090b0d06180210020616081017011505030c0918070b03011502 59
    0x10312907801089440d20000e80d0406119a01140c88580d11400c810403c00c2d498040c0d20007500080c110008030140b00000c500105000602d07548141c800c40d0080951004402d0780880c2c541201d21040145904c0381c107206140e50316511110b024021301001103484501c1c05488620381140046a01e005c0c0c81d0050511464070500600c268081c2030f0800d5402e013080099003081c40c03601c100001d80968044200d5540034005940e00200078603103440f03a00241c084e8442c13800901050b0541c0300140c0c081440c100400c03c690017500080c0c0400001004d0000062403602c030710094079082041120514901c0d5110307011450449611407195220b440242581d1901100c1c00e0b003200081203540003402127850005520043c2d5241c400d000d4004003038840c01030503104c0c10b082d01030000710290000b000002c00c00032500e42400200880d111400514000d1191511607074074040380c003c0e210810035401011000b0035a129900000d600800c808000032240300b110b940001e0802000f00361410014401e50031789a4403104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 788067140 1250 788065890 788065909
    0x5130501150521030f03090606032e0e160602100c030203040b0a0b15040e0f0f0c04060507020415030f110301050106080610121503020111010e120d090b04080405030c0a0302 76
    0x1005900c000c804051003e40324614001c2c04422205c180d00041082520480803440c18011002507088900a40004030003000d0046802401d01c100c0400b003035642114182034108560604100c0b00381c5103d000c0351186001e86e40041c2e00303c0c2c00564014070600c0c84000c850f00c1100712804191a0850450419945407240d50202400c110402521840308204e5961030a01e60703074032005541c96150340c2d030f507a910000354071110482c2e500c01210100030000c0d00c50050341006a06c11120300c2d520b1407406040402c2070315aa084500c1c02c1e030300150f0b200b003105030311481d0707400a402550140e90450b01e042d00c0d80c644011141d000c2103410b03010307905100c010003106821031039668000f00c0854030a240304490741c1c1c04a40312410700a007070305001d040001c0c410705044801521760030b0701c1c001c3c2e90300407403400c0b0f2808590a8502c00c0a9848155024401d00c00e43c151029018002c19460400c000c81e00b00c042c1c0d12610480d0078103031015100c00800041c10041072400304031107441d02c00255400d40da15451a00028071246 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 788068390 1250 788067140 788067169
    0x40207030c0206031b031303080f060a120c080304030812161706190603020a02010f090b070f0c151d010c020a020f060d050420191215051305011505 65
    0x1400400441e05800800070700c284007880c5c3e08401a1640780a0315080c030103200c003d8040e0081054107010a030104900f40d1030303520621028100f0402c0302c2c9841440c2002c0394070104280c50308121440e0200320f001d03090005000950162040300e48034000e00003040c2c05404003801400c0000414008034000a4124100c1c2544c00c4480d91076450350303600c08001c90b41c44003200d94480010032020308003080325909071740504158102c5500070400c106141d00f039002241c00225014000401650000b940e60384a5451010a00d0541c035140b1a6800183d0b15428658181454000001d4440719164900d5222901020840a0b120000d00c0103600007000a03440c2d02940c807004e40621458803e120890316100122006940c860b10200035a141070f003080804a07030200c40701031071248115106101490480701076181d1500100b010002c45250a00ba87c0e54402d1004040303444070700102c101e942c2c9200e00c1c803c01d486111382807254080e0960b41e10b00315003180c00052522b00c000780060400d0003c2c2d150f4112400114 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 788069640 1250 788068390 788068399
    0x30a0b0306013006090f1b0305030f07050a020a0e010302090f280608030d09060b0405070504180b0405090d0201050718090b04020f031009062120060a0914040207030c02 74
    0x200ca41000c0c0c0400040c3c001c3c001c1c2010f4100341c02c500400c110016041c410f28019038003948a240ea00020107540300c0103107c040d00030b910a00107007001c40118001080201c4c4030f40211500c80c03031242d010480c0d904481d0300c908040c0441000400070350a0810030903a0000c02c3c803160404034602240b0602c034071001a41c00414410b5440e540220411003a4000c0001c0c20491045a0712900f41141c200d01800102204031240f42c00e000f02e00180d410580102d42c0a03000c29190942018204050f000c5c055008a50884c10b060311808962025143e40c0704941c002c0030000007070f0034030003241e110103401c1d601d0262200c41080403400f40300074981459338010098550184002c5104101c070760024010b80a48a041e03040d00d9000420f2081d10892000803600300c40740c0c5c140a0050030b5030343c002502981400a8554540306450005078001a04c2450b42c00c23003011542810758010700d41501007019900181c00c21408580d9401081c00b003580040034101c0056002c85055150641c0340e40d008001c1c240c0d042009004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 788070890 1250 788069640 788069699
    0xd0f05030114030705040e0d03060f0f05011b08030709061e0f050f13080c0319030c0b09031201090c121107020d2409120206060906061b0111030a0b030601 68
    0x441d5010b119131001020000c00c2404140c1c4001c000c0b070348410890610401003490000e0018801c418040707054102e48610303c018003420308d0b241c015140f0600400340f800c02000594640b40005844c60050b50250380255030356a801801c00c10003811000001041c0c5c65020500a0310308041c80c2c1c00040d240c1c9072881840c0158444400700003801d198000d80034481d00c00381800c0c2010407600e000040d034034000b920880890f0b0751040682504000302402400180003c2c84001564001c2900103102d035804c40c07c00c0c000c03079103040c9800c184660300c240c003a0000456a40c0300c0d443c01c585103a21000740390f01000003603403c01c800c800e0f0790f504110b14800c0c11002402a19102c0b581d0040c02038440d000c8507540034246c0341c27440c0d078840707081102c0c020184041c0417a0140320385041a13550620009040b88034050252401107661210f4040000755006a00915141c90007600952000c10f020b01680101d038403806100c0381c803424010260303020b0b0b0315070030710a90007903004000403c5950000010080d0700d81d8801c0351205d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 788072140 1250 788070890 788070929
    0x80109050906180c033a12050403050c0604150f02210c0405031b030111030f24030a03030e010515060d09020d02060a0c0302161404050613050f090d0f050301 69
    0x8001c003003000640d141c007407181b5580001d039010304841e00174982414249510808940016013204418130303002d000411070740046031402190fa20040e04540642440750900b5004030f0a149002d03021102222580c0038420035040030070550003900d000d82d56011056007041c0b441448211702030703074038032032900d40c11015404188902c0040701200c0107084040c00b039a42c07a2409140c01e030880300794941340e14020340c80c2200081c64a1100030540c0e00840c04d102451020f41c507042c0a03410705000701c04001070800007044505016030750030170000e144075119071000320b85065a88411400c60b1801020b070244415000909849540da250031190401c0da90320f8001800308690000c241d610001c858002c3d0442d0340015280c2c00c0b1504000500c0f26144030307508507230381d00d001c2c0543e80410800500c13804410144801c43c1d45c14038a002e8010561110b13018041108640500c1f41e40c078140d4009989218010b080c00741800071100003030114a21740c0405081a00c40300d070001c00010218841441010285100c0451082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 788073390 1250 788072140 788072143
    0xc07051021060905091c0c0c15030e0615010e0f010503040206180a120b090a030905060c0c0303040f1e180902040b03010e01020d06061106270f0c0108010905090618 72
    0x8050030a010041206103045d289295030750701c090008a001480300b003813814050384200401c000060303004e0307050707240035160005100710b582502c4102001d050300c1d00010800001c04002c614070581c1c2c15601180c807200303500009041300c3c2403912858010f10440c0c030b6054590342c201c000c4941090f41540d1075503850f03a5000c0c10108440b01e80d890260300c0200d00f00e0025640d0710070302003c9400c034020240d20031a0340382d1010850340c82c4003480d401008214601005c0180e072030100003070452800141c05445c4241c04a200203811988190014103041500c0d034000e000300d124040d050341291150b20030f0701103803600b41a00721815000400740c0040141d00c900c244000c54807240c0000d080120007030003d01c02c0742010000a4041d4001810f0031204070302c1c001700003070458407039201c0c1c800110040c03002e00b92684503003104400c41c0c801805203035001c0d6a4000c42c15040402003084400502c00603010301848902c0100041016106034009070740e80c1d0802c000d00c00c0105000ca900c0b074014201c014000c1c4040304500406 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 788074640 1250 788073390 788073401
    0x10b122a0d0b07020307030e0409031202030903040905040c09110406051903110a210b0609060a0e09091006050411180112020d0212070c0305161a09030c07051021 71
    0x1c090842c0c00090000b01c0340c002000d41078080c46502d907500118003a0301400100ea645d0200600020f1541d07010b542081403e40c0219040301011095916280c0c69001e814142da00907203007111040340b850001c005194951281c1e80903490903501252030103123080c000a1031402010000c0c1c00800241300050280f5000f50700c008ac0d04441020460346460300e01070b0191500701030301088102c002e14446c0d150300380f0b006841030301943c0000030841340c2040c4447c1d05009140e00b2210111051014002d018512942c600d980907129501000080248070301291008013a100320f580094069410100090704058580d001e55801c038400c3c208011403e81003400403507003010080c00601e0f1310b81c40001d6524501c202d94005081c1c144c02d0500c40605e40d210904100d41c0d0a0a40e60090700198042c4a0160351410a0354001400d43c05091420545210310040c07020110081e80c042e0200e0f88002140c138068402444104d005081c2291004400368061002401c4011100c03142d645200070324006050b66989903008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 788075890 1250 788074640 788074643
    0x5040203151905070302270a0611070509011211030a1211010f0213030302010b031204051003060b03070323090d030f0e071205071e12050a14010b122a0d 67
    0x1803000781030880300500207621407c0b8058509840380302180d1480c1c1a0200041381200290852143d10300d41401100c0031603c05501551500400740002651f070303130305c01000c1d011340510080c04071025082d2910491020a91a100340a03401c02c0700c842c800301d941101544480707461420004d081c140403000d07480c0103007100002180030520100da00c556040c0301f00c00c220103403840f80d0020003c08400c81d08060307548103030511001c0c1000e0104000d02045c2072403034804169140318200812081c2c0c58000c0000c0d560001c6441d0000030340d407824100c5002ca007200383c68031001d885030864082e5003402c1d0000ba8071040348469100c14980c45403a0340100d01c03043e51020308408504800c0c7c030b991741d49582c010302212081c40e01c00e81c0c7d941701d2940085503030f01041c0406005402c0300c4080d20701107494445803582c01000b45105444900401c4c8062000c0340003201d291040741d58403400000c450728120100540550311803041c03542d551100d14203130842d29041400c92800c1403541aa040300c290000000350b41c104601c0300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 788077140 1250 788075890 788075941
    0x12010504050a030806032a180f0c0f04120b0412230a0e0a0e0108010e06091902130e10180809040e0708120c0606061804050402010e0d150e010504020315 67
    0x303000705182c810031f915a00741101107411040e03001180c09450680c41c0c0981e030a80941d039040e0042804400c03450010302d560060222070b00e05160b0f071170103940410b150444042d291448500100020014802144000d211a07402c09120402190805200100f2985a8000c10100001d41665a039000ea09096200400201000c1d0a9a224818401c1034042881441e400790309241c2d9258600f4000306e002481800000010201d031103180205001030b0f4540c0100740d80102d540d1140300320301c648074011603003d4004080100380d60044031000c0c60840703c0814807840c0200303c00c800d0b00005840c1d1411590f000c98215800314403040c00100e814100100b9034032060302840303181440305082070100c0c081c0c03180040c0c81055401c0b0796034903810711465100d100020035104808005000079468554000c5822a006252001050440002003002c800c2481001c1d6445118000c4c8a00c100d141405800c6040c46008000d018038100317540429600d28404d80a290000002d4000410f92001e081c680407011b586140f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 788078390 1250 788077140 788077183
    0x402130c0309060e0703120f050d09061a03071802310905100b070b131713050d050a03050d0b0907110d0c030f0509010504050d06020912010504050a03080603 69
    0x28805001002d0b41c10003210164141950030441c80c03c081820401c603500700841445c43c10701d00c0b40444074603a2049400b41409001d20040f80410b03c41e00c10320b26014801c010021341e0a03489801d4081000320b440b0000d202c3d51284c00203020002480598200c1c9203600034000d6142d2402c080010202c0007451a600808108103448121003401800e03204c08940314a24100095101e41e8035074810102180280720348d1000c100898400550083c54181c0c0c01003402a0403012a042c0c0e5403841d611890306044130140840200d4400101603044a007440208030071076910302c6600e803980d90940c544406500c05421301c2404288401e4044481d005800754003002098000b0914080c4409001e00450344000c00300341c80345003c10300001e4003801e840d0341c0360354250300d40301504041c5680c101c6196010440b040e04014041c4400960b9499100901c3c0c2a240b180101580796003074042882084241c081041c100c0d42e04003418040440d0000c0360310030409405107803c1d6041d94aa4021900e85a180c205100072407030381c00b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 788079640 1250 788078390 788078411
    0x5160302070911130905040215180d1209090213120c17070e07080402030c0909030702030312090105093c06040b06010f0203040509181c031e0204140405040213 70
    0x1c500401d04504c003901c0140c81980c45140740c004032401100d0083d0082198080d00c84150301c04009450300e01c03004051980c80b0358914010455500c2815400c0394042644a00c0d02e9500da000b40380c04020740f040c0300381141481143c40c615845101d241c4079180102d144014088144043e40740b124000d4240b6081e00c40c440a08009070968030360307080c40780240205a107004100618402d2000600803500113004040d00c008200c100b0008890141510506110401001c3d0040e24140040d110404c02c051101413249000d401103400e4400081c0f201007a40c010321480300b0300d030301050740c41d568681c0004a141445042c040390001821102a07280c012032003890b042204007c500041144259000c2c4d95084002d2540030041e030b500e000310300580c1c0e4000e50312000181c20250411081c40811040402c448001c04251243c0449600380142c24000a171241000381c5507000d54040002c140c3c01d0554110300c0c00d490b0845201604046a031650300c180c3d00c84001c01d0070341d610a030805160118604040001c0c240d078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 788080890 1250 788079640 788079671
    0x20609060c070b030c120f0c192003030a0c08090604110a09021605010b06090f010c150212010812040b091002010f1b0806030c011e03091a010303020f0d051603020709 73
    0x4414404214812240051101c034185e181140c000d140190b02c00342400300040c000071207000074a15210030000562b00c0c01c1060448440100461355047e00075581c0c1c1c1c02c01a0b9518143c8502000d03a1082c05282c4d014029019400030304540d1080d08404040103060b00030000031110f0351725912400ca1035001041d090010541d0301d401000a5208000801c9801c0503007003401090f024581e20b0740d40c0403e00f9100c1010b076500800110412900c9003101c104400c0100d80050308917003103000c008081022440050002020070040c0c02c2e8655440f202a81c1840d02c2c100d0320003503c1c840d815002e4050f070f094185002e1458001d41100e1001801e0381810b00200c104c40415008011008a11500140c41c0401081c9503040c0450038001400061f96240c505401083c1c444100f00d4049840404040d501d103600b070049401c0100b400c505490401c420f407003d5155060081c80c06005a541c2095504200c481d860069000030494407a0025000c140100b1902e03400c003079042490702d502c181c08181c2401c0d140c3c00c10614 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 788082140 1250 788080890 788080897
    0x30708030a051005012001020721020601080319030e03090909010c120612062f0301030b061c0b0a060b0d0203042307090f0f0f140a09020609060c070b030c 68
    0x646901081142c0e01e0082c2811410f00c140700303442c007103240a5051800e1391211000700c80100b4400c400946003903140e5440419900704190b40024003414400c030040004c0c0d051004a0050500da00114181508110710f80701c908640c00d01c0c6d00c241503441619003101c10051003500c008840c000c1001c4176030316000400901814400105c440090b11203003427441a620310348203180079500b2580c80b02002e00010741d00c0400800882c110608054a01c0c403034042c406000003061200d0b48507801e912604c5c2d5246d8035080383d40150180c42d581c415207504c4022411003601802494160360070261000b41c42d2908205800144015009903c0b4407000290711040c40e01070360015406648201940908a00c80c10900e03140d1240401c4c0c000e103190003002c410000304600c2e41001c043c501e0a00c400003182020404c9040c21202c00440c210510703511405991b2501e441c02c0041d40d8040d1806600f07001950351035000440c548141c1d02c1680c840d0302d0200d09221110304c10031041c40a82440381550b1350741e052403001440c0031340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 788083390 1250 788082140 788082151
    0x2506061e0807120309090515030f01141e16031107051c03061805040309050d0303051510050706020d0207050d050717040b0403031d04051005090105030607082703070803 74
    0x801e1400001e00e02d00b00d01c494151064044c1c0d02c02502030300701b01c3c080000d494090424944a4a2945e0754412960103002c0400c086e0000000020041e900c8030b404a4020300042c29408010940740c4d10310342010041061651040d0001190103442d07092810540042c1100340d12030b04000004100741c010401b0024210391a0061010701d8146c91000c08030842c1560503500800806011200311280004c103290030840d080f5101c8d040000d0ba2544482c0440c0d070881d4036503415000243c42e40d041c0001d0546400110340548000d84542c449054102000f5103144034108005005560010b8051240c3c1009d0b81695803160307220040d1080004442030051640c2c00612050b5002401603240040c1c400e05101290304681c50030300344034141031440d101900c4210a8601004000b42e05e04030110041c0d407284a25407140d058500c040100d68108010f012041405821003402603010400384000c080e0444201d55001078245166400010a02e6614203a03040c0701000000a100108280b0f0801494001451084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 788084640 1250 788083390 788083393
    0x1060906080714100e100e0907050d0515030c0607060f020a0f0807180e04030519090801060806091207170403030c02040b09061003020309070503030c1b062506061e08 73
    0x1d070700e40b0200400d80313094408040200c0e00d1241d0100c41c1d410483c070344000070f00890a080b06500c40c0c14000c5040c4100494090000820005008042202900ca540d0300160044102e101034155980030039500c2d801150710303522030000030070548204480d980001d0f1941410b86019903da2001110150660300d41c0b06492000c111184001107030144101d0107240c0100c0e00b1800c41140342e20304844402411406042502084820040d0b0003180031010b24901c50361000d9564071142c0d0345012540f9003102e10642010081e074105c5c4040c0034004000040c01800d0301343c07c809503680d030445441c01100c3c1d207002c00c184050800c4042000024560003e00112070301e4026a0b0620a4014082c20480000d1086808980c030460601d00798a44034882e40c003845d40f10201c00d0407206c11a032200002851508400104010740e801106500710480b600c1e144444200000c1c0e65407410b264070380065000800b031385500e05191403030100340503060018075005000106200904507000102d5050804084401c501400e40355 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 788085890 1250 788084640 788084669
    0xa0b060d0f0605120601061d1008010315090308061207030c0806010501030516051b03040504060b0715020a020d05180d03030b0909070614280c050d021c0e03010609060807 75
    0x580c04c00030b5048540308100e4002e80126820600d042d03c400e10308640d0104001e041c408542e099449038161103510402079110150b26614501c0c0c11041c1d401000d4109402900303014403440040d800098007a04042d048946400e120360100f80300d46845cad41580b01520400c000382c000501e02c0d50100701581a02c8081c2d8051240755560740145c0540e44640031903800145081160030011054622110610640d4005680c80e081d038810010342130fa5482d030400c08484900150b0041040380c2401c0782c5400f02901c1809604042600802130b46a241048014091000c0060100401d032841e4440700f00000c401001c40701c046046050040042000c020400d020701032802c04240b5400c0d0008403101150a165034642c025604003081103800d40200480c2171400412150760311900003003021418803070200d5520f641004003141806850200f01c00302c2c00040d50007000701c4169030b01540042d40601c2001d03040c5107003550380e02d80100340102041d078072400f0b0701c0d403400801141030207000c2440c1c021034007200c0d03042d00c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 788087140 1250 788085890 788085899
    0x1e1305100920250206040b121e0112060e060a0b0f040504111c0c0305030909250815031606030c080f01050f060c060406150e1e0a0b060d0f06 62
    0x282c664400c0a401202a080c445481c1001c100114104003401848402038801240c0d40410510f40258000030440000807601c1e401c003003031700d023400c661040c00500c2032102d108005100306048001809003188001c048483c820034001140c1102001103810b004851161501a14500003028032542c41d51080d441000382031841c1c80c0601446000d1030300300180c035100266107410400810155008061410ba40001c85070200384030182200c005e5002c2c0000e16a511465020010328030802000071664040c6000c2c42900c0c00b66214800b075110540703080c522002d0321402c0c0711084046401220355414461a1006c144018003034405c4070483e44981c900780301281d04c01005940301d88040f28012840f40a0074010030140c580900c074110b13920300c043c0c086461b090400c02c0d00b900701102180c0644290342c4400c0c501d011011040101d50003040c1d204402182420000f00c4200c03842076246020aa0342c05020220302e201c00c256100c5070f01c001c001007000d6030310503189142030301a24000700d2040d2510310f8241c2c0002d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 788088390 1250 788087140 788087171
    0x4110409030801050f03100612020a0e090712020a080a120306090e06040f06060b0304060902100305240a05101214040201090611012909070203091e13051009 69
    0x10300180d1540b0b400704240c1c2480107001c01d0924007490241d2500c41e060710310703001000912030803000d007505940c05805c0e80c1a90060043e0070f807059020700f54103011401001031045000c06c200c01902c01d02081400c8000b440c0c000502c0c0c010140d08080c0385800f81c90004010015540040703210f543d1039032018040e1950710b9400d0070448030641c0c46900b0540004000500103941013402828141c4030301c00c00544103490302c0c140c0c14030f600115004c840b025540d0000c401545001c0740407154241c0da031301c0d0078081c0380b620003105056030001070140031080b4404400090103a4541f40e4030000b0f810f02514080c1c0000d4a1031004221060b0442e00c081d14032300d0f08405246517506203900a10854041e107417242c0c2285859401c0715107201c0c2c41070b03102d0b0a56a03003481c0024a370ba401d241060711800d2012080f0100281c50401c1030882020703060b04299801081010324540706c000a4420010840d616401c42d1024800414440c3d00c40c080028100c510b0002040003d0813601e004800740c80300580200900c049840d400b9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 788089640 1250 788088390 788088401
    0x230a030b030c0d0803100b0a051b060403140d0b03030c0114091903140f041d090619090c030f062307050d0506030a02150c1006050603060f0315040605041104 69
    0x854001103c54005000300d0b80100045802030070242d109200c0940d00d0707118001640000f00b20000180e4005500d080000305100010741e412580c9010b0440c0d420315a80241500880f20040885810b0200750070008003095440425260005410344c0d640d6044500000c1c020019912104c2c04800703950301040704120001269042414401c1391210035a00342e40742525140c500d9000b118140c075041043d007003c100010013500041001030507200391151542600d20b051400281202c107668048400c1000c40d4100d07810126005801580c00103060100e4100b5070080d540720340000d01072800b003040d0324080200c2603020150020741c1a52140010107004c01c4012850703c10399215000500a02070a03140718000e138009500b010004085400c00040790b0f0108001c004580401d4920031000311f80c03070400030b034180312164003822100c004011340303414900000c0d00c500000d05a14081d2070450500300646d1020000d4030401040c080b0448460319046ca084005010100d84c101d0308940202c040f454503040c01e0054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 788090890 1250 788089640 788089663
    0x7020c092e0b0322170909010b0a0f0521180606120307020f2e03060f0815150a0909020a061b032307050105090c0f130903230a030b03 59
    0x340780343d81c540303d16800b1204401082c400e0300010644000c030001c0c550031050072090800070305280d2104045820080302603c141d204002c004e0080040045055000060b10428012402c0c016165420b1a44071328048005a1804003072010541c10300c004200000702e1001a083c101049459980d5680e0600c403020720002658141ca0f802030221900501e0820380c8090a4040980143c0d010041008070908850380613080c690300d01c0000d410038040303550600074280a00381244040081c140780c61141c503034503000311602000e4800b020f0041000c86160052110030783e10001c0150b41600d03140c41c4003000818201504901c642c0f5520030001d06103008040a005201c9079404116004120313031010b8070a98034039141c48403243e00e00d01d80794074852010409454041d0151740006494500b03000640e14010203030104501c2414917440c4c0d220300707981e402c0202c0300e800c40b00c05c0003044400d01c81c9010748540d0b0003504141a41c94041108020185212014000e41401c40d07a041c0304034100c01c4145070701e92020040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 788092140 1250 788090890 788090909
    0xc0815060c10050901090602040b03070e09012108090306100e0106080601140912030f0d180507180e0a0f03020613080306060702130e06010602150702030301090507020c092e 76
    0x145507100110941c841c44c1d000120000114111000307a03a1001240e1064008a0358150f0104c244482d60380c3c0020b11003641003040e07404030425410200308021200540000001c5480d071807284908110150b0283da00241014003240c9990130614a54107000e0018000c100324101000e00000c3c1d00792191000c00c0c050380040c1c403002c03039040946018803256400000d031180c001218000000c4020b9040001b030500d119456079051304d52400d50307415000d4480c400413070302c0380790355001c80d1101090000c1940d01c00c0390a160101075910f1805680705018003182c80c6110b2260050180d034074240140c000b8141c50b0030b4402c2d400d440d0181c0c2c400d1800301050016820141145406000242c0a070500c4401070100c640000c00d45c1304154400120b08040e80e25241c0507140c940c002c0001004110380400c02d10004104401c1860744a1030035003402940c0c0d000c14441e0340d01441d268400b08000c0c034001d00502083d28005444280c8038a0141070003005201038041c00f4820f441002040502c41809000040c1035545081 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 788093390 1250 788092140 788092153
    0xa0507020d060e120405030f0c13410c0304050a02040c12050412030524150412030810060f14070309081c0305060a03020f0909010f0c0815060c 63
    0x1000d02502041d40700e002c42d542075661403040c521200c100400c010b1032007109001c5540d10305040625040011480c072145182d4002d54500b04c1c03d564040c950401c0682a41c7c0c00201c551000c4130700c4007400d000b6610103096152080100b94140c162050b07440c616440d124402000e0b0b102e0702d5003448a40300c1241c000d000c40e086840c40f5401460310740c000340004401d42c640605180004000d00d011078005072021500341d0baa19082e114030580500560790300000381509030701c0c0c940400c00500d40c03041c0c0741040e49109590314500d007140c044414041c0c0b0040c0220103030b094840c80c140d04d800b510a030300a42e0214240b0308180e80015560b44a044104100042a9507281070300d2003000e4117441c0d9400502044061110307101c0040b44004040200c120215a000e903840000c1050100240c00c07a2801350210340910b032404400e0000d0b8940b000c202070020403d56090303c3e280d54030080e02c2c0c010192800b007a11860300302100304000503802401d4a010f1010b02090000c452441010000b082c4910f040e034880680200d07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 788094640 1250 788093390 788093393
    0x905070f0f0f0c111002070e060f0108150315040807030921060e0f0d051c1401031e0813031b150c030302190302040e1e1501180609060f050a0507 64
    0x110040040140301354440b02c5107000a90004081e004041420001a80121003c21500b4110300d14650004019143d01d6810340d2000002070210300020024507800c0480d040031049904d0800441c0c064407002c00440c5503e040c5031400050540c84154141d0001e0309aa102148422910388a07072034004032680001008001d6030b456102404501d000140b803802003041114a6040a01c94404401039540c0d5241d5076104190101c00c405005201d115031403460300403000ba5650b42c200300c1c28152500315010350103046100c003000302403034040032004000e00c2001c01d902004207646403403e420f517403160340020b10440c54202d00020b0041e01c0e204030b035096050408c051181a004d5185011b040f4068a405454981400b81010341c2ea040301c1d24803400694001020000c2e00607020314240c100d181c0354240c01c800e019201101d800144060503100306d1005801e40c170074040e07014855001c1c40c4851005850802ea0395a00007400303c15580c842c50f004103001d00500040700b1301c1001128060300d001e895050820f50345 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 788095890 1250 788094640 788094647
    0x70f240606023003041a07030b150319090605010f050f030a020d0302030d051e011203080402010806040b12061b0c0607180e090a1e020f0402220905070f0f0f 69
    0x1ea0008140c545000f070100400180c4500030f602c1a40541426108140f80d4054010b044400030010802c040c540090320f0459540d003180e01d009a03a10002898603500e42007000303c0e45002417140042194600100842002041c1e04554101c40214021004469031a0305000780f5801d480c0398154141c0181c414180140f800d000542c0c40c250003441164106040c030000c210403500155005403c0d0b511081c4200c03400126440c0e4107000d8008511a440502c400307560280c00c04a01500090500007130b01c00103520f0f922168403038591303041d00900d007c5036011024030140d2542c0c42642d0b41940c0c0c5c00a51800a10030303000c5400c40c0c1d00440d0ba0f2008103a699200c0400f10798003511540b0031500d150102500103400001c200c6e2040c0100c40d5003001c4e180f24041442c000c44811408201c12640b2500211400090b9540c48032000e10703648282c43c0541d4841d8568140a850136002202001c2003800742c9004c181c607541c582c050f503c100e1081e10b0f89102515908801c0c0d0300503401c082c9600014840c0212000111f12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 788097140 1250 788095890 788095933
    0x90d080d06051306052b150b0402070b0f0c03011a03040314040e10080607140c0c040c020d091a0406030b030724020129060708070f24060602 62
    0x228124002034407502c890000e520441c1191001443c142c071800c00780714618080d4440c006140c06d070160110006d100e00c2d42c01410707001440c00031b00700c440411007103048880d40c0e8220045001f0020070440d43c690036840c0c050300d59042500d4244402e030410b00014580c45a030030469041e210f6822094000050b034220b83c100365800100f00318200209601c01904812602003d00098403001410b41207503e0040c0c28000c80700416400402542e201c81706210341a900001e90340d01910b21031026540d0340300809203092400219007407643d003162034049071042e0b003907022951541d8940c055466400c81941c0f105000e00503e2802d80110411000308002c204039400780d8002c0403011005815540c9188e510a03031140300c2414411500f81b2080d0f04446060b110303a0a10031241008444220241c1c1c800032035519034440d101081c1c40714080e940000f078102c1031002000948034160f40c030015009109040b498203504400389640079034184800380c820803200083c60701510b026a00c01e940184001e00c040940b0f0040c152 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 788098390 1250 788097140 788097157
    0x30303181c0e0603100f0306020403061a0f0d050a020a0608061002010614040f0e0601031214040e070c020a0b040906030c080a020f0906061b03191704150b03010c170903090d08 77
    0x500b45c940000d420800d0301551802140103590050310340d499820a802660010f041071a609401a00380002941d50200b4201c0c41c024180c45240008083d458070703174035080c1c2c1030f100a54807426240340040c24580c4101500c2c81642c094800b901d943e03604020981c00c0c1d4405004807858004114000007a50405038041c2114808084001c16141030f003128803418814203070000d40d003a56034103980006068104c6645c014415403108008c0c601f62801c48000300024000d04940200301041045101307550320000040c01605d560b4240f1507655a9504840006100900c821100b40721014000210202d000c80d05689194014002090514105040202d10355005000a61140061060b00140d007084500c0c2c00c4030b152440011642e9060340f00c03007803d54043e80c0e0300305420843d9038020b000d41c0b041090800b6030856845124452220704c11040c2e0400342c001800005d40540ca481c1d4101c00c581e500c00a401c00b00e9101d0075410b00039481c0c03402c0003234580c454100c0d01030300100040b1076140000d01d080004d16455 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 788099640 1250 788098390 788098411
    0x509011d0c070f0f0204180b060609040209060c01090b070c11210304081f09051002071e05150a02041401050d020405030d2615010e040b030303181c0e0603 68
    0x2036883da40c807440d000d0b410700e059419818140e19902141850720406200c0d840502184043d02c910784e850510b80e0710014120f0b03024820201300c08845440d990165011800c008004545603a00c3d0b0515500a0a1128007a52a45c42c1c940200c1c59481c026103d044400760060010201d42d82c1c41800d00912003404504503540f00d90107010309003441c009101500280c00c0340e20207003800c0c00100001003002103c22880561092529060300001840001c0e2800d005c209260050b80b02c41403420840b20008510303244a040e01405000f082c00c00c40d0100d40251481c034541280c101035103900340084120300840c083d00110411041201c000d035802500a04614210719101520303103910b4001281c14409040000720209445060000e84850124090044561b107401c166072285030401000750004000901c00b030600100c2600800343da00c4a070001c031202480501141c0d074138280301040b8a0f07081100c1121405134040c008000288125901034255611082e68600c0c41482c19201040040c0c0d0018000c4101d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 788100890 1250 788099640 788099647
    0x60c0615010e0a0e3607050a080604170903061303031d0d0c020d060c050304020a060507241803050d0c090503060c1c1a12060712050907031b050102070509011d0c 71
    0x20400340484c4007107a0008070308401c0c0e0000c0c20382e05040c0b506c0280e4011500c2255400400c0c000d00500140761948560031145800003402e03050542101445601101a01400f8241c2040b045101e002481d007000ca2003030b034040010481d040d1020340c0e903880318034444030305400035015010414421007014170910300043c003080c2450120b03600c02c412100d840407403c01250020080009601d07104181400600d010308010780741400c1030390383c0c0740710203034904c0032281c46400051541d03c40c07252540903203510140e05800700100e00480c203011b80f4036000098190750481c1082c1070225182d02c80d03482c1700121280070780240001d031142445030301c0700d400c00c0403074504003144a01d4404100045000c0c01d00c01542d11084596658a103109000780503281401a06036a4858814000c4180d0300c001220030050580c000058291141900903040000e41d520151038a1300302d0800501010a10740d5140c2140d40036000c980207140d030b840500201000911070740307001c1420a120106100c0711080001c0d44190f0021041c1d01c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 788102140 1250 788100890 788100931
    0x7030b030106082b020304090c090b07031808070e16030b030607081f050f0d0302010204090212060405130308070c0219090207050606030708030423060c0615010e0a0e 73
    0x85810b954000c010690001c55400b000040003800080c900c07951a03500c2040404400e03010f03640340b107a8400d03040041c2d500da600148442c031944424005e001410749503540ca05407410000c10303003483d810100c81035841030040051264000503a5004582055420303000503075960481d4403d00c0741c040000410b041c5c582080580c03550f02402424030807051612480042d0a24060180c1c841001141480c000d1000c0b000500503955030400c00c9148580c222044a5131001c81c0c038040340039004175803050404074004200840c19030104103030180f2440058604001c15070310100c030b0300782c40d50034901c0207004100c8034004030b40b8247c46584c0850a450000d040340781c41d8404e070301c0d800840403c60741c00400442c1c2c1c00310b010410004103104076600031508900803c140c60500075030507140d20941c861164106a0724103a041203522200d110b50a00e1402000341d0b8440c446400c0290b25040112408050081150510509503015416030b40101402504a908035810040601d60030600a03007011040754440c4052074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 788103390 1250 788102140 788102143
    0x2030906062d04180b0f0a0203070c02060304020d17040302010215160c0c05090f040213092a0905070f1107030809040b0d0b0703150b030906151f030c08150d0b07030b03 74
    0x1e100e522034440c1748414030700304009001c201e1018141701e82480c0104140301c0c9440d40103103064611501100c035691b4035152840002e2a00d03641c0200289119900c0c00e0b4918002c03e40c002a00031a8003c0c0c096495210381c170101220240c00840300c4c04e0001501d811400710240c403801c0300200b0b191103841c0100203d510ba000190a808044800d4055610307280100002c50502940c1c500c440c40c801d00d0300780841842079590304840940c403e5074032405061190004a03410102d002d000007490800c20401131400c2c44440105042e81c000c07141004075410607107d00a000300003a406045a070040e0003142081e020800300000b5141a006556111f1a8049020f012a042203062030080c0d280b0748000500e4004106072242000e035503807003031040d03071401c1c030400c0000c140114800b61f011244d401101070180b0101e0000d044000d04d804403101b040c514031006828181c01d6408000c3d255065207401c040c0c1d030384619041103040709168010350001c070883e0040d000205809142d41d0801000d00300032030241c90b50b40109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 788104640 1250 788103390 788103431
    0xf21030504120605180f07050f03010b15040503070605120705070614070914101d1c20090112152d140907140f0d0602030906062d04 58
    0x740c070340311340e11000d02c8107401d245030070305d141952054003420200070320340e02c601d407595154440e10340039941b910804030341503030217501c000c96096008110114405060401c1d240607041070203124000e2140f02000300c8e03114050819280d03441c2070b10780d41a030580d940e08422503994000b02ca0448141e03072600c1d000c04c4140b1010455510608060340e0b039a00301d51070070f1014044140100b80c101e00500790030400c00c0700b40782c0c01050345c455920185144504010b080c1c0100e18243e08881c60b0041c05040c1f0002101040103031032103240e4070364545c1c4c22205528410810842c500b0420311174204000d4071007200e600003d1701c3c514000500c2c050440c000903650318203440c0d10819000240b83c4902003401003890920b8003000d108009003440000c1d0b14414a203401100c183d40d031000341c014060040603d002040c5940e88031602080808030103001500180117615002000c0c0d082600d4181c91b902070f03103001403e07a0030080000e6140c03010403403010b08003c0c5a100010070282c0d010031911742003904e40b41c9924041e012035000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 788105890 1250 788104640 788104643
    0xc0a060b010c2a15080916080c0603040f1202060a05010501030c081f05100909140403050f1b0a030804201003020c0703061a130612060f0f1d070f2103050412 69
    0x1418500c6c585106014108107030742c400c01551001c400018030009400080303a41e0305080990780a07a51b6203507400c281c0c140002d5040010130301e07548104507844856000c240c00d4050300d440c030360910803a604c40006405680b00284010002249000007030025110340b600810182c8082403100395a0f515000410010741c0d86d00d801c03501155034050104401c0d8601d2051000c1130100342080041801c2582c1d000f0711030b208509101d00c0c15507002c544401041ca9401c10030200480e8581180c810580c0e40c0b03000390095004071011348580c0700f09443c5070000309210089800319080100440c0040d54400403c3d0000c1d0041e416100b250310440d074012000802c184102c030040780300a01451214803422003084448414007924041035800e260b4100a0480e0036101c00c103055503c010041615100381c0f4010006189910001c0790701400c000700c19442065034070381c0c04003080b20802980d03c4203407501d4030944a060380f0b00c42c50445111111403807040c0300a00703140414980c0720b0700d0203510305070740c40742c0080541c07007203c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 788107140 1250 788105890 788105897
    0xe0a0302031b0c100302070507080703150608030c060a02031003150207060e0d1b290402120d0503181c0f02070609050105160201030209060c0a060b010c2a15 69
    0xc054070b0b88000c1490011101030700d03000038202c141140d008a08a040c001808605142c1c010410104221050108402810511017100d1101c0d80d241400780c0070006a03811048803918048001c10b40c0803010007211580140b000c020007154550030400c0000350f100030281001000d1900022001401013141140c004240017005070b241e803030314206401164490b90900a50742c1c44001001d0302690441d0108022602042d02ca0010010302d041082501340718544c1c0700c1c00d003005540d8017035503900450445070141c0c1c000d03031f810300b0806aa00c002e0383d03450901210300c0d0b0120f48203100292441441c03010a800c0c561941003543c58000400c01c42c440d103c8410000500130803a555494500c1c141d04101803002003d45290000c0041d14103400031307100f44526048200b461030724414510542e40242c040315101c84000c0d00303440d0b8811310402c0240c1c039030400b81c01c116202810400c403200650300c602c880d452100c0d0004c0405100804ae060300c00c1c904060151010f03080904040000340c0c03203a041e4116500d4222584 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 788108390 1250 788107140 788107147
    0x10c020a09110c070f05010f18121a0604050c0d02090319050304060e1c03051b160303020c190b0304050a05010906060608100f14130c0302040608010e0405100903030e0a030203 77
    0x40fa070b506001e070035009400d50540310342c020041030780e0205040c2d280311624100b01c3c60000b16440c603000307000c40a800c0841420144d040d00c07070802400301c0d00c0040081366165210364684641d010441070303590a4601258080d802e01115412100c02c0d8003c00c0c034a00d0042c00c60300c00441411201c03403c840141000d881d143c1000c51704100b4541c020070301c0c441c01d072003c031080889400170780d43e50078800c090104050100900815031403903070191180700680c1000300008a6500000310000101d102110740000c80041c0030b0001c501c0350354286080c400c100015405642503003c0e080c032041401c40d0300024402d440a100c0d103443c00c1c000c04c00c28410f00d50350600565010170803d00b0840c0140001d03001030b1003c1413182ca00181041701c8905845001d095034602c00c851000b49502c14000f60300c40e020051112140c501d84074104c0f40c19a01030f40200229000760721081090703a600c603007004200c0070456014000340c0042d440b0a01541403a40420344951007401e0008844115100061030f000710701070100c02503070000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 788109640 1250 788108390 788108407
    0xc0a090501030510090f0b0601180308040f0605030112081e0c1006120c14011103040f140d030f080414030316082d060402071b0f0b030c09010c020a0911 67
    0x900182e034209401913010300001d10b040d41c94810280d40158054208150741d80801c84903031184034800c0609624042d894901350312400c00c840d056100348100c20903d40910030000300b5078041c034252412925401018035221032140caa0200e1580b050801e842281e030b0110b600c010b450011400340090038580c030002c20001100703c040904581e0303142c02c104e1044091480e0a0002643c0e044114251980880780d04402140180140c40740b8046080310074035404045400301750a841c110b40b0b03500720740c14110a26012007455091103000000c006001d400500704010105076140240c4030290400d110b07815101405065009441c01d540040d201058550500c120f2030807040e9000d1119a001010214824440103c82c00316110051111560350700b4032003003000151081d5510303410749000b25013201d08454041c075031850107118941d10340545102d616982c4000315070054400b0580b88201c1065010900e010301a000554001c2020003040380d100d01c00d0b141c0425205414000c150100c074400e40b1050700c40114 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 788110890 1250 788109640 788109643
    0x11502060c04030b13061b02101803050a050c0309060408031804050c07110d020301090f03020f03030f0112111203092706060c0102040320010f030608120c0c0a0905010305 75
    0x1e40390340e1107950244800e1010501406690390030121203681200444440d151203c060700390989003242c2007080010042110380c02180d094400340d6030f210100a8008a040101d458146407031000d8000f58080c01a10300c1180224005c140c1040e80404481c01c02c552100010210f6000780c02c18113050700301189140741d1070360524082e010840100d074144101d141884010541d4020002c0240443c0d242d00da48008a44500149004160300a0000c0c80300e0007440c1440803080703ca601341240103100e02d00b0488003e1501001ba00e01030b1120391350890032a40307412245c8007015444030342030700d001941e1110b40405a1f290b590100503428540041d549a0081104004541500109071008540100b81e250103c4442c004016444201100ca0a03141c90021019030f0090140b50001420078000044d0b614a18082660540e620802640c070b2480c104038400c0203c09030340140c4502c0c1510350001025100d12601100901000d0303490001f03c1e40c9401400c0005420082150b205001c4aa80d0f0780041c02403010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 788112140 1250 788110890 788110903
    0x314070c29090f010507151b030902030703030c081c06090b031507080c0c01020a02100f0209030601150323160c0506070302090409050604060519060810090614011502 73
    0x14506500307004152950032980305403003080b6403148168611003401c030003680240166504150490060044403141025940c014050001c401e03105009000c8000070641c0729000d41140e5642c09000b8000a600d55034081d504904040c508548400050040709a00b201c08180340c0c607591400c08000c51380301e1a000102c01101d03d07401442c0e00941114184600703500b4016000740e0080c946141c1029035980d824101e50880c010542c800351070b07500016041c04038690005103281c94002e031076010407901007454914404c9200700c803040c68041c1c1103100100700d00d500110044480d00300508002c1403551703031004c0c0315128400321800907203c11540d0b01802500b0051a88103001d8a802c0d0809040c1c0214580700c10f0f0381c55500401c200d0401d90002002c3d2400c0d207664025402040d4040304484c81410300c4d182c00744c05090100d91100b01545c103c02d000000300500e004110869031490050001c6090344403410000e058181e1081e0340c4503458080d492154080341c0780443c020118211620509150010700038200351 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 788113390 1250 788112140 788112179
    0xe04051518071802040b07080904060e150f15280c080334020105041a010b0f0f090a030807051b0a15020109051b04060e01060215040314070c 62
    0x1141d00e00080c40910004001d010b481c40035680200e1491403400000c042e01c503a03000035a1040021a884042007002c0000c2c001c620f100322002e101140c2c60308a0401c0c044005c40700103055001a01480043c1e003000958080d440320043c0404a040d01c105075504803d9004e850240380c9241001c061174418058040c1c401c605040a01d01400110303040e4552000600010b030140c1289500c1030025212a001c007a500581c503c84001d0700259080040030183c002c1c50221400e80d50000e10b003441807189255180841d060f607030001c25403814056032500d468015000142e0000804100b0040d07400b0030782e04c0312017100055129901d03459486050346060341c1010700c802101c0c06200b5124002541b0390307032048004001c3c0d48505140100c4074070380e07100c202e025000020340a41940a80421840311001c408101020518140c1d018010150b030f4200440542400344105401a0810101440c81301490034016400c14020316000c00b000c028280e18920f0741e4000a01100c0030004c6210402601078541140c21450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 788114640 1250 788113390 788113411
    0x507181503050a020a1e111606020d022a060d060311130501121401020d140a0c0503040f0b2512180c0501030f0f0e010c03061505071101090e040515 65
    0x2030030f004c00500340c1d1512002c11180407032802d00d1b8014503403040c151b91042409007002c40d40a80340840303000c4880e2505008100041c00790320b000040ca180001210007a007520848031104d00c80031104100c980481c400c2105078014020824115100741600800c9e019501410020001d20324050070050300b0540e0410b000d402a040c0b10042062401c1810400b40c01078015008a1005000d5a0383c00d009106d000c1117081b01d14030304000350400000c0303031945510580781c18a041002032858007040e110780c0400c86d0020308144079001241c0000300400c09241d003018602a0104410811891080c4d030f502240e80c18200061012105508543d908e015056a40703039402c0380b03c212400d003507c94541c540e515010351411300d80c589244802e242c1c1181d219203040140c128080100c1c158805409000e0144044400002070030710002180c1011a00c9d6001e41c000c8140c1c82d010703d0714070240e44502c0b4041c015008541402041c0c100010301c0e4402d240c10380d00c141e1007a009890700041c40070b000c2c001c2c8031000d8002e0885 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 788115890 1250 788114640 788114647
    0x405031b1017040809270f100b031302010509030d0305071209030203160203100c02060105040641060d090c0806091b0a051207060206060102030f09040507181503050a02 74
    0x74050700070101038003d500900e1080c0c0d1500c401020400e0901c3c0400c5594140c00d07000e014042e010034008466000d103007078031801c1105844442404002e5641d81c001d110b05d503041007003c60101a242401d107040148103051540c181188000024140718510280f940802d07103410402088651054013076690740200a001c12200c1116100256a801155030305000d00d000058082d0079560708218802807040c3d205e8050003a0310086000075140d60003846014002c0c1d01344140890940c0d000403c2c40b01c01900a00b0650b06110f460035032902d98150783d07800d2050030a20031043c40c00764848100502082c9005c1c030012400740748c039241c0601400c1c40b80c0d0118042e80c200c08140003030388101080102090b0b0f0142040c40c4410034903c0000e85034100c9034070190b440901d0151101a400d0041524001c0369825000ea078182e41d15400160f840f0310600c940d090802208002c500081d240950241f034220300b0928180d1400074030100203c02e043c205410206211400700d100b110314a43c5400b80f00e601c4480300f0015802c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 788117140 1250 788115890 788115917
    0x10309030e010e0a2c0f16080a0603050d030225080901030b180108061e0c030f0a0b04050705090301060b0708120c0705010c260613050c0405031b10 65
    0xc401d01004060303040102c14805008241e9440501c88090010318654603404c500342080c1c14052800d03c1c101001c02201a4001482041e00400300c9104841300d030b00245103050601d004590410307000f0410f500d8540d4801c00400403903410001c4002401d82503d005a58204041c00060a50662580342c1501d46c04400e075480080c0c1070005442c50001d083c22f0102e403d182010010700e908028810014607540707020300000f0001c0d0002501130140c14422a404410402d142091003021000c0b28840784240003000030848003c0b074860b84951001960000240d004482c40006d81a0307042511003400203040030032058402d140038800c8100500780f11905925021082c1d4131350440c0c0c0a401102c80243c1d10744000202003070054400c60703540991240081200da510580050310056400c00c060a000c0d00302194001c81d52a420150360107441c0041c000c203500da0a14044402038a0024411900403a081c00000f601d500d0170049000350348100310110885c410707081d0500582c04a50301c040c0b03040003080720394401f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 788118390 1250 788117140 788117147
    0x4230615040e010204080115170601060e090a0e0625020c0a0b07140303010902070606091e050907080706020303011401230a02031e0306030c031b010c11090c04080c01030903 76
    0x400000c410364010400d0740900c10a03d0090095038407520045d403c003200b009002d0301031241c1e107043d03620781100200348e0703084100c20540c0c0780c0c0240503030004100d412601c09514600f007a56180c0c007a0040d000880e51004480b0039038180701c0b084e9030802c000d90b902c554401000902c007021300701f43c9401e48000c200b000c00400000742c00b58001d1194811400000070480c003440120b074060500400810200d0342c1c2c80d60741d075111400030b40c0300c11800daa00f245001d001242d1118940940011000c421041c05030505548003490020600600790706c0c0300d4420302c0c00000c2c1c150010700801c0003c05958001c4c42d107a614103440f0040034a0a002a181003200341010348a40f41c00d40190f01c61400c2c14107035a90b032120b0014009038918030483d0507003904ac0b0070303008000e04c0002c1c402004600c510003d0b02900c80e08102c901c00d060742c842590310500b24520042030503a02c5548a40d15142e1054000c2041000c035152503404912040e906461381225403500007400d0000341010840c800d0390704001e11b810040348070140c41c002c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 788119640 1250 788118390 788118421
    0x6031509070e0c0d050108030301090e031207030f060503100209131107030c15020427060509060f01050403080d0c022515052b06050f0a090c050f03042306 68
    0x100302080c844000c103d20030788440550358044c200003020415542c449181c60398035003092040c920b00d1030138079496035441c11020096a451341341e40c1203030f00503540703d0b09026006040e00a002c81c5000381e030b034040081e1381d940c2040082d10366540107000690f200320304002d00c1017a00c00d2241d06004941042160800000c0c5041141c0d0312542518200754542e99900e07019a0030800288656a41800802c0c040f40e03040c060102090321811402180d2208a440482c940c1914990b200700355202032103000280050405100d1888440b00500d0b16900d40754507951601d420790011a02034030903543d2851510f0180c0d40400603002d00c102c80401d8180c40400c1c9410400c20070105000d001c40000050341d106e20300502030802d5a07026410321580110402c01c041c0012050030724072208146040c20030000145e142009030441c441c564015040c407000d18184424030000c0d02c10349506004100c170401810143d8200c00c00550301543c8110011040c040c040b1041c5800b000d050041003031903400140910001e0151141103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 788120890 1250 788119640 788119649
    0x60703111210090e0f071e030609081809160e010908060f04060506060408030f0310031709010f0e010203070209060111011e151a070204150e0603150907 67
    0x8515251003692a0045014000e020808803540d0818041807010500c000026554039034810460681032507840340d5911011103900b1416001590240300780c800b69513030a03500c11b8500981d00c091554076580e0008031010031400307980c2a0300c04988410290b4003102c002d20b1074a0701702e645051a05001c82c40303004a100342d9104d85c040c40780c0f92200180d940d005070100710003400c11200f503410b41e18142d582d4103104d510072202200c5c030750314060004809140c0901541c042c1c441034401182008842156400181d00107010104102c1040c017000000a6070305118001c2014010f6982e5242e882020000d844e18003060341120a0103c45002c0d490181d90000a882c007482d0100c881d1b0001d900c42d4001641c2d4015031101341051075080a142000802010850548081496804105100c450045002d0101140c029540c62618032034140c100134001001811040380000c10001d40c010190b0400ca03c01c0c0026804140704200e20740400031185020b2001e0031100c0702c1c0c3c1100f5451403518400c07a075180e0403075008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 788122140 1250 788120890 788120897
    0x210309111f030b040b0a0305010504030f110a02060d0e0307080406080f010b0d02130b0f04050306060a030203060c0309010f02070c05240f0a0e0301020d0501080f1b012105070306060e04020c0607 85
    0xf16041c25945940000c08104000303000403043c1030b224100503001e40022070b01980418500d80201108510a2402c0c800403803480c0050a52035401d90301300110f82c1c2c070505101035840c2c1c0f91800d1124245007400102200c92050401131340d90751625201400d0004010840305400540320300411500310014120344081c90013920050380e5100170100c030300c04200307030380c1025440c2440410b0341c81c0c13003580b084028410303200d040f0112a4199101000c00003c503141d4080217402da000400411118410800a103403c510000300119040042c840c107801260000380065800800c544010000c60400c1520980d48104008184140c07003100c0d04600707041e100d8401803000440d00003600078001340c413814110350a60001030080d569483d0784030300d401c0035180038058450700340101c0656803240300b00040d10580e2100c0d44001c0224111184005542003425846210320b0b0101400c5140c2904e5140e108181c401e4106403800030f041760401000405218030001c030540200d10400103e01010000949103601072450329 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 788123390 1250 788122140 788122151
    0xf07092702090105160b0121120f1b0503030703060e06030c010e0105040506030a050406051609091a09071101050604020702060d090c051003020a0f03020301051c210309111f03 77
    0x48800b441501006001003022907045002c0142c0e4180f018120b4004c42d0300083c1869410340900c08030804a540286031500c1c8800c005091401600401a00465800d2152f0b10101e02813414102140249080f0345035000042004107150b0140701e100044c5c030b90014480494034207000480d69448100c3c000505219070814080b00700e0b03100c0c008440c09010040e100d80d0b220705000d00d010004d0641607800711525400d00d40001d903d08404035448424400d20799070781100d2450042d0301c1004200c0201200e400c12000c1c0c01711081900d070b20145600641050b9074028401e031004002500712000078200500c0350307004200010169440100b40d82000e020100e002881100e58506206008407d500c41900603030b0841e004040150107a002e450040740b540c440c00d0031704c80c806400328200c0c402400ba2540c0f01c2209c0309a01b0f0092809528080c0c0584180c03542004070700300e4200c542c42d040744a0003080002c1e844c1d40d0340e8401c00c8080b11524541e03081c00d45400504528601c145100c0424041d00e00040580c2c07103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 788124640 1250 788123390 788123407
    0x702060f19090c080d05040510021203010e09010b040e1b010e180a0905070b12010e010e0f1302032a061207050c071d061903020604060c0c09050f07092702 68
    0xd401000104070130021103966540600c400751081e0481d05c01c0d02d02c100000c90b842d112442c000b090303485140702260102d5103960309080c004985080090312034411990386440811068aa80c4244440e1220850007040408542a413040c1d40f402c075000c1003410880280600211916132694140081851001001c0159a400c0720071005210030341c000781182c0305014002940041500003017054030441c1c8130300c1c03a46a0300e5040352020400c0a12410682d2403c00d000aa034114014440c60b170013140c002001da0b0113034400c2d000607207890340c20749000c0ba090688801d0b456212403850004542c0050550300d650070400c5820644840000042c507040610034000b40e01d9103290402d1041001a20081c100c00c008601041d401c01403041040780c50902a1000c4688140c641000f04004412030341e00404103450142400012030320110001400c840f5a6582075002c940240507025031486400c0c100a1256189040791000701210050b90241031405101c2c002c2c000300103803031007610441e0f100001000d41d50710b886 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 788125890 1250 788124640 788124653
    0xb0313030311070c061202030c0717090a140103061d0612150106050d0c030e0703020f01090902041212050711090c0c010e070302040b03070b04050f0a080a0b0702060f1909 75
    0x560503502e50354000041d41c0000c1208004003203085c0d4010741d580e429000500610b0808074841900d904076104014044000000c12290340e230350814100007a61400c00402501180c10cc46e00b43c0c21159506040110901175940d05201c0d07100107091111a102c01e181d9012140c01c20310701e001c1c5c202801a0340d4000b812169020420480694003292031007200ba030b6a440100512541151414204042c00c00c41c1c508500d6100707004140600441e03002420a080c5035501300200102807250150600641810010711002144040c01c0100384500300000352040c44d1502010302d51000000c002441400e02065001c01c22507040b00c00894030030790b103003030b025110103d508140b80100d2400780210340c02d0a41011403c0404649201102d2080e079041c000c0c25145410940c5030001c034024150300500c1400200f0081c50240c40e450341c032038409072100c8030050319500820305002601350280c86600800d001d101d03d0790390401c50161701061440701d100d0542481c0002d079502d0b284001d45110000e403601c0055007803220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 788127140 1250 788125890 788125901
    0x1120f12032901080f0601110307060b040b0a031e05010f0606020a050f030f0909060d080309030703090803030402090c091305070216080105160c030309240c0201060b03130303 77
    0x30800c401600c21105500028040c0542c500900400e2038042607580810900c0c0b01c020203a000c050711608229a00c04800b001c0041c00148214100542510964a900014001000e0643c014072006c210340e084076040c0f2068821001c10140600a00141000803805100003440c0842143d09c8103c01110b030350500d1030160404940c48104107182040016400380c0024204011030300c51410f440c000421440b80175142c0c051027a545400c080b003080500801d281090a40c3c0d802000101038804031503c41d02c86141d07a410850300388500d98000264901855005a02d8100904035003000714658030301580421a40c10000d000d04042010226030071b503881d51502c00480991803014410031071454400c400030760315107000305c504c01d03010001c40380070400305010301802e842801d420718101d110100300c1900303d40b11520f0000a07403c01d540ca44524001900c0994244070a001030f00a001103440d0050120b0201c2d00b0b07942420055a251074010040c61400d84140ca51010100050b403900c00307410705054000d0701 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 788128390 1250 788127140 788127143
    0x90e060f090a090813080607080c09040c0210092f060904020315042a0c0c0605030601020f070b0310090c020d03150503010e030c1608060a092109050405160801120f 72
    0x8000c02c080b80015261192141129456007c80390551100c1c0026615580151582c035000303a000c200482090401d0340041000e0b4845104075940705140c841c10408481130000c0440d40541d00c0c10758580d02107083c5c1001c0c095003004521040b01c4848040001340584200d00ea210b01654000c40000c40c641101c400c40c04903440003070814050081a001c415000548035045d8034000056140b040c44854071654815982d95401201000d0581c1440000d4481c0d40000380450704510036089200003001080c0b191034001c1650152030390302e0342404000300a0100403030f000203180d1807811210001d9240d002070340d107003142100e04000400d1440402c800c0c02605060f00015090740c00c2544110204030000002c059018482042d00c0403100c055a4048400582c1d100705c210303d521000124862600c80d50204a10501c84c03902e0044099501000107824001e00c800a000708540da102000380e82450b01038036a01402440b00307440c2018202d200031301a100103000c0e08103a84010031030b660801c91210103500c40c0342d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 788129496 1106 788128390 788128403
    0x7140903160e1503190503070f12091d27150609060909100f1404031110180818090c0403110f0d0b04051c0f090e060f090a09 55
    0x3170940c41e080c4c0b41400200040000030b9480d1080211702d600c00d46041c510b11110f540302505100240d8000d984900b100c06030f002003c030440060a42c490451100e0305003c40e000c0d40c11007414181168448401d1090b01c1208000c2841d003224103206041c102d50414155545800380310b04030130103030b401681561082202480d8850107070420700d6810901c00c00043d1920581c4d039400c46140041c3c50942c0452044155100c8286003486041102032002d2014007400844419845095912110140a100000c18810318048450001c1c800c1c96000511048040c180315000c2c0a0b15401444112441000c0000c2c50140e403c0020a02035840740007054540d4010b004d4071544544400180b04482d94001e08904101007070b298a070024200d01d4507641d00f04070800301c82001d0000f81c000e4202c100c0c962520b00800089655680c0003800444c4243d403410016280d103014580645405413006110703 = true := by decide +kernel

theorem cover : BRFrame.Cov 787949640 788129496 := by
  have h0 := BRFrame.cov_init 787949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 787949640 ≤ n) (h2 : n < 788129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
