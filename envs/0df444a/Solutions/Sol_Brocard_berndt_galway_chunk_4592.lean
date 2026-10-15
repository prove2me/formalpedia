-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4592
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:06:56.672978+00:00
-- url     : https://prove2.me/submissions/45bf2b73-7aa8-487f-bb85-c41d7bd8e67f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 825719424 ≤ n < 825899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 825720674 1250 825719424 825719431
    0x103170a27030309140a0513090c0b09043e070213050601020609010902010801030b0606040f06020307061a0d0b07051b06101203053421031503060e0102090306 70
    0x8072a426801001055048580280104080d0300d00000418420b000216100d410340300c3c4a00441c0c134600480e40064055202c4507103650300c2680e04a2164484040c1708040d0081c1030894040c80c94114080340e2003691100000300849650444000d10003150760300045d400000c034880314018010300100300141d0b161320b40030140c0d800c070720000070f02e6240002c0024640a000703032400b880d030707450700d254440940d82c0720356078606485d080034281c50365841e00d0004c507207148542d5009803c100c40140c000f02c0d030a94044003c0481500070801804040e1004070509880d0a80301d001590103040040c141002440381101680d1100c00f40c00c2c890f00381070300d01619000d03040e10303403110b4045500701710100039402140c610100f0140140d4a55a0060303044c990f006400340c030440400c000c100b107008410041c00b04005001c0c83d142d640004211138110401d1400c03091020701c01e100d044800500c1c41e180e882a40c4644034051030a200114a410420b24540300c000c010310b202c41540c143d9540801c5910041d40702006000d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 825721924 1250 825720674 825720737
    0x111f0507090e011505191e05131403030c012f0909040f1505010609030b090f03030f040c24030506040e061305070503060103030804050706140a050a051603180b030103170a 75
    0x1c902c5048800007402181143c16009120091000040703c80b410006a81030b1a05582c0322b00c10030406000080c50760188181c100e00e1036007003251042d44c2481c80c0c1c04804a01c0e402c0c80c4850110b0851000c032111364040c081b20f80382c01c241c02c02e00140104482c01d0517048150301540d11251090380b0301ca80c103020b88509801102c0842c1d150141081001004481300743d100f13520320081c107151450b203009640c907444080c003d014505050004034082c01240725040d80100b0a1810703001c1e0003649204042e00c4034510496642c082460301001844900300f03070050340c170f907581480003600341a9075010701211000b000d00c90076111441507040218494508100b003d0286020303807100e01e4180f43c2440c0891402d15560020020020f18201c108204808681922107080840c10081c0c1c480b840796008036094000c0641c103804811050090000303168010115403880c3d01190b941a0466441d5072007000144001e100040115442c91b44840360420014007030300c04200d0707a1504910801b50700d4004010025418003405 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 825723174 1250 825721924 825721937
    0x10518070c0b180d110607210207061d030c0d120e1f0b010c0b2802030a060602120406020705060f04080604080309011a090f07111f0507090e01150519 66
    0x151419810400c1004407104d074600001d4040c2488041d6844050103800541403140841281c1030b49203034099800d1261a41c1c8a08548465103414580041d040358103c2089816548400d18600140403040301c80c4d004051005008008150070102d0307413006040d0301900816a60102041c50f0213061021000511195100094000824111404842a09020505210080c911000080d5502c0301041e801503a429500c0030010b4141d5107030341c800c01c0d445900a6071034400000c000401403d5844402503c6580d800c03503000b0847c40c4036103004d40c4030340e014410150303210401c104000d1a04500800b64240d01101c61030500782d58500261401c1c4e4142c81c01c03100000040104400030380d00748941a80303a6510090503550440c2440400c42c4000060005000c5c480200f0019106c40d0007048001c0d0701d1004601140d141003140d184002480310306000683c0359a0426010400700c5204110b028240d981203094240e0991070000080d501d030b00ca01c100842030000a201142800da4451032090b2400f80075210f81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 825724424 1250 825723174 825723211
    0x1050c120720090c0c10020304120905030d090515090406150e0901030c051c0209280b01020d0518101e031e0b03070e1806010e010518070c0b 62
    0x41c08820503401641e0381c90140c0b0308204219903030040d0071600011000d0080390780d80d144100740c500703202942883c00d00b640d00000034001041440701500512003926907a001c002c546902c10180c41d0807240210900041e100c00060040340744c407507810042c0d164107450007840c0800c110702003010307074030264803003c44040d40601c0422075a4010058102d4a507040315188055810740d95503152700551402403d000ba000c140034403405401d0b147c4211203854000748407a40500d4244545041c0091003048010b020300c0b4814400c0701c00c032460203512980d42050b00130f080c4c0c505546078222201d03000644400114510700c2a40105030301c80d042c100c0e5240c6003d03620002c071020362038504900b003003415642c0c0d0105840c103000503030f0702c15214000c882c0b0f1200c032a4005c40e4418178039000034600050743d08440c00b811051005e000180f202401c418803d444008142c3d0707070070380c1d8541d200c1e0b5100e41d09100d0203420850040c100100710110031035040c0e1042c030609020041c031703401da12602641b420071a0240c02100000450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 825725674 1250 825724424 825724433
    0xf0d021e0d1b0611010b031f0e061611030408300d0227030a031809180606050117010b2a0f012403020d03022802040c0e03030a0e01050c1207 62
    0x110b410044c6010000d0041c00080300119584038813001c444156083c015001a46034a0150040e0720b0320710004040b203445040c80c0784150040c802c11406440486c00205800040c0c08000c07068508941c0000c01800081c540d121101c1e2800311140c0940003561410184103c1e40242500907003c52020103000507241c01580c07101045090840080114514141d558124107580c0014900421a0700d0714200f1a40695144810014405904846812403d012040400b0600a8910100c0314041d07002481540c7d0f482c0c00544801580140c1d0382504e400400040c05801e0054004110780303e4040462001d1500003944110106034040260000340c000d100c80d1a1210024000c0c44004072452070400c0104e00b25404c4100744200921000340540008400e07202454001e00514078008800038042026410500704c230750b41c4011072142244520314241c00c90208901c0349298010a0324042d0042d807500d1180721742590b203540000300d1141080801c03c01d005181400b03200d109103252070680c40d01e4030786840345030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 825726924 1250 825725674 825725687
    0x307050712032c030a031517100b0f030601090203060102031303080a021b010918060f030b0a11040509060603131509030905040b01090e0c21060f0d021e0d1b06 70
    0x30100d91a09560610f144414808000c82c2c1404886050006504e1101290495000f9459000b00d4100e0f41c042034040800d9800328036802c0400c1150800c22044000f1801c1200310302e402e8045a416500c00c800510100c141d0b40d0003103401442c14012a0304040904801c1d56007018550811540d410780412415512a0104901c4900702c20700d8074001600010500000c222041070701c25074001480200305400c000a80d9401080541581200b804107aa220304104800302d205442c00d008036841c1090fa08000d0303081740c4c01c3d107054400081132401103480b41000c200d0550006081d07269502d68203441e0344000b03031020720540900288c2c06004515441142809000c070001d942c40700340a0b5080081c80450381c0c0c0c0c0019002c00761072011150400c1900d4040034000140940031702d26207018404d840e00401400007500c1d83c2e02c00d03481114030640c654034007801d0015141c04004000d400c030550214003411a030301c0042e0041249006003c044103c1c484c0d840c1c600305149011301c003c4d0016100308052105680c8401d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 825728174 1250 825726924 825726971
    0x50a0b01020c09090c13020c0609010b0a120209361f0603080912071e050f04091106090d05010f02030f0f070503071b02120c030607091208030705071203 67
    0x580d5400240341c00101c0c19103d9480c5c500c1107100e48810b09a09852158540c140d611050148044032168546408402c1c001c00c1c100c5074a9115210715400000d00075601030f030282c4581d501408541250316509585205440301c0c0701500b6190855031240070304115000020102021840d0003032400203907007143d0000ca401582c12902010342408030134000301e08050215004d060003921001c1400750301803003179401c0449941000369009000b9400c18011200d146d07000701901c0b001c0703030b800342c495245c8000c100480302c01c000020440c401208404200c4d01d40b02c806000070a038098040940015070303543e12070850301205015041582c1c044280455102004020395108194480b04609401c0922000e0024000180325200f04221949425440025039020010301039019200484080002c10b0642d26044d040c2e10f100e01902c0b4620005212520492225049999000f480c040761581078480701ca40e075000034881401e21008102e5900014a0443e40c0084c0880b295400200c2000e6683c41e1401c801d100e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 825729424 1250 825728174 825728179
    0x201801030e0a081b030c0a0b04031e0e010309080409060b18040e151e07080a050a060b07020d0203030906030405070f090c050a0f1e1805180c1b01050a0b01020c 70
    0x1105410001102c5208942400c44400ba6a030003280013a0141c5203140300d1b903d00c02403140225040603003000600b0604500491003510342486001a1007600d900c50b028500010000411782607807001c0769402540000c40c11070190701d011345456210310364903050f101158400c0311003840000320807070303902113040143c00d55610840d824081d480d180c04083e03944001480300d01450500010200d005011110b007000072815003041c1908440c5403000e00941610700c11105802c4d1641031400181d1003e107a0f00c507980584015843c02d0342043c1c40d58092201380200108120303050722080090300d1443c0c2d1250080c510641c41440104003182c201501c0c4c0503030f40746640c451800b090a00907001d00654002040c3e40d801041441c2895409030703542c00c100d4040103c6800c1d200c4100d4104105001036600c071190200c5080c1c5040440c00442e81c030014410403c926044460f20b451151000c6000c0e100f59500825015402d21920181c2c02d01c175a01d0f843c00c6580540b0600300c001d40e1542c00c04103d58040c4840050803008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 825730674 1250 825729424 825729433
    0x11011505060403140f01050c12070e09010b0c030d05010b09030706030204050d02060c010f090501020c0d090b120910110702040b090603071811040f06270504201801030e 74
    0x10440801c0140c0250300006020391011800754511520030000c074203812000d580240101e0810340b440c0c00c0b40e0360140b00d001c80c42500110005035110b0003034405441d80d00b00603004102c40d0307207070440da2661600b100c11049aa40410040752500500e1801aa40a0000441000d981d1203142080600e0086c0300e901c03030f005150040c04100496603680e500301407010340542e5101d9490580c07200150042111450043e005071900110b9400c0c84015030241c00803010b1001118210040340c90140c400c09403d00c142c421141c02001200990300700b07000c0f90340d048040401201c51482c10595290240c03010341402588c4140d000c06c5d22810341c60309024901d12241c058500c0c40700e034101131011070746034469801462400112a460364040d901c0790340c080108185260b401c030707880c5c6807102d032451010301c00d6200c0c034000510030340340034208101c1003420807100d0301084440b984020328110500006c1c12080ca00c01058414151110300c0706140f01e00242840141c00703400e8001c56003040009001c9501a040628842d4007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 825731924 1250 825730674 825730679
    0x90d02060915070e060f0d0f0b0d02130c090b0307030f050105060c0a0b07020c0a09090212010b060304120909060b0309010501080d0507021c06060b0d0b062b1407110115 74
    0x281d091030b6503002445494261000b03c0b0b0307000891124031424006942c4045c00082c402105110365203d1070100c2c0c0052070a00000004004011030000c1e16000a50302c03607040311110081c1043c070b60000c8a108080e0502c0d81c01e85649105121003034100f202d0410100752644400c1d0380c0c3c1312191154601412080740c0041c1081d111440c07460762000071100c002c1041d8a0f0030f0100e40b4607402001412132110008100e02140381d11082c03e08007038002d12104034007510340c17159847c0c02200180201e000c8144007070901030071941d0710344540344100d40c0d130460541030141c3e1800200f0840850b0080d03201505820090541e64204070f4041421514146c1c010f0b1302503000030100e00c4040d5401011292899011a0003000740c0904000d01c1c1340c84604e44400614a41c607000c0005440d07003846015100b12042c2d0081040b81c0054141888030600c80c0090610301c0c1c0b9070924840403a00d83c0052410000808250001660201030915501505c0c050b42c180000c150300c0701e17461452980034000d15032103000c0c031b100288041c0d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 825733174 1250 825731924 825731953
    0x31b011815020c10020a090e130308240303030c03061206091f0e0304090c08010914060904051e1e070f0515070804030f0b160903080c0f06090d020609 66
    0x44148010a490707540020303610b14400002c000072903060200040c2190354031220100030b01130702190b114141d4406103440c002180c0c000e8000f40d980100703816850300c4000340c0c1ca00c7d00302c2c0e01e0030b81041c50030654440c991040519548082000e140301c1c445c3c2003e040c0c4e8905040d010815001c040c090314140346e51000041000c0f210010682505a030350101110980c4115a40d2110107030030b10b8010807000e0322002c2400500e880e442d8101c2c2c6002603090700c40d0120360b600d9032440c00588900c4040103441030202400b2a202e400c009a010750710501410a80d07500002d540800902140421718644441e840790705800305054400e088900b400000b5002003504600d0300c01a400000b10703a1240b46c0c030a54144007000c42c00c480c0401240e0143e940030719902d94079600d0b4a4010880340c55240c0c19a601141f240001e40d5a0300c1c40c0700c41c000c0e241d0058032501c00c0f10780f42d603903045c0055120005154031401586030700052070000300009070182d40848040c00f000b104404000380f500200410740095640700c14002e00509 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 825734424 1250 825733174 825733193
    0xd050c06091813111002030a08190905060402030d0309260708041d15030c19050d03030b0312040302010c0b1021060c0206011a0912031b0118 62
    0x8210966040d61a1211040090458106201e64100050074041000400488102c1020b11184500444440d010f1010240460b680c081c102d0744015074010001070803001d00540d01641e00c00603008a900001c00504000030981d00c0c25001214142d0180041c03004519042c0844641007110380740070481c01010380c8901c8440d1081c0610140a02a100180e8000622004c100c0e5405900844c030aa038996480c000840d58028140840780805029400301d02c4c030300c4040c0e0b50104861402070003020201040303401c001070041e600302c0400c8503404104c4c001a40792903401120410034040d440c00107424140506050030b00c54441c2542090000c104000d00060303811201003846141c002e5542c099565520404002801440c0c000d203060401000c10140300c111038404400d0380c5489180300740403420003080f040e640d880c400e000c2c1c212245121800000c60a0721400a44001600181400324801001c07a4841c11680f00c400004d0104102c41d01c0c17103c881000f4058214071800c1448840d09900454075411183d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 825735674 1250 825734424 825734443
    0x3060603021e0309030f0a090603060503060f013c050a0e0402240d02030a091101110c12010906051e010b13050616050f0d0f020718020c0a0c0303031a0d05 68
    0x42d5107021001c074140304010401d49440400790b0a00c55900e02c00c0c000c0192000c440d510070000000c0c1003d101080700c1c200401d0b00c0740a512004101c07aa90b0f400c241d00465650f07450404991008080c41e0010740c070a0031441c1c0f500000303c1e1442c5101e41e40d4107120a1180c098025040070001408100c103000068442c10300d040900120301504242c01642601d15400e248902c4d124074007800d00200a110000707907107901090b50385100d05181c4030881c1c81d26005448918085108044603009814070300d61034105240d410520440500c0002a200744a646900450b60305446580301048004000000440701850b0340e03015100e038030950750500c01d00124001150403180642c0b40141300c00705001900104401800b00004c0d070100a5910505041e094103654180e100c44c2140010880c060b80c2c0030141c008150181070f00c803081000c08a00070300031a4803001c0d51011703e5482e094400d904504c008228440d0080c0050740c030903540482c0c4040c007800700104484940a04920075030003130400e86e00254002170300404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 825736924 1250 825735674 825735727
    0x2180f0f1005130e01090c080601022a0d08030106080907081f09060e0d08240d0318080604051204081e010b040c02010902041508033405010209010306060302 69
    0x1044007540c00d04840d14080d8045034000682c46403070104440900e03400c00c034140e40c48210100301d01b1409440c101d8240c2c41c00c2c3d6002d030151f0020503441c05081c0c020055400306101d4540c40009407600320000c9204180040c0007694480d07c04001405001d41c400754058109100380000d10351103007010400d585551044205684810700c0e0400c040480e85036402a607480358000380d0030000c0034001e02c50300780c4820500c5155000110070300006605422440c5c0e44480030080424070101800c203120910072141003c46d000e50074002080131042c40c581c0080d05240140180380068200f6044ca46000351614000e010307004030744da500b4001882500c2001900c45075401c04408801c41558403d09483e004003113044040e134000b401c14108a42141d015007044101610a07901003140c64066001040d0403003650140c4003994000f000846640c0500640f210030780c00c1d000710400c20300312880c003540e6040d0060280450305030750041100946982c02d0300c9984010101030070107525040a175240d07030f0720f82d400310f482c210b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 825738174 1250 825736924 825736939
    0x8060106030e0a0611090103050615041406160c030c06090b0306090a09060c0f0e0a050a060c032703060f0b060a031d060c041e0e0c09190902180f0f 65
    0xc0d00c142d4100203054181e500101d007041109000801c10100b80d005880c1a03010030b04003008076119080450411440000b440320712030a00d030034181c1044905034030b15170b62036000c0d0041c8911030201800364001030400348a10201708034107143d8078005207000d9056008809004043c0700401116060800b101e41c08070702218802000d50f9842950001000c82030340142c003561811940c126219005070402403107407119250352418600c08005c00040981600030345402c000740070380801c4a5401590003540c01407280c00c1070300c200311904000c0e0820b2010b907540030a9903a485001082030144602c501e41c521803852000b44005a031000114907140704190744141090ba07148221540d0848124140d00d0038070325a0706403155070a21044a0310141c201c3c0c003910421208483e0b4102c0d01c1c0001d4100e40b0100c41c690700c41180d60380e44100300f03101550002460140c01c1000404000c221003441515003002d48462400161034828600c4800041292036884501900d610710070391041d0b654107412a40300310821138440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 825739424 1250 825738174 825738191
    0x80a0e0d08190c1101061a0f0a090b030411090f2502011116020312040f05012607110c030f10050c090307030302010c1d0117070905060a020106030c0b03010806010603 73
    0x196080d02e03204910460b6078a407815039003110742d1210034060202c40210082c0402c40e03c82c0c070a0002c101d00e00a0701241d0741400c1201c0c201c542c2042d009868407040034204a0500385c2d484424410b42c0d4001c842c201c0c1c006940f1403440c2c52a181103a10700350009601d50300c0a5039480c2020070031080b0f20000f5a039440c0f0344610440105614030135006448558000780001e81c95010100f03080d00c42e03100041080f4403038007507800b0042d0094155810385045402c0c88c01e00079440340c034040042d60160b000f0b07078262001041e6014406500b0039060180340c002c40050341c8818100a41522060500307194080c0244240c100c5181c401001c40300140c0c4900000c810980001c40303455804150009206040d180e40d00b42c041c1010000905406501280508541c0d4540b480d546400306265100b0007141c40c1c045011402074503004402820600b0140d80c4900d003414010b06036602c600002d460740d000242030300c0050b91214000c0c0200911901644020701e40000503500b1355051541e02901c80074140210b504050b40c942380d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 825740674 1250 825739424 825739441
    0xe040803060108090c060705010b130221041505070f1e050901120902040c0c0b28180c090f1a0603130515010905010320011b0f02180106080a0e0d08 65
    0xb440c565044c0241b82c0399540c00c141c9000d074080c0025508407071003004c5044a0074403200c0680206c1d2460216020318400c28401001c041d100d42e100070b0401e885103e0f1000c1481040d0149104c1c0500504843e00d44440d0050f05030170040111500c8003100762298201c2105495041e00401600d5a00400f420500c403030b88501d8240c50010300e000b40f0040c1d0b01030704242c00d0b9940756422184401c451401148840700a03500e0580c0e0b80440a40f900700c00010392110030b46003101d0019544520320049c04003c01c200d07480b5844d102d23140302c0034180e080080c40965038a490042080035200f0202004017030021005501c1c1e6a0700081e0585c0402044912880c3e03800000d001000303410b0142184105450f5459201961652410030042109001c216000200104402c44a11070900a0301c402c841c140d41c2c0c6150400c03540e810304070030f05580104030b0341e841c1401403480050f0307510002c2004402d603d0307a05200641c9800c0d402003045030040d1550a0309460a41d1010880101140d90b0704503420720704044115481d0b8101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 825741924 1250 825740674 825740683
    0x406050706110a09050907090303020601050904020607050d031d010e100b03100203010618060e091b13090c090e0f0619090203070c05070b0f041820130e04080306010809 74
    0xd010034240b00280e54014650403144900a9460650ba01242d66403818001c2e40da02c4036501000d80903034041c900400c07240c0380552005a20600c00b800d56401c20825a451700d1a1104d090303e040007082d207410000210007540c0c0c0d0101003808a201c024004c806266480c06d80740c50110200c1d030142030f11407040a80a490030059034030444401102155650b9446000420200710105840102d9082c101e0009245202c0e04040c5030a14005144a45640303a01600d00d03210b0f01c07100030b1420b109400b44070b400031041807a4081801484071000206600703e004c80003c00040c0d0316000403020351221800e0040c0d0244c5d19508a91000050342c40c54002910080c1000c2c482c01c00380c0c8841d08040c000820003102e258494159458a07100740c040b50642511004814035601501c010240f41c00c2003488100308045420b0b14052000398100b00c00565020b545200300d8045451011003507101c18000f0f58801d20076202e800407002802c000041c3c01d4141000e6075444c901e4031014105a04104501b00482c40480f018032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 825743174 1250 825741924 825741941
    0x30a031706010903140d031d1504140a051509012c0a0b15030c09130b0a06150519090b040302040b28060215160804050c04021308060a110406050706 65
    0x200480c1d411003240c20310b1703035550020080450009041c1035500344540321507a00703820600d8815016041d42d07100003010404c03100006005035a03010703107048600100c0c5000c6c0501400e00e4060409480042d001c281074440e900e0010b007110006030b00d0700800c0041601071280d402c00f11480c0c1e61240d812174078100c4450740780080303880020300440010701c00d10440088021804c059004180c06460202c0c0340807041280e0990202c484c40b04410060b4540c034001030055555a9201129800001c1e00d1615070340c80d4424550002c141d040803e40003d200c81c8200801c1800783c00c442c04c14a80800c3c903030b0416030000300c1070141e480001e000b640c4030312a603203187d030b43c3c0c0e01542e40b842d140071b141c0d69115442074106011030029204240150082c0140c1d2040f9103500c401d100d01c2240481074404072085010011541548000c01c1030321907020f491802449a80e42d0b0000700f030740000140c4178400160030001424140f440181810158500e00489501c0303100351241079400300c40b05800c20319215943c0e800c0032805002c092 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 825744424 1250 825743174 825743183
    0x60a03090b161b02090c160804030303050906011a1c0b03010f06060e030c06040e090f0a05070303090506030f18030708190f0c0f120e040e010515030a031706010903 72
    0x10400c100c4800c2441d486500c80444a030f5401c10002540320a00c3c004800c0104043c0d04500d06200007070700003101c04018a0000e90b00d9010000014098a545901d034010750400ca002a44880900c64900c50801085001d0000f1807201c0c07205d855880c0e1b808581d03102e07a60101c0d0b007a0740c00b20402c500c5502039a02a04006002030000d104000071011020010f03e00350041001003240c082e100c400a04001401107011540545061310385810020b00b00e0542d40f0003011a030031441070348c40d0768034022000e0000c40481d41c0301d20003d0450a08600d0081e0000050350030450040d90144100b00203003c181c00380c640c03c1907a14407440030400314120540d00b188a080c0d009070120740700207450344040c21041040c1c040100303103a4800110703400c52041146c0d200ea0380480903002902503000032011850300b1010141c0360b201c50920519041c041b902040c251040004154000e035543c1080241c601003240c0c0411109034214007500ba611036039a40600703803800c94802d02c0d404480070000903001b40d0003201207034083c5410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 825745674 1250 825744424 825744443
    0x10e060a0219230d080903040e150a03050d03020d06120506040b0601260912270415090b0a050102010209130b0d050105101716030b060409060510031b050a05060a0309 73
    0x1151240b0b40c4d01c002c030092410000380104006040e100c0c010003920301303885140c04109041e031942d0f010041c900d42c0c140c8031543e0110012000100081e8200310b8a0740240e10b0703480158403040d00711001e80444020740d02ca0034404d0074001c1c150340007a20105806a00550082880d1180d84821004840c0704a4410846106203207a020a490000f03440181074400c1d070020081b58045e4081c0505000d40740108581c00c9800c41120f400e001510f403442c0c0458204d144060f100103112a4003520a6840302999404007542da5503441c078402290500c0344e8505c0c06004207000070f5191014034030100d00c140c5a003260b000e007541d2f901c01a600303440e501c08804d01806600b20300240410300300300c0c0070034071318040502c542124001305180c01d000320180460f04078007c50784040f804083c2461912151001c420041c03240e580107540d1401c0100160301441414020003012490b07600103415031030044a4003817110a84c890725030321100e08001c1941e5004100007682c0064079081e454070b0100034107034040d2821400040040a8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 825746924 1250 825745674 825745733
    0x6050f0d09020406090f0f062601020c030d060510020111090409050102120408040e150a15051303050d02100209062a03070f1a09120306060c030414010e060a0219 71
    0x250304418120700302a6070801c10701780300300001f50494900d4842c08074030701d5600288203a10301e030071443c543d0243c503207000262070f04448140a03411507124416090b0f10755070ba20300600103401c0c000b000204400c0f45000803c620313030f10049036000c207001c1c0c41c800602c0340d42c8424802c1c0402c8000e4054074103000a00340540040e0901d880c1c840440d8000d8010b6111003c00d8000103466a1000c4520034681c2c0700c090640d08a8904005058a4030b00c4041001402c0c031908100001e4002c070584809001140100c016003600804840700a04052880c00351050383e03030041c084588ac07a41c800d070407115071200e141000c4a80140b05404130315901503d01c21101c00f400f01145000a2007004501160043d02c901c00111030a81c2c0d000300074980541c2a901644554004c41810310520b00c440c2c010758205400070049800c0c03603500041c035882c45d400b030342040b0000e22201d088c01c0a25600445c2070403046908450607424a480c00200969401c00048030300a09071030700c5003090038058450b800d100242d400500f0400320070f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 825748174 1250 825746924 825746939
    0x3030c03070b01240806041512060609050718050f2103030402090703050712052208090f010215070507030302070210020606010e01020c0f0d020301110c060103120906050f0d09020406 80
    0x5400b40308000d1100c09100b448210788010350784180c00c10310300e034031071720015201c09081c480140182840e40d01041100c00c004503603210030b00404910503201c1e4402255942c105070000060b03480141c03800050000d40c03031801c50001c104140550583d0000c6e503d1025201c080c4001070b00300b005154021069440b524000b00c440710000c002548118025106240071b511105011030485000b1101d039400900c4a40075103419502c01d804c8983c0011a02c0840074144880e00c0080d02401c180030800c8600340400107440d0b026081041e20104421001d0001c1c0c0312088002c4040b00402c100105100100315002880404140c02036060310102c0707802030084840081002f00284d80d41206407045408211901c004003215840000c6060203040003600c015080da42c0b10084c1711a15640480881e81552101c4418002c00d0b0300c030024140c071310802001448035514504180941c007a041c030420b0104410460706002c11600001120440b20241590f00e0360785035040e500c94014680b4050095029052050000303048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 825749424 1250 825748174 825748193
    0x42a030303180317060310020a0302070507150f111c0e0414160309081c05061030150b0301060909060e06040203060d06090b041518020f03030c0307 65
    0x8a00c2600c0801450300490090305030364121800c010005805690001d9051407040c11160f0095400341c129104c11f00c40841c4001030780c10000304640026804a509418003c08000040c028100400305601011a01c030b002003c200e03122565100780021186200c0300c41a00700420007038050201d4a48000388c100c1403000746a6209048441d1085042001820030260301c0d10482c0d019074100500190401c030f103e041907010304410031003a5000c240038070401d9a02c0881442040382041d1040c40041d1515003075003004041c80001400804102480440c0c03680c40f16044104a1004800c0604003119403105800d10f0260404042c0c6c4080b020461074000b074043c54010285068134450b03103032144015150264034040b80c055102d0300c3c451004a1300031a8507810a540150f03080103000e040a240e80384a5281d8000380d60b4143c038100d510044210030001402013103d5030000c0408003140a0184000c01c00c00300d29880b441d040064820440b0b4105942c056404000b110705a440311000d0b6900ea1450b070030000c840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 825750674 1250 825749424 825749429
    0x90d0318050f1c0807022a0909070e0906070801031b03050f010b040608011109042a121b0815280302030d020109030203071103010f0218040f060f03020603042a 70
    0x40f42d0200d0b480029043c0204a41849160960b000781650300301e012402c2003014544121540803c180007043d039680d11240e44581c42a0500c0c0010b017061481c0200110100d18020011407480e003120062100c2c04d0740c0080381e40d04480e00300f107120764012203001050340a07001650004100380b140100d44030b10800306401c1252880e0040360100092540c42c05a2030a032440c1118141d05c0380c400f04161200e5203019030005903400c62240401d07000c00c90001c00c1d10360601e01d10160354041108540880340000480c0074440301ca0f080311165001c05400f81101420012000e8031498011010702c0f82c2503181c1d1103141c004440701c2c00028400103458134054001c030310480d45000a074040d0060980f00c03102d03e80140600007506038158011031404030a03440d40451102c2000c1c66030303490354840d07665404d08445400980015080c0d12184000340340f070101044211000038289040403800d0850410032400c801c01404101d94069852507500d81d51440c01074106101c0502c01905040505c0c207007499030411501e0f1905 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 825751924 1250 825750674 825750703
    0x4111b06060a06020a0b09030c0706020a0c0609030b061c020303030106030c140711010503090709141e0124030b042a020303010b04060c110901181103090d0318050f 72
    0x4403601c5141c00e00c91050064054070016a120101282c00542003e10039a0f01c2410001a07a0801680031825428240690311050050307100d1400e04003407200e06500d000041100c0e00748090424519901d00c00440401002680701d1950003108106800d00d8804608020b540102075903a01d41c0c407160007800408016084034001030b40014885c00c207084030070480d00c9058000368160102100d4200440d01640002e151038518024444000303048000d9004208004041521407101407900700c1080c0d0310382c0c0b52156124846166000100060003030086401c1c032000b802d451f0004e6809007a070042d009002c80c40750f4103812500d03180701c070116085001c200403030040c001081c2c5810160902000ca030340340800c0c060801c0c032080411040102034000d000290301b0714440c242030b1800c184111b001491030b10090784002542e00c0f200c035400c140d19186215040b02c2000da83d00c01070460903c0101e1070391741c5080e5180e0000341940e90070000f041c038030410829203c040c0d020b070444032003071501c81328030b610713030000180085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 825753174 1250 825751924 825751933
    0xd11010e0d1401240306110409050403050406030506030c0109090f11030103052107120e011413080c0102030c0c0d020616120f030b01171b0708091c0206041404111b 72
    0xd02803000c035446007408910901c44003420317415038a80074000d102200e44410310620410000030824502d0094900c154003944483e900c031442e004002e810360728020300380b0307110b078011042c449866070704001d01e9415669041f00002e2104003024085004101810030b03003019030408030000080210005211141e54030309a410058604030410003203050040d40c100804190a003120580c2c52032280d0310740131070140c0c149404556026181010303c0a5817081841001e0003d2824042c800c00c1410041c10a50307170380030710040d031800106034030036030716480c24103d524410001a4002415599003906840e048403000340303d01c00301d10241c80e01a44101c80b1031705003408145600c4a0300b04a9019118540c076032501038442e0151784206411100101800030f00047c002c01c0ca22615160704201c0c60050301400f8443c4046a039070307500c05802c1005074150307000b04503603030300400d100e041c016182d0b5410b5070200c4a100c5440c42e400300c07031100010064400030807450001e00c8041034503040710070709140384c9000e001c2c00c0f030644 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 825754424 1250 825753174 825753191
    0x5070e120f1912030207020316081b0306090d0e0a0b030708040b06090c030103030c1a100906300302030c030a03141510050a0c050d0306170303060d11010e0d1401 71
    0x80c0d4101c100b41d800a00315100c00c89101101074000d800800000c0d100070f0a030745107901c4c1c40078081005040c0d5044441540e0190072007883d52001c2c50041800c0990480c011b110900e4a03a026036511520f81c9061070810160034900d489540781c29012501401c001c0203215183d1404400040425508840c280d0300c48148030003281982c24aa1b45803800344a1824006285a08544042c1d0754000013020481b501c0100c214440008400b1006c1d03c1d018012040c4210651454001c4503429510700c2e80207903404842c210320401040f4280d5151039079546036940c40c00146040342c00e00340e086018440c840c580900000480c440c245030b265200101d508903c031090382c0c5507100c100070105c2c070450341c0c050103820418100c4034100c2580a4030140c013a1008034940115400c0496990500f0407800414643c0404d40b00c50040c05101071281c5c00c0d05016074400011801e602e854000035030300c001c586102605080d0b80582c508616446140e621b42c3c20320024103220f020040720302d01901d18111800100503554a480b080d17 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 825755674 1250 825754424 825754453
    0x1e0a0804032f030d08130f051c1106180307062412020108040303021c0e030904061e03231b0f0a05010c170403050d03090201030b121005070e120f 64
    0x200b00090010710038602560720070307940b425010304010015020a40940d00080794034075043c01c4140703d035000d030010010720038100e241c11560b254600c0c00e000c3e03007840400a1640000d103150b804100050455042c82c2e044450a06600c900710000c0e01140c18220b100003001202c1c525526003c62072032000862035542c1c03030310300003234002c10130001e000800c0700000c01c0100b44070341c02400c0030300510250640555030791044081200d0940c1d5942c13103d0b400228401313000745464403513000100500c01740d01e80ca898810407954000091400002e0074480075001a9903d13152410040510000031070807a00c0fa600e100c09240c803400d603e4107900344903294103000c0d1041e40c1400420a4201e80060312400f084845558994441d4000c41c0604001c000b0140000800304404020300c03081c3d4440d548000504401a00004041e14807800c5082d0181d024003c0090710580c00050f000c11802494400164540341e02c0c1080328101c402a2845500c40310384690900ea002020400380b41111541003110841000d01c000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 825756924 1250 825755674 825755753
    0x6070201140f0403390b0a050901060f030b071205010311030618070902452d030a080a050a090f081908090a090b030615031e0a080403 59
    0x40060014514038074190481c0079040c01c210308403005d10032001400c00074103405541544e2210041d150560408280001c45801d4490603801065410091003000d0034102c810041030003521004061510030400a00c403684240e03a40e50a5826190003070102e56036a04040c111008e0b07010003640700e80901e8012071009406038900121002904015080c09441c1402c014020340100540008101d07402c042609801c03aa121160f010f00700e00910113005016071100150b84a0780141003c0c000c50985400e004460b03141c4d9034000c41c03a841051f001c511a0340001c00b21f4140b0703402c40c400500d10303e004140c64150701d4001340030f48450324490f510803e41c5a034981030302103596200e200380245a00400040051a144100c0312503815008200c114584550480411815000c981c008815031740c1d030310404042e81c5001d2000f590400d4403090b0b071800c06200200007a85401e005500c0d00601c000905a052085206110401000343c001072440c0d100d55903030900d610207100700c6005407100300c40301c01e582c0c3c48400e000c01d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 825758174 1250 825756924 825756931
    0x10512071a130806070c150203010b030c07150e06070314010b0702210d17060105031e070c02190305060609010b07030f0e130c1805060708180306070201140f 69
    0x14041414032640c1c9441c6041d60014407500005440c2e4200400c104808202c0c19000302038640c1e44070301c8001d00b414880c040c4003082c42041c01040c010401004007040340740030340303800440150485649030800d140600f001e0b007140001c44075071400c182c2842c0d2601408540300303102d02c041d901c040c070103500b500281e840c11450900a00350416024030020025003801c1032501e445490480d076008403540d801c81001c0c0f07403101c168050301c00194000d10500003020400309540e042002030820701c1c150701340340c0311743c009e0043e0300c3c14124a68001a8001100c483c852040c0561b0650080c000e00703904820400c450141d800e0324041641d6510400000c074141c0e050002091b4100c40006980074100106950308643c3c1030380746c103c00b034204040c96420246907070b145003160300021100c90b00000c03580004100601a000c000140c1c403208041c0000c02c1000d615884210394880e54804e402ca9a59102c1a00c43d4100d104100c0340203400d4031071202013000554055110445040c0300c0400c00d58541d9030a80b001001e2042107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 825759424 1250 825758174 825758189
    0x7030f080304050102040e01080703020109090c05031501090f24081312090b040b03250f0302030a090b040c081011041202032130041b1a0301051207 65
    0x6046000c5060000038581092055001600e403580d6004000c440c03940a0300f2801032038002c240204115a088002100101962001841144038070140074000b40401000c03030342d410f8026800241181e1240703803840702400307102480c42d03003050300c901c18040401c8400c0e030b8100284214540e0043d20b50f01504c103103803040381c0840302000000240d07a1003000d501c1104980c0414420b5004022030410160030107800a40a4001526100e140c4002e0120000e00e2020348010703903035408624009141c1c1d00c21640e0f007480392903082c0903a0f84d4039240c1d443d000a04c0340c003502030040d1071014240810001190120411980508101d42d02043c00d01d20500c225102058151014041084100078031241c44075091180c0d40010286da001680c00c600d2210455a80704107410311800c0001c0440d5241c0d06005d4004842d2000036074075008101884070024105405480901360104400b910010b20f1074152020000e00300c0e2031b01202100110b0018820207400038000d0700e20881450b102c404010400290b00707402c98906c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 825760674 1250 825759424 825759443
    0x102070b0313080d09050714031e0d0518090106181e15030b0904030302130807030203120f0705011a090a020316140c0a0507060f050304030503061512070905120703 72
    0x1070340e83d16200340c0c8070607240d444140d150000403000c11001e0140c540101480b003400c0c003064050400701414203805800001000800000d000340d42c20380020201e01900704c0c0d00306aa60f540d02c18403854503e031400c1403001e501080b40400403405c4c99024820880014000502030011501c90f40c0443c80704980f035060301d5811107858410084440e80d5284401c105090307090010720300c1d4504002c00c08085003100c00f42d01103030300058111400c075030850000c4018a00040580f07802411030b80000d4450b522100e02124809021806407032002c03041c4111030586074010005c01c00301c1840190003445900744074a940c07082d80880009000101e50b40200c80c403400c180ca01a0140706c4400d08192404451201d040302e65440c1800900c000e220200701200c1d0041c01000244911482c1c00350041840c18203800c0e10080202c01c0c401d03c00017036048015240c00520460346110003410041100c201c40c010000740c07807111014034041c0460349402c00004410780c0c005456003221042503420380341c2d98541c940300003400d480c0c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 825761924 1250 825760674 825760711
    0x91e110313022e2003120609071e02100f0603030f140418150b09031e0a0b16030509010c0c230a12030b0306060d020f010311030a0b0102070b03 63
    0x20075004400c0c1c1140640c20507120f4403111458080c00640781e400800200740c500c40103c56107607a008800b4112148030004515141c0d030145c0428180300080d02d582c0c0941c40d5000803c6031030740611486041c1e01c01d1118600c41101c80150000d69034036002100405c2107140c0195103494101c10700403101503e070152141b00442d000180304403400c0d0600100748400c800280408101d4900303c0c0396420b03e0940c9000702092500441c0c0307030360400822940c003e00c0203c0c420008450300d030703c0100310802d4402440d54420282d84000d031042d4240700e030385c1e0401003103c6032890402c69403104040d0340c800030035000d9508200c950344408045080300d031081b00c840003140401c60510001800b200c001196000c0043c9181c80c5020340c81c140341e00e001220082103a001100404440c11650301d1b105145650300b04400074092814140082900c3d00000040a0b000c1c0c1c044d1444038441d64001d41003004030501c42c8482e0340da02d1824100b0389004180960409005000c2e118000640ca486001a00c0c050303503005906400028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 825763174 1250 825761924 825761929
    0x5040c08040b150a0909031101050f01030f06090b0403080103110a051513080304030f032601030b090102070c030c260303011413020a02031309021905090a091e11031302 74
    0xc801841e01908142404441c0c149490b80004100201000c80e40031440304810725020f42101c44404010303052782c1c0f41c0700411a411404140d80c0e03045a81002c8010810706007400c00101408014078003809140403841403104040c0d1022030396040301d000b2841c030340a100b0242d0804c004001d503442030356404a14114529040d445050041112592324844081056034920142e800c542040d8021b8840c01d000d8182441416000f482d00694240f61200d501800c1250f801c907100c4924060102400b000d0007500000c0c542d1000f50304031000c640d084014075544940c2c91170100c0202d070044c0600c0010400c00c0b00044013121445031a40945c56100c005035041d6800c0000218a00c8002e0701c51984c06509c800750b174030703501e072191004280341203559010b1a41c90302412503548601c41241e101500302c3e8410040030020030003040400b105a10749252107952030303a0072030000c0c3c16030300190041a001844c0104581070010a00802c2100408080c03050158405030241070000e400110f40c1400000c840c00300705d00051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 825764424 1250 825763174 825763193
    0x50612070509011107090e01050708010b0f131806030c08030a080a09020303091302090406050f2d040e010b09132607170306032e020c0f0d081005040c0804 68
    0x20308041c0741003030445041264071803400720325500c006051b42c1d9901d40c2641c070750070070300410303501507a00e052884030313545400d811800e207108041e01038280c5c50f00030070408410215600c881c0c00806118903c950511480703400ba5004181c03070f100480f040e40c4032803400981a00080151804000580c540c81c501c0d540d41c608a00c06080013960407a40b6010401000c2c46540d611400c001c20020320380001170700d50000c0002d020071500c0c1904041d00c00d040c8000c0700369290791883c16082c142100c80c01012030071680f0461109031101c0d2007070900d500038200403101020b01c0c4154031443c0c0030141120100d0064a6041450f01c613490a10800b90141c0e82e000d1004034440d107032410080b8400b440501262420050361116105080d920385070443c109030000501504e854200484c952100118020300d03040080320120f101c1c2103414400c145c0b00c0c0f68000c60341d40d240020503c01d0b8071306140607106440d9000c04110000b49041c204942c802400008041e011550381440d2040c6482d0030010f4a0b20711043c0c032203440b6020301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 825765674 1250 825764424 825764437
    0xf0b01051c0b030102071202160509150a0504111806070203031204080f03040c03030e0a060e040f0209030f01050f01141c08070210020f07081203010302040c0c2a0506120705 76
    0x6070780c0714100c240741900d091006103100c0c0d0060b10340d607680300c4890600a0074000019814154115030750400c2c45555601a681c6130060110340d0080c200e0b120b15008110302160301d40c4100e91040c030340043c044c41b1900d20030081c10b42c2c1c0206c5003e214a985054100322450145c0b20010307405620a0102030100c8801a001d030360002d025440c7d1a040640b007015402e25681300309c41c100e4403184006420020160041c2d0000b03402c0e5070031980d81311600e0412a0050600c034034035220030720030742c1c031515a00404103460741101c0744043c1c040d0503511651581c0120300e003c1c010681d0020f40d012006030002541180f104c0000403c04801804519a06046a241c02c41d840c43c1300340a880e002820404d01e00182d6070002e00001c603080c190007900214040d0030310f50b81442c8451740103032902e07000040c1c812414401001105d0540b0380c110b030000340c8424280c1c82203851010b1070000a2105407144001e003a4807002c444c00e5284a064507900c99542a00c8800380551030040c00c0c040195104014080b6040501030380240c80f6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 825766924 1250 825765674 825765727
    0x120e1917040314030403060b03061608180f06010e310809090f0103121701051c050f0105061329040e0a08030f060103050618070212030106120f0b0105 66
    0x42070748075140c1c5076070043c84142e40c0c012640000f400b00200300090107192464207003103000d42000d1500708800e1016100d0b80c0c0054003004542400584003825848926107818801d03421284142d00d2140400d40c0d611080c0034003c00303c00050002801c490501300c410141003c0d003805140b460145150108051b03010a07805c94142100f8030803010551141108548229801880264030394554201880da0a032030050072010890b8940200420b047c00b140580d04448007030b6007000032007001000040014600300b000030315a00510041d0b1040d040f05401207401703031401b00e4004800e0540700501d041154007070018406045890386a812250820300070190b09105c2c041c1020130810040f00003103041c1464a002260200d0011051124511140100701e9001c0403e0a00f04400d040010000700c100d0754000842c50b0446900000501081c4244035a00c032000711008555100d503101c1401406041400040c040d4080c40d0441d810426229400f44201006040c0c4905107000403050021070b8084e240d01d070860 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 825768174 1250 825766924 825766927
    0xc031c0f02030904140f0c040f050105090f060703020a0506062b1a090d0e0301020a0c080d060e040f0201021b061b15072c09070c021906120e1917 64
    0x20011388032800340c00d0740312000541c8840c2d90729103144004020781c0090110303001c2c42da042c4004c0c4200103c0044141c240c2d402400c203103480382c820f000041c0044404403442900401c01181c81c03410180c001680400191040c801d68030141c2d01c3c402408100d80300c190f00411034900d54900c451000340d02049002e4164018682c503804100b40b10912000f80009030752400d800d903c05254400c015920401c00e0405030300480080d46400f280c40c6009244d40f0350b0000140404000180000410020343e105000905484600084518160030b1000c4c1501740c4e42170a03405805510f00a0503070461003a410010343c60700601c65810a0307083c504480604401a0100300244158440a40c20b0701d07050106034810780300da81d01d140305003032810b82414165803034500c2122101501502c071681561045080359000c0401c0c40d00050300c80007400011541c568590710350000c480c00380703004034000e80d11082c0d0840c151440d01041c460400303001d00180d500c10444058060300403201c003001c0001440c0050025505106181c6075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 825769424 1250 825768174 825768187
    0x9050f060d140907080a390b09010806060909010311060d150305011d10110d0c17090d050d0207300f030c0806150c0f0f0c031c0f0203 59
    0x2182260b25420741050003814180c10028006002c200d500f0241c0b10400103404010f11540d510b03008030343c103692511040c281c242c444020070f090341d10681007801980c41d04584e030180e43d04030416a80e03119421090014080c0000512241000000c5403850309001d81100f0890b0302c3c41d140d54428658103072004d44c1c00f820412031500d60380306c10301030070410242d110f06202c0402d00d0b5140c09804c585612101c070317401702d100403000440c0550200c3e0460b102c609004010600d10500607030300640b0711071180003c41c414605940710b0b01450740017420900c1c441e4403002c0e007022a1214218035540703841c8070741d01c40c0018400700090505c200300c940103002c2e01c81c03060010044c7e21408140cd8403805040301c00301c4c0000c2d5840c592113081150b11104076100208542000c00241c240308200a080907401003119000d0f118000040811180ea2822600e15040700c2007a1814100c20142c2c0c1074803040c0d110883c464034840c1104040300c519000c9044e48070010111400500c070204880e0507185c001007604180c056000a0001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 825770674 1250 825769424 825769447
    0x2601020f040303080f100b0d02030601030f0609020a27122916050307050307030902031c0507060f140412020703050a0b01080d020606011209080d090602210709050f06 73
    0x191010b144241c43e110034070f2411550303401324500003c104440c58080140d0401491414208990120481c00300143c2e03656280001030300609a0000324008141c49d28400050321607440c1d01804c0c4d1000c1039540c09052900e03590800c000407101e01d083c02c090b5480340310200280c0d10007400d40070880384941560120032889aa402c5914080044002c840480c81400c01161568494082d408885982810703800d42c104800c0c01003030f500005041c43d0501d41d81300f09040039543c0c00c20080c500301c158202d009038942c0020100818603041480c00f200c05508140481070000000d0242034a40c0903c50301c42c42e0070750f82e581c64000218020303a00d2380b815030141d19400310101e48184010342069010340e8400540c1c4d45807a0341189042c2200b03000704d0840d042039040c02200d030b900c10f00240301c01041803c04190410142421030580c80b8000c9488540c601d05580c0c10308000c0b2035006841c100c03094030030700a200d00d42c0b07100d402d580c41300c1251048001120280140014a06810849841200602a40c1c18010008403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 825771924 1250 825770674 825770677
    0x4090b072a030c0311030705060c2205090406090c03080304121205090a060507090803041d01050121020a03020706180b07141801050f0a030504050c0a2601020f 70
    0x181000080c1012a4001e158034010390440700c1c1198644900e81c091116840041411400600c010100710940900c20100314081042d1441c0b00d0f080b506541e007900700b0f48010452a840468001c00400002c11005122191640010101c40d40640441e07241d40d00c9039103010080c01500343c210b880c608200d80c0400480c40440241d403260b0f04c56400c11240e450a42000750680030b00c40c400341041820001080071046001c503400e442650300040105903911350748400c0d6002403a07504494214480464001940710b1640d0704a2160003d8400110360f69032504c5c011201407010381800d14582074a01036400501c94543d005111181c03807031600504000c100c4c0d03101010f036025074590002d81d034030351803100c802d2143d502c0c0c01680010359070403c3c2421500b2489031024600401c5109401c920761707081d0115030f40e40207000725102c020440c40c80c0c6544411690001c1c0090400340c40550b001e109120403075100e801d202c0118002e80c0c2944201b940100e511240500c10b544200d40054040d54080c0198200a40350f0710 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 825773174 1250 825771924 825771931
    0x71205030418021c0204050d142523030a11040912110105240402071106070803190c050d090c030209130b060f0603180708070b03011e0803040504090204090b 69
    0x40016135100a00703d044009500f10700c09103e00303288104010400d81d03030b4400c40100c403140c2c030001030b42503103031240d803c681052141e00c2c2c040000d006182d01e698042030201c3e500000d403404410280d41610280031140b045030140c080d003e400d42d12030036004001c00d842c0040300c10440001000820114441e503500249410010001030104d42020b0070402d10800070b0058952109041c51094442c200c1403001c0e418691503080c80700e0081d940000c070300003031280c8800c0d851840c0001401d015651034031460801c50b00d52040300c03081e201d40240c000040680140b402207a140f42040d80d5040c0c106460f403400b4100400c0040c0c02110551800d240000060f1682e18180d4807800c202040c0000300510344c10b00500d03174600106505d209808a283c9d42d03140740d41d03550a4070380202400340301414001100d44d12614041031030b00024410b2003800400a4441c0d43c0301c000b1810390721110b1001c60040d0030907841d190048544d001c0d14200b07400c10300003840301e401c15921246180740010301c04a00014181c8840c00e40d07140a9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 825774424 1250 825773174 825773219
    0x70b0a030905010b120712080f0a080402012a140c040906020c0d08040b2206090b070f0f0206040605130611030a05060a150f0c0803070906020705040e0712050304 71
    0x500c0c1e0881406020701c50290841400d4079000c02c141c68079542c45840d042a030168082c5194480002020310894405407003031014180b01702550307043c0c00c40e80a040301c082124100c0c0012130034031414410581002d220880145031018000c0f0030340d0705944d6941080391803400ca03030301841070001c3d19445503900e003d4101d1050140400523070b40c500c50440b513424200c89284a205011201e41808009008004541d9204510111042052001c0320341c03001d88000590b400b1742168108208103003404240741e00c0780d002d660b40e42c2302c1c05030300b10000d1819510b40d00c00d001c0720300158002c00d0000740814104d804c09a4089401c94008010704d1555542c4402c031441c21040c9000b00901004104d100211803045039005942280c1d8008440d01e08000c624510203400320050401c01d000ca040d900743c0e4011490301d94815800240c1c65101c0c0740116004000042520840c0010302c100e180004180c00d040c1b007516404500600503040c21818200c552415188807507045402c2c0c4010400018800d80c056415400031074a0f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 825775674 1250 825774424 825774431
    0x20315040b0a060e010b0d060305151032041d0102071b0b0a0f09170a03120234082b0c090303030c2c01031401140111070b0a03 56
    0x74102000d1952006000075000c0e442c0c1002844500c1d50200d9060448080703409096550141c848940b0140405910050803032050803442245403120355074241c860700b40382c20070b04407450b80d0703c1100c1080d94001041000000102c8501003040d00309044039541828046c20200b040030070107a0074101d041d01124595181c0e580422135500b0401800c0e4000e413501c642050040a8038102004450309100d01c07010081800320348400c40716002c1c0500301120007400744801400141c4184960700782c0720800c60000300c0020f40d10040c05c400a1005200b6951054012000c0e100b041e5201107040141c101e0481e0115001d481c561100c0000545120003040c0d0080c1040308155103900c00b808490b50304032282c08101c5414208916400b0680c1d100b2040310484c0e801d4500482e00150551050780c3e902100d41c0c0180200c2100301a40318994490328180001c0300003a602003013901f01690364003009600a006248a00040280d180e01543c407600405000ea5103d206482801c0d680b860780351398950203800c08001003600d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 825776924 1250 825775674 825775681
    0x809041506030b13050f0609150a060e090a0501030b1303050d050c090102060106020a0b0f060111010603060b03070e0408162102011505030114070305090703020a0f1703040e0609040f020315 83
    0x8200000341454006000c2c140702601b4481d03191a2100c100a00007405455000000307415172100c40400250300030080c1c07881d0700458031504010700e002c0001c584c660040040d040480c2c1c1c0f120551140a040700d0f08841d0441c01070325002c00380a03810465240c2642000002e102e80000d0800030311401f80104900c0c040d0590300c0600c07000190428034140e21440540d007011144e400490408048117602040c1c41109078255030b40d0800503a056101c4105000f031079880d0800c040100f0200f0781c4140c0541008500320364030a580c03010b1340011000102c8004083c0f0405111707c8002c030203540c05424116204a48140c401a1a1291301d41e10b1036006884000603910342c0c84e40c09843d03003a0035aa01c081c10090700217200824201080e8550540c0161500c010180e45000154a040061100c000650b50040840041030351f141c1c11410f040c60140035411002510041c1c82c044500004200e804130384504001242035034800c000c0169000300100165001d03000300d80c4070401a0750038005c0c894007020255802c103542c01d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 825778174 1250 825776924 825776929
    0x314090402040e150307180b120312090c2d210703020f061216020309041e0c050a02060c070807020405010303050703020d2321010e01031103190809041506030b 70
    0x80c0c20504c440c1c0aa00040c0050080d483d124014104202c7d103100023090035804da4003c51140030340245402c4031340c0004a001100d02000305402801110450200c8449407403d90030070210642e6080c070111003e14011080c952a0018610307002c610318000c0c00c002c4111203011844184026100c4902c110742c0181130b003882149400780f148011584160b91345410034401141c5003490480c040c0c50203403c859220141c407481442003040343c540c01009001485403210340d85210400c6031034080a80c88031820302c0c03000e0800c0ca200b08240d0316104415801041603840360a80a03249030b10000701642c0c5004104402400340c4c0b210301505000f5072080da2003540d110003509009060444402d00f000401110302c103802c0c100c29111041049600601c0b080c0e541c0c40c5080800c100740090b012a5518002c0b4602c800014102d0904400c00d04072070240020385c1030481c0c1c1001f05078840500368624441c00e08034120354400f04408101810448501400024610240c9520b5010700e400c16400f0714006078842070280d0260 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 825779424 1250 825778174 825778201
    0xd200309030c0f0102070215031302190302040612050604080a050403061104140a14010f0203070212010501150201060807090e03090d240b150903031b1614030a0314090402040e 77
    0x20f42c80748021405c00382194001620b60409901307554120740003002181d1060451005111055401002030360030724a4041c4d1440c2440131b0b440142d104038078180c00028018500c1500c1c10240d0340c010054101607032640d95401482d0098001c4404000c000d000100c0000c1e0644640c00c44c61011100958440786840d048800e80300200034414000e1140b03860400180d0809840ba2007440c40909010724000c0d0707034040403841c50180038806540240e10751194040301c00103504c0141030700d002080b00140051040c0041c2d00380e400034030400026a020300000c0100d907209038801e03141c0c07600c0042034914201c600000100301118860042d80c804c021300300400380e0781c03801805d1310300e081080003000e000e184140c000103000115042c0b20704030410740c0010766451079581482214922403900515003038428030014030310343c2e409000c4240240e940c1c5a01021544840042507d581400018002c0028151301d550855400768084024050003505112071000d543d11400a4000303080343c3d8801203000d01c1c2031300d01c940c00c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 825780674 1250 825779424 825779443
    0xe07020601170102091e03010207060207140717060a110d0903080a0f0902060708071e210e030d211d010b0a030206033907020a09060b0d200309030c 65
    0x183e0b88100210044d9498044610030440400c1c94408038180201000c03034003a21402000608003440020782c8010011100c12060b18820b0700e10456000030344074092980540110460561594004070000d980c0c400e854104104205500d60301078204081d0240040a464010208502050225080158100c00391040d00c80c001c10100081c81401859000304009100d01c01c00a803070103400282c0c035414000000c01a9049014110720520b04040342e05064100200d03803814802030200e503046050304280b09441120b91002e000b00600214000d07030100790340c800c00d118102000b10401031084200c0318210321904140cbd101d072801d046d03400300c5a0076040d0308507658014014461a0481c100384050f89412080d40c3cad000f00e04200b075040d80d00211032000100c400c0003204410325a080003603009068511030244c41c8851090b10683c80c000c0c2c030f40d6120790680f442d03805050000c1009000d13a002c0c44d5180c0c0c00420003641190214141031132150003001456204646030b4005600015103269181420003074540c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 825781924 1250 825780674 825780719
    0x705011b080f1506040306020f07080703080411010306140d060e100c0e0603070906050c01180303021b01050105010f0309020a1505030f0a0c0e040915050f15040b0306040803040c0e07020601 83
    0x2980c3e12030800140450055010260006601040c0094071003980c000310f650083d041941e058075000d4501e00200200c604540032110b807248200c20303505550003405983c06461014800260070200e40080c0f260703071754000c00700703440d541c0e00c0b203000032161031051110f02e000401207007010507415001e80d00030b401c4024100710103008100c00c000300041309910515490960b407407882c01e241d507014035015403809040c54406450a50713200800309001c05425034014240c8042e44034042e200c101c124941d807801c03079600f44140d03070100d026080d840d40094469070201c0290b40c4020240c0350610307280c04601260340e804040309008107400100703200100d680c6c075160561041000005024180c0381d108001c0003c180860b2440c01035455502680c100038022080c000044c2c81c004040106241008403820540e00645070360819a03007042003c00c00b42454025400c030482d02400404441d2201d941d0521643d100a106642d110822500410f4007000b41ca044c9015921a6008203019414260300308000b4140004012 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 825783174 1250 825781924 825781951
    0x1120608010b121b2206080d0915021b0114370c020120030316120c09050f120a0501050411010e0f01110c03030703020a05010e06060a03080705011b080f 67
    0xa038135076000c0902c034482d29800c1c2c40d020103440710b2502c0d00d031224040e001800b0200c2d052000c0460100000a51015000070a40e00e05c2c0c02155500884181903400380540c000580000780c60b4103a0410030f0000c00c58094041c076010074110915480803945403c074221007135201c9040003080c054940c40716200c0903104040b203480c0141d410b590001806d034545041c0001d05001c0701c000762407440c103c00a900c0017003450321070a80e556482c00e12030750080700001e403a103a00400e1400c401d075403c800e014419400c8000003512210f03030850802e010805288140d0070030a0707100d0220703515000819000d01403404090310610010400e0300b82890240d0a41c81001c030f40904005400c046015030b40d4403a1501c5066060030f00b003444040901d002100c1c04e07c040100110740505c4001016810958000399804138107020307130001c020440c250003420b6241d075401c1d204681d100340d0030a004c0c400300e9101070050020910543c0009005550044486071000130340080a01182c40c1d003042040c440d403101c6051b07520160402014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 825784424 1250 825783174 825783193
    0x40807060c09081207060515090f0c130801050f2d10030501110304030e0d0b070309050a0c06050408011d0c011b05010507080a05070905100f0e03100e0f0109020f090601120608010b12 80
    0x12049ea000610710306a00da00e40f8003051000c820341c0300f1221482c2040f050000c8080c0c803908a503002e4182607920f20381091948000400c1c0c0c00b50300040b1101015004c1490303a0505952640010015014244901126241c2d2000001907401d00c204042c0d003c086d118192607141504024184000c4880d03800d020b51041c004038800100200c160f030707604c44558117000035110111300b82a403406141c0701c40286503455052011903480d4011000c2d00c00c840c080f400074001c05401d20804110070250070100307452a402500f02221542c0181d10900c0301c000140a64002030210740c6969095440a5507618041140c804c14080004e01300d014080d400038203810941754076898000071810220030340351040104150000b110040b64404d032a180c215110081c11200c3d8a020aa0007100621114102e1005c502c62425290208217040c05240396082c0c0007008810350400450500006c0e60000b1301c503a042180c060030084000c1c00134440ca8000d00014000003500d40c1d080303014030200611f5144981059402684c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 825785674 1250 825784424 825784429
    0x1201170f0c060301210c24020a0515040510020a120e0606032104091a0405100e0403050d0e030a020717160306090c080307080306030d08040807060c09081207060515 72
    0x1c9904458482410070303171100380744840e035807007864140380100f6600080f03000040c6400b080d4418104040d40ea000190503441204050f40d07198020380004003c0d40041102031414180380081550090068081d14010504a19408200d90100c1840c8000c10702556048c10080c0c038521903003182400300402801281400300010b5030b105582c0342881000c00303501c0b40c648000d88a07034040e240245840c40d424000c84409040031082000600c002d54043c519000c00240c0c842086001c03501260105034968030319880340d0724116681c0e444513454030b60f1180c4440b020b81010400f04005c001e10340165000c0c04200f03082c80315102115500d100c0769140d40d03101c0a00c080c4d151358000380c0c80302100e5000d600040d1003121450540c04c440859400100240008503c4a042c425114001e522909048080d900c205c0b41c8400c3c1940c250a0a403805046860b080c88650006070042d03019030303200c00140c1000c0c84015501d0442c146004801010804800c001103100c02c10848c03140606a0008510100d0000c00d6402002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 825786924 1250 825785674 825785677
    0x3140a02120f07110d080114090402060409020a0903240e06070f05091503100314030f190e060301090c090b1602010c030c150603020102190209070e01051201170f0c06 73
    0x485442c00307160003180b9000e000e001103a08081e2580241d4525004185028084060900c5021041000030b481440301d0314142d8041489681e00420f003a051900b000500130003500084465420700000a40100206090010001e401405440c0c0010240212000c1600f07444600707007900116405202070015a40d00050501c0c0b0040e1240b410036210380031200026007019603a4a04101d03201c002042c403015504c60030010301501d0050004d0040c642d440d0340401d0340c03441031081c0102e00080900c544081ca5140b51f0035032640015918082c002c0d98040d4000464503403007a40403021850751402c0d443c400e1600410084000c00161003d1800c125003120882c40b400c2540d40001e0411036101c6d00c01d810580940f403d10b000d5a00119810042002186c450004101c140016809880340c9180b911014480711b01c00d4074040d501030700441007030b1a18a8180c130138036898030318141400000e10030b44021000c142601402058a04044da181c144e54200d1307103040007000310203160150407101030344159407290310 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 825788174 1250 825786924 825786931
    0xc100905120a0b0106030204081c05032d07021b030f0d030c050c0709090b01121109090c12030909010e0c07030e010c02040f0507090914060f011701030303140a0212 72
    0x1d481c5040010303280c1200e4200b0490302c0000b00803240c540008207600c0e6141d400b410179500c200084854401c10401c0040d143c01ea1a600c8500284003000010000d070310101031200ca5512080d05035031000b9643d210340c01004012149480180d0200b1f225100110210160070218401600540701e2200c0014015480d1880f810300b031801d164403060002003042c41a005c560300440b001003500c1d038143d2100c001c02c001d4030078440c0a50324281c06800118044e5105001084619405881300d01c800710002c0c24040440c00c024048074036030040f1491800c1c02c0d224103410000501c801e001444e40c4460200402c910030106030420540e03d8160420413841280303039030484542075094140b01a4030f1250310b0040b82e25090003140250450304201081780302d04403507080742d0701a18450f210301240c01c0c0c444904504850074a00400c44040c104000b043c400d0401050413410f1503018505002c580d090b0039100b6010b0842079104500207036807450310546d01d683c0b0b412a1900601452010b51400441a0210400c5034024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 825789424 1250 825788174 825788179
    0x50a05030a1205070b0c09090c16061d16081905031602030c062208011a090a0f0e070305250501030b30011a100c030e18090c100905 58
    0x540b09070001c0d5024500360345851384d111684c0c0903c0e1a00c0c1c590f404140c2c0110b14214040e501c1d0101048509440c00140c640164940d02400700e0f02019880c0d490203422080b0794858000f81d4440c1803200c0003c00e020a641302c10700000c010502070701c0c11500614040307803040c014503d0409000203100181b4080111108108041c0400f0070a50303403400002e0520446182d0140e01040c00a2280400502615840c00724405200218034580d41c0d00c01c280d00782d601c001e420440a0458004210244c500b900b081a0020000140002c40701d907209020760840740c42c451854680c0e40040001c000704034007003101240360300e10b41000300030708900ca5250340c003222142c1c001d8505050300c440b032104d01781e101c00c07040c0c014102000740e00c0c0c060107850360003044050b801c00c15084129401c00b90003403410300d11202d01601d4410302400c102a520107902d000c940c6202c60711822403c005480d0003002d43d5984100080740d03200a1081581082e00b8018905858886a519501c3c091100c0119500c00385800511110840f40c09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 825790674 1250 825789424 825789443
    0x503070e0901180b06010305090a02060d09170301080f07061809020a1b150621080c19050303010f090e070902210906040b0105010507080d0b0f040e06070801050a05030a 74
    0x7140641805001e000a00041c5521401000803d10101d005114010042a24200556143c0101090300c6216030a0081d400010801220000403002c1d0b0100d8812801500209032071500002c43e001150f2007a4090385460744000070010170f2480a12291000740858144214019141c00d54030915030388620030740201c6640400d040034014000c42d52481c00c49c00321a49500300404c1464003150a121952401c00404d1420002040514010149980300c440542654048815030f650b03503989940300f0300400519000784440c00c1e030040100701140791106d100303902031500c943c1000c110000140d40b46c1d120307040c140e0914446030340c01e10001c150034054400c4c4030001341c4c0c0c0d0a450f50141201c801d15140b2450000f2007281001b0482d1000325031036014610407440d4000380d0340d840d001183c0500400700060f00a203010800040c0815203988619191280a05810300d2011800001001c0b10054800c2e0f0101360000c004008110398803181440c0500006c84103140314904003004244d4501c0ca0020040400c1c0c10b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 825791924 1250 825790674 825790681
    0x7142b0f0809030a0614060102030f191b080a030b040515040908040b120a0605030c06030f0916080d0801080f030a2a030c0501050f071713050106090b0310060503070e 73
    0x1a0204690141c800541100d0a0342d00da403030005c0c0109001c03040110448150000301d91250704c04001c41e0761050b0200e900b2420301c6041368010b807100c00160316041c28450072415031180701511100e8203484601600446454146404e070140030f03a9294600144224909401c01c5644400815035008003441030b6800103216044d490030602d54403030341d003003900401008509607075202c80c400c0c10a0310601c61440c1c2030290070b9442d03040c151f441c400703407090b160f100c4810302c0060340300b03c00070078550742c0f204210003140c0980e261040d2900b280e200300d81021075250040030070700300701d0fa0304103141e40e004203049030041810403c00e090280c0c480c002c0c169040c0821260300c0e040c80c0324100e907100710b0b0016158001c5004480f2100d28010b0100c82040030116019420035000880b0741c0c40003801c540c491162621078000b015000f82d002024000300401d1043c0c002514003081c000301e00b0910800e0041c1103040720000b440950701d410145004468030104000d45e052010500c0592400302d040000c80e94200014a00c1d40c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 825793174 1250 825791924 825791933
    0x18090d1404030308101a04170102040324020405150d0506011107091802060c01061a09130c02190c0f0801151406041802250209011a0c07142b0f 63
    0x84146d0144803000c031a40007203e08880204018421070712140c41c0294032000b1054403900341d001d10310024001040040e8148c2d0700100d030440700c0d905428219801450192a80300050900c0c3c3c0500f040c09500c070010444e56000030941c812650001800d0811415035100801c000e645d0307e08600940010989a6405010040c858801107051690041c011602c40701940c01140c001d2210f03214a5030001800180200e41b02299030450b5948d02010744280ba40b40c2e8081058409042c030710b030403402140715000c1c2c44095400402d599504c2648241c002c6a181403400240c84144a0217030803d19090340741a400050800101101c107044407281d0003603d82a1014000085150240340d20001034420031410310895013400f64000e00d21255581032940c80705488201a00c0610b000d40c1c0000d4000d4182e00041c04004111900341034604100b500982c50034540000b054100fa0060741301c0c5180c20f848041e81902440c288030b40050795603105a2010200c05801e9544503109001c00016141c3d01c0700a80100910 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 825794424 1250 825793174 825793201
    0x30e0106052101051003051b0112050a0905070b0a0801030b0411060a0509401112040204231302010311220e09070302040f060518090d1404030308 64
    0x51900410700105014840a80418080600355002d280d520305800140220300d00780800040ea60804001c205000810710701e44a40d400c42c080303503414000f110391b1028a40c00f0501519100d090910004152030000340303050307454074203190001d002d51481030000440300d5500c509250304698224100e8081c0d615181040e00c2030008200300307950003030703c00180b141c1d8240c6c00600801c500c50068030b0403500c0c55520100210380c000c50051980c868001c40c0000078142100d1030000d840002000400500410078000603221648401030b11164400300604000a40c42c0900c41c1e485020364080c0400d0f0342c07692024144002c040c008041c0400314040d41c0c40e01040d64402e0344090448042008000ea0310b019038804200c20b040485000b41c9240100080403500340301282c1c105004141880050036850f040d03508000160140408d400d0031a1f17910180001c02d541c5450902444000c868039000040c00c1803c0034504184080340c0820611040312148000c80c00c09030b041300d00700ca80524000956881b812119801d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 825795674 1250 825794424 825794429
    0x5160e090415051311190e07090b04080a06140103050303040201050f0c10060e090106271404060207170a0903110112060f0512010615050a11030409140f0f07030e0106 73
    0x910301e001e0800c01424003103210507031518000d091140c050f0502c4005c206c0e01d980d610300d49240300d070148982002615a1754042d00e810071501d0800c148c28a48681c44068241c00c60382c40300c1c4043d4060000c086c240600c6200c0c0542070b101144c21607100d5815611410b640c4d00c406007000b0304011002407040348003a4074005403071900071080c00340c850407800640640c0c060920b034020000c551240c1000f180040030305110303070b00403110f09202205c03200c510f890b0a03149104855021020b12501c0c1c002c1001c00c0c40460b05e44034842e51140e000182c584000e030a0500126080000d90b0346018810040509001d800910000807603034010560442c03404010b0048459800000f46070035414200440070451520b107000d8041a82d10541c1c203c4200d2a004d00d5840c02d80741d0034418000802400004042428802c0c0000c00c1d200115040441010503083d0300c29185903c00ea0010600b9940c9000800300e10a050005503040111448043e41a050a889407000e0000141901042c5035558001451b11a0700307400c120300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 825796924 1250 825795674 825795713
    0xc0c012106090c030509010504050d0305070c0510020d05010807141c02040905010e0d03060521031c0506011d010503190e01020d0207021207080a080c010b060708070605160e0904 78
    0x4025982c0800001034180c0c41d48640120381045d0014808a105109841c4184d80200c001c100098140c003095005007001713030502e400c100380080303c00040b640421040e4280c01906c8001651000c4150710b50084403410307008142d25401c01078003001141032200b41035800b00801c03200d0039010000844070081510028100a40250400f842c803010b00034194801350b00c400d06002525a5007414407070071401c89001d0300442e903001e1600e4940c2c0c0640703203541d065100541c02c5c0004903407410040e070120815040e00000b03203030394141d1244104540d559008081207000c2c1070072190400d140510f08c0002c0e0131408001c018030031602c000c240450316100303260404403004a000c00215901c41e44451000d003c3d50002205034010071030034846600415000500e0400c4603500d02c007405d00420030369128491030744400200c40704c941d2a0030000c4101e0780d800000300041c07442045802d40c0d600eaa4684402a160018810030310540301005507030506400c48441d982031081202c001115546510b0181d01039400200c03440d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 825798174 1250 825796924 825796931
    0xe04061505040c0203210c0a11150906070207060306031a04060f0e0309040509030f0301260d0e19050a0504090302101802130e030d0e0c13051504020c0c0121 69
    0x3d90b201c0c0c01100070a00e00c0740d600d9041e0030603080400c80324245a0305039401032035040100400741c10b40d0b1080c2090854940d481059543c106200e100030020380304180c0b440c5003603030404c0041c04019601000071034000d0203182802e000c014030b562285032404100c05c800f801501407040001c0d003044000c3e0700201500d0360400301045169800d54510740c0d29044007061502071840c0c0390101c3e030400310000036148036260100d038030752650f0709101d1041d1000719100c11040001428030080e55080105010494540c44182c0e64480900031100804c02c1d804841c030311500e00d00b29079140031300440d02e9040a03042a07507070503180420140036502c4c040f850441ba020070203112524001180d03010582e2408455841030080300c00340c2007440820034070f81c22610099000d0030594407c11031103101c110240c0000081c10192829517215600000120314200110641d840b9a03656820800603207041109890803101c009a80840c1070080b403072529591030345145031960502200c2042c070310300c0f505002e581220396400c087c41031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 825799424 1250 825798174 825798191
    0x9030609031806020d110708070306090311030c011a1c14100618060b120105150408010c0809010c0e010e060c0322090b0411090906010530100e0406150504 68
    0xe4440340304860840014146e0304403008001c000180110548410f00050b00541d8550b503140c00042034100001c5090109040711008144000d002821005140c44004100c2030241c001c00d20211030700703440c038600c0b60f00d400000750b03070030ba060744140a58076910a0755040101c00110016140c842401c012048280c2009008030b418601c4140340d020b03444007902c003805460707115400035902c0c2c080c1103010341091849400411043c82c00c1c2605c003c02a1503401001d140c1600c1d03040c46829110300180c00008a18400280700001e002441080070900180c500600740151040000340361f9264040d42c0c0d442480c02041c43e054180c03040c41162112990086100c400760710300311340740c048004184208030849107003900c01591420075018411039443c08841c054030341812801027281c1900302806050400a052004541d0030b00c02e0003032540c03401c62040607480360251000014181820051a801c2d180c24029000c022510380844580c0d005030340301078003049000e0f082c0039141204000c0c0c1e001d02d45c080e080c40740c1c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 825800674 1250 825799424 825799427
    0x30519020426010c050a030f091e0b0c0c030a0e211c0504050a030f0f0203060112020a0b0c121b030d060e1302030d030e01090834020109030609031806 66
    0x200011010b404a580c0d0440281c0400c0c00ca4642c460914040781040003603040300d074802c0e0702650152408180014610f085921580c006408040c5144100c814071140b90082c4034001400c00c2d0300c501003040c440d20780280d82c002e4036102d004840050061107060001c1c5d13103181d914500a4144506110104003807841c8030a035035603540001d402c60204002d106c04040180c10f2186007250250740c0b005e03220519281c40c5660340c1c85616104442030310030007400c051a40040e982801094003c01a00c08a90200c400c54010448603003a0303540328699140c0100401403250901144c1c820b9048071160300c841c1c40341000d820040f80f4170b40c408800780c164000050440300710715803544400c1c20350303000806408580d039807280ca442019104050103035141e4170860310b820046120f41c121702200d481c043e0002c01c0010080d0350b20b010903000842c03480d03003180c043d0750a080b9003880d50710701c43c140000140845480754016000a810501e085c0009003c42c3e0320760945900f0325000303020302e51150303041140e104d0b80642d80b43d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 825801924 1250 825800674 825800699
    0xe01090b07030906120504020108060603040501140106210515090c0403080c100e0a020d080309190f0201080c030f0103060b1503100501020f0304030309170f031c110f0a0305190204 79
    0x48134007149800c40300481081c52885aa446154180c541c1c40d0326486030030070042d40d03420007001180d0310340d00c8204a6200a000040c07190081441d9100c18201e40304035002503c0003490b540e2541011440d1004021759001203616401200000351094021526250702e030441500c619040078000324400101640416000190324503804034656040201048500c591a280d600e1060003a512002c2840440c000c00c0c905002160000008411a000348070b00700014000e4070003001d025268030149011000643d42c000e40d1040c1e02c5814840341614501e003d10410781140410700025003c07655425070150740b622204210b110174140e038880e640e1a403801034140c0400c03522b00d00506005010f179442121240c24004140c07401d80e9030586400f00c0c240d04141c41a02c0001050900e03005a210312614100001c0d42400180201640154404514860403201400743c902c03003850010111000c100c107410800000301031744d00048052030040b540d40c5894001ea6004e8003100c44030849070388000340c00a42c0710003512 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 825803174 1250 825801924 825801929
    0x140f1b031206240a080901060504060b030a06170a120c0f081308060c370903050d02120f0a3b030a111210020711010e03010b0a060e01090b070309 64
    0x2039083d503190b4050302e416920b2a441c2d80300c00400c0c1038140148018a4020550203621240d02800000c1c0c1507030f00c02c0010140e4415a20003101c0d01030000a000081903c2e00030039001c1c00049004800c00b58002400559645071520050402007082c540c11503018400c100c0410825081606482d25003207600380401c0f03641c00403444140a0011520015902c140821800d204006101200742801480f40d5800030420048170720b0360301e600100c86020054246000801804185551601080340c03d5290031450303c4c203680110810355000240070803010310240211610602d0b11a4038545802c407117030341903440c00701c5007401d182000c00051140c1000b1000314826225142c4c185440541d2404180070305855461044000c2d0000101c400c10f800c0d80e0400300925400117100038103c030004c2161301c012000326040300750f0480d02840c0c48014042c1c1076900ad0101d2241442c120020414601c440d400150006404d00ca1740c030601041c03506188142e07020b02440f50042407081102769456043d40f40c014070105890 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 825804424 1250 825803174 825803179
    0x3090615090b011103090d14060114010f02121905130b0a02160e0a09020a0b070c050109050303120a05070e0402040b0909010b030910050c0c0d020109050d140f1b031206 74
    0x8440d20076a0b603c201300c282c1c41603078500d010b14a0b00700381c40f00340080610301c1e05043d5070400121844601030340d410482c540c02080c10350040402656540001802c0c0d80c920300d015011940001420305d05916401c0c201c40303442c0d8068040d2030a00c4140c04055546006601001c610400043c50000d2a041048010901d00350b1950980c0c68855502e03546130501c3e0624010b0480b40e04541000620540c101d03400011028001489000341e2685c946510149074004001101e54402d00c43c6c0401c403a50b00066400c0140c5011000b441c286400e103426101e030b0039402070005500c039031540003241c040e5004001c40316529a000e4029541c99442d031000701c5040e4080d0030320a011740109000010b01383c010b1020340c0e00803010320000e0544245800e1000b40a05000750402000b00010880c50038812000c004e0444600041e4001103034200903800c0160400c1c4c003845516051041540400c15006d900740d003110300d008800c1d1a09600d0307200c070301450070418501102810346444009005c140c0d00c00e059040fa48500d004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 825805674 1250 825804424 825804431
    0x12040228180606020a02040f1b030b03100c020a03080703110a030203011a04050315060a1205061008030f090d0c050607050f010b19180b040c0306030201110a0b01060f0309061509 78
    0x410000040302c1141c812800181c2007400b050f0300501c1c20350000e0030400000b0030049482c1c64840300c00c6a00c0c4200d405900701084c0e9a034030340741c02800c0c140107282c00d035581d407641040031280d02d100203526078030704400c01000c0015000000740201d000e44c2c001c0c4480d4030501c454030340311152200058020341c001c6c0120104200c0c1103440b07108400e680c0c01181c00b91a00a03000e4400107100814841120b030025004541c08000c04202051044501695070b507410f015100501c45401e200c1d810740b0002c0d5032600603081c6904100f015004030342d661011503c1c0520180c41e10342024440e402c110211440c6034001a510150005d0010b00b44403001401e4040c00003004000c014084000040201c2c20300c00a98201c04c91002100421000803464212155804c0d0b801c80860201103460010b000c852410540038003080e0350345024819075a004440700c814101400040081411540ba4520080f40520410003000000c41c3d940300c50031301c41d0304801d1160340d21040602c8100c5064925003501a654014141028134 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 825806924 1250 825805674 825805709
    0xe090a060f050403050a120b04090309050f030703020f101b0606060206070f090e090c030106080106080111090a1202011206030c0302121b09100806192012040228 71
    0x1e40e1080d6401140d0640701c06142c5041d403001a1441c2860010380307102c85a4480d030f004231940307903400f880e03605521950303506051908001c10492400d03040c3c0007a6001c1c1d44020340901c0140c48150710001125000ca5100500c260032680c1100c0d05e00d00d00303407141d000150300348003c801c00041c2d4100300f094500903002c2d00e1650391641c0003100c54016400005000843d6280c0c00c002601001c4110f5420030b0a80054403001c951080110742514420784c0000d450781e640b58403c10501d42c2c01c2c80381f11101d5021004076841c1096041c0052103a080c140110160242015001021a03001e110303104800724500c0301c288416640c80c00e04e802c1822291105a0081ca0aa80d810241c090042030309040744800b040b420589234030740d0040c0062040c0c000e00d4080380640000002c249800100080d6101d030414000d510030030740071024014140c554800c1040e08880c070911600c03440a521900740c1d601291700d895042d44581c2c950002810450000c000500801116042016280c103840078581c02e5807040b0003001c50120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 825808174 1250 825806924 825806951
    0xf02030417180603040309080f06070e0d03020a11030309090405030403110904020105180121020d0b010903050607031a0d0308070e0603090a0b060a080d050703020d140318070e090a06 80
    0x8280c2c5211200c800150a118041e4a0040040c3d50894080d150190080751925a07081c540f8084041c1480543d000c0400c000c40f95500120b8601d1800c0207846025681100c0d5038080d64940300324030010f11800e842552280c458030100305845404400620720741a6007802d05180e81c580e400350000f52681d0301484060805030404400143c09a941039541ea454500c0b0041030319010406408240e04000900a80409107101d800e12040e149030350440042e0f468006506680c2100c0c41c6000f80d60600600c0c1c9010400300314081180c65006405040c0452001c00b401e18400f10129904c08080e80024500101d800307255106142c54071880c0c640e21a000000703608010400140400c0300c0e041d025500c0342404500003010084c50540152000e4458600991070302c10403400c0000101c0c8110016401040358800e150b0304102c07501c081000307410500a4146041d0014410b880000c044141d00c1118030541d0102c4a020401c01e070040c58800701c100c41718141041c04c40d0300d4002001e000d0ba9402c1c1400031800c3c066 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 825809424 1250 825808174 825808177
    0xe09030d1b080702010b010e1e1e0906030d021e030d1103041b0e1302060c0d020c0a120b130206070b0f07111c0c030c32030903121c0f02030417 63
    0x90005845004031651440e04118034403108910074414509c551018102589039902d1402e034840744240d260041c52510b1050000204004016910907446117803031140c1d1640120704400080d03600520075040381c0103104d01a1441c424550040f00d0980790200d503400c0f031100e410285000302d101d030300c110305036031444840303054804a071780500c040d50031003100407415511112801c905141d03c040d0079141402e0018904600342540700b8801000350304410007180710f0746080700b0803002800311900042107440a51321440c10121000b801c0000c1880e40395094400d40d40d604094038620303503006500d11428a0700300e200c2c24a061060712010302082e048520701d801d030800403620012100c1c8003201c2015079852442c045802d120804070581c2800b03007150459000c10001c10b14106111f180344404450380b41540210509841c540c0e5401d1803640090080c200036580c0410800801149104040d880b0110501c8a0549840540d11030701958030f41052244070034038a8000d50310560203071441443c2103030400c14a600a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 825810674 1250 825809424 825809441
    0x61e010e06180702010612050604060b0306040b130c0e04060c0f051c090204180803041b0608280c020a0507050402091c08040b18030715090e09030d1b08070201 70
    0x802804546402c1d07030300c2510002980007032144008543c20b40d44004000f9403800844007130711590098403c010510900380a090140402540101201e00c0c5c40e88490b0406403020b0a50340e111207400c01601d060111540049001e03224106842c940340c2440d00e0a0001483c0b012032a102140b403c540c4503521034000c100341c2e94150080c0d84034510394801a06400020483d0940480c1d010340d42d50802100b4000c080004500740748240d82d0150f5070b09040c2080010800c2c14a038451280c602d03014140141940a441941c00c4541c40880c600b405249001c000c90303c0d0000034100c0f00151508000d6520300740e0001700b005905000c1d4090340d80b0151605d0a01090348140200c40380c0010803218a042240b011760311000045000320505400d05072601d200c188a81d000d203104091212560b460348420340780500810005002003902d81d8601540d100f8083e00032034061180800281d859000100398501c1071049804c03034000c66000f0010005115010709201d0082000f10001804001c00030320030f6401481a04032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 825811924 1250 825810674 825810679
    0x80108060601020703080d0f090c031a0423010902040c18050307030809090c07020a0f0501030e0f120c0307060c0f11010506090a090201021c11010c030614010f090305061e010e06 78
    0x1c2c2517045840321005944200440948540d0b11444010014520b1081410f810f03ca03a0100046074074504045420401d10b400003a2010746102c1440000b5070750030001322a00850b4119008169281e0280d2801041d0b90903000c0d420a017007140504445a00c2154008164002c0400b80031240d1244185542c4d85641e01004080c5141000034000c6460310030b84c590362084200001509e004c55540c0841ea42060b1548030075220034040005001c1913030180180300a80307484c2e000402407050020307041640c50141c001702103400c000000cac1c0340400390001d004446070f15800450901020502481c01000241803c00e600700044c0c103100074604902c8103008041c040e6070010500455901d954204600601c41e03144c0490640c882d5415a2650310343c400705039001c0c02280d480350612105418550707400e40703201400d81c0041520b06181030060360902200409080000c0ca000c13210a400450f040c0d03000c80c080d40000c1c01234480e00c810883c3c010b2030007100035016440044c030303810542d9981c44036204601d000d5412030fa = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 825813174 1250 825811924 825811933
    0x100608040804031b12060b12030a0c020609040609050f01030b090f0703020613170105040203280602130807080a05160303020c220c051902190b06040b090c090108010806060102 77
    0x41307002c6402401c00d11503c0c0c1c0c1464942d6a55940f03002003400c80c1c400803500d075622440402075901d41540c603070700d00b10311400256240881d03404005168081a0340028407810b00403135520700c0394455900080c007401601004124504124250000f104824072086039005181000030304519004540e81e01450003002c01040087c3c19542001015080340703108000e804540340c000107007644100030095900301c5402c00000c050410707006040c14141c00d03044404984030840700d02a0000e078906100f1910395080600140c031407881109490002c15158450400b034461030301c000c90009004109000074900c1a07045070000f280080700445008880e220140260b00718882c110000d061211f100150320b0b0451000440018100c04150b0031287d6500c01100012b030042030091301c02821ba0b4508181c607804c0d0005002598203844030120402c0c10683c01000790f1101000309040d40c039550404039011710020006036891900303240c0001c00b600540c85143c005034a080002a5103400170642500541e41a4040c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 825814424 1250 825813174 825813179
    0x61510030b01030f0501150809060907210b0403180e0c0306010c020103060509100305012405060c070e0c03041109010e061e060708281704080d0f05100608040804 71
    0x1a40285030694800b4103240d15010003041d12410341c815580a80017103240d0306410301c80c0f035400420030f000042604180f0380c440302c140241a80700003030002c122080c030190b4003214100c0740d030440c8024080f61002801305013100140400c168100d84200341214018241004150f0f03503180d04c3c4446e0400792074441e040d8104001181840d441801d50440550060402041d10380d03a0318007141c0f45001c02c46000c250524000000d008103c800c0c0250b1a8512120221421408034102c281c46c95200910805100d003000250441c1d80070f009209220050480010040b100e00c1c01e0000400700d0b03442203c00710703000500d500c1c0200181c50705821080c10f035640c0e0000403425035205000c0c0040c0c40c100c21043e03500c0c454542c03c3c1610668441008041d42842220f10340c0d12000003804000b9850326100f0032010b200804500c0184031030b406070308403400d0494a41288000d8403941050a0340307104003064a0310079400e240085031a0201038004034040e180d0301710000f1100f661a03504581d0444140c500518505040104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 825815674 1250 825814424 825814427
    0x21c05032214010b01030e010b18040c03140703030e190506221401111207020631030201090914131a0a14100510030e0106080d030608061510 62
    0xe01d0007296422480c41425000380c4500304190680b915032a000d0791150003503031a6581c0342c0154100b00c10404001d201c80c0030410000303000704140000940210842e50b000030244a0760000303000003950480c280607810880304020580b54102e074041580842e802e0105034446081000d2071800440ca5840e000c0015824038080140c2580400082e500705141c203400701c107100a845110300000e003046000c40414520720000507024080c0004600b980c1c0d00a1039400c800b014606c4111040580d040b178403240d840200308100b0704070041105019118182002801c3d9200e035400c620001603038000d8076010105685c8030000f4040e5138101006698000c035040204400c54040d03106140301c648030300185000f40b024040340e07410001f81154038034001612912012025215541c1c0e080d042024110741140c0c2e03500700070100d05003841c0c100e400310070582d41c0c039021a6045400e500050240c6211015161065803011000b0068441c2d4007d080300350003200040703000350348100500d440f00140030381521403200e1801c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 825816924 1250 825815674 825815701
    0x90c0b04060f0e0102010f0e070e0a0908040e0606130608040b0f060307061409061204060b0103200a11060703021b0c0a03030c05030409050a0522080313050f030307030c021c0503 78
    0xf07068155904d540201d6020b030b00f58041c4103505009074008198152400360391201ca0103010302082120791900c030074000031484d1002140c054a441c02948013041e1980e401155461149000100005000b4540811529030010149000d5030041c0b604020383e03115443c0c810002c07201a83c0e1183e05912004007000b00038001d03c1d1a070300704400340e540035040003034103c0450001c5d40031101d5841d901161404100410460344510300d0a42e00a01c9d003000b18107202c0381480e00d04c420541808043d0072010803050700741c902c91100144000a1103043d200903082c1180d025029410044208190b81c5e44a0000552224001014a0580c000414000c84603103552010b9a4048220074260f405001c1013102092445070740c01250300550000b07100050501d84070340624545014030f2042402001c8d4a005000813482400941b60410001c26094003c1001440c015261035282c0b01000040d001c00b108001c903d541503400184d031001c1c0d036001da82000344020240040303400c1d00702140d00817030000e2000c101c2400c08684c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 825818174 1250 825816924 825816947
    0x160e061b19141615050d020f0304030f0305010f050105370e040b06120c1603125406020a02060108070617071115070e0f1c1a040303090c0b04060f 64
    0x60551500c000f1b0380070ba1090703900c4090030f551520000000d110030194000000c0382c0038041490100815410b01b86091007107811441a1410080701040c82881041c0c801c0c03200e04034124004250b0715803444c8400640e541e01100e001140400d024600c40c41042c10b150140c480107020060105107004d45001009089030b0740644202d1031840203000e40c0540345038014280e40c000e8043d0701c403c3c0c2c181340e04540350070596a040324a10340c04440b0024880d00f00f01c13028084602c0c0486801c3ea100b240b00c3c81081601e007202c0c40300c421404421f040e1911000d002041e4014441c11810794241e8590b0380e201e0310050760320481441424001120460001405e9407516145a000072461030039100c1d00c0c03115030981f071500345c49041e030001a102070800c1c41240303604036015120a04094900900064100c070020f1149107402103c80207400520107403500b00450800e0102800c085003880148504260500038010801140e044507803070610710010031194191825102195841e5464010f84c0d900c84000725110b201c80d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 825819424 1250 825818174 825818177
    0x3050d0903031b081b161101110106140901060305060306040b1b1b01290d0804050a1806050105090d1410020c15160e061b19141615 58
    0x8150091100c0246554281041020780d9800d001d4100643c668170340b03541e2220403000360082000350031944c02e464040c01c040ba031342280340301c001000b901c00161341d148411b0f81181c440d54031341400400c0c0b6601e15101030051070320030744081e05582c2e242c4006408a400946030303250b050f44900b0002d0000341c69040960707803003900c1c0c0c004440c0000c8052021640783d04041c1c100c400e4000036421402466409110f10f44404110107018000144110089101004d07801c56081c000ca081e10401414080c01208450081c20050b010242c1c00355500d0b01ba031000d03c852110212000e0a2a20004496218900f80d4800c00401404c503001d4012a40ea0080303645040d0325004070a014030f200d00e0709490514806030095800035806000080c4048810a9071030740020801c01c6038403680c030702c0e0302d0f95142d0101c00e240e840c1c901690820303900d40905c0440f108081007041c1b41c02451080e0000741001c200b1070341c40c108060307108000f40c3c04039110203071196413070300841250403141402252041000484c0c2a4511880f03e886 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 825820674 1250 825819424 825819431
    0xc0319140307030e040e0105040b1b040503030c0c031002070308060405090c210111032403070b0c01271101120f020301090c0905120c0f040b0d03022803050d090303 72
    0x2030351091401c5420428080e004103540d01500c01c2c607410301c4e002c0d09200c2d56400000308468a4140d82e000d440c40030140c694004920641200d00304c220302041150301410005044940315104200c0496645d104160154000d0003480e501c2c4804038034500942d44615810b48450314a550b4042c140001000002c2442d151392048030f819807183d441e0b0010b5582804841c8440c1401e4414005030305094600103c02994084010002c2002e4690b001c40005900000c0b011080d4814400400003842d061894002c1d92210341c0000d000c40104a055002c4448010421350001101ca4042000320780d0814482c0064400070f04035010540e190301c50140c0e40300c0030012002c005540060101c04004a8001747c000002150b51240b880c103103203800981c607000401080f60780c2400f034020b041105031601442da0030240205840350100c3e18075901c84d0050640c40c1006032500c4020036841c107000796150104020300481c020144c00e0500d6008000584036803250300764841514001c0021940c83c002d14101300143c2c109541d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 825821924 1250 825820674 825820703
    0x1a0a0c02031204080a0903021c2006180307170f010f061202040b0613091a040e0d030c02071d06120d02070e06120303010b1b010605010e0f0307150207080f0c0319 71
    0x45026a03220301c541049d04003071544070a8a0300180ba5038000c04c07242c2d04a05140302460311683c03000300321003444501e003d17041103841450713010900d0803882d40c2150b055a488000d44003000380d0001940914125482c00030300000c0d0f0315010035000c480c560b01903040b0031440600c101c0090308203a00700008194024281030b25141f001d00240804d07629a801c150703042a01c03500c090041e01820410400d21800440d001c002084c1701a450700e0f52a0148001c0300107240d00c50003000d20840c0240410801018545542024140c13000322108140008880c0d03144101e044100c0d0000c20707203000440c40b00b00c038881d8004205507801c01070b20001002d00100400d60010306100020700d80d1000380041c41c000c040c108071181e2240c80d0300d04500c0c400034a83c890b00140d680340c4a0f08020603a03020804482d0141c060701c0f00c030003141072240440d0401d03040e40c010380703401042c00440010280e070000e40c2000700e4842c181075409104420314503075140c404543c5107660660000c0d0220704ca20095000c201580c0e4460000108540e9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 825823174 1250 825821924 825821929
    0x30c090e1003020406050f1809010b19060f022a0d080f07020306070503041a0a2301150203040e0f251206080f100b0a031a0a0c02031204080a090302 65
    0xa104031400e6000c6071540c1020011800c1c44c0c010f010140c201295460446c0e030110780464114040301100b468100c02503000729130003000030b6102e60411304015108a0009491040e0080c04103070910511001130100040001740502c08950701c030f01c1d400d60120f64000f0405940c40c0004014a80b01010740c000128020341300011010307402010150540c0b00502d446019034010541090701c028901803e0000810030400000d0640c03e0f611901c2c2c0c0004074080c0680c550b0311040c0001d0910710070024520f01d00b0185517000e25000031010303040f22400020340705140020741e012030b1640224400e040480724083e020640c00034240c2282540998010103841965200c40140c071100740c0d441020b034000c61130201d12540020041e01581c0d0140040c2c80041c014412104690307070345c4800e00940480816900d540300c1c000c1e550b4403000305004540050302c85001003999052054410020388480c0081850644607609182c00802555141040082145c0840da03d076200c40825900200404081203181240031005a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 825824424 1250 825823174 825823199
    0x80717060f12211c11210a0b03030703090302090402060c1e0d0f0f08040804051302040905070305040c0e06060f040806180c150c1c0f0206010504060302060a030c09 72
    0x481500051080c2401009403d6180b10050352218144a041000039503008140c0703001600791400001c005510401c030400621a80200610f42040e8804084001d80a004020f01c240c0501c1c410502086121340b46410035a5030b1003044c030b004010401d003240030009841c003049965801400609164640180c0e40d68043c2031691903011045403c20b441030340d10307a40f00200401001c4001030305200194030610030300a001c3c160448030500402682c400020308008054055500038180a0304d02c210007510013103504023941141c00340d243d2191910001a0700648203010b03442c0240d400c0b1414600560401c80b0000105070b000b17046941200c41006401000c1c20004014130081c91540050901414898011645100182d0041e040c6078040003505810395141c0c40c0f01d0340c03580c5d0300c6410145d495182064060901361840c10010480f02c0300091503084c0d94028107010041c007260360071344003903a0700d4808000444159001c00380d007109080c02000c00080c000e9001d08406d5a0a0415200007a07807034100c030007035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 825825674 1250 825824424 825824449
    0x30405150f150a121b0504020415023309030c1b01020d021615020c13091a01061d06130314011109030613030c05010f0219080717060f 59
    0x9011050308100201c003241101000000b412504141d4451400b03141301180c0c4908030340a00305003002a0f41c178883c00441100c500060401800564035256240024108180564405800350003240010800300b40d010000d08070301c03904d03450140d4600c002c2481103610440020407924691204000311031010008208540c03644d461701840210a0610340002824205501204010b5510219074019801801006030701940d03500d80c5000b20318507205c00d040b850311000a4a00e81c000400822050010355240c011412140c050800302d10501248000c9041c5844240b203440000382031900184484004455074a480c594000d01950030720b030044050b5840b8444950040782e0280c0e0324240e24402004c00e00410141c0d134840c10325103040c00e80820100f52550300042003501044076140c000010580a00300302814550420000c001400000c10803030000c0d4041089500c1d95598000c102c540c1c184034004044c0324019a654004c0c40001c280d80c0820700c01000341400d40c1c030600300503100341a83c80311400d00c0f02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 825826924 1250 825825674 825825691
    0x20c1f020301030c080d0905120c0904060b0a150e01050d060305060906090d05040501090e0414150709050a080a17091309060b0102010e03040b0c010b06030915010b0901120203040515 80
    0x3640e502d1443c00602c03c41040e480b17481c00ea0080e141c10400c81c0d8006208030300316482500c04c411640030801d200e60030684851071456201000c402404144513840d4440010040140c42040b5020340b00d807009516605682043c0c4000382d0f50b0681000d59520035800f07000d5a10206d01c010402e00c0e102c1c5c1d80e60b030030100120b81031442e5620510400a01180c204900c1042c0d0105003070161400d810040001e19211442c000c62581c111200c01080c02c104c5180d8908403038121160645003a0a140703120709846020030345450001801041000c644d038549050307045c04850418001340580c0c2d1260380c4002d0032486021b004250b400d010710041c1c1060302c44604c0560002c00c0c4605c0000e2004030f52030400c00301c5141c443d07001d046a2501450340030b82c410010841e016180f10729100c41c0c03101c242001041c09003135001d02c015044040072080c005d41560000f41d480c010600c8001c0b1020300c5e0780f0f40d001c040c4140200020640020b015503401c0090035141c0e80119009801982541c10aa006030031100c0724640542c2c0410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 825828174 1250 825826924 825826927
    0x150518060103062702180301090b092e1e061d090607080708090a06091a0a0c020309040e0a0f0c050907020f030d02180a0801150f03080d020c1f02 64
    0x41a603807502c00c0c8006800e00c3c691004011300d8602a8112048110364110314555000030502c104102c025032541e0040f070020000c5c0304c9070905103040901400c00380c6001141d0b2282e112903040d514403660a42403001406410ba0301071400761000180640545511901c0d564501c0c031401806c00054020b1b0000b8007951503134280300b10582042c055100ca8000c0807001c060700700409001040381d100d441160464540d24003540207460302904a820008400b40080c807003441c0035120340410100212107254034a61034540f1031b059031a88501c0d001e49048840d4180103170010404401c0a1510368420050700b2140380413520014525a580b164925060801756150308100c1400c21062400c40c4895500414a03c00362903032403841c0e00c01c580e6902a9151102100390041b40071900e03100622403070261204011700c840340150b6184007480c0208580e40000012480c12200810000800086071086a80c4200720614010961a401d40250410503812241d0b00a40c005a0003000b40740c030940415a01181c0c006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 825829424 1250 825828174 825828181
    0x301060b04060e010203160611040902070c0914093c0105010f0b12040f0836030f03070602130807080c030714131505030a06090b06010e0a09150518 65
    0xa020f00d84451031040c1158002c21080024080c440c98126800ea481807000c1a400792001041d4294020b0703070001000c4a201083d018188880c0c10a00400c039900304004022048a50074240c04100c81210301000070f03071003840c000c00204050082a110340c040c4800e90b01c4c079a40009032506d01c070912724060380b505a440c0d01c01071100e6904407007a40e004001000c141d81c6848503486800001d20300c01040036002107820a40d100c04d0255a900300c90f0f045068080c41801c0801c107904582c0700b41141207442d8200d00304919200d1583c1800141051f104003880000c60806403150303110400303948400d1044101c03001c0040c0001e0201c0080140d03101400b60035010702080f03000e25051620700211540508610551249035000c03580b1188012542d40000c3d034400302e0304020550034100000002d501c2190540701d60400c2405015040d4404d081d210f106582d88400d546403c4011202c800701080b25a5020301d500c0000c1200c40341e05d5000c0c008840d00940307440030465591000401500303c40d02d03860401d24464040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 825830674 1250 825829424 825829427
    0x9060310090b010e0c07050d030c140c1f0515040e030d050108061e010f090209010c02090a0b181e07032304030f0906020705150706020f1c02030910090807020301060b0406 75
    0x3580c0c452901d80315103007803400071f03202c1c15904c41c1d03007003481c100b856669000001d40a10410000d62590030890140d030703850550264007030359007410307030440844542d1211012440c040b4a024103030288a00c3d00d01501030032662402c10006025030020318041d848100802e40356600c07036004850082444101411180c0740205107006942c0e48268140c0d00e00d880c01006000084040c180c0c0c0302a03442c44140161900d1025005841d00744a90501a502c556880c0800c08030345074580000c0035480303081d188045007415000c42200e010400b0750740c1071a10348280d40c00746010514000103135840000b9241c04180600702c4d070714400c0d080000001315081d60510320200700616802c1417200702510110b2420250781031400000030344403800e9010300c034402d8424503110034400648405851107aa00200704658850f5148407080d215030054071440c038080d1030400c030030f008069280f0907244030b07000260107410000d2404200c00002d00390a03100f00c4128000f4010180540c0f000d124038005050040c81c00d80d43d45051610 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 825831924 1250 825830674 825830699
    0x5090109120c0617130f0813180c08060a060e03030d0501060302030f07170a050c0c060c04030b0903040e061306150207032102100b063606040e040209060310090b01 72
    0x241c4041c0002c0500c8002e1880040e150030040e0800307000501b1a2003032600f81c038240b05400503820490b9000502103134264003012032408011601d43c040184039000003083d20000c40c1115030790781c402c8100700100002e500421245d4904a002403d50740b400c0644801c110840f042a0032100004e6404400c200350007404070312a54001d0300c682000c8410000750038404203a00401040c0056468503900031407007503981c6100365800e44012000781c4a80e45000d400146807a0040e10040d15001c071210b001ca204c291020040310103484481d540a83c040d940c0c00203101e5451000d070fa0032051130b5a2044001081c84410b0030001080126034080c083d510701e5401d143d21b0108401d0b001ca0900f054113105046100d0300050030110b04090140046804185500013030003d016030300281e141800342044d81005102005000d11085404048056400c404c00c020300c03403036014a025440302e110084011901619101110036401000101125071040c00c54445d041950360640040300c00000680040c0800d20f207004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 825833174 1250 825831924 825831947
    0x6050414040b070c050c0409050c0a0b0405060a050c1002030a0203040606090b3f0d03060603090f15110c0c01090b09030d081312111c05030705090109120c06 69
    0x2840400181400e07150000d82c49005800d24044c031150040a904101d0244014915401e008004200003022400c04548901d5a203505a1041e11032042c04129a8030360302c20384d0140c1c2c1c00900701c14182840090151226031004044003011700c5141544600700c0c420380011803003103855200250301d0341070900c0d003881680c0036600024030b00c0b41030145442558480d100b509045c1a0034465171510741089100042410500c0f1500e043c41c00c04500600c0c45100c5c000a02c00d0410001d6034080003860b954507030841c01c485908000611400d104098400407441001c1c061001600300b640000b10003507140800003061340039170003504840d007283d0502c0d0b039507680002207280140165604685000d045400194843c001c1010a07018072281a01091030a01300780140c03504140e003e081d0040e61441d0440c080c01d00310001c0600c2001c1e20841241c00c1e0b03a0862003421340700803500c0341c90301425600d038600151440d030449200703c5d0400c5190140041c0c2007082048a4026a000c0c0307507101900d500b0807000800880011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 825834424 1250 825833174 825833201
    0x60f0c060a1d010e100908040509090a0506090c010203040302311a0f09130507090c0c020f010e030a081c14010614040b0f1803100c08010609080705040f140109060504 73
    0x45203030034a581c01140d00c0c0c1d0000c16117200090241c015281a008038092600240d03080043c0c4810480704250004520810300d0251048490170354030350f13928035520f5a04040860050700140402c0005040c58000035010003049031030034140704595039a041400e050450100d40003a02c50b8070700351150750220140c000903041074602c1e0203550074078000b00704803450282540303010140160904080c4041400304c075000d0505100d05100030031031184002c2401c130103640b05901c5640450050b41e6198060f54000700d1075031001e40079014081c140e49802d5807a401000300c2c1e4034101003040c448000000103100343d08401000c46684e80940d41007040060507101603400c8505c041d03401b080140030780e410342c4042c1d030151441d580c2c00640e1104131420b0040c0b844049400c458051155074262449048070313400c00101c00d29a50344940f42030380d0328401101c81010354480c448a54100520500403401c21360001c950401288501017100607030b00f047e00c0c2031450260720003252665a00c000780403500c1c00c0c0c007402580c0e4001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 825835674 1250 825834424 825834431
    0x302040614010203180f031618020a200106051503160302040b160201090b0417010b010206160c081e031f0f1e03080a0e12010e0a02060f0c060a1d01 65
    0x16107001035038030301c00d0200c0740360f8201c1300c03118252150307a900842540ca40300c00303070075942c2d4000510014100400c1c00c2c0200070314445480840c4021941c0d0744203a400001082c3d890f89505082508403d03400038003100e078102e00b0b5403502d40125640d00c074031081c2d0740c2c480142c030001c40da030b890707c2000303505640c141e44201410540100420031041c0d6400b41500d0245408a0710502968400d10050743c4110007a0702c090320042c404a40001c1a50081d05000b110f4100c0c540240b04400c0e06000480c3c8410044030340741004040c0303066001b0164810345041005900c5204404e02d880002c040180780c0b0342001e0341c20f5a41c17440010801020801c0d80348064110700018a003010110306006a408200025004d084007423015800315090243c1d9914004006640104005640b40b001c01f400814100e28110828045d910202c40303100314140521450007200c80020181a09600c03d90030003c40ea8030024201c82d08040900022421500038018203024080040c1c002451990a4100c140500c1c0d0a44010700310740d24 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 825836924 1250 825835674 825835709
    0x6020c04140103211b200d03270b071b17061521010b010e06070213090f050609150109050f0117100f0204062a0308040609051603020406 60
    0x4a1901c010284c481d284218102d601103890031140300f08940c548114443c2440c041d03109104411040c050521080c030401d08201d200041401003160300340d43d0040004039881e24100d00b440c2004940d240168104004404103503585100040582113240103803188a5989081d0000c00d21a041501c01400b0401041000511101c101ca469103401040e00c01e900c0700c0d01c00480341541c0c60008040c040c04038802059a58940001d449000f00007000185010505154001011385005000d80b500554005c0c8000445400210760300701400103c1000c44942c180d0381c0d00040020030a0040c00c3c07003903000c000286070240c10f039000e0701d815174010390108215900e0141485001c20303500205a055481c00c5150180011841021514005003800948007079860414040440e201c030b50014030403103805940c6d04030a0300310325a440f003e02801d002c00900b003181403000d600009000340752540d0f125000d66400203902005840b010304081c04602451902c810000090045242610480c0081c00360070200350990740 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 825838174 1250 825836924 825836933
    0x909080c0c0a081005060f030f010504030f033312080c100b010203030a11040911030609010f06053a0b040f020406021b0a080d050a030e0a08030c0c0c0a06020c04140103 74
    0x1101c0c10b213404862616100001c900b42c0340c00d50000101100074086512880e40d01070024001d040648040300010422a8144525442401034482c00c0c0c0001204c594480c1a40f400c1c3c065407810030031828402010104005201c107a00706070300c0c100a000303076203036503458800003015400d0500a5186568261520100030980c0c0d0b03000050342d9010314880750000f41c41c2098540f00c0140d0043d40d001700c0b8514103000c80d071412910a8405180100f405540c0180c060340c0b07540d4081e0305814280a04d50018400348142101d00d4071010090301c1328102001e81c00c10112591081102000c074108000041e1900c0c1d40e540300c55810f01d8481c2e00100301e1030368001c43c206402d00400a4071400e4190b464a900300c901c440103503403035075015920710040844004442d2202d4080c400a84a07401420344500840e150000404003030b40e011608207015a803040c4540c0c915a502d94000c01c40c0e03004581036040c03500c1001c3c505030207a00e61110003005428150010205c51402400b0070040c1d0301c00c40c14110784030102000400009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 825839424 1250 825838174 825838183
    0xc041e05192f0c120309010227060f03100315090209060d150b0112151a071205073306050a1526040c1d0720070909080c0c0a08 56
    0x2002000b0340a42c0d5015148502c6207040030016510301d01070707000400e0200c034100550007800184400004076022202600300e480e80c0640624170309030031000400441c075140e04620011940407400c0c020121107661a610b03554000c401e0001c02c180c4050b41c0314010b605515144680d16449003013107449a120b54000e50b01c1c4101c01190408000da203075110b0030080c1c4668050310405184515501c030421011a13180d0491303840d14150712034030300c0300e40b601d2010a81c4200900100d07101c03580c0050b1903800b16491100c0480c6c0742c5d0302c10381c3d080d14105107001d9502c115000e9507500316080c46a0100e2920403210140390003080394102d03400540316400d881d20801914400d0030200c052203a40c3c1c2012080400d80c00080211105080d0492810000c000f0800040050a0021000b034418207038000104824101142c1d914a4080d51362101040c19000d0700a4010700040103450b401d04800e00f9192544d540d80d2400e019a0600e410844130407102080b1304c0d00e0050b00300100c5200c4001159548103040c41c0c080b040752034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 825840674 1250 825839424 825839501
    0x5060f01051608030a0207031b05070302100504090f0605100306030c1e03020a170c0405010608181002120613020906040308180a0b120a0e0c041e0519 66
    0x5100020a10b1500d070b51009144850b101e0300005560b03640d140112404000f54032102040f408a8100c1c1c0b4000e600840700800314501071350010041c0451829a002c100090130003d6031001080010800172a15020a029a40c4001304010000c1a068100340400044000c90740005040520300b420800c042581108a8422175002c00801030511fa8280a801e6130303c0b0302900040d401c00207254000901c05482440550030103215000d03038400d466494100000e40c2c80c2881040c001940d94404640b4229a14a0039071481c1030050445000d9507400c43c0300400d903040300c00a0407609105070100140713401d00150320010030991580840c90454a1343c0040e25600844c0000b030002c4601050321224030f00e01d015800320100c1e0050040a48603034504d240042c030742c046d000300c200c520800d4010500190450007003075014521000030b00060110441480024142401000464840d1020340c00e000e410074800c0600803822a105a90a080d4100404c4150707a806031030b00c9a40308104040344812512080398418 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 825841924 1250 825840674 825840677
    0xa02180403020f1f18080c030a1b0f0305030718080f0c030d3212240901051504031a0f0f2526060406050616020d05190c1805060f01 58
    0x192610208144100e0301417009006059420001c0d5846103000c0010180c50741d000b81342ea41411419452001080b00c1809110007802070800015010000307020381d02542e802556031401c9801540c1002d60350031544400d80c40080d00c0d80122210800d550000c3c8107240c03a59605400500046482400041800084c0305c5800c03054151110320111500c0300003100c4807107078104102030b91194451001e40c0800d801c00d44088910021800040c21125030b028192000d5060040035580503a01c0e0038140400c0e07000d03140302030304801410400400001d0010f41c072100041284c0607170200a18100b1180c0d11280c9020745490b4600ca0440c04100c0e0b40120b1501040c9040b0300450000302005442c8026540c040c150b0030a1100341000c0c1d5007820349480a5405140318071800c071414000141e84205000d141d2042010103080c0c8200b90001e64050f0400c81c0700d52892030b224900701e8800f00c140c404c0e0044000c03a090030842d504110300c40c0070450070100c807031084c10311052050700b0401410040c001414603405246650b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 825843174 1250 825841924 825841931
    0x81612030908030a0f0e040b13050709030609060204090b030f0714010323040c0519230a240801051320040909050d0203030f0103140a02180403020f1f 66
    0x2400c1500c6078600400070700c1c41004490300c60034000006092003618411800000e0005403112000d45041e002d82010450f01400030345140316001c0c9514040e00c8010100002c2c85403442002000440a1140440543c00b031031005840d00d01b030010081c01e0381e010080307440c80380c6d104030114445140c022070713064203d44c1c0301518581180980b500503005400c88003049000c810816141c10032050104605901c40d510880c640038115454008024048006000c003050401d0640b03c280800f03080c051341d08900190016032814412040c2c03001940c564103540240c04c10303c03100d5103101c0c92502c81054021001c0494104003180d03604007408031340080218101802c0a03521603c4000812100ca041110198080c0760816551a1141129400b80964007801c503136a110b00701c03031110414400f2003941d0295140602151099181d81c440351b101081039000d258450050021220060351204480100704810809030503551415050107800e088803952000496000320040c0b1440201400341e00c0801824400c001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 825844424 1250 825843174 825843209
    0x403050d08091e0609160b040e06030f0a03020d03110406080a0f06030b070f020f03030601091a04080a20010e1c050a1502030f0703020412020402070521130816 70
    0x40c0c0382141c83e10355000101c9030000c607204445404a580f03441002040304441c00c100007a004a1408000340c0f080c403180c601d00340700a0200c40410701c00c003900408010115058034000d40ca038141884c641a0040b000340c0d108041006000390503000d201218440b5499460800b858020b018100400040220744410350700c5510000d00e22517640020040c68200c84000114a4854001381c031202d032940101025124030604000300c854000101d034455103040e9200c03005189802c4002c0b18100300d110078202d02c40c0301400302040b00d00d800c20002102d140503005070001440b80103c8143c0ca002200c910904001d11800008903e842c3d489034220007d910890500d1344920034280142429075900c1c00a21900134a25007480300a55600518026442d44002550b41e481d40c1c44260120303c550f02ca56401020720f250b408015150030390150140601400664103900500c51018844640324000300440d2800800c2c1c43c4088201c5002004c003a0107020001c1c44140b11000038400080c1640c4180ca45810780004e14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 825845674 1250 825844424 825844441
    0x207031101050106110f1b0603100b2205010305090a020114120406050906070f02210d05040c0e090c09180f0f030711100f2a03020c090c0403050d08 65
    0x820030998a12000304040c2d40c5461000784052a01c041040d81c1d4410440a0301d80342e0b0001c550b0fa482c1443c3c0054505040c0c1312801400380c40c0e0401014001010794041001440503440c0000f400c4d10075804007a466030840005020501e415190801810907207468100413544600042d01c151032602424608000030428164903810f12804542c1881e0300713080b1050008000b4582c02c031902644085042c0e0315581c1c0e855104540c05200380c1d54150050384241d0703c441100350010011003d4042c0b11104078507000d2840a44001d40d50103503001c8409420000042022099203e160313600000050040d29041d0380301000120b0a40019002018540d803850200c07a0001d0100702001098441e80196a80c440e00d400d009916a08045026190004540c84410042c940010412034004050b102c100910006210440d026124203600200240b001011442110b850801d000700c198460307402090980441018007000d204040c00c103094040d8140018800281c003c6405180303000c0705e10300802c00d503850251 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 825846924 1250 825845674 825845687
    0xe1507050f162f24040905010e01090c0804030e030a06090b0906010803090a090209030a30020706050d091106270d03020307080d1415010e011d1207051522030302070603020703 77
    0x2507401c1306810002e00003401d05031a0704424102c0f80d669000c581c035684c1e42c14190303090710400520707000000c24890000f00041e02454020034500d00c043d0888540710300554401044520300300c01603c1ca21415801c000e58118108042ca000d0401c0300095802d1642e0310020810381003281c0900310000b500402c62404a80b41000b003e190150801c0c903d261504804004c1c440d0100075210048480340d80784000c0315080d000041044c2240e5103665a00d143c01101d0640300001d100384c060889086140c0c0102c0e40007139a403400606020300720f002e0787d40c11a0514090300e1240e0908000c0f00e600456401e0040c41c0840e40100648030580e411881c1c4a948842c0812a40020800141c29094801c4d558044c498907084c11030241c1c001040a803a000c0d003004681c00191132000c0640004012900c60306814440340c240300542070141081c510403244699292f8002812014200c01651a034180100d07841030002040428030000a0841c000200c1d11400c4da10000d4651081d40124404c0c1600003a0345030801d0312449 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 825848174 1250 825846924 825846979
    0x10e0d0507150501060e0a1202010f030f02090a03050607020f070e130c080706180e060a090f0f0e0c1503010b0a03050c071e0606090e1507050f162f 65
    0x1408014a6856660182c215651b0b140b41c0c3e401040b94500111340c180184100c4000346030141c40705819030140e44401c401400c090303544042c025800344613030b003059125030414078051403081e400f40c112803400000091a0580740f13000c07851180d1001e80e04004800c1e04840107500490f00711280c00301400301e4242405504c04e01d5010140300c2c410094001445a0301c42c41080c0d004070442c20400c42d0a50790250140c2c02c44050781e000da4801e202a602b0080c211007540210f5041c0d100000104402550080803c2260200d103031040458000310400c1403645002c41c002c20001c54111006401d5504124034842c0038003c500995041c5039607080402c00894000c2e003030328041940310452407506001c61042000350034403083c04680304c40c10311001140020a40c020346040c40340314030040c02080b640c16200b01740c04102603c0170080c0101001007480341c44500c0010000c00e0581f54010b4081149450401d401480a0002080d0b00000e01c00701030a1000342e8204081c80b0904540028104480c6241e288807800c00e078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 825849424 1250 825848174 825848213
    0x10306051509041505090a1d01090605181c030504170406020109030305060901080307030e0a0f0e2a03060456090f0c1e1803010e0d0507 60
    0xa07a0010080007068004200c0c412042d1014400071140b4034500400840e18040c80b5400080100060066506a03001c0d083e51800c0302d44c1e4082c8442c4210009003119111242501d420380c4030800c01c030020f8804030307202029644410007003004a030004c410509855420b0040c0c0209500e5201043c00d000780c02c0410008200c4500c01030780d4541e0b8410010b030080c418048200c0100c2c4c2018001092458030700300c0c01d8100c68240015515088943c1d074120380703140c64520340c01d80c02000c080d4081382c0303120010007100282110018020060401c0e60b0340c0c440d901c0c5507002081c01e00401c5a0020354042d02007040e01e82001d420b80f004900d041c2200121500c0010b501450f10016003100100c690b00c078040c28800c4811054804004484400c1d4510b4032803500c4801403081e08540c810021071102c010043d41c0c61b510402c0b40b40c51a0400b081c5142c4116000301c01c0c40c1402044030045075003d0698414003824101c0038040f00200001d08620700c1325903d501d000d458940510070081902404e00810130081803811164 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 825850674 1250 825849424 825849439
    0x1603030e2724010809030a0f03020d020d0c18050105090906010c0f0c0914092104150e040b040e06010312110307210c0b0c0702042915070317040201030605 68
    0x200c882000c85040c0940b00e19040710040381c0b441041e50088400c3c42c001c4220382d01451501e44040410351344402c41d00c14030f2040542c200102142e10030390348082d04504d03c40800208000d140f008004121455690f00d8504120148034208516a003280884111070410340302d81c500c035562030005880d10540008050b000301c410f42e00e00c00800001c43c0d83c04050b102010b404105560100100d840c0c1c82d081100d815080758410302854030030401c2c0c074495407406c25401e80110300d403644414948000f00c1e03003250340130081490043d114400d445c19011b00f6400210a450801800e200e103400d1070303540d03103041c440941000e116461b03000c03426110f4199099405032280860369240075902d042000c0286041036800014603006100880074030450012240e40c0d000209200c154031012501c00f603503445408121b03031041e91307400c230714800280e42c0408038035100e0080000a0100d8500c81440000c00745880010f50354901001447d0020ba040701d80002640c01c0d500035458290f40710710040c0e0040c01d00d40c00007644100c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 825851924 1250 825850674 825850681
    0xa0809030a2a0b0a1b031107020409020301091209082b0f0e06041d0903030c0a08131401050601121e0911040501080d030b03060f06012304080307051603030e27 70
    0x107250008248070540c0802801701c00c1101e40120304440c00700007503000c4804104540009494590056404180020700000c0c00c0c482c0f43d80ca840c0d000030300400000211300010801c000c03001303041c804001802844002198240811066407511203401030008040c06100390114a19500c14901d0b22040e610282c4940d030780300c1d2180303c400b450300007454060001650342e40c001000c0d5a804026240143c2d410360995042c14285201580d00000c001c004594080110010f400030660989100c1ca087e41000c00010356400c00b013000401e00d0303040095050480d418100412058600c000d4103a01d40d800c100c2000480a806182c006001c6102d2481154041d0800f0004a40c0c501c02041481911009840c2000002d001d541419241c24085802920001c20080003502550223000c1c4680051204010040a00c00695003003000d60400c0c3c0088840b0741c000710381d04040050410003880d00300101326580107004d14583d00104100042c641c864024041200b68120302500c00300119152000e09500031003500c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 825853174 1250 825851924 825851941
    0x181206061e0302030111040f170f0d0302030601180303080c090402160b07020625030504020d02030a05010506100503040b06120304080a08030609130c05121603080a0809030a2a0b 78
    0x240d2070b010036882546030032240038103c90800122400c686c814058031043e81c1c134041c203004a800c2a48200c2e113142c0506041403e0031030003845044030003000b6840c016100c1c14000c0005240da009034081c4042030304d2814041c40460f03044000158000c1d20000d015603541e820b5000704001c0e004031441c10360641c0000300c002c410003954806d01da01c02c1c1c150f54200c0e83d982c1e413101900410500303d20046140020030941510440340300b0742000d644240040d02d03804046030954007107458a100b020301a58030703955030010300103c1e03c1e10200c52030100800d41307851411802d0540384d050302180054113147c41100221001c3c42440d034280b05980c01805200240d641980082c1014062a4000c94000d480741d0340460025013851030900b40350110302c1d004882c00c2c1410b801c050a01800b9440c0c80c9910009200c0c2410070b00383c083d006c2c02488046d5100720301140d110841eaa8001e01110740103000800c181c0c009100e441c10392540118807180d600b4001c0344070020307a030b261402c1c01128a8922400b801030031482c0d08000300324 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 825854424 1250 825853174 825853229
    0x60721090c170c0603070f05090d1b03030305010611072606010b04181b0f110f0f0d03050906070f0c140a0c05121002090f0a06110d18120606 62
    0x100000b025078121448100070003c0520080b2454401701d0548120045605d1044026100c2124081d0041800407030720746660006800480c03c00c3d48020144409204050b4140500790051005050001035020449110b80c1c891f01180200c2c08110044041c084101046415400c0d000b49070f00c0545005584030468605985e1240c00781c0002100030103500282200c0520032981c1503076030541098002c0c0800310342255800c0d1980000c0c1c00f0010341048150b0407210500c100280035080c24000d18150302c0c000c07080340c02d0a0301001c000062500d4138080050b005000705e482ca40c0800c480c0b40c0a240d031030103a4419100c10701d034420064042d0700c00c8511054220320010b12031714410301990400c90f41c203540344c0030841610754811044c101504805607078215004250064003001400074100360258410b04042a040003299205a000444e0f1f203000000002c01400000030001e0107242500078010041040440c0c07400c03e100380c01c0114041c0205000b80901540802c020744611303014900040880007580000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 825855674 1250 825854424 825854459
    0x20711041d1b1e01030e012d151a0c030a0921051207020f040e06060a1d1306090609140106080f061303050d060605130602060721090c 59
    0xe1003100100c0b4909007003074a1460345204000c2c1a0301d4400d0780e0560003258108428602418180c1ba42c0700001ca80d0030138050b404078007043c5046000740d40411040442480482d42c0842c0c0c8007132500e080400591240e07070603001500c9109107980070341c10344451407101c94801c5c031a0340e00d0305001c0498142d0201d50301601c48030880b40441030f54101c0c50170180e2070fa2114600d00384000c01c254054502c286024090b000505119800240361100141e03001c004201620054003d5030070341c0d0092010040c8a1508032500d902a0040000340d051403000c03010720000c9080f001d440319070300900481030a003c0003013a4002801c582c0e40188148680501444d22618081000e075184186500302000401c21040000d64a004141d10400070555034641082c0110260034110040c1c08101c01080070440030902809110014540c0350f459a0ba281c0c141300311b00e1800300190b00990115003011050150f401d40c4408101421403030fa00c00c000880d15080c180304010000580001d00980607800001001c034000c510400a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 825856924 1250 825855674 825855731
    0x70e0f01061115150a0803040308191103070b060604120b090d0c2120030703020123060f040b10050d06050d030f0c05070e160f0f05070602071104 64
    0x80c2034048042e51503d41200c00511481c02071400c0008181043c0b1200c00601002d02521540d5a180c8030402e0701c2c2954002c0d0810788581d88006990b201c42ca0800810850b9460700b8a8030003200b098424040340c0340c0c414041c000d0a00c24145011640a81d2458100d80003080c0c0b80403202604211460256107a01080b1004007203801340c01802e00285012712071f842d20484c1d200180d01000403d050002c1b021103400781c01102080b1003d0040e401020344038417030351003540700a0000d68403083c1900d402400d56003d10501c0200b040c0907500e170039144040004050f08142d00300c400110090b1500e01190040c13201e601e419900c051204a0404c02581100050642820841090003401d490700180060024940c400500240040d2015042d251140050110710303445801920041d543d12107801c202c4800c2075410304d02d04c80002802c0100d590300500d00038a140e0140c00c0080f032070b1100c03002c090142e02940300054095600002c44404004000104001480004008014490b000c2e0354601075000340c80351045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 825858174 1250 825856924 825856937
    0x8120a14271210050a02070606030c140a0b0d05070c0206190327020607060e1606081b1b0a050a0c050a0b030121030215010b0a030b010516080a02070e0f0106 69
    0x40c00c030305095035180c201c0b9040342c0c024500fa1500301408801030100400c01d005007a401c0c007009000481c0c038040c8500641c0680100000c45040c0041a10000c4d10303002500d101c0c03200000104050030b0030200b61140742094000000b49aa28000c05941e203800003c002903000c4000281c1c0c01000c1010728612400c0401c070341e41048040000381c08a4410b110b05074409110261040075107006103003c0f80107200700b510130400402d603400701c0c2035401c0c0381c1001200b0004600307038842400d004960380b0035000d035804071841207071500360769907103000b004244070320f0704103d04003034010880040c8890100300080320154444110740c203441483c1003207022440140180d62055444000000c0c98900e02400d40b4160b0b040c00d0b804030002c03450440554010301030388500302e0a601030708500c0b0483d80341032a8514000d110190070b0b2580ca444940c801002c642040d45820b050040034010000410810000c94040c079902c081140e6860b40c89c40d00a81c5841900c7c1d0000943e1800642004140e05101c148941220700585540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 825859424 1250 825858174 825858247
    0x3b01120255030b03012f1308011b180e100e0f060f15030c130509041103010b040c0509120102040f0f0509012102102f0606010908120a14 60
    0x5400d80d990401400d0151201803001b1342070f030829959100b000e5101040052403c03400d22400e81e03404400358003000c6140d40d640000c18501001d0003c02c070b4682e00301c3c603000b8500c40b074245400d00340001c02c0c01240850b01c030900c00500c00310030009070300d00a8006941032f240240381120411780f19900c104d403940d0064079500301c40545410610b000b2203822000d02c2805040d41e4480503c2512504081e03c900c0d5074101d1008002400e80750003814a00560154151081030580c04050500303496071902c00500a0307280ca01d0b14803042d0b6000d0159801000b0403107448100362140b48402c0c1c064061600000b01c9203000b00c1e40014040d90b0150220101d84041e00c03507100720f81e610540203911040c0184058494500020010010b2500e0038954140402605000d2020410200e01d0320469092500c64180d82050b5100fa01311000c0401245a02c40da0900c0c0c20180c2609040314aa102c03400d120640402c0200030030354681e2540070b001c8982d941d40e003042400d80c803030036050450581e040c419010355442d101e042445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 825860674 1250 825859424 825859429
    0xc040e0106031110050d0207020105070b092d10050603030d05010e090d030c1407020109090c0c05010501150c080309120f030f0a0506060405013b01120255030b 70
    0x244c440007415100c0c036081102074005c14010754072000040381041010803241002884030800c5a011f140c800001b00a007049551501c240641c0c03a5038020740d90341d00d07029403c94992001600c054081c01600000c9051303260f45c0d003ca45140956061a0341803130500c400481c90400808001d441402550104c1d1010351190105030100c1d005200803000050020703609484082d21007004003407092061410628080d82c41d2854000c880b281801c1100041e440b002c5401404000d010320b6002d00220700002c1d098100c5144c01920341d002d1100c004000c9900031000890600b41445501c1030a200d010b032850780c51040300000b203002e03441210b03001140103425000c501c3c2200c6034400d061041c14003510300c5240a0820005450140070604000d5550241815803081d040010b122490102e0300b0034102c3c1f0b0040f80100003d00f0303004288441562007481401040800c0c2c00d80c3c00c1c020304448070010603410101c91580c0182e00102a104605103c015061890400104010064140340f01c25a420848244071004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 825861924 1250 825860674 825860689
    0x80a05071704240c15051b09060d0509151608010806360a0812010e1306021b0d0909050105033c0d020106030b0a02040e180c040e01060311 61
    0x10781c401007190340b034848080450400103c400d07004030f0f0408290700d0b07a550350b0344070582c44460300c090740e0241c0315402c1c815801c01c0d044100d00400746456020b820145240086495409168142d000c4161241d004c208184020b01560b0218004040b42079194941030902e0003503070340421110400106148000038100c440481c600d03010b5800c01705010012004504408410295070410310680704000c284400521410807078a0030b01da202d0398240c4e44800e00320241441c0880145d10500700d0102101c100440090314188404085600080040e04c441c0c01030140240315541e900152141e12030000504251500008441c0448000280c00e11250303880d80249a03d812109840c498003401c444114171100c90340c4a400da403001840b03908403400700c000c108040d1801c0c00400c1d4200141c1d64440050090018034a880b41e8030520508056142604d0b0a141d501b0b0220010481c41003103000e51507200c00440c0610038180d6082c8014011b05c10041e40c041c00c0c500800f82c51000f210258210941501523003040f14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 825863174 1250 825861924 825861929
    0x40608060d122d090503010c0905030d05070c0909210519080a0e0a0b1501031509021c0e07080c1e0d030908060a0c02190507060e0d080a05071704 64
    0x8050704500703941d0401ea4900e440c01e03480c51540c2d194459640c080c40c01c4070480b0f560f100c0306940c400070610b141a0a1508664070600001c0070809020b90900998a001968403003400765490040e41c2c500c010b04000340484600e070014034242d81082500f90a011b40c60700c104100640840708803a2000309ea402c00c2d10103100c5e898641500c4004c1030005040795000c0c400861f4010001c2c030001c40c00c004803418003070404404c0002113451680000074090120f4ad0344002401c011001c2c2810404410041c00020f44006d2500c603074070b100da40010b13440d03046900c0c2c1c4001d4158000c01040a00c80d184951a00755101c80301806202414452107190701450301e00f000c80502c02131030414050414694442c03e01001c04440b04042e03050140d11000052601c1041000f144241c0e98000e00040807440300b0707030080c104102c03c4040014007030380c40c52034000b0031800b1413607030100d80980c1044140c80071500c0204841034100380b40039001d00c0012428030710041d006401010014402c8c0400985000d507900d6207a9980102d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 825864424 1250 825863174 825863183
    0x90e10090e071412030f030103050d09080d1403071106190f020f040306110c0a0c0509010e060a1811041e050a030506190b04020a090f0504140a0507050c070b040608060d 74
    0x1141161040d0402459440c811320003041500d01d444540684a49a07a2017a4412034080d4000683e58101940c071403040d40180c041e8030050000e8a510000040800c00d000002c50f02d0040300001007044140206407406450140e00f055803400d02c0c2041d04050313403a4161070048065414203290002c0a42d90340f007190701020480140a00701800e40e00c0b80b5004203880c2080851501c4104100c04240c039041240b0044140306050039034605084c41c05009001006a100d007450b194400107221300d0755600540b84080e50841c1d00080405020019524050708201880700724002c4006004100c51500038000e0403031821180c80034850603514000d004003040b0901c00508243c0024003c60711400700205081c810341011354001c51003000403c000b47c200d0f407001040d240820200c1208001e00c0904440a0004080856082040c3c4648802d01c400ca076000401310840c00b5a5200010101400781003501d079080907a00071200c0300da4640c00c2200a56010f401040c02141031000000d5070752401d580511100c6911 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 825865674 1250 825864424 825864449
    0x50d0e1509160f18060b030f0603010f0209010512070905060c010e0c0603100b0c07030c140a0501020c030a031b0804030b0a06050307050a0909170c031b0109030816090e10090e07 78
    0x3d14100e44d60141c0c0401042c0c001980b42c050014010440001031800b0b9980c0d82e0003120b1904140b03040608440001c1e200d446014014054001c81da03820206071950b507c6011170a0781d0503074603100101d41e481807513004241d1020004c01c484814400c15482400c401c030340941120801d5084408104035404100c5100c040c00001c2d070020f008054105010340816144ca1007110410b94980c2d41d01e201c450f03050b03009502d184102024031105482c200c3cbd06d80c2c004000a00290901d910600042502d426480c031018080c4041040004814403100240030340c03003600300012230740700ca07200d14110503e983c0584d481000d142c00d0100100382d61030003044a0046a90090400c158103140100e5030024050503402030302c1f01111298901400c3c11003030300400e805c4181d007001c0c40e61008034079606907c030260080c011040d0f030714000d404000a0340007081250420112000c110989a21040031a092401900600d401000701e000b48040340007841c1c070107000d4a407111403d01101c2e07040030416544074014070800d540402c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 825866924 1250 825865674 825865679
    0xb0d02061b0106120807080d1e1a0406061e0c020306070207051e1008130f0606080d183501051e0403091401090305161a0a0503010501050d0e1509160f 66
    0x1071030780003408c1d041340a400104d0036548d02c02c2d81e01404880200101c40154a40781c0c555401a80004d280d60701d02412a0300b00901810500c1c0240056480d8040c25415521051b80004d458064140c00104980c024201c61a51420500094445c18075100b0140100340315844410760a900404003084100c000e40716a0a054007004211105103002e0060f05100600c1c6131282d010429220058520502414020400340e00c2d0001349407400d04030018280030006841d80416501508401d407904942140c0040140240b841e55a0f269441003901d202040b0003096800e040c80c214107401c110300c40d080400c0b41c04503400074002c00500b075100c110341c0180010207450041c41000d000c9140e0f2006080e048c503041c04981e849a9410380b900b624a1021000410960b00c2000718031601d83c4160420b0003030340040e5041101d109005000742c0018083e09040c408041001c0100c500ca80c0e0100c61049000300031284081e07054094400d891a0030b075104a4240200c0a1201100908510b620f0860740344050460541d031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 825868174 1250 825866924 825866933
    0x703030f030506040e0d180801020708070204020901052a1e0d08090313090e0105010801110a1d0604090903030507020304052808030f03180715030b0d02061b0106120807 74
    0xc0003c02859119585464550008404204200c010392403501c2e0b401c0e071080348507041081100503900c26031090707004100c0000016003950a03214880d43c1030f0780158a8442400060f106401068580d0110340b0b03601e00c0e0082c00440500395040241d50500c00c4e11801d0144540c40760f031102c00401c012000360b0202c6c02000319181305d044d001c1d500039080b2090741d05000d04990f034000d00c402c455101c2c91240b070b1034001d00b1200f1361080c45200d0042034200001c00081203001c00828643c010724510f00184401898900707d80142202911300503000200007a665503194151030005158444c0c068000a140c003001910b480d000004440039217200400098040c00304140741c0c040983d1203c210380081407040130014040703800f040500482c0c41c02e95034487d164071301603224103039038042501035000c1d40e07210481c10081d1803500c044030482c0801918000c20303048900e03000300310089040c0c80f0003900700c500015076a00e032551801d00d184498822500900c440342d079940c05c03e0052408840d000d4404e9800700048000107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 825869424 1250 825868174 825868181
    0x1e121b03160c020402210f0907150c0812070f08010f14120604030905130908030106051819060e060705030f03130b10030303140f0402040b0111030d0f0e0703030f03 72
    0x50038507000b0301010450303011500380d030085948241a00c40c0d029644441c2070010341c040e1790021480c0c605901c03914040b02180d0b9140c0c0c41d4800d9042d80f01e8856114000300c0e210780107070582a604174030160b0b92039120604031100c120040312403c00140710320095400040c85552040e040b9440b840a0790036143c02c5c40075000c40b1003115401164009141458081081c80c00d0281a11403800380d1140300380949003405000b4441106501807044600e8209c503080000c1e10380c020703641074402c10b10300305440d0821640c3d01e41040202048182c4c3c030038800d40140c07603040d402110180540c0c0f0b2669401d01b43c000c05c0000c0c41028056200c000341560414404c95400540903005198010016010351018014a4075280301c5034800341c03180c0b1009031002c4018000e16806008485540703072041400680d03490402c4c4003213085c00b07020304004d100d192581c1c00340480303a110326211408040c003074041d6a0f9034140088400010f00800e818114081d060188002003040b0100d1503600b103c0d00340d180d0340140795400300120000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 825870674 1250 825869424 825869461
    0xc0f011206140406080604031d011209060509011506080103020d1b0e040b060907020c0d02061b06040528030318140a1b05060d02030a021e121b03 64
    0x4108118030014492035031401503200400c203180d0324805410001040c031041d52915081031003182c0c403807010301001039408410140380302e01c003041d00030345101d000340101c2d501d0441c56840d102d60303410a840300c014403402d6401135002d4a91040204800c2c0d1520624010305503142c8910404900d002c401000541000850000380c5403140403156400c09640e281c0c2421244907821401d000f5160004020800c201c044900e500144115001d21151910703100003941d031040800d03018060f443c104815002c540311542a81c1c540031643c01c091007484c01c00515160345400898007505c0c10321903040c480c0840303140031420310024441c1180c45130f045030f1341d510306601601b6055101d10001c030010003080081140b0259040c4040081005018011400d00f40a000144c0c9100749011400e107400b800c000e15030345c0301e046a0200341108000350304d0750b031500400301c003d00502c101010b0b0030002c5070b122110840e41800414401100700f003108184d4403484096800450018200c02d82c04c03c0c1040443c40600c2c004414402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 825871924 1250 825870674 825870677
    0x1b180620030d0c02070303020d0503060918012c060a020304210e0d0f060b030105090601120501230405070602030309030703031e0606050c010b1c02011112030c0301060e120c0f01 78
    0x9405102104102110b018614940041c5c0000b802070040540c1130041c243c0303c6c4818503105040d4240003001032242c40340980384039050200f400c01111420000e403c0080c031100307095080511110500e44d1024858508189446a0300a010011350301c82104e1094034010380d008000007954003110500260010001181841840035200000381a07030b5403c0003000c1d800340305407000e0300400307158944402501d083e62441c034444e03411303d01000080000001c0d01c60441d10b1200300c40e1a901f0090a0290040184560001d141500480c40580078540002501c1c0075500c9a4100c52200795a50001c0380ca80c0001da0704120b07a60030030000c01c00820301c42d400214414001d00c00001c207060031034800350110380c415401140800c0c004903581401b0030b401e2140500600382900ea40004158811682c0d040103072a1100174103010f100d0504080441d400c000d064024402c1c44080e40d5603003000203500e2203603003092250000040340c0c60a40d02107410151b0f20000b90b80158401401222135100400801b508460302090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 825873174 1250 825871924 825871927
    0x3c06050402130507031e180b15090c03071b03020a030c0311100903021009030801030f140a03020a020a09060308030f1915030605061518131b18062003 66
    0x2505801074401c5501aa0442c2c600080c03004281c8403050209404c0d01c4000421b43c03400003040f0301c00340110010946107a101d029881155541d150a083c16005042d02c40d0300007003071000308142d0807440c1000b98011000c0f901c45c0c0f032040c1c9a800c407000c1101000308004006030002c0d200d88000900405024408074030a0804546041c1028151b1b482e200f41c0b000e00300745043c0c95616050625805000301c484001c848034046c000540987c401404c9100f061000622403030940030060107000d60088500130f0302028000b034030f02c5c1040300d0500940e41d5a890406038841c01c2d603114005000d2a15101d504101ca80c800315050850740e4517410300f110100010140710300711821004c03061940030140709215849034002c10b4088464254108201100d000800070b9010b211190710766185074036410107452118024103521510841c99802240b6605042c00c840e16103903060484112229400075404040072841c4c2e6a00c1c1408600c140c2c0d0084480b080e40705450120b00000c614244400390044000d03c030b0445801160b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 825874424 1250 825873174 825873199
    0x30108010b060931050420030610050d0501021b060714040501080a0203100306110d0e0d0827010c0801050f0a060f03020d060f0803031012051c020a0c033c06050402 72
    0x844c2035404c100d404403681e0342c101e0302d660790180c010780200e60720520560042485280c02c0e9400f8048020700c1c002c2c10704c1a04078403442c0c8100300007501140c5410b04841c124508540c229000c9955408003074504034040b40070302c0100300a1400e400260750407120140d45880107a00c0380e1100e0802580b001d00078040c22030740010080301013081d50148444605901d0308407541c4400190100c0200e800725a40002d44c0d8014800c0700c03c1165200d4000350300452104d02c41009000c07003c01800d10240d012820035490350038604030380000d54205a09030704a800c00d60b41003c90094000030070410b01720502407000071400045100004900c030341d014003094280a500000c2c52612000f00c0d5054841c139901142841d0310001c204206604003442d40d800134100c2d0103d6404005a5941d0300b52299954440494600021082034a55500c00c000c41c000f002d402c02c210903c65500c03410b2106c02e8110911000c400d070007031280c59440583d0420440554040e58008246000001e69250030140001030810707130f40070440281c0f8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 825875674 1250 825874424 825874519
    0x403030f0b0d050c211b03030c01141501050a2c2d0904050606040504030905040203070906020639040b0d0c0f050c031c0204090908030108010b0609 65
    0x4010016014400030190f00d0110000c00103981c0c02044003044121799040480704040d40014580004001c074101c41c0f00c503038540c2000c030780b460003007403500196903003003200750480314080510345800307901801501c030404001400159424403074000c41e0300c00156201d150072200f024036680e01c010b00c403180c0144500303083c0340c0c0c1c00181050400440981e80181c0361071510301807002c103105040d40b0303c020340d080d008070320381912016280c00c00281614003d9032100f002408245c400c2000402400c80103004544a09100c0e40c02010018a4000c580140c400c0030b000c1380c1c40109400c40300350444c0f9449060700d00c0c2c0030310b456402240b8480003440607003070505010220305507002c907003c0c10581c3c0c40e8020010b032076180d03000c1c010111603581c501c420620000b000071150941001c41101c8180142c091050740d030841d04000c3c50f00900c5550300c48003010b403601c0f0407581009000c100031412100408001d02c550540305041110a00c603040d00303e80d11899a0084a050030032415401c2c41d1280c2d4034501c090311002031440c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 825876924 1250 825875674 825875689
    0xc010207050115080c0d080a0e0406060c3c0206040b030103150f02030f0402100e030304090c030f06050a1503060f09022701050d090c081213060201020c060403030f0b 73
    0x212020b0b5125041e00070b01c420b004a000c07008001c520010080c0c0d100342c1c00402c0f01c0c00001c5501820541c00000c544244030b0141000c0020400b0250080005680c1c81d400200342109001d4201d4002078541441080c80000c0081071403a441901080703c0111405a030402003030100d100d00301d811402c00e000c0001c001909238080d40c003c5d03000c0c81c0c504400809642c4030608440300791f8094221700b8410b02c14405070084c3c0100855110754140c44034510308095000a940ea100018411a4948000140852856896040140022100d490a0221147152095202a101d40e405415000f414503501040600f0340c40d000600c240b41c0a08002541c00d8842105141c03103c0c242d003000d0000390300050b04181e03540c41352000c00340b034502001d10003000c414003000003400d510a48440c4e04049480b50045020320140e40c044200400b13190b801ca0f00141c00b047e00d00703207964105040c10a42100365482c00281c450041c000c8441101240c0050405581d580d40d05800401e4145040000d0720f90b194600102615101d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 825878174 1250 825876924 825876937
    0x1020111040f150c080403030e041e0209040c0e033a0c020f0d02011710120b070206070503010308071b09090605011a0c0a020f061611030c04020705030a03110c0102 72
    0x1030310480341c2841c040500e410300081d500000c11003000c4210010905c4c9a09a4060300da141c0380070b08500281400140207040030003082403041c500030070070700054507455004001c040c2c4261814032000f0034051007900c40614001c070898054110b03200e10746002034400c041d10000d511450205400070502d68101483c490300c25000000324204000382d5055280803128100c2402007101d80d44601e0180b41d00080000c81820150544d91024001154611140140a001409511810748401512410441131600040d00c07104054000c070400306189500c60022030f810b0b00c1d0492025403030194641d899075000c13510080580f101540d1400041034203011400f84910540c05200d0102d9154101943c21051613032481c0f030f48140c004101b04034010030402107510540d094044400701c0b02080101d002c240c0d0351149010b6084122a02d5440e40c00f04621a05640b03d2b9620a400316a0b52440c4a0140400c82c815041c0c050920703481030103420340081c03080d000310340300c1a451a0010304042c0782d000020309903040f05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 825879424 1250 825878174 825878189
    0x405090a20011709191106070b0a0b150a050703090314010f0c0e0d030e04140c0a030f050c04120f05071d0a111c0626060f1b090102011104 61
    0x4031a003076115a80034442110350054161281214200400220313a2400102c4940350501720864800d01800100b07903014004900260080d40d45250704d241c00c910001d401c4808070155881c11403452000e00b0484646507403062501d0400b03141c05140b4400340c80c030f90403080003242049603401010000a031080d040c14103550090300045a44c40d4030020040c141d6142180d031000b0000d00d101c4240050f80d984111261003a01030900c60013849608020802424031603001d40d04c4241070030140061008180c00030000d501c00d9940c100032075030f00e2a5080e0103840082d24080b2004506010911840d400c0382c0600034621300c40e0843c614104e407180d4540b07040626540c0302030035030110825100c1c6008441c047c41a48a07010110800c820490b5410800c0e00c0e0080801220444420001524106002e9441440030b03054003410380310329111100f1755114261200c1d190307400034001e031000b0800400f00c0590981c0500f54403014128100700355514103405410103080d443c11592942c521500b140c4003d0018405407000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 825880674 1250 825879424 825879473
    0x2062d0a031d0a080f0d0609060311030d02070f0302040507050702040f2913020a12090b1e0f070e0315010e0403140c031e09030f0c0a080307020a050405090a 69
    0x440d000c402a00b4140300d000150354101c8441c050000d054001250100c07821580140e85a2410112410050a07507402140802d40740c524048244031020a402150600807000c0f1045580e0b40c040032602d40c105e601c180101804c5400c0240010300c0d003500201c0c0d10000503d45903003051700580019050b50007585049484c0355075400120f040e0305020b01e07002e403521004400a400a0301718000310741c1081010040c180c0d4140d0100e1041003032407286107081c1c80b504024a042c44803070b08030b0400b196a8072003075449400a0340703021070b500c0b004408952030f548583c8843c00201040d64644005803840440f4020442d8035000d140611401c1e5034403850701c0c0d0301807c1842c0c07000410f032503d86400b400c0541c2200d00801d035071200384815042c60900104603808600391126403580c485146058401034043c202d8541c1e494020380414680904001a80c04c016941c115050700c21a540c49514039101d20403071801075004400342c241802642010740040d070300b28400900725850071131281c42e04960951040d00e1501c25141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 825881924 1250 825880674 825880691
    0xb0403090f0602010e1002030a09081c0c08040305090f0418080c070506070b0103111c1416050f0103051f060c03020c090f040b04020a1a220302062d0a03 67
    0x4180e64100c002d0886030000f00007009240c1000d941c1c90100a818154041d0004001111850b25410900b205940000d000b42c9911320449405500ca60008030750b044130745444241c5e040203201d68030b0640501e400d6200c20340713072100120074445042c80d0704020741e82181d224a0224000521201c003d0301c0301e809841c84d070741c96400301486030f8100300f00740c0d018500c40c0303a003401550301103510000c580d8112076000d01c44940448200c40400c8103a501400d8070300f4030340c45040d41d060521100d00764020300b81d035403181560a803645145400c200d64004e030103900e0b000401b81204a0081d40250310454004030031032143c1040001f08460b84209204036000000003407040e8550f1410181c0411004103002c01c201d402d50a80e142c03844030700602080050018000c800300d10301040654075024007120182161a48224001005c0d907440410b0758441058060846d0071700c2c00a00b42d03640b103e400d61017901d034010101071030012440954242038071f61040f080c00f400091010100740d0f60301280108544c46031604d01082c0c0e40e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 825883174 1250 825881924 825881939
    0x9020406090603110d050109052b080f0c130302041107170f0306060a122d1505042304050c041a030a0201030c0201090b010308041e060f03090305070b040309 69
    0x46259100d0208641003a03028800602c40440c0d8600160040c0d480c40317031103089810031a000d8004040050b005020354001882e0b5000701d81c2a22401c7c000c2d2591020b004004d2303100480d282c140c120b503c0700000407030b6000b00d11070300450f8000309940b0305003100c1040c8894880d000101218180300e00041c0d0311800140300381c01c00240c01301203c1c3d0310407044803a03401d00943d20500100c500c8001c1816104007000a048402c050003000030444102403003100304800182c108104018502c21007500d00502420310020086801314069080404040054603134114606014840034010714582183c69961920701c00342042003051a25200e6802500201170300c00c0794400340800c4507189020100760040c1008140301c143c600040f64140c1039420300e00000e108803888822801001c600d80c00034000c542c02c40c00002804030000180050b5080c0242465911036144150000a2094810240403490806116001a000c2c5e07000b00a00b41c024140140340c08115134840000140032102100401ea440f0428081c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 825884424 1250 825883174 825883181
    0x90a0305150f0906070909020d02040e090c030709150e060a08060f16090b09011202040801090f0b1029130b0c16080c090a0f090b070f0305070903121e03090204 70
    0x1c03180f0300900300606010800901101242c003e021020703170002440c1c04c40401d03543c100c03001025500034003003a900388107291325210b2801c240098464850244003048041e40b0f8400c542100740e0510f01c4c480d8252920b24038403804170b4001c1c80154001c900c80c2e000140e0040c01d000040c0b145501e41003100c1180340c07904000c003080380e83c02c60301b004011002606000341c0e00b11001b21442ca20003400c1041e03902c041c0e4840c44000e445550802d00d00c0f5400e04560ba410005030740f03540d0030b140344109000b4038a9951141c084540045911880004460402041d0100842c0409401b80307900c0c0c191100b450030f0b01ca01d40481641c0c00e2a4000603d041d800101100d000009010000c450140c640b00940d08034a40451265101c4041c03178450304c50040f0b074010070030928a0342c3c000034503420841428059088241001240b46000720790001c082203981d440d011129110b4880c551040c0c2203901c038200c8150441e243d041c8800f1115241c01c050203440a076900d40307400410302107a00ba40c00c607030340440c448200f8814881035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 825885674 1250 825884424 825884431
    0xf020705030a1404060522272304080d0f090b010e0f01060e0f0a05040c0306050a1e0e150301090c062604020d02011e03020414030f060a02090a0305150f 67
    0xb14003007403100f171151980c001c048410410f0084107a2000c1da90858181840a010360300280104e0000203c80c444041e20700150401c040810400300500341e4417000701102c1480002c4c40401c1414160001000103801c00c2c042c01c4030204584002811200142c4110708488081c00c081c1c41009907580104400291410710b903900402c0340c034400c1d1043d45000c5001d401102400c6000c0e11072040708040303100c50344624030400001c20b0020000d0218402c00310015008144e10b0007103600400d42e4441c0030881070405541107025040d84002c440300075281c0b02520b440305030040c02074010140013200b6680d1503070b82401204d070b00360302072100c10036078900c0c00601900b014012070381003000d80c03030120160b007007260148175403607200d60180d8040d42484118030049540f42c01400c444011030002d82c003194881c1d076060740134006440240300144c00070000c2c4010144e4be62089029122142c0c000310005400102c0d40d0003408038154081c114403a00c6403a83d403001c0c1401c7d5221500c0641501d403008100c00c0c000f0b40b001c020380 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 825886924 1250 825885674 825885707
    0xc08100b0c100204080a201e220e0c030a05030a0f030f0203072106121e0c081f020f16020a0833040206030103030f1e020102071103010227040f020705030a 68
    0xa03803844060200703550303a1904c141008030b24040c124441194a03404054149c041d51001c00040b0302a001c64400001d14800000d1849485464440401400d001580c241c49a03003000095003402040c81c3c040300c440c10f411500800b05500c5407915002c0200c240080c1d4046c103403d032205038840c50a2011a031944000b2481280002e043c10b00401640341b000c0728080c0d41c1a0410315501d10203102c010003d64420990300000c1846500f4800001c0412020803006070300410101d8810640590403501d406a000e0b8050000b601c8404000301101e0341281651207203202d101501c0c1c05a110342c3c5000d1941846150503050030700c05141240d11a030116202415200c400310076042100c142171540100c0d4060005000050034006d0360388445400c9402780f000c01c401c442000042e0140d004031104000c0c0070f900440003c07114018240c09a40e05890107000f62070801b058080100d0003021420290943c42c40c10400c82030b00943e0f40c401001f1001f9030b41c001410404d0043e401103036a100c9444c030040c425842446c5000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 825888174 1250 825886924 825886973
    0x9140307060f15050913050604050d110a0b010501050702040902040204060504050901080f0309060f0408011503200102190f050d210204030f140c1801090c08100b0c100204080a 77
    0x90518112150f40b02a24425520980c0c6039440aa094458000d001d80c05441c0c0d114107070810040210001e004051264035a441071840c102d2070002990352007444800030441e2207400d0051007107511403800f074400356000030400326841d8504c0d0040f40c00c036849604140c00044000505002c2800c1550207240104001d400805140d80900301054076030190400c0030b0b01c90500095143c0e03c001240c416100a000c10100800210740c1c070032140d010304240f5120031200038880c1d0b41d9007a0810b0440203200301c4cd0b08180c002d011582c41990f40d0070071580c0c1e10780040391002d0051071603801281c0c00f00034071001d180654030b40c0006414131042c13401f005c0c03003910089042d0303e004010138000183e000b61041b007240d074021600c8544d02003a180751414020300c1b0031314035085010103141c0c00750101140c014038122641d43c80c04018003032038802c1c12180580c049456444010480c103041098a2075a4000c0c103001113224250b441c90042e5900e002c00781e0344a46d0002140f0b9010f5050304040c054000c0e00c041c0314008002c200c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 825889424 1250 825888174 825888191
    0x1a190e0304050a09090804030c0602031803010e150a1e06050406152c06030412030b030c0102030f0a02010e060403030b1806090f0402040f09081b03040b0711010309140307060f 77
    0x60240f15080c014011540c3c0c5a0301881c04001c0d00070207940142d0b0384011990f6019803225402962500040044600c0702d10402c2030701030908040c815810b0f40300d80200941070024106c00c01c4081083c01034891454240d4400c2000c2c170b2122130000ca403050750495200461030624000c02c1100703a4070980c009902e00746a801e4805201034101c103a81c2001852840c520a20040b40600c02040e41404140b01c1c0e000000041000200242040e180b43c0030300385a102080200745440506a5a1202005541c00f580c010440c58040850394400b429104d5050300c0046042228000580e042c0442603030f084002c82d03140c0e802c506081c1340400c4441c0511100c00f100c189a032801c0c10004940314000340c05910801103402c0070a055448542100a40110b8190140306115580c544001c440e44071010014500b81056090751020401000715000ca60610b1880d9081c02e02070b0303c1380128802507064a6060543c0c0f4490f50300000d41c100c90681a10315102c015603100d2215061150542d4003142810000038030740b5484 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 825890674 1250 825889424 825889429
    0x90d271410020d1704060b040e0a15050108071e03050f101a0105161a13061413030807031e0f0c0306052d040e1c0e1c1a190e030405 58
    0x441070380300d9501904e041c081c1c5403800c01900074458000c5080e0094140710108030b00c4070001074080051441000f003545401108028079085400c2070280c0c0d141c9400001c01004922020302c00164282110086001d0290703030703903a0b92468a9178540d1400c0468101c0c00050100d85454858404491202c0100740d46440c88000020400d10682c2d81d6800d0182168446e10240000107c1d10841d460255024500d6414448902d042c10399080e10701311021420f140d030302c1c11440041303608640030380d25070b002c00502206607507003e80f0301e15401498801016a03400c00e444034480840a6840e242c046103200050080642c5090026200652083e805042c100042001b154644c0e180c095110703100c3c01c0750703440c0d429408036001ca240078004250359401400c1c008041001c14003c1840d034048445100507030180c980d804001d40325036820030300b081e0b1701c0000c180114008000070103651a14a1280181a868880140400e581400d050f50f01c148884001001c030240c552491190390318401c0c0c03500085040c02d203403000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 825891924 1250 825890674 825890687
    0xb01030201050304031e03051603090510050603100908070303180b010e0a02090a0801020d05092b050f1809150a031211030406020a06060608090d271410020d 69
    0x1e0410000100060905104842e2403e00901c4001316400307621078090010050f250503940d9500c1608010403110036140240708004110340c0c004060486090601d0301078000f440010601c681600440d00ea5951980701482a042414492080342c2d4460511b402c0040c110741116600c042c50814612101d408038114442060448142951390b45d003540d81c02c0703c0039000e40549540706400012000000c258141c0c1074006e0004c42104680c10041d40d5900340020350380c0d0f088504411442050031004800c403142e0180942401403140c04c14510b0148030b110018000d038000b40300c7c0e09048042d5007644005192002002d40c1005640700001007a0701c6000000f0040011840020614400c1503280c81d40c0500a40c822064000c40f034080d0380d21143c1e00c0c04040d48030008002c0844886150030000310b903483c000c0d5205400780064034001c01d2003e0310498142c0d109102100044d8100313178a95161020800c60040000142441c1101095044410000c3c00a117452034101a82590000f0010600c0ca5a0101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 825893174 1250 825891924 825891929
    0xe010f0806060d08090301090c03120207050d12090b0a110705150a0c05070509070906020105010506031509070c020a121a060d032303010e0105190806072109060506031203040b01 78
    0x803110543c0c0806480d000242d032013142030443d010350805102c1400e01c03038903a1140045a024900b00e8092000000b0101c0c0c9032000d50094a602c000180c910502050090340003461200c0341d800d040501c15200e140d00e0360b8903002610386c400010050000041104400c0c081c3c003001305800d07a144084165003013904440c0e405606010010002c4600d00d500c00c0c0101006903500401020b13060700c80ca4180710034014908169802440099801c1100024050502e0740c100ca12582b4040b000460340510f81081201042d03020b802e007800c000d151143c040140c1d4449110500030b0500b0700c0303a4050a00249440301c840840c200ca955510f00c01201000a2030700c07000c1084120950500d00384824100c0161618007004082910481d00304020001058208000c800681a2881200d11510020705610f00c044d055469000e108455000080030400880c06400c0300b503070016035106c5c0c48503150f01d00e1203080e045841d060410707242c03103850310144601c0381000e0050484112810000e58034624154980d03085048062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 825894424 1250 825893174 825893179
    0x304062a1b0804151d01020307080a0e0a0602030a09050d0b011e080a0620031603151715011d0c0906070813030c0b04030309122102070e010f080606 65
    0x20203828501c06800340010002591180304035441c1d54542c2019644414114070b1039020507002845098204442108076443c0c2038164001e5192001903030380c1c025184c2207450703807206111b40c40c601401d0a9032000c0b111030240070300303600458030344802c80300081c03407070752558000c030702030381c54030741420082500c0007142c40c103490422844d83c4810383c501c0e03040520030700c00703a004940f2400780800140400900d42c104203580c18841644544281d6141c5035166a88400c1d18641c4440140c000600d54103402900000c40c4640302c50000d250440c2c0d00c14140d400c2c424060104441600001c500414255200c1c0c20365002d04400b02d5900aa00704030b415620500b00b028112284c22a004a6183d095550f03030400c0300c0041d64000c0315540c80702610340704021003072024001180c44c1031001101060926012003650202e0750903a442c952160700d0700c0c8149081c03040b0850113842002800d20100c00396081e6500c1004684800c0e030003810410f2500441e42900c18040c1c0007051441044001006281d0002035542d8002008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 825895674 1250 825894424 825894437
    0xd08180709020c0c06040618051c02130e0a08030a0c09031505090a020a080307021003052a0706140a0e0a1a100f060306030506090105091507140d020304062a 69
    0x403404503490403a07001001c0358030810009000c10008d50201a051702021010642454161104100850040b0188001300d44008100051015191a41c845880c07680340c0c401c0001e102141102e1380742000c0b4268000d4070300900000074000d1841280c81070740f01b00b08140c501503112a0450b0303102c0812400880342c4070546511040072131240391040c4001c1c640c1e264000c0c0000304069450700d80f01c1d181e07000740c007059202d40307011405210114081e002d4248105507007544241e100180400f8040c0500c40c00458412603881845045c0002e0b5081c4164180c00440c4410b001480c039001508074140c070306e900343d001050380264421f800000c03140ba00c52120f5580134642040303185c0d0351b444207600a00641c1d2111540c0d41801d000042d10540551000741a603000c0e4003552099030720107844a00740c2e54140c8115010f070340007607040c02c2e81c51448140310b600404075240240ca545502030661000703400034560303000d09541c00814007080051901c58882c03030541100388603094401c510081c80a41c88020119003d100c070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 825896924 1250 825895674 825895687
    0x411061813091221061d0a0c0e130e01020d0e12091003020d09050a0303061d01051503093a0c0b060112090c0905061912021005090d03020d0818070902 66
    0xd00c40042c031984403810003007010790b80e2200040300c12041c66003102c1780d55804e03a01044030b0011134081c40c450180e0545440903035100e0b60b030500407900507520041038143d6481200d1102d4bc0000c0c0000d1540b030006110104201400074485410806242140c0c501d040d07007007084140c0b60301c8a803149480b0010034100180c0b80c03101c8000301c0c005054004c00080c040c0c020506500101500740e440b07982601c4190301050381000034000724291080302800385035130140c0c0c60488921821858030041d540310740f62000b40ca123074061858030b000e0202c1c2405d05d8903461000031514103820349001c0da600c40b0b0342c2c038251130140000b0322030f510f601c450100b02400c3d04d8104000c1d00d600000c002d1b0141c00070701c079a0303a0101c0d803010701076541c4224500400042d16203500c2004003000d0001c022003009448004c0e41c905041da182d140c8225802c004200c0c00c05640700d4244074040c043d4540701e6603a5002d134283c0d1030003134000d842c0f44490b00300c000302000c030300500c140001003815400d145101d4002681e141a076440c540010707920308 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 825898174 1250 825896924 825896957
    0x50f0402120a05060c090f2d0d0201090510050912100c08070507020f0109080a030302181504090c0c140a140304080c060c010f06060203041e1d04110618130912 70
    0x11f19171404a400c141044803080c0c80e1091445400303940c0e4601c0b645580d42041200c104100765607c214041d0001d001c00341c0500ca01d1801010107260000b0904003a49440b66400100d1307201203c1c1d10450000b038014846005000116004140d030304a140c1c036000009103008500902207002d441030190243c07043c0ca864a119900580040014284290880e00140182d29001740a540809101451455081d83d565607030b050480300314101c2070b1118045401c007404c105427000207041b9421050100000c050741c5002040741c012151903e110780c18042c159003082810852241419402c003d1169401000104036442c0c0c0490020502d08048403e103940e510032200440c0036124030074140305914a4030400164890b00000188111500c0c1e21140800c13190320030000c01c1000381031080c0030b410a8540b607112083c1d201c914070254818812039007001d01d07503800c4002c201903800007030710403007144100003500134980350200400c0c81540004400380008040b0355601d10f18000051074800c18040c41001d41d00003072 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 825899280 1106 825898174 825898189
    0x10e0c041d0d05030a0b060a030c03231501261009050106020c010c05160b03070e0603040c05190314070e07052d0d050f0402120a05060c09 61
    0x2840b900207945507840100840c0405a0b20f01c1e82982030f60b12200504240d4031250707400501c2c102042e00250440d030b070f5a08a81204800f02d450322480c00030b00741c215070740324222050718080c4840c0600142c4240c0c1021704101601d01300c0c040015200c8081101c400e200e00501c10300261000d0fa1044910202c0b2028060180103070404064182e465024052500c00380303118404882d444100e155204108009942058400030b200005204030149d0001098082d59021588d09281d07041c0f17607a031100c03403034120301c6060b01841c20740c42622640c04094108000071a001050110f144402c0b41d00700ea141c80346402034840d00f4204001142c07150303115400740c86900c20b886a0641d80520b01c84030201c5107616424410442c04c42c20030034035070a2103e81c080d41d40510380040014003541414810002c0c2c20706051040402071344580c2d074840200b500020000e0300418003101080ea03601c900750114451 = true := by decide +kernel

theorem cover : BRFrame.Cov 825719424 825899280 := by
  have h0 := BRFrame.cov_init 825719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 825719424 ≤ n) (h2 : n < 825899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
