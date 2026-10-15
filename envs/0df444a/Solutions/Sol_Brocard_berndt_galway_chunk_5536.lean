-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5536
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:11:04.850406+00:00
-- url     : https://prove2.me/submissions/06ca6d94-4f8a-4788-b960-d1b26a3f441e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 995503597 ≤ n < 995683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 995504847 1250 995503597 995503601
    0x313020a0b070f05070f0f230409060c02011109010f0809030c01020a0810060905011407060e12040e091b0d051203240102011b0c020a05040f1431060f 66
    0x40a6440d605629114801c100082050170014100566080a410300e00404141e01800d01c0c0309601c851090f10481400010421250104102006200b0080000c0504004004000140c1c032000598039111102410361401e04c10780e000100141d468941c108060841102d50000181c00d00b0018030062203074559a440a001420106526a4030098145030000704c09030740b02079680c403030301c18850102e405000c0c0d40d90080d0016007444c91018201e58a1136985041d400501030f00d000800c0c0f0b8000c0561400b0312600d0100103001b101c40d0003000308020349803024036a1700c0300320803c10b180610a180114604c241401c0e5a49078085000d407080c0e40c0d107504010f5104590364411185190100c1c0050109100d08107004d203d008a40340a20007081a049400100c0000640040c8880c0620091501e8501150340751900f1901500740603000b88400400c04103040c0103030a40106200c6a00705090005190f0290440c44040c03801c1171840111181d032002100c0300d100004c02d242500c80075140d80c03040922019034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 995506097 1250 995504847 995504857
    0xd061701021e1c0b1212042321030d0f0504120f02060c090406172808090105090409051e060a18110102010b13050123060313020a0b 58
    0x600015958807109a101e80c0840c64600744054a1101809006088841202c22540040000a001640707000c0580010110746144100f8502442800c0c8600901e06044015000b280c4144801001035840d90905035100300321040c982c3e81242c40c0701d007000080c00804001c102415104010b0700d1400540b544124251f401524900d002c0700d40718010b010422062903003500c18600d0b02c1c600b00310360213480e400013515074101178100102002c01080340c0216540c0d9502a000401d4902d00d40c10101541540342a00c4a218040d01700d10750b240d4035070b60100c010b01404e062102c1a400007000b40352000010055901c4e400aa11082d0055a00d82004000a44c10095035a004010490542102c0b1006520502d8088002c28405500d81010310b080000c2d50032401c800d02c0c80f1b610903030309843c0c0484200101d00400c1006080382d4820708041d160100582164001410390302100300c4040000c170111717800300303045040b0040c0c540c01610403c000f4040380d01d6140b0000704184010800320310b20740d948100300c4141d000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 995507347 1250 995506097 995506139
    0xa0b0303092413081e0a061e020c0f010f0c12020a09051e03060601031a0f03030c15100603060609060c05071a091905180a020f040f061205060f060d06 66
    0x50000c2c89080c0040105d03080c0780440144041003203281040eaa07440b49a001001021240c82e90740c02c500c00c0c8076804203146543c02e82d000854a4922007030784a6915003034980102400c0d403030190102c04100482c002c3d00c80c1d802154030740c60300ca44000b498200080d401900307050b00700911007401240300d50b90318040088542d01d03484503244000000c42098103140000e070206042c585450160050000c1050300d0550704e0303000300c0f08010b00030400c8022a06521802180341e10038050b8641120440707041000710307401620100200043c035511021b007a0308689a0340617110214054040400509110740100c9041901c208151040b6640e14180101080305900e440701d588000800c86204a04290b841c0c1c400d201c100d909004a600d11b008041070841041032030520282864500007030708010290100e500146005104698559440c2188601803110307000700c41c001500d4141480c1e40d10194003440703004080007083c00000c07010103010000c1c4c0d0b41c031100000890a84a00c00003c02d400d201c043e0f40c0175130ad0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 995508597 1250 995507347 995507377
    0x1606021201052e110109080a020a0c090905030f0703120c02100b180604050c0408060f0a0606231b0102120406060b0a020c0d030e270a0b03030924 64
    0x1040c1030400480c580e502c6150040105400b4418464203d04010000412078506015901d410304500c994050035990700082c0020340d0000710501c0f82c56002074003102c0c0d2401014140c0e40243c44084040030343c5e0500d040030b48154028480107807400414802008518400c0c00c15200c540005d9480c8000c3c0d4884c14450380150300541c4440910090318042c803026090102e503500040241902114100c0c2c901801722800746035204001b9669120700d8003110064000b49084a2451a10b0720301c02001c03000854242d0f800a084c10300028505000f0700c0c0a2405000b1540c40c034031407881c3c2210a9841d504492800104e6a00c080840c03402d200c0203200404169481000da0f100074038242c10700c0820341d82e075580b1005d05030300c04028803501140d021800c4518041c0803110b010070329007182421103409806404581d40a03ca030840140030350100780c00c4068187c00041115000c2e036031809a9001c482054284980581040190390903c0c5820f01941e4914828506480000c1254210400d5183c01c1002d4202d0301d0f072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 995509847 1250 995508597 995508599
    0x31006050301050a09080d02071112071a07200a0918060e0a0203030403200901140915060a111501080d08060f0f060a110613020a0b0406080c1606021201 67
    0x42020f001d40d581c0016948030030721000350180e64110031445120314074012242d010a0260401c07161440805007000c004000c065510040030601c2e4890a0912415018540c0e446018210000d100213540382690080381e03c4800301f0810400c421000600308101d03900c40026280030610b800d0324071424102c100c5500d0301400b580c0032840c20704212820160b41800b142d200b8210140113030b0300002200e09a0b41e100c031782cac15800c1c602c01c00000c3e41c0285203118540e00070801400071440c049a401003400c80348040741d90700740307513100c00541d040c0c06000c5800c041d801807070811421049134010b50040d158142c002086030511508512041400c03203084e04940c080784c12415020800a80c050f00d595013008042f1500303080d41c000c032800030f40340090988040d400383c170010900204060261a101c03a5505054041d107145145c02c502c220f0140e901104103d00c100340e402000316500b02e0310820b9806459058840314840c1c0c6820040720040e410151070500d201101140c440e00046d160300107000c0c261018540c0f80503075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 995511097 1250 995509847 995509849
    0xd0501051303110727200d140105090a110d050c070b010b09030303040303090813031b08030c0a111906030606080105060901120e0304050639060609060f03100605 71
    0x10f00c0b16040140c0480d80070540c180400b8040e29051082c040c42c03119100a107000340e2220f6400b6041d08690411a814264540c8070a40c4031100200070741d08540c0c1013000681c0e45201e40d03003403001080c01601d412058044c0000c0d030246056001c558080b296098040c00c00541c080004151401100e08400c0000c1c041044010002c035075024038003500206d80d03850f003060021070100307503207000048c00034040507200c0018406124801d011181154503040f20313070940548034103007448003c03662060103c420b1440a800140c04078007000b40c40b5415404406401c0701720150311882d8000031020aa07580c401c050344000741c145030b00d031403000004158a890208200b0314000b400780a0303d105901c190b000e59800c101c40009030703a200004929100c201c0350f0001b8418020b544a500d18055500070941141000a01561040c00010a90780c02d2003003c5580080c8850f110042800300c040710684a807692098020624600c1c1442076140e000310f02030035400e24501d490300081d01d04a03249082d4561507a61b0503090100d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 995512347 1250 995511097 995511107
    0xf230307051e1e161e060f0b01180807051306080303011d0a0b130c0e03030d0218060403170a170f090609061308130f030503190305010f0501030b0d0501051303 70
    0x45160b441201d6090040d070900b600000a10490001c01001217104140e6000017903a06454a16400074801c20810703081c038100707000820411080358046030048001c84000301d0902c0e0428282c0340c10340040d02d051403a0000b40448441a1087e822600d615802d01048075081000514000c085002c2d16454842e9082c52340711300c10304050300448130582400d0a000c1079407100150301d05958030070300d40068241c00ea09030454940e45204405035050000094000001440c5d8002d00201080141011190b0300788070100802da21480c84010690b00321901c01c45003401060025010714841d50404209510406405500d10507084038126800d8442205225030f0f81d904014095000f410080105211f0502000d12801407401c2c001c024510500020313042204802c50044e040241201486124219100c2c80c1503900d0707410052410102107207081c50700c0c8411b442405164129604d43c40910400c50508004602402ca01208980c00504440c0c8013030009a0034880c06104000c98468004459560714000341 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 995513597 1250 995512347 995512387
    0x80a050609070c02221505040f0b011e03020403050a2406180911030d031d070312030b040b181902090a0e060d060e0106060f230307051e 60
    0x40a81045010070140d40d411403038004a40390105c2e10f032003040720744101103d841401e10b6004c0c1181401c240b903165292041040000503180116000c1c00080c844801e00400c80e183c960382a070000e41814824034099000c410005c0c1c6c02442c2d0328003d07142903200e03101c00d483e00410550885404c03401d44640c00f0613008242d019107600801d0300050201c0c0380f40c903058640c07400b9008102d1414a5881c21040e00b0440310f400409200c0b034014065604410038950094014024240004214590044550030203400440d240b0b003680e40c4490300d40041d2001190031001420b1440380f8640044e9610086030403075a44402002c00c2d6005200150580d01c0c2c1040ca90302d146407441c10750030f1004d005010a42d425642c80340c007001912a81144e00c01c4075601d400005600c5c0b00c0c1c003007001c1c0280d07181c0410040c1c040f00c1908044107680c1c0540750709130350310094082200c5480c4201d6182c00e411000d2402e0b4100c4100103001950891030070724010342040448843c500d0404c2101e003203010301d00d00000300514202c80b001d010385 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 995514847 1250 995513597 995513599
    0xe1510090e100e0105070e0f0f0429090424020d0207061b02010207020604030b09030906030a090210091203030e030c07060809010501270e030d0c08070e03010c02100905070510080a0506 81
    0x5c031060070202d9010b0681015015900c0c0302d001c3c001c0c510b02003615486544844200010030901156000d51103401d02880000517007400e034030409500c50305074284800d0050180b07600200e080310426918004920006d807060300141e406401300030840014400d800a00000c5014030000a202180b092000202000d410703041e03020b69005010300c20141c3e8481c4240d808a03600207a031701c803603030307940d1409142980318020360356a0012000c001e100c1c1c0d0220070784c0a41002c80c800e450103107400c801c1c2a4190780304240dd02c1000c100c80344000284000a00c81d404c9044800441700441e810016a0180f19081c0801900f00400080d940c0701000180c041c03d01902c2d0050110407420115081c0551041a00c003600200c9035121603190510b401031550100101c0c0d0b030042214104100c684a0900003c1c1403d0013510103000041d08640c0701c07241860306224480d403491164006200b0b44c40c51454500190410410a851038040c448ac00990f80c0c442e8610701c16640c50035030f254005890000d800e18200c4002030b00031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 995516097 1250 995514847 995514851
    0x160506060a150e150909011710020f07260301090c02071505070f03020c090a050a0c0e0307140604030b040303021312030f0c0f050109080405010f030e1510090e100e01 73
    0x142d006182c00c41c05807500c0340000d80700d00b00115042540d80000d4414001302c1a0004801c0c0e000003240c041c1010303c0d030f51032440340c001e48000c4800100070038160300604903407690100e4100400c0380000d1803a0a86000e0300d918001c020080560200032102d5600268400c4034181d032a608400316242d8180700440140488c1488050318296503000241640220702c0010115040383c0410340030b142c000c00003600d1840c00240000ca02c5e00e03040c0a060040d02041c0c070f00c220f0700d034200307003144040901508000103075a2015000748901d600d8500f45240c05282c41c08071070b030040c60400c03000c40811040034196100304d0182d100903a076003400c0c0c0c80502045245520015010040491070000070394403211304441c2c7d4040c0e02e0865190010781c03c005446500d5101c0042166280c00e0aa100300142718020f402152400d0320b40b6800420602426825100c48110005460700f00802e006919004907546c10b82007082102c9010501c0d8880e6403420448000c3c2c8411086a4040038151b08510000d00401040d0b07034440000f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 995517347 1250 995516097 995516129
    0x1f060e09030901030c020f0102070609030e03060415020315120609191a060a0504020706051b28020c030d03060312140313060f02040e01030b060307031a0c160506060a 73
    0x203426160300a81150300e040680721030001c03510301c3c801c101e00d20350080860f000b103645803105d203002e20080140803401c9022803683c0582d84024a40854050f1145400004200300f00b1500d131a984020340c00140b88594030a0141c0380c100490f152002180e42d0303030701c81400501c2c4508010a0091410104607400002c5800320307411540060a000d40c142c0092a150354808a00c0c0c483c0d41c002a000072168101940141c4081014400e00c800c47c0c201c03a001e110030000440b900d040e10b081101d800e10810800d4090400a81074402104402c580e421005298510682d040000c1c1040080d05100c440340c1c010002035107445080c4184030680c840c0542c1e040d0582420610310026a11002c01030100070700c081d540103001e006520501c90075800030b0840d004407050456480341c40d4000030209820a0105491104040000440704c1c07e00191000980e900101004503442440c1000062040700a1a0f0101418184408204c119090340150a814400d901401051403c1c50030b2001015031130f40900c800c8803600d0700c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 995518597 1250 995517347 995517361
    0x130b03041e150504050a08070609030e100905010c0218091e01020310150c080a02100f061208030c0d02030a0614030105060907050a020111040602010b01140708030f0a0b031f060e 78
    0x2031524030b074030700e46102040b20740e101c1c100300e428020038040241000d007002814800308803030f9074031629201c0d10940360740c41c0c0548080103014130301030052169804038800380320501441d070081241b82446880103181400600c204410104001d50a54103041e0035031003118101e5412120310040944488010001c60851500040ca0502001e40e8454201c1444a440340d042c1910311820089079010341010322181d89480f10a0029940d0007800e44450296103040702000031070520b401180300f00c0382c034042311038019500368503054074551003c1d001c4602000100304100181d00d441c0091807180c0380301c08000601d1868501d00550341000c59903081d02c282d242100308425942e0741c00f5000d03041600c0b40741203a122150380310f00343e0050134410800600070f003021600095055054001461504c0e00baa01c081e20350f5022514800755005031540201a0001400000c0c0390001e001d203100e50101e0441c80c0450903030204000300c0c0c1001d020501d201c18600000b0001140d0900d14024003004154520204444e07180c440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 995519847 1250 995518597 995518613
    0x20601140a330e0f0904020901090e030417100b01110a030e120105100618030c14040908070609061a06180d020a140123091203130b03041e 61
    0x200401c0795407241203042c120160b0041211441d0028094550403412902d00005400741e01da00503030074861100c0e0f00f1641540d041420700c3c1d600036503014004a455900300204031001e0701900c48151043e110500c80007a50ba50790010000c101588003003d05680504204810b081c1e0300c41e04015818803e0300503022038800c9000a0704201c55816152054008680400103000c1107240800c038149503092205000703002c000001c1100840310b541d00c030318140c2c0030f0b0555003103100d82081c40085c000c9040107800700501c0b200035900aa031601c0c000e1001440b40116503030301e42c26030030202c8182d40050341c5254490801003288603010026640d101d070003466080000c006460f034401e0031101d0345440818101c40d040781c2c4441110003940c82c1c4c010100c0c0e19031a125400d1382e0444810225003070005200d04682d9441541c5c5111311001d00c498001c0051a180e000801d00850306d04604405020f44010012403551380e50700450140a02801c0c0e0405942e820030f810244c245240040d0214540c6e400b484070140000d42c20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 995521097 1250 995519847 995519849
    0x20607030506010e040507020309061b010c0c03020a0620030f070f0504050d021c060903120506040207020d0803040507240311040617090a06060e190e070b0c0309041a01020601140a 79
    0x817070300800d6a030b03107655080341140100b0341c05542203500440c0345007207001240071202221140c00002c006c910b10145003140e040d4071280c2e018000d80c10002070000464200c0d0049110061010300554188082c030320940540d520440c1c3c0b80044030f0400c0b0a00000f154050003250f128200761611600781800e01c80041d43c04000584001c6c89034900c0748180c0e000002403028840d00130341004c410080d41c002d80c1130107450420309201300005246482d001426514051081e501c209030090510149200740c0d5440c604a80d00c043c0040d10035200d03491000826208114001c4030345120420040809482010f000c5c0c1074130348414001640036800e000a03c00d966000302021208140c0240c000b24640350400c0041c20700556441c040c20035401c1a501203072482002008078060b06900040031541c0780a100c041045603a0800226030541002c13004201281a80c03002d001c694803100c0c00d8900e040701d10b00000d003c6440300e0b06088004464101d4010441d0b80600c80c450044c4401101ea0340341e2405a07002401400903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 995522347 1250 995521097 995521099
    0x30b040c0f1e0201090206040311090106110a020108130c080c0a06211d03040603060e090a0f2409050601030302061803041a07080304030e040509030c030d0e0c060a080106020607030506010e 83
    0x40418110040740300350401c10704103401070000c0c0d43d00c68480c1000b4ad0382c80c600030143e501a180283c0005031151052100d81601e107441c0c006020f00140c594011902600040d20151029001d6094400455a8110010000c1013900000c001506010f0140400c40d0155840b03041485101c00200c42100030986045201500403a00010a51525102c558100e100b07101c540c0f80f42d10002c1004240650190301240564403400e912403a07640c0c030050304c1c82c0e070303a01d550344020480502d600700b100000e00e140b083d41400d10202401e10a1051400341e24200f10740c8000019109988584010030626030103005454026910020241995840280c01592885184500d03554609549020300309210490f060b00c0c4e00380c0e0300505490340c1c0e0501f400c0051401000098941c4510716082c00314401c5000042101e12090080e4043d45c10202c601050078018848080c0c0d0b07a1041c042e24154130744e10341d0340d00d009120100141e1103c0300603504006009103000c1b0001c04400515240000b800318513030b000300343e40110a030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 995523597 1250 995522347 995522387
    0x936140109080304020409081908010e16050703080703061205010501030b07031401030321021c06320609030f0f010c09060e060d06231801060806190503030a030b040c0f 74
    0x9403e103023000f20707481500c110301080c2881b00c081001960340b202c004c81c1210b03c5908007038040e0700c95040d101014040501c440d00030402c20040c640010340504001903002c0c10500780060155074540c40c0c05503c0c1800fa5081b146030355148014030411410250441c0c000e00e81e49030030400e95148030192144030700c06000181c20b018507810079000e44c0d8102082c46090f079121600039502c4010325011032030a03404c4144d004003084c1c145100032500511904079010010701580f03403a5107202c0118419034064280005440d000b0300100711030f082d0f54508001510400825a00030880c1740b005500603421100320381404000c122a01d0010000194000010001c08400f101c146aa5840c10041c8038000c0c441c90b807094550f500680d0404c03200030002809612080029580c245900e907807003840050010090140802207042c80000c44c0c072904100c61a1030414038051441c040b11501c0d080020b20b10b800607070807039001035102c914441d6a07080034041c11814048034202480d0b80e8a0080c001345c50380d0200041451004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 995524847 1250 995523597 995523611
    0x80601120501090c0609180509060c0a020109051b0a0e0c0a03021b0d08011d1015141305040f05070c03030209040b130509160f09361401090803040204 66
    0x80800c0d440010744550201c41c0904c180d59034207001d0710b40f0045118006c1004208201c100705807483e402014410201c1c3c03406048140d8aa42d062901a0407607814601159070b10745071a00080c03001c0103140403002c0720044100f0720341842001c00c40c0010041d080042c4040300310051200d01a50441515074603489400c0150320b541c6800007000850204810241003882111b40c5c0c01c1d40c0f50342250015058543e01d41c680300030900768200c07407040d04c2c000351150325401c02145d004000f400d04c0b188004180400c240740006180043c1544600190000707021400031906040040009240c179105000a030442101c044c403240c0b8241001030428152400c014060640002d015031266440c6c1e4461101e403400200b07030031541541040510010401204c40d04501c1c8204880488201c80e03a0410008652481540822903400d00c00640701038240300840010291b540b9140c0e520b01001550f000220742e001c82030b0111159050308005400c0340006041e41c15591406889001003000c3d1421664804c2d010756002c1101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 995526097 1250 995524847 995524853
    0x4031115090d030903052a0d211806030605180903251218152f0c01050f1803030405120d0e1503071107170d1808060112 53
    0x24800d0308100c0d9406515402003404050300401d400041d02d026104580341240400404508081f90b0782031085061400140d2004500e89101000c80841c4290300d6210b01040840314814180000003516021440d503101e4881c01c003080391001c2006010521b070502c08145800c000c43d180b608030400c9584900f40c0040001c9600004000711054000d4082940d00d0580401c4815204100b031035408030707440c00094071020052032164400b81c80c42524030855000f52442d00c1541124000d0f20021101030081031115030007005001095603140400329a40340f01100168010075041c4003100a0003414800144885040105040244c5000d15000310980500d11001c100107403550040d40c0c0309940c4013841c05104201e0300e10100704178000012a88598411412050410000340e0b5401d01038072081900703100243c0042d100344000c4071450380540c1501d041c2c54803205a020f1030960300724070200e950f12003918511620b0384074410b8050f8000b00100303100c406051000c5a510703120107105540755074401c8811074041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 995527347 1250 995526097 995526139
    0xf0906040c090921030212090106031112190c0303021606080703180c331b032003040f090504020607030507080f070606060801061b02360f060303040311 67
    0x21135410f0b81115888000c2690002c01030b5122042820645928601140510340140541010b0381d50181049220006200500140c5220489000c409109038107414888020107046081c9490250007205805070541c1006498403014004141c10f0500589080141d1a4441c1c05181c00121030302e000301384075251203a90920714040703090250a03540d4256001800b4080b0303048845074a01046001e2100c0c2d44605a60010002c0c1c01d154400070442c00c0c0c11241030b540c0000c01e0084160301ca8100a00750b41d050342c1901d40384408100a203402c0d9480000e0600207030f800150328100809200404ac8910b240550200c0e8060107040760080505c030000c502c000801c81c0000503182115000d089450b03d41d001424403002502c210720440000c684400004240c842c4206c400100701c110007554020000d01c03942c00d00a20007e6854500188260020041131f19581440c0e03418001058007000da1040c14000d103548030003007028003500d100e544200710400004400e44410343e9890310840307020905002011b00c00755 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 995528597 1250 995527347 995527373
    0x207030f030c05090d030e18090a020a1a030a3222030e040203073c050313020d1104090807020306011e140303090d05010507032414040e03120f0906040c0909 69
    0x10102340407020000410000565401002c0c02128424040d0f40d0f01c240304a60240e0400c01031210385410800100401c1841e0008424010801c4c40c6070707410241005520000154000c00e02110004542481003000710005880c1209010000c40c40f0f00c407007a03545c05031407680c01040c07041c0140d801100040c5d149004448214040400400035600e18848070303101074009807a034801e100303400d14000700040b50380e1040050f6846540190f1075112124003d408010106d0007958084400c40b901011420b9644c460340540003400c1c0c40303900c0840e11207400b0b104060170000160031100006c40c1c001810325503c02d4884609084504031110b040c03804c070228003c079085200b01c00100790031aa544184104000d4158401442080c0c555801c20100e030700d14100c52096088001007001c5c5c4102c02109116100e4610200702d00707500000d10010303103c5180641b0504503000341e884029074013803a0b010040000361405070594400c04c504003920052420341d68414044803180601d02405540e1801c4908101107901290 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 995529847 1250 995528597 995528629
    0x50a031b08060106080406060609050609220213050f040e0d1107080d201c03020c030706150e0f060616080d060b040801060f08060604050c0d0207030f030c05090d030e 73
    0x14103d6031603100180c0f11910980d000c4500510305203000904611130031110007a500000c1029107040c02c0241001042c441c02e0300406104094600041740b52502c500c02003400400340100019500c1c07801c410441c0b083d030540c402c0350041d070518040700c102d0034000c03429200e141014182204080b42c000c00c41460301030a600440244d00c51180d450f2030381900011030409500d49191100520400c0108140e118584544016519035036503c0300101c00d40241c029000140d4a141200d0402c13a003500c0d100103469185170744039140980c01d0003e00c40305c02001d10071640300e0440140d030403050a029010850f030f88100c9000182d2011300034005020841414100da0045541c1d110521540d83c50300e130030a42952041c818205950300e040c1d000500c14204080c2c1c04100c52000c00a07054540d00c070f006200142034020844c4070540710811089803000303190702c050400180a42ea40c110320106643e07024045a08003482c00092240c18401070205d0394a003000841c0c100c0e410700d80400d030342c0c180101003401082603103802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 995531097 1250 995529847 995529853
    0x30c03050a02040c0f080a0e101109100c2d08070302010c0207060c0302031b0703050d0f08100509070309110a0e0f0105041122030b0406050718050a031b08 68
    0x80c00000181c2400c03190003228200500388000100b03542912183c6802004100d03407400040541502d5440810080c0303040d0217640364140004d12040860705d0384410740060b000c020075031840e1410301c004102111100380c00c00034118411a00c0300e4050a806102c00c034400001181d020424604400003003082079844250396840d21443d01d0040c1c0600905040030005114003800011114861000c451610750103030050741c9081e50321400002412040060221284071300360001000407000c01460501c418035a840703041e2002d00d4080141a108041c00350f010ba0207010750700723020996410f01d0881c0c000b451820000349445403450030148480c0700104003680606482c00c0002d100602e902c4a03031142c11125013104047e030f210701c03c004c21956101100a01d00b0000d201c0ca082d5a001a490311070010100401380034455929940d0348500c0c0d1046408503941ca0b180c40c2441581904200c000003000120340c80c030361602c2e043c00b011840c0d4400a210141c42c295050503058841c801c540b521f01c02902d891025 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 995532347 1250 995531097 995531099
    0x30b011b061103070809162106150b04080c010305220c1e05012322030609080405040e0f0d0c030e090103030206180d020d140c010606080601030f110403080c07030c 72
    0x80175000f80e40844449035035003d00d000107400d070580c1c0d00e122000c1d660004e0412001e49601e0068000740e5007514811034020395520310820310b40003a02e0851000340030340c0c1038039a41d07542090344c004d0600f1143e03210385041c141810305026184a42e03064006211700190341e0380c0c64000440c10007034068501940007105030400081d8002495400380550425030b00700307072203440038110800c00c4c003644000c44622090000307900b8401141d00303c203000c56040c6806104520001d990f500c9803104400c81d42040405c030b440110005003044142060f014548330301c03003046c010742182c0901c890195224940308000b02d04200e440c0040d20308050040b281d01c0c0b00e011010303013000782c5582c6a1401a40c1c0361000e8440d503010204c52582210342c82e1001802c07075828a050b07409094a01d8440c2d41c2503903c2c1c0c0300054140c4429006002d48403c0d4002449041c0040001d9521103029040810001d0200c03641c030320302c2c2e0440740e040518041200c00e000040b40d08495001c2011a6180307502c4014a0608440d600010718408018078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 995533597 1250 995532347 995532361
    0x40602090d1101110303040b041b0b0d1b020307030903060507031d07050f150f0703050f070f0c050109060e15250c0e060904023604050706030b011b061103 68
    0x34402030401030031303280e01000c1a40000070980d80e0104071402003801c26910002400500f01451240e0400c1c3d10204482c0041c0e1922444c1800b40c2001e4000c1251b2a1b03682000d18611108418500c1114001e0021310310f40002500d00030b0040201d40800f801550301c2c9c0c00811107003442503000c14007401c000009600c16008251105450b0500c2d031003094405c110b1200c40c1c0045192051040e2004a03202c3c02c481e10301340e040c007245003098016030010384c1400b40038011543d10765240700041c822544280000d0300b11512a01e081d0031040c070a60840750401031502e005220f80d94101040300c3d07490608999010301e1090b80341030b40100e0b01c11071210307290130f40705520484140424843e400c01c400d48640d6981d01c00c22f4a030241540310364021a4241e070320691f02c40100b0090700788400681c00e540700e803507464646d00c4098000414001d00d40c6001609201d2004104810302a061181d43c02414584c902804159a00c0b000208440310400f0b006180407810119881089410707030201050703a810003001d40d26171400700c5e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 995534847 1250 995533597 995533613
    0x827030c060a020f04140103091a0601022505040915060605280c0b0406090209011d1509070f1e0c02100c051207020303070203010f0504121103030a0203040602090d 72
    0x809040340d071045101081c9408200d009641496200300c00a5040c1480c00740d5494006a00c0840c0e107062540d240c0040010170300c98500c4d03010300076040c11829480c0c10100002860511901880025852940090220700303105041901c201e82c02220040303014a07460400f4940d02c80104040e80106213001d50000313045412501401940c0e00d100391521444107107030f400e6200a031025450400041c1000307660000aa0505141504140560270000300c407150396001c03c0c140c5130b0a812100034910507154601075201c0c54010300c0d501000355050780711141d05da0408100342d954050140b00c1481801070b20451040e1103403903801c3d04000c05c0e80c0f10340b500c5940720b00e026046d00d80c880750a034012865455035000f800d000e001d04100981e44140200000d151040340004540c000720001c03a4140000c011403000740e542401110014460b1420001c0d06040500d45911038010910750742d001c0c044940c1c4411002d03000130041d02e6101030b900101695035591490094024440c020320190300c01410410b6005004d02c403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 995536097 1250 995534847 995534857
    0x601210204151e02030c0604121e0306050a0f080a03210c170f24030708100b01081f120c051f0305091207060c0201020c0709270b07082703 61
    0x9000398500042000108a845e40300b82c842e840001e9001101003400070b500c40c03100a41c2050b0500e02020ba090111031545924880074107600d0019417a00c0301030084d49441100400180b814064003080341c0c0ca0710116a40752141c0304006018002c50883703100204030100d0030b1503100301c2240d008020500c0142805007030441000141041c1d8a22000000c011403013440415010740740c04100b892101e42c400140d03801c501d0018030407540500804c080080c61003400c21030342c0c030110310003140420441b444c50001020950021f044400d540c0d012221107060504a2002e030090380c060a41005440000d0b05000108026591040e600642d108007172190101d01003a510a01500030356007071040c2e0310340d03551160740d40e0a0701d00f080c401400200883c174001074032580030065000582c0005410121030241d440e0414100d5446648095202d1405542c05000c0307440c107242e400d860011505880f016a101c0e034215241c000d10210601240700003181c135032102019031424001c16151004106200a981e071600c1c0d403c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 995537347 1250 995536097 995536127
    0x2030a08041805070804050a0611040503070602072c041104060f03080d1514091008010c090305251e090c0e03060112110d03140304080a08070305060121020415 70
    0xc2c010200b013249118101d044d011329008001020702e81c405480780c2c4002d003110000e031007114008120001306c688042c00030b03c0c000c20464000d4200c007481c01a40d00c1c000f05010400132004840305000400454400040f5070300a40c00516180c0d0100007035010a0040c0b0350340c1c00a12250069400000030000100010103c01c0800c24080c84081052002a80c4207442801448441440841c07010050304082801d2503003d03002c60006110180d07100069400c40303500b400750800007011490148144402000301072002c0c03c242602d40c0f40c07181c00c0005c01080e10190700920400c80e4292801210100c05c40d03d02001a1000070020003103060701050103000d51121112a50013405a03400000e09480303414024445160815100103010310854208900712040140450a20014081020458944030081d520851140d281c555482d00c840d070300640501c4008015000b01410030f820080b003a40d000c0840c074058200b018400502c006d03a21818000390003180c00a0020303005000107000c4a5602540316500382c84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 995538597 1250 995537347 995537351
    0x11070f1517040210030f110d0c09080a031b02010c1202030405120601030503120711120706050906091e010f02030a1410060804290f070206102102030a080418 69
    0x80711894489440340c0c100d501030b5000007850f14161440d402a0800816201c010800140303202c45403100c0015600704590003454107940d4281e221400c0e030400b000c4c00140510100030b000c5540c441d900280b400700d80380d01d03007403191010b6084901164020110800c00962100b5141c1122008480080d40c0303401612a161040d20390b00780003041b450001c5030150589030000c02540c90203003010450460004003408401c204003002c4c1e91144a403406121002e1214606000d55580e941241400001e0b5403010780060042d402c480d050140c034050010301000f0f00045001204401c03c04001c105004000c0300d040e0384901790001040001155680d4000031000d00c0c1c3d01c0180215803640818605175560034042c0c280454040004100810010817542c2c01031484409044603400902c10410702030360090300c47c2d1402c031300080c041c00a450303018040c246e80300701100300c1c0206031841d0800c843d8810305502081036032041420442802d6444c20700c40b25410342d4104807810b944950301d10044c20b1a01c0f0040c034103090b0718 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 995539847 1250 995538597 995538617
    0x1208180d0c03053a0c05071b03080f0d0f0507020a030c0611131a07240908070f020301060602010b0a09020f090604080714040c0e1903021509090c0708040611070f15 72
    0x1010303100b14102041c1d1941e1b11400c22145d5507515042c0d07102c1141c500c0d0307404400480000003818120003440a1551403840d02e0702d40c6548504402501c080049c5000e4007400c01c2e040200791940014412039a90b01450824186009414044001d002c0715440003083d00000074a101c800901d04c080c1c1c4120707102d1460313801c0c0002c5407802c40016409002c07001440990711180c02407101800d4159000c64158454000035841159544ea01a07a03118074002c94144c2050510582989000e200746001070440e070000348914103101c800100c1c02c0c245030041d5374160380e0101d0464440350310801965800d0102800b1a55a6034452941e1551200e041c440c010448080030105801400e2a005030f0794030a2180e02d4002d00c3e00b1000c020400d00d44800f10602e0751130003030070100102503a105019515810f001d1685599a803034500207010600364000d00c1e10b5955103040000c00002841310045404864803854449880c0b60740032034040c1450020303803205880316254080407a4410030400c016050211540320b0036100c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 995541097 1250 995539847 995539957
    0x106080f10051015030e030403060f14060a09020744090303031501030905060a020d060b040e06062206090f0509040201020c24071208180d0c0305 64
    0x641c10448a42c500c80500304000c11110266503000c5003281842d00300450098012421b41d032842c0c2203548151a060344902002000c0505807040315160b0a810103160500e141500100360540c16912401c040d00d54002035a00c2440000401c04242001200510760009406400b01603440c070000c170b6441d03511400441c01409803000d0304c1143c0755120090081c505540c0c401d08001070300c8492050310790501d0348a240aca400035105010380be2080a0317920b00140ca07141403c200808440940c0c1203207086103003c2206000007201c4400d141e5200380100d403070541d900d580902d200c0c01800000d040301c84140c05000c01184294011119100340c1d030303407140c2c411142603580c010408441c0050303502a004da008499112103c9c18011074001d404402d541c002721030b245c03c1680300300c2254045441594064034004950301110b41c45450b9a800480300303010702c0d07049850301c416182c90700c842403159800d002c1c1020300c0200b01402407003a14400d074003411b42403000c00890144041407200d084004103821a48464100700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 995542347 1250 995541097 995541101
    0xf03020108070c03090e0c210709060903170313120302030604051509040605070509100918092319080a110303071d031e07080106270c110106080f10 65
    0x85590150742c0d0b01700f800d241c40000c0d88151310107170080d40e0707078642001282421480b010001c01c003d140552640858034100500400c1204160070542c00c01100b40400c01c086400360060616103501114011794a444030707800c000c8540c031036a00040c1606200d0501071081900369014510603601980d05010903541c051080c1200d101c099125a4406048004a40800c40c0c0340e0001d0750200060902601d00340c0c107100013950707500d101d8514030006540b4030814070882400e03608412100c4031961091161805640e144e18018441120040f00d08100801c0300c0c820080401074000580c90451485410740d070542460401ca42c8080000f0010501c030001c210280f01b0000100d9109020f6680d03a500f22000c4132180300209100740100a40c14810100d190020010582440f800440024010001d20b031070540e4003804d640290340a045281c0e200d5400444407007100d10b41d41e0020856580000e000800034400382e07034440c0030001d0021076620b050404112000001580100403d0000c1102c0b0318040700c0c0a00ca007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 995543597 1250 995542347 995542367
    0x311030a120c120509101a0901060c06090206030c1b0616030e24070206090307080f0903100e0c040f110412050304080307230a0b040803190203010f0302010807 70
    0x4070a04140160031556601c01d4600c8442494126400d030b0030003540c3d00a5801c140c4122005400c10f080c0000e0650b440c0c4111521402c0307500140d44080c7d00742d00022549841403141000f4803030440c03402010499164803082c2c0c1250b0041030140c0320b091130542d2030820303002420000445001c450302030007000310008049100c0c1070100000c4808400e201c0c400c90103410211100e024074881c060303d0081060f02090070540701f44c4210a041e24034601400003d22b00715000d020550250401c110700000f207004501282c1c1c1d0b9641c40b54026031340e5840740000c285084000c40070b90804074074042c2101e0254030042801d1621620448050024132442d1140340c0807281c00c0041010b04810800c810010003030300001c0900d01c1c9000b9000e5904150343c458580c0d04503840f01c0412034031255065040710001990703141801b2401780c5400100400026980c41740e0103e0406040030b481c0c100c01200290301d2140304d400391261209810400e6440796560860045445240c0c00124003048000740024041c502c83c00c2981 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 995544847 1250 995543597 995543617
    0x907030b2a090a0b0c01290a0501180504150902032406180409030c050607050a09060c030c0b10080a0305090a05010c021e01120216050c1002030a030e030c0a08030103031103 76
    0x41c1403c2d1800c0302d0b605070f607480b07440f0482c4a5501c070324850f030844071004090351540c074a40c49084181082e40c806c01884480940000d03060204c00f10b403a500480110010900741c400540d0000b0f03003017800c204503c454440ba40d0004c86030721300010801c618039945207500b220007550b052441c200c81c08540b08015490040d070301200c1c1018501d03030813090549820341055200034024141420b904669440b0503083c07400480c0d1104c007294001880070092584800b00400916036850060109699560001d003a0201c100300038007080e080d030012030a450708204000000300840b00c101c40e4440034030300c1d024045400111255100d15005940001c403540105042110690b009103064032890a82c24081540c0000c0345465040003100c40392240c1c101280d1005204000b44500b40c4840312456141c054500072482c4000c0d8042c0c40c44000f005011500041507482e4800301d81070214120140d285501d1175405205181e543c03a2141e0088081440b050000940c140e034000e41e07916902c110030a0346140d1b6845230701007003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 995546097 1250 995544847 995544859
    0xc100302090d0204090c08070b04151d06130506031801060e042102010b04050a0506040b100915111203160201020f04060e1305011512060f0501080907030b2a09 70
    0x224011300e020350200b00c40c1c40c4101403039062551202c1c0400e290138410f8219082200000a040c0034044002a114106150b140740406000080352452603001070055441e6004070340104560711000407000024010b03110281000340c44c0c3c905090104007880103500c618051b07519107100800d0120007905100c0c0b007180c0000e41182484490203000d400c88140303414010440d517846e04e0101581d82d0318040c59005000f600e401045609000741040100c0d000c0d50300340351040c040c039041e00d403a194200f02004200c8120121860744d91030210002c0d035005034407005184c154000e0344004240755107100065805060070b0403610281000c40b01003607080f40310b10745030018482e00602041010300d1041da401c520b5600042d00000b640540c400c03000e806d68000382c00a03071440c00ca03603803100c1180341d001c403540c28900c45160301404824030303040c8260800402401010304100000e000220351210402001005545c0032444a806190900e0b500500c520340c130700d40318102c050996410700c1994141059508240c402014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 995547347 1250 995546097 995546119
    0x9030708010b0d02040f021b030d14150d17040305030403020114090f0603070201020412060606140a1218022215050901090906090f0c0f0f080606190f090207060b04140f1e010303020c10030209 84
    0x40203ca88846002104d1007400d03b650303001e060031900042c200440c880c200550301c0c2c505520024200c045ca000400c03824100612018805503100c114841c06590140c4440d99242c0b21558100c1c0a0300c656000040401846a0704004000792540000d0407684240d03034100400e004181d00108912910402c80c0005602e0f0150724501c1104d68401d8517942c4c0c000c069000400034541c04a8501103d43c4650b164a51a6905080d4180c05900850024540c3c0140107404142807070001003000c2010b00502460b07503510711040e010410554883c00c0d4003030b0001c0c09920018024030707160518507110f014040c116003403010000b50741029096000d0650704075a0240c0841e60b600002d111110401c00d0a040c15002017000000d400c1601c03140e824007030510008096601e0000c0d061410949034042c204030302440c501034004201c1e401805507550008540f4118000c20385403003031201c0503a80c01c0030410b0f1100368003c0c0000100358000581c410000c5003682c1041800d100da001c15000c07400341c0780c1001c3c0c002c2500c1d84 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 995548597 1250 995547347 995547349
    0x8060403110703021c0605012106020d14090d02071508160e060a0207090518060609040311030d0e0d0c120c030903080f09030708010b0d02040f021b030d1415 69
    0x70800d80c0001850102d8080d143e40c1e400161000180507000301050010741d000f00140120b41c029940900f50004a51085007000340d460f001ca412501c0024003203030782c0801c80c94450700160b00401c103085078070700c0c1d1284079081c8041342c2c070b450301034071403010000d440b450400080d140345c3c080d800c5218100b142c4410300e00e6910f2503421a40007034924500310070020030715030800859032904042c06c803003082c0b43d0040105074109074494003180c2019120100c4501a18450303c1c1004d00001c085601c40340644919982c0c1c1c4461505030f940414030b502090342800701149401c0e070580182d01074110601d111048448085c9071010603500b20300d4440e00500f102054150300840180202441c45009200e4503103129159502c0d1104862030b041281c9440d8140c40003d014141854100301d480e018007000002040111040b0000a11025110900a0055440d0402541d943e29154143c3c3c49000c5059034210203c40500c040703c2e1a948800760540032079141052150444d4003400b0140d200760385227441e4103da503a0b524 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 995549847 1250 995548597 995548607
    0x31103150f1206010501020c090903070624030305120117151e01142d0f06070b0a050f09030901210209030f0d0201140712090c08120702030d050408060403 68
    0x420001d030005400341da600496190a25480e030180b9911024140550400000a0610024400c9103204003000c1092000d1b000020085034226940180d0009071040450342d03416907c032849120842c4d5036607540c1c000042c0354020004110000e0700c240001050707038032125010743d41c0030b802c412194154849090608021080c21103540c02010070751081403042c645018881802800740c02503900d00c54141101c035518101080d2080e03105d000c1c070391940100550380c02c201000211702510603100d401030300150180ca84500c412101d0b066004801c00300d00d85407081410018110076a0f1221138084d401c000216070300c0c4084280c8098034030580d05c10340104038040b01c04404280c805403020005908011910807030360200a4810542203410190910f032181610103401c5030341100d070307501000035040108400c072a07104039241c0c00f16140c2000002d440d503840c144183c004400f13402c444003500c41d031800010b42050300005032031007038821012a031b004400c51400326260300a82c41404456408500445e000038025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 995551097 1250 995549847 995549881
    0x50f090910170a020406050612071404150f020708010b060f030a14130b0603013612180812092704030807030b09041e170d020415031103 60
    0xc1125140751603150b51140d202c0c0c0c89404004074465005039128800c5040074010b000080c982141c5140c202015140c0c0340f45071440c001d201a04100e0220f01c81000c118001c2e05070f6000e85800d50002a12289914000d04a1b15140c07882e03c025110740304001941140500a0702010080a001d9a003080701d110090609a0000b40110041c00c0c0c0b00d84880100901c0c0c0f00002e4440c2c84071080548400b4031071f042078800c0300c0018102d2030080e4146a401c0244500e207101c1e407107022040c0002c1e40c200c2c2d108542d0700c95041102007401030100d0b444d4515400416400408000c60b0501d18101d506456950b42c0240d40d00c40c0e845915042c07014041c81040424941500c5030082d4054400c118080000700800c1102c0881c012282107021800600600103130780ea0500c0b4071301c0a10000c0c1c4400384103003465160014802d212140c014101c0d240150b0076010000381c1d004c070610f04005401100e44441d280d24114000e5001406040c00420000103240802c0740f00b8054407925072414500c02c2d03c1c585540450a500c0070130 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 995552347 1250 995551097 995551111
    0x71202011e09061401060203180102212101050901050f190e011403150606130b04061701080604020a260a0b0109051f0302130e0d030608070b0901020c0d0303090506010e090d050f0909 80
    0x20000c046840103540010f480c43d21111013380760396404005890b00405002d441c0c111603404012006001c40d866042201c0c0c10b40c0d03001c440d54000c1902c00000190300f4002a2180040c81c50704802c001401015110312034140c5204106c18090442d0385070501d03941e401c0c0903101c9040c895101011a03400c0c202100102000648004208586502d4544009a5900c00d60181c400100811007607200b20301d000c0c01103800b508806000c1c00a40c2025000511034000f18060f85a00c1c8a00002c2940d2502060010010614100003900c3d480500b42c00c2059169409202e402e000c2401c1200007002d264800c403082c2000200341000552003402c40c3c0a211050610716443c64102e9524500054600020002e811000030650703408280c2600304144907003805600d500150216409100d402d030b96a0b000320741225801c2041d9041400394032282011409441450009400b5003d00000454080902da400310700c1940141c0131650000500b00c0c046603140b0030076030a205800c00c00d200c2a42e9601e4901c019a0308039a03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 995553597 1250 995552347 995552353
    0x4020a0603090b040212161403010501090c230c0d020c0f09090d18030606141f0e010c1104020a0f08060a1406030a0b030106090e0c0411071202011e09061401060203180102 75
    0x10b80e0b00301d1030250724203800a014000718440048801e107270034020540541a80c800038819107180b0318ac0640070214100c400300b0300c2ea90040214880b80e400c403054a40540b10901207904101c54460060f4039600c0504845004032460150801c050514001d080d005d9840c070b400916490720222421507201201c40040c0c201c860070024004040303502c5010b5038014026101014505000c0d000800004030050700c1d008031612400c0c2c2c2040040ea0308401e000d14817450a0800109404003850584140603444501daa4414401f00c0c01d41030701540b00003a0104500141c4508800da01c0b210200039210f0403d2054901d000d040031550441405d080000d140c000120560200f000140440000d09450040c0c00008819640d0541c100803050204100d014a0009a408200a219943c0009020700c280d4001400031400c0f4031650011901c00d500010074490380038041007640ba0040e40140240060340d0083e610b45003090550500e0043c03041e2194101d41168008503e440c0f104124441c1380c90b84012004d040d80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 995554847 1250 995553597 995553613
    0x100e0309221a010807020d0e04090819180f0806071115090313090e100b0621040212030313150b0a080d0201141918060e0604020a0603090b040212 64
    0x40d4a50041400314441050b40c00b0510009000050503e1401080380702150b000500e4906000e0304040c1d1041c00b508261070110f4415100d050012041c498460004442d44102803000030301d0b64031401c0603200151901680d04441e40d07a4109d00107040c4180620340c41a01b00760702248220303000d03095402d44d521038041612000e50190411181500003141e54100035000065680444414640d010000d0403030b9201c20031042c2d400c201c0071955201122501c98903e584d850030180c0940e103040580b101036030145050301e0503029110200410560640b012030091080c055040920000807040ea8400d0040444d0981544026202c1d00c0701c1c054040c0840e0f07442d82d03031055034040b41e850301042200506a070100900300000401c000900711208203504a030626910700c20b100c061040011040c011038030724100070420301480030110320707954505a401049185005004408588013081d04c6129070b000701c0304220b4083d902d41c0280c00b13132041907130001c202c036040342c001900601d0a1602c10000401500031070341c1c14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 995556097 1250 995554847 995554909
    0xb07060f09050f0d02010606020a021c0c0902071505040f06090c1703090306060a12030f0311040303020a0201080601032d0f1e050c090a060e01020f070f0602100e0309 73
    0x1240100000d03a030302c0d040f8484040304400d04020143d03002c40c040c4002c101892800c140207448401a0800a01c19020724440d050001c104030a102d0040b90024141c140040e43d0b1000f4070002c0d0b001100440301c0810a1a1241d4001c0b118440c8078400ca80000c56101070781c02c42d075151801400c84510840b04074000c0f0794046400003241601c0075040015400555950003902c0c20189801c0000344120301c03a1800c1c9030140f00504e03101c2d03444100356505082270702540134031403000e401506040b00384030f642d043d021070300009059002800740700190003a2540f0b051900c51100440a0320800c1203400c90080503801d07003400421602680e01440c80c003a600000d0381d555039078842800e0310300036980b41c0c00d18505c2c2410745402d101c10f403040f95042000030200030300c1c00303014101203041c000031072041c0c005102c91141e10901c140d000703100c51041c0074140e00986840c00e8440010324201e80440c002c040062103540c58405000030360348200c0b1880d8058000850800500b078081000f003a60511401280300e84111001c400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 995557347 1250 995556097 995556101
    0x1d040c0e0a0605040e070b07080c0705100f08100e0112080909071106091c030c020c030601090515012604290103020108070518040b06071b09060503030a090b07060f 72
    0x800071520301040c000e152104000c29034001c07040080d800c3e0810101040001501c90495031a01e5002640b980c403903000482c100d0809c44154402070b0000100c0c9489501d960340703c96120303146c40090301e49162588501c0700780700302c6c04043c0c000e1041c052040401408044540b4800c420428884c0303030392620b08400c0b034002c030701329900940f010310200d121000c2d0703101008014404160311041080c0149001120100124545001c040c507070400c2c10b5803010100c00c554400c0c0100031240310003508460041d40c0d80c0c07038001c0041c0012140240c00d02010000010340d50303c15074280c454045203e515612070094168080c43d9040007400403500c038503804880c8050505145011000d80da400c03004610107626600000d0680c180050861003000310030001003103800e80710004c2940056051b60001440803141d00461841d01c2038182c054102e07082c0030094017503040b03202469000e482d040d14090207103e65440034166603020307142c01d004c0801c134509824803652500c1009845142c2c00b6010201d50100d101c120081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 995558597 1250 995557347 995557351
    0x20411070b0714042315070503071e12110c04110423030706020d090b07080313060204050315060a0f15030c020c1201021222080c010f0c0f090902041d040c0e 69
    0x15801c60315815a4543e146c01101800e10400e907008003850f08002e50b13109a02c0c1e206000d0014918052290b6001c02c018450801c140d000d903002c0c0c0310391429401d5a0002d808140a001d10440910030180025140e06042c042c044c040004810000e04041c00c08141001d8145007082c60840e6514001c449245a5010401a80100b985030094082c8103000300c40180010b02c02d4102c0704c40c130b8000300403100c00686034108999024200032140c0b04c65091600e0000040d100c1e640c4840d03070504c924181c910310f10f10900ca2140c040d16046071442e8600d5511060007016484a04c1010600174a50155451450290704800c403880202c2c419a00000301e408000341c884a103c40401c6c81c00e03940442e083c200324502e816103540045c1d215805081c000f514440c113542d05181000024101032001c50360098a140c00d4200b5501d0f03503031a0200303102001c1c030513000500d031400c03c0f0b0040300055541d1000054040241c805c030307020b5038400040300d2948140407805841a010107801110420442800000c003a200b00f00414 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 995559847 1250 995558597 995558639
    0x27130f060f0f0311060d0603081b0c0901060c02150d0e010501080a0803070f09080d031a01080c0f0702150d05070f0309020a0302270a0b010e0307051804031803030c020411070b071404 80
    0x15440f122b0344141d070102498988205e034100d610582d10200341d503607500546130444060b071611a112005520201c0c81101030005004100440884c52011408403a045113860141280003080700fa80c0c0c0d03035042542e8081844028140e0380d420008290404c0c41b9414281c1c41141c541009100c19681700c045c41d1038519000110400240c2d80d119205003046119105c2a0040d42440c0c41d07400b905106124034024458030700548007500c4001484021503d60882221181d80c08129481c0c9036140d00c00c1e2030015020448406001a000030240703802c0900a100c0d04200c0e40d000b0304481546411a424000d2000d049080340a0038002c450150711502c61076000580b19411028000c5284aa49c0c03002406828181020600c00c0e0400036003801036488210288100d4090b08030345015984507810b00740c62240034031076045041e21726036101100741504400d1150545200b035604000241e45a18011054003da210003400419402c012544d2244520861600342c844881020b142640e07400182400022040c00c0b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 995561097 1250 995559847 995559863
    0x80a020105190504030806121513050f070311060702010c05061503070f23220501060e060702220f020403140708060c27130f060f0f0311060d0603 64
    0x10409090b142180c0c428010079031002e00890a20350380c0900f90300700050000380209000600703100b19640801c010240008810000340403400c0c001c01c0869940c05455007a00c00340f20305482380d65801c0000031400201c90f001180045100702c485d0820070683e200d00700c1130f030400000d1076034403000c14000d00c8450f003d43c824624070070050118206160030f00c2415444900a8040c04c40100101405204840100d64244019030004144000041c00c40810b0b42000440b41c600c901540300c803040302e40d1015040e201c4075101c0031031855484d0b08001a80c030815000a4100c2201c40107840b00811905a1220b03041002d1710208008000140940407070f0030980c02038a1480444101c41c450b20300c00c1c48450042c25014001d40107030f28003a01149030f940300700501001346c2604421180c41c050b108414840703e070107001340104560a00601c0c1103014210b40034640c0342851a00c403001039545206180141240c15543d4054500351a540b81d0b07142d0b20a040726030380d820203230070061003503104101c0c844c81010310b21404603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 995562347 1250 995561097 995561101
    0x50603181002032809050a050d080f0c090909070e09031b0321040c0f0f050f0109060e0d0303020f280903031b080c0f0102180301050c0a1407080a020105 67
    0x1614011400c28041c40c1c01d84100140f04558410420300f442c1c40d0600c11051052003024010f94000f40034681024002c1c2c0144030450080000205040203496043d42c0c81010075107442d56103400d640b105039440007286100708a00c82d114140034107140e511003202c0302540c0c1c0d9240e49040f18000030300c0445242c030007030708005240e8400c51081090800601071100046042201210b0001c01caa54025901140c0c0312603e000141004043c580260141c51303600c848040c0c00da6102040012081e1500405108107500d86003018103504c20400072080301d071290340380003803030300800c06014003100c400c44190100b41d020001440000700400c0108451114100300c4025104901c420448000320000d44d14100f20b2200f0041020960000740f00c1010454880611011400d91070101c0c82031240c07040d080e6641c011401c90405041041d805021094844484411091400c90070103007210300413108a481074034107011040c2c140344540c031014010b40002c495030b490804180c03510b80c0300350404a4070100507174407a01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 995563597 1250 995562347 995562391
    0x9140d110f03071539091d0403080615040305060717011203030513020409140c220504050a0213020a0e040603020915040f06080303040506090c030d030b0307050603 72
    0xc6420401e42419015500b03000c0300e680c0b503160f50645001c0008115483d103c0b990074a440c4069440034090581072034040500710340c5210901c80002e80c0d400d10102c0c001002c00181d86071f0140110420150b07861030121a81e032583c1e13082d503c0c2e080192040d60003e07034400b002d040c40c414403801400614080c000605043c5000c00d00108030815401d1260241282100100700080c1440c4a02c01115403505021410f660341c3d000c1c03271750341742d104003006035100b820800d40d07400b0b003c400f0980c9a24161080c00390780c1c250b0045014017034174030881c4059441c00e410081c40d4042401c00d0b40e2055030014803501c10349a10507103940004881c04854044114882e90002c1e21030b02454000700e4078050000c050b01c0502489140d178001910800b03004013007235400d40644008c5116035542d5446400e041070522010405651507860407603403604200d90441c0e940c803949000c2041100d00081922400e0340080041480c00760742d210850213804c60014040d054818010041800c2c1c2e1100080d500c500512a43c0040c6558112 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 995564847 1250 995563597 995563603
    0x1b0f070915050105040b1e09150d0e06060a0e04140d090f060c08040306151502070806060910030f06021c050702010f0c0206012702030a02030f01090501050607030309140d11 76
    0x35102c01d040c0030b01084200040403c0c0c1090305d00000c1c2c501800d000c840355586100742144104601030f5070021034031100004e03101c8c9101c058040c410a40c0720422060400f4460141d0780c01080d510164858070b09402046404034008080340c3c094403e01c00b400546120b140c0303442c507002c940b02008012820b808820302070000d8440c0404000c3c070262810340c031021b003140c450100b6807141d404054039190f00d41d06410402030881c151200103000a2044001d212841c010094850301580a011801d01913007010503068507121301002d00070b030175914280000340e03d103a8a0004602000d14119003140c0c0178014002c101d111162004013a100022011803a0300d003040c002402c45040d0b031084024a1325205120401590028000b419141d800a119130620402201c0311102c0301d1200144c12403500020402400c1c030f0b0260050f600510b00880d144d401e69803540c1010098a0090080c0d03034102506200890100c3d2281c3c000c444030b5402044042d00e040c24200d1280d0414010905541c04a00708003540c2c0843c010030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 995566097 1250 995564847 995564849
    0x2f060411010f0216060f02010e0a0302030c0c0103050f13050a0c0f06081806071805040608010c031401080a0b0c072a0b090a0504020d150f03051c02031b0f070915 71
    0x40c400303043c808808444c62015000076000714400c03c481001c0c5440d10034000d60250b03072038007100811500d4848103071600940d01d903c10480b25043d4021064000c1c0c6650090240764010302c2696084400c503540d00300380f101240c0c0148002e580500c5444c5c5a40c0c040780008500c9406400e000c00040845e500740740300948038900240c000c0c0354140c0241da0803a00f990b4081103080c1c0111062901181c0c00c0c3e00008040e00d15120f68200c00e50062600b10001450001503111070501b00160314244290320039400c2c5c0c0441c1c000c09200b100c44a030400c441200000b4903010805900c80c0510000b1410003100346c0f11200c100c0300d807995105200911084840b0442c00116500340107002183d50240b808402c20085429450785200300390045401043c02180c14903581c04c0240b10301408506d41c2c802540d03c400100d51455203100581e8070b4090307041c21155403800214006124034042d0002c500d0142d02e44a1083c561504901290342c90140a605c10348409042c44000020b1800a001003100100162800c20701c1c911 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 995567347 1250 995566097 995566127
    0x14011202031506030d0f05041e0806090a0f11010302120f093007022103031f0f060e0a0503100c17090c06030c09040504030f0807030c2f06041101 64
    0x301c1d80030040f191354006a0455004420f242c00c2c2d00d801004042a10360380103d070000b403180010602440000340d51b508420086400c2c00d81141e4064980004668440c0754400024246c42c20301000e2001080b80484441903029040c9001850900c2510310003181400643d504408c4c0f1811505103d11420108104025000391070388882001c4e1f4820345119007240d00d65101c280e02103020560784155910a00ca0848a44649804a0150114540b05a120b80c0704039100080081006458040000e0a40001d4140c0300150440d20182d8100710f802d6079074039598401590301003180880481e00d80c40620010a000c860000b000c035030b034110b01101030300103502c4001e4445042c92900800150810002e940c0c8203c00040d65001c2d0340b51100c0c916040305200700420203400c10b05140900c02015408004c005541e06c050303807094441c1e05c40321000c5080c4d95502ca00600041d41d601098140714030a039480d40306480b0326140d104200d95050804605000701110140c8018580f1041c0a1165030418001c64070180303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 995568597 1250 995567347 995567383
    0x30204020f03040539010e030102031e0a021309020c010f150914060d14030d0c02070603050708131106091c0b011a07110a031a0711011a040b041401120203 68
    0x40444a6901a07924803903444040300c2c00c2c0f060f9901547d02032404100e01450140080d560307032500c454600c2a0000e03800c4e91043d00c8600400040907480c0074070944100c010285c03036042d0381601e4982202d020f500102442505550b070344902e1071090900344500d90228003405d00e01900c00786408581c90403104c0300c5c043d0762031060131042080425034a83c502108040d034020301005840b41c195406900d1401012240c9107410f01e403240ca40c2020740c0000d802c0b4100c48041d94244800c0d500c00c9001c1b941d800d420b60340d84518200340308501c80042c03c0b6a50075051848040d00d400e081508030400180d02d00210611043e4002c00a60500c081c0002c0800203409404d0309070396450f00c3c261070f44400311144030300c0c903020b4003024036800c90900345e40e0350100b03500065800603200c201400100072451406441a20501d0106400c0c0d4407d10810350103000303113040400207584204003a0080300500028040034803280e41c1c4503075203c14079407054443c500c0840c041d0030076218116800c000d0b4414546015034522800070010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 995569847 1250 995568597 995568643
    0x4080f13090c1b020910180506130e0c090601030f0f09050c090c120406020f0408100621023a1505312f1206160504030204020f030405 59
    0x3d902c0e441541c0c0ea040d41c0071074203035441100b040e04050081c1c0100710701d0f0103800000500c003091a00420300940d01150001c1c0da001d00c40451400700c0b5450a080c43d17564000603402c01d4545824092241c1c0050181070201c1c920600b00c6e441d8048a6a020514400ca40e0303070b03060641402000c0014144035942541c1c070f020b69062440c03041d28180208444503081080c01c20004e42044840c0d0140d5050803400e000c070701e894035100c010642d1180301e1003240c800f06a20308440040d00400c0c0342c0201510b00420078003812862455000e1184422541030721884030041002030055040030716902418600c0c1c0120300003a41c0c0d445142c03035981c9078512080d525400b400c203810300509000600e51100240c1d82c07902540c0c110110403034407010000084001601402c41c141c028900d51001006c800c2d0310394901800340c1c000750301002c00c0001c41580481c4207601544603000069000300c1e556004c4109150904007182002d43d203074000b8050340d204540082845101005000400000b007058040c1d07014402981d854075 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 995571097 1250 995569847 995569877
    0x1b0f0c0c17120705060c0706020412061d0a08040501050d02040e0702060702160509010501050901020c030a08210c070803181f050f040f030e012a0308091603060504080f13090c 77
    0x2170034064902c901407500015070104201d4298103d5005000500c08410000c0302070400c40014018040110002c1d80c00703c030606c05441d0082884103000d0751150509040a00708001100c0c039070000c04c0920f401a50030080401c0d0700c18443d940b24032800881d4010300e440c0c80c08100013414000302d40c6880d03804c00482030003031000b81c0e903110805064440a00e0403a4a030140b50004070300d1300c8040c0700019014051074450509101c040d5006207401803202d5003181c110616500440c00500c2c0840d00b07888000b02c1032040c2400603032034000a40d000f5100c16070030142d10a02888003400d203d03074903203541c990400c21200210401114040c0d103501400000c0c8100007490191145c466044561400900700560003090032010ba00407415070110580441ca400721403040926144c0d00d400010b1015800704440d5030004e240c182e00020401800b440b81c0c055a00b10b1407940e95008050300700680100d40f518001d00c4000920280000a4051745100a4a500303002d85009001e004650f80c0144800402240202c01d10794 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 995572347 1250 995571097 995571103
    0x9050d0c03120807140f0d0c0807030606020c010c0204050a0b060d021324141c06180203010323070515070b180a03180b0c0d09091b0f0c0c17120705 65
    0x885043d01c41d030150b40b0a03040140000d5403290f2011f455015141804160805038041486403086105450410074251540000d81c0c0d2082c2c02100ba50005d04c02c40006001414541c0049400c901c4001c004148141c0c000b0000d0640e410148011910039404600050380c11281c001c4100204016141d13a0351201c5c001d0704908501c0c520b5417212040c86000c190121b49542041d00b02c813404a0f01507007214450b80e944000302d0152019104002c0e540f1500100242100b045208490490341c2c454241d0600c006440c0e42c11034401419149854039020304100010b85864810907030340c4440c41e48030000c4e82d40000d45009620410082c2002104c80c07418604015201c0c40001c802c003245401d402e0400301d40324424041c2e060268260003585844401241040d8020310000d171810300300c545a120444641e403122090341c12100c00c3d0011409006545100b1061103000c1e03261500202580d251240c1d0070b0300182c9901c0d02d16110399000f440c0250403030000c144400c1050007141c544918034805146030650300e03201c80e95 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 995573597 1250 995572347 995572367
    0xb0d14100510030825120e1201020a201009080c3c0f0703050105160c020f1203090909102403110a030506090105070e27060109050d0c03120807 63
    0x304034000e00c45174508000c090300100299136070108046c01100c240000003844611900c1f1400e0055110310000641030106000341c5910740a6544c510032003080c1c041103640c8040400c10180524003078a00442c0381c0140754003030f009209005104055035640721000061a25440c1c0c007200140d001001d0b041d440012020b901307107040c11384330001105d00303500818409007004030045d901940e620603181d0001c10400103400c80c5104801c04132524120252564003510072419240340250300801144641c2c07010318291111080034441841202d081100440100f4a4a482684c54150fa5403090743e000c030a1268501400c0070410207034540f801e103103001c0180c685d80304007036020003010120880800a02c0f0745401c02240019a0030004680c1c1c0c40c1000c0300f0040c0202003d40b45080091070404d142902d40c14100100c00000c410500565140c06000e00561004a4081d10190401c010f402d80002e040d905c1c3c0061ba00694026480440e100d49180b401000000c1b01d1080340c024407008000300300c415504000201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 995574847 1250 995573597 995573617
    0x61f060f08010b130e0118061d010303050a0504120f0c09020f0d020309030f0a0c03141204110f060a0905130b130e030f0c010e0c0405090706030b0d141005100308 71
    0x164032002c41c4134240000380300c3c0340c021800b402c9850000290040c0004105803d03445100810000e0383e0f01e4040358041f0444081c0f403200c825403c40b00410009101c4d6001740311007591841c089081c0368485242d000c1140c204d0070190780000ba0440d04c0014420308100c00c07001031500c007904606d042403041d88038013a80512001002070f187c4c003000041c1491805c0c01150345101c41d903aa469035a26100c030014214003176082c02500000c006540c1154218440000ca81403d00c81c08100445952180d407603216400c4800b46458001d0500c80c040c0b5016220403002d40501380e02d41d01c84c052001e00345814001c50700e1402d16102d0419050400c070003481d8960144400c8101154000441c403081e40c01080e0381b0398414901c241e110f0080000d201c89138190198000c8004440c0181030765550082c2104200035141d00391885001500701c40001c02000340a9800b1b500c0070080a090050b800302547c58404645243d500340342e00780c1c0c110003254091401517100b2581e11504070140b0080c03903800d60b12480000d0284030b1510b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 995576097 1250 995574847 995574869
    0x221040810021c02041e0b120a0c021513050f0102030106200a150c1101090b181005070207060f0318021c020409050c1009050d03050318061f060f0801 66
    0x1100b400c074100f0000c441c00b400c0ba14040d9034032903681c0700101c1205100013092500c100c0c0088082160703c500002c49940c0100e0362030079941c64a6101000b0300404014816206610444d8008a01a200d080026103c0c51801904040c40442c0d4284035040c5041d50130b8142950344100300600115401642803100003940303407400c0c1c000000610314140b5000c0d01c4000945010b8a1140074820310b4100e8108056010260703031912003103540800340600340c0380c2c1818000c0906500c4c1000030303003200302c68030351400404031002150101c0300c26292060868805a450000503080389070140800740c0c000c0d8007428280d145241c20400f4102c410002060315010801c000d01c600d594040341030603052030340c090803d12074006108200f069194500140d8071041c500c1c200f4001d100008264021318051380d0300d4412154041c000c54040d07189964111980d50005240707402451040300080c920f40402c100483c81100c80c42d611001c080e02e6644d800700035070b21030ba01c54400c0000d02c0700301005869001d00194110b820394201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 995577347 1250 995576097 995576107
    0x24030601032f0c0f19140307020a0302040e071d060301050c0a05030106050904020d0c0906080105180109050c0c030c0703020a050a0b180f15030f1005060f0307120507022104081002 79
    0x10605020309001e10341054411003400100c010170725003201601c03501c600e149500c01000b420b081901c0380103401020b907112400d81001c000ad41000d401c00403501d90350710306443c1c0c40354485030f41c125516556480000f01701420780400c0880d0400f480f5560300800c02020341401c0224030040209644014000e88042013404207150700e041e00e99805868030403c00d0207007480a1589688010440c211a2090b0700c0040e0754200000784c0c0307040c01c2a070210030550040c400d041985c24a80380710f028040250150b8032114041005031544802071000d4222003000202418010b41b9500401207140b10300c0d0415846001046010452843e829041b5558190f803405039030080341407040040c80042d000055507402412202d9414a0014024011445281014004c1240f031b00c803035070050344070703242070080c503810000c200030040005000070051a031180d100e207000e90800322601c40201c103480003500e056015920000c403d075041840c02d00d4445203511540001801c00f49010300160b034901c030040c02021410360000b6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 995578597 1250 995577347 995577367
    0x60307030c030b0901270612030503060609061611040c080109051308180901080109030c030c06020408030d140f1b0d0e0105070f02071a03070e24030601032f 69
    0xc06160070f001040c0700c0007580c0d5001242c90703e8205842e00001c90003010041000420380344500710039507004500424001203117960580e49580701800c120752001c01030006800c141e45000042464400d811021803080e2011300d090101a00c00701c110500c00d60820060034103035a403044400741103075884600400c440e1203856190710003c2400070058401e040c001880d2808201d421002000c660043e6101c0c0c0075682e070341c00b0791422541e18030030040024105198a00100b8450542400d059002c0c0a0051400d5541c0803642c1c91907209a503010800c84c1c4039001102d0314000c44032155480300c1e21040000c05803605aa103110100ca108003150515103020842c0300040390309602c10b09d00003180d40020051800c004101074804100040014014810680c1c041091880452580d4103549000720390381c1076854049095030403018102002e80c00000d00035400d1424041c00550254500200c0b00b07180e524100380340010169040d400c42500305010f1342d410b881040072924104215003610083d059202c0541d05 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 995579847 1250 995578597 995578601
    0x221e1a010801270f1220070e01260f01090c090e0705120c060c07050907020a030f050a050702180f100e0c0901020a02030708060a0c090b09130204080a0305120106080402060307030c03 80
    0x240c40540581003016007000d0361500002d160b0001b0f412800c94501000303452038941d43d03c20150140d0303040c03280947e0040101d4945082e500e0141d80c0c2c090036a942286100308200e180c01030318180c0d030100740c0d1a20402c070240070003001d02d800508070f28003081c0040d501c2c0c1c1c804075030748140a11843d801840c44a8000744220001d001c02d04801c42d0080c0760b1980c428003507101558980450044600c244a40c40100381000d00001d03400b40c2070341e40760320384011881413504103441a0308030f00302e06010700c038007040188016034031318040842d130b12020b22a0b9401c9041160f02c0c1c225442c0010301da512042e000b11000d00055140c09400351740191104515640c0f661680d004038102802544000e4261181c5200440c14690215442c1d00c54000c01104000c81041c0b41c00440310801c043c410644402e004106403015800d00b101c034100444000c0501500d0140d491071900c0c6400a052025000603901188002116001c40e83c0340d0300510213450998814180b0ba0001041440040c0c413040c01d260742c421004207594025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 995581097 1250 995579847 995579873
    0xe0f0103063203010212010329011d071404050409020d020a1203020f0115141f051c050106020d05070f06050112060b09221e1a01080127 60
    0x70b030341005001c20155003041d403101148084402c00e0159103600307000342414802d0f00c0719410009451400340e469a184c4003800d5005800380031541c400f95420748900425502824024039008805044c1050040c51150b03e0f460043d000300e0400410b10342c0000604202410b07201602c504941c0010605240e100140c0c1e4540070802c025080300304640d0014000c404611045000c40c001c0c0c094840314403012508034202c6902c041c030f5102e2000345420901606026003c05000c080000d4414041e052001d42c441c04103014202c101e10010ba4006a807022070384410451081303c229400d81400700e5410070703801035128040b00080f0804c00c01c02140b018140103d15100d60611b46d0091001c000f1561a404041c03000102100c09407211402c1c800496030504040d051503101d90281c90380d030b440301040401c105079408031a00c0c0c00d41d40d44110311000805122a0800c96549034400d0710210040c402c08000c007040301105902002c0903900d00700843d01580e484c40100600602c000110250045040c5400c0d6006401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 995582347 1250 995581097 995581109
    0xc010e030303190e120901021905212205180c040605030424050402120a0c05040c0e031e0f1903050d0f0c11060108071a0d0e0a0308011e060e0f010306 66
    0x184186541c00307505e02802080380741400c1c2e09840312022101c18141c03070443d4081e0005c1240d800703010408080c1d000241e010300489050380f41c40386042d01c1040c903600b0003510b2031200d402000e0303204020030291078120f0004103122007a4411505a142024840005000c0c91042a060040000c0005e04000c00b40500721072107460440c8a072404090304005500514013124201e0048028001d821107021002030b1800406030704c600345a000609000c01e10001d04616031400060104013845100c242d034003400900c0410416011107400700160420240c0740c590701c11911500e0b41c2054200302140e400c01c80d802c2880d21340500f0038647e52803281003141d00900c0140101c1d80c240c1c0c0f030510032983ca0fa51183c58685602105004c8035501d90701e880806441d20b074944a8280c41c0b88040a4800c0c036190328002070506d60861781e8000441e080c0040c80c0310f09141041c20220005010324005003c4445120f240134032080e00741c1c450181050074a10068201440029403034803079085055500c503030343c0c4039420402c0a001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 995583597 1250 995582347 995582353
    0x30d05091c0e01030510030f1112010204060512130218040c0314030903071e12080c0303090f0d020a0803071227110d020d0206070f12050a020c010e030303190e 70
    0x10034201c0003031020070060001400203060102103942c0401c0e030074008041d070390886031040040c07680c0e540d1003401c41e0842d1402500140701c5d500e0145406400c0c8044c100400b10358542a503520710314514400e0f8800001e0040e20200e080c0046a0050380b60282048020341e100c0346042c410f070f221401e10300020045a0300040101503041e5031f03035828941c044068142d1000c250b0807148400d89820031103d144850f042555480c407071f01c1c20300b00411003002c01150215400b03520205d10380354590303116608644c0100c43d8034645034481030817500764210805c40d50092203010b01c09028080c0c0c0310f560307203086448081c0c035440400a102e501070342c01e0201903024410400303880c11441006415810180e2850403504015100f14030400b540000908080010030641503000341040b000740d0039036082010f0350300402d4081d1001420300c030a000008101c0d40641d0100781954640b07580320581c10070001d140140150366181005400e0300900402e071800029aa0800c616803d92a42210094402c8000b0550138080e0f01c1648 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 995584847 1250 995583597 995583643
    0x71e0e0c0a051c1409070608070e010905030d05041e08030702040e10050414010c08063111040312020c0d120219081909080712030306180506040c030905030d0509 71
    0x2c0c520364400d6891581146500005651701c40b41503888189902c03c20001c0340c0f8960000d8140d6100e1900d8000c0104141000d0401a403564040303450026050388210102e140014140500c07980f00c04800c07400d83c410b4032140401400e081e1181c4d124010120001d015540300e43c40850040c0381070000d03001c2c03d814900704003c54945410024030324021044040301039440d01c0d800e1072140d4407441083e4400c250140c4000c4100107821b031242d003080640e94110f982540715100c1c0ca107009020b80a40c0c202d8200b0012029240c80c2903040c8900c1d4603015116150556200300d00c00310f460303103d011240426030340018080c150118007000c282c1c140ba40e2029541d142d0004c01140c002001407903c0900890b000ea107034078060302c60080000b0fa48240480c090f040d0182e00c4880204500070042611504c401e20914002c0b601e0755555404400e40c448052a2031456a110002c02040b41050f11070800544c01750715003408442c0d641c0d103a4544134864440c075900855104d100044000c50f040007200e500c3c03140799402c84000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 995586097 1250 995584847 995584897
    0xa0e0609030d0c03030e0106030203070329131509050606130209060a020a060e060106050d0e0c10020c010e10050f0c030702101e0804030f110c060408071e0e0c0a05 72
    0x60303c40482c21400f00c5e203000c80708102c1d001d05109000a5981c080d004013070030703400c40e110510503500102c80703403460403144c40c0d40c3c0300c4c003180080f00320340580304105500c12000d0440c608802c07040703860100c440041d4a0090041c010902c001940b42d00b106007600c070b00b41c003501c0f0210300700e02902c21442c1980e00400002006503440340c0c0010121402e6028403800c0003090100c0360300700e0302c80c4401c1c8148000600c080c060040d084103160300022001420304212500200709001044c6072401d060144405030b0820140203001c5d50300600d511400341c004468010700c100e44188080c10300d009150040b8003100700841c0410080c08104122400e89030020206200c80b0503000c03004040001e12100d0345c00e590080b02c0d0210207107000f202c260703000e0780e8582c44000003203000c07000880c0d07006800c052410b4944540f0441da0801d40b0307420000c0c00076200c10780260859034140708600e01c41010351603142480d041b106004012000da0240c29940040c000310a03a50780d90010b030030440382c0d402090b500c0702d4554840b508041103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 995587347 1250 995586097 995586107
    0x613080313030b01150f0f0c05071409070207151107030b010308030402030708030708090d02011e23042d0f080606010f0206162109061a060f0a0e0609030d 68
    0xb120720816008000345e0301c81806088140e0614503040c081100b000e07005052500650308030321100000e00c0c007030080d00d40fa80c07291031401c00582e014040c1c11401d080d0900042c18009007080c0d1000d903600041100a00d0aa9940301050203120100c04102a00c0c045075140d41c0f040c000c840003503403c0302250196503188c2c140030105620940f000ca10034400e4810006880201209070765503140c0000c200c9050061520074010f040d561404100d041100004050f54281c40c202c0c510004194682d84400c6c440d08000c400030002c407618805d500c0c41030340600c000c109085055802d21943c0200d241c401842d41d91a40c510841002d10b908500d0b02c0143d4a140400c088000003041c91141009a80c3d101e061040e5040990316010291001d0302c1c0301ea4501004008203010b10511071403007a10307400d01c086504540301640120b41406108841d071030f4850b54031182c01c5815811040186400f111180c0c50060400015411807068078040004c6c0510015060700e15900c0702c0a442e000c42c006020b42d02203c0c544140181 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 995588597 1250 995587347 995587349
    0xc03070e0901240605030615160b06450f25020607030203150405040f020306061c060f0615020f060a050103150902030705030d1d011106070e060405040c122a05280f0e0306150613080313 81
    0x1c2c09200ca113b19806283c2c142c11206032100b0341d801420068a030054110065031000b841003514141e43c5190010705d407502e00c01c0c9803260f4040c070b925150060b200e204040c01d0190140c1080d200d02c1c10303204602920644a06003480da16481000041c8080d40642c2c0c440141c03142d9846440040c0e08c090a0b0800b150300403c15880015591003900c00542d203056000341100e00a01014020081940e100060900e26900041815000400302c81000d981c4030002494041e0001c0c0345030020708907081444008014603409545050b003400e2954558101000b455540c1c00010308210800880102c011520b0312840100d8014050103481400240b0b01d803c0003030800c1510414248515140c002c0c0740c803001c40d6039030284045885403000703180d004071680801c030b842c0c1d00500403082080b41d0310070b0003900d1446255820b41c81145151141c0000f6020050040c080008c44028035000ea01300404004409040701140c2044000444a26494080c1c01c0c950b82c8926100b030708110050f02c40050102d2495070b40f031040720 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 995589847 1250 995588597 995588611
    0x114010b1e0f042310110601080c0d020d030c0816053a020c09010305160e090d030c020c03070e0901240605030615160b06450f 56
    0x54203918140d4180400c2c42107480010050000740020300c603055071030071251203469500c80d040030740440910008203910001d10885000c1500c1028070070400c0001d0142a0040180d00c010b080a1116000400c040c030386104d20003403043c41070180c400c0415000d11041e103281a0000e101c0ca45a00c190307130003010b0f03807440420250390501c9142d5103241c0032041c0441184440301040403400071444650004c0d6560500c60b001c000c00e50203441d1501060343c8a0401081c025070140380140741ca4600411344403283c0c0410380010424451040400c00310080c000748400166078075140019074503441c51022800d11001c004081e5160046074400070b0100e1101c2c0360b0501940c0641300030056421044101d05c0740c0c0241000030b0f0340540701d0b0320341003006a020318065903101201421000c64482c101c00b00d919203902c24682050034200c0c2d05a1b02c010700018012141e131000003540c80301080120800c1c100750b0220300c80c0c1c00f41070805460160484002403110b00322000c20004102c2c1c815418200c0f0444445202201d80d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 995591097 1250 995589847 995589877
    0x3030601200a0201050c0114090a0c05152203141006062313050a0603091b0503030715180609050d0f1b03030213080604150501060e040e0114010b 64
    0x4035845440c1c5045102000c842540280746441240d801503c0d91341110740180410755035014100800280805458402d50038403014003c1c0e4242403801034130001312a08520701905070303108050f0101d10010103d642540b20203140444a020401302d50790700c4485600010b008405245d40f40a0500c1c000030041c16062505101344152911480111051001d0408c1d0030384204482280441c420700c0c2d00c0041c00b400300c1d07100c09024000c1d00e074001b180143e1190b074411000a55251100c0045c00b208403400c0d00701ca2401c0400d00440303481c000000369280150700c40a0705065905001c8510701030240c1c00311020300e0910380c20080c402c10350308200c401410b00181c00d45450007003036800340d90188644070a07505078003151030745080601400544204042101800c07810b00d9800c02080848144428140c130080c010b801c0104020b15103890a00c10800030841019003450400c0014408150031950440110406440000f440150201041c2c05090042c407512190007000c000490002103c000030248a480c403501 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 995592347 1250 995591097 995591117
    0x91a0a0c030b0334030f060b031b042408030406120b010c03110a230c03070602030a030908160f0201021522060213091b021504060506180903030601 65
    0x141c064500c2046a2503058000303403850003614140f070004c0001c0c4120311400002c01c4440c132604850641080c0c00a03903612112074030f5102005018012529060815005885810240ca10481c040d480c4072041c0c501c6a40c968501c0702c0c5a0000c00340340c1034500309903028a40c60690303501c0410b0320b0358014080d9000043c42d00d80d61480b0b01549004000590348180e45a803699447c6803001c85980c0991300001d1841d024214804000c10381a4034510100b141100071403070b0300b481c0030501900e05422030b0241406504129820480c0a4000c010798240c6041414041140a81880c003e552881403000960740590802c400c042401035100c5c020101c50700c04e8003190445442c0440585014604407030112000d00c801c000350030200c3c1c1d025107491a05115840150500603400d1400c00303a081da503041070701d0b03040d40d5032040b80140503206554144041c060000c1e240301c0c4600d40041454001c000c0c006000c1c0c649440100d80641c44280080103941c902141c0a000c81c10f206e0500c0d03840f81d0081c1d41d0640081c0009070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 995593597 1250 995592347 995592371
    0x40606050405030c0109210312090b060a05090f16050408011415010518010e04020702030a06140a110d051b032412061803190908120a140706091a0a 65
    0x78188151401c0d40001c0e0380c403030b01d11f0058041d1640071200440410056108071842490107014030000703141319100da41498900b01c414800811940d82c8036621400115090203c10ba0210303d00503001010b00c511b00d980c4503030707038034003900c00344141da01914040d842e10b0a45d0888000200130355000e200158803501440c42e0781e2004444900802911041c12585117000440c0b640c045c040741c555110010300090b0410010b900041d0600b00c40c0e200660740c5545615045442070600c82020364010503030b2170200301d4650321190b11040c0d8018610410007290f550000714031194910b04420440140701c42036280e41e80351059001486480c5030047d001c0031110030400c402a0300c0c00950343c0c9061480300c3c00504699499840311441340290300a002c0c502d000c06c0000b07070441401480748402d96001900c400032411b02c3c0a031007610740402040c0c0d200c544c001c240310f00c40c5a541d008051503880c80381c20b0b1410391649003900b000c000505030724400915882c1010100d0002c00e00d02c50026200302e880900030045004158 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 995594847 1250 995593597 995593607
    0x30c0503010b06192309181621150e0a090f0b1314150c0c0d121b030b0418081c0204030c06021f090b0106050a020c040606050405030c01 60
    0x241074190302c40c1c0c003485070400c900100c0c0c90300144001d482c43e1101c01e030401c060280b4000e80315604a0610340200040c80052070900e1f1b20f20501e03104907121544240d00c0e01d00e14a0728109026070203081042150714040c03803d0302800b103420720b201659503030421804068032071000705242e09110b110403084a000004044510500c81d0281858101c020924000801d41e103500481800800c1001c4035034103011030001180041481c0d250306078403040108110861034602041240c0001e00192204104000d251303507003100812070f01200320890615030f94400354064000040c0405c8103070b00e69040c0c200340c1d02004550303043d00000c00386482075808108240301e1090340060094904000340c03005d07500b0001a0b140303a0f021040c100d11500100001030500791640e80e04021040b8540c0a0001a404004450068081980c2d05a984003002400300009000d0350b4411040150502c04d5100340400424007044180c000d1101d0040130b100200f041101340d07156000074005030483d0050a000744580e40e000760855020ba = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 995596097 1250 995594847 995594861
    0x602241f0305190b1f09020f1e090310051501200102121b03250e0a080703020108091c0c1e0c171f020f120f0402130524040b19030c050301 61
    0x5e5070b045040b400c0541640296118515090941e1420019000844000c40301c6942e000001030344182d48002c2001090b14001000801c01d810b41c2c0707000184091160a461800144402800c0c4105900188030070300351251401d000c0c0d90115400001c103c81c00b01c412680c1603205d891013240203003070a01e04d07003d821464081241c401c0500046240b81c04040d4281c003036034260010769841c24841c0b440da410041074201d1420b900c204144d070300240c010f10071582c1103046640d000810000400d500d1425003015020700c40720910b010305000c1c400040d88180a007801001000c0c1e007100700c0040d02402c89140134a02c40c002e601c07540720300b801c000701400c09107100814101629185140710154401000038000c0c0258881d824004801c00d080150710344121018000511641c1148200301040c507041c010b010459588441000c11203150001704200d4200c8001701c03003039000304400c0010481280d00c001c900100f106000d15035101802d034802c030300449811405c05c01968410304c4042005a030361030a0500ba1420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 995597347 1250 995596097 995596141
    0x1b0305070804090b04060e04120804051009080c0d0e0d080a0c08070b0f0c0a020703020609130513200612090703051911040e2505040c05040602241f0305190b 69
    0x258800312940c1c50b00c1070000b2b0f5001405502910600a1071020301c404603001c880c3d0032038581c6008a07080c214440144034042c1407400b181403001c8803134214070018800e6098400e00800152010504051322482048450030280c0e0040e2030300e80d00c0e8803900700000c0392142110000b04100c2580b00003036a0010704000c2e0f0b164040c1640003422800d00f55030800a0507001682c41c0c9400400c1c82c0c1e140c1c0c2486d0a10b0003064051180d241e1001401c400d1800d0403030001042e45100c0c81e901008a0080d00c180e19003c080b00d01103a6926030700c0d0503540307450701c10500300403003a0300c050058820b0219654500601d548111880b034429060402c440104170144000d0b50f0400e02000d2541c0c2100c8c0d90700040741c0c405d814100d18110740304044c400c43e1351290005003c860044500303a00194000c182886501c2c0c040050045c19042c0c0200780031242c0170150080e1041c04020840c0340320300920701d0200c43d031440c1e980710403004d15440401ea030001103255032410f68000880304141c8141c40458081404a5005205a00d600761 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 995598597 1250 995597347 995597363
    0x203010506150f0706020d1802011e0e010e04020d05150f031203160c0f0804090f021206060c030418020c070f210f0b1f080d1b0305070804090b04060e04 67
    0x11800310088081d404c9400151400d64082041d0240341c035451044441d007d40c3c5a0b1351340d002d014075000040c00c07a410031005400c12940c1301184a04a81c01804807200d04d102440c04c420700b501e118004c10043d000c0c00b40f601c1c110038240414000d01c400085004042c00500780c82000c02003441004255940390802900c50f41080e0400c0824260304000e159007103609806c0c140b8100c9807005a991050034540460140c811205c0400e061140441038018031404c0c0420410550500e2490a98142000009410941315003c0001c101c0075042c020310540d40104100351f281549000240c0111010354410340ca031000c540a0f400d000b0946d04101d0400c2c500b6624161040c0c0c0e4541d80c55003440950310783c0a0419982143c1d505e2600c1c00141140408a04c42d5551a00050340b5908407038a80440e000327541c0105d03480303400456480a403180e010103146c6d61203c5150000004840c24101942c90b44240c42e00509000f2001902250101d0203800c01504444150380420800d40e4070b502502803100c0640d0000c042403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 995599847 1250 995598597 995598607
    0x20102090108040b04030c08070b0f570c07050415060309021f05070201020705100210050a020c031909080625090527090706090b0f040305011404020301050615 70
    0x13942c0030074282d50082c0300342046440c0300f0031074540d03220719049110304443c1200301c1c00410200c2d4140c0700c80b07141c002b9a040c0c2d40380702441201860462085039030074244602182866520400709000112102c1e508136011100c50307070002c0c4100810240d00c041001e411900c0b410300c002440781400e120b0012412211402d40701154240074084016118144090380c0c4802e07040c2d401079259110740c006a01401054072480d560b00318500c000782c00d00299070311051107107082d82084440d180d00450074031003241c0c0308280010300c1e5580b84a0100203006695494a05200c045100c0210708400c4190a9400d142910ba6440c00b50b915201e0682d5040b00b06d480c860b205a070450005116401800f41544070078490618407403894032071010406212400c0c0103200d2446c10940000c04112070802c1d02ea0b0005071110143c0940ba080c900050481345291007198408040041d2a641d00c060440594015651203002800708641c4e06010303440c00c41c400d0381e05034800d52806011520342d01d00009520f9503582d411420b0b07403c0c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 995601097 1250 995599847 995599853
    0xa0b0405060d0209040203070c02040f05040302060a0905030d1b080123150c010935030c0702010908030a120f02030402031b010201022206090515040905060604091d06060102010209010804 82
    0x40d4200304100c1ca24140c090041c03280e03c1ea03031800603501c123201507078074000302c940b89004000540c5c40910b4452110b07171a107170621001c280c2c089601d80d0301c52448500464201102c0c0303082c40ca0351281c0003c3c1001249040b02c501500e410b2031041025820171940c80b150143d80b02c0c7c024102d0f0044d0944001e01c0310840d01200e089504240c2d02e503525040b60b6180705810808840409820f440105004480c22912000b01b001c0b05100c840c004030102180c403a9019400d604d860041c0490f03c40a04884150f88001c48c80c0f000316031145220074083c141c2c0c1e10942c0d403240c030240750103051540301a030010821820041c410103071641510a41f0701c0f980d0010010400e10390020003010110a00851050440d5000c1000121b1000500407001d044041b5080000d0158070b0800014170800d00303900868800d4000120703074a5200c0000003510190790310200d0000303e43d11441c1c0003132154443c5501810711642420203129240b4101c0c1c05000b201d003180400c0e00c44075038409004908034455524070a020810040210b008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 995602347 1250 995601097 995601109
    0x3060905062d1e151201090209040b060f0d1b210303111608091e090a020307030f1805161d06030703021503010f0b040308160321090209060a0b0405 65
    0x3d07020000050365090290441c8000e41c0442c2e48070f06015500c94052003504000807220310003943c800003004150b00903400074444660262001d084100400041880f66646410b4070141060042812960159600d0704210104240b1030700d0200102e208000140b10300c14140e00001c924101250084806682c0d030103034020300090b240c2011000703040c03040441504242d41b009240701d000c0c501c0d854039050b200c0200b008a803c100c41c0707428040112040c26000c1d0f150100307002c0e008005000301503142c4d0f4440038114014014502e207200f1042c100390000c51801d001030318501c0b01c3c0707000d581500e030860b000400d031811240f40c9100c1c1105412000400700b49807010f14407a26000040102a01d40c0250790b60000341c002034506001c40c1c01c2c0c50000004001c5802c00041d403200134064154140d04262640e00c1e81c038614040c03a118481960001428081018451143c40d41000368024480e1024401c2c5503c0000400501100b2030041320384601107903051402403884022a5005860b0f10325290920050140d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 995603597 1250 995602347 995602351
    0x303090503012c210c010608160314190308011404090201053c0307120b0109030201030b0f190503010c0c02100c021210050a061202090403081306020403060905062d 72
    0x7040c051068058135800301c2c044034480704400e0910040d101c0007400792803801c4540e19809481c260340260b2010301d80805912055040300d0b00070b229151a00d291450742c0341414284100b0342c1740e81d0944c80d0b0180030540c100e000c181c141c0704014060010101a90284801c0340c0481d0006030201d0b40500c4444035902406a0300040081400d12070141840d5148404116512a20070b0000503c0040104000e00358032500b14100c0411802c0c05006a81c000400600707442c03074500002c0e041548070100c00119458200c0018164180039001d428041000a4400c40e0900a802642c0c072035428010301e01d07103c40c42040c4071030303585400404040d0100c10301041030315100c144d003004a07006002c002030280d2094040c400980c1d2141c0441e000708035072801c00720a03802c4506941007428042c03d0140300d030000d42c50b803603540c590041d13050403c0724582d203d2001005150f80184001001a400041c020007005425041591900d20030303822240d00751203c0020005003407295220861002d007105035185644481c4a80035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 995604847 1250 995603597 995603681
    0x90f05090c0603130602040b0a2307230604141c09090905190b060109061b030e012c0f06041211130c031401080123091015030309050301 60
    0x440c40304550b0380307036410387c1c0141d40104030300030700454656040da42041ea4280808450341c0342400c039108911070860240100710010388403410328500c130035410036a031078001240c2060030111407107131400380303044106219240ca0700d1400340030b4091203c5148440000d40024510662039910b803483c1441c40e09002400f52140a40342d43c4126213003a440c1001c10034105412601481c0d00c1d4440740781c054009841000107500100800c41d44004010030300031300d56922280f40b43d040c50100907800d05100125070820f1072180081078040c110441000b00d1800d00200b040382501500d1210303551100d0400c0000ca40500e2003070f01c100f025107507aa0700024141c00074928072030100422002d59801451240c50072995021903440c0400d80d40c0c1501342e11150038401c200d005210580090000500c002c2d6428a40030058452041003000000070031020503082c4040b0101e03980701d480c108018102c3d8041e000d01400c0a200036000700703030508408a21428107000f07108041e4204084d05604050039079103140600d512100e11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 995606097 1250 995604847 995604871
    0x30201140d02041d010e0411010c05150702030a0206130210050d0f050a02040e130203100c02071502010c180311060d0905011a1003180209070207030615090f05090c0603 74
    0x3821060299101620244c0140c10764203281043c4404a8803030048103802840c03820104c0f0041100103490840e088204c00020b182a400d04291494842c1c03030400798480650b00740d081c0c4000c11180c1e5a001025140c001125802c4400646500c000303580f2070302c485100650816044820000d500e40070300c0c014400d8101c9894005180602041c521046550555400d640c8135000201000340d500700001c025080315503114003405c004140c2c1c0c0002e40d5052200040d0f480780c2d45030084880418001d000b21001001082287e85045150380c00081c02000030080700d001265215001204a25900c0c55803805d80354041300345230b4041d138004c0400c180c64002000c248081d540703421a00340040e03020b0107001021210009444803d00c254802c128910035103180b84402c05141c5960010081d43c1d410802c1c01481d010340e400d4410741c0364000c0403810141d554001411582c140080030000b0545131304c003001102c841328000c1003039521124454098070001c0e6000301e01075002c003100040340e24140006541042e910441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 995607347 1250 995606097 995606107
    0x3080d0914010510035a050106060809030406080106120617010606030b06090604150c020306010e0709050904031224030b10120c1202060706092303030c0403020114 72
    0x80c82d00352002221842e28000202c0003c008008440a004410425012580445030b05031154010b0032503858030a40c0700b10310b044444484822004451018250450940303072000e02c400c0c280b1a020f0801c61040e00300007113504000a40c0b441e0040151401e80303800795a016003907440d1440441b081180c901142c41c0440c3d460078009000301002d00326181d0810040004201e4910b00b0401508032007501c10200d02503881005940c032503548500031903082c0c814030038034030b0502c08400c0c00496040c281c0401c000d402d845aa00003003035040301d91030884d00c10081551103405081c2c441d0305000710307204d0603100140070036800c80612030104013a40059030f09004003100d8650020091419000140c0c4c99401614a10316141c240039120001c04a19001f801d0016042d91041110742c1c0c03003041c03002141c0704501c0ca010924090b441150ba4110484100a400600c140003142141c00c3c18800d8481540b10016889410f0340c1071080b054022081d03034820491103864a00b014035540041d00d140704240d5001400d284100b003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 995608597 1250 995607347 995607383
    0x15060f06021c0206070c0212150f1b0909060f0114030c04080f030909010513090c0311030d0305010323100f0c110f030703031109090108160f03080d09 66
    0x14090081449a00500280d14070680180c080b0650701007110464000c01c0400c0651500400c4208005038142c50a10003000003038411810800c2414508060072009010320409040d0440d11343c0c050840d201c6c40f8a03d4403882108d10b0001c2c842c0809154003e00c14500103200b625006030f159001e00b1042c105501c000d9026600c919030740c1d004484005060708041030900000c0320030440e40c0081e0400700019450056003000042002505202e20f600c150f0309160000448072039600510592940108114100f41c1c4901c4c01019000c1d000610074040d1262288184903d84030b4082c45040b280c005415261094140f01d4081611340b00c0780d90038006218515817882400d01da1b1040708030340510300c20001168a000440203161000c2c00601313440319802680400000e00b004803c452015905050000d41905241d21901442c00f0300006941d0002c550000003641040105070041910b10780781c103005c481c5440b0400d0110355507403800f015004400c20b000a5009074000e501c140b1603a03000d00300315012109818 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 995609847 1250 995608597 995608619
    0x90905070e0306161103030408040b0a050403080a17071b0602090d021c0201081605030106052802010906060b0f040e13050f0a0209070815040c0311070b011a03010608041506 76
    0x15413a0035501341c48502603104503a1043c5025a280700820241d8a54106903d0724140360140e8003440ca1071901c001489482c10740540c0c01c490003180d02640d0b4980b542e903c550301034101d00485940321a13f0701400d000480f000e108403554294035601e144a001c00b0041c07900c40000a403c84851507800210071410b4102590360001c843c00c6183c000343d501c440203019032000505c1c1d50400b0b0486401c0031305803440481d5042e0098266415a0494034145895503500c1c1181030305415640450005a550305011010403079040d0809840309000702c03018407401d9919040750030288120030701c42c01000c80500090060164026100c0e421034400140303103c040f82c0c85d0b19064102140c180b0405c020b5440282202d085081a0102e150f1010180c00c000d011482d00e850b291110059105109104a03a00d1380d403913402c24040d900102c808040491a291a01b0f490310307000e40c01070780c2809190038600042010440c441c004108882c141d41c4c00c1c0d51800440c0e2110360303c500c032000322224040c4169490307440216000a0700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 995611097 1250 995609847 995609851
    0x6030d231b0d031806050903120a0c080124030b060d0c120e030a1d01020718060311090408120903040e041a06010c02102d0e1c03090905070e0306 64
    0x502410482072165080e5601d8015000e204509160400f8403020032000383c440015101038014070302044070358a0349041801c40c45140121502c14440b141408407120055001e650000d41e40e07144c4002c0340e40c13141444054125900110b6058501d0120324100703042c1b00790881c80c0e0324a405031161303040c00541c079030013030070303119008622000202c80034607a60b01203010340250b602003032039900954a03103101ca003001001d40c00444e15a140d54402c942419041c0d92080040800030074140007001e124a0000320b0200181405202c161a44802e07842d014601d03140c42c8000310702856200c8001c502d0029440803c43d06e0710b10080c030100242c00b0601c8001090b0510700340003403003a4803c814003100f4040c001c14007104203030081c0041d41000038410030100103840d2200307a03071451000c90030016418a9482c0001f5000d420030110740412a5007a10b051400d91b0b0803504c5448525411102d01c2a540014003041038481c094000c080c0010b00c5c0315000300660305040d485150401c90710305e041440c401606010074601041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 995612347 1250 995611097 995611117
    0x20c060406111903080615040b030106053001050312030c46030f02070f0204021b070f0303090611030f1605150f130b06040b0f132306030d23 62
    0x1c1707070100542450b103151040d000751003101c041c900b41030810319090070900050243c00c06221000a08002c0b48070711854001012480c510f203c0ea94070540000805192000e20840e4000c1c400c10032400d0300c441d9140709880c800d0110700ba9190402103040c151001c0c0309605540500f04407420081c800c20440504020040921b005001201c4c04a150100900300d0305000b46003105e640c414010140050806814848403030340480340940c407400da44d0710200300c407440500007144030306c40c400c00020440b6400036410b04680c003036128050000e40d1401d055503510340c6800051559041007290034801c04608004d040d101e120302880c0100040d156440c140390105503004405400010400c20100980c0184156132043d2032040c2c01240c401e540d036811010b000058213041c0b1a584030150b48e40d15071550288821401d00c0200b0100b0380407449001040202000740d60640360722091341390b10920000c01c4080c54028000500244401151001d040712060254042c0c002c1c4010840c04121074209540054855501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 995613597 1250 995612347 995612357
    0xd03091e080601050a080a0204050406020d15170a0314070501021b0309030f0f0706110312011721040909150606020709051e16030e0607030204080c01020c060406111903 74
    0x1c10310201d00c0c94034405074043c512800600b0014014801c0c0071072101c0c000d41e07040d5008036031920365103010806802a500402c420503d4180d0208803108100c0340001150a05d0000c060540100341882d032315407da0200150200d840f4100368194810901d00500b0854003038000141000c090900c000c0710300d19504049110350b400481c0c40c1c0781c42e1600707010140406099200904d21110030007212a1180154881d20040c000d10300a1981c1e600400e004503018000030740b03000c61b010b41c0c43c5c6035010b812580f8080d042a9034450302905030b50791309511210825021440c8841410540f03026020303400781a450800b220640700141084223103490350700851001c0d01098018000075400c080c0c081046901c02049000310000c121400860060030103c0346400c040341d480002d02c131240004054010380001c0b660380350b091040200300300340b20b44d2581c05081902c000c40280d80444c420b1000490f991ba50b40c520b111342c070000c10403007004000e0040c060304040414900540d60f26110207080c168100c1c08001069021407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 995614847 1250 995613597 995613599
    0x70506100620100f020d060605032a070f020102150903031902040e040215220f0503010e1f0b060c0a030e090411190b1602030601060c08090d03091e 65
    0x26040240150464100c4145440b4000d0110312155a50b0700101c1e4100030b20307982c000400c901952501169800d0a15000c00e1021a50b1072100400c2035104844d565403171140c1c541c444011002050309581d005245640550910a4071b4070b5a0003901500c680480c154482c046d01d4200264030802c04900c195400000345450f80f5201092240c4100181508903485104000074404960034000681d0829015a8140c803d400d1040a0040610031b001c0394030000d56406c00d4800d039010b0115212400c0d5a80403101080301c2c2c0e950b9040c14260354107514106003640001c07000003851503034495030b00229a001c1e60003080006000300460b00e00d90104c40c204400343c00c807030743c50414107401030039100340c4410903501494503190a4444c12900144c40800511648518242d107183c2488620b206005d440e8104000f560740c00d6401a03201064002d1108034040d0050500010341640584201000141c10644840c50100448100b00b0390f800440400c509114043c2c4012542e0300d03841c808107840d04d007681e01c0082e2407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 995616097 1250 995614847 995614859
    0x1203050a033b100b0a0b030705040b040b0310060c020d1410091a0f010f1517180c0910090b060408030c03030403030b060a2c030f0a030305010906081e0307050610 71
    0x10100a005a03d01802c00038064455111601072000325038003803080688980701e00504030b070240f00f80d40c0202c03070f0400d002c01c011500f6050700008500548502c0d0444e601296110400d51340e0400c0c82601030750080e403900564000c50244d202c0c00701e0020351441aa50b06444030b0350400111152841e080c1c2c2e070600704d070031201c1c0511031803440c45800c1100088414003540c5050341941c0062000e002d1025000c1400b1001159107001f015071041580c00c00c039152019140c03005088202c0d4203900904e412a00c940d1245460500784210480d01410000400505d15400c254521000d131031050103594020b03404000c00a40c1c40c10600240c0359018100b005141d40e418a0704000b4207403060300c0900361080200300010080c07281c00520020a003111860511030200004001c1e6401d4019051400e4050140d44240399241d41c2c04210319510500c40d031400c0060b6600ca40e41da03400c584c4980a81e00d040e41c402c01070001d80201c0681081028420442240e01c0c000085e41c03400c1c02c1c050150344640600e05898414803503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 995617347 1250 995616097 995616103
    0x15061b0c010c150504021f120b03010509120a05250219061d030f060109060806150108060108220b01060201200a08131709040e0d080f0919080d05011203050a033b 71
    0x49d404080b00240141d04083c0003164903960401c40c0e6013104180028400342c02401041a2003000d10b031084c1c1583c001020035808283d94004c10402c92140c240e14901c1c920315207001c440302058510540d11011080007209980340380401c08030f46d681d85407184044882a48030104103050183c0311000001c01c901c2d1420703660520b020f13005008414100c181e080a0913950340c0c42982c2c254000801d00e4848595211141c407804120500f2120403e0040602664800d0207138254515040b114180d000300000000680f40e007203450310404110605440420000600c18450301d42c00790083c040001c41005082340b50348203042448408074022500002040c101c2d1145000e108100c201302a4801501c0d03841c0c001c650081c01d5020080c240c40300060180c02080c9001c00810031b8016540c440305035629001c0050034140c1543c1c0011801200e42414040086174240c2007064000a05505071215401c00f607414a00350702900301411034554000c02e081c0d2821410300b00704982084500c0910004400c11100c1e100141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 995618597 1250 995617347 995617361
    0x1e090d020706081b030a11030a09020f04090203071e080f0f0c01050a05070b04051e060f090c0604061209080703031b030501050d0b15061b0c010c150504021f12 70
    0x14420700f201040704040c1c0051036081800004002296250b450140881c000d04408100e00c49070340003c402c001e92452580c0c40748841ca40219000c003400340b090400c00044c0c5040340b03c000d403d5041144104050440e4a4002c07026400340004040a00e0301d800c2001e107000d03030480030402658400ea550614040e4103103c2803c902c0b50a103005850840c5000300500140302d44c2200030219180600045c003440420f00107416030302120811101d541406c10b60f2590307685c10a6a004c03450340c41d10b9000c164001400260066813407405003003542170505c1e1803003c5c1c91001d82010309034481d684030011100020004401012024441c0e14009044c0c1e1503034000e00d0b90b594512018105041ca408014000c50703583c0812154902d5201100000540c1d0741c45200e1444640c0e841c0f41500000042881641e182901c2e80c0001d0078800c01d01105d08041707216004491300842500c001e40b60304590704080300c1070f2601d03400c4140c0c0240003503c50020100c051201c2999507030444a03c0c0c000401c10000e03078003503c2d01b9004041e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 995619847 1250 995618597 995618609
    0x7021906330819140115170610030b070804050a0816061503020a05041a0a29281106040308100b04050a090506011803050309010e0d030212031e090d0207 67
    0x2c41c42c1000161400e05003e1640b002805010300c0d1103951850f00c0307094001c07190722000d078640300348019603a440310042410707411803012484c002c000004486d00c2003041948100c903040071194416031503940080c5d841e880064010f48107402214032440118007040e000303000d482c02d00304000750300c2c81ea20b05241040340c0c9002c8140904407034903113003040940d562a44e0300003544c00489001806a09103c202403811b036102c141307140c2010100400003265100c01c040303803c1203a40c00f8100d0854041c5002d440301a482440410211240400c07054001081800c03c07035030ac0c1e40c5042c07d0800d2008841c0300590715010003110110700003440501040556988071030180020001c50511070b040c076003404002040702006028940e44656913800090302e507032291010081446000c01d49402158803810156241d40c00b0038800c90105050000c840401d050511521040a4150b0f0240400920301c404801035580040c013030754110b01040740c440c480d00410700c0ca801d002c1d081280007403080c2003400001a0800b0001e41c025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 995621097 1250 995619847 995619853
    0x61f031e1103010912080727030b0601020303070c11182505090901180b0a03080a090b032403010b040c11070f0602070b070305070f080d14070219063308 67
    0x44c10000c1c2007486aa260507144e03042000c400e58541c4001c8640b9125001030760102c215410490f09459404550710301500c2c003c1c3c2070300b5003a5403120010380e600e01c002c2c0c401c1c0d00000c0c4170380204c20106000841905650100400024030311b1281c1c041107070303003c8054554a104540132810080c0e6110400041c05420800782011420286088005940c00205100d8050f0b0040d40c040c5005004855a00c18007450a0082070780000a4aa040c0a500c44d040010784c80003086814a02054903107011050700d1040c107610b482d00700c0188102201c8041c1c010400010794040d9214803502c500f03a62a405000c0b001c4c0c100f5070322155040c00e0f11004a14150199000048040d40c1c14804e000a40d03000c1030010a940b00c00d041c0304c0d076034151883c086507980300750000a8440309802103198104104a001080408507052040c4807104402031052061001541c150000d42c9c1711010b4011030040e0f41a4070002540140c0f000524682c841541505000c0040e05a290100000a490a5140c440c400c9000942420801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 995622347 1250 995621097 995621111
    0x72c13080f1225030b03250b0c0304080106050102060c16051002031e010905040201020a02240f0a0e03280309090e071523160c080d0e030609061f031e110301 69
    0x200313803908110a182c5031540740300f07031200c003c85d003c41010000824000c00a9030b274807840d80e08030907240d0300300d4041d42c0d81d15424003000003469880015000d004520352056540381140d034201e8402d088c590607804441c5402200001d44845d0301c60b20185110701412a2440414038010b08103e1500405030040300d18a444c0a040c0001341c2d034006100032150780c0c1500d02c40e0345003c100e00716002260400c0402e0b5a0140001a00d80801e101000a01414043c0344c540315800c0180380c0805d9110191460a281415041d01882c0d031115540301c0c2d01807002e0f000c0d0500b0f161071030b06c9a2080040d80c00c003400f0f0320300c82e82c0080c40420543e80c0941e201c00122100d86032074a112a50000a60074580c510300d100148180007080b4038103422604204d28900a40c007408645c840b0b9610380d12540c48581110070040442e503040b80e220280d00300456411b10880802c0003919190f5903449500c1081821003048900c6802d030844088001814003201c0c403582c28003102c21039081c020310300d0a8021504d8409032a40242d04141e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 995623597 1250 995622347 995622349
    0xc02010225050a122a0b0721110403050c090c0f0a1e1106010b1309020c01180507180209100c030e03072c13080f1225030b 54
    0xc50070101c01e5100c044010768620a0400900c0c0071925540641503c42c204002c9805940098080298810f84007405000342001c886031400700d022902c014083c0c0390020300113015140308640100844ca044000a03d6117a60403a8a40403990004441c4402c484005014010702604114454000d0f004449034040c6181c02d200b000031500440c000040c00d41c5000c90028040c0307001c1d0000e9032182500b100c250f0f401045045000b0b18040c071340412301c0d103035006240011400b80d05020455882803480007a4070701c00c602d0000140000c1d842184200c4103556036041d6083c0200a01031102364080c00b41005004c02c1e41001100500145511608000a40b0402041c1d8880d2941a094002d0103528240149000c0142c2026250700d01181404c03689400360002c04200e400d00e14000c4800c0d594a40c88039855880c0e11400c0701c80240082e100610306180b041d80c40d0000451410080044c04084100d06003001000340180c81440811355401c00090148442c0d240301d46031102d0b04101c99041d61070b09001c0b0910b010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 995624847 1250 995623597 995623627
    0x21506120a03050304080405060d050a1b0c02010c0212011407020c0105160219080609010e0c06070c0510020a08130524091903050a23070602060a05090c0d03120c020102 74
    0x601c001c1c01d0040110008042c02842d40c03c0d1402450083d020603540c08169180f103000700801c95260700150b281c15100382c014001804500240000d035201c1040030702d00d0b50015999110040303c200d07407081a40003450000070080c0560704401d40000070150030f905200c10045c2c00c014800960604005040c8485200211170324000000990191016038642a0007030201c034503000385400800b07092180006000c07050405600012900c10390030241c540d012054810045240300d0010050040e10398104140441d2400c0300c00c3c1070001d10540111038002400d0f13540c404d0690002c03031a401c10303404140c0c02080242480c1030134441c1d0916041e0580380d52119020f0003081800380b00003180c0200c1c0b00044c6100040762040d4504090342e000001c840c0820020328100c40c2031120814842e030b81ca81000500780c0f840400055000580d055078016004503602e103c402c10052000810103681c9104a0f00c084240d92079006c4982e460038007a5946074415402c0211000036603d103981c3c0e56045a02c108a051704000b180d0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 995626097 1250 995624847 995624863
    0x1509080a1b020619030e01150f1211100c141b01020105161805060f030a061203020a11010e27010602151f05100504090507030506061210080a0302150612 67
    0x84e00644650f40c3c03034a6012002050351036041800d84d860a031200340381c0c10051031484211181e01c0d0070001d415403102c12480003681803080c010701c2000d038000300c0c02840c5050480c0c900311000c2450000d109010a40396009030400150b5140010340011320308484840b101d4000341d14803c82070000f4060b0341003007039030707070300d8050b1514600e42c104031a400680d0320002900003c5001010010071450302c5400b1130020240c288d10036a1072088e80381c60100c2c0050040301b60300b4004421901500034281950045d11440448050180c80300d040003041e10003030025a030764150031018141081981c0e9080f203020441d1460303400041e007048041d90b100700c0710a00140d00f400e000c0c5600404c42084000040620360b480300c90350301d460b040581e0065409c0400c41145602c40054130486106220a0080e40c403012000d03401c4410035034445801c00700c02c00400500c00752200c080c47d00036009007010120980da9607c0d040c01d0070031803c030890043e00a28225100c440c5040780f030b513810550445040b01001d80c0e2040040d628201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 995627347 1250 995626097 995626117
    0x131b2603030a0e210c0c0420070c0b0a0c02101107140d0501020c1f06030308060105090307050301061205150c0403032003070c05100305060603131509080a1b0206 71
    0x8030002c445441e101400600a504c490f1400741c02c0203410340c08000030342c2e04210711040951246901c000241c0ca460b0085a100b03c5902d88001c000084185c02145558042c44042e40c21282003a00003a600c5600c1008101c0c5200594500f40104050300c1001f08090a01258a04010270001200014a80030648808442c00640350303c15507407240c2c000c02d4006a0940000c0d21a5201142030340b04004003007050040d02021003c6c2044c1c44105441003001c46546001c0500004c024400060495014000070301080000a086900381903a400009095034100d0704080c03400c041c0f00301200d0811008104c440207400720400c42a402d8604080360420500940c400542003101c00e0007003400451780b504100c5608500d1206503540c5004500b44810301d0f82080c440c46000361a8080c100900320711034811a0b0040d140142001d00d1a10390400f4840341d043d00c40815140e080c80d03144d2081008120f8803404103881c0c80342c82d086480340c04400e0060071481c1102c090071030304001542d1410041c1d0b5400d0485001140c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 995628597 1250 995627347 995627351
    0x140a0b0412030e030601140117070206190e0f0c0a231c0605040803010312020d0903060c03060b1b0609030301031e17130305100c05070803131b2603030a 67
    0x510342c2800c48140c40c1901c1041d4041c0608000880e42120340c1c5100320000e0380a0b2100c02c8907550038058101101822110000160040307808951108000c0d00310380e1354a03920705408206036051011150600c102e041c009501a4003001c0c00040354104007038540700a00403052180c0d413801c0b10ba065014445061114913110700c00501060b440c0c0c569040c51141d8140e0031030301c1081035251030301d420911035000380820f8441603913000c0c004490520000d03175520021038583d14102d400e855075071914060f040c009000c0051644800012811410070000f8040c0e14149510800115181c90080c6003441405880c9010f00c1e0810401032001c03c0803142104046004851100f80a40040c1020440f14000b400b01c1c1005400016080ca110000b022280003600e0040e401c0e198240e0f813049445081340c00315103003000420418045500030540384800b440d8000c048031898600020544d0740c510b500e084056002d5102d03580c04005003d401e2074842c41d160203100400818a00328041052a5a6800002c043c254520317 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 995629847 1250 995628597 995628629
    0x215090a02010e10030905030313110d051b0111011109040b0102070302010503071805040c050304050606040e0a0b04062d0506010e0d23162301090611031e0301140a0b04 74
    0x601c254408480386d604441501c0d10790800c81051803901e441128140c1b20f049049070300d4400d40c034003c45800f03c0c456004004060a50311101c00140c06c6000b87e040506102918416100201e000e000d1040c040a41856003951820305004003c100c0f070300522094119030100c00d0030700040c5d03042001c81c0d42000d0542004040f075410030343c101d404e5010541145030003505140c90f400043e50803401444c041c92084c401d0300c440d82d44040a02040751070700307071608450394440b10415021515480d90b4a401074045c05001c19600c0341c0e1000d1034800c10500d84040c000c2c581c110000114520076205240d0041001d1a0145040c3c0c02e20001600700f1066441c00703000c40e0320740320440440d46004100100342030f00c02015030744100c5994504000c550201e00c6441042641501e4050407020410f40e8820286416110220b10508140c1c1c1280c0708a00c0d10712241d9144010401002c1204140004903861081a600c5541e258145060540f0400007c00d00502941c42d40000384150038a28054600b80c415400c401c485c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 995631097 1250 995629847 995629879
    0x9080105040b07230708030a0f2a0504050d230309060f0f09090c1c09170307023901020109031d18010b04090605010c0c1a190215090a02010e 62
    0x450202e041e441c980c4c0c3d80004540080003a10700280d8071030a0500303001c000040000000c44140e48454800740150740102540b51a00600700c0300f044074112076458090308098441e408074220b0310880b2401d460500810761040c0d00c01c0c3c2080404c1c00b650b80c08001a600305051030020861900420410001516000c980086042c2c441d409035503562100910801035030800315107100f650360000540c04100340c881c11416001c1c00050044e000d4280e440082c0c41c9245c841c1c1090302c50507400140202c030850080848114a4405c60403560003023040c4400d043c040d0f9450100506454001900c0032810b59050000c4100400d07009015507000110f01e404514602c0b01c0900080c00c12078015402070310481c032560020070b023620040301920584280c07880070000551500b00640f00c00a200f0401400041d42c088184040c40900105117200041868124141420384184404200100d4484001648540d13103414141448043d1340b5001542d040280401180a03000206041d00c3e214106002d0810380c0928681 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 995632347 1250 995631097 995631137
    0x21050109291c060c09090b0a080307110d080403080c0d0e0607060c0302090a08070f06032c030403021c020102070f081506030f0d020a0c140d030f0e030d030b0109080105040b07 77
    0x31550f00107410013244204100240c44496103000d420740840c507080d1500810f042000206003902c00c803030011410603100d9a42c0880d61000c0c2485545c005041441401c005404000039102a61243c200c0c80c2c4c0f91036550940e186041c04010f500e2080100030041c4082c151580d41c12620381680101d004918002000801d0300a44500e00c90103802c0f4000200c0022007403408203c000660755608a20603a040c1d59110072010380d00020411044014540c241c0901240154404564142540282c9084c20b5807900080c0b100d5528000042800c812030369648119039041c05084080c107090a040055103081c50882c6548054410350031f002d44000341c0210308250b4041150081c444c003140110385403030800c1c810083d00c07803000c0706007152103140c0b00c1d401240484409031946002c030000341444144a510340c80c11070310100c42c11003140034412440c10030140c1e40c8050140341c0d020111520081503014900000410306c0546500c91035040e458a0288400650900d007403d410907903a29001c14008505014440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 995633597 1250 995632347 995632399
    0x909050c0901081f06151b08030118150b0f09010908061f060c020f040c0507060e0d021009260f040305010c14282105010929 55
    0x1500010020000070074201c00141444c0070403001c024801001a0b910080c020b803500d0340201d0904126031100d00e100d1906c41c800c50300b15000010030042daa244584c40b40c0b803080c0d10070380140305150355280c8044640c0c0901d000f4400103465041c2544c800c0c43c9002c00d4038010b80070701400d0b424000000148820703075038802c4414a0150110200791082c500b0030703001100200144010800551000400000b002c42c01403c0008149401400710b5003080c0d103420030080201800811101442001d21442d004a043d0b803107070114108003500140340b40c402403207011745420a803404130500a414125818005031001412019650300b54105404254410001d071085005a960051100c0700220f0000706111301500003201002e01911092038081c20702010154a01c01c0222200d01000d0501100c80b040300783e400081c503140407178508002d6506070030010400705505c01040071101512180140940115441303520102c06174500d420300300e14000340c850464005100c00503403080484000150114a80340d0740300c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 995634847 1250 995633597 995633599
    0x90b060d0f0209010e03070b0a031d1902010e1c0f140a050606180108031806040f06050403050c0f090a0e0a08070605040308010611250b160b0a05010f0909050c 70
    0x1018020901c21040003e42210880b5400a6194000000b043c10040b0388501900d900030f6a0f03600d403c0310784030281c014000d5080322001e03100c034035990001410b40034404034440000308200c0d044a80d101e800018150500d01c480c440c4111401400791038520f400111035040203500070349a101d11655030900c0a414030001c881c80400f4041c10000004100c408107a06104c0d0208032800d8136501000c406194420740d007401b841405a004000e002007940790000b40451180008200354035041c0c1300c12400c16416607581c42180840c5001c85d042c0200407051055454100041d52941a404000d000054080d4400342074100f1456462018000745241400a0416540c04c0100e81c2d82e59201440c0000041c04c0495050340020405800483c903070784164003211402a9440080240010030391081900c08100c103054030b044068030a00017000c40c00900503003a034031080a400e0f0141040303410300c1c4540e00801401c58220390314010052141000314400f817800d40d2100d2000003441405441c0142c0303040c40c540202 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 995636097 1250 995634847 995634851
    0x3020409080c121209070b16020d1401023c03090a020d0f120807021b01050702280b0c190212010603150b011815050d0f020409180309090b060d 63
    0x21590b80f1079154000c001d010044400421160750380d0a1054580c886400341c40101c103401c02c6107a800e65043c402d007919850005000310003213002941d0b144a80340300b045103e081e594000c50f00c880840325410201b405101c0440040035603c022901d0f078020700160303200c51450000c1c003001150050a04112504029501900e803103440c0005041c905e2800562030b408131800071107034000061091080510501810864000701040c4c44000703640c120000c2e01c5450340d810400148142d00250344c5210030103a5548103241e501d1074081d50603421220142c555000b0180d82c05003040014865140041c0414103541e040190400b05000c3e0700c005100c00c82e10500b4002c040d82004c101005004041030031001001541c03c0402c80e03100100e005488043c002c031030b004804449058108240380710012031045141c0d031032800754a00324001d18090300302c4601c16103d0034420b41c00f24040c0807802442c8196981c00032802080180a0300c1586c006000300e40034015001495151100001d06480303030000c0d51111080c052003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 995637347 1250 995636097 995636113
    0x402070c09050702010b0916090e0a0e01050c031b030405071818110102060709050904060504020d1202010501060e011416110402070f1a0705030f060109210c090b0a03020409080c 78
    0x34068041b12240d240305224850124a4140014205003010b403445d450f12800e607850f04100440c2c907480144058921a203460700000e03813000030f1103041d00c03580c00300c006c20303840f0700303045003444103400c4403400c1d200904c0310820511001c60b4000030814100c80007134440007040104116401c0282c082c58140601211440340020100075010410f0780e03203c002030742180c1640d9221801201c40b10042d108081e000321001003c1070100300c480c1c10082e40540090802200e1a05075501c5105902806418000503555540180b2036240e0200014660840901c3c1c42120043e280e01d8100e107030f20940d1600c1100600030000202004800802008500401441151907101c0303414442c1d82d10910510450304c140210710582014501c0201060140a00b07603101c60460b0b541d40c01d09052128040d10090501c10344c5100010b01210740049441240c01e8160800400d030011301c0e0101c2c0880c9107030403040300e050500d160780120b0346031081d1100440750122408034050086040c18161071003003143c80400b60081d186 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 995638597 1250 995637347 995637361
    0x1021f0c020f030a09030303090501090206130e010503010209180603120a110106080d0203070b13060c030f0506100219170a0201091e05030307030506041514190b090402070c0905 78
    0x80042000515078003600c40c2200c55030b4480b5100c0c030580f4400b4000c10301005040c00400d220b43e00901c000e82c41171000041c420010b400091860f045040b422140c48000f807400d0200817180b0042c9801000c0c1036000b91b013040c1c2c0900016030014498545c1104083c0074400107100740d40c0401c668035034607055503c503503654a09080d000341081881c942800e1150308003440001d000000041a0900400542c0a1070421450380d403070400c031440103854800449040304028021444a1080d00404852500d0024070400800e0a04017610801481c1920500031440c101d5812500414401d8520301683c05103043c21100380741c07880d041c0101d02c42120402501082034202c440e015441001921701175992060443c20000311921121448000109260070078400301b803a850203504a1500407000510219100c620081c240c550080158850661080c03240810700f84c5060512100d40940d1008034001d00103420100c01e849a8410381580d24002e43d03002907020117018008101002420074080d0070712444c00e1403a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 995639847 1250 995638597 995638601
    0xf0606092d01090f0e04080a180605070b0601030b1023070f020f031f02090109080303130623040f02040e0615030d3e01090804090510031505040201021f 67
    0x20745030303001c2a442c41012808100070845401151001c10740c00c0c60540c4c4540d25207403603402c80e20006086c859041d4450701100e4814008501502503a41c0300764644109007486203044a000d8059130500d4600351480d4401e80b5000145c80400050341400c2c48015161003d650307501100c205400440c00300807400d201088003e001a00441d4021503168401d01a03000c00c05880740c1c58060786100d0040000e0040100c8401e607005040c0c105014109044a07030344d1840414250350040b11002c0c8031013a0700000008110b01071041c08048250a0701c0b0703142410030440c00300314a04d0090b20140000c041c1c8148582150f981e41c10100c407020010003502c16905100048400045103a0a00741c40303402202c00c10013030715100e0070898000340f45401c403030070000000210341c41e01c11103c1040b6014a00c10294580c7c42c0701800d0055056091140f014aa80d442c50a12540202c030f1000e801d09a02c0b040313114040000ca5016104c040c0780480003040004c1c4c0e601d5501c0180c3c40c040000740780b80001c60100070302c0201e2105036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 995641097 1250 995639847 995639929
    0xa0911030f0906071707050f040303021f0b0f0d020a03122d09030b06120106150e09060306010b1602040c0c150c1b030201060b03090a020114030f060609 67
    0x141d1030009007900c900380d41d40d03140d10040302d80c007000461407840255080f42d41d0003210340095a0341480d03460a59081802022980b158106501590141040000d0082003412403140402c1c042c8003040380c1d45003900080d03c08244405468403a501980a50b0b055543e844840b000442c2d000040c030200403402c1d1005000c440c540800240141d403e5003805555814941d9a01459003c03030383c0710a44541569110180d500d00a040140c221003a0304c112444c40400b48185006819030350081c4040e000c410000030a82004443d10900414140e418046280c81c0003402c2c3d4151004600c40f1504e400f1540082c000c19034020303001a60250405010301007440d0800d51518142c1d000b85128440344005421060544260400ca1400103540300d0044195448000c101c2c1c607814424400820076682c1c4101e0b400e080d400c01e650a5100d908440811001c560300007860103610b450a0031402c2c00e501d81a00064410600285110f004e00000281e41050766203a8040100c1c10303030b89107601c1180c0c880800760000c0f0f980721 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 995642347 1250 995641097 995641111
    0x9041509050105100c0c030201030905030d051f0506040e0609131205130b0901090603020f0c120a0923010f05041e080c030c0d06092102011b050a021b0a091103 70
    0x2410050320394451082c40c402c224580c01821b0a130140741385900450081c0070a820aa030540010311800340194011f02806002d00d240b030504002110240d00c0b044e4852400750f00007031154008010402004004c0d400c0e8560001003101c4151090340d408254041007500d0aa008166403202d80c0b50013140d5030000c01400c51395040d83d42c4132515a03103410b140001403190401031400300b24100c0302040001d00c660020500c5d081072a500078204095815150f281c030804100450000c0c0022076500101544001c6282c020170000c40d102d04032035811090282c4107502031942c10b0402c880640c0051a55001c5ca04650043c0130368101d00b940d41c1c03007240d008401c400540c000c91b401400340d2020000c0c01c0c60005008446420b0081046490300f5407569010001c021580c5e085900c50507240280701600c2850405000d800d01c10380011500c00c03528080d07181c1e030622292001040c44420300014030569030024280340180e1040e110111250000c20000c3c140489561200d4800703410540007180711281e41d8003550150132 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 995643597 1250 995642347 995642359
    0x51c0f120305070c08190e0a0806010302121501060c30140f12130f0525030c050108040302010e060a020d0e030915070614040b0f0702060c0f09041509050105 69
    0x803003c408a07942d05081e90040c01940c2d050250a084503050411071090307407038504004408400c2d0402242c601540c0d40c0c822043c1c1e0b0004001002903040c445e41e103610303086105001c2c029000d00b102225140410600a880c10842505089010401400404c100000c0d0030400240010031042c0a40401001010030f4000504081040301d5980984c0e401d603030300d00001001040c2003050a98048165800003080c01d002441080c65100100f000481403c1c5450f0260010300384080b14824089500406842e001c2e441c40040e110400118040e02c1d0240b00380c4000f481c002400e604da60070220b01418110150360f5403400740805006490700309500529600c61222014003614040c206020380700e02a0012040d0041d1002c40601540c004201c028819540300741c10004041003e080c0c01003144000b01c2d805c5910003944000d00500d42400c1c1c4031140d02001c588010142c03841d1188026000b4065150303131a4910364080365102656075030750402101b98004d142615103031951800e00e03d000e0a002e11030305010b04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 995644847 1250 995643597 995643601
    0xd2f041508190803010902090310020301030c1706070e0d0302011506020c0a0b0c030a05090111030304110411032401030621111525140d0e120601051c0f120305 70
    0x1021140850030183c0c211181e40d080d83e103030180f00c1001c0d5000c00b801d80c0d03040c01440d0131100410f29a201031400b0754024406072a4417410704180404000d520340300c2e450580d014000700302005500c20715610864038150b076002c2100503a03240907405000d50117014140c46043e5a00403078860360018040d4100704007116249400396407903043c00740ca40f00e4406015483d800030000356030568065002480098018544502c40303a0300030b0022130440e00f00b510200c0d040c1c800148492000e02c0c042c0501501d400b0100030140c030b10b0030300000408031a50300042e440108841054010a0740c0c1c0617074032070401010400c200341c0804403401e02c0107000ca264041c08413680b441c0c105038021281022202601c0d00c4103901f894a00d0030701840005142c03002003160581d00c0b106e4500a010004005d8220980d100341d24000a00341401d02c00c001600d040c605496040c01035440b416251041f19002900c5411508291440c1903031002040740d12200c445c9192001e000c04107425002c40070482e9a64502c024070b005598200815 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 995646097 1250 995644847 995644873
    0x20f061c0c05091c03111204090605060307170405120f03270703170d0204080f0606090606090f0d080c0601030303060b031e061906020f0c0d2f041508 66
    0x64010011000c1c0c02c03c002440ba07138803080b0081c200c00c002c10b0003400c3c4051210b803282d08142c5000000c041100310300e070002c9010031001e0002e010b40380c0906400c03200301c0e04500c1e00c1c072401040d04040c00c44024640301440b0108042c84018060074001c1565403455aa6842c010f425968447c0d2045c0c441c40681e14252229803800c0740900300301d08240d81000058100545142c40388280d00001200c0050881800c000740d031924806840100300804000703014008020b44680040d042c01402007440d40100c20200c200303c4190341725001c8039007101e8101c54041110301c4540c08109000001d01008003810300000d11724126503c00038516040b2440ae0ba010301c0071a86031040c0d011240400d50b00e03640040c2c055440e003044000d40c81c0555903c003001034600d28044800d128030b502e017078080c0d038000070151700700c07003100740100109200b190b00000056030110900c1003d9641c2494090141002c456000e80120a142451a00710b10100da40c40c0000d005000c809070740703000741d03c15510601c20846944550320718042c078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 995647347 1250 995646097 995646107
    0x60507031523060c03160c240e060a3e07180c030e16140d020a0501080907090f021819091814010204050109051801060c020f061c0c 58
    0x60882d0702c540b15820100c051041c40400e4022031440d5030b03035000c20f00100200d000d000c0c1740301c6901e500075100e105150340f83c40048012541c03290040025540b007582042e0186400c0303591105443e0741540e6903a607a041805d42114881c0780d036800c018801d0401c5070740d10340201c56120700f0018100810070001d42d803400101e00c65544c0030039229030580300e070700280b40d04a0b02901e0741c005607005a003400c0120700c1015940c4100e04203009800034010400e100502400381d20f01c5400410049001036170a02142c594a400043c4d0300b09080c03055504020a80000a080e8001030281c00000c0000b00b10070b00080b514081d0f0303a00a900310b03441c0041800582c20701445141f07003034072500e1580300c07030b0703070036070341c038450400d251200501f000c5402c54078070840c40054107000441f101c2001c0400070701c036000161540c1c10240010300c82c0707580e0361080e4031661500812210311020a0a1300d8110b4545040507031902d02180b002c12411848a41216031190700030494100d0580b108107000c1010018400800001c84214025a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 995648597 1250 995647347 995647379
    0x105090105041103211305131a03070806190e030a020708100501050105070b1012030e03061006120c09030609060b040c05180906120118030207050433030605070315 72
    0xc1c0317002881d0784000b581c540010b102844c0400600500301e030316035021800b4403015004072624660f031202c000f4181c9274410807207090907a0031000340c0750b920300e0301c2c6040341d40c1c2e81c01621074022503050b1200745c10740c00c1599000f8200907610000303603503c0b00a0346101039100d94540c800c14807a4096040004c8281e5402c1c850241a1a416144c5c0c034204403e039160b0305002c4100600d44400380300094404641741c40f42c5101a040300748682e0303800000c3b00f880e10038181013500143c40660240040c4130140207150300080d02020740a012980013881a03c240c100720f8a03c91a40e01c003401c0c59150400244c28845130380c0180400c8541903506000c2c1c0d5088520071140d42c803405401b103403440c0301c41a003a14685071404440b50414001080c07001d84810001c0070600311442c9101341404d841006004004064041c4032400090500f00e80400143c0304c85811000f4403007400602c0c00ca10301d003260006c0b28404c0100000c00103150085c80800061400000150003000c0224060801d00074103640010380c0b1144540042d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 995649847 1250 995648597 995648623
    0x6030c0816022d0f01230a140a0e0c03060103030f0e130501090212090604050a140a0b01030311010b0a18180f0303050618040b0411060403050105090105041103 70
    0xc030959a8541104881c00c600040180450007040510244641040d007001090302c1902400d002a1003461100b51401001400c2610a03906003007580c079400111a15030170048012400c942d05903601c40c0e0200300100507001c0d0307491944101500b8408488556031140940034060000c03901d80c82820380c10136a0705d81d02440010001205407511001c0300f840745001d1030741c502c000f8050f1425951564403c609850090304010080c80d03000c148031071510052400550010b5900f005400c850805440e8652594859900a0440548170031842c034100c10411882c0b5145411202c034a03000d58480c41d0042c407101c80706a03035540301c1d800c0003005803080c40c020810382c0c204d0300540003107555400d07a101103d001c0d14000240481d04098260901c0102c0d028008100905209960000e03887c900b03c0c1c20011781250355082220052501c0040200142c1ba00c407a554100d90000c0030b102080c1340540005031540b1640c0c000500d55428202400901c4070150070203170169100f0000410341d82c4a54062554411080c4901 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 995651097 1250 995649847 995649857
    0x9050601091d1b090d05010b0a0b040b03010e1b2107050405062a0f0c1009050906041a03010c1d0105070b1f090504080d0b040e0a030e0f090108030403030906030c 71
    0x3c1800c40d8884034140c0203c150788607902c2d00701000d100005194a24012003604c981c1d4456a40742c01903c3e064107000003511080c04902d050900340350342686a8001405181008556200071680d410040101103100000701d0324015070301d0020270a4000c00d43d20b4010308000440002001c1f411450196040d501654000780046003803881c7d02400403203008001c1e1a4a689049094959250000038000059180303100c1c4004c0007880c00034001d200c038036590203840c10100040b64005014035070303464002d03e4010204a03404501c41ca0740c0c660144940c80407040e082ea05628143c000381c21650410160703c1e00c544030490a140312820003005407010f114a00005017040d042d1030001d400b91140c00441000303046904214644035450b0388900084030001d44040c1c403580004a9a20700000d454064041c0001d01a40e090080824005225030342e6000c9010040c10700c0800b54140d9865240c00801d2016080018020101ca50703680600d903032250b10500091340041d151810101d450b5001c0d00400003104440e94030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 995652347 1250 995651097 995651101
    0x12070201030b0a0e0405151015030f0f150302090c0c031207050d090305190c05060a0b130f02070b0708040f030e12010c02061e27100609050601091d 65
    0x45009001c031800c050b0b40310703000d0000400d030041c01c1345000744150320035002400c8003d044001214030340d400620200046412502c00d0040d0003100f11041302c109594100880c0000411740d22402800641045407600c62030300364030749078200c241c01038101164002e8900c0d01840d16070150710f00e00c600c5060030f401c0d156401007007440420102c407810194000743c9458807505058100303d0b00c000f43e03040c69400b07900082003ca81c02640340324104161011103070a003031414051030030f59150740e03d4400c01404026465a03d40055985480f800480304811000c20000c0000141c5010404025001008260b64152051000400e01e0313000e42c0245010396000010280035401c80d6034100c030700392070b201d101c0b64005c10303211182144020240600e0007014550740180c0064a401411103480e0790542c151702500c0b202c000148032040c1d0703400a002d141ea9480c0d10500b9425504500306920344a40c3c0c6210701c0d1410f1400200040480c1241c4c040360290030243d07580c54105903204000304907410800106815a424000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 995653597 1250 995652347 995652349
    0xf140901030f0311030c0c01170708150103060302120f0c0904050703120e090403080414070b0409270609031b11090402210f161a0703050409090303021b120702 70
    0x1d00c90b8070091080c582850302c041c90710600c03800c43c1c010440c1c0350200e074080c50141001d585c0201a26055401703020100c1d0140c6440c0a00400e00e41024040d1f40c2d06450030b1072200c485901c281c0084019580151018600a0380107d50541c0c0d08000b00a40ca03150040c0200c0d4000b51900d130604c140140d4001005101e200c7c01d40c1c6822072114035181c81d0009004d040082044181c4403e40c0f003c1c415402919035840e1440c01b420402036065a10310b030b08d4819049120705208449140013500c0c01c0d1000d900000855003410113502c00350714481c0b092a91000d1f100c044010421072140c10040000d882a512043d0a5406101f80b502c45003404400404207000002c0d50031107414000c1c0040c0d030103400113001c0320019503440d00e03031400f04000b0308071548250000600d09075016410802c3d4040c000c014501038411034030702040c1c41c00c81e840301c00459400680004039601418454019640503186010081080136414a00a0000d42c4412280030180705080542403280350302052244500401c400690715110544d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 995654847 1250 995653597 995653613
    0x1608040c0b0c010f230106030209011b020a050411180d170a0e0402040b0403020117270709051501110c06090d06021c05040b01080a020303040302010809250f14090103 73
    0x81034100d02590b032014904040107450085c551600307480f48880c5900042d2141c9260340c614140c008405060040007403483c0d41e40c0c0310340240c61000c140300111b00f10104030b10010340012010307030046900c682824071400070b0000000003040212000d40030b910050214006203d0b43d51800d5001820200c01001c1d0604410388200060544414501e0500c14441400c1e00003422a0055004504c0e43d440129003413085580000d20000780283c40c0305e4000c42441c001e00f84040c150613900030700c00e490545206907c01000100300951c0603224585090102d8641075250080019042d00e449001903210340301d080d503125000c11032035440d034406070583d0300c0e040000f418064001e2100100301d820560800001083da03101025026002c9141c8501291909090500e410071904c1a08021001d80001c00d4000041c0c2d4004225030803660f080c20000450b650b6150400e00307042d000103003444900c50144040090b09000d810305d00554082c1c1034504105030711606100056034034510f80d5038114030408014404a20b0762 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 995656097 1250 995654847 995654857
    0x406080705130806190203011404020c030705012f03190e0703060609060603150605030a11040905270c0a14041b05190804030f0c02150a02061608040c0b 67
    0x181885490002c00079008258204158044480f54002c00c080c0154000c040342c211900e10302610b03096080d9410041c00e0000c1005204805200d40c4e8000b03020b03800c0b05001e00c140d6407501d805c41c00800c000c0040107103407092018401d061150141d41c11f08070300d40d440203c60680303016060707003045040c50b25411407d203801000101040d01291290000000014100d1f001d4040904156103000c5461840c00c50040c007900c1080140f114080c0c2c0d91001480903a0380b141c1502e61204500d40080384170804a24081d010344190780283c41c240d41018104180d80078000509010385695042c0743c0e0710b003002811030b80d4880204111040d886171080c503042000c020440d00b41c0195840041000490f8098101ca000b89190048500d00229802041c08030801000c001e00c80004106410b220f02d00e40742a0303800601d5803011244141c24882046601420b5480352021620b1401c11100343d155100d44100d00a942d40c00200d8611801244400d1504a094402e40c1020f00407503103c00d032501182e080002c0c8107520b800c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 995657347 1250 995656097 995656111
    0x50a060b01140d0605030613120c0c03140f0d0203040515030a2a020d14030403052b020d060f0609150e2e0e090105040b04230f100605040608 62
    0x10102c1d00149480c00107120050340304100155092a100c00d050900000a01c4403681449068401c0b01248a114499000c45901e250083c02890701d840c20f0644104141c101810403946c4003210010501b0010710740c034807003501108948095404500407643d03845a8007495170480c0c0300b000c1d1308c40120410805150404000ea1020131000300c2040c82400c0920303001a600a1450707070090701d0f00455014003290202601600c0d0501032a0044402c074001480085d10060800c00000340130311401083c00c0010940c40380b908500c40c04d00405002c0b481c0a034120500e00e005651034007400084000e0305005000482d00c1c80c0c0c40d00084a440d1103030038404800384050791380501490300e2071b22030781d50340b14017100c08282c0400100701c9100c84000c4001d4044c0c0843c811b854140483c0c40210801980c9200240341191001c0380c021600c603196402103005802c200c1c203442c0e902c500356000800162048180503104080c140d0ba02140d44e40d0301c401020708204e1910178100030410400052240c1c42c882c412096002003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 995658597 1250 995657347 995657357
    0xc0409110d02040f090506160f05030105010507030c1a07120209030c0409080714030715022a030706060f0e060109060c0204021b1005070917100902240304110d050a060b01 75
    0xd44c881e0311000e649007014201c0c0c064000b00104140008403280703c40034000540741c41e07030712100e85102c0a84540f2060240d203051040c08035503101014482c903110250709511000c0b4100820700f29840400d80c440650b10000401c03600c949500e10114039101365180c3c1c6e0b000400610000c02d0b0042400010a464507044e07980c000c04120600200310003000d601ca50714030000040d0750f030f000141030400c0c00d82c441d10182100d15004020b0202c0400352900c03035510b1840c00c0d0324214205110780381c01c0740c950303c640c00c001041141010030000b00c16182c02c0c0a2400c607410b039910000c4907900e90b40111000c1a0901584000c10060b017900c0d00541030941c040d0030303015100ba95008011240c010100d10700ba4403400070900d1305440c0c1d410400300640c8445004001d1220001240c802c95100d100c40d52903031002002109021341d01e0b01d0181c259542e490342018425401030781c02045540c003015122207684215402c0d110700c03144010080441c06c2460340110340f550020054030340140302d5900d1300d029001c2617040c241088 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 995659847 1250 995658597 995658611
    0xb0703021002090f031f05060603061f1214060a06030e0a030516020a0305030d0b04061a0c01060e070c0302280209131403251a0a06030c0905090c0409110d0204 70
    0x80c0302040143d00c800c1c043e02c0c86d41c1c080e441c60441e000646100408903401200c0500902c01680c45010346101031500030410080d603041c0d0a0001c403a0007070b0606001c01518107141d00200004500e070300450140d0404c1d5000d0078410b4654005800780c130048a00d0030a268462000030001c0b81c811800b410041044030500c01010282c2c2c0c0011728443c3c613941047c1c506800004400703040c00031074131a507100543d081e1010300a042c41c0c090b079080d03c0d1001440240c00447d00284020140d1405c1d4044000360011044410343e900b45098000d00018040c0310440c054031032031035040121220248502c4125442070403056100003140d00340024804050100c030691040b0700000c00c0010610030050450440c078000139a00c440c006012150040b800003403140c81039010b40744110115a00441c607034035080a4203076000c03d40d01d61481070002050b0075800030300365440c03200d070100f00c40c1d0864001d24080c4410404552901181d401080100e4401c3c000013056088029aa503040c0c1c180140c04003203260004200140c98 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 995661097 1250 995659847 995659849
    0xb0a091406040c0e1207271b020706110c040c0e0315090309010c020105091518091306020a090e0f0117010513021003090f0b06010221090934020105010b0703021002090f 74
    0xc8070101a41300d00d001c00800c0307d05419280748203503a400360700d0b101100081802401d019440783d081d80601e10812405440c8000200c0e4200010b59541d500900208801105020010b1070b80d000703000c03801c3c464000d61941d00f1094200703020031406081c2b40b501951400201000654442c00c40c070004034180201030000e452180d2f03a001d034585040c19880e00c101d55610954022082207078207006030502c40c14150003844103062404032081906544801e00581c0d41074450000c0d24464925440031049140c0141001a248082d01c0f24a04a40480c0c18621011818500c1d003070907500112644081b40800e00c4130500540752610100d80078650760705001408092540318501c0320500c600c002d42e0b0b41005d40c414071580b56410031180c50001d01540045d0410762041c02c1940c0700740f0900b101d45100c0d14402c008900d4228040c4061b0b660b100d84aa404c00d201c0c491035941d01a0300580e1000080076500c2c15000080142c175920444102030303030590207802c05004800043c802504203c0c0550b4020400342d011040c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 995662347 1250 995661097 995661119
    0x33a0306080d03050916081209220213060f0c030c031b062007080409050717131208010f0b1605070b0c01180f030807030b0a091406040c0e1207 63
    0x4a01d0b5507000315992610000740c0d45410704498030101000c45c0c00404009210000c034100805400c01e06000350b0ba45002800610301040060280340001074100c09014030004a41c0140190301d000303502c100009907112400e588035101c200000012418001c14880024422440c0c140554840d04040003502c8001c120030308107034000c0c5401c50b0305a64948042191040107411070310000f411086030751400c0c00c070ba03907a44c0d01c50181d445450350f01c40c0c5030404146414092180401d041014500000346460b11107007651908400d14011b0b034200c0220100540060320480311641a2108506021480c0e45060040d40320356020b140c414154840c840000c42c00030f4028404280244244a50b4648514041074141c0c2100d49500c5800300100200e40754000081101c05040c51994150404080559441100b0340141040c0040f669005005e10004034100c162a4883c004000c0107403442c100f0b5640e00000c1c00308a8410740c000c000400e124107040c400c5807610310340d0901d2240713103901503442c01c941d03401c079080c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 995663597 1250 995662347 995662363
    0x14010e011e050a021c02330f06091501050f0705010b0a0e0103050706020303040f080901200319020c1822050105071b030e0405061804060b033a030608 66
    0x3400000d80319041540c10013908009800404a05001210499000c0c2d503d080c0c00c41e400400310f480e6200a078000301d00e4501000021f1090064604500e0022a8050260004c45070a885084500d0210f00d05011400c80315000f182c041e1281441c01032414090040d0340c01000c0211155900d49420195586031315103014018040c598100395a9411840c10724108405a00804110b500a1042001048910380e6040325650480e10301c50340c4107030300c0d40103d0f0180c09207010f0314500c200e107594080b40040000f00500006000b200d010f005586581c00490300e07219280147c6500c074040042c006a03e0744107881c80d507000013411008000c01010500c1100d000594410159526550b40d130401c007690707801c80ea0103904140c5030448a0300504295902406450380d518a8602880e17071000041c0ea036880c1e01002c1c031000602151805d0035131609182001c00740a85011550090207001d00307241300311790f861140401d14021005080c441400320b280308060354005507810010543c0341c20000402d0724090042d20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 995664847 1250 995663597 995663657
    0x3140906070f0308310602121f120201050414040e06040302101d06070e15070503130b04050607060e03070c12031427060d02040e100504050114010e01 66
    0x401075500300c0c2006400d03d10000d009085001e061803c501c5c18200c045010701081e2141c114010000c070440c00d115009020f43d541c150314092421043c40b2400c4c0c4480000035403111012007a0503140d0303d0b2070841003000c03402c14000340420070500050110b01a681060500d01c50003800005001c000c440c440c07854000c1c10348099025822a07000701c560f070040c6001d2401c5c2c04560800b81c55003580d81850741540d60f44000c19a408205040903101d4241d43d95004005299200f4a485603c40f5041d00340706071244e1200c180d000c00004a010001001c0305840151011100018a041c0c1071130200d88511000e41b252400d04c1190f80020003c1034000b8806281003006090449000d0600000a140150402e00c0c4100700b20305a02041c0010030310303d42034491801210b00990300c0c0c105150510030116620b40100c2900d81744032400810003280550160403164030a20148580c80903460f0303214107000031a0400c0c02860034840400d40d540030194001c00a0140d03421043c03400c105080c5044509404000c07101241d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 995666097 1250 995664847 995664863
    0x30b060405040e211315080f2e0920220308030a0501150206220215030a020c1c1e0c02130222081c0215090c0a080c01020a0314090607 59
    0x30117010034000d0180d02800c000ca2602c4000b030680c40d009007030a1401824404a680100c0c0014500c00c0c4900340d12103000041c100412100c9818440b100480c05076001c0c40400d540307444404100001038400007010300b0030190580e8904000c00341101185135a4110700c01c481d010b1400d0000c00039003c05c006508c101d94004000800754140044040c5410060000404560044050051451030003000d02407245010190f04640e2507103101042d190050501d40c1116000041308000400e400e94004041268943c02a20300150b10200a6242040c6510b61a000120414a07404018140080d80c0240300551700303200310120001e6001580d2030107400050311807a0b802054901d1010002403032003070030854001030005182d060518007580d40c512020701c1c040e03010b01040701e1400a8020300044c0d00300544060207400368a042c075001a943d00103041e1050091441d490700040e4201c001c0707140d07402400e050b40600904501910211001c091107500d40d5100c01c801c0141c1c2026075601e80042038020710802031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 995667347 1250 995666097 995666107
    0x1060e011202090f040c09050909030a030b031c081801020d0e0709020f120703150906060e010c12080403021c080414280c0312020a0b0106030b060405040e21 69
    0x501407030910012140607070050003841500ea83c1c0c42c1640607010300c141c40020721864041d1007101e42d00300b6503100c2070b08105020300380b00b04000088014020003400c0d890901042d4108000c0c1999480c407601003a80a0a0f1a001440b041c2e10600701c858010070310415084c4000101d1000c5802c907030010603c1100141d842040c1c0074141c0c0c044c441c0400400c2480b100314241103140155025602c6040700030300041260300001110765000e944030080121001c1e802d2000303a6210104107008203082d014080115041480d0100c0940c8610188407401d540700c401c82d00b0858488005490035440a08120298040c40e5000c200500203a21600d00d42c410300d41d01e85a65080c20705210004a810001c0d01c000ea400c148603600802503440c1c07000350b03603100d2070313190360f0700240c0c2402c202c4c80026258000504d4841054070354021240d0020303a141403903009032444032284e40d031000c0540c21207040c002c0194010006100802603031a246c0e0140f11680510300980ba4400058508402c0b49441494800c15107071001c14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 995668597 1250 995667347 995667349
    0x2103040c050108060d020607020a0f08060a0605191221050d0506062d190509040f050f011502070305070816060f08010939030e0c152101060e 62
    0x180803401040c080c2001003181c1004004030302e00340000345010f40203d10000d081000c540701c04503503100512541100990300b5499014203504c689090b110300601ca4186480480e81e440d200c918410503401200d0042070107071920b481074a0b4410000c0d0159400301c4080c030b100080703807021220607010100c1d6903540c954034410034025100310b400181019006610030f00a440c00c80c004c1e907901c0d812055000e000c10303c1102c0100c3c150000c510401c01501c260b40d02040c0070b080034030340044c06044c0f0240200c030302f80108650101d04078100d400c21116902031000d4200100000c01803a10140100c190a2041c0c0300250703100e459441c0b812203181e004034510b910003051140d59940441e4928064107051a20714050203031400c0c0206440810301810801d41c1c1e0355843c400c4110720031910448002c0180a042808858203054900726004011200000c40d0601c190264030310004503261101d04002060002d92142440b2804160f402c0454401c040d140005144025400c404450600801556452034154410741c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 995669847 1250 995668597 995668613
    0x405010605040c05090607031404030f0614060d020901060806010e060c1506011d0108070c0f050c090a060b03010b07110a080c2d15041806031a04170705210304 70
    0x1600c82c402c006080c403d00e861a80c8941c11140c0c0072390940340041440b40650181400391259900c000c02c01e0b00341c01110020051650003000562081840c40c40d520b0f600c00c000e110402048520083d48110326100501c03d081c0100d50310b0381c1100040c5072410700100042c2c042000d6a0002d801c4d40395607032109144501e80007140d40c81c1c03544a0800c1ca0400134021803c00d0003003064000240e0507040c07050080001c2c408074810603500d8161504404281085400381c20705c16218400b1100f09402070740c25100007032400c11540107500c1100e80c0c00c216035280d40c0c82c0000509007900709a20898031080c0d842c91045041d602e1803c40030203401e82c0005080c50809031001c00039181c0c028001c81d190303503803150070920030032805c082d00b00b40c1414165090311444a508500000034401c503041544042ea0220000c550940c0a901c940c2c107480c071405142212a022601a5000202c1114010015000782d81084500c0005401030300e4035621441c11952001c0034071000d64070a02c03c840904a006202004000c1405860 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 995671097 1250 995669847 995669861
    0x314040e06090615120c09040606030b01080709051806040b03030301030b16020d1b02010c0506010b07030e0d0b130503071a0f1602190c09090302030c0d03061d0c070209040501060504 80
    0x844000d0301d6081c80e0804401c0354010004c2d07807005a404c040001e113480f01b1490482e040960002c00c01c00942d40c5a8001400403e008c640c440d0014142d4000030b46800d01030710040301511801001000403208a52101074208001451150415120040111a5203007000594042c510900041805d03103403041a0041d020a40301d141011540540d90601c4155003001c2c0700050031440c440500141012400181c642a1000780300428901c1038000006500c2085009015014402d94440c0222005c21080020500310b6180103480c24a9080100740d03e0509018054466481601964145503031500d4050415440c4001903641903486820044c004540340300495101d103000380b2001ca0103440d018000e555000343d01c003440c4100da20fa1303400c40c01d020211030000000c0881000070b12600f81d4510b0001d403203030880d508009051068400042c184c5009020300d00c1602c42c440386104c041c0c0c918505000801e04050581000c50100f04220005a141c610000b48140d00440000c030740c0c00d1801c4180b004480135 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 995672347 1250 995671097 995671099
    0x12102060a08061005041a0711180105100c0816150515130c020618100608150c03160c0201030207050312180f100c14040314010f0c0f0c0314040e060906 67
    0x2040140184040f50888030000807040c045561184d905142046031403149c00d00c00f9070b0007009101c5015400221800b2203043e1384060b20f15a1200804150070f03260550b2011008211f903100f40000a0414070041490200a01036040e00c2d45100315400100c3c1210340c241e5100c40700c0d240c2c016040e141d03401d14114003800d0707801d00d2104001604808400035104c1b500940300501c902c3e6940c4000c40c85240c02c2200b259900c0b81042d08111580d65462216694140c010101c682100080005488800e9101c16281719a800e450a410705886100f42108c01600c5500b080f0b043c15820700c607a00104000b08090610b621701100c0e11102821325815034950203030b00403807050701644607607550945a0408074200401c0f011114000c1340800c1d60040030354040240c0c2002d0004143d002c5030000c00d00c222a9050200c4000800081141251015015047e1203c042000c004611580300280310b03103206100742c00e035140c003e1038220700f200860781d44c18080758002d03400104103034200801d010541c50700025950300124 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 995673597 1250 995672347 995672357
    0x5370201140c04082119030218030a03020d1214181510050d0204090210022401030f02130609020a020c03010e030421030908010513030f020601030803012102060a080610 74
    0x4074000580f56645d11741c4540104001d07861380c015111844440a0b02c00f0111125044000c100404800400a40008044214070720243d80c10b03086038140400c03114191a05a8050064804907400546000704402d400f0480180d44510400c090105050520b00030760400d0400104110030411080c688031a030b601c070300c06a1440078144070b80051083d82d410111203050300d50006028050000500404052030041d40050002034500c0403030781d0114140001203220011034401d503039444211903060b542404000e100703648140113800546014102103060006001001c00e0886e21071001c1f5007070748c2184007101f0160313010101034160707490280600182100703079000441c202450619152404184561816003202441403602d041c540720300180710140c000720000f400716051203818061642d01011054000842107d0001041440800c0c0340e8100e039080503190741140d00304284040c00e041030b8019050b0410b14920003200688801010f000310441a0300c40c410945481c8040c000c500f0b40310f4041c0c0003084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 995674847 1250 995673597 995673599
    0x5150108060106111906090c120b0604050a02070203121e0310060e03031e04050a0605070f02011b0b04060c020c0a0f0608131506090609020a05370201140c04 69
    0x440055020304407540703031a11070300c0c90103609034041c10080101c0c654526215440e05c030710240300a42e0001038159101d03c002024156030780303100812006546100502a68410700030644520f055080f041c1c006200c401c0041c940a01a03001038601207026400240c16000814906030300b4042a0a160f44584588016491450084074500e00003d40d40139103c107001c140340b26603203581c50800a03111000480c250000da00042c20507000500c0c0c101c0d2050f103209945040b07010402c9031083c0280d52076558800514481d15140c0c0d801941e09400050240c1c5600100710404e00c00f1800b130b01355090040d40904000203d00c20042c40c024101504014444d0244801420400001d8254011300044610074134003074010b901d035180707035064240c0c001c0d00c0584141d40c055080c0d6036011381c607408481151841a010481d417540c40f1104410303800303100e1204011943c103010203070186110400c09450044001001072480c10000030b01e000c8421003001040050307640c3e0f03012080850100344016001103500391043d0610b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 995676097 1250 995674847 995674859
    0xa031d2b080c0f0f130311010309031b05010f02071103060924190504060b090a0507050d09052d0f2d070b0f0a0201050c0c062707060c051501 62
    0x101d40e0140181c988441e00051410a07000c41c04180c0d00402c0f10603603c1583c51590384400152403a880c081510300c14008000c0550f40c0d80a407003070040e007940c0358503120034508510440414130401c01800340c500b5500c41442190a1503540700421406105640c0c480c1340c0c3c4046001d0614141e802090407282d0780c820801c8184145a6810301c9544080d050f00e0000d6640c2c4a44003122082030101d03091840f02d0a06e003c1c00f007005030980212810340e4003510400c0103980d030301c1e0581040c0c1720180c405c6800714004200000e01c291564210320007590049044813400004620742c1c200400b506018400300c0b1001c3c20104101004c24002c004210341d81c0c1c0001c01a10b1a01203400070823166211a240044400c2048161002c1003030084000410350388006540703540f601a1071b010700d40d208a40510042d480d00000411a2585409603415402d00e0380007410700d9510a02045564041d80d0828688a80c0d420001d401c0443d003040800040c0132155500a20180301d031800a15114016285108040280005000c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 995677347 1250 995676097 995676107
    0x50411030c0a0215010605090111063d031b1712091906032c03180604170a170304030804020f0f0d110123030c0a031d2b 53
    0x803200c04020642c1c0d508402500340d290006a50804008090f54400066202c0e08180070344060202a264580c5070080d0076021034440c4030460305165100b000030414528070094a80e000704070702c01da4500356561880740026180717050050340100e0307004c0c0384295450301d100c1c900320901006041c81c500c180e48040d0099609512040180c00e0f200e013030388000c01d0301951903407a2171240c044010203080000106032a8035000700a0704540700205c007c02848107401803010209000841d4840890002e14109400301d41d44410b40c0310302c1002070342d101c14203110100c2c800c2080202c44030070300552002803a9044451030040652400e40d80703148101d04080c010000800c0d00f003101294440e40c100d030021555414200042c0002044090150b000850001d0075410002d03800c0554801103800d0700c950412000b403811f0391800c41c00e12010101100401d2000c1240c0561000107440d9440035810081072407141e240315150b91501708044035140d80d00c07568800d00700c00c4a8403020854a81d44080f0307044201400440600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 995678597 1250 995677347 995677351
    0x5010b0109081207150515040515060304080d0608070f03020a09140411060c012c03030105060d11160b04121d01080a0b0a030c06110703171806210105041103 69
    0x3203070f07280024180100008110240000c0d05180d0f4108440d041920103002c900d0814125603000e14a04130204600d50202c24144171048401003070f191455441d0358542c03080f504080030700282a42c60700404145100107110510140041c0d1141d480c18600e903004001d60038200b688855900d62801c00654000740941c8030a95010360132420b030802c610308640200701d40d0300c41e845114160b035291210101c0c512121128200a00441c15548802c1400d0442100d4803880f00f8031849511410400500c4401d204581002e1214060220003e040c81c40040c0031941c41c6d12240c42c01c842c80c46c001e8040004018600004038004100c91a000d40c61120102001c4e0095291820143c1841030007400604554600c2d04103807680d50307001d0440031400341d81b460450300d407005501810700420440808000e51110000d411002c87c1c1e0466080c2d10b008013800c40010240d4050780710060750b80c9a40c5134441480e00c400c00201340034181803420030b072007095404866040d1041a00724610480c00d000081d113581c0d803240152a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 995679847 1250 995678597 995678623
    0x20d02012316090504020d1401051206040f0f021009091407140c071d010303020f01020f0306010f0e0315010f06030e030304031b1202060403120b0307060f21060305010b010908 77
    0x102c02c15119800940f503e0390964030541c0d20500018860b000e4001d207400c2407603085d6580642c5c144503600c403400c00c0001c20840c110001141d00c00400180881c40e00101c0c2c01880e8059454450f00c0160351f00403071980819484e14a01040504108100c10105071107511207221204410a096042c2010020441b10458203045d1070303050007054401e43d140c0f080c4105802481400e011459982c415101c1c904003940034401030b03000d4050302c000170002d08418002c4030340a41515105038610798580700103549460201c2006802c1014400321505a5141040003a0503040c40041540003980341201566030f40015030022000c240c2021001070701440008250b9401c81e81c0b40c20290882d0980741c0d40012034038203410026180c240041705100805401081d4140118000d5072141d0b00c1c00c52100801003510500c55a076a0594000d0500300b1030940300303000d076065024180ca07000d02a21800c5d24903401c42d40c0441604200207949000030010860240304069001c1d400b8240b40984030302e010f10558840e12808001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 995681097 1250 995679847 995679871
    0x504050109030801122f03010f0e12070c0b181002010b150a05030f06060f1201030507051e010324080f0f0706140d09060c030906050105240c1507020d020123 69
    0x1081143c560343c0701b01c00c000001030001c00035010f215403104080c05666604400d540034444100609640d20b008035032900b9000010443c45a140100000c201c0e404a09a5030856086001405882d660016024481c0180340c0c0003254140d560010490b01400100a540303412208100701300d02c1a400c9819a684140444038842140d610a0b000c500a44070f920754070181c409001500c0041112501c0c542410f81c1e0151084864a540701d60034482c2c2e40d100401400e0740041c0c101e040401640c4241c1140c2c00440c1850707507880c55031a4442c440416007a240e041071100780c004070801c1c0b5240c2c0041042d00442001c120007031541c0c524140c00500705005042d001c0302040c000046010410030279400c20340507294045030410240410b210000c004180e00101119102d0070180001440d1400200c4020019041a180c00d05410550001c507107031341c418000400ca034003900302c1401d544101a40920310504064001d08040c40c02c2040090850b42007a0100039000b0b0200c00c0ac030040d0f0340c4003803201c0d407110125440c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 995682347 1250 995681097 995681153
    0x5040513020f031504030203031005012f071a040504140f07270312030b010c080a0c030c02091303080c1305060904021e0d0c11060606030402060d050405010903080112 73
    0x1190130865002d00e035a020000c0c8009010415900100952203620f00e812400f80e50717a107030401150308040d40c0c0c0c4052840c680d10f29040d500c945c6900440c0b05e0560900c003c480583e582d800b18080d00903000c005440300090041010082400c1c180901d00700c0c4010418070400d0b038a402c802c0520130203400786c0802e0070400f040c0e2020b4031003080c00c1041d19030b6072882d01d01c03401096603d00d40184080045181440040d0811007900380f954090881d25480c41e80c4a400242440a0107204130359800459405070b04000c2070303110400158444500c19801850320b03400e04840032841d0304026240760700240c4401d42d03050081084465401000c0c2c008000d580080b00c1c031a40e40e44e14000060064040d96100d48e4a10324080401d0304440d041f00024002212450030600658091440a1750b03484074002d420a903a401650000d1034a1904d080150b03030140c8014181e0f07050107a0081000211402181c086030169550009002410340150f1070071f0050400c51444007410711140e90300c031201c0c001030603030740c200000c4100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 995683453 1106 995682347 995682349
    0x1170c0409180309151b0f03080f04050606060f0903010c032c0c130608030406050d0609020c03090103110d1e06090b150c0c0a0e0a0605040513020f 65
    0x5690409601d00000311170405030210702c0008103c2034103145071450000c00301846150b0700910014441ca00b0500e005050b42001410b030b41d40d1007441004000c0025400100103030b20007001d031030b2551180c203c211151541c1c021005420340c10f5082480010003198107600004900d8070035103481014440440d49591000c0c6130881d0040b0769041001d1016040c140442a41d2907004d601c2c00003d03038295900a500e003103401c0b03900300710300203600050b00d0705403d902805031201809171940704518040d0040c4046640b48103401090341030540701c00410114140407820364400e016220014007200e041400c002c403c042c0c004060b0030b111490600040f4860071580304400b5172000c041c25460340840b0700b500c4032100e9000000b17070031003d100c0e42d0780440320743e02c89c1c0c0300c42d030020440750f00e041c002418850040c01c1a10115040f8900440c5480100000c0c071001d5040c401c0c0c0c0719015921003000c200444 = true := by decide +kernel

theorem cover : BRFrame.Cov 995503597 995683453 := by
  have h0 := BRFrame.cov_init 995503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 995503597 ≤ n) (h2 : n < 995683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
