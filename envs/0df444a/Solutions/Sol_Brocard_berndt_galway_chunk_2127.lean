-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2127
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:52.33147+00:00
-- url     : https://prove2.me/submissions/f22186b7-60fe-463d-bcc5-8ffd84384731

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 382374100 ≤ n < 382553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 382375350 1250 382374100 382374133
    0x903020c1e03070806090d0e0a030c090209040501050a0b040e060f191e030308010501120b09100303200604080d0209092d01061e180603050117060106020a020f0d14 72
    0xf02600901c0040c11903070514a11036035845801500840610100d05c800c2440b940314060404006d40d00a41100140c0d56286442c10003135008a0410340101e04110000c03555080c11900b0004603044e0181d00c030314103858038404a40e0440060b00c0603502040c805400f6445a81d104c1d0401d4914034001200c041d041e140c0109450364088002240152008104040020070780280f140ea044503070a00744104100080724503040181001354046501c000ca80c402d114003074a50030a0f000c1501c0c0300340c941c1d0107a076038401da005440c042141d240e0609503220b040010005403d400c0549000b0088d07590141c10440d078200041c5080204848a040340f0200314164103a500001c1c280c001700e03c404180c44003ca5050100081203103c02d40a018041c1040b800503210755881005081c204003482c9420021981e2203c80c003c0c040c0c4000c0c491010701c0028000d41c0503110314041215070485e0800e8005100c035503032a600740440006001010342d40446078614480200c0d10518000c000020410b0141103407c5c000d02d04c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 382376600 1250 382375350 382375363
    0x50d140106110d0903060c110106060f1b0b0403050a051b0d030f0b01230d0e0102030403022103010e100e0a0b0102100605150705031303050a0c0e04150903020c1e03 72
    0x380d243e0f1004030729141c160f800c441e1150035a5048040801e41000380c030f9081e5011802c41003000180d618249000600b40e600c440d1001c0e60040d1a0340e03d51120040c1070000d0a40003400401400e00d039440c6002c500041e0080000700407211890620600340300300e000b021030100d00a1280603034260080c60418503002c2d81407041100080c0c1440b0708110b502c01c1040001d111724454008501c079500c10420f0003040c01e030f006d0701340c0340c40d4401706c00140703d010020071043d07010303403c240e400710054400e062480c404184141e0758101361500400308181168a40341d801c4125a1003c1c240c03801207000c00c000402e040000000c03541c89222220740104101d181e0100081c904034079041c5071510146840000d010710755500c09401c1c0d6400b14003c055854900ca41803450070b500c18204c0b6036804e1281c80000000704030001c909020401d005250144400d0307540c82c2900413129084a00414013121350407000b101c0c00301070b8400e0702068000d1048904110030840403034142800f2120790035002d03c01245900440c40e04105a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 382377850 1250 382376600 382376627
    0x703050c0114030604110f0d150b1c0f02040308030403030b0a0803040b0a0c021f08070909050f070f0201060e0114091501021e010e120406200c01030b01050d140106 72
    0x210407a4002c402a2909400090b00c2544030320703190f010b0025020700c0b5009a078101d10441da080c1d42d517003460304141c00c02007082620000c15030058400000329040458183d98405c071107088101c0b80c0d40220300812008004183c40311100c90750030710010001c01c02201c05140f143d4881e4a001494040b040100043c82d062a40141d0340c40d44200001d000c0032900d8070a80d188402c56060000d0102c6040c80010905504202044107080e08080c8900901d988002c0c5140504440d8a0300089151900d81b50320070344408603100d4000804203004646c180b403107000492018000f5100006040e80c4403000c00d0f030048130070f910903441e0301e40202c558030941c60200006501b0a008407400318003040c1c2c100020351607041600e00050303003030f80026106c0c141031029080f0b050302d001c03c0d009030380340f065018070b6210f15500180140f500145e04201c60079031070b03403d40c2e448485140710341000308160710032500114007401591500504028090200c5c8600540034024241e034004070541010042d81090001044c0d41d011a0f0b5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 382379100 1250 382377850 382377857
    0x1704030b18100b01050a0c02040b1005120703060302030706050a111f0c02010603050a2301020f13060804030e22060335120a0b0d060603020f060408100f06030210020703050c01 77
    0x9112496a0405e00b00d40c40c0c4000780c00d10070300065182c00010001e16550030b8441d00f14001000304440c0650010017095040303081e81c040c545071784480000f1000c9038220b001c004d401d940501c3c000d00040340210007800d10004140783c1080d01d005420300c014240b10b0f105034014600810429190103410340c50040b4640b060031032000f0001c892039501c40c240d642c2c0d0391000c0a420301031100f004644c09981c0b400d0791038403841b0b43c5000790754400b18804105e845a00001c00403036580d00c00900459a0f40c400d020300c50050740c0540d200e0182d501c3d01d804000150501020308404503090100c0c08641518a010303d80007540034210821b0351120500228000264402c401e051110142c14002410300c3d555080d0741d444c07210381880c04580c1c0d4601b442030f0b005142d10100350f07034080103000384502040742c01c0c0c11100c103907442540d414000f0700030482840950300480c0180d055603040142c01c1c1045480d00e5200486000d0211000b251023582ca8020420281403c8819401600050401e10602104002c5409200c0080ca13 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 382380350 1250 382379100 382379111
    0x809030d02161d132906090109050606070b070e10020f0708070612022508070611040803161109040f0302060903090d020f03010f0e010b03071e031704030b1810 70
    0x1800c1d1445542d0051820240420b0011104c092000000c1c000c08000b2518000e041482d035000c8480c02080300440d100b610034280400007145100b1075000303460245002815150421059640d0990a604c0c000c2ca506e08010320181d210065a540c44140015004690042d294030000d103000306042100340d80116045600c400e01c200640ca50028422041c02484200140c5800c030206103010076803409020496958810900001400f07100b100804006101d180f00f0068400346205a4805000d20320404496420501070b52000040148150b40524441c1b0024501c40e01041d0006003840c400f42c0341500c00c001c260340c0c98020150100031203a00592090001c50800c281840065074010310910003d004030100c4500800c645c50940005840c8450000180008564400c440b80200f8000080d2842803003620700009506905400301d8126207885005000c0003800d5440d4061025208030500359070079030401001020a807040c0c0e10700e02883e04020342c107080d00456aa003528050308040200081440c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 382381600 1250 382380350 382380389
    0x703030b0f0a05010f020109060f1a0f01050d0b030a02100f02150610030f0f09031806080112060e0a1209090606050c100b010201152c011505070809030d0216 69
    0xb0445181215030034a00041007061051040380900641000100198140100c40000400642200802410135072008246101d5802000701603040c2e11301c04c43c0440c2042058402c4040039030401074070114080e08440852141e03a01040140e840c80f0842d000040040c1c0c80400200c2c2d0500c4891800d0240640c1c06c1054240000055040102c1c0b42c03091040c15940c2d0041204000b00703420401081d205007000700070104550401806110b840240740380c20300d050796004540c0a002c0d01c200b80c10394000c0b00030f811244006035100c2d4020841c84038807603603900c60014210001020941440f04e120019614101500c0c64454280b080e41c5883c0c110800340081403006d6001c0381380010b2041d41d00c003240b00000c40d00404000050740100090b184246403201c404101141c90700c00d090003204040b0010501c444400d0321001002c030700c0142801981c10b40d6003100c80541103c5d00c19005081c1481c01280310314a000342c194000303460041d82003400300c01f40e000a014034225145094000000308039440d0110f1180520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 382382850 1250 382381600 382381609
    0x803011d010f05092d0f100f05120705060f0903060f07050304030c1b0602010203100e0403020a0f08040f0909021f050930070e071b030e040e01050c0703030b0f 70
    0x11401042d0046540000240222408180d00341d41a469210a000911a21025117060100850b0300c400d118807080c0114801d1445101080b040701e240c60070b610282c504080811035120022010b010252007250760201c1c65030b0715080200620380f00318103a0ba5842d0f100d841032604120000b408825008112000c009100380c001d012070780e0140c0e01d85003e41d40c00c001458800b9070208039800d00c240c040c5406901241036601517009502031000c1100820f140782d0f44851a4602d55070841d80100140c00500803075002901503a9110180e80c40b454503141019180d0801c20054100e0b0340c44241c0040d10f43c0d0b005010750a1801000100070071501e1a401d40d40b84110028010b0300c00c4000442c0141c2c1101c80f046021070b42900f0500e00048482e0010f81030343d80401ca05580d601060103410384020104001c980d106000d8450314502d02d140002d161114031460318103a07034000302140c07582d07040754460351121400082841264450810108400d480f0046802c000b0b044440c0300d1509401040c000001142c282d84 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 382384100 1250 382382850 382382879
    0xc0d0f1d1005130b03070c2d02060318060c0a030f0911220f050702060705070312050702160f060f0c020d06021606020c010617011401090b010c0f0803011d01 69
    0x1d6400c01c15078500c014001c5240702d107001d42c0140150038001c000d0100c10b55000a002c0e04040c094030300180c0100b1080001c0490881c60302601204450094a0200508190020750b51100103c598002128480c62100382071440440e2065610f0000294440540d07805100d8240f2020038408100840d281c00c0c5c0d100484000c014501e02d1280500f0f01202d00300100b00c0c8501c2c1d00460205009200f0409086940405014240d40f0704016000c0d000000714418440d00036900c1d51509942c0d05848145645506001414094450021406041c244000000380901404010503081d031724000541d1801200500781c6c3d0f0348a01190402c41c0c00302c0082d001d0b80e00c940315a42d079030b030300110300690711094855103130404000c4034030080c042800483c05041031203042d40006c0403100a00c0035601131010008041c3d08840007000d001c440440d9810061041d60001d40c440100c1480605104107103802a464041421200c0141115201000001400142c00c0d03000601e040751300c85c4529092a50510418032450b06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 382385350 1250 382384100 382384129
    0x6140d06020c10020d0203010f1502030315120607080411060a02071a0717030703060902090d0b090708030711040614010203183f030313170c0d0f1d 65
    0x58001c03810300000c1ca8240541d803d014400c1e1011581c0d0401130b40500c000c0c3d0024410905082c42d072410000b505031065100d07404400855014620713554071070b07071f418811000600c00c203608001c0c80102c45844800811001c1e00032002030701c03111068034140c548403030350703440c94000d5a01450083c00180522900050078800f40c0d0401055203500b1a907581101e0428010288041c0800500c0358034008a008030100642c002c0c8101d683c10301c00c1c15143c20003a81a40b00d0914102d40103400300c01c0ca040400c3c084544550040c540d6020b884069079a44241c5203540c01845003581c12107030540036001c45241c24410703803006280c104043c4165140c40780020351680500ea14038010700703010807145101541c034045070280c05c1200200480040101e0350141010b26041c2410310560500d070221019480000401d4900c90f116000400c2d05500c1c05a40302c100780d803092403a1010403041030003181410a010b21400140d031000d42e07281001c00ba40700701d000b00380d29610700b102d054030035180b500d0440d41e84482151002b40d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 382386600 1250 382385350 382385363
    0x10b09190c02012c030c070f030c050a0303141804050a0e15011a030702120406080115091a160203030c010b01180f0b03130204151d010803030609100f0303020d0306140d 74
    0x1d010b141600342103102d0494600040c1c011410b008c104a018400013009aa0207109040c1c211503c0d00305002c81642c1a00019001c035601a5503d0800b2080b03000414545c4a91291912002a2000400c0c152001610b0200c40ea81d04c41c2d1100c2e0340c00008001c202c3c1e400c003809006804a51526041c9940340c40090302c1c042490800000284085000700104840100580b040c0350f030320f550762540200610828011026441c2d650000035026610ad42d441030f09580529200340d40ca0034002108a9155202c80344c0b907200028204250005640c0900241824480c90700000c111040030000040803c00504010080b000d100304041c0201f003200b046070819180d10040150740ca40306c2d000e8207003070341e055030400a42c0a4107140d1408840305075a05940c003144e45c402c1c115a1900780c0502c00040070082400307034a503280d100b400022030500e8010f200540000c2c02d8004815001d84030001015440e070581c009501690100689048a6505101d501c00500111440070040310110002940846070002c016006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 382387850 1250 382386600 382386671
    0x605060310092a08030d0606030c03090c0501030b2d03060702030a0e040c0c02031b09091b04050a020408070b090f040218010c0311100506040c0305060306040b09010b09190c0201 78
    0xba43d446800b42c0028082c60300840352204114030004020b1b040c58045e00c2c0c0020b003088000d501c154000d0040025041d80000902d100310b080c1030044009050b050703003181d403001004c00d60925050f0b00000040b031815007841c4140642d180c15050524008000d0a00411503004001a10b00035504c150f1109080c81c045501040307a103002002100e03403011202020390305004100030320401c1c0070b48141c0307142d26440c01d99030a00c1595411504580b00c442c1d0030001d2030201141010750007149010b40c0282d501c95411a0014101515024803910300300d8203030081c54000d600026100f12500c1e10355429074582108860070340c50141c01d200380c1080307103040303400302c5040c0007040d40c4050404d40504658911040031000b2215004100c81c00d22025060542e14a40680e14241c0440d032014400d020b110b200b9603018004001c80d48503a5513003044494003e0041401d55a01d01d1001c20603690059618042c1c070105030041480c115902490007200c01004110003503a04d00850320340480b040080084000c4400c0d41e13103541 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 382389100 1250 382387850 382387913
    0x402072001051e0f3601050901140f0708040315050609040210050d0b091003030912050624060f0301030209090a021309080d0615021002090123070b04060506031009 72
    0xb607500854081c0300b9030f09010031a00102080b00a00769a03c540b040017144410341000006442900c16181c58600040903400400401003020009010310340400100d289406402d40318640650001d410485028030304205100102c1c089000c2c3c0c0340c019030104d542c3c004500700ba50001d100380700380b00104003c1c4800887c0101d600b440c42c0d4170040d500c800181011085140441d80710042480500049011900609010924007101c1076084801a400402803280740c0303c1d07980111420101440e941464510720803030180907240c3c1400340c000c4104010b045501c3c1d50462040142c03a040041441b5010352044500402580e00c0c2100d1211004e4050400140580d0324240301e040c6120b0720002040d02401c1c4180041d041021041c10500788030300b41d0965840240c4403c114041c2e201b02013940e030026001454142c2d880010b800103082d89540c1d002490329010150f6a40814840700301c9051b204030340d88900b08103650500384121009103010704e0b41001144a1640e840340c17a9400404203034110641da500c00351 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 382390350 1250 382389100 382389127
    0x27170708102408060106140f090f1504060815010e010906050a05122406070c180f05070207080708030703080c07060b12010b010e090601020a0609060b0402072001051e 73
    0x3108156254a00354196856000f8550b44410a204444c0092000061001c1040c0309100396170755000485070280c50100e1540c00c200381c10f28940c030500c2d03008502168055012017810f00074002800d5503200c008242c5080124000340c19100c0300c010341030101841604a140e13920509035003d030391040c00d2441e21100e40c008102c031f43c1e0240700c0b0f15545500108040c0078203500e582c0c600c03034403959101c01003ca804064009100440c000c4c00c0008101c08103d0000744102104080d0943d40e50b11b0f0b03480001079100011041078150307002504d651002d600302c0602030083d40307401d0042c0405040500c00031498141e0b2540d0003414503000070400c3d0340240d0046000020000e06412045500710001d0482e030540c0c00a02104e80280500110f10340400d01020044c082420500082442510143c000c0c01d005c1e43c0701d480d803a01401c0305d20b908407030b15943e0300d040902940c5d4502c00b811090340500d03240d50824014900b00d511025806800c0d0b03040c4481481803141d000703541240311910065400d0681e031686c22103012030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 382391600 1250 382390350 382390391
    0x503030a1103090d05100609020f070b0c13120302070b03270c0a06050a08150a0302090601020a0b090d030f110703110f0a060b0f0103060b03060d032717070810 70
    0x45130310041020000042c40b00004803410107910f01e15040100b103a0f903102c0a8100d00c500400b50703c0d609000d104020105a0403824143d10090358111645442c1080440c99603902058100c1d8806106a542076018964104070f80c00140c0318041c4010b00c1c0d41000029a1640d440f4020f1000b00c0369019100b04901c1c40042c1700c440d840702d0000d82946921a140d12001d01250003c01d001000500c00f080003903102c0c80e045100e07140c00700024204841c00c07030441d001d1041d4884020034803030543c0300d91174940002602060f20140b00340400c101400c02240201e60040c20f03034049082d10702055051000f8055150505130403a143d00768581000c1c1c0d442541e242503541001e0714080040707618080c660406052002e84d41000000d00d00c2255090050701050300194103e034400e0241c101c82440a00c0010454141560545481070103424400707071203070310300681d44018000020f64000204203940200041c070041105440361a180c1d2019003011814500215581c6044010161905490b0648407070000e20325004c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 382392850 1250 382391600 382391617
    0x8120901050906040c290403050d110304050f01030f02090915030c0307081203040c030515060a08030307020d14040902190f021207022202070f03090b071707060b0d0507030201180503030a1103 84
    0xd91f445981d0782c1000341c1c80300d070303c040f11034046569989a100501c4003c4110b5007502d1004200c04030101c0300d5401100108006415503c00c90381c01c0090340110303511501c42510039405018014900201c00051600708403880700d40034080d5001c16000c1c0941c01010402c64030300381c484038180391255a40e0800655848070303984042c040d8022602000700701e00000020a10402055884104003a0745000c029a00d200444074100180c00004000b01c0440c400e80000b44541c0c0402c039001e05003516011000c2c1260302c2401100d4000398075000300d48842c4e07000240b2204c144424000381c0008803024400304007622401d0002031150388404c511700701c81003000c04991504450507a04544914203454110b844c1e103c8108158081001242e00180040c8070200f203403103103580a00102010b04140798542140e400c80c010454100b41c8480004103581c0710070240f50a4940520018078000c0d00d0f600005d801101038008020003868411418004d0780c6000080702c2c9418414a0001b007030001c90301c147d90450144010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 382394100 1250 382392850 382392929
    0xe0a030c1a070b0a05010e0c03010b0a030b041d010b090c0702010903080306011b05030c0601140a0b07050709020f1824070303060b0a121503030903020904030c08120901050906040c 79
    0x113112074100b596008505a0f8001c0000c8500340c2c81c1d9038036495035400244100315142a040051004141c031903000041900009000801c1d40040041c41e0f1041000d6003120ba01540c0d9200c81c0380019242845180e60841410001d65160890303640000745141401d000c090f042c1c1c0d900002294040e48649142c0d40715000c07800560b1a0101c1600e484e40e120380c08294a2441803081c2000450481e0394103402c084820740040c0f0305000302d803070300f5402c07801d603000050b00b07441c14081c100001980c1160f0740002c202c0c0341d08460320683d0701c0c0f01002940c0b40d400c0700108940d000d1414140b041c20403c41c400640c0401c2c0700103078001a00d8515a1074110041c1a040e001600c0b020400304800e500716401031204040500400c2c2d091046406480c14600b48030010f200c040d0014048840c104090f080c0055810740103802460080c040d015a5100e40c9080e52121a075006011500d1003003041408081c414280c0000b940c8001d006941807940b0740401020890080042c0403051500c0c41c480098070550641c00b01d4030410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 382395350 1250 382394100 382394123
    0x90f06070b010b0711060d060e07030c0206070c140f0a12030510030f1b030615080a0515100e01080c0108090316061a090c0702040e0604120e040b0402190e0a030c1a07 73
    0x403800c7d00a03101520032007120220f0540400c00b4603009000b8884800442e0340180317040d07075271122700302c5441940c5a8280c860608800d000601100b05000182c1c032454082c00403c2c407507003146804010340c1d0500e0400c000300361810003400040340011510404581d040b0743c040b00050b481f814410355404441d81410000e9003010400010001c098000c00c6030700441568070140c0302d946003502915055680c4004005400140d020750703c1c030b00385030b1283d600b0028209601107000e403120100b81da8070b002070300f041207141d002c5495510690391203404c01764011030440295007411341070490005c0c0440c074460f0080040c5c0e1510321022407082d100c0c14440540100501e01304146c10245e240141a5101c0c0c842640103078107100041c0c02c40540003075001d028070751104441c1c1503400164401c95500007042c100561264895001e80e050b075540340042c0c803031200301110700c180021068001a080300051400140211841c000c10008555000b802d01c0448507054809000000403040b8540c00e03110b6110010715190005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 382396600 1250 382395350 382395367
    0x41e0606120320010605030709051f0609090f02040503031e1306050309060115080a09060908070b0a05010603060b07020d060207061407090603090c0512100c0203090f06070b010b071106 81
    0xc0c2103494403ca03100c242d0059140a1107005007600c88074001c281d00746d48181c808214110b0035600180d803104840900002d2a6a80000202d00721520391086000030790707407041401009894407400d988140c0c580011071510340f030314000c6a124000e0f1004204440c001c00c0c1d50055074210001112580811445d0501081d521a18040d00b80c0d04240d0302c480305482540000701d81000c404098174003100041c1c072450034507035440000102612069a0803185c0c9a210b894443c0002c1c5000c3c06401c0311440b4800003191032900020a90803584143c0c4044101400c11070200122030301e802c110fa21454040d5034211707030341030f0509001000c0d100b213600c000d01141ca030a03d40d000441080c040c00d17004000c00da0b250000c05680e901c045090710500b2101614820b103a80081083e45090000c940840301c0000071b442e4134080720a100c004641541001d0405a040000c01082e00d25040c88072109480341100c1560606c2c003d61503282d010001406a45044100040c1c0801401042250341c604108018500c56035420304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 382397850 1250 382396600 382396607
    0x110a080d0c1502040e010e04080409050a020304110d020609060f1201080304050a060e060f0c0a05012406090305030a030c0504030503040b19051c1d031908010806041e06061203 77
    0xd40d0300303480d24401e2952444902c8002d000f00d03002c80d49840344c0e0703141990901508180340c8002800c1110b50a4041100107110a0036004007031041040e0680141c42e4545814005400c00b41035145601c114041d80200c0010382d50342c0240c440440017940c4407500d524041c610f8002c244a0010b01c3c1c5840c11000000055001001004201399034098034144800f0f82c2e1040e05a641900e034405843c2e1064050040111000e02c040241c84026000000c036005101c2c0d5864031030031115010304680b010903403035401f107207078044118801f80142032518001546a1841d20342d0f9490b4017561401500301610341d0084c0b6941d030301c21010340380659001819256100d5407246046040d52111f10841000e46906003244a200d01600c150381041a10903444240c841c0540f0342d9000420803503202c4140c00c440140341d03032198202003000d40f600d4407165a400c01c80c140403200180c4400816403040c00e1781e610400421001503070f26240031003182c411610840c003074481032400074090800ea40141000c40750f800701401c1815803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 382399100 1250 382397850 382397867
    0x21060d0501150302180f0103020d0827120f0a060f090c081501140d0b0619090b0405091c03110405040c02060708010b0a090621050c030103140613110a080d 68
    0x3085a0b081c2c0c0e002d041d600145c0c5400c100301ca001c0b08160940c0c00403c09070030030702c250310b41551080788103c2c134080880004401414a22030284082c5c00c140e429078401d414048914a42005007800901500381c8805d289541c1d1040410024452a181d040d00e0002241300c1d0442d40c41c80f544507900c0500d180d101c5c0f01607583c4a00500c81c0408012351140001a03041070002007608074200580072100d00f10081c1c40358002c0300d50103000d040d0003107003903040310b0f480c6291982c80c0c0d8060000b040002c00d582c91000100420784e0350192001005804c00081da010401d2600b13003112013480c4904001c18407c03500d5005d02c403607005e183e200f55009810b11054030100303640459641c0c403500c11516030000c2039880d8001c0914500401c4001c60202c0c0c50341c3e2060003a980135228440e000780f01d101c0c07048143c900e920003180a41d0000d0b01c00203a150400b01c0148100090344200c800e10801001c004c03d050304d403142904101100760070300038101103c241c40700c4240f43c4681c400ea8000c1c10402045500071043d0240c020030301da0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 382400350 1250 382399100 382399103
    0x11120408031918030f021218130c0509091515030106170103020120010e011103010302010219080901050306010c050604380601050c100c0503100b21060d05011503 71
    0x30802000981c1d805010301c2040a11803c0344035051400240741e5003a6014058011201c040d4410000104000c1c1e1516000340792103085000109070114244090000103e0100d000c2003403641420340c5100f020381d000c41514800340b400c42d581105602d580c2c3c800f200c0500c00d080d00b0354104102d40446000c1020003802181259a42d40d1001e60741c0704a8100101826400e0000078000340c2c00a22004c6914148001d0424001461000151505003416060700310f0341c900c8100001144040010825580c05000d840043d51840542c5c21481c0345903038540c5580d1080213200c4d814041d021001c104940d100b4400001a190701074120340340350901d0300b05000c004d008860311908445030482d02030b28032141254034062000c400e244244040c0c69210054442d900300c020181000d10940c00c00c06e0b030100d02401000c20342d030407580700c2c150740703040c03080700501960b47e5504400c2d03440001b0400303095403004200141c411948000807030b11440d10b8034400140d465800c1000580a0341c24111080f0740c501031070130040d0899 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 382401600 1250 382400350 382400371
    0xf3f060902180618060c0f0f010507020f0706020c04090c030b040c150302070218060303130f08060a02090906090a020f0706021207031b0c030302040b03012d050a06031112040803 78
    0x11100300c0403c2080c1c828188101c001c2c5110191030b0200d42008000781035500d030150300b40c429503460a84200d02e014800346104c24269101e506000c900c94050100c520b044020324040c0041e01c0c20008043d50325810f0142d0345000780d9a840c182c100b4404001c010704003035a801702407a1a00d0515041001c45240140182075404000a540c142050302903c01c0b104200d0b0302800c5120b210710070801c002d144260080545405010400421000755103800081d00540f41c52680015544c4c1044a0540740010041c04c2c5103c3c2d61041140711078941c1d030f40b402c0e9a03005900b103d0326030a0342d40e5100140064041d01c0880c01d08890041140420440f254000e4250030b21106400c2102e50345400c0c2c200c040e00c1050035190806014800807842081c8180c1004d140a4028100035280079610941400345610036405500d60f2011028203c0310210901c420b1785101003290940c901160502c0001154510306114031405c4c5171761244122005070000082d0b46490021702110401440c09040244603a8002c65010112 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 382402850 1250 382401600 382401637
    0x6110c100f030e061003060509030c1203010603060806010b0301090510030804150327081806130510020f0304050f010c0c030b04150501081f14160f3f060902 69
    0x210301000581511640e4a02c0c41c0114040c61b68440000400c1d000c0c1012125020400248902c52010441c4103410307420000043c0c0c1d02d62402c0c80050850314180c00a40c80380e0000c00040004280030025241901c1c82140c0c00a0715440781c01a0b02c8020742d6030b910052046030045800240041d80b001c9180403210161001e0016070205d042c52450160300c0c00b030300008482e00748414030200e00110050032058400f4031080c0d662070036500c0040c016400c0500724100076006ea50040c403140c1003c07200da1103528400c2c001041090303590300f0819201d010341c1c05914050f0328034004d80d00c220b07032003031007100300160304641540506a101c1c1401c0222a408a40c00d5452139240e0810200e2801c6a1240d10b040b81d0f2075101600740c1d20101084007500c5206034007500002c5031100c01804005070040b05583c0210514a0440f8440b404000007405040441d07903501d06000b4030700403080900f01d01809401814001d81380c111191800588045803081c00014060045881c08001240c01e40d4180d00801c040070fa2555109079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 382404100 1250 382402850 382402871
    0xf03010b2805060c0d05090109030813050a080d17060a0b0705030a0207050d0b06090a0905060f0910270627031b081608040810090605070c0c06110c100f03 68
    0x2503134480c281920301194426074082840503c81c5004c0d0034a408145030041d09595644c48076110340d0004002221070710321240041240b8900310f640d100040028030007414202d880000702a24410450030b500410685183c001445a0340c0c00310000040c1403062985900c900712400c000d41e0300e0300700000e050050b1140c064081164038242001c00880f640c850000c1d00145d0302d82d002e001e94032002070202d40c50305444002640c0010b0341800441e20840da040b24500d0f244c50141c80c40362410034020031410002d4a441000c92403044101000c11008400c000e1145298600e071030894010814600c44c3c904007200241c800c0014981d0400b055041c501070f640ea108081d808071020644020082401840300700200085025466407010905800780110007090800c0d036900d14450900000e14030841d42d45d983e91810f001086100d00c00c0f60b40200b6075180000210301155200c00e401a031a01170300c010721a000c28032618480d001c010b01441480040e041541111000034054045040340c2101d2022905007c100340c3c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 382405350 1250 382404100 382404109
    0x20f0603011a2b150902041202012a03020a050607030203070e0d02030a02030d0906031404020a060804151e2a0e030f0304060905180408090f03010b2805 67
    0x241641c19522002c400b4940007800c184240d840552400400140d000c40002c0800500c42e00e056070a1000c0b2010480c9610f41800d034989000580166903e18810300041c00900d81e80c42e50400c0c150381c282001c0581c2007804c0c10b9489a90411f000b410500c40f2500001400c041d40400c542002920036000c0380c81d15221031805409900003141c5080004849403500d54680c03408080c030750000c50026040e00c2d414515078010a0401603c449050041602583e080200d140c3c144200c56002c00d0403080110582400d600142c045003030f511580e4108081e203408281401503c0c508411844403e0340c080142d5258200349850140954441c4015039107000403102041c0e410000301e2180d44010f60407039418076495801541d8024241c0740a03500340c40358050f00d2503111010001040a020709032901801e031340c5480208203188003204d40c1e642d004611402404001072242c41680c810b44004c40758240c6014070100460300400c40b0301e0706e031940145050700c2c02c05a95038441d400c01c44c28031020100c40e42a6120401d12 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 382406600 1250 382405350 382405357
    0x80702060403050a03110a02130b010507140706390309120b06010311162a0f05030f16030b150303070b09100c02030f03040303060b07061401061d041505030a05030403020f06 76
    0x10750040d00040449c02d00000c4c1d035000785240c41e41414084d0030f140e40c035241c0d41c080c0c00d401030911000781d202586c1480900c0c0c0040143d040484004014582e500784030106100b013041e010600032030442c481c6110030030540104614005068076068043e10b440c04c5040c03c8613440b40603681203022074039112504500c050104100c545035000061040c03504c03c1542c1e0b0784c2c502002d203d106980440d001040d0442050b004041400042c01c0c5008902002c03400c0004060074405840700c04031050b0b00020300d107882800c901c42184122038001400b0000b50b900c080408006004135035102c0e5040c08001a54020425442815401a402c80003118500b500c0038059100b04c510101d941e1001d0f0b4424004003034800c4481000750313403051207072030085283ca50312800d5008541013070004840c0d55446000300d040d002100c22002d4010f1916181c210501d010503a040550741d0040c0c000340c0e00540d15035802d14000501d24680500401020b17040700d1205d407040c10900d441e6005800b00724816400344129089501e800303803d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 382407850 1250 382406600 382406603
    0x91306051c1103100902030c040c0912060b0a09051f0f0b07050709110705160e06130e0d050c1903020325020a0b0301030b1b16080702060403050a03110a 67
    0x2518100031152149007110000908101c0324510045440d51450300c050100c031520314404d08020407907560601c101400e22900d00c9003240110300c1c000740420207a90201c240012520002d084010100450802c10050704064284035044002c2e00d9001403600c9450b0b102d144607140c12420300981080030b402c0052405018414103503807044144040c4540201e000044c00030620034800c41d0b4081e55640c1d84402a80c041d00c09810756081d0218030030381400020711600200d08108040f080e010750800b0654846520050407043c003e10180d007918800903000d51103242441e4121007114503446450f580103102c2d9104040710f403624000e40740d00083d040320000114070110b034103802441c2046229103a854100300a01201010008400040000b50701c500b100d01d00a40f04080f600d641e02c4d030644c20042d01060380913000c210318072911021001748050000682d0600403a142c4010414405c1c0d060240b070b0790050b081d02942c00000014000100040003030644009486511811403600e1080c1c840c03910303813214207230 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 382409100 1250 382407850 382407859
    0xf0c03051905040e0c19110a080d0e15060406050f0a0303030e10090303090b1305122101080c01170c07020d0c120c05010905030c060d05060a1a09130605 67
    0x31a00d03148500005404071020309181072400c0968405901c0181001a500711160f03ca001a10843c4190fa043c40030301e1041450900a0b07640fa5040e10080d90b41100100180c070751200030038503000e52405908143c90801d0408100c0380c075922056800014240199800c62055251103400601805c02c2e001c107100040000700140500c6246450030b401808205483d40341c1c5002d5070561405082440c400e440700b0600075600000c200c000340c94080702e03182001d01b8040e02a01d80900c400e0000f240000d41500550704a102e43c0c1e00c8194030058580680c2c0022950b070b001c03440350b00c00401c81c03903800215005000000d0746d0b000f0760741c3c007000764032510780001340c454102460341081010050b041a03c40f41c25011301c14443c41400a6440800d0180032641c62002c58640062100400466a00001c3c95000e48012000352002c07800e00c074009102485801c007001c100701c0c0c40d03a001490307541d149040080100058144460400e50480710403241e607100c01c2c2c0c1740e4460300b181c10000f402424140f1880b81560380260 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 382410350 1250 382409100 382409107
    0x907030e03031504140906040201090902040e040f03031d0a05010f020f041a09180f0603070b070b1302060301030f0308090309060a0c05011508010f0b0f010207050108091002070c05010f0c0305 84
    0x40f4010303a142030554a5500a526020560f8036085c03d030a54621503120350021b011103051034030004150a5069005981c1180140400e00c800211541d0b02da800c02d03448003a5903242c100e01d00e416405402400e49440d150342d418174418641e80c00200e04001c1051284000300541d80d44028468201e00a4041d0000107a0b030a110a02c101c51032003800340741242c4220001824044035500180c84074013031480c0140c44100c072505100c035203c21040080d800410441c0a4442c06052010f4070320b4a000740c401c054020b0480a010444c0c45454508000c0c0054000e001182c0c0c0e981c50f403d2240042c1074004003100000c940600103412908003005032001c0070001051645840302d8100c049071011840781098031655a55400000c0039450761005600a01c5008008202c180c40442c40c04c1c1118400e80e101401541d605c12010020b0780d000c28064150381c001d081c036581c0d40e01c072550810328280c0d1070032004082d00d100007114414041c000407010100d45099950408401ca544000c03210070410440c004c000c2601030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 382411600 1250 382410350 382410361
    0x209060d031709010e06070e0f0a0308090f0402270907030606020d03051e040c0602100204141c0f050c21150c1317070509010e070807030209030d0207050907030e0303 73
    0x4400764106039450f00204c1c9030319480004908100d0182c64050218402001c402c4003814503088030300c1100d208070743c01d1401382d186444000491040c40ca20901c102c0d4105010421666958161101e0880e407984605025500c1500c03404501c038034881d450b100c0c4401400107100180701e4001d08003aa542640940070484a500083d8003800b40506000c0e840070700300d480c042a141c5c55044c494403075405001001095482c00343d0107401d240303410080c10b070303100d00400050210b020310041032442ca5000359681043ca1001c100810b207606110500100764a100f0014201071040005400b02d050074212102c4c4421140d401c202a201d0702c81c2015025160001c2d900b0100410700c240c94942d00501c0c0d0340c40149025080c2d840409071144c9238211145403e420891203512a070204400320150509851902d0194140f050003240700000a06000411040c60000750080713120b41c0503036505882c00b4044030803d25601ea406502c45202c0e00445024107400c000081513140720b0702070b01000403440350240d072039500d0b00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 382412850 1250 382411600 382411637
    0xf03031608090103020405040c0806090115091e0e070305010f2c04110d0f0c14131e020d091109100603051003050f1515060315040b060c0a0209060d03 66
    0x81c082d21818107030b0922002440b505c480c0030b6040c1031000340c0c1d40e9405528100040140700501a00043e2654443c044032190944d0090a640141c1d038a1840d40c625a0040080c1c1005d002c1840d081024007206900904c1400ea4064000c1390680b84281140309125072642c01e030740c180c07002035420ad440420340c8201c8101c4403c075038005680c000740070f003500c1509050740801240202508140171182d200103916a2800e1280503c0d50f50b010708210000500c480d246c0d600010005d03c481e50030220015500c11440d11b0030030940307410743c0030a100c17080295204c02481c1c48400080404110640b40b20b500300d1a00180f80c50f04600304c5101d828030020340110f00f810326a0440c01844024415211070880380004000b10b1410820280843ca40c0300041038080812a02c2e0002008094882d040120401e904a0f010341c4c2e44000f500e1340a104804854082c50309980040c018003680b104045c1c0060b40003400004105004c02c084044500944100a441e00d591062050080c0218800b500042c818820a6069501c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 382414100 1250 382412850 382412857
    0xc030c0f081b0c0c120a05030901110f19290a0b0a050312070309080706020a1719020c03160f0306051e0915070f1d040207050303150f03031608 63
    0x116140a210688681d5244034443e40c807950120300940d000c60802001460084240b82a01e40f040028003000c0c0300e02d0759801d58900440ca45241441821022451550010801c9040c20843c4000700ca00402581c001e0240c5443d2a0805032514000039400c103500818114000076503034048409100c0c290380390b02411000740000b51502c0d5000090010000b220b1ba020001e90350140c2240d40001e0b568845441c0141090040d6400010103402142c000c0002c00e0300810703c1e403010b903003002020b410000c2c4040421007900c42c04a24010112840c1c004c2111268006070150207414158104c85a9640f2a40d400002801034403c455110481c950203100140180c0c00c4560402e2652650704200e110458000105074030468072004154403201c10030041040b205101038000c5210708100301c0081c207000c0018000c0c07541d00308805a10000ea00000b40341d450b01d0b41203d07113090704101a01c0c0c603410440f206c1c02003a42345e01c52091040b10150304410303151401004595111400d500c00d990300c104141d86480b0740c0e40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 382415350 1250 382414100 382414111
    0x210180302150706050a1d070e06011b080d0e06070216150512040b06040c110303060103050903040b130801050a110a080a14093f09150a09090c030c0f08 67
    0x10300f0721401c0001452805040c1c006d07042610041551030f07121517030510104400e905466030b86c2c8101e80c00c110102c442d220545d0030040a290007020111094a0f4896540d001c0c4001020524000348544640795150701200360900c0c04010381e03040f41c490302e004036178800c5599008080e22030344000421802c141c0b1000d00d64030700f045080c0941031620343c0703409024000c001c450580304201607600b0820300d49020b1241c05c2800c00c450500e034803a0017810200a5585c04020100c2e410705070340d0070119880d80d00800548008044070712000c0c0ea1620007030202c04110207a842007a18075030a01011981e4004c40c1d000b03550700030800700880f50500881d03000072140050050061141550388207841c0c0d020406406102d44500c013848010090741d1640c4031032003102e015411101c2c28031018480781034410040c00d02c0450000c1140c104240c0c0300c011210015150348080605c060b010a4002038030030300140c01100e45421030381400f030100a802082c07403007502941d101001440000c3d400b400614100c0b0b0082e0007058025 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 382416600 1250 382415350 382415389
    0x20c031c0c3e190b03071112070201030e0625030e011d060601110c060901140d150e270c040609020d0e03210c160f0210180302 56
    0x20b80b049600c2690020074070716840240d4540300c455141021105035944800e1009840300d11490040000c181543c010740d01424031380501c00004170354042d204001091131440c12406413480d074407400381200419072162004901290030070350076601b205e0001c6502489141003440d8215041d0400004070b000c101c000f20204180f56603011130f4035410000f40705020301e040e100040385016040000c602c6240c22030040c1554104408070101e0b15010b030000c901c00c0d00d000000e98060380c54034240300040c0c039141d030b80d02048014007802007a22034042c61036812906d160351200c0c3e0b901c0f030307066110721400c5c448810480d40502511145050083c8000440450b07150115808081d03640c0000740100142c10340308a03901c00c00c00e0b80e401003a6450301400ea80b24080300c40d0400c400662800d10b0791050b85044142d50a88601060304800002e241b0041c49000c546d104045166020f001e080c051a0168440d034210f9010780c054600058568600d0b8018a01c1c1c071007190b41b044c20750480b00d01e164200311858a80c0581c0744200d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 382417850 1250 382416600 382416623
    0x6090f040b0d0b040605150306041101050f09090c070b01060804050307030c1401020d05100b161e0203060901060612050106020a3509120a1a0a0603080a02030a020c031c0c 75
    0x400c2483c10841d000c0d40c82014041080d0801e84855014848590400c62180d00312106000000c1d4001e5140b00107080c007800e040f85c54000c0e898144886010784c40c150b40d00304c1141030402000d40c1004004104ca00d1180c1c1805455980b07a41d021100c0302d81c11200203285070b00400045d0003082c052050044014424107041142c9526901c01a0984c1c102c0b0758084085070b19002800601c02180c40e0140203070903000c1580d03007481c0209210078004404003001500c488104402c045490000c100c1d03d0a149402034121601f0b0305000c9506070081081c2d121300d800141103c10b03100c441480358042d40d8102c1d82e00d5801000440400e440c0e207084090641c082c12640c03041544e503003d48450031921400d1800c90080259207501710001401032080004100315240d0300218a800300040c03494044110032085d50101c0801c030307516540d05400804d520342000d17091400120b0300c600c00c00d50000003007103012099403d55411082010506980c4d0320703c14000c8240017405c210441c03840388280105001140101ca0b00a007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 382419100 1250 382417850 382417853
    0x20a0b0c031302040c0201020a020c100215060f0a121b030f0b090109050f07050a0806010e0106050f041a0304021801030b130c0504050106050c06010609060e100224090c06090f040b0d 80
    0x4031750741c0e0701038800581d40208912202a40500156500b03400903184031a10b10f101c000c0c025202e0440340d0061142641202c00b040340c84d11801c951b0018410098400d440c01c64807021440d04d00021507404486802c240911101c4c20b28940100380c0841c1d40c00b00001c11031251541d5244d0070f9880041c0b090f01290750702d00741c03080840d030208410005900700c0c0015045943c209010b2148210540e00700801d0342c0c1c04a0010001d20301944a00307070444890307281090722441e0713110150645100b59840b032210342200588001e01c40d0200d50045000c0d40c401c80b5990400070100948402d112003d00c03020f04180d01500025020003500000d5040b0f05106882c1e00d40c20a4940002404444081c0c225600044000c2802020400200300d51409481c1d07a041001d94246401801001d09849025035405503401c0080d4045850080041a21020601240c2511031078440186041900222581486841104030f2601c042c20040125010548045e1202d24103d008405002c042c102c01220160005400c900d80d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 382420350 1250 382419100 382419109
    0x70f06030902010219120e090606030406320610210c0c0b01030c03021503090c0d081c050a0b010504050306010e060619080703060e071205090c0d1a0106020a0b0c031302 74
    0x2c0b80c06200d006e01a00c02e0f50803940007403109203014200b0740501c224034140103050b1b0b0341b481686c4c0d000d503000c0c2010400000300c070b0030010014441244800f00403012100359400300d54004800d0701c102c500340d59003200e12440c05801c560421100030620064003081000010700f00682d008100341c4951070170b125060914545d00c0400c191801d0b0710036034100728408800d00461500c081414084124544581e0071070800016051319030301030f260b8540c800c03981e078601e09c0c01700a0414183c1e00c178851030501e07001d0a02642c4014102400c0700b01c49181e64107240003d005e81a45c00360003500c0c1074806c090010001e60b82000050040703100060591036102d68180600d502200300c00b100300380e0b20b118554a070380c1c850a00010140135075001d40c204202c0801c1d0740003048511070b0f000001150481d4081004505520758880c42401d1941e91400365400c89800c0c00d8050a11403181402040007071382d84064410b40c1c1e80d40004980307070340e800c0c08020141041d020200b070781c1e080303d04c000d990031880d12801c1410b02100d650005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 382421600 1250 382420350 382420393
    0x70b190e0706171b0d0207020d0204061707080f070e040f050616120606051801030608121e0a020c121002120109050a0618090311060703051008070f060309020102 71
    0xc07000103032224201c0c8540c42c0d2904441e6003140c0c4441c0408030100012035040040d0045c08808818254007003030b4081555510980798032a950050070070400c140c2c41c0c0c41101d0002c0c040000a22241c8a41b24000a8080c80000d80104003034032280030380701c15410701c5400b492904024006555151003040d1900128206000c46405000134903c0c0609a01500e540904071400780c2e074210810a141c250100400c50f004412036185810040a4150303549201c0c0c01a4000d003603542004100d84950301c0e0141d101030518000301290b50800700d181010030084040c0000500c0340c00100c0b0010381000c4484038850500054102c11003002d0030a803000c0e030700d1447c5c5010403038100c0c00c1800c484c1c0c0391000c010000011144140c031381103001807905102c01c600300030009841140c074101001082c1e60750140074080c14031841201e4001c2d070a840980d040d03411700d038200030042c1c10140c4205526a401010000f40f1920006101d4216207031204240381c02c0e0b290810a034000c012651083c0e056009100d50110300c40d01d0400c13034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 382422850 1250 382421600 382421609
    0x1801050912060f01080f0307060c110601030503030105150304020f06210702070311030d0c03141317060108071422090c0905070509060403080a0e060a02060105030111070b190e07 78
    0x188401e2411034080c01c3e4110040e40f12400a0700406201d00c1c031300e10b0100c200e401464001001240c03480c811340003201c81142e000342b464024010400080304012010000750304850044840c808001a803000003c110f02c4240e078020350050344040000018103040d4003412402c5801204100245001d100c881c1508500b06c0b580380047e04108001d10820000440044450f48140d0081104400c1c1b0034019100300c01c070a4010301417203595040501064410021509102c0d58420030950340341da500c1c03e00c400106469400802c0340103d80c000300d06140000b80b02005c07100d0460000020001c100700b44203a41d80c030488582043d00095085140c10080e6000c0c031140305108500c5070710351624000341a01155009801d82003003200c20881c0b100745503035040540c2e040e650441c00581c0d80d0945c6050030b6919594003400a6041480407400c8194282c011035200c3c101c40c4c042e0020b02c051600f1203100d0a00d8407840400520001410000c07400101d14000035491202d03a100303000036001c0d00b0456052505205902 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 382424100 1250 382422850 382422853
    0x30e0307120f050711010c1506181d0303041106070218060907020f030a03150503010623030309010f05071a090102041a03070e09130c090204050915061801050912 71
    0xa0400201c2c0e031180000300c14048510700141050300342d64030003001021007071855040014030a5024140601d4042e50414650b10340c13010000030f55202e5403d05102c9e044002c4001503440d0414504021024068050034403001602139461070399990754494141540019042d00b24900f40907500060b12801c51a00c090910031090184600d054002c0015286000385480308641040100010050000040d40c45011040c2404201050040007540001300c880d4001507040d0301f4800c0014081c5089400341d68030b2101415a82c1c40c03c0c60203010b040d9244104240d150015a0022034220f00320312a2003c0e14209200d001411803513140025031030200c9406540b240c285941c0018104001c020750b00c00300d4002a00350a245081d4070305564040d21482020104c1d6000340c00e4040041d18407043d500340340c0159a48205860318094827440d1142c001e4029000c1e50b401010340001084000d90303030004499014000806031032402000080007001000702e001da02d4140f00081c40410f40faa90340500410302c9940800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 382425350 1250 382424100 382424123
    0x301090e01150806220b0f1b0301060c0206030a0f0603050f07140a09050705040b0a0e010e010e0d11010909052d0412031109061b06060616060903030e0307 68
    0x65000d42190302e607103103180d00c0284000c41040510702c04109a54018a0248208400303004550410091441514020aa10321020802c1005400180360707500640d040420f85811050f01110408544020b004030700100320b010240c10b0051518800031680071000c0240801e00c0d030020422402518680d8200b26115003080c646030208a804005010040000180c4011103001c903102160340941680502443c032502c1e41c0000d10000c0c081d504903002001200c2e03080d40d40b030b40d550000511030140c0a52060000b03982203000d8200d9803107a100706071850b0004003010071f61000e9540b00b240c050000d1070443d0501458030300c0011012100e02c100c621a40641e0001d1030030303001c040e0900030807003000c480950b51640d4078010300010071101d00d2024500c44e01410006900d48401080014034000d5143c1250300100009000d40041d9071040304840c40d019910489020b52101070810840b030148200700c9460111a03429100804d2040e040484054000e080000300202d4880340b07a07086501040c0e09464510250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 382426600 1250 382425350 382425371
    0x10140307120b0f21010603120c02090711030a030e0c04140a054206030c0c01110c0307060f020f2b05070801030326102d1a0d02030109 59
    0x303002d80701408404541c611146101c41c0c0c00079030320302000103103050406800c44c1c4281c000d403025441100a0358000d0301a2082c4004000001c080100d6400d007240642c03a0080411412400381d101c40f0f4240c011100a54140111884214010868800d000c4880c1c4178114000c066038071680f003036101801403025010801d1505000b03034016650b01821500745070440d5405000c2c0d013000c42c00d43d1710900c84601040c840075103080c810025280c1980b510309501036000002d004211820100a00c00368955500a1060102c0320807041010b005030000c005082c0c00c10404800010565480303890108070f041c10042c200640503407102c0940d0840a02040502d0310011000344402201111004c0b1101809080c0000c1c5130240000385400418807004090240c0d00d10038600e520620900351512400030030401070203140880c0c5400c9845078131320840301c40816440085a0710aa0001001d040d80c000031140e5491616200c0082c02c071076000c03400869150000d2208040329a03c03800250700030710a0f041c01080803545c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 382427850 1250 382426600 382426637
    0x1b0c0b0c1209090117010f020f0703180521072105060901020324060c0a060c0f0e0307140d05070605040302010e010527060f12070e0604031110140307 66
    0x8003400310301041e009000e201c03003503074854880c94199240303080c0b07040c600111201281d0141400304514441940081003000d2440440c2015010f15406540c17800402d214070005c20b400c0c1a000c0c0175140d04618644e458202c0d04078006400e141961510003100ca51556030f01c04c2e0820f0012000e44c04507090002400c01081c004100011500a0f190400842ca103060401c907103c1c0040982c00e2505c01c1100c95500008903550b120255002c090482c4c007500c0890009141080007040000d244001050385100500f003800d101e070f01c01d01408035016008240300c5041180109012916554665009081044040011b002800711400400c2162641500d4a055100143c040311034032449a04000e010721142148044402160548201d00060301c0c1e40c4140240c040f0b552481000c40c0040f054000062040d043e0800c0d840c06031003440c15540b1507016201d10740400c481807080340301c00340ca448007103004403120b0f140409185480c4040c80c1428421580340d490202940c2d041100c01d180440c2001000b0341c50b0002c0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 382429100 1250 382427850 382427863
    0x81609050f1003030311161a10320a0305030d053301141201030c0b030603071502030904140604050108010209061e0d060803040303030e150105011b0c0b0c 68
    0x240e101d20851450000350b44600e40341d152002808160311407403c5032181005904803600c000d040c1d20342c2c0132050200c0c180324007502d6510070001035640400000900081d440c00044069880f8400104101c54503440050114080c41418000c111001d544a074075656403154920015841030002c1c4d521050b171114640200c41e40204a015084803820046007019086c0d00d00710005603004410300c1c8d2010307031000100c0b0400c148006405020310002180300001c482d00141d50f048903c5038410315101e944905c0e101c0d826000c280c403080d80650220a0900c001e2a424501c0c8000c0142c510480b401c181e91000010255503421100d07541c158888014012182800d000c1c941c05130420340002d51030b10074414081003080c4219035007100038001d049000e2400200c002c04031840a50000824850542c41e20322080e103070350140c8412000f003840e1040d580b040885c00300b907141c1c680780700030000b003220787c80d100c01903501640301e0461b1030f225000d8400c8040000c0d40003005002034500704488649071014016114a80322 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 382430350 1250 382429100 382429111
    0x20a050105011203080402060307021213030b01052707140a05040e070807050409020a020a020409050c240a121b1e020a0b2d0c13090b010e0906030708160905 69
    0x224500f41c00c04a900546101d4119605a802654030340c0c0c3c0324000c900785019401800c808000000307400034407131482c0074a8401e907406001c030282140d9a980412040440b50380d24500a00c51591106200c4070300000d03a958445880d04020040c02044141e00c44560301c00e400c030f00086480802d00340501c617000070301194400450709017224682004200600b0310b001d2407191207051a0002403202c40107200b4070005c114542d010b0301c2130040d0036403844c0c000e4844400040c801d00407406441d0120205641c21401d004415844d041e60f440d0900502c0304456101d609461180c00c3c2d5210b070461224581140d420540c05442070741e0b602c0885001c05030701042c0340c0c0411581011984100700060104482080d031a07008500480032a04c1c1c01103072201d86210030740c070100381c0c440e825a0004006800c1910002040260940200b1500c81c0340c42d0500075085440401c0403074001143d030f0092004038141031070540e4025500804039004182d0b203488041c41e2440221000f1040000c41e103003045491030364013030355401c41d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 382431600 1250 382430350 382430369
    0x91e03160e1504020a021e0c030712060513080403110103061d01060923210d020d030f02120412031d07031406060108040f08131e060926030408010c020a05010501 71
    0x170301c004200030358036600e440543c1c501c10f60560500c006ca900800420b03d10390b0001d01507039003041d51020210030280b51941e0686503941060005001100c3c0001062116a070248035275040c5419901c4d240c020760114680789050558401c0041200390303001d00102c404102035031b01c400d9158103014005094007030b5517000801816039216248444050845000c1c126081901e04a4001c0c5c00e2105018034103840003050340c10382c02042d04895170300d90f010500b1000d460117a1800e2140b403070101020000c80c440c0c0c4001144440f50319000c03c0c0028000b45040c540c4000514020601c0142d000d00c0c101a29010210714900c1d5201000810800001c1050740c4080410100548900d140c107400203003009a006000500103681c1d4a40c06042129410a5a802d00c83c40d0040310341803910784180300d2210380100727151810492500c100185041c420085030381510105010b104ca16865045a04c482d90030030b518134000c40c0000e010108104000b44075065070304200394001c100e00241e0342096809c488040c1c112000342d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 382432850 1250 382431600 382431607
    0x50a050d090605040b1326010c0804200d020a0f0f0902030c07030503190603030804050c10140f1b0703021c0b060105070809180105010207060302091e03160e150402 72
    0x18a90004151000c580c0c0c01c050041d560f500706000e110000000303801403030307440304520407207d0002035000034030011001c030340c0080100f50091481661148030441e402020741e075104032401c0f6090001d00303000082c40000340414a20282c103a00007030000c2180c4c2c10105200201c0740b030800c500c00880d40c0740c400400c00014210b1440c2014190144248144940681403010000100351400300d0203200c509100c001070002c21500391645402481110160740a132024803458642000514004a6140007401c0c0c1742c80d00c3c619006e403688201e1080c0c000e030030714400343c1e0818800e8050404251070701240100c901d001a045040c02c40c81003004461044800d0b440c504032910080000481c600817480c1c11140900308039031508210b01d0045428401d00c541e180c1c104000302c2020750201c0f05c451000d8103030f1b13801740c0913034001a45680c2c08404a00501c40003e9020614800c030460302c0e070400c041ea03a0112406011703110150b400030541c0010611f154480d440c05681d5004009401d620130182d0460100100d9081d0326 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 382434100 1250 382432850 382432859
    0xa17120c070b070c0e010906030b070509102318040e0d0504030201030b060702030a0501050711030c1903092103300b0a180504061a060703050c03040f03050a050d09 72
    0x19681c0d614002c2003010140081d04000784003204071070200800760ba1441300810760b100c841c0364000e0a014842140c441c225a008103401c05c0c012001e980c8020005020301210880c3c0d03882c00c6551780031a403801c04103040c0c511010b4800024071001021a42c1945100b102142c403001c080c072046600300401e600c80e54010380408408640c1c094101c80880340c0918000c01c111104400140403032190903030007981031140124410400c2010f4015512850345c40d00e4000040000c0da6101e40c0fa4802d000c800303a01500030107544181c0c00c0311000c06045171402464030f00080754480e403190341040041101e07108003003402378035802003540c410400982440f008004078640d480a090720010303402c0301c0358011085c50721418400c1d950744501c00350800811710004010200061105030000810041e80c080c1e5070f442c2480514401e501d044000c07000c0c02d14010b091280f03000440e4074129000d4000301c0c408407040c0000c200000d900c58240c000d08001e940200d010b01582141031904270b2400c481c001c0004180030764907400b0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 382435350 1250 382434100 382434103
    0x32003131410080702030d0603062903120706090605010f0f0f031a0603010905061905010e04020f01120209030a030509131e0902030106081e0601170303070c060b0a17120c 75
    0x40b5421198204200c2e2611201c0c816411405401112020035140200c00420304c21a9004680200c46001d0154404004c41a0312203004803001c0c182600755024024001803020540b004090a502803140040d0104441d0340340410340740203034001400c03aa00050107105000ca8032905d44010944040042005031565560601c5a0943c140700c5508085e000e0005140385c40c00e4004036a065806010345025180840c00c114002e05e040d99101707007052510300041810742803e0ba0150203190020301112200074500011642c0c410464190607500b50244aa00d01584017046442281ea200343c5550361915411018800340c150507280801d000780c1450503004d0540318031020b62404164800300400d0f50751050000ca800340c91103610a00b001e1080c0580c07080f042501d610681c101c0442203060351720a980e280c0c0090795030003144c1001005a00204081401140225100b0403481c1c4544804a142003000e40014080c0103030390f002070b240340340e1748003590700c0c502c0c041c05440121520300c50072a04225003078421a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 382436600 1250 382435350 382435369
    0x706020c010e04050603031201091b02010905100209010c051603150b09011401111b040c05070b070804021507350304060f0e030310050307050f13090320031314 70
    0x150040e41d4134404580c0c1c0740c8003802101c1603181d02c01d424880550350307011030302c00074548442c0381c1c024600400e1000220324810300450311240c0c0c2000050494181c00202d40b80290300485289050003540042ca2001903010b000916003070300143c104864480ca581442840e4490744c01c00100b003146400c1c4280c15030b50314a01103905480440d07001d42c00002104006072120001e00210b4a030610408a40f980c04600c04081075080060a0320281309040001c8820b540e07a0246800051000404400280c54240318454696110340010141703001001c580311a40000e43c858a0142c0f01428942c008084141114100c0700c083c3c0040e5140f40e42113052640100f4090202400050640d0344502c080710202169030000c09a585800054990703d00741000c101801c100b040c401c0601038006c00e90005400c0c501304120381d401d03610151201c1300704c6241d0b14521009000c45034044041c403920300609080c48040849503450140920011a0b440e004512001c1480c0280d0313112106200200115244a171200d8040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 382437850 1250 382436600 382436627
    0xb010e041a0a0221011503020a1710050d06020a0314070c140a17070318140d03020f0d03060801050604020406050a082203090608060904110f19080606030706020c01 72
    0x2100032501c5240d052070283c410b049140c41d14410011310901518400d4130260b049070540c400c0303583c005080c048103500368080c0b2484000803032100884441010304598030641c1c0040b81160310340c40389845000040c20091104003c5c6d61030380e4045104c10807207426101e2526072410543c0604002e01d44450000e110000b028402804552102101d24000008000000c0b5071076005c1d00c6003c1c55841c0c1c43c3c40740c00350b800822095000441e1a000010882440081c42c1e003542c405000c94090300c000c1707030240061810060703001c5003148204414031018008c18049000c074056160390200f10f1614050403242520400f80c00c81e4802ca204103c10048150002c003156071340005410f00700840d955691807003011a0a07140b000b59581c1c00341c100382c4105a8132182d502d0954403151241c03007503915001c0c10b104400f01e0449006041d8405004030003018900000e00d510a42001415800b0f401050941e000d20120580d0051206e9409202408400e1406200c81d501820340d9100602e134041c103d200007002074075500750 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 382439100 1250 382437850 382437893
    0xd030608030a030f1b0f0807031b0804080c010f02090f03060105060403142815090f061509020d0b010201061d0a0b01031128170136090b010e04 63
    0x4440400300296045203041402c1d00800176150154500b02400c00215260110f000803c4800003039501402481442c80c01101c841d100c0100c00700032641580c0b41c1a002e0030a40b5071a80900c503c05035000701b4010004920020000540c4401d42d01040c01903030100d08003e41c0c071070b4001d18010301a9855400564046980141280c40c00c03013083c0e50750500b4404006454850203506803801d107043c2c0703041c0c200030500c244070780a0881d00d14084035040e8200c81c0301981c02040313000c5122029000c01c1403030700701c103003040503110714003180d2607444040703e049900209202d8401ea45901900542c3c0d80c0a110f03100040107801c0c40b41c0c1c851711060505004410005148484056417200e0b000543c0e4401c1d130021038551800700f84503549402040141030010020000341c003195200800031a4454424801c5d101c000203c290300c80700c0360b420041a000310242d44040742c41101c0646103501c1040b81c41001c540164605000300058070303840c90030002c5c182ca0381600b01b0800c60b0030307400a210014103030700d2000002c0e503200702 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 382440350 1250 382439100 382439111
    0x2071e0804051002030310050f03060a0f02041d01181103070311070c090203190b0d0602030603210c120901050a18030c1404050901050609040b0c07050303010e06030d030608030a03 79
    0x280c024098000c9810150300410504124101d1a07000070003540101502c00310481c003140d548003001080d03200d40003490303015001070000c9050a11180c00084010814450241c20705c2e807652400308202c07081300050001158424010000d10074401011251808402420710101583d40407041c0288400340c070003410565184c0001440c00107420a440b040c0d58414502a8850340e039894600207900140c500c072903002070f4170009070403540044c07040c0c00030504080c00100b182c1704561112802500010000794040c0146041a00540800c0e0301122a000d10125030a8171080004681840c00c3c025a1042100036400c0000340b101ea03800500b03441d060219403402c1a081c00521407441c03080e45807031380010714400319000302241e490329242d1510005c21050700c0c05c001c1540c0781d00f161426a0801c0d0b6500782c101c00010301060100c5d0140702800da2100c0720740b070381d00e1031f060107503503500d107140d00980c0f0010705000d1400901c04ca500d000d10480d81121140d141c20300006007020320f010345a11603e001e6005155440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 382441600 1250 382440350 382440353
    0x703080c0f03041503140603071719030c0c090506030304030f150e010f14040f060902060705030c06010528180608100209030d170402010c02220c021002071e 69
    0x4021210841e20540c003035a859a507610307064002c0f20000050358000c01d04141007080e4244000c4502881404002c00030000d940c40d0140300500d1904418580b0140d000704490101c124111a10b11100c00c2e2184d0354070309030f070751140c02c054200000942140d511203090005100e0340b65400015101960382082a0003980b58007031421060000782c0802c0706007181c0c10005040d500341d0040d40240d0004890b00402d1000182d1910b08004d100b5084500070000c038082e010030000320b80907511100c06944050416882c010482d01d0f079910390703080303681020103541c0250700511150404148c80701e18100074540c0c1851181884485480603840b500403410518250034400d94621896004640104443e800742c0d05560513088400001c0d6020b071520300c0c003074810300f1100d0402c0c41c412015860304a130040800310494a466004480082440f1400c1ea0f00255034901003104040031007003011800c0006000240342c10022130080d0610941d41a140c440c0d62051005001103505a12421003c4405805005103c0400d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 382442850 1250 382441600 382441603
    0xf03010e070302070605040507030c0609050a09090303061a03040c06030b0603070804030905150301031b050102030703032016060509160303110f150906090106031709180a0609110c0703080c 83
    0x21301001400c03030342c01c0800748010b014011961a003078900500c05801026240c081c02d072642c100e284143c0d0340110b440c01040103d2040b680c040d82c4210300c00d21380829030316540d160f0314454240341120000340860001c04e1004000c80410300c0e000501041c101445400d08190000384540030083c6040140031201001400700351049881501511000301211000c18000b00301b2801c640007404100c40f1040c40202c0c009a41d0382085940c42141c005900852a02115035400c40c050482d00038004550020f08001003080d0403d203019221030f81d0300540100c0e00f0700160900320107956000d08000c41a070000c21070300107500c64244006007944d825040c107011241d41c0c590031a03e0082e2507680003025001c1c0d0495145003000861040d4058072107070044451944600c25003c0c22a19a84030050184a5941040350041d403400d0107401c4001c002010381c140758103030500000480408545040f40103540f03010a2160001d544a8411403224540640b410308041a112954031102c600001c0c248c20004188240000310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 382444100 1250 382442850 382442857
    0x22170708060f01060c0c15020d110604110d0c09050c0702010201050703090b0621030c0607201e0f0a082113020105031f030c050913200f03010905031209030f03010e070302 75
    0x9004019984003c0d100a4503088441e031f03d4400243d680c1382d0042b4410000408a0244d40c010b040c08140e0040e0303e0801072803098090007264600e007007010008549000307104031032040d0fa0072100b040d40c481c1144002400c580c0c0003050700050510f0180050040381000490681c001000c0d66640d00d610100e241c140842520011107810310f00c40040c0c2072101400104403580941030035241c0702042000004660295240d64145034280c0d0302610071103e07600c000c519180c0400c030f80441520040c29a45c50450b0408840c0d00058a50754130019100c11107000121310290800381d41c80080d09c03142080c0301c00403c158995000a4100140400070481003491241c0307000485940e000c210183e6507403840c2030144c90b019482040c1c03103440e080c00090503041004241401c11540220044d41c160b4606001c0c103507200d5402c0341d40f50400d01f9110240c0c1c45480900c20520914041d40003503032110480a41c1180c0c54600030040d514540007400b44201c40700c415420350f81036a00c0d101000c021555501c1045000b8007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 382445350 1250 382444100 382444109
    0x714210906120c040503010c210c0c020303070302012a0e36010f060305040f0f03020c030d0e090105010203040807030305031306020328021e22170708060f01060c0c 72
    0x141c4450600c820b00920300c00134400c98801754000d2245c0e4400640a0702c0144144a40c40a05900d121103090b501c00e250348109800c07140c5003810000b401c800c0d00800d240d41c03c25201100940c0d0758817203007502c02100c00c40c81840c24010110714111600c0030302c002082c141c1d480c503e0b6405a01150502036842c15541c640c05104102080c403007404200d01d5034038042a000030310810700d242c1c0e032000002c900c440c1709014452081d60000800030941c00039603107010480c005942d06a08500540c030f1250b4150347d00b4048500140420341d50060107500c4079040052402045e440a815980104420010b0300c4000c1100003c40e6014280b03140c50380d48072100040503420007040107108510000c1000440c0010521103200f41c1c0300341c0001e028102070f42035004128071880301002ca050802e40454140c03410b2401c01001e60324132550f011000c44042b050a82a00e54032a0418001c2d42c50b0b1001001002c5410400e502c0102142342c018400e40c246440c0d48a55800103028107030400001c424028117000070044404010f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 382446600 1250 382445350 382445377
    0x609060c0f03071b05030105040b01050904061e150e01030222090804060507050c09010b18010c0f2a0b18010e03060f19050606091210110714210906 65
    0x400f021303d005418144103607600c18260402c5440820340d4241441200e100d40c0d4080d01000b040c1c0d00303140070042c1c1c036000140201d80c0c3d141c607508440f000c200d0fa03145007801180615030228400b00b0410b81038501c0101d9801c145202c4c01d18800420142e80c07056507000551001140d10303000c114032000d8244c0500940500036005010000c5d0005a01e42d01c1001880c0f105c0c05001500c1c00c0750406010860680300a00ca0740202d03032018841d016400140301c0100062010505241d06080c030f0b503546120580c1002031064403041c240b1043c5501b42608032048840520307022110582171400c1441072011409001a0041d4034907410380c0a4032664098007940d482100010102c80c05490924101040003600320f070429041301e00360005181d5107807680034642c0200b5000f0300480c18500b800d401d10481a092034030307603a00c500c989803800c45042c00e180304032a0140428204169074104500384090008401c2c40056440e90002c2c071401c151501d90308074071006455407610540d4a003d003500003a094064491a5983d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 382447850 1250 382446600 382446607
    0x5090a09020f120714280201051303032712020c030f06131505041b08010c05030a050a02040b070f03021509061504150f1503020403051906291207050609060c0f03 71
    0x181d010800004904207a81621861400b2440c1b401c030300740d60041d01d50b901d15038a012090b400180c000d4101443d03190000303185503214209031003841e075011140c07a4241c1d00740f03031078215601c41540d05003c6007654006c02d500501c607040118401d40d5880f00000c00703400b6500c010442440070454182d60945c8007100c0c07501c1c1404681043d0411a0b602030b04044100781e42a024200041c4d0100180120044500070f901c840782155102c1b41402e0286c40020482079485908200c00700b207143d00c1001501085010b40c0c21544140083d16010303140ca80d50000480d005d1061104110040c0d10004550341c1c0000010311804031448503001041c00342000444545480c05142c00c00318205a254030a41d08a48818540d0003001a99003000da0480c402c0f4000504240c0101200c2261031007010703071301c05925101d1a000105200d4481107001c1c803010f04100d088501ca1b401032050401d10b0040d20205244180c807000d022468503040c000f81c142e00c20f041106010b4400850b0f074110b620720901100c04410360710780c00d0b25903 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 382449100 1250 382447850 382447867
    0x20a1d01200c0a06090f061b17130f1220031c080a0207030e0d17070f0b09010e1c090909050303091605031f02130605090a09020f120714 60
    0x2160345211055500803d00c0c441d0000c0c0541c0700d003445004445500d400d10035207031704007101250200b8450800604000700a500c1c4400200015401ca0440c60008a0f00e1f40300c0460100ea050780c08000d91212a401961030000d000480d0100c1c200f000041e070240c1208400b0303410004c031051014104000c00d07898011a00000c04541c100503282e60860402c0c1e40300c3d40c117551400c800c8012030003910b03000750000308403110f40e110b9410560030350300c1e009005444180070003e417a2103158096020080866034803c20115402c1000150309500381c0050281d40244a4449442c1d00213682d02000a44071450650030b0b8240c000d09405a100703000a0074620505204810b0f40d401d24517074071350040e1740c0702407207104d045a24100f400c09800c005041d038900901524440e950828078440c4005c525800ca4107559080205106016000188100a1005031265922340d0122001c0100c0c00b50b050b440541a907004000301d1003d0710003c0300300d40d54499440c44098898503003210840301520715480c0f076180c44000140001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 382450350 1250 382449100 382449103
    0xc060a020c13060f0801090803130201090e0106180501170c0d0902040908091c05070506030c120f070e03070b030c0f04050603041506051002100f0f0c03020c0c010201020a1d0120 78
    0x1800d40c1e11a2444c019603da0300c41c481804c0713a8400001078826001840498480115951101d406900501d404518039442d150410120306085e0301139808078180c4220003a400c031001140800510017400c10440c0840c810440815056004040c60806080000c2c1001c2c061026444818490340245c001c00850040b032070030702a80e500c034a00c4c0e20712441d0f1162882c02000c1180c03288400c150303804000703070001a140500b03004003130300050110445140c0c103102620410000c8818584a400001c808010314200140e003d0040d048680d0340d14000e40203010280001002ca01c210794201c1c0c085000259980c071580c0613110f4900568003c07a5000380b00000740f00034000d03400038908140d03880600420413550748a00704105140588846001f41c1c028607440000b440555020042d04c03036100d00c0110341c5020121f02c1c142110400c5100034086a8041010488104108000004034800f800214900061408091f10029400102420140d0401c0402d901c0d03911070040d090b03140c1041d130340b40f50040c544c207585076 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 382451600 1250 382450350 382450361
    0xd0f090b060f0a090b031e0c10021b06130906060c031403070e0405310c0801060503031903090c0902072001140c070e1305060a0902030c060a020c13 65
    0x6403106414000451064907002111a4010030018640038140b850003142002078000350502560500030400d00700c148800a054446c42c9801100140841b114204100042024080c0e45d001c1194426054041030710f00100b401880c401c001c4464584403c01429446099161504900c0e105400c2030000110311303400c580410000c61080d120303803100600961140e1190f020444101000038400b02480025003400d0b03014030b0704926107050921001905096901c1c01c0d4105001000d14008000c0c840414440040800005052a04000d025051600c40020781e00d001d469540c901c0561003403030244510303020f60301c800646035100c018824625aa108a40d00035048a502035401d98110101d65207611700c0107042400c4610140c444494402d0000c002c107030250040100458944540980441c0502401405034401c0c04031428035005088145800d50520002a1071400214101805c0d000141d40c08a8042d8075030000790384094a880b070080c1c0480c81e2904944115410030440b180b690507003189034110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 382452850 1250 382451600 382451603
    0x90703090203031e041503090f0f060e150114030601030209010608070c240b0301020c061b0909010305061e040b0105240d1a012102071703070e0a121a0c0d0f09 70
    0x80d171b4107050250402d8064900c10707400103002d1580400d08100207001100c031300b82014000d880025614565002d05450040b8651000b021b0101c8600100b0000e15100b1122504030f40030381c00b80c83e49514650100742805018080c0d44107200079070000175a4103120f81e00316542070341c203e0381c0c050040440c000070a000c0704070614664449410b0a240e0102e600b814000c61760814215802050303d41e90b01600c000007660f032040500c1101c1810801640190307110181c1034003030f60007607000d0705007070500314181d03000e010030b01080190040d90b8108120100c2c0c99013021504444080c2c1e42c2c50325901600c10f40d800802c0b108035406644407004902e20102069a50002070400005900381c0c1d8044010401520041c4107603001d84a150000301c00c005080c82c150300980380c000d105480302c401d000910381e082006138208482c450f00203582d090160510f0b192001d40e0000070300d0032002903055000c5a40701d20a40c0340481c1880780c019680301d8042800c5c2c0702c02c0030455826025040c004c000d1300c078107603803104040d04000c1d07070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 382454100 1250 382452850 382452869
    0x806030610030302032a010606050d1a0105070803150405090f0607020601140609180f2d0a0921180f15110718021c050402090703090203031e04 63
    0x181141d07040e540004240c0b50190011410000842090302441e99001800a03103030200d02c82c40c0301c03180d100b406800050001900ca503038854488160600c1101c483c00040068000412041002c990700b0104403a900354000b5440c682d66903d0035101540fa50100351441d800500d41001c02110102c085035607000c1190307040a0f540030b80c54800003281d40b054280aa00e0011100c0c100500c064030f03144008290310040079003440c400b83c54290b181006110221948410010300c541040111603000e009240340d5544001d5900d2805440c500f00d08d5180c4005000004060340c07025400c05100c4c0c00000c07031040c40d15400c0002003040b4007070b500400d860f4600100345401a07c0181c08102145c1103004c0c80240d83c0e400c040484000502c440444070003080c2c40388420603015101011400850f10094140c610b16400d40250759006681c4400d9800e208401100c0e202e5494103040c03200690790490b036036400600615020504070f4040c00044e00310f00c02d441a01586442844a03606003a49900c05002150344002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 382455350 1250 382454100 382454113
    0x231b0c0f1009080a03080f3303100c0203040305071505070807050a0c0306150815040308270a14010c080402060c330705070807030f03061518050a0b090409050a02060a080603 76
    0x101c5129403151410000070fa00505109042241885086420312248e401022940300092205440d4200e502421041c070058100040a00c01d00504010040c0105409203506602000602d4010180e0150883c002d0480e0740018054090100030450042190780290054141607aa803a041009144015403580c582e882d0820008000c0800306145007003508549a1490340d550756541118034500040c0122000c1000482c02131031800001e035030400301c40084005081e1440d1904140144108401001560b40e0505030b130600c1d000c3e404954540c000c1ea050741e00b40e80b00c00c0e8024000d400c0c1003081d100d11000900c09145910500211072020010724082c10b01d210481d110b040c070841d076510820401810705502082103400003031194a01c002480606c1c0760008502c1d1b201c40403007200d500751100440000d86035180c4a1b45030b2640c00c00030001070000b2210a00d40c5454406007103024000d0310021840307959200000c00c2884010700c00340100a600820b0150744243c40c28000c0d002a00a4604902911840 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 382456600 1250 382455350 382455361
    0xd150801060e0a11070507120b01170d0c05190305180405010e04030f020106050a03030f030501152106031406010608070206040201090302040507231b0c0f1009080a03080f 75
    0x41c42440251a144851000d20341c0e00c50500c0707400383c4904000c07400000400c004e82c00c0428018001c02c3c0c050480081c0b540805c1c40c881c1401080b242068105101c0921008403c00038680300080407074420096042800e800229420000d04012401a0824060b00000300607020103901c1790080680e18132510802c7c01d14030b0b0700c605201c1298001d00034400840701c0200424042401442c0c11a038406d918400410034a071118041881c1c00e549900403002b240c0701d0070482c045a501070181d14090002402031060044007008000c0c6080340c1800600081949908101c2042d07030950040d03009150402c089120164407000f411390b99007000d102c5d150014458101089035984045a02c0d0301803074050f514800c056085400304402001d019001030709100c1d84503890481e544607a800300180000d000d480603200c5c80c0040f0140030703000c11110317084200c0d0016007000b01c00d40c1d0f403550342c40d040d00c0d81035480880301650315030b09585c04030704e079008040030703101d40e01d146420568405040361140c001d0352001c00742c41d15007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 382457850 1250 382456600 382456603
    0x20d02071a040f030503090c0301021209011d120c010f062c0f0f070e151b03042312030c010b0a0608060306061507140c09010f06020309040b04020f0d1508 68
    0x90310b00400f094445a00344001c64441c00c0a5500150060183c070007603020440020b017240d1140c0030080e0146140360804c98119028800c5110302001c215100c110803c103000780c0c5440d101c55066000c100c0f540821101c100e00000d51240c14200384030030080080680396074904444601007221040449003000185840e13040840304203000740d41c200d4840c140e40d00c0d00d5805400910004000f64100144031030091000d07981c064200c40c2125031038680603031b51499107843c45a105800d200c011100c0d88100410840001d00303c1c0940c11084075944e9080514002c12300003602043d448035880f46d03901c0040f841c1c0384c0343c0b94194807250300c18900300c035003a420550b070751800d841c1d80a044030801d0b030540041d00003803441d051600c1d8552040c42804407141c904052a03071901200d1440d11400109584146880050750601c400c1d10360240540020f0600c0061402d00000c1d524454400c41c28080c645440001e041912641c0594950b22000d09034a0780350024420000d00409225820b203442d90103c00e00080c2c030480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 382459100 1250 382457850 382457903
    0x170f030408030409020904020d0c0e0a12031b0f050715090e04210e06040e040c0515040909081e122a091908060411181f09020d0207 58
    0x907850041c0d400c040c0782c080040003c0d00034880c5a40c0064080200c240240c102c0d1040c80704e1000c2c152202d40141c0340715428809040c0980e044a903198080005180c0400c7d040030f00200c00000e0790b03d1818500074949000908100c413403000401e070740320700c500200b0321400c09050040c4000c0141d40380c50084e5580e14035184261819240640b0665204150300c050189a43d00185110360a05100b180300d1050400b1482641c03043d03208043c120009000d0004020400d4511402400200e860b0070590604403540802c83c8543c0c40389104007651100950b003008500c2c03050320389281c00c152411094440f541894100c82c2c0c803864540b9040e2091a00190304070201c4250035a0300010340c0080c4030442c4080700001e41e01d5002c03031a01031780800c070101c4103000b1481c010511380180082d40003902a80c00e203031400d15082c5864002c03051140c2c1410720300e01070340c066031601968001990607144141020500d0f404401e01c426802014802d400003030604010403482d00146803461050540403240e10904400781080079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 382460350 1250 382459100 382459109
    0x30c1508130807030c3314010303140a09150c060b0d150b0112090303090507060c020306150103090f0c05150f0414120f0105040311010915020f07050106170f0304 71
    0x2605101c00740c0400c2c031030401d8070b030130500c06c07512621824201d42c200701e800140303407a40701402c580e003204e07500101100d406000507016224280c41441e504554026145000c500011101440040750041c1c56901ca0080600207281011300d00c0b82080302c050005140302d08941e0251902c50070310071003c1031400c10a103c0290340750030a039102ca0f620303400e49070b52000d42901250241000794014101c2485501885001c1e04148240c9002500c100c603417410509140e0158013200520103000348640c0035840100385141c0c4250980e01c1c000e190351080c40107030010008400d016181c0002c6039100c4007045051884142503980440e410300880003076005602e450f124024102e079440b1400c0c0410082004200380c1030140000082450b00f00c16211044e0303915241504c1e424640c81d0b9110010320041c55003290b0101d20140c1c1c3d0790000d01c080d0700309407510587d400e00721303040080d042e03400203c50765a458820309564090380d024009014581d512a0303541e20320281e075584601540107060211140b06800400c881c21507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 382461600 1250 382460350 382460363
    0x1050418030f11011104080a0c05010804050a0b060d0b0405014104110d0b07090b070201050a0c03110d0c060506010f0c15020f0c0f150105030c04090c030c150813 71
    0x42d0100c0c00c048038802080c0180999a6499a24241aa0803013502820150014a009113600d21180c1040d40c1c0c400083d40c001414070644400388004100c000c1680410790340c1201c006110303a1680b80122704001d10900026041c0d80b01101440308005045d0846002141c0221989500d03441c140d009910301d86245d0400702d02e41100b0000004d10211000b0110360141c016800702250180b480007040503007400c0030040714200b14a030100b004082d0450400c81c0034041201c0030b5400d081c1c1550001c0e0040c80358450750300c140072141e0075400400d0310a15140050845003002e5498100443d400907208482d1180111000d500f030100080c400c4d40f26114600030b001d8240c1d50100303240e0258070b0303043c50808440b40d031075042c5808004100400003130000a20306850004000c22040301d10310022800c00100c0003c1d40c10581c400401084590f400003841075042c070302140c0000d00c60004c2d00d0005101249a403000b050f141506000141c6104c404014440f114200c1c0c0314104250b40b070b1070440103461207040008180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 382462850 1250 382461600 382461617
    0x11010305100e04050309090709060908030a12021b030c0304030b010b030f0601050c030f1207110105070e04020c01090c030c0f0b0c03030c160209090f15060a090b0a030c0e0105041803 80
    0x2c45416a40854005024400382d0746030401440c0400d1100328102d40c50000b01368411400c0105a074030050f10320040c50700c1c401541c20054003060003011240207401056a0a80110710713508040c0d44417170940c1140081310300b240c4ea030b40001704d40d650300c941103480241c801c002c0c0d2400004004600d01e0403644510002081d40840d950b071b20005650310780000328010b04030b01c42444404004511700c3d0041034516080b06441003e840c12110040c24030a0800f86481c469052000307200c0340c20703082000400000d4080340d0150302c81e45800c1203035004191500c0c001d04262f42c42000002030158031891501036985ca00c1e40d4248440c5c070350b51020300c2c1d445000c003180000c0d8000c0001851409024010704a680070712084155440c01c9500020150102920801511b8004040c2080e00310000c00c15450003503590b9615010b649458400140c25102d41e01c212550540c4909081b2400d564100e0480041d6a00490000b0307416101e20160941c007109006040c00340f0310700703500c0c004d00b8411208901042541581d03039845 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 382464100 1250 382462850 382462859
    0x12010f0b0f150f1b0604170a0807030b0d0803010e010f081603080a033b0d0815061c0b010e0103060b0711060d0204060e091e012c0109091101030510 65
    0x3075003c00e25443c0c04003000d01041010524540700146103180790b030028000c0d4106420301804407551880c441408200411580e080b40b60018212a4046050305002818205d04800f1a0504041020041601d00700100108100701121b100a042c0d0b01802580207003107854000c500e65608206021083e00c0d0161181000044e11400c001d020007180d51a021a0f484c103054440c01221a42810348580c060550540039400103403c5031550721000100c00412a42e80754410141070f2980251060040c40151018240d17203840d0340d4212181d0810350b40417243c801c1c3e400964900240425030446001421040e805412507100e03002e0101510120240e061400b4030541d03942240500940d0301e030b03401c841c1c1400121007014451025100070700b41760329080c0300c0c801c2c420308005658500810b080f0b402014960b050140900840507a419511458910284c00c45622814202c0510900c05440041180000456103c10070707000308448911400c0d165008080c1080103400783c8808030340c503410300342c1102e20400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 382465350 1250 382464100 382464139
    0x30201050d05060f0a090e0c0402160816051501030c050a0f060807030e0601270203010b03010e040804030f08040503011a030d0c030c050109061e020307120b010e12010f0b0f 76
    0x6030085070044c1264000c68262002c00d003403160071750004415944c2c829440d8801c6800b800f89807103820007140c3c11480c2000300c0a00a404507843c5d2000340400102080d4458081c003046850307080320350480c04a035030b40381401c07910048421090208076070070940c4103c0041c40f414541c40c40c1050b1424425100c80203802c0c04012989150300500c03840415450701c814410518003800b40a0280c400c0074084071103000710703107950780d6448030002c10095090310401c0104800461034080d641511381e1001000c10039150790902062902643c1c101030400024408130300c0402910400400072560b080d4001d22030003102c000c5859201050003406501071300805100031549105a5280b40424441d0505070f0054101d0307212f040c21904680401c40d01a03545180456150a02040c0814a413161001c10740c81d52402c4400145103503401e81080b0200703a140d043c0500e03903a001b06403090107120040c1814501c075a1407007000b40641030203141440b02074600782141289007404100d002602074098541c1913404145020070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 382466600 1250 382465350 382465361
    0x903060412170405070f120c050d0206040b040905011410020d08190509030307090506040303020d050f0705031c320711070603090b0c040326040801110d0b0604030201050d 75
    0x12010802010007034841c000c000400e1500a5004e0b10041c0705280c14070150049080c0c0c03503084000600d14118a080008038222655010303200d0688006556484070b102140950299070028900b48002150210308040079500050407262814200c0c43c034800003c00340402055000180070060f0450900040001e00440b1041e8222850609010000001c400744c9001c0342d0050ba40528603420000502c4681c950041031480640320445000c0d15051940da0040e42e034000b10400c9909000020404209610112003522102504039003030300c1c1da032480c440d404140040f22114000c0305920349200d59501402283d9040344000340300d4608080a00c1c1c520002d203075208003c00c4041007044041881561103000e03c0604024034107910042048202c605c0e00c1510080000c1200442c1d020a03c000c0000ca40da600f01d8006c0f60210880c0c0c00848404244020300a04c40c54002c034602e0340c2000b509080c3c4045000c0206200c03c2040400c2101a10000400503035215511000e8000b07081030290301041801765106 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 382467850 1250 382466600 382466633
    0x20120f1e15040c02060405122802160803030a060b04060f110102040906030f120503100312090504150e0f010803070209091912110601080d120b130b011409030604 71
    0x1001d61484401d0025058401000a9000507080350b070902c002c01804200351a1006034004545007040c01250101c8804039100500c840c812040c8e002c0c40c8401ca000340858642400d60791070000a01e911b070464950780c0d60061f205030b48036903d4034400060215a403420b803010307240d883c1d0316002c099840704002c9542c0e0030341c070680e81107a5500700400a9800c0643c482c00c4015446441d05960300c4410741001204c6100d111001000e00100304100500801d130066480300b41d9602840fa0340b12102103c20072074604910341c104540052802110810900ca50000c40d001c0324440e5200b82410740c0e8000040c0c110000c28450704030594000d10403100146408051140e00820241c129800f0441500c032590343e000440700151500c030202c0c01c00c032811650002054000f07261120003490346500d09051165030381600c400c10340401c144035140442c10003d0380c0059590150003044034019000c0507084100078545500d480b40880d041e00010402c00c0e41000030386a00b414001c015200781d50350750b01c1d809102c1131001031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 382469100 1250 382467850 382467871
    0x10060b030a021b0f0d08160903030507051c050c100b030c040b0d05070603021213052d01091401060609030c030b100914100f030203031b0120120f1e 65
    0x108440d01183c00c00a15844129201c0180b144d860140b8000d01918800383c40803003280c0e8420000000340b50407070714a20440b41c2c0351808990b03030343c041d0900b1400e201d5884005c2c0c420180320010207007055445030141001d01c0e083c0041d945400d032010840011600403e9200d5055004140b0503845894070313901228145202420307113810343d103550b0f5456050400940007900801d41c003007000f01d105005094580d610129149120304c0c141066112a42d031a1402d0310b0072106000302449110603030100e850b914201108210080c800b00180380303040614035a01d005502801e62a10000081c120b01c6000d1403821640c0001401c1101421500c800340d01440003080e041800b25607250010782c1e01d40c0c07481481151803200a6902060900070700d48032507441c0c03c1d4480880080042418005650040100d0317030410104c5e01026840c1c44c0d844507050141c4410400750010000c00354060b400d6084100082680d4018884606002e540d480072132820340100791001002e01140f6414820100c20501da21038000c00b2904 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 382470350 1250 382469100 382469137
    0x3042102010207030c0b070c052e020c0a26011103070c02030c060a0309021f4b0206091b0904020f0a0f030b06100c030f050d1406010210060b030a02 65
    0x2113071085c070020103500160f1100000141242030040407039006020305402c4501c0200220004082412010041001c40e8924083c01028001a008100361580c2e018007074800414207640b50003030351040d40d103040a000140c442001040d06840f062181c54000310f1014070060450300d403060102c4058540c1582203070503106020b4400c3c0150303902c8000d04000c220954001c50084031501c14003004584440d0b03000e240621010055400c1031300300340c0155040c2d040c0041c9940c851507007040303240c02103440a942c48011788002031100141c403a040380700a40d00c18503000c5958580302c080159a440303503801d034110b400e155002da21100601d008080d40e030300240001e05804070022000300082d00070701950300c4454460b04a084c20820000c42c074000c0c641c081c0c0103c034503030311215901030080c0001e0fa4100c0300604008204210340080381c010020754800403054902000300b11008000102c0340d40341613800354054400c060780148820f92901408040d540158201c80c2140c0300d0480c044003a41151240001c04155030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 382471600 1250 382470350 382470353
    0x91e01060305330c2205130b0402040f0b09032509050408120709060221030408071401020c0a0c080d1d150f030f01060503100303350601020601080304210201020703 72
    0x740c410b6070042e150030791116a6203541c400c05200a510031074010881c5542017104001c0c9940f4800419101107c0746400b080314250500050002e1140307810441c860015a14041210b00000024048a04040e02115a541446100031145d0101450113810032414070009109805464024039085841414030504140c03140418820000046950500143c8010300401c00550f04020700c03024148a890304040e114028000320000d844000e0002d00310040001e002001c00114100c480c0304502d50f40c1c002c64072025102c00f02d42d1a10404441581e0f2040490310201d24007001040e0300410681613114020396004c16040d21506102941c0e0096004400804403546211080020000f8103003034040c0079904e02e0030b214211040c81d41138000d0400c010f014010824105006003000d0181c035010708000c0c802140079800308840682d0301095544a003c507421007403590300d0541d42240206000d0302a142142e889100203540c03800380f842100030b51110400d03103c4000d03180440f8803005a0041c415240265146d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 382472850 1250 382471600 382471693
    0x30c020a090e06040201080a140a020912070902030915070e010c061107081903060b0406050c120d0207020a32060904050405030c070605070c050402030a0b030105091e01060305 77
    0xc01d140429000f0408120440d031380055682d51001c454282004604442020400e131400020007403210240d000403005902c0c1d403028900310a078003809085030f6005841c0c3c1121800b940003903e4242c02407082180d101c0c50401410200f520901d40703565600040b80c442e41c011924000e21f010180c0c1c0c1c0e5603035003035824000324001c0000c0c108035004e20320325652003410008100c8001e009400c0307801050301d802c1c020b002e0a400101182c040761090f10b4140d844501c5480d506040100d4200c1e80071620a0006d83c050314614550084c1243e1402159030b051820f40c1d864003040300140d05029068081c5020070035844001010f044103c00400c041c0803d400c18000b44003040403190142d4041e134a5038000300703070407031a01000c00a503809880705142ca00d05003032950380d880c10440712502507680700780d401000080b1803040755400f4006206004000f40024101042200d0300c0d102d50750b074052581c002540000354101c0c0140030703010803a5840340c020586030743d03c01c0030285003030488004400c80e03104042082004588 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 382474100 1250 382472850 382472861
    0x209060a170a030e0405040f02060c010e030403060b09060a2d030f0309050306070507020306070806060d24050108040c050d05030c07090510060215010608060312070605040605011d04030c020a09 85
    0x102a00102880012410080c000f045024542c80c49071b1308150800000408404405070b00f075605840c550340300c594000f180d07409401e415580e100a4407020078000140001c40c3c0040f03c582d10203590310f46694450200b80001d90303002d406068040c554442e60f003041c9841c01c500d10603d400e0100c8402c2d10160300d80d031f2031302d0100c08405030640c0018602d040911140c50103100c0300d0b0704003a1505141d8506041c41d130200b501c69800410100510841d500001c0d526111481100d0340000030710340801140c18409440c08a109580041d81d500400c0b559010590b5401081440e00a0340c0002442403224034120030071030115031506003160203010601844140c910b0800c8810302a0140c001c2c08202d41c940038001103d403082ea64014021580300300c046541c0a00c8495036107054401c50302e807484c00c0ba9103100100345440c0f501c10040080e42030010b000f0741440610f50059024510481081c000c40e6a0391000965501071219030103a03a0a00c200400e0000c2d00940a41c0f9015101400c1e00e85095980c129040c100c90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 382475350 1250 382474100 382474139
    0x15010e010f111e0601060f0c08070212030d0515010509130b04020403140f0c01050f1e0f0403030e0901270f0b091302040c110d0e0402040806011203020d03090f0209060a 74
    0x4503140c41d8410311400504c20039002d0221032a2044800d020358000030004c5103031030405407290700002402c90030764556800c00d650b600c1680040380d5569448052444c02000308590304103055a565080380c030190320030300c103c94240304002d0008100071766035482e400081032801c02160340716a0030800007001039460234280941c0b071a000050401d24900144140c00d1903010804941007100070000e8854100c501001e407607880708004221450030110541d44034051141d9130085003c800040717030004c2016072028070040c01f89010b0b500904541d0740c44039400200c0107a2071009115100241594003003030140d50101c00c040c10550030106407001100c003c200522002d880d402103908014540b03c007981054050318551042c80e2400c00109120034401903143d244101c0c0c110204440070011459650b96a01510082c1001405131103082d40d44014003c206000d47c1011009405842400700c3c10b18007038801c0c40545904070700c0481188080307500300149100010700c0103510500400c0081005ea803040804070445 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 382476600 1250 382475350 382475383
    0xe01090c06031103010f120201141606150e0103080c03090d080909180304050f030c06120103031e090b0307030219020610080f0a030c020a030b150915010e010f11 71
    0xc6040c48801001c2c1c1c0c01d21412000075403c1040100208011a0186412a0810f207090300c0007258920049500c4010069450701810b40803918101c0351a02160250040b0f00c10b40c020020fa1403064411001030241c3d106508455503d140100b0104036004001e01c1503032003550070780c0c2c0780240140c00124400e200400c15900004003046c03404030703820040c07510780d0020380074550341000001550409580f80304a010740d031300170100038001e2007054401b004210307a0400001c200c203468070310003091480e80d00000d11094000604000d914040c1003400c0740c2250000f200703a9100c140c0c69080144005060b48041c004400b01542040010488802e01031a01299400365002e000785083ca543d4070003480c089070b00b0100440d0441048146041400200c0d03011440d454208550500b0a0b030000912900c801c0c0d001410002160080064031400c03603c40c01c101001c01c8903080c925072120b90764410804411030107035000c9994040c400d0070b5580034100d4521f581c1001c3c82c243c640d80a62041013410300110350102d4410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 382477850 1250 382476600 382476623
    0x6070203070c120f03030b010504031406220503180f0d030207090e0c011205070903020d03031b1106040212120a0801050a0e06010212130902040303050a1706180a0e0109 74
    0x100310b40752101100610003603860080a200646500d80d8061344100d008003490303514095079810364010000d840c002c54101d06190401200b8940141d25030344101d50744580f08031041910011807150b11811521b141d0482c000b1070601003852032040030394120320442e551005000700c00d42141c1c0c0e031340021485014400d9010b00002864806c1150995000b03e860051a4000c41420451641d0003450071405e00701c0c4041c00309054031012025980310110783c1010790000d10105108040c940c068024560508540704240107a810248089032180c0c50701008002c7e68000e80085009490108018a0070340c5030401030301d20b1488404480d03e001d6218101c500301044041004200c585000040c0c540184030000240c1158038108000130340b11142c0c084521074600300440d0b528503e4441048480c007400c00d00700119900c90316818007404503000024094002004c8d43c07141d420f0b507034034001c14501a00002e040201c241d401c1e10401c404a0030003e1558540c2e582c3c0e107260100065007405201c0040c1e014440c1480c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 382479100 1250 382477850 382477853
    0x302010207050d081605030a1506090819020603072001061211090121030309020d060207150905060105010c05010207210f1704150f24080109080a0509030a050607020307 74
    0x109110000c030141449854005c00c02d025030b80100815448110746001c0f642e0795030340d40c0194010083c2c0c00c1420f00300d050395017010a44ca40c2054110064508980484240d035050740074410381081021002504a070b010300218280030f00520000101c0308550b00c41041d2031142c1ba812500b129210f900c49240941007001d40d0080c401e000c984d807152003800340c4d0701071555070406001d5865001040190703070250070f01107009801e0500c00d602c03088850754002c10b851286922800c7c52070207504a58009c3d60203410412104c88108007500c100b090071540070001d030003644c3c40c0c00019694400d06480a943c1c0b55001c01031b6100040034200002d2a11011042c9a0141c510b050300051100124500c407509001c0b101e40e0b000440e81140d00e402c0c0c0d010340d001000205004c09080410054a4400e41e00d201550400421032102c9910f00303d465450412110a0740c000c07681c0d02105801d1b104110400f0300355107010404010494400d4008103400324000d0216a8090800e648061400200b01d40600c0140c101141450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 382480350 1250 382479100 382479103
    0x3030509030c1f2601030b060d080403060c1101021303060c11030c1c020303071b080403051009030212090604030f0f0b01080f100902130c0201060909060b091003031e1407030201020705 81
    0x144c007501c0c0380086241c03002500f00784090800600003d0301882044001569580c0d59a1203005080e07030280420351641c0e07032032800002a00c402c01001340843c10703001040441c560b0510a40e1142d0003205141c40358030749103403620802000c110401a0402000c440c84414982d0100000d203640800c0301c004096485008401001c481248078601d01190010020b002c3d1095000030160100190700700c50b00e20a0900d8030f840b06051003240c1c00201030b1301034102c2c5035030711022561126139114000d8003950181c2c2581e210628080c410310205d2584100c0c00d10047c80400d48400f000180c8a00c200c00c092481002526403604a41007640000c5042d44404500d40350708006201003a0410300580052107000039030781c0001e6001e1075944c1103640803a034940704503442900c01d4000100900d10b041c0d041064456600704000074100c1c540c0100c0c054100d80d004543c0d8244c402a5440032030344c056690708200e8000d5040c802007607120700c101d40304000c9518125219460400c0040c41d0341d52117500016500c501500d041e5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 382481600 1250 382480350 382480367
    0x9090c03060c030e0d0e010e0423330406031406070e1e040e010f0c050703081602120c010603081804050708040302100b010201090804031a0c070c03030509030c1f 71
    0x24101418040e844c0020300d40051000c0c40c1c0849410007001e0702410b4801221a1034204021a52140c00c01140d42c04814440081d092481006001405180d6440000031141a8280c9054814255a200000e0106041c01000c079502d103005002041d83d585d6626010703030007001000b10f101c5030f0300402c0c28401016082030010000700400d0300d100e059408501e109000c0f000300441403074015034442c0080e4820040079881445000e0740c07500c040000c11a010402082034002400442c007142c85600412001170101c00d10f5043c6804903402441c061011808001080e013180b0b49019556483d90b1002c00001c14410150419040002d40b00014624843c03c100540c2c1e0050844010b01c20180144804a5030224241c03011204418000c1030703414602c030040380148102540034007030780700200d03003c41040400d00c030720701c2603900301c184084142c1c440f400452810310400c0c000400d9191212000c00010340194050403642d1401010b40e4115120080422031b442c0441401c810f00c8110081c951441d40c0d00031400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 382482850 1250 382481600 382481621
    0x2220010f090e070309031b05100b1206010303180305060705091e0901050918010609020a0905010f0503040b04030e09070c05190b06090405030403080c0609070b0a0c030f050409090c0306 81
    0x1480500d000750140b21200302074006001c0580301d03040c000074907010304114114050f0040300300000349003e080c241e231501418465100c906041188840f118504484030303d03040341440b40135081c4c42c2d1075a41e06480700c42d07401c5680100c03407011000010101d00103000540c03103505c2549415a0702c40000c420001c0c219241010162442da2403101500700340c50301441319046d60802d4400d13030f210b40c0703490b4500d942d50070312164500c00a600b00040800e40382d00680251a0007145500c1d003a2445407610010b42c1c02a50010921000540a00020b000f281d80d4502d901e40107406420842840c588070720106000702c80071036611021501070484030041060030421300c50021744100c060f03c0d90742030b40d60300c504c01190058007051041c08018041030600c0700a208031002035500c4007400760fa0328190507040d44c486004031000c031040e0182100004020361700004440e031103940ac1d95210541c2c041036030b0a0ba5400103c3d5088002c0000030720001c100040c941c0304421882d401070901d190068a103103001030a55503590f01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 382484100 1250 382482850 382482857
    0x11100e1809030d09050304090c0905040b030604150504030e040c050903120418021e070b010f081b101e031e06120f060b1801081c082220010f 62
    0xc00c40360310790101c19652142d081550103d440401e82c1070261440c042d0b5007042d042c0628207515660040e0704440d0250803250700b40d0703041c0a000070480030180c031008202e501401401303401043e4801c0c00702c03030780c0031a81c0244203007080076800c010344002c142240c2c6000e0050010400005001205140c1040041d1140701c1d01d40c078607450a4208506020102401201000c84607000700342c80c01c0400d40c148040c00b001c05c6c1c0c0d070449604c0e8000d5040c0503e404c5000e10460100c10543c0b000400c1e00b000210b144410080031809884464614000340403200204112540402100ea40d0740d206100b2594a840c0091106a602041003e821610a00003808494103440b1161510404109a00d16814031b4080e694000307100181c90040c2c0d082c03400240203110111a40003a1080d100b9201e21aa189194182d0391213030120f500204440718071190952400b1081c1c0085402000042d050070103c03c480041541101c0034141d03202000da071680c841000200e038490b403800180b8540703400ca503032207035003800c40c0031013031030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 382485350 1250 382484100 382484149
    0x91802030c0d02042405010f02030405090402132a020c0409020904030f021507020325020d1e080d020c010b0109060807050f09030d03050103030306060e1c11100e 71
    0x280000d6660700700210341400351001c1245070381990b4465100c10400e00d003013400e00150060131400d08501c10b0481c05070342c1c089501561989642c034070000541e0152440078000941d142c07201e03000c00c240400e00162154445071a005101030f00300740d80c1100d200400fa0309510396501c51800002904150b01d10001c0f40c0280d01d001e00790005a510180b6890700b00d6054200100859901d00c3e081b424070901c2d201e4101c2d071903035100c24840300c940d00000034030b200c05081d098103a00710501c0ba1410210000340700701079440360805034a480820b0100d90b44055015207030040d940d500f121961080340c1600708000a8910a40c08107001c10f11800070701032006002001d20740390181c94141039010b480703138202514200c104000812900307010f0141d20101c0d900c01e100181202c1c5002244c0706c00070013501090104074002420070100261407800360b100c0752514040108007c01c50210710603106403044480c04140c03030044481c5a81c481680b1101a40d200d0001c19582da000140130120900101404011820350303100340e01d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 382486600 1250 382485350 382485353
    0xe09030c0a0204020a1115010620030d2d0e0d0905100f03060f0905070207080622020406030609050a060e0c010e0f182701060e06090a0608030f040918 66
    0x2007110040241c0c111801030725400010b40855607280e6001d03041e01d41e4815860102010f9401c00e0302e8604035403032591a42c1d108942c400c02c500c604006526801060740c420303c007030010300401c0c1d0802e0000c0340040707010000442d1110800c048594421000c0e0103410b81d00d0044089081050184004410803030400b50701541ca002c0109680c5206560001c00700704800e04444010741c0319802000c010041d499a07040003545641505009146c10707503054015215681c0009a0001d0205020703209807040c8204249041541d41c0c0b80150403980d0404076400307542c50102100041c0507108120840d4000c000604020722540f0302401202c03401c82c8003c1c0a544803405903403082e07038400c500c80210402501c07001c24070700c0d0034000705081084141d40c2c4400c60201d10200200d80c041d01044000c408494401e10000b82d015a0a04d0f00f21891381c0a0440203001c441c00180d81c50404c2035640303805c4200c0150000f0202da5540301c0350f00315006100f10140c0c451001404000c81e040328000c8050546982a8594101800303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 382487850 1250 382486600 382486603
    0x402090906011409030607031d060415021b0106032d11040c0e0d1104230c0c0f030a02070f060305100608060d0507090903020f0a120e1c050105010e09030c 68
    0xc0640b4104281c0402c0c1c0322101801030191440e1100107011180a070030011005000b5200d031204406941d800321410044d2000d000030180d000740d802c16140342003003c1d6800041c001e0340c044141d00b00185034102e0360003041e500c00d110700c00041d8000c2d240c61030060601c180150000300c40c0c4462a40086140310644085441c0c1184840100c500322000582c10081c0310b81500e1000407481e103541d01a403200000020b10412594023034002c001105c04100200818240034000417940b02c1760030070010101c00192000852b04000c000c0d0310b140b5012110000442000145181d11480c09240103820a0718204507005407091050041c00d194202440603107005034a100c502c84840c0f041208001440c004105541c40304050120210303000000d81c0d0350f454441c803000300030304044941240140b0406800003540d034008a8005034069010140268003000c12800300c58403000310903441e61001d02c0c20031504030b02c80403d00502c0f500b031244001080b19850540841e14942009282d036009400400503152b40c0c100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 382489100 1250 382487850 382487869
    0x105032b05070609020402070b06030c010512192a031b1209020a05040e0f06090d0816090510030e06012405031b0403080c0f0106061d013b040209 64
    0x2400d00e8500d4070b0707400038200311002e0161918040d4000340b00050400c20710500c0d0f05000d21580c000d40440d0804c1c0038000046519200b8510507011f02901980800c04000d9075504e6000180d80190000c508102c458000304141041503030100224400c2e030442000c4903415002d0902d001540010201c03a15580910207410076086800c01e100d60b03980c40d071400301107681d850f60110160802802c100039102d01d8490055840c1d07000d0940200520411001840c01c0d100000d201644444550b6507101a49840d000076800c2d5020b08104001e02c44490404a81a2994003018519851a40c0c1c00b10b000c0c41105422401c190042e0840e207144015210071881031180c0407805016215140b8001d0ba9940e90115281803480d4881c2000c201101c00040c00002c1c0212407001d04040d40591080e5500d031014684414203c520324420321010442315013003d0b500012180c01c8407030004060404240a0980d0781144400c1402a881e0960390b0740740111302c0880d80808042806044000c0d1401c40c50045484000344000ca03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 382490350 1250 382489100 382489183
    0x30c08090901170127020111100c03021201051507020613030b070804030e120304060f051b0c15070f11120105010603050717102c040501050703110306090609060f0901030506010503 79
    0x4048651000030081c208030309c0c4201e041041c010402900c943c2d100601a6000001030300c445030000c0c3c0086164506100b42203009008264220301d0102e0640c24441160041e0600e044d40403408400000407802861805200d400c00341e44032051440e00d0718002e810485d9481c00300d405038103120041c43c3c07034000c000100c600b40d80103030030040200308500e01e080310700344584072810500010091204050807400100890074030380455100044800820780601c2c9400b803101c01501e04d2009410a00c0825201c0c15000c666407000f0340351180b000103582600d404d4580aa01c41c3c0d00003591401081690f075070041c0d00e072050321416a100e094138100358400340f040c1010b07801000c2401801c5443c2e20b091100b07a00d100d810004440310140814903050910303034000c040449001004c2070920724002010101c010483c2e00c2118010300c0d04030662501380030307c0006100280b100e90406241c1b60f109000b560343c1c03507100d4001d620a400502d220340c18a0181400c0c4004518a0356068147c0c4025040303c64011541840c0322 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 382491600 1250 382490350 382490357
    0x20a20030a0f0e0d15051029070606050d151107020109030b15150a14070302060a050a0f0e07090e0304060815030a140303040c0501110703030c080909011701270201 72
    0x201140014400c0c4c410040c005004686040b20441550700d00d420035403061243c0100d040c0a50740d01c0d0320502011a19070200302126850041160004415070b014101c3c1741c2c020380c00000e11030340741c00118056011210040e01d11401a0901c240c1800139402020103032031404001504003c080d40c0044c0038075441d404002c104026a000240c05542503601040c1151001404029503004000c004c440541c8801911000101004800d5038144032a030111201142e2590081c1601d566060141c002080003404c007041540c0c960756014a0030000d0b010f0385e810f40c5041005005064500440c141c00c90300c901c4d1030301545401c10301c01000765981005920380c0c88040c00e082d1400680903000082d041040c043c10042a046040802d00c0058000001031441035109240c0c1c01d00cbd8176142d90040d05d000407100d40c402990380c400c0d401400020f100b42c800142e07541c0300ea803816040031001c0001035084c1d00d00760400c00600940600d4094181d009001d04503440c403200d50117204100e800d11072180c00b5854001d02a050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 382492850 1250 382491600 382491617
    0x90504020d02071e062d020a0207030210170105091302090408090d0f030f09030b0106030c0c0203030412030912020f01030e030c0604050607020d030b0303031303050d020a20030a0f 79
    0x30744085030100d80c8060313400300c180f50300d40e090203d003005842c200210581d03203285800d070122290b60510300010300ca02070600007500d031304442402c20000703503200600d42411401008800001230b190541149520075840e29241034002a9004895011070305a01252103620810700b40807042d40305452003148031b42c05445081055940342458407640c4a03004020750008101c48000060148583c3c4c122541403003540c450140c07801518027203407144c50354080501780314811001080310740d01903880b551209407542042c1072180840d40001c0d055411660045d440c801c240740341c6604150f0320200f40301c003a0181c3c3d1800c0918014940200340d1166039004020b05160343d40d031001464080c2041030341e151103206411680c1525103490810345510060b1200c0c0054401c030b07540d15024a000707000e054400d2002034001c500350303994600800004450180b0075000e00004101c03101001c8003c5c001000900c81540311499041ca060010689103014002d264016400900806507120f0303029800d01c5a031030561034050304 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 382494100 1250 382492850 382492867
    0x160c1a15041a0603040f0b0406050117010e06180c0d110301050907080309040506060705010e0a110f01020a020607020105070503040602070f0506120414030903070602010e0f07080618071a09040f020a09050402 91
    0x2401c806c0c2030018014804000410003001090340055058480164201c0c081c90303400c040c19401e9880c102c50004242e001400040c122801003481522078182c000300b11132040200001180d4860030201040d00d002c03800c107400400d641400d028043e0442492001440d140385400e03502074490080a28640c8504d84640201d1a00d544400c00c0e92201c54008000b00648040d1980450340e41002e01c4003269241980800400c480c94040c034081211001a006414507020580c02c010441e070007400224140042841103e0104c0d10400150010b06490380040044a007001d0f9201c0000d00181c0c1312901c950402c000c104022140513800641069005600508822843c0012401c2d4007800303100c280c0600c1140340007d01283c0c1504051942c1103d101a40d20013040c240c0b03a651512001c1c002d04000ba4800004507a004c6401e040c0007122911210940d00c1640e2603980010042c0340700c1213408483d64010500610398500391140c16082d034800700e0304501e4800c064002078110501442000c1c0704550110341d611 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 382495350 1250 382494100 382494113
    0x30c0f0702041e050606040b0a050d091209030506010e04150207060e0102031504200a0809010e01090f0b0907150c061b05071712160c1a15041a060304 66
    0xa0340964010400e0100c030f045001c040f105032440e01004000c0b242440301240403070a00f00d040f50103882410003aa45170402900094600e40d12114040300295a141d050303a0200345c030050f205400c2c0c02c3e80d58404000500c0c601b0030920b842030603009014030004000a010015612440480310341280b944050303101e1905085c2040202025800000c040d40000108410003080507040c01c40400d013114100600c145001014100d04109000c8483c8008204030342c001243c00b40d1620340d4000c40140000c21003100c813459440c00e641c05164100c810100e6103170003108110800e6241c82d0711507102c0004001807440c003500f072442140a125041d0a1202142c0240c0074481290408406c04030310092003441d0802c2d50900034030b50313800703c0c3d000d40d40300000e0000e24117800394841c00c07212200c041c07591660060f00c030752802e030b03070304a40492020b020f004035102c901000079140807244007009110041a002440c0076405101607003241d9007250321640c82e08a44142c0d00309544a24407004405580311520303503075140340c2003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 382496600 1250 382495350 382495357
    0x9030712020f0f010b011404050307050f1311071217010608130507181104030302060604020d0b0d060906061205100f060e0a020c15150d060b06070602040306060f0308030c0f 76
    0x5442c0e0740039240390114850340542044c4446242a07076484569482d0840b101c0241c002e600a495060300610001c00c207a2902c00c8195003c500c00800f0704d01c0700400d51030100100da03124444010079510100300f1200b440f11740101c0c0e00c069011801c1003503150340c00c03a801c0c05241105000c0c00c420700c10648003161a01030031600040c0c8040c0e1000171030b244692100303007451850300824407100040f0308021807c00b60300e4101c41900d048983c150010700c800d440301020030000e900174840700d201c0b842d0748901e698021342d521003006550a000d0038001032001c01030b043c503000b81d800d02c1d040800c0075810049040300140c0c0000303100f4540780c4d140e4000074540c503010040c1e8001d8401540404d42c1a10900240014001140d0040c16001606002c0750031000c840308820380522412038039084140da82842001c4c02d82020b200811b4030511881c000616188041e00203803c9800c410300c16a1150b5000c2018000c005851041c40c01170324811007001104d900d540d031035110701c3c48018040000c5800200b90f40000d03040d5078059 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 382497850 1250 382496600 382496623
    0x1030f0f050c0d20060703090e0603033015060d0e210d1506090b0c10020a03060f0f0509060d0606050904061a121c05040f0b0c060109050903071202 65
    0x181840c441541040e41803030070500115000c13881c9401e0301001d14a8514204d4601d10783c1600c6040145182403d44440e0000041c107840d01400300301310700e210078007016000300001ca2080d12070b00301600849007405840e03040107002c646104a0103108440c41e40d105800e440c1207011140d004501701031a007100c80c2c00d1528200062920580040520300d20004072030240541e000001420040020101c2c5070020b200018030864000c0b600046040c012074400b10010000c40d07412500300e4115042c041030b104200c1c1d0280880000107640c1c1c020a00c4052401e90148005004020401c500d00b82880006800240051300042c420b9058500040c20883e42c2c0c0c0224000b00801072100c190f514060900201030500003030441141c1220441030f07003152074072101a00c0120500c50041a24030b0003031076158160031150140100b0310405200000700e1503800c000200107840207640803912201180f0656103000e0041e0004100281403034100110940000b040d101c6454100002c0c3c2c1c02c5e4002c2000a0342081a00484c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 382499100 1250 382497850 382497859
    0x150221250b04081209030726120a020901030e03091804020d05060103030206100608070210020a1116030605010e01140910150305100807030f08030a1b03050f0f01030f0f050c 76
    0x100300910003143c01a0240030900d0b000c3d10580e5881c0c4000c1c40c2c41e0310503035400038410800b180e0612800254580c0350701c5050785030000075242c04001c203294149420226850302c1c0060300082c5407140d6581c180204010340b01050011800c20800400041c4001301c0c00049185507600103000400b07543c0c5510101a800350440240c40c0d803561207040007929054100e6034004001115000002c0f032900c80c0f450244030b60525406800300344254468040070351311000c440b4080050503038041c2c01015040c403d00861100d200c06928185240d442c0881c1520416070085004480d01c4004121026001c1c1d0409a60700040320042d5039942c464402c400040016005100c40e6060028a0380d43c00c2e4055000e6805031800d0203040e04a00c3d40c4d1200180d0741c4405000007008070fa164680d200c0040c8030013001c0c580200c103580c0c0201c0c0d03070740c49042c0f91004200000b9280000035140c10a11249400000c00d0781c0d08186e40d16422002981140c64100030424500002458414a840b2038000e0000521105c0140d000091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 382500350 1250 382499100 382499123
    0x509070306050a0b07032f0706080402540f04050c03011e02130b1c05070e060703051608030109021e0a020601170304030c15022125 58
    0x144014001d14280c02203a0280314140c5010400c4102c0c0700135105059816501e03a45180804294450340d40451070f4082d08488106414841000d01444503101600c92992340610a01c2e00340100303c5140b1020708026402a564002d010a016101c00d1885140360700c0040300d50301d80600240940880301c0e4150480c4c1084882c014001d0b51801603045901880c060b030103c40d40880f001b02018204e9542c900d8180403151300b01a030307140780642500503080d1005141002c141d0240d83d0301913032500750302c1000e81488100c40300c840504220f0862280d00c0e04400036260284124a131080450300c6407041a13406000d0181c04100001080040b21701e8000a56004080b503032656920901c00029400803003102401d480c038000c0050402108809071079141c0d2481d8003d2040303904e0003005414501400341305610360b0001300004008500501c02e100000c0120f000003000c54400300314024189104559654640c00a10498200040709542030ba41207107981c1030502e81c4011030800540903611300e094010a02e15000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 382501600 1250 382500350 382500361
    0x1030f080c100510091a0604091104180905070806010305060105010809160303210203130b040c0b030f0109180308011404060305010911010206010609080a080304080c01151e0303020601090c02070509 87
    0x1420200864000407020b0000700c6c01d907480c80f0400c1a00004294100382d06203c00c10070001c50790050448503100d40e15007032506032a0180d51000c10309920f086048103032210307040b000308641008144010810140a1700b13513541584d54107601c41c40306104180c1041004000328081000034881c60500700d011042441c2c88541d2894044c2c80940e44010b080000b0310b48160f46a0302d0071150007160301c41c4103283c80d5444416296a180180001e014005480d0b241a003100030944c10701c624021401414611a0481150303d040b08140c182c40404103090007001c8504900b10009400020396815030f01e07a40700d003201140701c1c000820003c000c1980050499030806d22030703105201d0415034001020100781d081e21780f00e80c1ca9000a44241c841c520a900c907982c480ca10b0031010405642c05141c00074030828040d40341500121802e800d584070247d50b00c03000c00c101e0f81c04000e20001800440500e0708d41c0c3c10941c410510b585c40294030b03802d05101710900306440e0b100202505100b440920060300004043c180e40b030504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 382502850 1250 382501600 382501621
    0x20f19020a050607020304062a080a0e040b010c08072622050301020313030509030115081b031b0904020a0506040f081018030e010e0301020406170c0301030f080c1005 73
    0x30050580b0b80780242d00120314000e1011044030107941540c0c40366130613040008541080c407060108260900704481d5004030028600d40010304000500f90b680c003084600300c404010032a000c0740265030500c000c84c0c40e000c000601c42070a03114801c1d003101407851000d4500e088c3c4000058044161003400c50001051115800510201b1403245481300d401c080541d00c0b4010b041c204d1200740e60052000f628030280030000385c030910041c007403c0805800417404604406000d88202c200b5041042c0c2c80d00f0041080e01001036a5094107030420084001740291409091a00e4100b00202350b4940280c8000c4001015910750314200350042c840980916070340c556543c0c4842c0e40200300d000e201418020b03a50034020720f11150155441c4a1094880a541c01915030b8007072b41c16544a1680034140905c2c0618881180c1e82071010348000d10107900c85102d10080050200b41210004140c1c1c21070407014001400461540e0232124203046e031200c2003a6031480005c03c00341c40c0228190291103103e003841d0400091492 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 382504100 1250 382502850 382502863
    0x14031e090307060617031c0f0c031b0c0308061905060f030601080907030503030115030b030a0b012619030c1e110603071d220c08010506070305030703020f1902 70
    0x70790080003080d1716034880d020024500144a0081e41c400c0c00391f020040600c030300301190f946542d04c001500309640304600c401e4507a60b401040100e0f580f00c2c9200030842440754441d800078141c4c81d0000e8000590b5401425500d406004640101d1b5035161001460450302d001074054400148200c0e1120010994010164411154640061011030100b090100009030304001d681d8040040c600750381c248105a030228100a000f84101a203455040d040c03605c0c02c0c06000350305402081c1450056040518100c0701d207050180d883d110500448503c20550804203151040d085500414620701c182c6003402c454000b29580060400f040200039040c450000106040000f4840c1880034411a6644200515030004898200100d41a401a401c0e151030540f01031004003c000e0801c004040c050342005002f006880f1460300340c2d0390f1100c00c40281504440c20034014102100c005160114540d0000d11900002e02030005154000c07c0610f0303281c0141d41656008010b0b00d40030f0300341ca20002d5000b5600c28 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 382505350 1250 382504100 382504103
    0xa0905010e0a120e0d021c03030b2b020a03241d06062107060503090c0a05010c1b050d03080a0b0109080c06090406030b070c1b03020114031e090307 65
    0x601c1c141021007010004140b031240260000311501040744007003000d40b0259080060f6a51220000101c0030060f43c0f20020b4440c410030440018500001078038000e02110b40600c001440341902d00f1440b003030300454813072289400100c22240c183d004001c0c80451000c0d441c1da04010401403081441e8101d01c2c040400d40751030062011000d000d40f81000c1c81d141041142c80d1427a10f0b0f60740100c00020200c1c140303c400c1120041e40324914039a500c0f845103202e41402134541002c00003803800014801303101400c0084688600c403c846c81d0302c21618183c0040c2a0b8805440020100e980d46101d54003044c095030301c2c4500400b0040c014100c0b2030198600205a40001c44047c16120300d845242c0714170354030485240044c1d80c03084004101c03483e012000c12000f40c000c1502c00d68030546840c0e0110024a00a90071070182c14643c03100d04090140380380102015920080882c1180745c60702c3c04001507039100c0222514a022034011581d030b03855903880701074010810384201c031501100a0074400403076400030080c94007a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 382506600 1250 382505350 382505353
    0x408100c0f0813140607120b06030c2215030e010c030b030309010309080d0906060e090325030201021201080c0a0e04110f010908070e01030204050c03091b15030a0905 73
    0x880c68000c1603030401c4040505a001a00c0c50000403030505220070103001a40c0210315085184001e810080c1c0342c000110782d0140082c44042e100f8074051080e004d50030f280d0004542143c210701e400480500d55018000c0104000c091440c00b0302925040c001800b0090051b015041d961068903500c01750180c9031044151100d5840c01401402c024880d104404905000401440c5000950401100901040081035420160030444101e9004191041c005080d05c60200400e8103450641a401c52182c0100400e07105d410812103042010b0228403000c0106552281c01102d8800d5402c04a00a00a24030852001c00c0c50340300204c5c8101c00014000502d10040b50407a000d6515156410604502507500425130216008a43c82c1454242110100340c1410b1520380505561201100e107410030b80e5005004000c82e200040c020340c1094058950b001c2024012946981401c0107003c2d40c1d0500f8410640c1071011245180030107640e00780300345099a01d4100c8998990034005190b00084c10301c0d0701c04840d00d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 382507850 1250 382506600 382506611
    0x60c040e0708040c032904050a0218070903030c08070503030f09010509030f040e04060b102703110d03200106150804080a080c0405040501060509010f09081f020c03040810 75
    0x70301d00c03910000340301e254050380e00100c1070f00c2c641d250a180b0096094070b924459280b400040300d407005031026403149000e00c0003003035900b0450060103941e00c02420400715814242040210140d0460191401c407a8985041c140246e0641410b08484c000d1440007460740c000042804400c0f0080b41c8020f01600d4408003c00c43c0c0e49031504100c0d500c0c891801160032840301030204010b00141e007200c0386da016003d5803000c128205001c001440505102c1c80b504007151010b1090191803040311101046400440d4456080d5400c47d114090001d500d1a0346900ca140c6072080d040825118901c4c216030903001043c182c078030180020025029049038000d00c1e03229842d00f0b610200d864402c1c015a800307a034020080c64507041041c00105c0301c3c44030081c00d007142d40000300000a02e51f100e500c2042d0081040c0e60314075844000800004000c8400003000d84104500c441003401405400301b40c0b0000c00100c00d0840c0340301801c1e01021000707402420808401400089400070300703041d0210750003e82c640c465400300007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 382509100 1250 382507850 382507861
    0x2009010c11240306030d0806100e0a09110403060501052b0312050106110f0703081b010b03070902091306080601141c03051210080307031419110106050f10030b12060c040e 75
    0x8118070300312601e81e40629100180c4043c28020311040f03000c14000b82110bd80940c8800050f419102450101c450400700001d0820901102d0701c20540500341c00c4414034410310700c21800750100d6540c050305c4141c045000507000c01f09030041c0741c504802c151000c0306000720360f1f451a021344085030b81d1640e980715014022202c002e00001048a0054035402142c5a00f02144140c015070b418007210401a215980e030f401e030259079601000080001e0031100c0025030340740bc0700710900003404180482030b100c16060000c01e00c40008040794036819204400103031021004004001340c0e20a600007a40c1a03030a00e90119070050540c04070041102060141010090b0346502c1c1c40360449401d248540600e80d0800c1c440200044c1c4140401c90344a083e1498441c1404851103612608819098255010881c00840451429000c6c0540d00081200f1245500c00781286000300d000301c40035094030030415959411010995840c45a80c00e4054200c4013104c0f101e2500401e6034015038414016444509a007600254 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 382510350 1250 382509100 382509107
    0x1d0304090e0a150c0c05030409020306010e03010911011206031406091606230c010e06040c1a1b1207121205070507120219062009010c11240306030d 65
    0x302c640d03a10807101c0c803442001c0755a840051500705007a00c20010341c1d0500c140400c0c000c0000c0c101505d030420005076a400c02c18009403c5000420340f850081c2d040c4480d90000c43c4458000d159088001c5c288030000ca8500c48086c1c0040109400042c00718a101c0a4240c41c1070001600c0ca12440710301044030050919050880075080e0b480c440c440000c0c0d444024552a40c1240034613070a0140c0c140d03c0d07681025107403003c40382500c034111450201e9a1015042009100303204c03007072000031b20000e60b020340f40c480302045000c00c601c00c1d54454080058415480c410050f010000010700c3c2c98400c1030b039500d440d6245014809a420326500700b00144061444280c2c2d0704240c0724150184c2041d0b02c40510307043e50340c5d44940d1508840d69852080d03010b041e054102d01d048000b01d54545a03c51080000c01c01c3d103101303206940107000c911400c80941c0900c1103100d1741c0d800000d911403030f07a000390300c288024100c000000c880e000941d800051052480b40f44103038071000403010390700840c0220142d0b501401c1c0541f084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 382511600 1250 382510350 382510363
    0xa0b071a0711070b0c1204080604030f0929040e0705030f0f06010905040f0f051017071208130503011805060601030b1309211e09051809011d0304090e 66
    0x2054250483c0d2400c01c804240d8a00070058000307200c041d03443c0012030b6116508290843c1d40705e0030081d08024204010168040d10f2400c0413885408c00b82065424450b0f00c0e03020a11218a9920f028091001c59130b0052000e003d0714014096018200241d10748010001d183c0c0d0801d8803440c0f110f0341800e010400b1164603610f190300c20f00c01030f95a804000c1c82c103010880a0140c07d14010036640d070f03031070360301e0b10b407074814003c0307510481c95840056002450000c038007001c95542102c000350364002440500000340c0c4031205d010250b40040f81c40761200c0c00b0300c00c102c8034200d95600c150790540c03038844880c00100340090b052100601500565119584020055080e92407091409501c40816039004010207501e07800391840310f0185030034200803001061a141848107003008000402d480744c4480940301040035045400540500d05020050326240119a4850041c8491001e081841e00000c01c120380962024030051821140b20541d4403400b400b5581f20f0b4007030702600642c03a0401002c1d258249002400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 382512850 1250 382511600 382511627
    0xb07020906060304020415060509030d02030301030c2702040608062b0213200310050a0b04090504081611031213030602090a12080a1e08150a0b071a07 66
    0x2080c0c255485070108122548010b004a0b031080d6500175114080002203120005030680343c43d03ca65410703005040602d401c0c500140c01c01158410001480008c0118040e881151081410460190389001c49041610b40f14000c0e00041c038400b090000b16154040740b12400380006440c81409100780c03620315803981d550000030005d04c40f0070200703840044c01c141c0310340340b4a40030060b000a03076800501e981065100b410407440d002c0040c08000d0268811424100d44000c0000b00ca81e55071440c03501f468010140242c1c4100481e0070341d00d0300007509000c059811184001004c1d801c1c54220002c2d80f40003060050702c0d041c80c0d4004c0c440e101c20540c8554010040791840707600e0314080740d07130035281d035550344007943c0440d0410307401034005a000a109840700c0040000f03e842010304035101e80c10100010000c0e84840c03448408c00114500c1c440c429500681c0207600000308070381441c40c3d046000e0100b403c03801d284e230011150940000e162018040e015510782083d0b1140d01c4400b0b49034442040031656030500244 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 382514100 1250 382512850 382512859
    0x40302031e040b0c16120b070f0e040e06040c17070504020c010b03011d15070c15060509190e21160b0103060209040b030105090d0c030e060307020f070b0702 69
    0x1084605004120600e40d0040072662440d281c1602e62005690030f030801030200000713074048444500e035102c003000c602c400707044082d01c0003000c0782d00b549a0300c20081020f4208418040ca040c56050b46900c114041c45903803030702034020b0201c41c080c0d800c51982e0324412901074549800c4040c0110f420f0707803090910320100400b035000303103041404c0808000c0250700840291800d50359800030888982c44c2030080740507801c210b640d000d800e00810701403d030400c0010764132140781100c0071007048801a0031181502c805600079181d8003420011011403401040150002076018a001081100351010740031000c8500c1941c41040c000e081e0b4000c021541da10044840814050707105004130100e0a42d40060300880ca5210b0700c800300c404007074840040002c000e07001962340e65000280030080303050078019840c494500341d0080245180c2610140d4a4590110141080012034501041458414941e11604a030002d041e290b03642040c0c00060b5440f1869038444e0441c0c059008002170160b210402e680c0c41540150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 382515350 1250 382514100 382514107
    0x203010506012c03071701020703094a0411030d14071415190b010512060411270a06050f0301030318030f0506061903110409020409121d0904030203 65
    0x35800144038444030f0030f040d003601c03980d00c2c0085ea428640114031000b404903400142c5c4c035801d83c01e0041c4220516001298800001c90740305c0c00c0001c4241c417403102101c0d41c9210040645000788048443c12000003c4150344000f03405100922403005080011164210200d8500fa04002030948032810300d5030340001900003e020000120b20b680007140a0341d003815090700c0c0e81942c0c5611305085482e0a0b6480d004400710004194003091451044140411007401d1503030138403a03002d9034075140b1040205014011074441d074842c0c00002c01d01c0c0a80b61a0400501c0c2c408040e10301d03481905601c45103c1c9003074401c80400c440011a24040c2049401408081075140e15580c01c40d10281e0305903c410b1500000208a040004040f4024a4011340701c0c9106602a00c080e04200d410440802d03004c984890010301c00e641c00f000014a894481500c1c41416200440c1d4041180005402050101006801036082d584001503055112040e00901c0311415581d980303460700700c4244220703c00103c0b00100581d0040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 382516600 1250 382515350 382515407
    0x207060806030712120e0d211b0210120f090c0902251113020a020606220b032104080f161e0902180102010e0307030923030a080304020301050601 64
    0x103c0703110088461504040311042c1a11012a000387e030000026180f200b000c0c8403d1011058012403203880700c1081c031701146034450031002d80f40d800718400c800910610042500038421401544408003403030b8070a100300040256032101001070b0101180442d00c941c05180081855900b9209070303641440c0f0344621a00d09513003031032691038a100c450382c15100c0722590000c1c0034507940c0302003440e800305881401c0561144000300019281a00107405540b0034503550200907001280c12513442a4200180b102096883d0b115000c44c1c1005800511101106085c90800000b13600b014004d0007101c51090481d4494500381ca8070315117404180e4030403010340e00311000421049914507081040344500d6090801805c2d1f440c10000226030041291301c014500059500545607020300c40d6440040d400b1001d50324042ca103940062500881b0b01030f000d14023142000c0c02252404070300001106210140880d40704001d5802c108155410488081b0302c01d43c20200011542e5116180304045240c111101ca0000c4589 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 382517850 1250 382516600 382516613
    0x7080a0f0f08030a0902190303051c180309080609010614060304080d05040510060b1c02160c0602330406050a0b04150602060106090f21060207030207060806030712 72
    0x246901903940d084615404008603200d00021801402d0184d400a000c800341e1042c000344441e540b00819504100d9401080841d80100843d01c0b5004004610744001c0c682440b501d000f0300c90400c4040240842d031040c941010b401058600c113490819084030b503a507507004585030a807000c6009405d41004144c54824540c01c02c400a103400910880a131401d00d4215505d410444004032001c0d0307440c0c0d01174070340d02084001c0d03031003040041d22402546510f00265950619030041d24030f4000310000d5800201210340942031041c81001c280d100c00400d124070307510316000756a15034003407100d08404001007000d805001c03200c90504502c140001120788543d51030707c40ea0001c001c024110140f0341c2d00c81d62941101e07070300d52150b4401183d003044458807190078408004c0c81c00c68141c2050060204260080c40861029107105007121000c8044000030342c01548a0152004006070051200d03001080c8003080607000300741d280070780d0401c3c2d079180550303521070040642c1d44d0b10394441c0c80b403004036018200011601 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 382519100 1250 382517850 382517873
    0x10f03030513050d0b0f060307050607081e0f040e010501030606021b060f1201031211100e0a0b01060206060405060109050607061d061008011425121d07050307080a 72
    0x300d42e03107000d4103103a40b08041030318101c1e01c013011280300d8210070400c10803821040403642c004e2020b5000b800020304120208540c0d128180000c2c09940c9d0100d0b560492004030224071901039803031041c01d500d45103002080c40702600075000e900e9140e80e032000040382c1944244110700c1122416801441c10a40c800d051480c2411000c0110f5000780e420082000038807942002070192840709071021a01e03600d941031840300a80d4400f00c03042000301421860319440c2c4d001500b80240c0300940d00000c2d40c8c41035040036526285405000500300252480005030380307500801c1c507910540003682e00b400f00e41d54200046401d85074901605078012000e00c030050205100781d00015486c400c803416051010b56004203130749060401c460484002051490600004c40280103100001803030800b0040582050010107070060130381e2090140d0b0220a4207005200c82c444d008030803040e5000c2004000003030681500d1050030103003001c1000544656500025141000078911085039002c001402c080c04055803800c10000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 382520350 1250 382519100 382519117
    0xf01082806060504110909090105060109030b07022406031504020a060f1110050601020709020c03040e06040f0905061f030515060d0c081e0c130e0f0a0f0515010f030305 74
    0x42d5104400b06060b22207215084011004c170348406c2d00d8560641c100409150020400807480c0d0412041c041d450f60012680c00070b5942c054081e0585580341c1d60103c2c50003442c07082e0011808401043d1141195608103007500070341b800d070161820f0082c10450400a20020b4030000c0d08035190000400c60706100701c034801c0707110810740380803969100645c02017880c0003c811045184241d0702c030140412507030108821030090612090660429100c101724079244c0c02240f0841c0c175104408000100550b607a60312568900c407150707034100000c541d1410203640c1c5000889500000242d00300424000724078010703100084903800310050825034403842c5507081090000e040150044844098580000c900344000c4014014600c01005165602002c44c0d802a2481c0c10b21440d58201c03656041c1981c0700e011030100040d0040b5404100a255400518689070724000344521b00e00591071035a0070043c0591020340864011030440782c0750b958100200001110070b00c0b078150071003030907001000001d0040000d01544c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 382521600 1250 382520350 382520363
    0x9051308180d050607180305070b161505010602010c05071127071809021801030b01092c1503061b0d05011e080607120515030f03030f010828 62
    0x404181001c207180b804000c00446640c1c1201c001c0000903544500105c90140c02c001c2e1050441d442d58480c1754030340a550141511500c400201003034134802d0b0130300c40700c0040d81c170826170100c0c7c1c4682a0034100415007030003144015400e01c42c0c820f101034420819603205541140d003d480307a96461040100c10411118141a00490002540d14090f503c5100502c04c0ea1aa210000445211303c1034200d0040c490308071800c0c00d172040c8400c444e2500c1040305218100c01c20300300003420741c1c0a400141d0700b00d0440d620074003183d0a04007040d403016410903e0718ac0c0804100c2c0c190b00c1c95845250120059025140328260980d002000050048162750248a00561241812890a0350311418002035030001d810040040381003001ea1845400c4c00c60600b0010040880a45054180781c3c0000b020403603001a464140f90b00c0d200400d05040282c0d0210790010350060440f482c0b40558100c05859800485d4060401403042c00002080720000c10552542e900c41c0809618030451324002600c24500e0b070f030059410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 382522850 1250 382521600 382521637
    0x6150310080a03020a060b1c03030b01020c03070b040620060c030c16030914012d1103030a090309080c010c0303020a03140921040b0405120f07140a09051308 69
    0x7250014003030300c40701d1030103035000d081e0540d21400c181055850202c8598020003d41a01c204110400c0300c0c48110700b5403500d0041489446500100d1034094031240c201c2c0d0500401800107403280c46c090041040340d8240e294016669210a003083c200e07802e66002640b16041040040d00265400e8010b5500503807030080c560808a40b0340d03040000103441c1c80100c02150480f40c0600c10103414038058000101d091802003980350139050420100320004031069000701c400703429040483d0140e1980030440c4440400c0340d0316481d084500300c01605c609041500030801500000c584a000410342d41445401a15800090314041c2e800f20700a610500100003099509d003d00d840c0c00d280c50b500f03203000e124014003c010b940e00e1101c40c0034000504044002c044101004204044c11400094030202d40c07049442c4100d15400210041c01e10111070100060f602608002081095040303080c1e00c002d0b081a280200f40640b2103400c942103810948400304006078203404c6c1400a800c8000a145103c0b035074501240d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 382524100 1250 382522850 382522859
    0x16090f0e190f140a0b030c01030c05041a09041d0d1404031b03020102010c020d08010e07020703080d0c0e01031a040b0f0310090209101a0f0909010b0a12020306150310 73
    0x310342d410710490400980b200c40400c42040c5030200320380c1104400030200f111040f0500025610814500482c1c10b2580b518120642c071401002035900507c0c105030305441c0c840c1c898030103018a501a0b0f1490380300310318260b0305000c00c2440540b071440514001c402400a03120100342594003880310507001450036002c00010001405d4043d6444d005183d00c00c10300b2002d81184006400d5511041075141150b1101d5404d40340d650703101c0640360454904100c041d080b45c690075022420580541c1025048000004a45003040c40c80e40c00200f118840d07580d40703011041c0785001142903d85044050860788600840d42000d49001d0f07100b40e4810100070041e0180c0e4000030003007400c0541000c085066642d17504030000c198100401481d0f44070610251221089040070f1100c00c00303035009001c00494000116010b501c1810b03103000c0b00c045400050001c24250703503520302c03c0c0095001d411414001500010381652252a07402928042c680041c036801086540010f40f11458000602c0720540c0034071004000f4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 382525350 1250 382524100 382524151
    0x4051b0a14070c0305012c030423030d0206071101061d0618090d0e0f060f0a09031e120f05091c0f08031006020303010509060409050f070603020316090f0e 68
    0xc0203611850020403002441040f1165030441c2c01000700981510007c080d11440000c0112420f03207800c1040c80c0c82010780d90103903003400041509442d40502c55010403c071450340000d846440342c8015a21500c0288050b44540d080e24020700c03800c1c42c80d961080c0c03400c10324a41c82000c2980400043e01d080a503605070549801443c20a0754042e40503040120402c060035445100117803d1b01c802e82d21420140e25900c081102842034000368542d4400115520400602c201c0f4802d0086411014aa01061a90f070b284010100032050031100000c51100c00c200c6107004164000c11414151203e50500c02540144070038000c0f02c443c882a2000410300c810f002444038003880300443e0144074019200d14001140d0b0714000d4a03504030301c0a644c0305100410a503a100e00302c00c0c6e0300102c142c60120b80c007100c0b4500a85071003192100c080180c0a154004101a50705602561043c650715515001d200003001c002e44401000b80901012280840b1050200b4032810400580203904441001e40852600c2c6584 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 382526600 1250 382525350 382525373
    0xa060c080705011a0a08011a01140418051e090a0b09030403060e01050601030c0809030304060b0d241503081207021e150601080c0913110c010b04051b0a1407 69
    0x500c44040744c190551001c1c100850010041c269140c000c01c203450040342c055800d184290145810804684151038100c640344095030014440e80d80b030f800c5a41000700000780070381811a00350080c2c40d192450b072195203002030710260060318030401a040d6070308607848481070018001c2c806913161108110000002d80b4900c0780341c0c0c03142c080070000145824204001001d40c2e01c4944078008106018040c41110100441141d4010b540480e0010b408500e03c1c000c52564880740c04050301c1d05011840741c030390001e01c40340341c000348801c0050100601c204107041100f003484280400b51881d20107000701411000381d072403c00d41011940c0100e074141d20115244990f0300d200d401d202d1a8507003018050b0348501e04100000e503000502400c041e0340c02d1820703400c466194014039800c50b01c5010144500d60444c1080c0e07000d60003c041c10783c00b40d0f50307500c6526079081c06020174080f00340c0110304d403900150071580041d1015a13041c00144d0310310303c0d00b102040100c8120303481c0b00021105c4601002104001001403c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 382527850 1250 382526600 382526621
    0x70e0111070801051005010305100905070e04020d02090108010b0f07061a0307030507151713240b0306160806090a060510090303020c0307050f04090602160602070512090a060c08070501 81
    0x8901417902d51140b0590921540c09141810300b0102400440c5003c0c800017001e960242800140582d10300c00c04035100c1c2d60070340e05540c2151000445440740c490540080440c11802e0b01d0340381c0c0990340c0303140d095402d02c0782c0260400e0039541800894001a55074100150600081a480240241e810700103030a10985503c1250658000c0d9020014042c2c0656080400005410b000c0400741c44800c0f1004010070040844043c0194920008108111050507114202c5c5410f12001c2214000758070078001c03d41344010600ca88103650000390001c0802c10300c024001d103184c5d1480d0031510351004bc400104409088040000d844440c0440c0703584a00101c40340501c49603803950299481c5041c0603040c60030329000c59000c1c1e00403403402d004648403108508030450040d6800604070000d0300303143e8000e0040e40c0d2200030070703004d10400074184903050300504031081c010800c0d0389030407440410000042c4611240c0d01c0d0014008401004914010301500c100d00d401082510302d40a4242c1d50300f030860f40d101c0c56 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 382529100 1250 382527850 382527853
    0x3020a0b070203120c060103030e03010923100b030309190905150a06030e0604120e0316080d080403090e07030e03030412020c01090b031b040b04090b01032003070e01110708 76
    0x418100b549003c11000101c402d545051030b240c000c4502081b504c8010500000d0103100340c403007402003e0340707096000b40c5040da004040900282100c09000a2099000c040b803c03861240550204005810b0710802e9030910005000b145031880401c240540b218140540442c00b84821000181aa0480c0200c900ca092611403600000070071070100144204580c00c0982058608220003029030000203845401c01e4112144808035800340000700d0f2140d40c84504d45425025400103956240c80c10504039042d18481c105403015070217038500807078040340111000380010b00316003400c2052403a001d141b03a03003025040c640442c00c4081c521038145184e1042d5001c81d08841d401044400d01a4180300b140001705091034104c1c0218646610304245000140803413081603048444a900707a0b185504940061102d140419121a0b85080c00c000520204d00303c44d02090428480c03c44003a01000100c8050b01c9500205081d500c3c2d080c800c40f482032451000a0502440d02641c1c1540d403400c002c18002090104c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 382530350 1250 382529100 382529107
    0x203090d030203040e1303080c18010806130e070306140609130201230711011d060903070e0c040e070212040b0c0a06050901060305010b030109032007031a150f1e060403020a0b 77
    0x10b00223100c500c004050380f0041205226403556482c403440400e00381c410034a0b1000150f11010002440b01011032030f25691149405201d20141d00e01040300c1e801c4038051681000b1070803501c02d800c120440c00f212210b51210142001560484555850720000d50062415402c041c7d014969154542c0c1070030344e0200704c1d4002103a2041001130909041c506028280b921800c5042800e440c0c0c09424402403006202e26004540c00056440030021794004022a210010703140c01d0820f8803070020f500070b00615000c00400c0d400109128000990603807030701584014189014544484140c5c41c3d0880484105140511801000030800c0360048034010122280001b03503940c03441c90201d00319911850001d010364100034255011a03003051141840c2c405008601850819803940141080c40c1504021b04402c1d00000d16500324a5060f50039101d2031400742d07a5518103041d0b20420200b45070454020340e02c200507148142080003004540703026010041d091600f001e071640c0c0054512803c41c4c0100c41c0d99180803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 382531600 1250 382530350 382530353
    0x30b10090c02071404020d090c0b03160201060602030a0807050c010527010b1e060f03130b01050913170c0a110102150919140d0903020a06050a0203090d030203040e13 73
    0x41c400d11414030300c00d0004003491440d04101d42c0101c00041c0c292845a42d0124042292102c103401c03031034141d80d1010390700104549407001c01c4010703003054510002400400015004060051080e41e0a89200d0780086040003060101100c00080080401381042010310410120600c2401a03601841d0244400200050002d1074800c80c0407001c0450100b40c1c0c10710101190b227071583c000204008030048a41301c0111340c8400840c0c2107205012440c0c1120000004202607950380d0380220070400c1c424a03071510580d81e640200501c2d0032041e1068003080381c1c1e815200340002c4c0d0000501d50009071040080f400e000c1c40c0000e0904000d800d071400e0751420f807412010f419a603030501880038800400d0a103046142844080036540705804141107c0c0310300b460304174000380421400c2d05500b03514440c1c1121410400040018240d042078403080703004414596000c201e29000340c0c00c0d510790324002e40c025410000302d07000304499184030300015010750004001c04112a500102113900c95941034010b00081046c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 382532850 1250 382531600 382531619
    0xf0703091b0303020d090e0402040b06070506040c1d010509160306080d02010e061303143a0509190f020f0301020705030307020f01090809190806090f0609030a1e0306030b10 76
    0x90710f105c0d04010b41804180010b040404280d504982c0503180000c60b00c58480c0818003511405a01078154460760701001300308540300b007460003a203080e0750901c66a56a60707175402034258028080c00d40d100c1c803030300000340c01c800c01d20160840c3c2440c41d1402244050781e44590604101d1140e4400005075100d01e031141300d014007005072541021207142c5103547c80741c3c01d440041103070482401d00c0600a4001030b004011104542103110307988210b400201d440040329458070801c1c91980b85001e1290f0808000543c800c50104003000f800b213041041a040c2c07502c90b60381c000d00039442c6004036804408401a0461614244081c200d4240326000840c2c0d80d0070400d00280c0f42c4a08404500a0743c0c1c14404024000b605600903501c03d43c105035010045401514a80c00c481041d50b088010103100d0002000b8604074000381224400541c08241d5503d9190b40805945074800d0000c40780c0410040c4040340fa0120503125015205c030350610707002805540b65a43d650080006403900c05d04902510801e01c4405c80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 382534100 1250 382532850 382532863
    0x501090c0306080a21170a02040303030e07060917100e0c1816050d0b03010e07060e190510050706050403020106031a070f052208010c0311040b030f0703091b030302 72
    0x11407000405910344c043e03445003140f03006010000007090022900075002401641480c1038000d11145e000440d2030503851520013500326201c1940068100001201841c4010466101780c47d40c50750b850b02d000e030030704004604024010803042c07564494541940100c83c00d40c442d0012178040d0301701610b00c0c91864410080b1082c9000d05841c0503855a0702403004074109030b034050007011400d04040c1c2c0c071003485051010043c445441003d8240d42481015498104081118803c1d01d001e501c454401803035010034059141302038101240751f083c00002c180300915100d00b4103070003204103141c520300d003864640e607481c00c0d1481a18101c0141c0c2d156a824420010400c454484d441640c140306c004520701f0550091104002180c48000c0c044001601c5260101491101d000039410319030811400b0b6031120618000c140400f0110002403400b5051004c80601ca4200d50481d01c030b06c503c2c2419502e0340c03690700844c03000c007410000130700d070b5035160204c00910f40400440401c00000071003a805840c604020b410180d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 382535350 1250 382534100 382534109
    0xc03090415080d3603020d1a07051c02070206040302060f03190509060403081008030a020309032b030525050a080f06031f2c0708160501050d0f0501090c0306 69
    0x5180d8030b6040c08601646220041e0a031071030502c541d0b0406184c01c4a07082190703904040e4101c1c94a100e40f00c2070002c2c21300b075000c0701341c9003098010b07080e0784c0c1000031120b5010b07080b0740396980741009815203900030b03451b0007034040f0074002840365151a0b5a9400184168451110710410800c04410421703081c014002c09500700c42c0e5001c040c844c03403030001c0702c481d10b4000081000b400d00419001041e40300700381035142d10180c4000c60480340d841d224002c029540c0d401003041d240c0300348103251658844a050104c2d0045840720340010102940b0100720a0740540b00081020403002d02e00c00f0400030f500c0c031070900300d000c1c1811070b141e1070b940300082071004152410060601801794052001d200f05514002400d244c0324159a01c988484140e044d21140a010006803200601d148a001c9008040300d00c0301ca104a00c0101c412904180d40c1c0703600c003984520182400c140d032050069000c02065001e0710092003d084100300019601c103803046210100c410a8001542c11555000f201d034030a41c01d0f104550252 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 382536600 1250 382535350 382535357
    0x100905010b0a050f0c01061502011d1c0807020c060d0509010c110319020307050703030906120c0509060d1b030b0406090b06030114130515130b0102060601050c03090415080d 76
    0x41408000d072140c480d13110701c0c501d03010300080c044000c10020362061026006c03001001d11170302054080240a4100846410f404002e04050403021001c0083e24007000250040881010b2607400816182814000c101c10f0960245503040340d5641c0e5041c0082401040f00b14000902e8113200034601c1c00c5426020a20381800401081035030494800800c0d181c0305040d21300c810700000d000c0c000032404d500448200601d20b1040e290f010003015084000c120540382d0030340d81c0354a201c2040207040e0588440040c1e03840460b5042207074502600b055001808a81da40b408045040041c10088412018512400d140029a030341c0c04000d61707140600030030004200c003140511880e40964000f900710710042c13003000d4800c0f4203034600c1415900e84a40744602101d0043e000c210303d113025520300ba41c181e0101304851040013108210b008c41c030414070a01c1140e02041c1d004094a6443c040107507800d50040514042910091002003119500c50060303450015140e5101c003281491f00344890f1034485850071007420b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 382537850 1250 382536600 382536607
    0x30b0403090911161e021302070b1308041a090d1505060109050a090b040e0304170610030308070804060204090606091d07021005060d201e0105040306050901020f03100905010b 77
    0x2000c0c140b002e0303070304e406400912140d00c00c81103a890500c170380d0001e100250051a101d1940e407111742070b0b50141c5000c40c00307044050340c40d036114090030040d40000400104218400e21050054082c2c0390a11006000d4088007145002e03640800a2200d0704480012209030080d9550050019900e02549030070030702c00c2c00c0003c4a10706001c0000c02c0c0c0d400e1802401251940c408a81c0890390307860300001c55240d15401926503943c0c41d059589a45420240384480340c1c071911003c0351000204400da2011250180d4810103241c5034468216411b8030050001c1d81c40361380030f00010510149034450f0000070030060320303000e40040c1b0b0b160050003260310441071a5603000c41a02045101034021038982c840c02c0703039514001a60342e12540059022241c903030f0060b010320500165241810000f01103800b00c62012501c030960130074028040361b0340a03502c0d031055000901c103210800c001220b030341001c1e410000d540000b40c2421042560b050154204460100c680035070b100c010000b02400e486010f0152a200c0005441e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 382539100 1250 382537850 382537867
    0x30304050a1a0d021b06060a030215030603280b1b310609060e15041a040e090309121204050d0f022805010207080a0609020a030b0403090911 62
    0x610310114815004280c0c50b01d516074190344500c800b00c8904050408086465003107104090036032448490060460b8410400494140d1030f260300105c04495000380b100005036940644003106402c060003558145c0320f9a0724100c600070300940f0300440080b08440350103c5541d1070030224030114000e031170011901450518070054031000d01c100e8180e4459001c403030001c0040000300307a9440c03078441c40003001500c0b49030000c51001c3d404420f02c1c0450780c0698401c50030290020400c5001440340b507a20030301e000c04000400080c4508584200300d0090902c03c0b07400d1944d581c05010070b5a0b0b049509103481d40001070080141e103012132406034203a00301802032800350141c10012400d8412801a5486000300c000034408001b8580b4030320b40d0256002d090a0142915a90128a0040c003829100036026204001060301e5200158660480d074500c0c00038544007016884490003028051000c0e40c010511000c0800413030020346008c0d00540c80ba5643d400c03102e25045003542150f0f4488401140520200036251 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 382540350 1250 382539100 382539109
    0x20d0605151801030b06060f041409160801031b0b0c0a031803050a24021201090c031109040207060e0a080c0105371e0b030106081501230411030604060503030405 71
    0xa0641798003564507a4540c80c2c041c0080d450740030780c0400706c5002d0300010340498000c00c6500003055201080d200541d0b075032501d9400040c00c408060042000030094801040440d0000001801e50091003d94002180d11451070500075448191032007415800407500004044c1d0104402c2d403880b044070007481401e811030b615503448608210002d045100071580384030018800d01c4554403a500a030b4030440da600518803005546520074410070389500e24241207020054001d001d400e258401c20480246426041400c002c02074000440c242c441c2e41d80c95a04100100301080402c40c1603005034402c0307440358003078028035082d6a00207204c48070260190040d00240b01c006e810110380c4220301420801640d001001c1000201a040d0a10340b0341c50450120511102003584810500030781540280180368640702c0055480548413480801c3c601040c2c010007001890715082c0052902c41c2c0441110003010070005020f84000721000904102c0c00814040c1c2d515040c841c1a00a00c2c0540146081c68540400034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 382541600 1250 382540350 382540399
    0x15060d020a0201180501140a0c0f0c0602090301051e060a030c05010309210c050111040806010513090501020a09081501050609010309050a35270d020d060515 69
    0x1801458000c204503001d18000c3d000b010300c80704854040d1020710303803d09042e8043c0c40c82d8034252080b8000e98001c29400f02140c007804136006087d44901030300720b199041c21154034402d500260341c165800d01c40c541d4207030303003e00429005d81101d50401c40403007403ea04440c0f03c3c45024100c0e52184402450800001d07029481c00801c8881c01d08001420704950b003400c15010840d0440355084008141e80071075115007040c580380b1010302900080085000400c1114018800d90082c2c40c41f991009004001c2c0c1d242041010694041c00721020031521120f42e00d40382a81c104000716000b06803211014000690108a100e425070140818100e0035450a40881c6080c4141c41d80b00c2e04250310351700d40c0400c2c00400c0007012045540720381d0a00c100b412100c00720b4444001e00e080c2d4911281e120304000d0807039030050280c902042807518914452a100c91810352464000c0d8583c0341c1002147e4814000340c0d840391118000c1d280515408103040c50064038450700307a5005030143c1d2203124482d02003a00b1000d0f18580 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 382542850 1250 382541600 382541617
    0x2090a09230612060108030c0d09080636030a11060714030c070203070e0f06180a0c1403091b03070608040f050c1203070506252304090605091506 64
    0x1064040d071140b001185114900e4070710031195106210001a0481000000300108404001070b40c81e043d02c4040d0481e102c81591140282c2030340700002103000c00c1c80300b41120740505450035a8403015071079441002211240080b80300410781022034081440713501300c82e003002e19220610142841c1d103040940500308125094401d0054180440000d464002140488512035001000c03113403441d40d1021340d604a41c900300d030348072940c888090104286041c0b0f40790f8580f42100e0001078040340d60750007030628000d0110445090030401e103140c401d100000da0310003c5000e0f00303110000c0e18030b8604d07802c415a03907484170740c01c0103021354003400041100c1a4002c2e100d94200781d0110701e0034180340e10350070880e280850303d20300903502000540010a001070b001000b0103c06100b14140c4140e40d84210b500d003071014140c0c0030040080d2094203181c5100384a05d910700f0030351110500c05007099802201032a07160304590040b190a582d2850f09010f01d207040000e0507803004e507081081c40f141c6034480119402d8010800c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 382544100 1250 382542850 382542911
    0x50c1507020708010906061404110304200405041b080f0309010521010608040b0901060b1614030d0e0709090507060f0c02130b011b03050a1805040504030302090a09 72
    0x4500e6480c400d0200c0d20040841e41e00920a68120341010402041c0500c42d029504020342200940c81c10940210b9086038101c0851074150f649580380d0f031136000702d409107200c1e00c003200000040403583d0314483c2900941c05000c0650000a40000e038885116490300420460f42c01007004080d0402d0000444031070805c2860301507220031003010b0f004030402840204120820b40a400071070001e80c0000503510490052801400c1902c40b920740c0f5003261554041d60756444010081800f10001c3e80669004d01c42c072030b04010340f50038141088281941c000000c5004000e40300c01d40c0000d88102004188041d00c2c0c0c1480800680038651b980f0781e42c0d040355114030000c0c400ca403510040114041c80b0015492a001344c61020400140a0a00c0c0200b10a20003140803070080c0d1030352141c50344842004980c903175064032042e140441c40c0c8000d0f58680d448610161810b2071011000c10302d611235002e140e000d24400c0c1c80160b20f43ca0300c4001c21000c04410b8010003005842c0c9081040c41c81d803500c10344a02d0074810f80 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 382545350 1250 382544100 382544143
    0x906100b0702150a030e240109180f030e0a0e0606030703050403170a0b0913020f06131e03020114120c0a030f02070b060109120f06020d24060f050c 65
    0x2c0800c1c0841241c120303100c440600819030703002c0144c1580100314804100c40c10390304000400c1c2c1442c601c07c0d1040b00050011210600180b04210450b4040ca08211103100740350119140360f5180e050300703a074a400440010f0000403030b800d120b08100d401d0303030301506000a24403a24580034000c5805404001c01c517608054a1300082400d02d401003541540c0807a543c08444070f42c2c900803000e10003138969046201d024010a0000850f070300c1280e2a01250b00f58024020702c0c1f0101d0a40410046d60840f4920307449142603c3e0b0001403005121003000c003090031241c1d2085405295000140409012880c46091401700304203c050758444038008552080e003c218858030750000b11002c4008000004440e40d80f544009200d40a200102c900644101310903a41e0240c3d030380d10780655901c0304080d4030700140841c0d80d00c201a40052000d40140010700c58903440080d44103050002030010401080b10407a41c0d50301072500303110055200e032215621400341d0400e80d1a00c40d404500307a940380032014488181d000082c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 382546600 1250 382545350 382545353
    0x7050f090a1805030a120204061e030e15061806031009050c10081807120201080624030a060909030504151403010f29041a090402120402090906100b07 66
    0x2507020459080a010440c6900c0003185401c13079885e0f200e000c01e50040f4a0b13401503450100000c1c021201030b94210380c0c841454124090380400b041c040300c00c4d400705060303c2c0c2c842c03045032620400c1884017020711505d6107483c03800e00780b05001407074481100e010302050b00e040401020b5100002c1407045071010310800101c00b00103084c828106008685007940c060300041c0c1c01007020798446203481c0195090800300342400e00300995656540798500c201e441002602c44e00c10007541c0115487e592000000d40003102514039100524002c0300b080142c2072101c000401400800300d0700303208081c0684400360701081811525140034206001d944115060400c4241400c8001485410425024284070000549a5844881141320b414080c0280d80e81d0400b01245280380322000b81c8161081110241342500e02410001408050351112400040710708080240f40e4013622030744020718200c40f0200807503600f81030034410480101e0024041c803c00d64000c0042c041c0f00580f0420800441d0200d0200d50b40d1844503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 382547850 1250 382546600 382546621
    0x30f0a03060b071e15230a09052a13061509030b04151d0304050319120509030307050d020312062d03010b04061e2301051e1809010807050f09 62
    0x10300401d11402e1b06210070768100d42d0035451103144014413090060031507540d695141e8200c2c0e46005004c3c00d147d024034101a10361034143d002061100c003140b40c505404131460049034000b581074040030052a562181040300380e030594084965100305241c2003102e6031542d10783e000f806c040544050035902034000c80c01c0c80c00080703a01180702c4807101088006414074581c01e40c2d0b1240c2040c441c16000c0d0255442c40c29411b82e8000207503034150790010036018044c0000d141140ca64115103e802d4042c8804c00c06680450420442f00a000c040da50040d59142200c2940e582d20740c801802c020b00070300312150444524281c4148070000200150104035804030701c034001038054290070855941040c540100480c11944150012042245451540344525038400e41104624500c1078003264105d88802545000c1d03101d140103010318030b418a07452040c0106110b000009030301c01c1c51a218041755401c0da144440c140350b15024010401d02003c1c240c420719141c080703900c0d140f12f0343d0054403440e480d80028981454 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 382549100 1250 382547850 382547873
    0x30b0d0204050a0501081e06150a120f0615080316031404140306060d05030d18080a0f08180d0804020406120b0106030b09070906050c0f030f0a03060b071e 68
    0x3002007040c045418031100090050900f0f00841100340100760203c01807107960300700500703c402c4100c0180398a6a030261907648850020001c40e900c01042000003035900b9920303a8118103a0b00401b1580710440c403519280742102d5000d82800b4061103840c10800401c0c80200c107a40d0040b0102d14050022002d41c0b03401c035244500701c5401000c5020214011030000d816a0450b01e40c01c1301036003203803800d4403040100315080d0001d400040084d80100f04900f484441508040915080c1d00d0f102e100780119541c4041454110142041c00645a2650507100071780c000d0400d03402c0049810501d880d4101914925202c1c81a030030140248a8548003140454903107601040092141441c85070b041c01030f03450f1801314840c0c00e1140000003820201403100501c1e041460760f0250f00e1030348924100c00c0c81d042c000d66240c0c02c414a03600c0180505840048150303000d00c000e0158a011004450b6100c40e88480601120116000040503034014044440040c0c41415603441e6100c44840380d003454a01480d02106900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 382550350 1250 382549100 382549103
    0x50d050111030a0e0708120301050d031e110d090602030f0f090d03020606011205010b04060c110a0e06151c0213030507090506130c0e01050a09081509150f0601030b0d 73
    0x1500002000044072090b40144c8209a01d1000c0d9460503070b841c901c5a80d540c80450150203c00c40800c0100a9490b10004d2125481e12909042e4860051035844001469060b0b5071480420500e1030010112030048c0020070400d032035410b068a650b41400002941e90081408840400c44002540d2804501390400d5400c8004018140910b00403e8600251285d5090300d5050104050b501c440c12050704078021a410f803a0302c9081c09080c90301d032800c200c600003805801581c510050819140c1c2645541d5541ca020303215944100c2c259003010380504c404030301c2e112841c20b258201070105091800d042104251340e5040b4120250f100c0345400702d804c0d800e11440c2e01c028990700c030ba01c0300090151407a410040c424003003160307100f2809401e104801c00303071001e070441030002a145940d0f001c42c1c1e6001c3c3c1b01410705007071030b031420040441d101ca080c9490300c0f0800d080d68110504240401001c100204541c1e8519030203030300c84494504000c1040c0440c0b90000d032810b8103040c1c48038210030044c1c84840c141e07010203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 382551600 1250 382550350 382550381
    0x4030813020904050f0114070509010f090902160309052e020c121c05040303080604050c040909030207050f03030c1f2c1005010b1b011b0503191401050d0501 69
    0x90a051420b80d40c0c0c5c42481044003619400c000c903041d005050f01109500c80c000b03079141c0c07614040c1408011215005a5000c5d941480075118001c1410500d910281540030f404800c402c00b0f0010038140500612000c0d84403a224880c0700d91000240c0207682c00078055010703200c4000310f1002003040181c3c10300d20442c182940008551035100b040c034000040d41144000c03440d500c14180081c0c064110f480344100d000c098003260b240030200e101410036511195010b4148c5c002c43e814651180103403403d90301c84000a1300103a22440007030140746044444010360710400c43c0110314102c00c03469070684881008100300040441d52a04000403000b980000700c04100c030340b9440030400041003049051194034007090070140314807052183e0a284511415050703809100c520f82c2400c1d10107c00e006c46024559031000c642d500c1d05a04d04a450100d034003020f44295944a244d00c91078400f2283c000d000c14087c81022040c10003014044140411883c641580e07802d0b59100070040d81401c0c200d0240100754940c0750b00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 382552850 1250 382551600 382551619
    0xc151b020a03081003021807030e0f0d090902040e0c0d020c01090633140103020405060307080117010507050711120a2f0a060302130906090504060516080403081302 72
    0x5556000c201d100c00c140c46510b50700c0c90303900c40c1d40c40b0200c1604603010080d000ba9092803441d12070702c1171402c00ea81c49241031501003000c0e40840421410201d45401100507903200c101c400b01003641159850000d01001070781181420b1400c40e07000b400c0e101c0a04100382c4d03000c0015041500d0f0f01c45404840030a80900000e00641e659481d00b80c001b4072070036400c01040340030705440c4031554584000907000d101034100d03052145414011404580355960b000d5505060b400c0100080645800b00030314400c111036140c00004e507161104110020880e207000e910341d40d1510302009400c5401005680f102504089101081182e04002c901c102d070682016a032103100b52a074030010401c8500d0307029000314400360403d410b00c00904404450143d4810126404540035800340002032281c1d02400410300a40b42c4401555507072083e035412501325400030102c0d075840324100030500515008050b081b0140f40c00d40d020700a850039001b07007d040b02500050811070403030003140307505000c02240409560018900d00303c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 382553956 1106 382552850 382552901
    0x5060f0120150109060603051303050426030313231c17010f030201020c06030f0f04151805070602060903030c030a1d03070c050609010c15 61
    0x1054072881c10020941002c00c5555030080155180015000c1d05101c4001c058503c02080043c0140812107050b0000c0d900804843c00c4a04070400048604241c0c07036040d070590b204400030000740c400070080c002d509904100e0f405489200e0240e4108962110b4241c40f00c0b0b55010800c00c03801e4010321604c2002c00880040c450800c84e56281130402000101c0060126a03000c2c0c105036085024036405004550b010080d01c841c5110848030103003140740c442002d880c1d0305070081180c860b42418501017010003030121b03003217044c0080b0010280f10000d24000700c0d090790741d034880007514144a890000902c0764004910b060050814401649c13465507101c508030300710751000d403040001c10740c1e070f50b0703d13078004c0c06684800d00c0114400c1029554a00352410240c1c41c03441c0a400086c8982000c00001d9616a080b17a01700c21817a6010300c10102c200c3d40000e0b50001030100f00ca5072011070b8800c0032201d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 382374100 382553956 := by
  have h0 := BRFrame.cov_init 382374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 382374100 ≤ n) (h2 : n < 382553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
