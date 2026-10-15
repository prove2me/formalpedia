-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:38:39.699885+00:00
-- url     : https://prove2.me/submissions/6f34cc2e-49ca-4c9c-8c27-13395b8de189

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 911690647 ≤ n < 911870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 911691897 1250 911690647 911690651
    0x12070c06180c0501022e09060f05071403150913020d0309051e06190203090a1d060109140111010605120303040615050102070608060105090d0b070201060b0c0a060513081c 75
    0x2029800000c2c4510360310900b11003000007040e9801c6e01c144007442e4803824507210703480d8111000055003900c907441c041014954001220304106c1401040b40782c0e030282d0100c1d80c640800a0103400201ca007400d1104a5044981c1035156540341c1d207481c000100c081000350490038112591080540080c02c03101511410b0391200c10030085103104420300c1c05210000d42c0c03c00000c00950f041c22400c4a0041d6030810140103d910300704521001c21107003261a88944118441e8a0507055a0112081c5054101500f4680f0111042c141802003040490810849052005094108000400c00e4015500620008101d440c400c100e0355002500d0354012241261414036080d1030002da200e183ea50307001070b10390603401000c0031420200142c035000d80190110f8144842800b8a01e41b41c4d0743d034800c40b400244120340c480e42c1802c20312400f81c00d45403560060503036094103024003054100e0024140c0e40c5030f034000c00e002c02c1d1600c0382210641982d51075078000d0010840040c2c4540300408405103c980d011401c001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 911693147 1250 911691897 911691899
    0x50912040b180f130f050901021908180613060c081902070609120302180a03240609020a03090b150618040b040504210507020612070201020c1006060f0305010b12070c06180c 76
    0x8194200e01c1502841c0d0005005010140d0074988144001d50b0f00c2880388a132003489104070f4100c073745001d01c00c551401c07006080c40030f54410403a00780500302c42e045560601c180705080004103501c0040c030849002075486d1313011410405200302504500b0f092604200840300c1c030340182c10020003030741c0180c090756807034490030112f084103041c41d0146a003201c0e0020410040080e554203c40c0c40d0b8002500802040c41e1200e0001c0746100c41417000f8030b4903681c140c40000e1807049522744480c550307400409011080b11120140a9542c9400d0104e42d44c0e00501408480c0b12070765640010001c1000d0f20903650403603d06010001005004c031581c41c815600d80004050140c00c0301c0044075207102d032843c001c0d00840d050220b040f880701c2c0c1c180760b190440303010300001d410112404c85081c80d01940701d9010842e0354031010100724094000b0101c6844021034070b8180410340c14001d0711500c51140640c008102c285910014000500ca0010000d000784d201d5801c0c031040241501f85441e4000520b001d0f91a0300d44800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 911694397 1250 911693147 911693161
    0x4022217030723030d060b0405130b090103060f111308060c0a020307030c1e030c0309080c031f061e05011704050a021e04020c01050912040b180f130f05 67
    0xd4076001c50344210360f41144021024010344607000d404680001e48014804085100e00d01d001d20707405030000c0c0040390b454038a464208441400e915541001c59403034000080c0c1c054640e103806078103481d00100003182e5503030b4200142e40100b66081c60750494107008100c802c44030f4403040e200c100300c48070803085801c1e9445206036012588600d40744500580d008000b10740029001da4009403550f40a0201c3e082006008030491211050301e000850024000e0f410190405401a844c2409071802100a0400158443c04641c0e40c0c0e5a40111002410340381c00320301181142c981241e4080c14100d24803c540c01358010050104100d00c1c010a40803030010382d130558009004042c1c2500c02c81e044070041c24107c4c01034090201c40b07154000e1b4034602c10005507030707412140c440d80000d00c0c10410b1040000384031300e00040024240a00b030000820b010008000c05c0040025070b90603a001074086080d00c030385811940d400103e65040c4154400e070000ea040582000000507640b1820103c17410130002e000580e1020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 911695647 1250 911694397 911694403
    0xf151905091201020a021e1e0a0c06090807030b0a020f0c0f010b011706060c0f0105100e06121e03130b07110103050c0f0715240603020310050d0204022217 68
    0x102c0000050b8407003260344122042847d203229414a00405407003580d007600940c1e250350300000916034060307400310401000f001512003090008040900d01040a130307080c000800e45407a200c2c800500051891008241c4a00280c0d040b10042480c080070280d03034544062510352640c80c40c81e4800e000d54644001200d59500a00141105a0081c3e02c040860350740c182c100021a04480f600030418820804d40e001c0da0701091103010301a10750030b000e6035070711843c0100120382c0380e400404460050b43e21803603034548440002600c0040380241d081c042c410095961915103180201805011310b00c051400014143d14410000c0a41c07138000d100e402c001445d400c006400b65941581e00d00d41c0f40400704a80500c00032404003401c0d02512803203c020030124582520b000791004040d2410010303812111071014402c09101c00c60090103241400d50a51621444440541a151140f103000d0700810a00c00119a0b440c0e04449100a2090701c41c6d070181d075580d81e80700b25034401d801249282c00b800140c186280700c0c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 911696897 1250 911695647 911695657
    0x60f0e0901170f03121b0715020418060b090d1b03030302041d04030215130b0108030301170a110103051b0d0c09060e0307031506081009050105060f0f15190509120102 73
    0x44170111454582804180315412004080c010b00a0140041000101c9150075000540031044d800b50b141d0707080c07002d404003d004c1d1111001c1950300c0c1600411400039144141c60b4201c4d8216a0300c242241d940c00d0107401c2512a9210030301a620782c01c000310405800d5400b4200b40c405075140c3d640d000070340e60005a0021816100a80541d00c008440e01c9408091230181c0e5010804c0d8550341c441d01501e07654000340150a0300480007030303000400180002c0740c2d001051001440200e0051410318070940301e440902c0d00c0001503604042e190400200031100282e55a0044480c10108070707a00e9421100800003895000c54040000b41107400004505100b82000000218020080c0c40c0603441c503960300003568811004150429168400000c41110034047e45014980c2d107400404d10550a250a41c211070300105541d100d0b90550180403c01e8840090401d1907480585a0501c03103190310017050b180d401003068459000c11481c10502d1066800005045100700544140c2111405007489070f09034012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 911698147 1250 911696897 911696917
    0x9011409104a01020403080f0c120703110105010f08030a050d060f03050f0d030510030201050904141609080721030e06070609020f030a0201020601060f0e0901170f03 73
    0x4401c01c048440c8069000d5210011840c0c0da4403155507000340042082e0103a07030407600203142500000e40d40785001400d07070000e40e20032000071843c250640c1e1b640801c50040b1022001c45034808a5481c041c040200076500c03c3c00b030030740041922200c403841c00501150094194040c19420400001403846042d80310340700751068100a18109405044111140d402004800204136141c0750006520310a484594000d5400b03100504048841c540c055440c001103900520b081510300301c2001204d02041e80050152a4241b801940e640b40c054001030103442d260341c540400c28426400e0102c3c0755084c2140020040e400d0325403540d100e5031920410345801d0070b407140700505407094001c18465804000352942951081c1046100c174100900440c00d5904540801c0712526550702a10b015481c10401450080d0750440c010122182075a00007925908184541804e1024201c580340310580030b800d00c0040a200580400780039030351280d42d40641d03071f40c18080c41c40a001c1c6000c90903030010044100d4011181d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 911699397 1250 911698147 911698153
    0x50403020d051e0301060f0f0503010302010c030c02012102130e04050715050d0606050901030b03010e0d0f09031b05150c15190e0c0f0109121103010e1509011409 71
    0x1001d4505440d280d0014044103e11406180808074070303080f00380950301811a42d51583d07600030000718083c0110b0320039085042440824801000184c1c1d0250b0040e8800303505180c580c0020b0220b20041e41c80041514846846620010043c070100e0840d5000c1c3c10111620315201d0310040d55021501c18180094601411940003940148009040591002111002c070302e80b1a14088500070344d54111000c54102c80001800011100d029603230602490135010000c400800c61985142d540301d0f55400c0003840001480443c0d03151414640c0a40e01440c000c642145260002003e480d0007401c05010f82d0098074400c42541d8681c040424050094807416040e04005018400014001648c0248006c0200071102400c0300c0321803250703515000d4044282400c50041c80d080608408018803908c040e8421810071a1100c400c014000511400c82c000795008980d0240c0c40c0e040c60042405070281910300ca0300351055201d0380c1f000341a4916824444c48489008204201e807441c2200140201503994124540c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 911700647 1250 911699397 911699413
    0x512040f020f120106140603010b031b1b060412030e100207050c131a03210d02070204061e151e0201411312020304030204090c03021305040302 63
    0x24200c004204155000625080302d85a644000980e0b240041540c0403580c0d4407070808029070303966515102c03d0300e00211501c0f415903040c07402810181c000140540308085e40e010048101c0303070944040301c1c10501030305400600007a500352130607642c15050f20102c401c10006404519050f202e07118000c0b801827103030080d1440c0100189280041c3d081003005680394042c8400c540c203256a07015900d900c4005820010138100c09002c01807600d984108603890282d0400b603044504031814500d200000041c00c510503441e22003006102c0000c0c05441c1000b0b40140c030700600801e602c580031010000b040307400c0c4071400c42d035519084c20107480d0040e5103012012031181004407080c089220070f00451485030f4400022940744131107189104c858036850b064824625200c102030800b004800a10000c03210191098490501d120500340c901c04908025104803032000404d15010b00c06d01c01c0324021030b00180b0a10456484d070030249410449840100e106055400303094100456034000c0c5442039030142c025040754 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 911701897 1250 911700647 911700653
    0x619080a110a0c03090b030a06080c03010903080a11160311100b13020d09060504080c10050105091f321e06090402040509130302010e1c2d030b010807051204 69
    0x43c4002000880502c4810a00030404480c3c020246108000c4a03201045c074a1411451504013048900302a000340d0500c0800d001294002460703e4000f0782c4141c002601c3c05c2002c1400304c042c026800ca000102807442044001c0c55440000d0b0f0000c10346010646515000c20b1141a0444201d20700b00c0343c100e0b01e00300c1020f001d0b4a19034003801e02d904c501e000c00b00f10008035a035040c085460488080303408042c04a01e10810180410014600405900c0700f040554142400600c40d680001c0c0720000e4a5039040b01851488503000d40300c00100003000354032802142000310b0503400c1510501508090a00070304c040d20625000ca00580034010300c1c084d6140320a061024403500c1d80c0310520031500140c00f000002040e4845001281c400d008440781508a10305030b24000742902c1c8074444d2517015502c44031011b104140190b902601d03520301428002c03881e500c2c100c80e011001d80400c03110101d645101c50040c0455405070045c0c001051301f6698070b074a03550340c00016151409004001a00e00350341800003800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 911703147 1250 911701897 911701907
    0x51f030506010e150d0308100605040503120901110303103311010608032d040f300308090114010f0b0d0e1f0501050301230a06050619080a110a 63
    0x2e1100c403213851202003d00210b00307255071026003140081c00c10300800484142c1000f40c0c10242c070061829030700d894900000250380380e0402283c210102c40c0080d69801301ea00426241d0f00f2104100140c80e100c0c9480314100090000b03130702c900480700c0c9845c40d030081c0000011034050002c0781031000019089842d500c04070b82c51180091036a000759139600740400c4528003040a40180f02c44420700103c40000b6800f13440d000c1c420311864200030300d0117100c00c0c1324450100701a101030300c1c03211011144800c0352004036003400d8848024850000e504075902d10a141c3d020440a1181009200a10200440f181c4800c0c028a09104014403100807040c2401101e070f111005101107141c5c22408142c40c44005c5005082500d940c02050000e103000401c440050424092503004000032002000038190350100d068145002c2c81c449440002c890740080c0000c0324651140010f03120161030180c503515101d08601c125043c415106000c20222400602c04550034010f68040640002400707050503040841a50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 911704397 1250 911703147 911703151
    0x4090501090510060815220b060408070b0f0f04060807031415060a050d1a01020d03050405030a0522030510203405010207021315030b091e01051f030506010e 69
    0x2112074800d195092541c680b90a00000e04d000c03403d1610111f003400074482241c0c1032000b0580104400c1c0001c001c5040c01140c000c0c1196482403103182d40304040d00400c44c00340f040d040ca688803080045008902a5800382000c3e110341c2044d1402c001c0804006807020684070212122066003110a42c0c1e2240381c100100a44014045420540c1c105130012244409517014803800c18100c2d844941e031000651b90400c0454500304103030504110380e003001d0b181c1c01e44034440d00c0c00d224140400065544d0952050688483d00003500c490a1080c00c0e03164608162214603808e8420111800c1100d411004c8000841c01004106449441803a00395620010401448121000180b40700030340e02902c000708904800141a9205100040e95018148100901c405d200403001c83c4c1103107004820120b600c0100d60040582c0e0300a01c080d50b10b81c4c1c0d4429602c3c0340c6803205041d400815158041c1c1000d03024150030040c021b40032100140a000255031800c429010f040c030016280d076101400406c00003502044482d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 911705647 1250 911704397 911704411
    0x40b0d02030a060c050f070515130503041e0306050709030611090102030304060506012c041a0f0f1309030e0f01020c0904110a050616150b060706150504060b040905010905100608 78
    0x82e0801c6c154150000701600050303070644298014010140c50301040c0030402d03900695404070fa00d002c065030340b070721a9079004071b000d00c410380284195400d040c9c000d051066002160b10100510aa00d000035004005443c50701c4111040742c1800c2e251800c180c4000c041d140784400683c02181140d41d036440b000050000038002c00d060040b11701404650704540b11007116441201490a100000c0b22000c0c04111070a64050906044030904d10403030304d56814400180110007120460031180c40000050340080c000b800200b80b1501e00300301d84080603082104e01010300421030f91024030510b40da0042e6110303803c21640d01d0b4859080b00000700001c0e08002c11341c44060700070302428001c1da110f20228101c1e900820070340404413480d05c20001080b502080c3c010080030007280c14000f103802000811498001e0704030051880b92500c40e5600c5011401c0da05200924005000740041c9980b080075112603482030042c60388680c100000440c2641d51402100d001b5001d00700f00110311803800c01c1c222a0136101900d10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 911706897 1250 911705647 911705657
    0xf060114300303040b0916062001110c0c03070b12130f0c180c0c02031f0b0a26071a0a0e030a1209060e1f09170309040b0d02030a060c 59
    0xc258000303002c001a41c82580f08000e01020b6062008043c1c1c54000091165800d00c4802e503400d210650b40200030510288188190400030360035051954094034007280009008600401c40c0b180d403001c0081c1080c8214001e034160380c841601c0d00c1102c140c0b0b1258004620000140001084100b0748030120844058000d9030034000c04e12440d40c03180c58070492a40400000d04078400390a054a2a5107d01100b040890504100c21841030b4082078841d010480c48142003184450b0303a00581d0301c82d81100300c0760080140343d021099101c4107200075041c4800808500c201092404602080e0f0000340c2c501642d0303480b030b5181d200030041da0003043c9030752000c0ca03004c080001002c040100703a1020401a800c042c0314418180076021910001480b4252583c0080100950303908500f4564481082c504a03100483d80c0d0505030714204c00d400c2e50803003001e50014126043c0180300080984c400700190000c040308860a1040c65042000c00085a2044002a6058002c1c2007003200080701944900062907407800d103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 911708147 1250 911706897 911706979
    0x2280c0605031f0b030106032a030c02030d060f09060e1b0f0f07230102160807020d020d05031804060b0d0c090906080619090302032d0406020f060114 66
    0x243d6981c0034581c4442001c00d070110040c0401070b01030241103182000c6410441c3c01c604103101d22400304e02030890700d03018551b551045103580c80c800e00c00c5034981c0600440a0004550382c640207103c000652040d4001c0384d00d89100483d245403c906090b00035200c00c10310081e103da541c0406034003a4007000004502400411550301c94661400103000143d010301203102c404000100c848510020011100711164030402021414024a0141003801d5030802e0078191039210301d202140c90216803900c0a58000b0516104904111001004150106540180961030f010308030901003500c03424092511103031400e1054030840341040d40aa00181860706e400b01005994003501c40440f94583c0108180d50000001c22141e039120102804015140c0c0720100035802040d00d009480e402100b083d00c24241505004440007418000000600f1045030f4201c1c2d51641c1d40d042c042d540f541c00318440350049c000c4000000d9003140000b0a8052590040c1c64982803040440d0228a141c03c805007804c0c01500e0205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 911709397 1250 911708147 911708191
    0x1908130b0106020f0f06091213030b01030b150f01141c0c0302070b09060f040b1e0c190c05120c0f010f240510120e0d02280c060503 58
    0x94201d00802154018107080d0142c0c03001c0e10306002a509400d0510352104c3c041c0b1590070400130b00c00907547c2c006410203845041e10241700c0221481eaa201a0055801e07000100601c0665046140680803c0fa01401703501c9041c0c05000d04080092011401b040710903480002800112004201e00d0102801200e03080c20b00076160001c983d0a0911480001e07130204140c1d0402c003010202540042341078006001c286088039881e401110006c1c401040d408661020803202214001c1401c86841c9042d940421454180c0118409400290000d8035190508403801c1406010b101080c80303490300311001d0090194824078a40090b030110340e4503512072090182e0816900000c1c840d0098071480389501240034586104000f481c202444800d94603600c81d50420450395980704415010072249040c160501080c01c0340d0798000b0031200a5041241c002e42d483c5804040d800b003508807003000d000d030f10a642c012210b194403503030021042c4020000d4042250a0214502038030145500800c0b640700d140ca8185402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 911710647 1250 911709397 911709413
    0x20a06050a0f0c050301081e070303110a12051305102007050d060f0606090f1208040302130b4e030406050d0b0609030307020d0201121103090c0303190813 68
    0x3c03680e0340000f9004801031121042c14007094940580d080b40d0b107140504940981d0343c0b00e6140742701c001c0c24800250084926030106020207a031075500300d440c071550014403139400340c45a4440c090407080441583c20214a51030640d0b55052603c01d2030392445010a03941d1005031402c05403501410b000d106140d40003400ba076032840121a034500c901008205441200300c545c2c2540c141d0340111041c080000028495a507200415604031001c1c0f40c08805415140d04241d1001d101d01e82001e5000110500741807030382022030b080000ca82c5002c0d1010f0709036213900304103644164510008001d5000061511107810b0001466401403010205140310820780c4c04203045155a0256000f6400300700c021135000c04403142407081c80320340721090750b01510700b0300c0010019450740300b50500284a42c07203400c008025644548501450040300302000c101c01e1009a2880c0c040d40c0044031500307040d208c0d0f00411151400d020085c0c42d00c80a1a44030b001b440e136841e000a40d007406000306214090001d03c0100404500700c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 911711897 1250 911710647 911710661
    0xb0a0c210c0b010503060915100b070f0203060a0501060912021f120506060702180a0905010e0a0b15180c0c15070e0306010605090f0a0305010c082401020a06050a0f 72
    0x2a4407080e40704201403900c1501210141c1c0141d01c60b4000500300a0301d40000f2918560100c500b80c44001599620000303810704030002e070040d8500000101d81c1034100071910002d80c080d503008034101c603e90342e108040c12050b90402d0280d02c00107482400c08000130042c2e1441d40d010b40d48010021560038941c40022148450340701620000240d81d500c4410743c400b887d110349500690240c42107850064141c020600b03040c00101c10008503244040000c0499400c4c1c0c0c480c00742951703c48001e11004910420841d9207500c0000203683c80b081200c041440a50240b0706405040300242c200811824010300c102d440100040400402d10001c00c030300b1050000502c2649041c9a0303031809030641c3d08080c48002d09905e550000c0c18025403140d1b00502c4030a81100c15188407501c1100c10004805240c404124088801c2c0d01c014210340c00c06030407210382d0740c000711907a108881c84103009041000f2284050780242e401e01900b40560012441140030400e96044140e12060071a000b145003403040d4000e004071707002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 911713147 1250 911711897 911711963
    0x290c03030a060519150507110a0b031e01140108060604030c0b04030b160804061109130615020a0309060305061c050a031b05070e180d0c1205040b0a0c 66
    0x40c81030103014600d00021007400802c3d031340400f80040c44c1440070b03102220608036074a070b0900001040c4902000f00510310354446030805002503507240c0da01c12030200c0700c0e0815114421003080480d0750080740b00814240c43e04a034903404240d41269035101c01034400380405450240c104004010210110703940c01c1260f8014900c03e111a991182b446c1006040a10040d01101c490b0080713070040e2850036840522140c0140e00b01074000303040e1251708902c24207445540106500085d0103108a144c02c900c80c0d20000440c8c3c45210983d4240f591040100d841c0d0410200060205084810903c80144240c0c0000c1c0d000300c01920074900e0034038007900c80203c03640040e821a02e507400001500c00305603101d071480880d007419604c086203130605070750b0b03050310740d030303003070003141c8a4100040010b464a060403964035401c07020042510240c04140a000b04003000c6d08900342c502e0703003c5e00c5050200328462b4044a088411000341e550400d20f002000b100d11103a08101130325180c402e10740d11904002590703060301410751 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 911714397 1250 911713147 911713151
    0xc0507060e030c070b0a030f05010b031503010605040e0615010203040e01060e0105071a060307051f050711360411060a030e06011d0f1005101b081b0106290c03030a 72
    0x206e01c0e0000d013611300c80d000c3c4040082c20440100400d84000c0240c80e08200036100c803030791060454001c00d00408580c3e00169100e818072240c00c90500300891800d0141c2e1820920703070b0461035280c0c016a5039108920640d294070b24440010000d443c8034440030782070342405141c141e2424a89071905034038400e640d406801508131074000e01c506490200280001402d09a6845803003454111075a250106120f24480510000007100b0040001a800a00c1c0d840d400404980d001c410510300e800d40c220500e02410320201800d4425040c0007140804248603d900490400917030b85070900740001900607004a10600d902c40142000c0000180984c50181070081803054107403a1609440c02d101e10060300b0800c2c804c0c04001445800c00002c0c18a100307a03034059507074400c1c0c1030341000116506c0c484200c54906100c102100a01000840d8008186600b030071030120001c443d00500c0c55081784d650744241181c0d9000f21402d00f441c119408403400b80548000d078841c0c2014080040c450a6500444104503850303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 911715647 1250 911714397 911714407
    0x170406030f0b01090f12020307050909010b090f040c090e15010303080619120b070513091d1917071401060303030e1f02090f06190e040c0507060e030c070b 68
    0x1045900c0b8140d01c125003403801c0c1d040745180c280900c8500440c3e000e000e00b14002e0010300300a54904228810080c440070300704403031502d46803100754000e22181012511841c5020b011503184c03250303214018042c41c0c100c1e5030000f0740c1e890176004c000103001c8401c02000a008a500166803811135684c040c1c025402034403100918a0a4001c0020001f800c840601068803024814892141c4101281d2090b95101c80220210b465040303041c2c42902846804183c2d0003130540b80440ca4151540000c1c03c10810398914550012450712507680728001d118890b1002c1d0901d03210040454100740a1941c4c0480c42c1c141207182140c203072602d01c90500c50300c82c80300c07482e9103070380c0108200759161185808070303000b00000d040c10303100c002596800c0c0440000c0780d00030241c012404480981c0c3c0e041c0c644031800c0000b0190740e0b40b03200c001568683c0e9402c1030000400320b50300480e00132560509009a1050000301d944042c60003140c0d03501c580042070110b928050750312043c014440d940408006640181c01640c4a407030300c1c0c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 911716897 1250 911715647 911715671
    0x5190c0f0b06010810030f1704170c0102070f0e0a110c030c070302210d03050a18060902090901022508070b1906060216060f0c02130204090b0a2117040603 68
    0x110005406840c041e17080c1d103020008605546802400c055101034005013100180d40303600ba450040e41c20800d492003540341034080c0b81c00009019800e164082c0c090303648081d0707500d0303294040b0a03c900ca518402074034800040d50344059030b0b103c0040da8001d101050300b8100c00d030660624580245807a01026403140781c0503c1503142940d5180c12126000e03600b1151032407032020240e1502c89440c407a80038075031201d000c28a02c08107074204e10355040805403c51034946090414801401d030040090f4052502c1c10701043ca08172060089031702c41010190080c40780b20b603041d28260440340b0400151400d40042c880000029201c181c100d00a40300c40f03028041403028451802d086039080d074055015540300038040000320340d00280c1c00080300c0190800c2c03010420740c1170003515400f910500c000c2d0701900c2900420942d07515940a0025185568000c020101020081c00a80c2906000302c3c0f1030008103030401405401e01d801200010340c0300c0c0d198007001101d0601d51402c070703030800c0d040800403a450321210304403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 911718147 1250 911716897 911716907
    0x21e03120c070c0e130b0f180d020601062105310b010312020f0f07141509091308030702100c0c03080c0d02040f0306020903190305190c0f0b0601 64
    0x440d104102141c0b80c00d090350303598a1842c10910400707680c440720400140d07614a40107210007010350000f120082916190000050761a400c0721400c03000c8044080c0041070001c0040d00994592454000f0600d590030f1080a83e00e036200f441110b0403031000f04034036102c0041180100e6003c0c00041c1e074044001d840c400764100782804040c0311035410039042042c80d004540515010b50450780c222964003001c03840303401e00300d0400f0b101e44020000c901c2158018650140f00040403812900d065510403032a0103004100441c03c55100084030b4a010284450495803409200c10303604501080b403a0b0070400d110760b40d5012107401c102c0304000960801c0c1c0110f40d80b690903001d10401030041e40747c0440048072694001d00141c1c0d000d8480d62810340c000c07511144021480d4101c8004c0d00f240b243c4040c403159030340751010103544000c0700d00d4020f0203020700351000300c0c80c110315400f40c09902da19030604140c1100b9a095003807460350003000802c8004010400450160070f6128a4079004001804403880c00d0302c00580 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 911719397 1250 911718147 911718151
    0x607090b1207201509011103040809090c2812021218030c0a03021005060d02030a060b1306031410110403060f060909112b02090a0e03120711060c0d0c021e0312 70
    0x7c10748034100304201c0040d03140011100f81d101d0860700c0e070909840700035881071103019060005500d50040e4000442c0600d034020180902080c56544030360364800e440e002801c1e0b011300120180e40b8020b10010520a6607540d0707141001c1d15040c002c4905000341201030a02d0464841030030b401503003002c0081200b40b500340c001c2d0b9a10090503606160054040e90209036140c0c1040b00140c0070715689d07140300c031047d5288032640ba01c01880d2501400301c981c49003402b81e84143e030f492000340030303214103442c409101e00c0d140100c1902103c1d08100354181817468039102c02500c8840e0000040a6a82e14081072410991040b030118038040c4100c600301d420807000340040c505100c00000c104210001034103404c12061041640c4403581030383c0340000c0e42c481c8440c00d4090300000034481141c1c00040340002c041a00c8040c454424580f43c2d0b40c0314482203015031641d8827034000341c44840d0101400c000b000b00c0b240c195040300903095190710481c3c00414080f400742c1540c54008680520755000001c03205140c3c107920142c1ea03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 911720647 1250 911719397 911719421
    0x106031407090b0109062304060302120609040203150a020f04060e010f0e030303060103021315020325020916023c06060f1215090607090b120720150901 67
    0x110605010020344040903501c20325007003000134141019a20711307c9680d009074448040003a901d840d03d407807000d0040d4120841d55054070506000140441ca00a4a42c0d4002c90700a0081c0004400b0984004004000281580c0095408000460b1064034107070007400100344c0b0707680b500e012049242c001070001c5004403500c401c01500e0f04507101590380c00302c2120740210f02400e005075500321071518101110016400b03c0d035003004a10b00c00c9030301e07038000c40100ba04007012841c82c552040c2c480d000c1b0229486503a07003e908442404001822642c0d49503aa030158040c900403944569441152052500804e21040c4260320b0844c0165041d00c5000d944012807000c201c01826561070440081025036040540151080c1101c501148521030b05115021071811007410046e070038138100c1c0c9450385d10101591203100098440c1b40010f1a82080e105075140a841c0050040e52030711007a20072608402c04480d0300404440d0003071210191030080140c1880404040042040d514090307811508480d0b80c80030013 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 911721897 1250 911720647 911720651
    0x28090509010518150102070306060801020304060b030703050604020d020a0806090a05060a022508090604030308090d0f0509040c1b0516060f170a090c030b0a0f020a0e0103090f0203010603140709 85
    0x41c14103083c4464181d021121071981c01d200c80004004078602a06e80d070015101c240741aa0106901c00190010340c80b0324020441070101100c100281a903500b080d120182250b04040003103030051800000740795142e40000c103a070007665220200903007482419508982194014000d6a003000018015150b00881901c02142801c0c0c101201104000c8070f802c401d2800c94940c0d40043c100040c4606407481c004000e49295201d40d04e900c1d01600908060358200d01e184a20560041d480703100b400e07442c00c04c0c600360f036450741000c4107e820f00015001d00b8881e101800603c0c4500440c080009120003580c034000d07802002100c0e4a044800600c82843e0011010014000d00c104407254000a03440085030315118190820b0341d642400e10004c0100c048018000700f60500004184016501d0300e50040a0101c0700b085100300652020089124081d106400303d110708100000941c0241c1c0450030041c0101d41b1007900003550303800030782103408079002121900c0c81c1c400c4800c1001e0341046514040c1000c6101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 911723147 1250 911721897 911721919
    0x1230601350c0301062703150b0402030720011b0c14030d1a040b0109090906090803100611060c190302090a030303020414061608280905090105 63
    0x80503441d60180040710480d22030907030248048003060384210480d00814038882818620200540d5030f0081c03003800002885046d9542e1148210291908080126250025418510350b41c030345481a40d11300340c030300e216500c40601c0c01a4640c2d000a41c410100da96444901c00f547e4101c480a282c00048440d40f680e141c90301210840403044072401010341542001b240c0d02119140c00701035451101d030000b0480c000429244221002e83d08010341c002000c0c660810708100b100107101c00c0b40d1f072580302c1c04d001900d6040204081c3e0200e500c130038040341c001e15010587c283c141e00e41c002c10754400e94411640c06070140080012580c8500c100321094105805000303030b0b04052010300d40c40d010300000242095600484034140e01c0c0a0341c102c8002403005000c2d945007540c0c9060150080d0464400c8000b035080d480740d000b115150160858500c0c28121140703030162a00790310b5800294000d20408680e400d103400030440c444400c1505060104415614244c8090030141400310744101030348518068800051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 911724397 1250 911723147 911723149
    0x901120b121f1824090c090f0209010e1002070b03010e10050a0e0604020307090806070c05070f0305101802060f0a030f020705150402061308010b0f0a050109031203021209012306 78
    0x4160042035420000180106080c1407042001d8100d4020203814240381031220410441300c2c52020b400c40c0d52010003017000011507170503001a8415424220700003400120112221310304000c3794100140e0768411a900591588141201a0300a803ca815404116420000e1258100e03500c00c024040a40d50082d42138a000403100d8501c0c0301a010900c12900480060690b41c0704003c000002d18031a07040b12418284401d01410721540a241910107029a4801003a10042d84004104490b485001001208010181e0b80018070052440050445807428680e0169032150301030b020552000a94541c3c4000301c40014084440101c41128410f00500148012460100d8014075804042521100395a0359100140c0103200702807000c0c0d010b000307402001c540f0030710560200042d0001a5000e03031b41d409000c6e0410184100521643d80040c0c5a0038040c000240c0d4685403c101822505025040c17210602011071300c0c003022100706039580e65a144e01c2542600c0e91184100100c040806042c040c14400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 911725647 1250 911724397 911724431
    0x80c0a030215181315080d0f03110d020403080a0807140313030207030501050c04050f0604030506071b020d03050c16030c06260f04050607140901120b121f 68
    0xd07003906815100803e401041c1e14000c4030410032618014200c54910600d9030303100c802003554100020381c11700303050000310b80c0a40008480c6108411601d500401083c0c1540c00c4014151110750000c8001d4140002170981401c2d0020f0800b03140705042c0c80741c0340c0032900b0008000240007040c0702d01b006003000029180117507680440303421400e12050080c604600e820305a141403140d0340020050340c0390000300030040c0744050241c001e030341044540c282c0802020741000128000c81c00090041d4000700045885107010b00555480d80b1180c0040c0e2403070206580000344031000c03180040d00401c0d800202601503010902101501c80c040b0841210554110385a100c5075007107a000c0d01092040305040d201c0442031034a51390150f071003091420f15031450300b18803c1c0711409003601c013220644540e1010a0f489401640380c118440ca69170fa00301e007807142550046814204110041407521740e208100b10140d20390600c06014020144014845d05845102140030800211a91081507140c842d540102407027a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 911726897 1250 911725647 911725669
    0x201021908030123010f03020702010c0c1707050411030a0504050f0a050601090c05072307030605090a02030c0102061e040201050405131401060318020f040605130501090c08070c0f15020c07080c0a0302 88
    0x7851f00585035060ba100503285d501c054800940312180040300061212135000354420808031401c282c401850765042070005071185054080390460007840051880d15003a03116030780c8035014600b16841d070003007502840d0a04600c0320007a5a0740d0040b000510141442c4e006e080024011860034a1038480c1d1501c52444060b54030070785c81a0000f0710704820711142000c214402c0910342000c010020360800002d0305a6800343c40c0e00c00c90083c0200d0036070301030545c008104a44281003101400180004c28034820108020081c002c070f041c0801803001141a4a52442c184900450701c400010a002e00c03542c204240b000c16441207003014240b0340280100c144c07803443e02490ba541940d6003042a09081e002038080c00c84e030741106801143c43c0c40c800a40b2140d94100d5030480d00e44120410001031150703412107034035404072410400f080c4100406070004034905440e001c600e025040c2001c803032140401c414180d84c4903401c8004107501c40c042c20710082d4018012502043c0f003c4551b00e8030140317143d0100f2800044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 911728147 1250 911726897 911726927
    0x609050d02010f05090a0b09040c030b060409090203030f0a0314010f0b0f03060a121a01121a0402011101050106030e070b1806032d0f0a0c021207020102190803012301 73
    0xf0b00034405015501810689624441c01007800d115244c41e00c030304040c143c008285841c451400c01c0e1310303101030b50300038410304e66800070141106181901300811080030700500c0300d040760944030821440e502c5402005c0901051491958042011103011480048540341a0884490729050540400031055288122401410101e4400c0e03141c0e5071304000100c0078112036028080c1444010210302c01c00014202c25100c1500d101495412640c0390f1150f1010a2000d0030300526503000b040003001c42443c04541a98003510500d8504299204071440340d0a4880c203078013010100f62103022600101c0c2d0103000c141c02405613120080d081401080340428a590b000102e82c0c09581c0c00008510b4000c0741684203d01d42c8a0010700c000c0040d1121a2007c14560455000d52580140400305000c0903050007040e5100c0302e2603005181c40e22201241101b07544c003a110490551003180700307410543c00640c40c0ca440c943d000f000610388940c90300303c0882d610039013072200d0074920804045101a0b607070440d0341001c0e00b00d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 911729397 1250 911728147 911728157
    0x6030d03151508100803071703060d020d05010218030111040e041415160314010911040306141605120103080706140a06090c0215041115030c090a0609050d0201 70
    0x248100800038a400c410400103410380c0620010360001e501500440f070b1300c0f00e019000b5948010442c1c49008030107008081000c0c0c1d84824641600c880090350300044018100c0c4085489c980c009514004154000c64480c3d40108145203203070712214600350f1402c030540090101140090481d00980300f540210511a50001d000c0b40030310480c112860342c0101c1a0040751001210020700f0300819404407215242c1d010300b2142c50f18882d20030b00074810083c02c2108140080d03420040d40c00c000e88402880d03210480300621000003c02c045000d006844541f04140c16001d00b4003031030200885824400707840520000700a69007081d42c1804e040b5044a0700700c002d4135141c84c443d10307060024080c191144181c01e40d4007000e00600e030b86180d21500c102c80842c0c50800101d0301c0c1140907619114210740d194032445100c07000a0120b401034001e0300c14400d00400400e40f111400c0040d80c0c19030810b54166500752004503010708a81020b00d01800603010710f0034009111840c00c07000840c82c0c0031100000741044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 911730647 1250 911729397 911729411
    0x4020907030e1f0c050702102d1106060105070206030a0b010210020a020d020c0316050d050a06150f050603010b0d0207050a021e011418010c11061b100506030d03 71
    0x1072180c1e000c0300703560000700143c0701449050b00d00444a0366070b6074104a03889181041c07400ca0075014104541c1c1081d03001d00902c2040d50b4007541568041c15400c1e079850098003011000c0d00c4080e580b55103210b07440c6642c844650307071805407070312030725040004207000d060001c00c00c5440d01503035071807017942d070321829080c00801d80490b42030040b03003400b1521001d9400c0f1800880c4800b61680c01245002011032564202c03400005601c04140e910740190b03811031782100403a402840035041051902010500880071213519020341d648aa0032100b0441d07511a204509010030f1018000d000e2840b0002d0000711350320390642d4108218840140328030103420b200c1303560000b452001c1040c180302002c0440d030020071030300014003c0c6c9500c9070542c1d501d447c468006a244000c00800004444c1500d000c180c035080c034645000c50010040d00c2070041032500f5181d440e041064040b682d60b884004290264503021001840549410214074080c800300d56041d00e01e08000c10006c007900c1c002a200e19402c500c1c0f4000c5800303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 911731897 1250 911730647 911730661
    0x12020106090213031101030b0907030c05071502042103080f070c02120303010510030228090906081b040209030a02090a090c0803070507060c15021c2d1103040209 71
    0x40100740d0084040074004100c49681516450046003100c0c0208601000c6103070740d6004500301c4e180038400c19805200e0b030011501c010321903400350358000b00d43d0615a02c1c1658648a041c810140642d44200315600000c040c0404400c04011000035885668840443c00311341d0b03009841d902005115454a00c40c107070029814910840202d424150050a61444921081c0d8015201d034400d010b410b00500341c2c01c42c6110014864400c880c00342075200c003d40350000c1420807001c10401a500d804040001c44a40411244100c4c40307000014085440240482a50081d202c3d00c00c01045020390710840c13052102c404162000304402090380e904440c101c042d5524405140700802c002d94002d40380000820001c078006400100920741a802401114007040e0b6a80d0103c0d490340d00d61000410540300c2644512040121307801901801c14080b8401c400040c90501140486852241000d856885c0340185039900c070041c150f1540740500e06038180010341070380c4910500f5100190000307003c0c0c1802000502e407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 911733147 1250 911731897 911731901
    0x5070e0c071b1d010e0c0408101d100e07120b2e0801060e090a030f05070c170a1505010b0a0e030a020a0b07110409030c1b03020a090903030506030307050a120201 71
    0x5440001030003804043d5030803090030040d01c2402064220003510000c03900034492002038400700c65200b4010080050340c003c629000d000c2d54042c04c0e58070140303840e2001c00c0a406000b464019a0b400200084448880d844546050150361020401c0c1c2d407084034141c0401c0d44203009681c818220851500c45007003002450115200c0d22843c1c01d040b0600100106161308190040030440d641005481041d80b13078215810744414031a100140070840c10350b0340c0100b0a000f800901306850203854000740c015a40d00d5001c042d102100602034054010035902020080d10240300c803012002c100c0f04010760b604000c50300320680305025010090101c0381c604045240e50030405070038465809010016900c0d13031990750803011f411402c0f04492035031450034050245c0c05d0a10a00c01c04540581d40e803080d0560503188c0d10344d042c458420500b0a41312244010001d40c444003c004010249404001285446810001c0c00c4030409441148280c00070009400421000680c031540c07940c021071491050244850140c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 911734397 1250 911733147 911733149
    0x231f030803010605040609090225080405060403060c170103020f0f031f020a020708010905030307030902180c180a0f03170d050c0a11010b0a15051c05010305070e0c071b 74
    0x145510010011480c80e03408400b82c17044a950f40c640c1001c0648071412041640503658802040b8003911001d00000d881c201d0801c010140505903080c03400792540f001c243c2d035610079001580ca46d62079440c80c0703080c982d01040101000444410382c000d25411640090040c9451681c007500c51141d141c005840ba68082c080748421180c03500413285d40302007034643ca4019400c401802d4001d03004014001404150600031101401c0e40940514a5a628060181d00406483c0410b0760480c800381d8149034000ca00780d903858020b21034001d046031900e2000461018210360030554500078051003008002075a0101c0c004426644d10074805141d10341c1151140000707020791600d801d002030911043c4041488980004d01205040d81d40300403a00e20840585070a85104112231a040450780030308100c0884014604044d8501d24941a40744c120303083c1314540341c80d80c008a20101d8907503890041080101c10400d80000b013096800c0d1803414a01001c035540c0600902c140508026034124801082d00c034030a176040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 911735647 1250 911734397 911734403
    0x1509030d0f0605030c010513060513090c080f0a1811060702030618011a01081918150606020f1e0a0816031205090c060d110c0a06231f03 60
    0x10001c80158860710191003240700b0503010303000780340d601c155551148085400c5119040ca845900380d1400300c0444d43c41d4441c2c1146002840760020204e5100703414025400c84050551714540300e41848010403c10038006403404062901c1c040e00c9460000903500d0507501141c100c04645c0c607035205000811000d10070500300a40c90300543d42040075008082c0e80c41104203c040c4001c00600e0400031042d87c500d40e103031070540d0200304034100085845003000b40d10841503510300000300b64840c214a902c44844150b40c01110105600ea04449281e0f42903c41c1c0740081205100400801c43c50340581510703000b00e41c180d03031440202414101251942081105c01441d40060b0103079445100020007101400d40c908110001105080845507070508c0c2e004d418001ca50304005814914500010840294010703034a8038400c98459403880b1083e40c8140c0a4074011420201500b081030082c175181089441444034180704000c0d850117000d9160454a49990007000d040501c822070031004603541010945034002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 911736897 1250 911735647 911735651
    0x180910232e030f020921010608010c0309021203040f0b0f04180e01050906010302090621070b1e04030f020409060b130605100809060708060d05010609050601201509030d 74
    0x41e88450740c0c1038444008440c0300781c0d01008080e8424858005a101d0110400e903c080e500d4200d500c15602561100c0c0104911400013410301d07030b40c4001500f0744800507011000320b6030700c0d40c049003541042c403141e00400f50f41c0c901031868103007001d00a91061290303000b0b00f1410f031008140806c0e401c1e0408126406460003c41a200103120286e2001c040c005280407001d180d424000850211100012102d060700d0f4010860005a900d5106208442810350b400d072800204020140c04200070901a210181102082d1075a4400c0c041455400e42140d10200580a480c100410000b15030b105182d60001e41d41110301164001a03400d00d00081e04105c2000d40d4803241a01c032108240000d5403043c0202c600948090704107080c102d070700b5524004121508840c4d508070344c00054885109020165002000801010040c603080e1240f6086502640000c1d42d0107070741d0018482113680200d030f86803000301003504001a400502c0c02c0142c860304464111010782044d000495007404080c4196000c5961041c81 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 911738147 1250 911736897 911736949
    0x40c120c120501022502010e0135010e250c0206070218010e15031c1e08040c0905040302030901080a110c07031a061f0c060218091023 59
    0x250f000394080b207900000000c030940000030030a00c0040300c55007590140c580070100d80c800401900c3d42084505c0e854401102078171564152900405803019559110f0820038040d810051150050500607050701e10303400c041e039800000e0705545161041201d429142046035040351b88003080442c0154400254030469030f540b0550301480714606c040c101e651441c2028100d0325881d0a0300854041811456050303000102c0701c0f405401031079129418503440349000c0a107090f90107000340e0245e8000504400240c0795070306001c1401000012403000e000003860400c0b0368141682c0c040e5a91007a4442c82c0d040c006402e002440e191a903500c190004c1d1990255295500340d0344100f95203401450004840382983d9024040940005850092007400d000d80b88001828207048100510f2410781090320030490500c3c46900020058009410b2000c0ca2440410a440c0e4041c204400c1070070007010786400005109040121800c84245007006910000401d04410101c401080700811402e5401440c00703004a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 911739397 1250 911738147 911738153
    0x60d111c0b0607020909070f061706031207030818010204080d0923130e030f0730030b0d060207050f1e150a1404030f0f0305040c120c12 60
    0x1005054503400d80c14000503249810311084808005100390410400d00102005052008555420600c4401100c0200e07a23110404488420150000780002d01800900700021803403211194001a0443c003a00300365003180e0400c80d090040e070300d0190800c400c010114450401030200d010034040e050000399a01c0d92500c00e201d40d82e5540b00c140c1d00004015942c00503510151903041c150000e0560b4500000880715403c006003208128101441242d883e51180e102d09020002050040314120240d0307182c4081d810100a8034075000f0140c00350060b2000503070340d2250622450340c400001401d0001d01c0c1e202000100d0184071410308014086840001ccc1c07a024410009948080445124102c030696520369402d00c0308440150762040300c1e68040d2543c00b0702e0303003800e40030b86030f000141c618006040da0503941c80c607a24050959080d00071135000b44003040c1c12035200c82c01e406231900604040c8a6810256140d11884000d8400c01d0350141705804a201085454010900200020300030031180d404982 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 911740647 1250 911739397 911739431
    0x40b060d0c030c080f06061005071703070e0a1205100509012d1d0a020103050703111210050609030a0618020a090213050a050d1214160b070923060d 65
    0x80100c2038244500c03178900c54181c1000500510400c400340079111012600d07801640d054002e1402203490a01104a840c05040c0b00c8000c0c1d44204003d90742c103442e24190344144104091140c1010b4100e00e5281a131402007030000a80b110784111106c1d0000e05075540480076801480ca09038000b80012a201c044081b166180c40500c100e8002d12404210502c0070703c080907150368200c1990b01258100f0303072003600598040d90107594402c806040100301d40c100c2e0b40d84024154460000b80a102e0942800d200d44444000c1d042c00150500b07441c120b2400b800c4100082d6a641c00302801007115480700c446100b117122540c82c0700c00e080e5018018006042c2c580d024800603400030035120060f261103440000f214030703050041104a81000c2e000b090102125225103008100c0304040c0000e118040710351180c0203500302e008107000a040382d41e6010304c818600e41b002c0210b0002d000c0d1400c0242c40b52042c4840d5101082090110030401c41c07100701d8a0156002c5041801000c0c0f968481501d0142d000103515200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 911741897 1250 911740647 911740649
    0x11060409020309010b010e0306161403131709010537080103120c02010507030e31110306090106120f2309010905100c02010b100507021c020603040b060d0c030c 70
    0x2a00203004d058045001140c0400c1800d1030123915501800100d0701300d406100c0500300c0a000d9240120754036144004070829540292075079001c103030300300d9100c80a01c001111140d0b260400380b014140b13440c1c102c000080c1103000300e074101819030b007145c02d0020564006145140500a5240040c0c2d601400e0007009042482c003403006448503549104002b00180c4602a60740050364142c4071142401886e48040b2600501444125080804900e00c1a140d4441128244a000043c00c0b00c400c041060390050054900c041000048032805009000d160382c1c0c0c281c0b90380d040d21080e04c1e1124100c1c0c0c2000c4000080d00f1100080712155140ca26045840803030f03e480700d10b060003161170a40054030350081841c2203c03c1e011001d441500b20100090081c1303030342e8000c00e140f06110301c0081081d4461078002881728001c501c40704045107000480b24210b00b03044003c2182d2944200c514480017600b900415410310000f80018660b510a5000401a5440385003205d600b45e0080c0a40e008581c0320704c0c203104081c0702 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 911743147 1250 911741897 911741911
    0x610111f0516140703050921010c020f031312150207050309041b092105100e070611060103111507030207031709010c0b091f021e03010602060f04110604090203 70
    0x1000082071200c9018111050105001c0c41c03c2c0392404001da101190540c001580695200c11000c080c4a038040d020841c150b1054141000045d01d02ca03000030180c584048282c2c01a99600103120700c98031024141d00280c201c40c0d0f0304030001d212044626005068440c10306200328a603102240441c107001d00003000d0004402c09650400030700445c40c484040c0c0324030114030003001070003094042c8407034a6020050b2400c0401100248400d0300c00c1c0c0e0310706040c40f039000444105a542e5801005000f0001c0003810020801e40c102906031101c0c0b60242c0b901c0700c0c01400080e01c0350302d420030f40103069200e82c1150304480c540f020a25481d11030390329009413608020310080d103410b000454050b003140550000c807103000105031100c2c10701d0003035035858042c0a40d0003012584c0a01681020111002c001c08907440045000313034005a403200c41e80c00e140041101c6d40d0346800040b40038001809001c0e0005203035500800c43c580030390001c1d540c41c03800c0d50f02d0f008104042e54001c400494005040c12494002e54020b080d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 911744397 1250 911743147 911743171
    0x120f0c01030506090a0c031b0203090a06050a0207211a07020606060f0409051306060e0106020d02071406130b04060309110306040f080c0a05010c170f0610111f05 71
    0x40250044080d540300382d4603e503100e541d85011440e56000f640c041c01d6410268100840c0258917081100e20f80c5844c859044050303000014841101e141c00e0150034050000b0303041c0355040006029000303659210750b01554004664460034841e0901d00401d2006c411940700b07000d540402103500076044440400d4840340c0240c4140703c04100c9614080342925054003a00c29880d0030036140000707910142401910341809001c4240305100441c00764010130b00580603001d0200095450414000d1600d04401030340000c5420070742007031106042403d03400b40005400c89000307448114444075507000e5100c075032094140007000a800a40c1c0d9400d600101c500300d005881c01c0507095083c42c2450307100e407002c4030010103400e04840f20f0030000305100080c0851858140841d10070f03a00c550f49550071035540589941c0415441d0742c540e01c0c028001c0c030959600107a0000a200c4908050001c0740ba2440e10b001c02106100b1410451041d168040023454122001e200c0b500c035110320b584920704010402070311600d14800c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 911745647 1250 911744397 911744413
    0xc0a08070e030d1709060c1c0f060308120106030509150705120106091802070206162604030605090c0102060c0f070506010e04060b060414040b1807031a010306030506190209120f 78
    0x3640480e41507c6280001101403603c0420380b50050001c0a00340e076091070699403207101c04010414444c030806103105a80301d0f9540d06202c15001d4540005902c807004160404003000124140400c0e0001032108040303510416031501c4200351000d01401003211440c401c0e500000892691202c2450220390005002a41c1004c2c0c0182203c16840b036601c010350807410410001035003c80101281590b01e00031400040018000070041c0b04080590022201d035420204e420b1007800814031816410055a4000b0165040341c034001079190307400200300e11841c0b140820120410a0700d502140c51195100e026201076684507281c0b0800e28905440c16201340f850b1024032541410100112016030380151111000c1010750010080505060200c4940004500c1c18418500c4003003c02c1f5805444140c0b4040341000340420305950031802c0001882c100b40c200001040468008102c242e0000e91100c10060209140c4540002a00c10b4440e1940c22040d0ba41e9206541c1d58086400c04070f521a10301a0340c015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 911746897 1250 911745647 911745661
    0xe0603060d05060403082a07080a02010b0d06060602010b0405150d020f1011160308031810090f02120705060d0e0f0d020f0708011e0b0a090203070c02040b0402030c0a08070e030d17 79
    0x24000071f070b8110b144134804000700004102c3c1c803c041d1550b100d003880041100f1071030717001103096800c030840c0071104561203110500c5181e4081c01424070340340f01984c0400c1181b070b000c5076402104000019590240013204503440c29900c0321007940291610181c112012003c441d107005100805085211f0214010000c1c0d1b2850500024940c5044a4000c0c0400341580c440751300c4c501c105850384072022032a20070580e0b01d9640c07031028012089184d003d5860080713003513940c0c018030508030000030406030550000001402565a40c3c020f4031104071200800250300001303d6050b51070043d814906440d18850f41508644d000c2e1300042141c0c1d4a160941a1a551a0b40e400c3d60750907114441048a5050b950032120104029168098003210100404082085d565802804103c2e8020f0320b01c4d5001500001d030280c02c0d800c150240514401c800e031002c600d10314108090680b0340c050040744130104502440410145407142d00710303600c02900281560100c0c000e000c0701615422414503e000c804209100184c28 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 911748147 1250 911746897 911746951
    0x1427150711030d200a0b0705030105030c031606030c0509030f01022208060c0c03190905040606260c040e0708060a0e100603110d02180315070e0603060d0506040308 72
    0x1140205482e000103441004074032200b40ca000300c800c80c00b90311451540b4008603140301070740d60007811688c03500c580e25418031050505010f18000c0041c000d03400458010304ca01c1c0203500220032507039645800952500a0441282d0301c1c49120390181c0d2511456480542c101d01c1940100807040003400030404120f5407510843d07006c480c41c4941101c603009100040c0900101600511340c0705105001d032841c1002629465004024005041000450444090056042ca8030589000c0d01e00f5040108840d86903220320068035140500400c00004104080b8916004160548002e0620300700c003891145080e06000b401c41d01c00b1288540314103030b841f8001030070601d88178005003e5422030302a561541d00b0300c0d10076005032544a2130090902800c21110500008520103802c0380d54044191100d501c0f812810103103481188a02402070014000030312564a0308801c0921070003106403101c1e41c60b560b8000009078004050304000d000784c041c95080108150b4440540c81c403480c0003c40300071207500d4807600854 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 911749397 1250 911748147 911748163
    0xf050306131208040f1b0f08031206061e0c012004050141070606080724050403020a0b030f090303071b020d02031c090501142715071103 60
    0x7460740302400304034019210f00c441651141c01005031045091103a600c00d81a6060080c0c0c2d051061800f05080c400c403041d8150702e400601c800350045007071440c0104078901e10303040038107058031139180010800f09060112400d11100d654a50019444142c01000c2d140682482807001d038414a414028811800460b016181a204180e69681400030704001462965180111144110b20042e09100310301381155681d80b070f8200c00354007003500c0703813618604581a0b890b203030884001908014428080c040b43c2c14851100d141031200002d41c02c4051000c2035a1703074071681c3c001942000020001060805000303004500800341d1614210042c2c1d2040e100341e0b1640403c0d00c3d02c1c4005840c034414244014060410350042500083c00300076541c1807940000e00d00a81d01c4401942c0031080e42044001e190880000d01c0205000c2c2000c00c401c1580700c01480d400d214102c1c104032008501820a0b80c4104141101c0311461405001c040703656040c1454100c00d0740104804903541d140006501055041c0407601c0d40d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 911750647 1250 911749397 911749403
    0xa080301060f020d1418030d05120a09120f0504080d0e031905070b0705030c0a0b16031b030908090405190c02070b031b07060c031a0d0201020a03030f02090a0f05030613 74
    0x11729002441c40012525030004000b007000d0380300d12818210030b54080c407002d480d9030019102c0655405182e0202506184001c01e40f495851400040401059241c1e215012001044c071b800700300c03483d0720700003138bd914096030308038505a21890380b840c1641a0001d070050803a0358110200c81340c00d4404081100394000e801c10007400c43d04480020400390309060051f119103442401524100f8021910292400d841d0755001d4640c490058140302080a8101e240f020800f03641c0390034004c0c0401c5803410607000103003809184c1090740e5101c280d010300007408251034000000510078001410f01c1092102904030140e800c0050074508103104c03200c103000103550011a107249418504550740e4994000109003260500c4620b902e0070804074001400520603101403c4550320000303811280700440703088000b4400c0c68507000d0b03c003e0522101503a00050171100da250704d480d01140700c0610928440c042e000d000d0b8030542001e203050707003c504003502394503c6060b96819800c461403950b403c0c000d0582c0000141e40a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 911751897 1250 911750647 911750657
    0x5070e09160e01022b03061502061627060311160219051003091502090102030d0536062203030504030512041208010e070e0f0307080a080301060f020d 66
    0xe01e01038000c07003190b000140165004411182080000803689a4a1200744058030b20360026160f090312485c0301a00f02101c5a420703810114002079558030000d010f48180340342c0c458482006a1042030346130342e02c00c004000a10128040b01b05082c140360a4020720001c81e050007041b113403c01c1c000003952000361000c043e6000310029902800510785402542d10401c00d1280f0010620351501e10304558003c13042e0b540001c00c0c810505240025094a0301c0501070750b40100013102460ba0300200365030100303a070f01c0700c0000c071a00d895210440752280c6c0142174035456009a107001d040001e8502c007807101d0380040c09803040340e40d600440320500710079120894241ca9000032440c0c0440d10951290398030a21a0400c2860301c01301c034120003941d00b4221422600030b201c10707001e03980303c582c014001c50041100d2102d0b00e1080c14034505c050000010054518011180141c429a240d030301001108001c0010b4000d40c0d060180a04042150f94001d000eaa408035080184081c4001d10000d04001c0c0d400300c940e20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 911753147 1250 911751897 911751931
    0x7050c360a020c1509120702013e010e1908030c0a030609020403110310050118020f0d02030c0a110a020105030115020c121b010c0b04081e0c0105070e09 67
    0x99040d414402826141e1015400d01103492243c80c2005044100c1c40310494521480c50000019880c0c40c0d025241d02e4600c00c4107006000050340c002d615105078410031900714914505414800c240c0f070151007040c1c02c48a40030321a00f07924030010340c00366519117481c5080daa00c8565040700ca44006c040080024166042080000c1c0c290302401c1c090600c020aa19010414660f104042000d980294101351039545904072410518501008800544442114180001e42c5040031000344030004441441040d600040e50724240d117981d200f00c500c01c0e04002d80440d00c034141480ca02d1351a40100b403c140100f9901000b0300c07845c240001d130a01400303605950310340c07540c1e08000007001d05d081030756514000e502c00d520410300603984040d07031800c03c400c151006164800e1030440114034030f05001140c0d414018842200004604401900766015401040301d5039154030842c0d9203080501c03070507241289400049254011414190441030207800b45584010803010100200030315030105690400e029080002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 911754397 1250 911753147 911753239
    0x80a09050d0812181203161b060c020a050102301b160203030d0906060504020a0903060c0207050d050304230d02010e19030b09102d0204030807050c 65
    0x48070715444180410032041382050303200204c0c6010108050071094100c00300c1004150304040b000d00e02c852159203400450102000d11400050001d808043c1a06841d110f00482050080054002c0c159200d0021941d0f001d9105280c1c044800744810917443c0401d002e02c3d51101c090002030203010300c1a044031100201c0d891a100102c5030701c14510807400c401200414000741c0e80a0014103101c00203140d002c80e4424003450020708640c0340e07812940c81948140012540181c3c0034a4080640390320060016820540d023030242d01d084925801180d024212207500700400401001400c120f43c021032510002c100200ca50002d03c500e0400216002540d0300210400b641c840c500b4101303488000351940180c110b15826514645d49941c106864082200e01800103103a0700b0003200c10544020002001605480d00304828002450700ca114101c0960403200701d00018a17504540046078040709207035803000c00e49440c645400889420078030501c80342c407242011400300e0206090080e900103d000d40404012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 911755647 1250 911754397 911754427
    0x2060f04020f0a080604021f02070512010608010c180603060b12070c050318030f030426011806091208010b030a1a10031d0f030f2104080a09050d08 65
    0x81007664081d500e00c040e41c5443d100c0341c680401500d8202c0142ca02032910b801440000711790320500052010342d407161030714155808500304058800c11165812050114540c0701e000d8281904014499460301011858180c1c0200007900c0c00e000305c1522140302680e44000341d0482d80b01d40705103403003400c040001c44104000214071a03070191250408003000d9034540c84140c9507802000e5690030b001080085041e0758030303040100880000840b0021450142000703106401490340002c0400030b4803600020140d01d00702908260b03003105000303d135860a00001d0800b140905202e20083e9000540b030302c55007801d94842e031206e40c1a00c0c50000c07001e10750385034850b00740020490b4200d4500c40c80710b103200400c440d0b50340507000c00600c00560f902140810722494900342c445060070411403213601540804040d00c401206441d41c00c07154034034040d181e180f1000c201c42030001c00c00c455035924000300100010810044094042070031b1079030340d06902139140c3c000e0000387c007034295001c0e014010600200d21841005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 911756897 1250 911755647 911755651
    0x8010b0105031b07051b03070905240102190605040b2215020f0403111002032503111c1202040303020309090a0b0307080d020d0914010807090b040e0402040b0301060602060f 76
    0x3403d440c07031510f800742c3c07281801c00c9000c021070b00d000036100314840d2081c40c0410104000c1c0a407114100100d0401c0031501e03000008881c1c002410107004080c461981e8000e006610b0700c40b251a00904d0032000d145003401c02031000b00c80c1124030f40c041c840031071185413030501e50091030441c0c4514102103120032388404040812003080d100b861074080150742c5c43c0c2c816180c09400118031a441c510350700c1e1840010040984a980e6403082150300602180f02544940d008258082440145a032944070003401c0c1201d01500011441e82c0c0d81c815500000d000f1880c100ca40201440d00d6510441c882c11040c582606a1243e8400900141c0c0140302b48a09860b01c582c00c0e5030040e4070540c0005018104201090030311207a42e01c03001c8990001403c4091403601030203e8000c00300702e854005903580c02d000c40445003c0c0306000085c100002640000c4000d4000d01942c1c020308180d6108546650740e6151b88142807004231070403800395080c0742c42403041e030605008002c00e94100d40c025007416030b00c0d2826180d0300040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 911758147 1250 911756897 911756941
    0x1b031b04090207080c010c051c0902010203250c17100e10060305062d070c020f061b0f0d0906140d052d06010f0c053408010b010503 58
    0xc00001418010910007402ca0703510801825845104c2c00a2650844004684240c144001000700c40300001107800b80302d00b410745150001030b48856a00040b031079809212100303880300e80c0340e407030b01e040e108495504204410721400e80880c900303031680b2442002c046900d0a410751a80450301141c044001d5820039000e001c40f0714110b070342d0110700040d1071040c1c6480c2d92042e222a0004403e100702d070503280300c5060404c0f100e5402403403828100c020310503a5001c000e0800d01004003219184045660b5247c5284028000800003074a40c140b00184120042288080749160f109014441600c100b0206000c54511f445460301803985180c480b040c0d0b200c40040104203049581000f00e84801e001d540300f154012048081c07002200c60060800110350f05d40d9040c0d0360b0401c8007903001c0049a03a4030880c00344c2c0b41e4103e490041c0352000315107003052414000c0702115503000b40500c1e0841620034007601900d0700e401a2100b1400159071104010308880c1c0c0340c2030060010f101000000e04c2c0e450034580310343c500700c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 911759397 1250 911758147 911758201
    0xd0f061a070302250e0903031303030203070201090219141f0e01120203090d1b0f0210140f071739061302040b010e1c06090b09060f1b03 60
    0x10441084211001920b11404016943c00d07130305000710507000c00c040d54000780c0e40000303600d58204001c42038585885076034010101a0000b00251506100303400c401c034000d03800b0301000070302d0101c02c5078410480218000e01d24107000f40c62296407031f494482450b640142e000f0b01c5105040490741011501d412885207880e06004415000700c88488445c030003184210035900c0540079000100c40c005080c0140c2514a044140c012001c0d034003c80c106c130301c003440f9135a070441d181e1221b44010072050721607400b1404021080640401d000c0142c03d101001800d907244520441d41d80c40c1418100400d55014421070384000d412544010b82c4c2c1014018922061400c40303201503500c0c02e501e080c0c610300d0124119020142c450f0090b400300700710f041038095030032a05803d08111440c0d0f05040302140550f001c094800741c80140480c01c00060120700d60200503c96042034501d0745034034040f0383d4036a41d080196214998003c2d4840040d072101d00401e105158101098000c0d4a55110742102c8004074000300911001c1d48 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 911760647 1250 911759397 911759413
    0x30c1008130c2103180303080a0b0301061502030414190e041a011d0105120c01050d090209070203210c030f041407080c011220130e010b0d0f061a070302 67
    0x840807076980c964810f00d10400d844150001d240040840300014081c01464003032420600000c1d800c0000941d00840300303040018203031094000240540001da1142411404144188012507030120051080e07640341ca581d04480d006010070b0001c04940c84924211807441c4510a2003801d428a0800750060300690108082c1c2d0305220b04095042c80c20317400101c1d4098450014842280840c1c1320303500415007150766094080001d8051504c2d402075034159810040700154442d031603189035109da00b00680140001034a480e0440c4080e40e43d0740070030000d000c03072242d0700740c4010946d5110402520540142c8a424110b85a041c045d608405c80948201d8005031424401c500845c4100b20350720003408040000c00040c000307400003401e021030b0352030041040c50405840680c0c210300e001c0c030001e1592012095a80d50802401c5500c036012041d008140c0741140c0c0c1d000060b805050344041d140c1d004c075000c410010210614040340403504036201e1700619000b054945d4a82c1070710310300680399143c021b00544000c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 911761897 1250 911760647 911760659
    0x290f060d1401232a220905012607060905010c020f03060406023001140d0501020d020a031103060a030305030603010605120102070c0503070f0b1308010e010b030c1008130c 75
    0xc10303450410f200c3c41c0840c040800c25110420350a2102005070034030b03800248464644c99850034413514590303070b84460070080b410002041e991801130050002400030482541c551072030301c0c0540115140e110085004040384c0306111000300301c54046907140e45520344520701e01401900d001e540340000740e070300c605a040b1503500750300e06000a80c07040d40709440c0165240d02500d025140703200350000c04d05030154031640c400c02c003030300440803c1d042d50483c501c1085040036020000b40c5000303800c40010700b20750002c034010140d424540c020380a40031b080d031818000074401c0c4500c40402d0104840d0b5a9011009010400c0442c0c00f0780c0003190000380207000860070303645940c086211500d003031044400d9a9400680907080c0110108a040504001c0b40030b04412031078000c0f045201117084c05180c10042c0700040039462a507883c0c80200040113010001d01026800704c00d45030081440c99400380c040e000b08000c0c0c43c0c00d40381c01e0320000249c89584d11080ea076916803100340440800c5403d801c6880742030010000c104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 911763147 1250 911761897 911761931
    0xc150b030d03060315020f0412050c06040e07021e0c0103091104140411040b0d1103010b0405091f05010602212104060c030b0d06020306030a290f060d1401 68
    0xa07900458801150761865841c0800d0700809410401040314814400703200b40303540102c1140d040f075140400040c601015420807500388102d9401d030030f0340b01400050005d801001d154089203c4c0c100f94081c0d40440d01c0703c915040c01d007100755410644a17041861070382c1556000368411400f00f4040c0107040503144000b00030a007180d070090b13491610402c0c0c41c0100410030015940ca20903000056a0500184400c02c01107034000700310740d00040803008800d180041545095014411500780240f05115074140302100603110010b00341c80100802030034a40d11005001c90007400e04030b448960050035501c0303050004013140c06503096090b22000741040203041a003440c02d001c0320b4200303261003039000c3d500301441c6c0a0110f4041c030410038140742c00c03c0c1c41006641d803110380494189802400150392999003000190070b0644c0404000c1108207161200d2012482e0803407c02c0740d14030038030b00110442e00e0344454480c506030100d4180e640403914ad03181d00000741458138144d11140384a0008504041c4415425103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 911764397 1250 911763147 911763163
    0x110703020a09020c06060a0501080402090406090f0803150d021513081506030d0201050c0405040b061c05060a050121020715020a44060a420c150b03 65
    0x540b094020a8100300c1e1030041c061140c014a080307401000c81e52610001811019008201074811a2000d001800b2f115071074004030005ca510100320b0302c40804502d008481500260f0700c4c640c0410031f07951082c6081c10031030203255409400900d007a00c90800c410f04104103510000080174480321028001403104002c1001c01020005000204840d01c2d200d070900d443c02c202c001440d0210782c1454188200d1030f0803c81210241c070f0080d02d0202e804480d66001c41d04a01c03915640440980c1d02d02c810540106050344400d0282c0b0044480c820469650401103407624172003041d5441e144c90440e21030040e10195030061503040d10600700d440804462055620803030304101c071540c01203140fc041c42d128900714003400039808148880314000b040500302400024540c3c40c2e601c0c1348035000c503d012500640c0c40c60514001402c2c041d034141c03044403001805180c154818402c001040403031240041d010700c20030603403600070070895544075450912611490710200194509600c000d0380c0b1040082c03152010f0180d10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 911765647 1250 911764397 911764409
    0x1507080903190c1208090a47161b020402090603040516080a0803240d0b01030c15020a02010e040b1e0a06050c2a091f0801110405040203090c06190207080312040201110703020a 77
    0x20b0000c000c1c0400301000a2001081a101c403e085070274031219503000822040401d114075451500701e54680b004c14001e100d60003090750320a1003c001c00081000c0041c0c0d25810b00818045440c60564500e02036964450034007005091040a02c0040d0310383d5280b80848100d00b11124400502424032030228070304c1d48403d901a03034501440001401072000f101d14903002000b80090500c2e40e0001504005d48814041000030704008990082032403a03500d0390041c0e031100b00b009100c4181d0403c8014008048000422560301034800c0c84070004206002c0d405494074110342c0d0029103500340000514100710b410120303d03142947c5138500c0380c038259118544000d02c030b4004680380b030444260034402201c41564507445203aa9070f0502041260300d00300d1005072401c0358000d0300c0c0540c490702e03150855420107039401c0e03000ea004040031a030819958040d1401803d05040c50f002d459003161940b40903610391041c1c02650102c1d00d0203101003401035100e207400c0121200c000084d55041c0e9160313400503140001c40e40c00b41e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 911766897 1250 911765647 911765753
    0xf06150b030f160c02090601120501090b0f12030406110a06020304200405071e02120c0a02010f02060c030114030f10020c0106081507080903190c1208090a 68
    0x200c2441110580e55800c110070743d607401812840060001c180e038142030070082c007443e0b580740480e1039a40122012410441c10030b805101568447c0000790040181c4020144141240c000402c03880c24004508007407041440040d44c5018107040c800e403012028082c0f4608144145070580b000b24100784007660040b40300301c070465090b0300c4403000d41700d0b40d20180880f070b0720503841c000038403010f140c2240c2d9020742d01008041035101342c1000c60b01a03003040c40c4601086524880091102144900071610303129561003605c61101003009050200d03645c5000302d68400c6217890420040c01090000184540300343c4000341165100005600c0c41d5042540c80d5076190405d07070700403440700b40825081c0114802f41001c0b00c01069591031800c294602140b01800402c284550100400c0c1d58082c28401c6412064502c60312210520342900014003200c50000e007512036003180031b20700e01d0a900c2080103600650610004003200c509a840300050f007035100b0b064003080c1030101880c4100e00b50800c071042450000d0000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 911768147 1250 911766897 911766901
    0x60310110a03050603011401050108070c1a0a05070207081009150c030501150c050a2a06020f10090317070e0a091b0804050304060e010e040e0606100504050303070f06150b03 76
    0x3002d400d40d4000b80c100b6100340d0500500c160040d10f005011811102c0905e00385c42261036950054400040070711005d08407500c0201140c0c40c40c07901c00201400391000440c104034541e04c546c0101c1e1190001d0082c018103400004032041c4080c0c043c3c02000c0e9260040005030002070014a0400440340c58540d00001319482f000100600000d044070020042004e091a044400c20784e59050703190540c4d13220040c2a4035014440316841c003030b100840603403c5680d0b03d10403612038807802c0103903079601c40c5094020329108038812818410701c0350040c11034259040c0c403060701100310700600008111b0000d01003410485100300b81c4060f41c0d10240c00c03000911048000003240074518906030007000e0a07102413014050144107001c0041c0000003100d040744c21501e05402c82007515001242c1c0e8224048000d64414106012aaa00480402e407180540340440f0100800000c0b0034060b1582e00079445144c0d410307001404080c0210b019a5130340440d003442040002070340d00d901510a0500c42081e000501e0010300401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 911769397 1250 911768147 911768167
    0xe150a08010506060a18050604030317070e01050d02030405010e1006170d0530040b060f010f051801090b04060c0203120301080717033c070c0501030506031011 70
    0x8450009005544000c0c07000e460300e403000c500329100d003040c403904002c2c0b031900700c550045484900e24042d0400400d840c2c3d03159540d04005280d0802c54801c10b403c04440b00210f0007041c09080c055840440685405040045000c0e2110081d040140250349554a4000324200c1600c240a1082d4201c401c20b80000c12a0515001c4021041d0000d9104a140d00176110407112540050907a0719000039003206500b4000c11461146124200940341e070a2130410f10300340010800d103480c182d48140c100b41c644144081c0c004004407001021919990040354040004543c282c2c2e09401461100606040014405aa03130030341d171500c0d9015602180014071410065807c6103000c1c083e4950440000c40d41d54110b50426074a02d440e1410740c0f043c01c07800c02007040c1000c0009428000d0350019004c1242a007014444400010702c502212607c0310054444020b920081d90310702e905407100c03542c014082e00e1703801d41007a0054000300806002203505110b6250a0685000c0500400e00ca1940c85c807405a01e40309042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 911770647 1250 911769397 911769409
    0x13081006080f030301030f03090b1204110607020d0b07111516020714060715140601020d050732030304120305010605091c03090906090218090129040e15 67
    0x140000045402c82406640703058400070a0304d06403034000f074508000344918502910302e070700b10340e01003140c009001c2140142010b0019a040c425070089501003c45800c00081018512070708800a5000842240101c0825800c40103d640b180b0300382007038000d10002c10465442e110b51085d50752000c0d0030329401c01c0b40c20200c00701c40c0109802c290008107a400d0801e00f400941a00c000003050044501044682c24029022809446034008403010400c04d041030fa001030900c0c3c4210390890240c4a036032020000c80d40f00700c086401141c1c102010808021360032100113003803951011034a4410845c01c55000b200c29042c002103000d1446290010f0010001080150075520142e014400f409024071415005490395120f50000c2c0c512040e511070768003511b18043c2c50320fa00f01c0c1c2007160707494685040411898202d0b0f0040c10b0320a5001400e0240c072103000100481a07000340141440c84a00c0400c04409900c00b5112924808643d04054185a01c0302045681034004890030383e10203101e00c010b00381c40d0402c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 911771897 1250 911770647 911770649
    0xe0a050a021215040318150e03060610121107021008010617010b0304030e0a03150b151303080f0c10090209090109050309060901200601030c1d010605030c13081006 72
    0x42d00900380c1016080f212081d5043d004102406000765003034002c140491000c0a24007401c0807080b80a1080b600c00da0042a00e0945c0c69061b020340316800201f802c514009618080240701961041c0d44446d9801081c4054400b11000c1d521045007030000c1d03030040e518010300305504001c59031140c61070b40c581080204034083c0c40881d0701d42000a400140700104244040b030343c0c03054160900034008451a808200041080d83c40980380c5040f9240e0714108110b45d4006681820303048842e81c100048440601d0742d90320641c0c07404011801040410400a0794200141000d204060902c50420032038440703490400070f8502645000755a1040403034114a000645160050318200007041840710319910740d03503a0710a42c017005120f0400422160102c5c0c0c440d030120724965880308140404141c0d0420310584e1600280030407030749010700351000305240700c18528000400b8002481d00340c144c0d10b0148207030303015800600315500c00309080280320b107c0d155034013100006200000040c10050012001002140d800d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 911773147 1250 911771897 911771929
    0xb130b0f0a3506040605090f0f060702100e1e1f0902101e03051005030a060614060c0d030510211e052d070b0403110f0d060f0e0a050a02 60
    0x2e0041e1096880740000300940d0180c1d020034000b03890b41b200400180b510f400540c20f804603210f425046004c11001041560194046408641803e84026007150030780d03030142c7c40e85034940c2c80407080b40c0800c2e031148401d147c64407040d000d407408008031401075040c103401812a000c80030740300d14414045052036085110317840401d207002d501c040720720403051182c0c0080310009000c05440e840814100d8050400c1c150041900030100e40c640411071800074080c000c0d620440c2000e0503103089144142c24100100c481d13a4200e00003a02c0300e01803c0a0640040c04041c140b00710a85410501041c1c1d0a0000030489814070800a0f004405026180c011501000355605000d008845510308000460004283c003503800d0306501070b030184000505007104480c00640c001e11610440c640022250500801082501d001e9010200c09407421010300c2820300105a50b41c0e000409103000d5000706003d50f11281c5e040d541c04070040b40c4400ca1340c2c406031a112400fa4203071501e0b00110859002c501e0f1018078059980c81c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 911774397 1250 911773147 911773229
    0x203060d0b040309120b010806010f050a270e154203060106080403090503010c171009050c220608070518041107060c030b130b0f0a 58
    0xa89100410a0a020a40028050140303000450300301409006184042c1c4940107000303005084a0500d45c040c150207210782c02a17405031034004214160391810142c02c1e00c60150000354428603280c05129402105401050942003101c40402c41c0c5205009240708000740000812035441d0302d0036000e140b4040030b00000d08400e0a06c1800e84092450441210015040300d0b20607142e0034054211101c19040001c1c1584c035010741d80011840c50b07045121940550301039690560030035150380070f060072200380075002d10214418107070229445d541210300c1d580c00303654103815051803170351918040c003901c0c0305a4007000c0d0540e0100f0040300c40b82844240c4603a81401364044d1160381c1c50032201604084016207008100a00041d4201d106094107000c1d0010300e0020f40108000c0e00c80900b00c5050303070400d00003184c400b401c1880d0340400301e101e8000c46620150080c682442e082039034120700014060060802c0d00142800d01c40c5441e80e41c0c2d030050f07100415000c04046461242d84803524441314070b0040502e901c603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 911775647 1250 911774397 911774401
    0x8030a051908011523070b0108150c03130f0f0b060f01180501080c070b10240207050105090a0905010b0d0e030720180a090c090c08131e1b090203 64
    0x41d20031a070030342c100303402400e01701c3c0e43c0d42503840384800b0750401d03651000700d06500003662000c11252200c0c840c12500391005585881c000e0304240c02914a085c0d581c20f501c07500c20300100f842c140c1140031101455108a07898500703840a99142988401303081d20540310f400101d410041c4c1030501001c1700b0807d10092902000304010140c242528507114010141000101000074880c2290075084569058001900c04000e00c0c04415180e0000418002c1500310450400c4c900d15201d82c03803280c0003401d81c9a80281c040c00d824540115440d401c072a80da140e00403041007001502800c1c500c95035019005261080d80d44038103140c00c0a068540e10070328940e450f030040000c2c401085100510213034484241c1000d1100040140010b8550740307115000b003d01c981c0307250a1012550337180d40901070f0300b80715031a4150a580c0d10148802200d15542c0c1c42d1001c05d00c14400211180c00c1c10001c4204580302c0c11703058049242815509051066900c0115028500d82c40481d11140400411200800001c001503281d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 911776897 1250 911775647 911775659
    0x71209090e0610050a0f15020307140102030a0b01030612060f02310602031201090203090c060c0d110106051e030a1a010906150507060c0201060e130c0801021e070c08030a05190801 79
    0x905152040341c000303810280441f60381074404d108540e03d484e089000008a5013803051464002d42c829101045818949452000c2d65400b03402910203c2d1000615106001c5d035a440c0c50000d0001009116240ca500f007141c00c5184103c8001c000c40048503c07660412041038000030303158646290403a40542d4002d200080c901ca80103440c050544028803005a180d0312160002c6140c0072024240030b52180001c1120580b881c2c0c0003031140b000030144c0d0f4420700003d1101071700500301c807114055141c01802030b814000e101103003201003503402c6401800b100c07415a041e488445040128644d00720540c3e0011004010100c1d917070040304007400542c8401c034101040f482c005081c920518000400e1213840700074900d1203500031f5020500501450380e0350104c0d4a0040039003c1001c0135260700721010080c0d000040b60b081014401e444140310110700301100c3c8280850303403085603004a1011141140b150b034001c1145681400075107260b0355640c032002e8070f90152804180242107010344039010011010010404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 911778147 1250 911776897 911776919
    0x40209300c031b150405030d0806040c17150d060507080618070207031202150a0b0117040209041b090c080711062e080601030c08070b0708071209090e0610050a 70
    0x1082d81204d00300150045200344802902807039000c50fa050043c400c00d81130f0f00360882c00442c0f141c20106d030304000c603c3ea20a0140c40a2003c0314031440003001080c00280328040c0e000102041c8200200f80d00356944207542c0384010741d64121240303c00691138009201d03c900b410394584800c0203c3c0150041c45181c4540000c0d681e100c60321004d4450034001c00c3d4a0f1145009100500902c0c2801c04800110315108070102c1c043d00c5c55004042c001030385600d07088140f818100105e405a5801007030402c1603211615074101450040c282e01d10a105800c60000b00c1305c40358420b062281170f0a8a401085240640001d040584d0483c2c0c400703841d8101c541041801d0300364544c100c0b10300d081144510101048800104100d980f1500103841c50b104440000c010312045c43c4144080302c0c0d0702c000b02c8070219110000ea040c1402075010091420b1014001c0ca800a106402101050341c900c0c640f49c0e42c060b564064010940750f0200b42d014582d0009000d01486078816500c41016140030b503a0701d00728516102250b05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 911779397 1250 911778147 911778193
    0x110c0a080f0d09031d190b030601031509060905060901180e011803050c06010b0408060a1812030203090d0503070e19030231110405040209300c03 64
    0xca04000070500e2001905000380e51001003004001c020ba070000b40750140807072010262024001540d515080118584121500140200500881001c91400c0d0095425401c042c0c00b0a0500d034951503949084104c9414400040900c9080440c1e80c1d4508a0000125074028042c030380210300380c00c014000c0581080c15940941c00349000041c2d441040d51459004100310144111184103001845c07050650100107449a25505030607240d643c1da9400c11000e40e4407451144c0c400507040f003400650414500e52158191103200343e05485100c410742d07101030400303101c51300002c0070a60100500144070001c11200300c9811305030618900e1030900b400050407010b508441c071482544064099030b1040100e40e0004011a030284c04198441c0b61038418144c0c0e8052440e424011042500c9101d08001c41c3d80900305000720800801c0385414107020602001e90300c4846066000004994996607014400c0b012900d40d0111402c03010070358403124030184c20f014080014078441d5110100240600c0702d1882c1c004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 911780647 1250 911779397 911779403
    0x11190c0b0f0709210213060509060d080c0d0c03031404020105030612030705010509060f0a050c27030f0304050103060b120a18080d1a010c170a1818110c0a 68
    0x40095521100111580e00241e008080c221141300a0034450090165000708010710843e050079820307100c1c3c10f00d40100c1e1418441c1c940e0012000012440030305054034400844e40c0141a201e1402030a500714914001c1040850000505004901c4040c941e252040201c48010551036400c6130405e07800003030040c04003a1034144114640502d05403480010001c075420284e101000740500d180c298040341d111502125020304c6401c1d02d81c001200010302d0b203e21445840400000c43c00c00301039500111b104908551038184080c843c185890040c0d8042101242140c5808025945d860908000505039501c990240b800f848040c410601c804460003060741d40022680c070700090080c800e40c1d0300c8090f410500c0700a0b028038030011303c94040010907041071510056440a4145242c840801164107052011010700012040e442400307200c00314a005004a035180d05d01500c1c4103201e00e0540da13240c586507025110048042107407810045044c050600f06118000c0458240500104d465440380c8010b4030003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 911781897 1250 911780647 911780671
    0xd0e0315070810031e14120f09211f1505100215070305012309061311040806091225081b01020d0605061804150911190c0b 54
    0xb03035600303da90041000440c0c01805001070b07400700b42c0c83e8403101d072500c9400361001e00130904040d16400d4001132141070042e6074100c0600d014515500c05a1710703004036007096071083c0c001000320180d03500d501368500607844031005040340c192154031500301e000d00644103c100342c0c142503c0c0960005107135484003c0700c0d015180000020302240c422070808131010035034600c11410a090104203941540b0050685402503103c071060f200c0d95408658601140420790750220125001410030b04225504064440001230301166219801070220251b80003500600001d0f400201080340c2150204608103d019085841a242510801400201e40c0310100d5240e948051400780404111144003211451040b1703000b0817633101004c51015020758000c0c00020305590070070401240d5403401038202c0303a1145003c400e030a0f01d18902d02c00e1001030555208103183e000040030000500c0001400b0303c207249000000c00540c0c0703891441003000c044001e45045001c0002d00480000005e6078a94106d401420310026 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 911783147 1250 911781897 911781901
    0x1e07021603080d091a0106020c150d02130515310b071b032307060813031b11011416060519060f05040f020c0a06050408070f050d0e03150708 62
    0x220f81c080e00030103a00030f14104010441c8a2102c4404517554180c8016909a07400341080301c0400c1b03046500b0080006400c1020081c02d02149065802001108094010280000d0b52440084d10481e04450845c404030300024010031101192130130312210362080400b12020103891030350b0413800b410310302071204e84850000740c0c2c1040c44184114041901035000403000410b807070740750070024206542e406400c11030341c40e01c8240a410740413904805841c082d03502c074a240d0b0b0740d900149080f0200e80b0380030f505020203802ca040f9402c06565000880501917021001c494408600041120169000300115840c0a1103010a40e0110f00840211190840d80c0071aa41d00c4400055501c0c460605050079501d2a00e0300c001440400f4040380c1d0200d42040b41d0801811101c407415400341d1040484412040d0480311082002a8180c0c0c00150010b000f118660f0030021282e592428903e8560802da134294809054000c415901090000008400303801402c0e2040621051115000300500840140010140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 911784397 1250 911783147 911783167
    0x5010905150d1211030c0613020405070813030f050c060a09140d020d0c06060b0313050c04060f030b041a150405011d0402040b060f07151512030f05040506031e0702160308 75
    0x2603414001c4250191f030315a08001c4200801030203000740072409941003000042035107000b030300c600744980d180300740b07030981200955400c030740c21724000700140e0911409200507440c03c5820091503120b0388446400190110907802c143c821040c0c4000d12001e964442c000041a4683c00300340c0401803001418a001f007800e4a2a000015181c980c0240e104060044100400724910000040e07400b0301407420340380b00c42c1101c0240400d43c0d4040c012584c2009040b1410000100301c0e01180c0d51013402003d030503190706802c0044010440c420303104841e2640207803c1000c51840c0a1060305c0c010043d8160300354224102d50a050a6040020806845150784d10800c040949801040700c5010494058aa90b40c0c0024900f0403128000c52000c802c02504c1e0203604c0b000010110749030307030030b9038040ea030040801e886641d0200d40e01110180f03000d04200040c040001d140d25920044c602480ca00410036141100421040c00ca2410080c00035085501c000d044905d12a410642d500903203400954495903449013076 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 911785647 1250 911784397 911784403
    0xd0f02061b0a02011e09292a060601080a0504030c0204020f070b0114030721150621020618031617060c0f031306090605010905150d1211 60
    0x10502000c10020121a0001c66001051450200d40f00740c80381000d084d15801c81000b0801c1c40d05410340881c03811070050005903030f4411100f0601d240810117250020b4a1050030b10305400481035078103511864050740030000c0c0c4040140351403007400d80003401c0500c0c090000030201d2201820364240c441d91240030609251150785c03a0441c0740e0b0081c00c1995100740f5000000700c142d2140c2070956104103001d002240c0e00c004036001d075120100003001840c4450600d20312005a10540c10070f200c4001151007107030005000c405801412040159002442503e0840e078080e4080141d207800c00310b5240700300317900010794030181525480d554054170050751034904004a0300d4800001143c003103101100c1d80004101c0c1c04004e000f140a859901540c055171203101111445000c3c0c100d2001c060f503800c1c0001000000510b542c0c0350164000c1101144550154891808689007030300250b4119840d40c0c02c002940150981c451407000c03003540c2520182105071100240112900040020000c01207607508030800d01b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 911786897 1250 911785647 911785657
    0xb0d110d0b040b0a0c080609040b09160605070c051f11190c1a1204121202030411190e04080904021902030306010f0c030c03112401051207050d0f0206 66
    0x11401d0115410181841940c0d02001c441004616080610030f2188501c0f0740c041902503500030f01b5101480e2183d5030380c115206802410460288a48500a100c075543d68041e1700081c41241c880c0b0742d8940550800c0f82060138181c200e2400380902d0300404411003046e00c1c0940001c101842c10840002c40710750381c90b0806070b0b440c41203110005160751a00506c01285003030001c50744c50240c5d202208507104601000b5015030000c442480c41c8a0b0001008209015000c0300071940f00d28000f1140320515803442c0032a08103440507607207080403034032540040c144400b84161909985a07003460700c525000302000c800900031300040c0407000c0460380b22125100c43d0181e460100408400d00001c0900300741c000d549030003c80301240003610320001101014000d0b034500c0d0030144c150350741804180054800b07aa448085034500030591064650701000c2107040020a481822111962051541350408001e6102e02081007000740da008400100b01c41c2e42d034241403021081c0c0c0040b608045050324000140c00f4018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 911788147 1250 911786897 911786903
    0x702091b0408010f0e01061a07210f0e0a1512110c06100501170a020711101d03010608150a0603081c051302130e01020403050a0f02090a0b0d110d 64
    0x407401040c4140103402880c0c068812001c10000100020f00d910700f41d030024071429404101040034850985600b100401c800b60080c031001c001107200c03016420700384901094880005602904a0070f86c0c030351001400c240b07813000b200c240107940d062400070700407150800e080400344003221200d41d5000b0303aa074010101c1c540542c903801c0d480d0075003250341c06d032241d800b11460486c00d41d080034081210744c081c42d0122401410312520348865500c1c1d80030480207500c400c0d03040e00c0c040c0a01020403069a11380b00a002d15814039680d43d0300040300c0c1d00319000030070a82034000713109034180764080c0f1020000043c08030703049030a03075480026910f880c0701d120028042d54001500c154000140e1501c0650b2006110003480103002d0200455541c41c0020094070074131403002035200564103510043c1e0b58040e080242189c286800040c0f4041d034aa90301d40c039144420404994010140c1c5040095180a554890744405043c60901209540a0018002c9120100010903a108105080c1119103401c410307080c036158 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 911789397 1250 911788147 911788201
    0x41205090319050607020d0c03020307150b0904050d120905032a0703110909010b0a0608100807180b0a0609060804060e0607031e0e0a140f190b070e06070209 69
    0x4180c1486a01c9000c05c81c0c2c0b520240c801c0041c02c401040c82098549400d0350154055814a00c550f42c0f20300200b03a007103c0704035889444181c02d0505075680d40380300e03000300d01c03580040180c403090b2070024141d0394000501c142c109291018000c0421004401c03152640310100340031207408010704406050300e851012549503131140100c04001c0089407400b204412400710b50050b103a5480d11032240c01d035070009513a15003012100b0000c22006018480c01900300c0601ca01031117500d502c070a401841c2c0380380c65004905d0443e40b01c040341c018601c64440ca0800703000640d58010300d10f0408802500b0700781103100b036104200303c1100050520100341e0000006014980c00d803041810a0b05000b0054807180d00ca2003006003802c0d003c2100003a06200d90342ea84555080602280c0b501a111620000c2803010442454040c485c0704000740001400509004121007400c110007201074101400d00f00401000841802580040e6071030607035900e0162116558100c841070310b1a910040030305981c070070449010f00440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 911790647 1250 911789397 911789443
    0xc012d020120070302070e0c0a031d0307110406120506070f02100617060105010201051905060f04110a03180b0a0e010b03070f090f0b0a0b0a050702030316060f050412050903 76
    0x1010000060180c1c40c040c5e400c581440c0e480f00341d170006484042d510014a500100505486203001e078100341c0b40740440314210440841c542500ca402c41c1d000c8103040700c060346504021410340c40d141c45940058541c00300381c1d6149002641e41c2da03a45a0010300550203100142d9107100b89c40b0f100700b00e0100d412192000510402d03585090604604c4071152840310300303020300030000c070b140d510500ca1107100b40c404400c02030b40301342007800d13040013440003074102500010019002c0d0b51130388607130281d45d220b00480c00b80181d442541000090445003015144400c00c0c03a400035120109500c00091904074049403c0024031424a42400307004040205845425000340d820004000e00006640d60443e51a29400d204400c4602c3c1c20004136508240032691262603104240500100e19002d407d080200c5d041191804c001034000a01d540c09c164074001c80c01070907481c1641003040c03a01905211800d1544103110504181c0d84084040e5141c400740f004001020401d080b1070b40d8204009030101120664400c0c00c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 911791897 1250 911790647 911790701
    0x210a180312120b130902010f020c0a090911090c0405120d05030712020d050c04050f06070b040b041b0803030406110307020d030b0f090108060a14040803072d110c012d0201 75
    0x7804540d00c01b640860200f004148049001003060300084c1e0005026000240c200f5480400400740b102c420384c0c01500324402084039896a031031490060000f54120b80d240c074500f038204a01020b00e0542a02d01c0c1d00250b56122003070307070041c1c01e89030414600c2c04d1001c115918030100c54000d000700402d40411500f080306100184007050001e01c1a210b050741c1c0382e020154105c00713005862044950090070348003c000018042844024070941140c403540c1c2c002c004827251140c81d9045050b0b5000039201e03400c0042071108000c114801c182010411041d05030440c6000c003c0a502c5124242c0c21206164456290441355078801510348601030004042a140756112120b241c1e5503401203e04003003a500d46041c2046030002c40005602c00da501c03c0407185556102c5400f10f60b40185155081c45003403001c3d06400d400101110b80a85c2c5203890f0b1344016400c41c011000a203444104c0e40c200b4140a0032030307101585c5440800d00d481d000c0307a4481d400a0481a0f170b940403401011048012840c1c44071000000c0d180c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 911793147 1250 911791897 911791901
    0x90506010c061e06170a110303070507030c14010c0b060114160503071e260d0e0a030f0305010510050f0706050717010509010b0a0f02210a180312120b13 67
    0x11a03c6216010449207403507510650b952040080940c406074010940e1030000354034240d11180d000741c0641580c4c10080d140d500d80303252400c0d5410481f81c0000040050009401148045c240c055003407901800324445516001a90600038200c141004a6540c040000b1000da0341120181a007108202e04c500e005820001e49941280c4400ca4041c103040300f86881000b8040d0050340c41c82d4100c04940a43c0c1d508090a9652110740d14070054050401d00c06d0398160940c51203055520b0442e48046c1403010b10520740107290200c201501030a152a106c0180003e4451158121081a003800d003140c1c2c6550f500400d0142d03020f040d00c02803c0c60b00340410407940d194001910b0300f910300b268000295603601c54040041414090060318000c01017805051606403003100c2407003045455005807540c44101101d10200a20240e00d1203014120002e00e10220a60245456070394690142074502a1400c41e641c3d80411200300d90030710100041842c02c500a000c0d190300c074044007500207103040c810828030608000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 911794397 1250 911793147 911793191
    0x130209030610030503120a0e070b070b0901270221011d0c130b180705190206060a1a0c0708010906290411091503040507080a0c090506010c06 62
    0x806070041d900803452260484102d80c094940c030074082e43c20036150040c6004c081d80024458821240c94024002c0c41c80d1051080801170021a10829500c06940c280804040700141c0091030580c0740ca410783c0c01c0c0e0b2204003110112408486002c00e240109c90000481c400d03051100d4180040c1401461041440d0540c41b10600050300364040c140e03010720441d110b4844841c0720040c5d800082041030501c00a0441c1d010784589030000b054000c22031584912034a200f442110a6800308a0005414415648001c840c141100b07662008108924103034010611040b1603100d415603000c000201011805060707001c0c1c0e071003417850308212044030b5958104140606081030007610024a8645c03070310341d11401c181001c15507155003182014134450110601c801040b89040c40600044c052098a586a690b207504821007200182e000740c40303041038240941084003680c014080399000032080d5000600c091150003c0751885500041c240e5500c6005980302c60401070014901450071491381109940141400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 911795647 1250 911794397 911794399
    0x2030906010609061e0507022b14030a0e130219080115080105030c0111070909290613090303060515121f0315060b040e0711011802010f0e130209 64
    0x903c840799110415540e100c4605000303244010750310543c203012809040108003043c0301400342c01c5c01072406440340c10203c0b0740c40360324204000742c01e44041c144400c0c0980b50741c2485d0040080c40c503001c0e00707800103010300c0840c60003580a90210b02c0340f81c400c0c0e070b0146d05803000c628a070b070140c81d071810407444000c3c02d01030240511500300d0610700d084080702c0e21805900d8140d40c405001070060000702401900c40c0201e03400102100d100f03403140450410864002e403000607201f5810403502500d2440440e403d21202e03c4401d41007130041040000e02c3da02c656031074441c68040c440c0051103140504040380580f02036045690040302c0c21741522165021080100342070000c2402c034401e503484040c4100812510110000310300c201c0c070b010074808900e144541c0c10305103203c0800051525900c40521141e0b410641c0040c00d004000e1040002054014084401601c800e000030011205003401e9200c07180d0611030064104086508a0b460843c064606101a40801000e8a485050020382c5030069032040c4911 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 911796897 1250 911795647 911795657
    0x19050f040501150e0c0c101107050106090908040302010819180b0604050f011806050d0302010b03280b06060c150601090503070509011a0f04060201140c030613020a03020c01020309060106 82
    0x891040055107054009481011302a8490354aa481c0003142540144003040c07428003509008400d13440c2184074206c8108500c4050980b03a04480c18140d08444040d4071003d049420484002c001510507800c0b1000c0d0f81e42404c00b000941c0321028035070507100018004e44001c1d45080e0107410351141e2030483c1002140700e4626074501c0c2c2d42e8007080c80b0a90b60191142aa150003140061210310a041841c0d400c10001901c0010159130300c07800100304060610003900940d5440b83d09000d1410240300701d00182e2600b508103c1c01e114203400c802d060888058002e04090480303c00308410b542d641046810b00711003103041b507c0482c03d0440446140030140c80307060108003a41c0d0f002821b0b0801240180071214003d0a05180381c1ca801c0980340170075558903084036400402c00c0364840c0c170183d901c007038005480203074000506041480029842002d0280070801010b0050040000e1075991060b00c4561110078240036031203d400e460b00b540a40030f0461640c1281d400401000310002e400a42241210382560312 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 911798147 1250 911796897 911796911
    0xe10020a0c1716022101110a270603110405060d0f0c02070e0a0509160303030905070b07120c0203010b040603080309010c03020307020319090b0c030a090b2119050f040501 75
    0x14142e10384100300080390801d01161048025140040540307000c800d81034680450010015025800c4031540510040d100a000c039014401c0b50303100390045540c2c2d1901d015a507030210442c1d400000d2441030701c500010036403501480b080e20350621054400400000e000f25440f03980d0f01c001c140c00b420490380090745070342c50220008012171002895074100d4035441410080c9031201412003014100044c04040e66100e00b0b14a0300300d10803aa800000114041d42c0c1c005a83ea445290060410205130b109004688050207031001196090800c00780c00f0300182415503e0341070510110340540040b8246030b9109103449400014840070b04019403086000300300170403400901800603400c0340002d8031080300692003448082034001c0420b500082c548803c3c100700c9011a0b480c000321507254000700c1c2007012a00301040b884c80043d0000c00700340182c061106843d0134140080c203080d0281102c80f21401c904030007140818030b201205500070800140b050410300c032502d0100300c07503584004140c904903400d40c81d0142c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 911799397 1250 911798147 911798183
    0x50c0103020a0518030307020d03080a050916051e04021602040b030d080f1504020a0c260d1509061502120c03030601030b0102010f1a1801180e10020a0c 67
    0x8220b07222400c45899003414540e541200c4542c00031901c0c00f10380c141c40200850400b59403900c01314000b9910035918800c3c54601013450b0415903001820381009640245144403c051403109150305582c0191408100341100c0e24071440407120307007450325401c00d100082a25074294000782c888007107402030b40d092104000740820b01d0b607160940035001c00054000004030701e0860721542c503140c001400d60985050301b141c43e40050103d9103c1214680031a0240658a04020020b0204040d1000c03103280800f80c18091404290940300701148040361650303a42c1c049403003000c0480894013511551808118250701c9490440c440d081c050540b4000d48184a90200e0514070b0908440341d0303510350005181183c85250054028021140d00b69042d5501c5611001407240141320301c915007502c3c2d4100c00007204800062019044e400611060480300403401030114410903a04030002c40c8407403c0002c1d220081100680c00c1450012a1400c0c83d4000114901c017164403811201d41c29014005034520165124 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 911800647 1250 911799397 911799401
    0xc0607030201021e21010e160c150504150209090604051f03080c06010e100e061305040501051504090201170c070b010801050906010f03020d03120e0d02030304140105240d06020a0309050c0103 84
    0x48502c80c01004940d002231101c3e8040072400440368028104000100000c2d5616042c1c0003c022200c0e08040d6604200b0007405008651b802600240c40021860000058007007101707120002c240314000c5844030045042c0030702c81401d50107004950b0041a2445840c2e1502c102d2981c0054418070052141900200d490210403200034055100614080340340d070300c0c0c000401c100341c0004102c2680490703400c00010b0594214001c0b11b2040303119200000316403818000007203115440f030400350300a0b490100d1020050b600080000c2c4034911840820040d41d640c03100b03200c0c036441080d42c000c003220840400000d501e40d0541000c0c1c003c0640d5000c1c0c80391a030b2200f400402c805c0c203c0c44041c1d402180c4208410100f07009840324010200f246001080c2501e001d1059483c0803440900741005a2000040005002041c220a15103014200003402a420440041d0703440812605072042c5a403004802285203079200c404d615001036124500755110100d0b841d000e0700402c03040e4400e56442c01000c0b00c4140c2e40d8424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 911801897 1250 911800647 911800649
    0x4110a08101d07060221191e09050109030b130f030f02070503122704020c1005010911300a09031106190f0605030106092009030c0607030201021e2101 66
    0x641c0102046da040c1c500029800114560305025240100000c240c20b5103402204005900c058407900b00c41115041c071100804401820001003111030031040c004d0b41c1c0e0190301141100d4204070014a2601c400130038150040048000078103c80e160180b40041603042070310086520b580d6001d88442555500a042e204c1e446407060310000e550400240b4148000721010240a03081c0c480d14084c000301d080b020404a920280200305142d0001c10790010207691030007058094205104180100200d101254946028941c074602200768803030340b4000c0543d0100030341c00c012511a200c0000f10b041c03c80461004209210050380014201040000444400542c05000d200d20b580c20401c15045189100014041d02d680040038030348501c0000343c155801d01900024000300040020818020500b201520145105401800d0800e1015a10607a4040380e1100030603019103020307075102c80c80c1c50124024410088110600c030401d450202090401074043c1042c80c1c401003912101d460b007403815003000a02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 911803147 1250 911801897 911801909
    0x1503230c01050909072718270f0b0a0203010603050c0304030c0b1306020c031b0706050405190306090c03021005070c05130905031204020114090904110a08101d07 71
    0x1c000a0043e410f044000580c81003592500101485040030350b60400c0186465003070440752035000a0044004000b0000c54894503005e0801900d10f9a490311410340040d036070000e001c83c410b449400305000032070b044034101d0307640700d96a034000b80740001100d00250020301031040040d01d000001185000351008032801140c054903500e00081312581e4103138000034000d00281b000100c5003580000240e640c0003414010710048041d40d15020308007001d11100301054100c00f000c0d80090b20400c0705d56003090440c1d0a448041d80c90341c689000b001150310300e8500310307800104020b244c001c2903814040340203172400170399100301c0303094208081c0354504843c0c0d405065806084000c1003602045280341110200349901e4020501003120310303844e01ca440c02d540201030b0140102610324208001c5680c8541185801144021b01c0b40c28084070002003414000300420003051940a01d1100007241d42e18040300000701501400c40702901e1114000d0000707000380c2e460000454800414a4400440c0070410209480d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 911804397 1250 911803147 911803157
    0x20c010c02130905010b04090303020d11120118020f0406023a080405010e03160312140c0a09050928050402010e01050d0603060912020607030c05031602011503230c01 73
    0x30ba507900c540014441e043c0d040f1103a650325642c01550742c40398014011158000d417030041e21078811201010540305175102016031010108080707030500d0400c400d1681580c080542d000007480b40751118000a2240007442a0384600200d030004e0240d600088235108040659204028445c010315880504501c0107040c81c469081001c0e11607013a4403601c2c1c1944d015000e40004188a0b40d100f1010303086030300900c0301d60704c90100441d15009150300001c102c02c02050080c001c0110501ca180c8501c00e10802400f84c1c42c0448001400c0c9070014410000b00300034040090480e0100e041c0051410f44940341c100c5c1c00091300912402c41c8454040070b00c80c00d8481c80d01a1074410000f440e40bc01103c1c590710103501d5040091f6601c4000c00412814894400302d0351182c1c040e00a48040d68201034035169004082c3c400b058103001d001070f52694000192074000c1d800d21124401d0202c00c01003a03001d05541054100340340e482800010500c0501e0680390306268142c200070007011030442c4c015880d0f07644c4101d1540494 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 911805647 1250 911804397 911804419
    0xe07030b12100b15030103231f09080d050906090d02030c0d0309020d080705070608241002070e16090506040f14040b120607030f0b2101020903060c0703020c010c02 72
    0x30201e03089071541a00042c01d544c548070b28502c100040d9082a0800c0e104d030041d010091440c0305011007102400d03a0818001c20011a1110703174a55441041449401030a44441000c020465a0030503101e52400d8500c0a0000c0d01c1c156094907a02d1008445203801c40c40342c45080d4020f135002100701d51416001e400601380800071414180c0141c504142d0032a0440310f1280d00601050003040a003625034860b1024141d40b41c42c00394014061032014000d201d44601401081e09600759001c64211000d03402d640b01001c10f0300d0020305a00384202603011400c80e5070040d00304084c1041c04200a807d01c41d0ba900c800c80b0702501e80003400024040c5000d000d4007040051130034401d800403906014403080d0000e1000c5140c0316007102250541c91801e9000c3c5465000c8000e0003021030b01409031248407225030004218210501e40007410440f0b0300c881c102d000c0b00700e440b071510344003500707404035100300e90043c086911900301005040041e9019007000c0e001802000045d45031984070f039009650700c54001303082d0881a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 911806897 1250 911805647 911805673
    0xf0d0507080d0216230723210703030e150f0f161203050f151005030402040e0f100c030c1d0a1503230402092e0e07030b12 54
    0x80d4040c00d101c8000280da82001000501944101441c5500e80241c0517454450304415034505070040d04010107041031a40410703a13107210304900300d00c250412110603e18290011013003a20320720b8a8002d4645000f40a030100601d9000405da0030a21000d40c4c065404a54074442d0407414010503079403d42c01c001c1040307246803074031550014082c2b03605160850b2409056507520440c2078000010340c200031a13126000c1107107150305a40c1d4250b010503524000901a0304900004030002e410000503070a00402001040c15502c40d07178000b910007901d05080743d8480a0071011140e550301038040a0034420f040582000f41076101e4002c00840a00c0750310788104000c80c110514902030b00515141d0780101c6904800078001500812094000072203440000d101f028641550782d01300f85a00341c0c0c0c846030104c0418000107840b0000b1403603210008448540c0c41d0000c601e035074450840d61b00000c11400c140d6090100340d880c4a0300302c2a004001070388042000d00c00d58000e104204904040b00d20b91604018615904 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 911808147 1250 911806897 911806901
    0x30f0f0d080903220608091c050f09030f2104050d020d06240f051804030c0f15050604050702011401031209080f0c030114190b0f040e0f0d0507080d 65
    0xd052a01504d080019428a144e03101c0302043d0103240c001d02d2018100400d5802c010b40c641c00c52108000f070701550400d105e5046810400890034070410000080038464948920260340b001c19008080c0e0300b40c01034480352243e81d1100d0008018400d60750801c061040312a0800325822610041c00c079080741e0510781c003004201c040145003900e0213030301d41e101418052242d90300040b158500d60b2941541e03505001401c807080b5081d8000a0260501d1070019100306287c141842d031003581490700c0e00002d51a4500008110154113000344540039400301c00c403003031900750841e92003a04141c07000c00c00f5541c3d14008900382c583d114000d41da03400b5404014404240000c0c0b86068601003800c1003500655070b8841c003403170221264400d031400d0b0410402c1b010f440c90f0a0045030703a241d10340c0c809521242072012424403404081c2c400b01300540c0c0d81d054842815103074841c1c1d003020200024020031541404114458a0750b8442401c800700b401840c004c1d01072a0301804c195880c01340c00c450134a080038092210600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 911809397 1250 911808147 911808151
    0x150e07030c11030720010f021002160206070b06090a06030809040f06050a08070314030c030d0b04200d0e060c0f07060608071203021b01050a0302090a030c09060302030f0f0d08 77
    0x10054564403800700c02404200402e0000d204082c1c1d40c1000c800c0382240c034405c29040011504010300502c41842075a4001075082210340c2c02c030130050380d5178011501410314540002e0000c0d00640041405418410f0640c403c0e84100d60039500c1290a50324901581c0c22504140001070000606110022260a19501520042c010280c00196054480f00010360382191540b00d00c5180d4059441403040081d08407076546440c0168008608114160000c1d0303440380210380298100d99641c80c0b1003026681c4a41140d1035002c09a24a80c10b0b20f500380303052080944c488640e1a080b02d0600b842e003c071030040020858807400d8101d850900300141c25096802036489104c054034401c0c0c695001080342e543c103101e400d0041ca030655a01400705d5a9141c040c2c10100300c02c49000c1c4040c0e0000b5000900c5c3d030484210340402246280060351080c43c0f10003d005d02c41c881c0c002401c4d0500900e000300740c660280d440310b000c0c1c0740200c08035807142200d101982e603980441c0307980e40c0e2590025010258002e006505a907 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 911810647 1250 911809397 911809421
    0x170703021303080c0706030b0a08060402120109061121010609050112110406111c1209081612270302101e051305030606090f0c040503011a04150e0703 66
    0x4001c035549890304880e6410403139540d195070f0400102080b01c60341510544c40c20000030f60b0011074003464403100580f54040240068050b5202c0700c10714048171400c5d44080c8030242d10035002c10042c801d4000701445600018032448010324011031a0004005c03000015048031712603a40c070850039081000440d084101107005254454071980c820001c0d8203110b0107003010f8100e5a4500f4451700682682c189808c00b60068002d00d43c1c25800703072103141c550110294106540442001c202d0710a1840c1a10740ca00c070f0075105c20341e403141d11102ca20400c820080e06500c2c80504e07030785072520b610808000e03108400c0c00d140c40520b054100101000182802904186e40114904080c1c2c100008038951040d00502c80c22000001130000440847c40b91400061101501d0300b07034020a900e03c0d0005c00b240464101030501c850441c0c18800040f10003140508440140c00c01800030700071844e030600d4859190b4010f204891250742840c01071803880c01c000400d001210000c008040154550203419002032800541d02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 911811897 1250 911810647 911810677
    0xf1807030206030103060f05010b03090a170d05070e0406092903070f06090305120c190203010e03160c05030d09031707020607121e021509100504050304060e0117070302 74
    0x101690b07418002d03500950041c500442c00c2c504d10700d284811200160800582d896080c4188091801d0004242000d941c0c85030501e08050303410082a001d40c029128552006800c0400b0040141c0e4400b070381d242e0800d02607030b090204940300c6010300e095841c018684000425403004011902442d250014111740018041e40ca69548410500f20303a12065002000070925840d800c00401808100c2e20b009076040418450614500040301616444100c49001c4c0c203a5845420030150354080d03100d4070342e01000008032a80c4940e601c0070314403642d400743c100362002d4100e00b60002e4181000b0811480e0311300640e84e410502811655150083c10f02001031200030f800c28030020005844480051030841e0042e00403072074120703060b007008000003200c48811800032031440008001a4001903d190204601040f8910aa0314045090300c0c001c031004c10f42c813000d4200744c280700a1080110040007500e5042c0d030b8003142c181010005541c030704a8070212854011200e0300044645201e0343c00380280c40d00403401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 911813147 1250 911811897 911811899
    0x51806030618010b0304050d020106050901050d0c090e1501090e0c090711120d0c0306061b05011b0f020601060f23090d050106180e030a0e060706020a0e0f090f1807 72
    0x780c030040c0d01340c000307100d0500d0020a11041c0b103410000c141025003e840240030860a203004194591418807406018111403440401001040c00408003d0a07801b40300b04070b901c04003200c25556600c0d03042e91076040c001d09000442c98003420302456078410205801000720001400070301125100061007201084840755440e1b04084003031003010a8940c0d00d0390b5050b2200381000300d41007140c400b000c03202d0915180060401102b50001c41750516036401c0704502001c10068100a40582307601c0042400d0000054804502940c0002900c025500543d0880d4010381c2c8a80c410b64990350f140100c1c40200300c103050b0f034464280584c2c1c0c0051000210741c4140d81001c50040200d070059400090031a22039442e210180106580c3d05c0c4050178a4550361420311801d00405811900c8ac0b007211100400c00400c2c1d120001161900c10803500e01e603603c5142155504000400100141200348a0303a20603501001107004a1408410042c001d180498409201e511079010341b40300300441120111281c050010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 911814397 1250 911813147 911813179
    0x40b040e03032d1005090f09060403180b030c040801061d0a0c09080a060507110115150509180405011802010519230c060a020f0a0c0303060504020d0911010518060306 73
    0x142039000c3c0d00d41054603401d040c05c0c03104014a1120081c068030000801c02c0401040c0d002c0020f5142e04960141000e145000e120440040c0103490354004040313240700041401030601e0440010001c45020038020043d080e250800005407240c80c5035600c64001e10708000c00c116940681c00f013101e04107907003003415200d41c3d1060810300340400d0030420f07900e040d070f6007040112290304001c222400c003001130001c114491900f40341804800050103040d1002030b150001c1c00302c441c00b9404952410a0040c810002d650740c0a484804e8100116001c0310746500f0060b454841b91851059104031541c141c641c1810461881002045407103031543e48010409604c4503071192202c0c5072842d0104e05510314030301c1c4c1e0350340c2d03501c81c038901c0c040b005400700c41100d10420100c141c48100070b041c1d50081c1d82e24178100b005130895043c2100900425081070754041e2002800010500e4554403000c511481840204280c42c44100151420300891540c86081003a0a885000a28000e001158410002404101c3c4404984 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 911815647 1250 911814397 911814481
    0xd05190f020d0609051915120f06140408040e04020301060b030a200304050304060f02010b270f010305100c0522030b0c0304150207020d020d03030b040b040e0303 71
    0x12014a407580040c4100c05030055001d000040d040c08001400350742020540d0100400e92003900c002c2041d602c000c601414045d800c02c0034000d08006070003c0d41c200a0b401c12414070300304c051f42282c1c60340c54030840507880040d1401c507911441d0040070300d9051501e027004401000c040240121b03455543d818000c01d080e412074000d107000c0c8640f01c100213140294031900200e881c00324228044c0004e002c5c02080300189001007218240d54035031820780040c421200081e030140c580b012010b80d00041350070985803030030501040035101d44554040f8001640781c0c0781c880d80d2032480a000140281d049124801c2c3c0203400743d0400c12080841c1c4c50140d2904120595142c0c400100501d0302c0154034031100b0030018045040040c40d004800704034054514207080e0381d0000c00c0c018003036803840c2080c0c011a80c0e00665892110603000300d03402030502282c0c030003903107002001400022201e5114030301d010308a800a0400303201740004525032100851a544a10f8801060751000b14464082c07480041a8101718580c86 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 911816897 1250 911815647 911815661
    0xb01021207030c050a061d010603021f09170a200f10021501030c061103030906040201030b2d0a060912060f0209060c030319020c060f18120415050f0d0519 68
    0x24000020035900c5030020241e107091f6815414280e1381050343c14000342e541d80300b0000c0c042d6156404003c26800d0140b080d92200600d5011001d0445602442d442003d80459035006072442492801d0240304c140c000c460702c01c06032482140d0030686585001f00d45081c95131494818a1460040f03440800c4081c0d000b41484001341c004030396520b0000c00c00c0050070303041400c0d100f644403c2e90245065180c0002426078805000344064109034544004c6829501c541520400c850b4105400c16015100048803a8101c0e90085590b800740c40340300342c00a0780c01d01c2002c102c402c6d0b0361280190800c411041c0c070f0781c00c0a03003103d010203d02180d00f00143e44003541c4820081c11807503c0000a55142e250808829001d5134104007403036010750040042c45140e503070100d182540001554103240b0760751600c25202e499880d101c021502c65101d482100e01483d00940041c008440c00b0b1314054030510091b4074111841c0c0601250503941000030301114010000d150019a0b1040c0c01c42c5c0d043c0b00240d281c0e080070381a1008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 911818147 1250 911816897 911816903
    0x309080c07080a0b0a0504030c060b010e18070f0908070303120b041e0624050c0f0303071106061504060518130f0b041a040213030c0b031006030b01021207030c050a 72
    0x841002c600c100b03c04c0380f074403a40c4503000840401c0700303103425200a400b1048500e4020411645c820a50360142e029041c0007007656005454224000d11000031002d11540503646140807641039015080018807900382102034610031809002060310710760f0240e0340801c10114080129880b014040c2854172944100f2165031108402843c000c802c001c0034400b21001508041c0480820600380c0b42101c40586c1c4201c1401d40ba031600559a0f0b48142c406030030108080c0d102c86042c0000811710810980c000440c1d20440107420681e5403035140c240c20409610344c0040c0425141205110822100d0b00031000741c041d01e21401407094410000364000b03051000d441a0a00346070380c1d603c071340381103400b0288a54900d8102c241d03010001c00041803069480d000000081d180b01705e800280002544080c0300b151401190310016019030b50761180c103003410541086500e4021691086000244035100707000700c00d41904103801a1003240c025100300e041641c0484401d60a2060b4100b96800048040003006105c0740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 911819397 1250 911818147 911818153
    0x1409031c050114010c030e09010b09030c03030c0a1b080307031205060609010c061e0501030b0403030b0a0617040c0e0a0506120c0f06090d080705010b010305060915010309080c0708 79
    0x1041295480c514044910050440d1078a0700602c100030a540503588819004d003404001c2c40c98a10b0121380c249000011142c11080160000440440e11000741603031850860949e000c90341500241b503070302d0290410284440d131165400704003003800340c0b001158106020380d03140401910b542c002840c540c00707460220001030700e81c01104c0c4a00c0d042e20456030800f00c200c2e103181c900385400000a14900070664041d001c0781e603500b40109521083d02400c103003105400400d200a680d6170800340d0342228122000d40205e814107684400c180744c040f071220300340c52082e10fa1842d03021444211900e4001c008100311903252043d4004140c1d00e51800d009403146681380f1000c10103181a00501c903440d0038107135400300254401c0c0300011050382e4030110620759203015100151601d0780e40c030000d00010303403000001e450f8000010341c00c82800410340083e00c21790301c00e880a01194a40394280300044170100e0346081c04130820704141420b5840f0344c1010403803a0080c00d02a0511185410b040e04040056020074880c1d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 911820647 1250 911819397 911819407
    0x18011d0c0108130b070e010e040603080c0c0a0f0b1e0304110112051005010c08070615090e070506090405090a1e0611040e2206060e0405060603010905190303140903 72
    0x5039009028552014000041c904910f0301030340d928103045400350841051003801c808030012640f062007040080c040041081c0b2940c1e544e81085411584250103190785070040002440d41800c0c246542c03c2120760b19400350031070b40c0c0f81014007940c58101c0107200c076281f8a56415a000180c40390042c5000382d000d00074000300350180740005030903144040c1940b40c06600300300c200042140500c6c1c801d003c0b500282048568461280303401a99803250b10401044e00e450700700e07407441010070340414001340c44698408002464802084a80d03130412403040d80c2d0300101c10021071405003031640005400514030700441349170443c9a92a0a40080c4402045050341800c448200c1485000d0080b80d69180084a881e0f01c0d00e403c180c40d500c403082004119003280d03a03401205002504214800308904c50f04558108080e42e00d844000b01d00c840162815282449400301061803450180704d507a500a910400400f8140c2140703c800c0150b01281d6016014103907180b0141c1030500a20f4411481440e10001440ea58 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 911821897 1250 911820647 911820649
    0x3160b07030515010e12070302031507111204030305070f020306070e2112070203070b0a0e0f01030c020d080606040803031e07020a08030a02070611280c0b18011d0c 72
    0x982d0000d01c400b004071284488402580d03082618030a80d42e500380d0351140010302d081c0c8614603003a00c60b80029010710070652a003104940b0030b8005406070040f43e441d11046140f901c065540e586940c5260410741400300000c00c0003034080d00013040407a11603d82d0b441c0000d4541c00003400c0150031201880885c0d1303034124400f80c41c9001d11001c2c60f071502d0006d23a0b80d1504001c020160355490402c2a80f041c40c07900207004015594200300300070003400d60440480c1e4808060000800003a11039207141d0003400c4401400032298080d0160032a000a00da000f00701104c140141154210405800c1380e800c200200008584c1c1d490a20085220b5503c906010010900000030404c0700c1c4002000c02c0b0454001c485104002091441200d0700004104005601ca04c2ea80c10144014080020300d040c00b0800091445200b80009484002124050700700300440741c100035099070b0402c0344c220003c024514000010350203000b90481d0003404004140001850801007111b01c103102c0d0300c02c10410141c1c2c480a158402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 911823147 1250 911821897 911821901
    0xe070e071404030b070e060d140606120a0f020c0f0102070c0506040b0711041506080a1d030a0c0f02030102030711070906150e0102161e17150903160b0703 68
    0x216907441c202075054407800d141c0165000d1400000d04219810001c600624442c106c203400140700149030981d6006111182c80013040c0402e50020b540020f40d00145140c500321050702d9041c0c240401010391a07844041b43c1c002881401c0d180700302560f09000d0310b200107a04100719105ca2080e20001a500c0250b4144041560180e41c40148240400c0000707011a061402c10b07603100c42d90120650824000c50030018025002845551480800c403910020384194441c17030072401103032072902c20002c80c03903078000b00034000c12003110302d80700d03a4000c0008005040c401e611000e4428020741d40004018015800039081e0307803068440c4030018000d419100c1d0700c0542806000000c213000d4000704100e07032800011341410000d03640c1c02c0b024003503000003c07000d503402840301c400444031107480140d181c0d44800f5040c1e407000344c0c500c1646884018103c0890300e541030344506448d0344211402007a442d270114448014468005103115240c2c0002c0c80f036401162280c00e1840c4e099882560280120703d444000102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 911824397 1250 911823147 911823151
    0x7090c02010b1f02121606020a120509010525032003040c060c0203060126070306021b061b030408040b030907051c11060906090910090b030d140a090305010e070e 71
    0x3e240000c0444250b050f00001c83d001400c030202c2041da00d03804c2e40240b2281702d400c0070002400781e81c0001503241049600000c05d111102c01c0503010003642e103641a000e400c0341d000700d030040402c001903003a600074082000480390010030703c0d1070041903492246140502644041e0890807803507001105110403c02c0b00300c000c0001c0d0400385003640800c49950000303079540c5030610582c6040142103d204025420900140c0a507006100c00c54109646da850100000e500a06e1030544031034032666010500200440d441d03004003520b804499606e0480d119091a6034000340c000c440c92101080000341064221020b1841400d19802410090740340c0f809104031a801108024040080c0408080c00203880c031202d00c840003402c0d52039544030710707484002c244684a422036003680112110200107010001c080643d00707548000c88280f101c4002c2c501490764590303000703400d900859200c18034410407900c5038000d800c10380307094642050b145030790303844050031500043d1002e8050f411919081c0502c3e001003985c0c41d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 911825647 1250 911824397 911824429
    0x1527140403140c0d030203040f0501090302070608010b090a031209080d050a0807030c120b010909060f0305120c060a0b18130c060908030d051e0f0f01090513020f0307090c02010b 78
    0xd440c00705840f020903229100200381c03800303241d804000320341401008481c040075203038000300803c2401444c2c100a59504250320940c400901404c00100700e100c0c6001c01d032112014040d21400100b41180d0700c80c580070707001007080300401c0030044000403001d804000414078100c590b242e980c2d48000d581070040c883c0500030010002d05003003201640d01140c3c46000380580c0c41a0050005609102c000121800b07903140d40482ea03058205034005c2650700c0742c40e1504045a124004582c015881c40144145500500d001c17486d4980000c40090f100e5220303038010046c01480108405191210b096141600d441d040d502511541400080030301040a180003d01c007170040c0b420108101440d083c3d40990300e1080640700c1000a40312400f05400c07070483c0000102d080819000b14006d03140200d0b170618008400c03030700c00d02c00b11007040000a18401c2445190300842c4480c1c4400c00030200d136020b11840466a1440d035802d8401c000300000c00c454548517450941e400ba50000c21104518020049250f00903a454 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 911826897 1250 911825647 911825687
    0x10f0302091825051204020d0f05010c0908010e0604052e0203040b0a15150536090114060313022107080d0509030601090b0d0807030305191527140403 66
    0x7100340380d42840c5c0304c55402039044502d03014001051501203141c040e10200240552b0810350703101c3c0c0c0240c000b10000142d07400500204a103074003102c0603d0780c0c0d034429603000d00785800c60f204d550003111711a002c5040c1d20440c00d42503200100800d500c0c2d0708a9000311810b0728044038020070b001c61100c050060240003654103402240312400c01704900041e0004046031014860001480d9600004100101240e044040c4184160707140a42e8200c81c040c2c0440110b920405600380007003007050705401004050701c0301400450850b075078500b1f03001488c5003c04059074040000700901c0382180e00c2e900e60354120a41800070382901840e28400c1c03450040d05e01e00c40f034180003041c030411417640c82c0054894119281c407a4082404848030000c00e007803001226014002c043e000483e01c06158060300315500402e212074103a1a442840714140b012280c040c1500f040f241d9011a0800c18044800341540d44103010303070b00350100c00c1140780e103240c100d50500040f40c40d00c440328801c202c181500b14040c424002034103150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 911828147 1250 911826897 911826907
    0x402030907082d061014031501120c0e09030412141605030d0504050d0b060a051003050f060d0f020915120a050d0c0b0106180f0b1206060405010f030209182505 70
    0x86108175034001c80c604051070700511031895070100710b2150f14000c01c030084402035840f940d01c4921a10000c1060b5940f40b0820000925011045482d51060307020f08007841c1403e080001c0c11200710000c60094424620f400414a00c502c410302a1060f48151516001100351410091504000c0d42d5040d40050080600003000661146108180100d0384400c202040e951481d000901c00074041e0001d030381219004425031485900742c4e02841c040c1c84440e0100c0c071940d561b01c04101b448401d000e0001c0c00070754020384c0c1600509080080070703017005803a100b0801401c00318011a031600c2012407045800c0d0320400000051140c04c4c4401c00505101e440c2c40d4001d003090742c98041a001040c0301e0941000b12044202c1d00704107810442d2406000300079030a05525070b48482e07025694000402c018000442000401c40901d4540704072000c850f03040e1038600401001000039002500031611041d00010522050301c203d94100a00601c0b81c00300c1032004003c1c1760f50040e884440e411411083e030502800b00b007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 911829397 1250 911828147 911828161
    0xb0304060e06191119080901060e100302040515091006031107030504031401020d020d06260d212a03050606070b06041b09050310060b090402030907082d06 68
    0x12003901c0c400f04110104801c100407072000c01510a903200c0c000804400f450741141d10b03500844090140360031200034483d4075103030744100b01d01e6802a68504c10300e9880038000c03c01030805030080fa90000e031400000c40c0060b0b5850100e0703218a01114140710100c450101441502e42500c00d0a610b000c8071402a8240b01d2141d0340984144180d00020308400e500380c400503085402501141d02d1781c1030142c41952a15140844e100c043c002c0390040709500000590740000318051380c95410070b0510b10100030400121005410351f0408804044180140e1110310b4207403110526000700003a0000e000c2c080d0740d00b40043c6000c00e90f14000e141403081050704180501619176504402c2d0ad0006801c0030204549881d560f0000d0024040154a0404500c041440c1509960000440022100305078241c0f5441c0325400000380841c0c2050045090441040c000504241025405540d01901071422589007640340c0300014584440b004070010003000c0380c40d02d6030034003d1440300c848401180340010b103d0707420703c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 911830647 1250 911829397 911829421
    0xb041e0e04030348020102090d060b0f030f060108070f030309050f2d010e041413140a050102040906151b061e09060e03090d110109030605010b0304060e06 68
    0x207400030301007503124140300c0c84040f13480c0081e584807400340050780794010104101e440820407182c54841c07008454520311500d41c0c0103008954066000425100513a00c0316942c7c0c05c0107050750009150083c1d17581e52203440d44c1d1410805407001c00200c0c0000c2c242589440031003440c080c03194100440303007110310038100006600000503030141c4c0c0c0200c2d0714041c80040c00d404104500c0030509080e40110000e1181034950401603101d5003040400ea803a281c41c03146083c244000d07a00034021108881010301c00040c01c07103003c0c50000108501c11180300841103a80d2003d9481c03c0d44405041e10265800a0204260b030483c2c4102c40081c52010300134031001e008600c0c05480d565262841504601c0c1d0501c00204001d8164400c01403406030102405082b03c480300d110b4001c0c00324080455581d8030740703211500c2c501000001e6446400c0e004202e483c2c503400340d90380c20001209261845040c400105408000510309000c3d0034040d0459003166512031405007045007d45081c200c2c410b0903a0061002d001014000d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 911831897 1250 911830647 911830651
    0x6020d090b0307021203070e1003060b09090a09050111030a150605030a05070e0406060e0112021315141b1e07090b1302031611030c10090f0506010b041e0e 68
    0x2521403079460f5618407400343d09211400125031800d100c0002000303240d07908005c400e46221405c0d1080011700d030f0322010590403201c2601850010441c02c1c0070807612803034440c41403580819111000304d891105a0388240c02e54012154084000b0400700400804607601e1103a4150640c0364414115200e00d40003003d0b02c02d100c05000c0c010060385441c0010740d101d00940000d1070804003d001084041d560300c0c002885c14101c00800c900017034034000703011031109040c0244d41c1940c21481400104e50318040c0200b44880341070142805100c1c40b140031041d02003141c40942085140304010400800600c0800750030070b40c211a1010f00302d1214a2079100f02c007030008000c01551044000042c1300f400c074800080c43d02c0c8640e14a0480903000000708002401080e050f0f01c2c0d10112070b290030324485c42d0f0040e482e07100d00030305210000580c440440400450204e402c461034440c080c0c42c2150702141d558403564244074098100d4070820b140024108030464018009041212184481038021802c103a0440404280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 911833147 1250 911831897 911831909
    0x61b080609160e0d03030b13020c0106060503040c1413140f1f090b0d060908090301050606070b0c07020d051516050403032f0607021f0606050324060c1606020d09 71
    0x140a0802c0c0c00c050103907000411701d01e00102001c2340100e808800c400a94400d020f80304055013000ca001900c1805042564007503540b00a84c2d9540c1030400524908040380300f08800d500c640422440c06a00400c1d100d21069600703001001d00301071805a82555103154068880040c000201310090255068440c180003520184e0b00041013034000c00c400030390146400c04005c0c00007482d000044003001800c0c0020804082c06034000c0c0926501c0c942003048900031510701070060040003002421050002c00104501480101240200c2c0c08507240c03180342400d0096015410b200a8007446201042c070204a99049810310b8124030f41820345c1d4000b010668000c4074050000080321b002c0440302400c0140419401e0b0307420031107410b441c0c44070009665400e81c500c20810107004194088020368680a00c02c00d48a95803203007861a12402c0400c0c91910070f040c0152403907000c11000314110742e1220000d02c10585103100524052010310030f001140d52503a4000c00566110b10328030a0742d2030b0440200c07002c8800c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 911834397 1250 911833147 911833159
    0x1603020706170c1c0b1203031f050607080d150305030909011e0b0d0902121c0302030103110d0609080d1505060c0d08101208040e0912040b07061b080609160e 69
    0xf00d0185110103003580a20091b80320201070206004610000040d601c2561b640d42d0064264a900c60300038000300700c3e40149a0000c0040200700702241c86040100700c20342d82c07018005802c8040742d0501d040c0912a0304225002d0b0800540744035149042c0130360701e014240429418080705425481e00c96113904a201d01100c8640200320503039401120360200d002c0d0303500900441101650b880c01c007a16210840880040303000880c00c540c100d03a10920960f8181d952181034034a009000b00100a81a01e81c040c0c210f801c280c031507139200700081040000d00000c14504402041034911140c1c0522045100c5d0071482c0a0705090102040c41c2c0d10004158441e040c4604010002d529a581201d501c1c840c0c41e0411640b038580c5000b5002007020790030003032044a1080448248946807a5000764070717203d000c103e1803410301043c007090200048401c010001503108000010f00341001c1c4510301040a12904002c0c0461802410000c55043c8200803640c40040c41520101d640404900039101e2450445014050702d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 911835647 1250 911834397 911834437
    0xc02060714060402031b01020a020f130c0f02070504110a05071707150f0504051b030f30030f0f060a031a04120f081b1603020706170c 59
    0x24480404a50200c0e030005140a201414200700d02d0340c540742038908a020f881603a0041d026190101120007036080141d02400540b800c1e40c080014240030041c0c055484252610b1445003c80680b1a04ca944192506c8058080d42e5164000e42012095403106000e42d0a00543d1030004801d42d04403070b0343c014076050042d1502004e0904030844002683c0c81c1d100440001481c1c81803200c0c84102c2840e1000000c3d041c06940241c42c15001660f90644005002c3d51101407034103a01800182e64080c0818050300304c03954aa144070340180b0702100702c24180c04009011881e1100c501845080060294000d00c0b030310301e5400c001c0560040d0482c01000c0418800840000c2455913035402011001560040181303484410340b800d50b0412542c05030350803501c10408034010000c581c080c9c408a00320341c2c12912941441e039a00103110003686461203415801c90382c00c202800c440302031010000a11806a03000740489400d081000d45014824600700244c00c04d1401000180380741d03282111444680341c41c502e0100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 911836897 1250 911835647 911835649
    0xb1602030105100f090e010e100b030c04020c0309040902060d09110f012a03030f0203070807080603160b070204021b1e010209100e0d150906060506031b0307020f06010e15041505010c02 81
    0x50100341103001e023030300404000c078000511b250080e10302000c08406450341c0b0010082040304900c5181030203440c0d81c006000303d140c0b82c50b255002840c1203002410340da160240d41903201040300c212100490340c83c0803040c03480f14127003810b00a914580c002030030540380249884d00c2005010705502103a03d1440034044a200c10548207401c0103010030304200d01551241011000984029400c507800b100140c2c03d02d0015681d4500020403c181201011311a04c11a0521104a0080d44400b6060360425020042c100e07010911443c0c01c4c20903015000038109010032030702e422001d01c07240c000030342440c2e0041c05501025610080c007211100c000f42803c082000304c850100346102120100581100c6603118581c0403002c03a50000e0410034860542040400c0d150800c115084c002642e5491000141501c1400844d10080040d030b0480100c0c01164100240c1c41c1c0405d2824200740c20031030b1050024401d1000c41c0502d0788024510300303421903040c003041d1807902003a04244480d20902c2d04000080c1c01860035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 911838147 1250 911836897 911836901
    0x1b030b280509031905070c060905240915370e030c0108040f05120405040e0105010b04090905120313330f0b040f06050a120b0606070c0b1602030105100f090e01 70
    0x1019407081c404d41185985040c0503000700100d1048500503c40540700340302e09250800752009403000c42008331306246a0009100740c3e00401e480d45451600e0030011800c070981040e5a5514416110840e00c80e00700c07400c8a11038420402900c5403091122506e0124040ea8000c40d90710650720003071a110170035940b54100070002c00102c18010f06103018141e08031082c0c6903110024010388005941c1070208000c95448a42226400d1003008105903081c00280302c0c10082d034100790b0a1030b010358201c4880484e2200282079031b0b8020380704002075202794007801007080301340b8450101c1d50036020022152907040d07810405000c0c42194407403d902da5100551424207030b0686c03058500e0320001e0000c2108180480d4032000801c52401984c1c41440d0784940025144608078070b10b0180c2d5403015200242c0c8c0c6409092140700e40003550100d070610864840402c071540854041c00342c0c207180c0741d0a803203000c0c01c0c1d0040c103084074005401c02101c40c0c0d004030284603000c20500503104072030f42c60313000003500340c4031400480c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 911839397 1250 911838147 911838157
    0x801052a091e130e160305061b070c080a0b13110907050c0106270b0102120708070b0f04061a030a030806180403180b090a031b030b280509031905 64
    0x640040f0709a4520085a0640e02c584408803d0350115001400300941c1814004850300c8000c081c0d81c4000b001070b041c0744103001c4040100c40c0030980c8509105155840c20301e912015005417040c2d9100702c4a02c010300481c5030311260014604d00180000240c2512803065041e0000d0b042c60040407080b002c00e07007840c8654212421040c00400030044561126100400e03c1c0c2c20342c0c600820b840c052044503880b400c0900c107a0300c2c1200b052b00100400c006481031005950030801082c1ca02c0b5406105500126a10440491003040082031407601442c0c10b02e000340c100c0e0641c4404c900c0c55440c0c80780710300749a2000501c42148a42500784003015039100e600041d0510340d44075030113605041c044c00340401c042c1c021200e003140030000c0d40300444654482d07001071440c1c01840201030740a011005e0410100d60403541c4140d0710703101500621503136a02d0303407940c0305505400e4800a2868034007581c198068560400c030001500050340d07084c045420489003441d07880c018040d100040b44507102010121501400c101c038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 911840647 1250 911839397 911839399
    0x5190305010501080d140a0813050f03130303120e21090307030f0201080708061311090a030c05040b1e120a12030203040605151f1103040801052a091e 66
    0x84100d42c0c441348181e40b205010043e0710049617000c40101d504001316019221110050356030030443d81c0d15904c01c200710051051040d14240995204001200070a00040901080070151101c020340b81d450001e0401c0c0c0340381c0c02c00d20094984210a510440e02158400e055180c841c0405010200303045c00010f188a000f98040c4d051240450000411400810b0b0102e4103000742c03140b04281e610390009480a20f8100d822550111040103441041040f56201000020990510760f09184001002c0343c041001500251402000860204103a03e00b5010f0f0b2a481042a600c040c0d010544506580d40c100380801a41c0c07044820f1503503455042000c110001910740c11000d043e04d95040340360041d00035030050750251501c03428440000c80e030018076586540c0000029181004100c5203000c0d1106541d42c905450341004800b895400c1d40140030805803024180c00400052607090184031030740c14002c603940e4440407000100c4000101e03401c4c1c000369210311505484008180201c40a20803240c07032460506 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 911841897 1250 911840647 911840651
    0x510150e0a090b1206070e0d060f0c08060a09020a140c0f0a0b061903020102030315040b0d080d0507140a2f010e210a030b060702211204030c0519030501 67
    0x66442c026800240240d08207546803881d040040700d0260f103c00f02115140b010809a078010724a0341443c018502080340035400015005682611820591f480c2c541a9000101d80d0001c0c00315a00c1c080c070120000300314480045140400280c4047d04280c0c5004202050840100784460100001d000820010b40701a0a503503664041e0301c0c003c00d0861058903a14050282e290110146c000300300290000d80760160011070461b500d4511084082c010711030559001525011100803c3d03c503081040c00351441030603841e84980001e10488111000100701d03000b00002000c0d0002d540c968403088642039555031600c10b4200d481d0000340780c03070103003903100140080b0f20680345151958010b6110044005035101034469140d050741e0b01c0800c00b800544042d0341c0380300c01c00407204094001d41c0404803d4102a007d42d0511501c8d40020381400002c050720f0100706510080048002001e0203019005c1d80d04c14940c60070f15040d510340c13490368031550017a980103001d80c01100718103020440524000399441402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 911843147 1250 911841897 911841899
    0x40b0907080403111c1b2325051c150e1005010e0c18091311151903060e040302011d0706023d02130b0313020402361002010510150e0a 59
    0x5000c02c01f0b0004420007428042d08641c00b1140000300c4626090b5140030304000a00360030032041100501c04018810b41d02070f05281c80000040d6900d90424002c050f00c84005482c01c81c01c03038094101550340054002003450040107002d05840d0750341803a0005a2100240d8132240000b00c45e0b0740000b00c603c51198010002d00400407944204101803039540d102d010f0024001c00d4100600580e00754040c4488041042400030300b210403000300743e60305d80c4071041c540800d6042e504c5000144252040c0c4081d4010307511810b01700d00310910b04a141d0015140700c0020020a032800314000c0d111a00f000780038020344070700d00d081500710115407608480c0c1c00da6503590f00c001040301080740f0001e500030101d60664880d0200c00140d110141003c0d01e21441c00d101e44444590360340e60800c8004d40c080450525410780f940d80c83e0706203040c00682c28409c002c074095007072400a4a03030204545054040c0f101c40031a8146130801000c1b04001031340c1c00407036a4039004152100c0c03041030140c8010211201654000c420200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 911844397 1250 911843147 911843183
    0x6180f050d0908010b130e0709060315110c0316061103070309030e0607080d0c1809060503100207110f03070504240f0e0c0306040b0907080403111c1b 66
    0x181e070702080740980c440020712a83c500049081c0c5586101241d4018603000304040300b0020340d0000400c00b0a040240c0e060103440e80c008408a4825800c10f4039080030b209030b400d240c41030902c40d02020140c2c04290b03501740840048001c2d900e201d040a100f08040e9034000368410443d051b0860300c155114850229144d1402ca900100105808003041d00018003c0f144000c01d400c00c101120b00041d000f012452420082c801c51201406104001a00700000e100d951310600e822a15504003034100508007043d020b1801d0101351030981c1d050b10080080340f04000e05000030300c6c40003002650b40c0066848154075400600000e081c0642d9a00890b005828480601999a02040003000700d0542000820304140c840340e0b026400e40c1603000d04511030101d0b502041560390074402856020b4030061021400d107003035001066081c038090b80d0303c00105801c2070600c020160018082c0b0054059071b4028185105807050114035951205a1f070014030040094190741030240b041e00819158015060f04075000d2004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 911845647 1250 911844397 911844403
    0xc0d1b0e03070e010614070507080d0507050f010b010503060409140d0c02040614281d0a051e0705070f1e140703051e0c030d031505030c0d06180f05 65
    0x100c04a846401007441c08100394150410190503100715a682032140c2190141c901c08a9000300400c0e00e19100301d10001540c00401c01c0104403000c240d071f0300c964540c40c840c0303492450108040c0302803000c1d0741041030781c81c500c1e40e000c0242ca03032004088501107038024160405800c00845a0001c1205005040b4450701d4684c100c209185218800d440070080c41c1e5481120300b9001c0c540031070b081c1d07005280444201c107040c501220100c1189014111060b2030796101881e030340c0580940801851035035520300300881c00004d44a01980f106200c85940f2080003081c0002f0f891030002801a0103010003c01d0003418007500c0341020805641c4000c0040c003202c0c1d455510480d00c5c2220404a03130084c001180e605601802048080071a503105008280e4211400031a251100000d6003010300c134812040090500d0b0380400074032840350090b4800041544000d42c2411540402e900140e000c0e5020030140035580d1140304109481642141c0b000903031124680b80c031507804180010243c103041c0310900b00c00a1045c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 911846897 1250 911845647 911845667
    0x16031b02180108101a010e190f1a03040f020105031905040b01090c1b0f02130c0915030b130c05041505030106080f011409060114042c0603060c0d1b 65
    0x41d00403070304c1d14043c221858040e1210b00c6895410315081e01881c44055015402c41c06484100900940050280c1d50040d440d080140d8401d07644074401c00c2041003800b07000f0f40071304040c100c12100345181d40303425118011a0071240300028100400040020340450720b0940c2180c50b600c061105101504050910030501c20080c022003c0c0c1520301150490418064840c184400c21040c0700c543d40d855136030303d500900d610203a1003640c01c04d07400b2030f890506511a102c9c2ca4000c00e010780b03440c2092410005036442c14000e000c21802450316041c030003242540e400b10503503441078000c03502003409814910100c0d1a406254450f51609a4405039880c0640e0064040c5069135155520060195a20544012030050a10900300c03558200d14540401e41407000c01154807450606041388400d0070030000700b0165006e075000c005104010751011003012b8902c2800360551008500240c43c0c0d04000300081d445200c050605404401c0000e41c0351109603003a00001c80d0205207100646e1000000c49001c2d0034401c1c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 911848147 1250 911846897 911846909
    0x2010c080f130906090c17090102070807050114010b0c0a260406020a11090f22050706092c130303090f030305071101051b09030102090a14100516031b021801 69
    0x40500106180fa45d600c580c1074540d90350f54a01220844440d211a04510041c2412145540801c40e01e0302160301c0000a007074140c816000080c0e101c55017000989240350682100003000310401035031001060004158002c6a00184415050b451282007504502c40c0000b21940701c0c070000c200003a2554000c2680740344107005010840040b0780f40002c11881c41e60850351740840130340341c40200746081d82d0240032a0083c425150700007040c0c699a125203203403203040c2c1d00042c001032540500b4406000f00100b01c103406510300d41c030380c07502c51640041c50410322402011340c1095070108030342e0028940320b50000088036802428251500181d801c0003005800d0440360790002c140c8100303080b1848201440b4581c41540904800b40888100a410683d1944142d034010b5156400340102042603850910741c00041031040420380c5685518414080703c801041081014402c091110010390001051164030361941442c150407203942c3c0380000b6000704c1c0c0e8000049c2d004000700310b9160111041605050590328 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 911849397 1250 911848147 911848151
    0xc09012f100e03040303033306020d030b06030402090709030b0c03160e0306060f0d080f040311030f0726010e06151e0d06090818010807110a02010c080f1309 69
    0xe840d0381d01c1c15201158a0802550b200308010400f2911a0740446c005004020b43c511000c0ca01d007c6d4040b03100030110266100c01e0400e84104125030301003120070a103500702d04003849003104041c002040d5000c0100080d0080f49240002106644200b1240001d10b40c40540780015081a050740210354208544100800304c1c21400a4082c902500c25082d032607000030300804141d0740340814842030100101131b01e60025088000e0100064904000e401080e00a8202c01c1c1ca0783d16606105540488055035207000e80c110302e190401c0b2250114240701548e248000d008410119070603004a0780c03115101410040d443d1500e882c1d44071001144041c0039519401004810a110804102c015044c6e09164000410008000781030341c10100e1482052500a020006210b000c50329049441d41c84840103d00c245000e44581c66690380200080360401c00c10320b8060009a130030710345540c2d036022007640a8144902041141d0070407101c1001c80340040170110f0007175200d034200e03540380d04074003090300461070340034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 911850647 1250 911849397 911849413
    0x18070305010f180b0f10021b06040e070305040f120804050601051e1c1208010303080a0902091915180e0319140d0203070507020f01090506030c09012f 66
    0x542118034102503c2604100191442111100c1c0d00140322803c4440c0d001490790748000307034550320b00002c80e0006005401920303501c02c440768002c841c45510001d05200721030500043c170a40c1d10020406a002e542420b0001301620f650500110481c440d8200810a000540085030030a40c4944010b0056124901700d40c100d98854041101c0e2840c074080b014400b845000d8600c425241c400c1030462420074544003480303070300444d48540743d10100e5820b242c40440d0b4400c004101301644110169880415200e081010045550001b0f03c00d00010346070400e02445c0034101890b26540394003600d259048200d0403d503050741c03841c0d041d075555024203040107094078140707038001c03c19030200403140c007000780003d00b0344806e01078001900c4201d451115900b510700140004052094203100445c020f184075204e144d251009803042200340980405054104000c0c0e80c400c0003980c40d0602602d400004a000c440d0300c41c0c0c0c2000c0100c54820101c560603240212907144801890741d80e205130340c0880b850f4000c6ea1181c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 911851897 1250 911850647 911850659
    0x903160222020f070b070c020102030a0c17120f0a0e03121914090d08150114070c060509040609140423060a0f0e0a050c01031a0904030e030f0d090b03151807030501 72
    0x16607003004c7c040d015810401ca1801c2003841240304241391132083e044c04003009691a00c140e20368112080100d940030f202e609000c11003103006529030b4007081d1301c11b051140b0080b900c0615140c0c026060400800503e03103002c56203401421025072400800840c08018405070303010451000101aa80e1140c107004d4103d0340d0008505c41c60510344a407915240f2407178145034150044940001503400c03200da40f18140300420014040054550091220f640e0303858a81040c0000c00088035095480144014a00035984d4102a012500942d005412600004041041e02c107412041440d0061001007030207100100b0500601e00d912880c100d411440080084a10080807a662210658806481944041900042d039071107a000039000c1141124036038000081c0030003183c0c10042c1601e00302d000c1060701c60003e01c01c0c1001c0002130307145054403004003054a03024101401504480c0210002082c0000000f014a181444030707060003c00946401030400f0188605654080d040d0b580c080080c2c1003400010384 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 911853147 1250 911851897 911851907
    0x181207110411281b0206030c0c16030213270204060f03050105010f1a180307210b07020c1509040b0d030507050c01020c060a0c050c1f02060903160222020f070b07 71
    0x40b20024500040710100c5400b0003111f40c10003049254108000c001c030a450b180700f8003500107140301c2102c810201900b1441040101c10b0002c00c034038412440d08503041c4c0320306600380c081041c5151140703440108140750700104018010707942000810210101d0000100701e0705512942c1281d0b4030118059065031100e1a021205581d01c41410610800b80300c1c0a00005034620480021000141203803403ea648504074415903041c14141a84bc00880002505002203024981c1d40035090f84090240c040751100000c8412803001075101c0350f464080303140b2040d170b00d5503448185522b6000307001e03c0c913070103980c030f001031280e800844200d500f4000c80d5004030b080d5000082d900051540104128201800392000b100c8620520005580500c07624031038032000e48640c6e04208024072003404000c030a02260102a00c1d01c080a84041c0003688100302900c0d185500d410200c0c0c100381d04855880005100240c081584419090152042c0d4070000303103044c1a20b429801008403521602030f9540315030f100e042c2a80e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 911854397 1250 911853147 911853167
    0x7090519060509130f09060b0906120d05071505100617040305090f0f0a0b0a0e0d0b0601050703050d0501060f03050c0a14030c0d020c0618120711041128 67
    0x300b101070000540d40d141060b1401c0703004102000010305d43d680c8015002c2540c0c04034005031280c964408200300359080141d1402d81c0310400352a1083c500c03840341800342c1e417040c070494218200500464034004121607030120708040040003130240b0250800d080c404203041c00318803610001c41c840f07140c60002c114504413000e00c115003545400b070038104032000344101d0340c00451442d503028482c00c20300034a40c0d4441f0180300c0034140800d01152640b892007800707844010015825442581c504907184001b4990300c15040c0e2099081ca045502c40d040e5103402d60b46800f60020f11410305040c070b00003181082d40604e00b510300c040566002c1c00103440b04041040f191060000340f00006017504000129683c0204c02150003902a2802c54a006030315003418040b83c0042445a085400610034005200080740a42c01e0800304000500740500310f08034151342510410724010005040d400314041d459445520408070448402d060b15a0f5412002405058551242030001e003140c40010b0120381c10700c503c0c1408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 911855647 1250 911854397 911854409
    0x9010e0703120e01111209040e060a05060406050301062d030b0f040b0a020f03150604080a0b01030501060e011203080a0b0904031e02030406050a0e060f070506040c120803061e030607090519 83
    0x114219500442c011b2140d440f5600c40c40d003141e1141a060728685041100503c00d000c10341001483d408c0800811040d503107994061817181e0305004061107101446e0f4100300c110024204800907002000c0c200c40000113081d44098011106e40042028580240c00b64078829449a2200c070000e40d28012007100700e01a031140100c02c40010320018044e503d8581018402d5840101440c2c240369540d04420f2401c2d40d4100c048034203081c0000100100f203001d0150307901400d1386044500c82e540c140210321140d200e054030b0180810076090b01081d08040c0690120400c000080d010302298549403c0c00380c1401d0b101c90ba0001d06111403188032610f548040262002e450456071507600c5c01e241c84508a9544c960b46041c0c0398404800c1041141761810b240040c5200303881b0750003500c030601e407500303002c14404100c1e4400914000d07804508800980072008807030380f2040840e07081c1811629155200e20b10f1701c05000094042c495030051003003050300800480e007118001c50300030f00c0400040b4080d041f040c41c07902c0f81d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 911856897 1250 911855647 911855653
    0x1502120103120c060f0c110a080a1404150c0203370302010e0609160b03010617091c0e150c07210f03030209010e0405160809010e0703120e0111 63
    0x40c000280b001555825602e454504640207400c00e445074402c85030b038400c260700781036034803024284202c0e04050442c3ca01c1c0b040201170301d00041942c07285402403103000319200030010741d20021075484852109540140c1440c03070800484068034000608483c003400d074240e00c03c0c450024010702c26040410f110032402d135814108465102d01500c80e0203c070f214400200c06654807141080ca141d80304000003031192101030001c21007086441040c040e2030402e90030049003000101300501505400204601c5100d130300c80c203a03000569550452500b00460740f00101900b10340c0720540b42400d039018042d201030034400c0760144c1e019006a68044003600c40c40c80000c0c025040039004201e00007409244401d810011544804501d490b540c441e00300c1c00c40e031306080313001c241c0c00718041c040c40d42d000c0080c410561041e10100036506252100310500516103020f4820020311100046103c032007904102c00c0e070000c880444150307948914011a00b100d05888900008035100020381456100700c400c03081490111b409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 911858147 1250 911856897 911856899
    0x90506010903030f0219080703030501080d0c172109161a0c0f060a0519050c07060e120403050c0f03060f0109150e0703050703050603010b0a2903040c0315021201 71
    0x160f44d14003a160f07164095008580c041842c4e0091014000c0c80f03684180c1840da614030713291038003404035801a002140035074400c440c1d4100c4c241d000041665801e4101004a04440400c08607081c0e5104c2c42a00c3d1694050b90f020314000500e0081480c2d00541c0c4000503221058030000b8072034620308451060180c600c0203d450390f0080e081000041c06d000141c00181c85c001e100c200b03403061501105031000a00c882c0d0300c04c01c0000161311103141d034040000000e401e100301e00b801c240744141c0d4025000090000d50b5075981940c600f1200f08407002044ca4402159030b1203680d0707420001d48915240d80014010004a050040c2a20700030454600c00d80d00707803883c0fa405908043d0004003c1c1980800e00608000c03204c2c002c80c083c2101c0341201c0c81007040d541c01051500c0c14080c0102070700e0010709500d0180e810400504055a00d03418000191204400744015040d00d2501110f620030031b035051485845000011302c002d0064518441040c5d9005e140000400c002d0351a2183c120300c500c01007201c1300240000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 911859397 1250 911858147 911858153
    0xf0e010504060c11120d0605040905100507080408030609100509010b070b0f06240403020612090c01170a0b0307051c0b07050c0706050306030c030d030b01020705040e10150b0a0206010e01090506010903 88
    0x94203850089800000d121508d810124003110b90280c1c0680d01d41e403005206040d40784480c082c00b6032210340d07440d04540e00c0c2495582e41d2102e0101030041c03481011032100299190b242401d14400400c0c2c0100302100390b5945407141c0c012a07001d28000e80700c0341ca00c500040d44400c180509030340995409000042c0f0503140c8502082c03100d21502c40c0119850040000201507a81c00001e80403541c00003450400030308214401500d055841e0240505020b2900e404082c4000c2032900d0507400b500c0c00001282281e10040001d08154490304001e9020350614105c00a04200c40c0030903551610519a118603900c46040945180c00741247c429080c0e4000e010131b02000e44240081c42d08128090221440302c1080c0b000641000c420b03100e00e0b030002e81d4901500c803580d03a042111600802c0c01765401c01c40e0362030301103540b903d503c0c507102046c19007920394004441c07184400f00440000c000c04004961140c01b000002520b0706400e101c0c0b12a0307041d6400010070720482c54491903014103016140c00e400c00307203169 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 911860647 1250 911859397 911859433
    0x111002010b0907050c03120f0f250e0a030c080102040806060910050d0606230301050106050703050306120a05060c090a170d1d0d1412090d080702040f0e010504060c11 73
    0x8900c90016006c14044100c40c2e002c00c0d00e200380510307616510859240391005501901d10001400d050680e061160301281c0500c0301030700c4c6d10200001c0e180481c05d0f41c06800102d0400d00b480c3c2c2c07004003440d00000340081e1800066000d00159400070081d20100c1c0ca60004200e690b603000e407040c00b6800d038000e004000501e40061408140c9101d03583c0892002d41c1c51844008003d0120030000d401c92a140103000940307003e208150241403035080c802e0600f004c2d41c800929601000b4145402003200f003103244800358040204103d46940402150030a20b8242030590b202c2c1c2203009040c0c0121554400814000c008541810403002404000c000c140d454010881e0211803460354042840e03450020900d05450300c40b4400407450254591255800c068003065180402510740084246010300ca61501559880030811036107401c82142525002140000f0b00103040284000b080300d0318008021444ca00c041d00081c0c40766000701001c110b10600745009441208520007046d40d660028007404444180388 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 911861897 1250 911860647 911860657
    0xb040608070905041e150e160e13020303160512072a091503021804020d022101061403240a0f06090c02030417030a0c0b0403020a060603111002010b090705 68
    0x192041000000103040940f174101c04440143c9a00340c41108800d5504144e000e00c00c0c000081500510424107141d12860340402a4007511014013220404140060010301707800000a40043c160b81e602c2c0038080300c8250300410307040121210702034600c0203042c850214050b181d04135084244804c400043c0d011a010500454014103403000c506840072500c62114802c2001c0140d10f422001122411401001072070200c50b00041c2c0c0c1001080100001070300d41400c00103d00358141c480004042046001c600000300b21403400c6043d602e4138500107266403500800001422040e0240c418000c990140040307420030042400285c8071242010450300701c0302d0f034400c03103a0350704400380003440c241c8409080c015580e1000d4144016030010405009803000b00c1c0181602021400080d0b00c1c4c1a40818007420b04180303024040d004554000008003854000e00a41040135844001001000e8592801181100448800301e000e4160405c000c1e880c98014400d80c004036000030036041c450b545d0780b881120b585d400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 911863147 1250 911861897 911861903
    0x50f01110319090b04080408011503080f0307050d050f07030b0d030806010e0d0605041b050604030b22080307030f0b0105040f0509070c231908070609210c060b04060807090504 77
    0x51190301d02c01148042c03084d0b90085110340d5007955214900b2580e282511313003405e90b10201190000c0100700041ca80300807901d50688510a668890f9906c01c0243c80c0ea02400140300166400c0c4400c01c1401c1003002c5a041c801c11480c2c80401240c1d8401d41800b0859804090041c04982d22401196196001d031600680c42c400041501040000d1541c41d01d0982d05d090310103d80c0582c00031035800c0d0003140d1148800c0030b4001610b1850030540785071070341380103c1c001802890f22040042100500c005402040c2c1b003081360070034502a982c4c280824002c6c000d042401178112180d1801c44419402d40c864000c5030102c822004c0100c155600f00000c000d2270f040e01620b001e0500109100010006000c00180e00107056040c0085103070f01000003003542040101c0316500d881d00354507800100002d0440b01074840c002d4002c2c1000603901c076a80b92901a80c2c469040c200a5014103450101d2a180e12400d01c40c4da19201d4501403200260745820b21054401c240100150b9410140042c400c1e07102c00c0c0c1c011503001e40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 911864397 1250 911863147 911863151
    0xf0702120f010c03020414090603030a0e040908040b070203010b1e1309050109050a0c05090c03161116090609061203050f190e010809070602030901050c1f0504050f01110319 76
    0x14035910720908640b071200d19000441d0700441c04000b90014044000c48540301590b03403203960b01d0a04006a1a44201c03210035061100504504655031181c2d84000c10280e80180503e60740d03900c1d003407110029009032800b00d210350308044030244a810301300c480700e40c19088481e19080345200302c000c00813460110001d0b07032090b079616001c3c8004600c01340035000c4428003d1025080d207100c1810001c0b041d03189a0800b50146440e10103100c02c090542c0110790b4400c410442c444500440328800f21100d400c4200903044510601107000a05201045c10b442250003074002088041c2c2d644440b841601c15910034190f44040304441500400e00880041c410510a0009540341101a9540140b40c1d080301810701c0002e2180303841158a0358001c2d24840d00b0000003070040094514203c8020b50b01c0c8105207240381080030106150080c51802c00c026006c00544203118a041407080c285130008000881b42511a8800d5031200d10a0b40410320644083c00701c0300564624554610200c041408805501520744517 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 911865647 1250 911864397 911864413
    0x105150a090b04090605040c0608090613060e03120a051012050c190e010b25050a020f21010b010f08040c030308180303090a0309081f0c020705150c0d03020f070212 72
    0x90b17051144c03911544c13051841e07803001d070f0030070000415501006000b041ba0364044010300144011f03182d00002d040b03078400004039013205441c20450031405601501002e070200b10060266440d501e821543c8106e080c408224411039807020001600312200001401a0f04200c1341c40166050400c6011818140305842000d250b13135030300c00c00d01070b090240d010700d84844c004580800c16980c031596102c004c1110410342c442e5021142c46e81030326408506002403140461000b2101c2c1502d41051180c900440400385d88003071081c050540d03010f060b910249500061071099840807141c040e148950080b074104a03000b031950b055660907240808060f200c98980d0f145c45404422050041005612980390040a41084a2945400340c001090740c0c118910395086285400c01c440a0b6460f40100e08941c184041040b034450301c030590612101d0f41003035400940c1d2900d001c02031800d4000a200c01350211040fa400724201c030034124124041d410034125003038010000c65016280250041c4482000801561098 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 911866897 1250 911865647 911865653
    0xf0803090a0203030a020a050c22240e18070b040603050903070f0809040605030d0f0e0a030b04051507050313060b01020709061d1602060402101115090105150a090b0409 74
    0x59000b106545d0300580c000d15200d02048014440e035003503d0010f54542c40c0415100b60a90000e040364944400310655514441148030f8111314071030841e008004d60301d04065202c1055080450782120445a4000e0101c6607103007000c07001442030300701c418010140d81064104ae40c114058000075251241510083c0141004500c00a558800c806c2c4520691503442085005000685805502c170301c0c0b09422952418460fa900136607468658509881c2000b1071203203003000540306c1c2503d900042c00012500d070402c030030410009008918080b02c02c2908a250707075003840440c0c491100700d862064098044103001e000941e15000441e0300300050060361a895111607861085031080c0d80a20040c0d40c03030a4032114162800c1086541001c036000d83c0100104c0e0904010307642c2e881c0904003d006090724061850020310452503800141e1501c03090707604004400340404803c5030b05580c0b01440b54601404200b90204c01c552000c0f941d1005455950a1841d09004d07100a001c05e0301c819400a0300c03400701c1800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 911868147 1250 911866897 911866903
    0x1f030204060f0611070602030316050c06070509090c0a09171c09061409030c061e0a050715050402090a0507090e0408121006050414040e0f011410030f0803090a0203 72
    0x60111050301c81c014516210b801020304138006072507403491300184024821140d010045992002804003c601c0d42504480708440341d109101141c00c0c2401640140003190b41d204008000c4000225181201c544803400100102d00c903451224001c01e90342d42081143c0c40840014038030000401003507991207009040c0140030580003c41d2200020020441030250980200014040c5200980c440f800d007800d05e0b000c01d030743e10b80c1c1c500f40a00c2090b0100d45844000e50104a50100c407140c0c02c9115250f07a010103024040d50041881225a01c848a4105216030054841c0c03503c6142c008080725069201e0301426070081c00040d00c00001c0140c5410041270000300b07200c286010714850b0785429500c01a44c00a000c0251000d411020720800e89802042080e0344002918190f0f49a0f030000c90030340400b800040c00405070700401d20041d001c2c00c990ba011741300040d80301c0c54210050b80b4030301380310340e640162007009040c99000003007100c00071820b2030003c10090000745601001520407240310310040d80002c0c0c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 911869397 1250 911868147 911868149
    0x6170708180609070819050c1908070b07150b031c09080d02100e0102030906150607061107110f030d050c0f1911030a02010f051606060906050f090f1f03020406 70
    0x10850f445880104880c0204104084022400607111b1810f0103182c0d03a01d41d200c01c44890200e106802108850701e5074192450300100030800c907000c440c1c20b0f903510b560384030b0140c2002800340d695401a401c1a60f1904a50080049811008019000318864140d50303c44021034905c0080030041d540801041e194400c00060220300c6447d00149001d4103c010710400b501c0942d50711000d16401402840040341c0d002400c1504661595984070f954625100426858001c216026082505004208412409410090542e28042c07110040c811990300203126030040004811909a40500d420070003491041000d005566036003410780d22107074950072503107160441c04110205001d4003440031030100a140e060380900300000742c1c0074003031980c00e07a00041e010000e2000c0140c1803181c001070a400000d0202601890301d039012030200109920740b48800b000b4145409801e02a040e203e0350003455180000c40144110300300801007443d9600c001311400c004170300d8100001c64000e18400070005940d40d018081c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 911870503 1106 911869397 911869411
    0xd18030806060c0109080f0a020f07060912170c061e01061b061427011e020702010908010e0d03050106110709020f0c010f020a0306061707081806 64
    0x2d030240c000c4100081a901001448121f445c095401410500d0b02d642d00701c1c0c0307602606100309591240c0c240207000c00304009910402200b20600300201c501481541e0b40c150703484090054031040e40101c241041c05401010800040d51103107444d9410303480101080f00e14551400b000170b4401e481840043d100f80185003a030f0001d010241d0800c40c0305880d056200a100e2600d900117007504084200c032012001e00800740c14000440500440b0540300c03d0860102e040a0640d10240003584019401c07810b00c611080300140f2500e0030b00ca99024504040040e00c8030902901008044410580005043c81403d4113105150040007808c0420b0365101ca400598418460070008024001c0c01c4206009601b030042840c1000e0994000d0081c131202c9481c280030281d100c03202503403c0280b10919400d02c0d08400009124580701c1c0103d642c11003040c0450158400400c1081c5083c80c1c0116008 = true := by decide +kernel

theorem cover : BRFrame.Cov 911690647 911870503 := by
  have h0 := BRFrame.cov_init 911690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 911690647 ≤ n) (h2 : n < 911870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
