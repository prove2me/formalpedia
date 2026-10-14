-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0814
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:56:58.671814+00:00
-- url     : https://prove2.me/submissions/5137477b-884b-42bf-95af-49ab93792052

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 146223021 ≤ n < 146402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 146224271 1250 146223021 146223059
    0xc0603050f0c07050604020121090c0512030906040312050708040905061201060605070204020304060e1e060105040c0921020a17010609110301030f1b0b0a200c0d020a08010501 77
    0x2502010000e0200c02d40c0e24100c6042030b40c000090001519184e0054904031892300d8441420080b1070162130f9034480350300c5403140c102e02440d410341070310b80343c4001d112820120400115003604100209411615035908417411039612031030581c0c1081d28004111400d001c0c0e81785c003d154020006000078400d4498020700d00544040342c2004905000d40e400c1400c03130320035119070780100714140001c502515050f409164000d00990002c908004204551410311600503042d4208024902141180071000c204007400340030180c4d010026003012401c00b401003140341c818000001d60611032110010000d941220204ea80603040e00704c49625401d80c401400c01075071a0003d01d610305600012000c07510700918445201d031003080c92450b429038840c20244904440e003507401c4030300c1800380419400c3c4585800010100c004405494203030f26080101200081c1d040c00c03cac0142003038405c0c840c6040100b01d901410f001180e00380d0b80b0500c1d0b4030104680c231801d80d2242644d548ac1c0000012401e130707801c0b03105145c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 146225521 1250 146224271 146224291
    0xb0d14031201062f0d12020c0303042102010e030403020402210c09040b011d0d0804150f090b12010b030703090f08040f0b18010305150301020d0606080106030204030b0c0f070c060305 80
    0x10000c41d000c0441c1c0080b90001c4941d99403105c1106102ca83c0079100340d440c9010195409440c24911071140340c595481640d0446013a00840003150500c80c0c40131441c2e000122a200a002001052803215528001d5001c0a817040e5800684e176540010071503800504208040049100da281010740319400b82c111810080c021070400c20004010340c4140000c841d0710504403060b030b03502d00008007032118021161000b251400d104000c08902c121090704c0820a01c4016981c0104e5845048001003d8120643c080040180180080781141c80b0492110b415600800c0e03448d40c40c2e640d0004110050004100c0c00341c60181e000c59484284540340004206036001e64820009607942c4007070090040c8103c001a000400c0c888411414561090f00040c0c1c01c0395124a159038405081e00020342247d200c110400030103507646104000c0c2680002500b401414141000c504044c03554950344071122000704140250540012a6a0001a420166510140c0004000c200103454690103030040000380c0d103203900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 146226771 1250 146225521 146225567
    0x601031811090106030c0507080a0509130506040c05070b2e0b04090e0d1403040501090602041203030c0815120a060c210b010e01030c200d03050a0b0d1403120106 71
    0x80f0174000d00456020940642c0c07281d00c1c01e00075440c2e21800b41c011054903003c00401300310b510050351f624038214000c0042103a001071141042d1040100729200400741a05005090000e407020030a580c1c03041c1c1d4040320301044040018407500050301c02030f2010b03029040140500302c000c959a4200000b0b0000d44098a01c100154941c50b1040d80d0790703e00643c29130000031510128510450014000b0f550803510500c00854000210f0b40e54206230b03002070b00910540e135000009942803652500403680c08040b2400e08820f941040b0020180f4481d0040ca0b4a020700d0300d00c033141111200403c0fa035070041d904060200445c854062000341030501c0d8240d50316642d002148600d040c480144070348040100143c5500900205443c0150050440c1d01411028000d0044554215280d440780400e14401c200024081010183c1009030460300c1c050300c4401800c0c94011450741c030ba21010b005819068008482e1003400b8100e25899146101d6199a40115424070b4000182250041210540030442c0142c1c00d035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 146228021 1250 146226771 146226779
    0x40e0c01030f051b07031704060209030120040b090d060515091608192c070e040206030a02030405030c0d020a11090702060609060a08062a040e010e06010318110901 72
    0x1c0e1a41641c0e920b000c0315070301400724200041c03c00200000c5d0320900746103601201d1000c065a203074504807000d48a142c2c000417500c5080c9020702c14100c00e0f004900c020300740d50400c40c8080c2002d009500032001c5000e80007403400101e0313403030141407841c40740c0c0507505200301d01d00306816110071411409000e00494840011601035004402403038580e0940f40d50f2120b16541c1c0b282c5030981000d08122681c5001d944403904004003920b108102c504007020703000c40300c04580f6420400c0c609101035116031807100d001424800140c1d41c910489070004940d880141c3c43c1d85850a01d40e0951080c10481001c9100b220000b110564000c030300c00301c0c2140218008819507a41400b40034807108100c501d040103810800004080b07150000390142c02000190204041a40303c1041518208056941032410700031a01c072040320700392254006401c0e10310400c0d01400c1030310b01040201656418002e003180c5a8030740000603500d910a602c8030314110300d0b00518910100340c3d800c02103684000c820350540140c807040000b03d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 146229271 1250 146228021 146228051
    0x801022205090f04020405180d02150a11040b130e160f0302030402030a060c11010207030314071b080d0b091e06030f07030809060c060903030a0f1103070e0a05040e0c0103 75
    0x184150b10b088945011991154208802024000e09030300402d480c3e105c481c1032408d01008079036401411500109801402a80c440340a000010800c080d900e04202e0080407026401c000c2d41c0845900d11902c2e80ca0304680010740c14031140a411a0101c80000d8040050708001698420201501c80e10703281050000d4013003c030140d07c002c64000e034142e8409a4004001505076000e040601e016292803c018000d008841d070981e48a42012380006e07444110a0b001a103401c50000d810000d00d042c9051500369640d611031107140000c40243c40404c01084c00140c1d201396400c80031001d08010300d41c400300e140075513211241c52200c50a940304ae0700a01c00041880c20002861a08600705c80001c090161441d60391303072801e0740301c182504c0d0044e0042c0074a1803001803c100300e82c0100d815801640c3c5900d00041d0300c1048130021081e100c800f13810401e0f80ca240030f24200480c0d40014291501c442100036000205044140729801181c01a03d014080079800c100842d101055140076070341171184c9240d4030b481e2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 146230521 1250 146229271 146229289
    0x30e0703020d0f03030b040f02090a080706210b0a0603020715110415020c0604030506090d0206041101052a011e0501180902030a0c0b0703090b1c150801022205 70
    0x9402c15621407610010801c1c04040142c42c9229240c0450b141c511b41d0007250035201181601c03010603401280354640d5180c4201000f000d00f220000404c8c1c2c252038100020316550100728407a01407003134031150521062a5803c4850b20000141c07100d000640d41d0303030b401402580101030550307114440103400d00c003141c200d014450036986141002c0e07052500300a4509003280703800320287c044d1702c6480000c00d020340703c01001e000154080c0000c0c2859281040c43c0c54102105003201c0006c54000c00c1c01c21000a04a51140102c100b081c0303490790b210000490822681c82d4007000000714004405007942c1103140541203440412091800d021160541000d2082503820a00800d0810380c01044100d0685442c2c1c1d20070781c0c2050004003200d00c101256150301d036001d42c2c150002030001000003040010705410041800c024000901740300e00c0c02c1507200c1c418500d1140761032828041529a00c1c411b0074442441c0c01f500c0034203a400001c6654035a219021208481d250030000d0406050100000f500d280c92006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 146231771 1250 146230521 146230523
    0x30c0812010609090506131a0a030804060201060501020d020613020f031e010b03011404060b060708030106020303090d090e071103130605040f0e011206050402040207080403150b090106050904050a140c0406030e0703 94
    0x800c0c1039040c2d8018121000d40080140521010230200d01c0784d0b0b056940c494104000c60184100d207654034105034000342525100d03000f0318190752000c040107020aa00180e0b0302c1c2c0c414038400d200ca448400e103100043d40180300c03042c029410311401c81c0e5540207071119685070480c05844030080080460b05030a00d03003a1000c1d4441418101c10b02c000040100d500b58100c41d0b00300500401d05894a1403540d201070b289d410a8111600580c004410000a01400c000301c0d50088180d05003191005d2038103c150f031102d03000801403800c201d01c040000c078900c50100b056400080700e90258140c119220100205a60001e100e9810130b02200a40004c0e02d401c00c2d08281d05031380d05280003118044068075804003a10010f0710890b041070f4200030710f03004210f07000c000d000994810303480101c1c24520815420195007002c00d840e48603a041000412103150458104d810402003558080f5a507541c85030300714020301c1c401c00e00e00e48101c0e06004121158203010000c00c02d441b05501e0800200000322580c580e5a0300e1804 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 146233021 1250 146231771 146231779
    0x2040e2b0c0615030f0503070c125c090702070b0309070b0a0909140601120e03070203120702090f01080a141c030506040c0206090a030309030c0812010609090506 71
    0x35429002c940c03076401c0391501a861507000d282c01c9941c0c2d170b1103009200720068269840e400c04225a010071a280301024010020340b03004507030310202903e4036841c12070381e908201d403448107905010010b40100c00702e010008100740c1c1031a40c080c140c13403c003c50840d503400c0c102c80152051000f1000030300e0a8042c1c0c038090b4915034000c10106040100890166002900904a900ca0314000081410502d001020401119a242e140300c2e031500100c1d10903550b40c203024580c120004001c0098a90b03100001540d4650b41c80408550b00c07004120140c00d40c456000080d4150107103200c84180748841900905295100341c2e501d9030340e079503a6130344100e120030700707008001468001c0c00c54940400c0c940f03140f03400008013840507510100f0b040301046400d151206110700201e500c4504100803480e0603c2900c103c0903a90002d0f00700303031a00c2c000c09070300d801e06400014103151345c41201c503080c9032013540c80c0844198810b14041c1d442d59841030000000009210398400681e621380b0100c2d40c0c0009005003030140034050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 146234271 1250 146233021 146233037
    0xa060504050c0313030c0804060306050a0b070302061914090c0f010c1a07050c0f0a050d0203040608010e0a060e04030203120105010905090412051e1305010e010518040902040e2b 78
    0x184c803240c102a802009504000c8441142008940c1d003100400c01490944c40020314a071a00c410700c05900c10300c0d40090018001400341c1c0c40407a4010800560240c06075100e20030f4101ca404001d4024081c10010102400ca11410400180c50000d611041c101c001c46a800c0c1009082004480400322034200420310391a40034084440c410b4094201d80050050404170b08004080504520300003020356041c2c010782c4004109130500a051105408814091010358a02410040050a042410b1042012002c00b441c00600b50381d803030b503003c500508010000d25199091504000b0f50b030340c0002d07061495007141107000048540c05840b401d012684050428000c80d40c65494410034490704044240c20310404000c50800217000003519031001c0140f800003a21105084030300c8000400540007107050260380e4241103070707581c5c1200564039100341c1a20101c0780d11220002282c0a0111140c00075001414052915001500031803686941d52100100785540d03c1140703101c546c1508487c801a011910714 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 146235521 1250 146234271 146234281
    0x3070b07021305070c021216060e04091407030b01090212010303050c07080d0c051203010803030415020f0310031b03030e01030213030b04030c050d11070605090409020a09050a060504050c03 83
    0x9030400900042c00400c003420351050010590b0f00455107a0005205d008005003146405a50f50900700d209100404450007440c6034010000c02d40d0007103e007805811205c0031403581c1e40c0c2d0840010581e00c0910340016000703100006039142c006000c05c80700b56980d10004030b4170a00900c00d981c4400481041403580707904e1500d09a03441c0c0c2c4903401e4408140a20f00c00812030602c10020340300350318400e0340d4004070b400c3c2a0030302c00e08040070303207103610015142007004014101001050781d0700560001a84901894841e0126000348281c1c21708402034040482008000c00060091104403406108098041c0f02c800d607804521213000c1c003000b0b000c00da0b400c00750b0b102d0354800c1d800703030510513541602d010b40c045d1207480d0320121207000c075005c40000b080c0d10500c2040200911071040751881da420480503021402c80003a44994690085c0000c0090107d4041403696440e00000b00280c0c014112194094a56a80c580130380022030b400e404a1b0b0a240f070001d42401d25200e03451061880104183c195114 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 146236771 1250 146235521 146235539
    0x7090902070804091802040c0815010c02030a1205040801050a1b0e0a0303030b0a03080304051b240a03140a060501021b0904020f011e08040204060e090307030e010203160b0604051003020307 83
    0x5007040c824804510305e500580142c44521072281140c8554844141920b0141e124100340c00c880c000550401c0803580c038107801078600107100c048140c0e000903e40d0005030303100700445a90050b640440225800d00051051020459005040040325000400ca1440b154001640c4104110003016008249508100302081c07080c0d10400082500401e5081c1e036656945812410341c000b642c050f6000d8120a0007602080c11003044140114019030780342e100c00000e000c644051a0072254480103520002410419aa00c0780d441202e42503900c100f2a0400e04001c0064401084207000301c0e4094402c804440c1d04c48551080203040705400102505151b542d00d600b03200c1746055a440903814080130803011002c8604401801c800d506080d0788440b240d25141c010401500c10b10740c0841103500d81d1205010101102008880c0e46e40e800d0304000b9080310080d00100e1941c81040c00327032240140c140d05060100441c9007400342c004c1034212410300c40d0313442e61142203918042c9403000a6169000d60b07000c205a02c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 146238021 1250 146236771 146236781
    0x3050423010b0607030806040506190306020c1c020d14090f0d050f060403080901140c0706020714030a110705120d110a021503060310090b0601180902040e0709090207080409 76
    0x148000001c40d1200b810000b050440d0000141100030920180c02c114013400c061007907550000c000c07180102180021500809800752030300020340740d1a000100b4484040701002000500c0c443d401c9240d075448402c0e14002d440d000c458601000103030302c400c0c1d282c0061903004140d961200c401000208440d60320010015003a1711403000712000d00600781f1190942d682400b40750b100d0303402030310b80a00c02e2610411a07803c6a000c280c0d900d000980c800c040c042d4049020064030f42c00d5a2141d0700590724601c82c00c10424a048a0071220700e51700c000103c0c5041c00740c1c0a030142c0c514546000441e003d15403280d0401c4111845107058218a9100c00c2c03040c4201d074800c441d11901d800e042000d4030a0300315150082460103000c211001181c50300041402007a0030200301107141c03110340c45030402008200e43d5910712151000381480307042040e0640100c40c44616412401d00030103140100315035a0360740d81c5003100e5440084520901081400d0000240e245240c021905016404044145840d0802c800200140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 146239271 1250 146238021 146238083
    0x4050f280203011b031d0d0f0c02060910020d0221030f19020f0703110613060c02190c1d011d130218090d0309050307020609060f04030b04030906030504 67
    0x9900c1d5648807006003108002004c80c140d0540d07001c140c030721301610188109443c1142c0b1201e01e03400f01c1a01124907500c010021004029482c004c04443c4042c000101e860080e070b414030713502040903e008c491403900050074040d081030540079110104031a0710000102800480c10a40703004c1c007040028210702e07a20550b0391348aa0301c41d02e042e60303d0f00c590f13000380203d0b044288a20f00844000484009154002c05210fa55842e66030041000f840e101c441c5815114260400610964a50b03a4034980c1500a11451251042d030610f401155012030802600100385072042c2c00d4481c030b280182c0c001d00c010049085050702c400024030482420000c1000b50410001415144a21446c0441c1f80c010b0b540c508001b071032a4000b040c1c640e21828140036007828020f01c41440e00501d49080c3c4c50400145020007901c0030759804480c83c0b40c60752025400f141c850311501d90704684502d00083d0200421490002060145001c1d0340c54056064548a01790f01700c90003520054440180307420038110000392002608048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 146240521 1250 146239271 146239273
    0xb030c03060c2101030b0703110c0d181505030a05060301090206190e1203130503010b0307120609060204030c060f020303100e06010c141f23130f030804050f280203 72
    0x540703e555446441088285c00c00c84142d0310140074410007030b505000c0c0300302070810f14500070304c3c1c0201c044509640705185e1001d034040c440c0c07203814444148000810764004010056001031400e085080042c21644100c0c1c031545564a0000401e045003414452488410303800350402e072910141e000c4041e2035002d920748940c01c00c07100d009100090389490070110b04000d0303400e0085440d0215802427006403480c1340c010500030b078036000d041d0620340e070001001d03c101c8d00da9108448a8482a0a0800240c0b01186000d02041c2c00060000308201e4482c2030f0904880d41a41c0b4649592000d98003240c9034402660480d0014292070401d10915841000051700208141011340030a500ca558400c0b504202404062558220f07607aa50b00811b144172115800d1821000c0c100000b03803802c4101000c014bd5282081d1111164a0020f0f903070103185d50300c071084140c024121080b80302e85860000c1020b04210790845c1d02d40600042a035213004000f6060b9001d562281c07014021011901d05030345140100b50090307030300d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 146241771 1250 146240521 146240557
    0x92006090913050a0b04020907030504120c110306090f0d0c0201080c0903030d050903091503010806010605090a03300302070203060f060418120207060809030306060703030b120d030b030c03060c 85
    0x14010813404c05401d20907104060649002c1c010044140401094130b41411b041600300000114159082d81d0003a1060a0281442c10789040401c1488c1c4485642034051083d03000380800604005040a0100c0d0f81d0022100741003040e140440380140380480090100f014031011601c140d0310203018021086028003260b0078000c40c0c00c61402991410f1320f02ca8901c6e04006200152810440c8000d03880c0c0311084045440d41d41b421101c641d0f2188144208002c010021602e005076a1b101ca00e0400107580010300100700c000c151510742c616508104070f01402400c0f05000c062454064002c2c0c40c110743d001006065107a4452130304940401c1c2c010a0641e00507a98508291003a5408268a14050244102c0302400c0300907040685804442e8000c402448038500801c0000600003040340e501c440c00760b84041e250086886d050340030340104480c0d40e078003140c1180c090700340e00d41c001361841b00d1040c0c569051058804030710a00d912101e0300d051040c0c240c0c200000261b41400d0440040c07900540c3c518082c20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 146243021 1250 146241771 146241773
    0xc1a070303023a0b01020c0f2106090610060f0e040c03021308030c010b0402090603240a08010c0e041a010c08040e090d02060c04120f0203100c03092006090913 70
    0x356600d0341801601820140c0500c3d06400220303407103601c10140081c0020610300340c0d100c0005411803c02c0e074031a449195036080b0344032070280503054003141ca03480008071183c07810a1054243c484404560407104000321800c0005c03c103208550202c0c0c00c01058982d0304070f8801000a03c40601040080c0700c0925808000c14291920110035031700003018400051600e0380c0c900d000030303800c1d907015000d2180f190b0b0061025040366074a103011680c0000ca4074100d4490034522007002e500302c808080b2000d038015041c403030000c1c00c0941074101d00c80c101420342d01c0800c0e0006402c108011aa6134100465948084000c2801e00c0d50046003072344042409020303006e04060b0b03543ca8443c007940044030b1b0b158245d0410f0082c81d200320b8040048641050b9a4408603080c14140740441030601c02000c009051080e010010f003065480500c241400b4282002080c81a00301d40f61000d005810109422264046051840f01d142050700a502500c0c0400408542c03402c02c42a00b04508000301418903d6401d40050001c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 146244271 1250 146243021 146243077
    0x110604140102010e0a020f0618130204090507020a120e06040305120a08010b090f01080402010309021305010f080102130927060b0909030a230403050601120c1a07030302 74
    0x120040100301100c09118040000090075100d03000580c812680c082401c19006960b41e20000d170f4902030a64206889180c00101300b1000d901180226400c0020600d91344c041c2c03401ca0b0010820398003051424042c64685600c01c0740d0b26001c21601401c3d04d5056002192135078070500383c1c50300304280100707090300b86620307625130900702040101d00342041c80000511010b201e802040d501e005100403000076040c41c2c582000302d2484902c2120700c80c10040c01b840002c085a010350700a4400d1a005440c0520100100382d04c03100402007809000d918620b510000662140140202d60614448282031040a80761480440113402803070304a41140c2c449009517820014194609075405014502c0412100301a13002c2c070002130030181a0441c0b40c0c000304651180c071900141d002ca03d07115518010021036205010740c042e980900d0b08003d000e8041c482c000038180b4008048004114050b810382c2a029541c0c41e2110f400b10685403d01525034014866840401e009030f010704008140700d0f40a0200f075111288031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 146245521 1250 146244271 146244277
    0x12031302120a06110a0c0b06040f14190c021b12060906060a150203070f0305040801021c0f0b09040b27010507030b010203040602100b061204030c050c01020a0201050409091106 77
    0x80d80c15944600880b03401d00180d8094040e004036620a15480c0c240750020050801c2c42c03000015140f40e8103440403441e182c507560f1001c11000220081000740d943c0081c00300070f102c80d080d900e0b4180300c02040c1c060311190100e4801c60300e2101d01d40e001055000b109041d410049100e900c04d659100202c2003044520074001d000d01071251103110003528407441c0c18810060904810340098803002d02200041c4001500003007222420740d00003a02d0740e85a1406e03d421211445a9000f240c1694008101c0481d900c010545030702d400b00740e1180c1031041082c00030740070044a4910215070341c400b00e264003140218241612598008100b807044900d580700075241d800050740040308071601c03030707655800304a56a41e040c4207028062200348051440d00f03152100095907801c2d804610341c1c04941ea081d41c03284603590003003103480801086150501e5032505040142c5000d410410583c1d050141542c0402c042d071021518212242e030584075203041c2030501032035000414000c102120405410300d9405000d03602e036006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 146246771 1250 146245521 146245549
    0x7060b03192f060f031807060f030b040b030a0b0711011d2e0c02010f0f060303090b030c040b0f070c080705040c02071428060c0209090a0512031302 65
    0x207000c1d42d182100041421444421030402d940200c600c00d082620f594a404541c0324040361000700b502c0e61101520a001c46c1d0111400d2a45c1c1d00c24000002441c9802c2105100303032101644007041000300403400c0c04103031600a07042e59416009070611030001400300d0f09a030b820006900d089400640500201e5007140c5035614075003101d10000b444442c0d0003100700031180b203c0904840b6200e420250049000340070152120501c017445c1c9600340c002c0d1081c401d51190711281d0241c0400e00c0703c5100b64003c0303002400c1c107001c15000500e8255010540b1008074040300d01440580d000c0a05d03041c41c0000c00c0e800d41e00320600c2900860001c10000003c9003221f861080135122030809410841c0c030302410801101c0d100b117a550255001603004010324112800d5840480c001910a040c0f4a03600c1003e00400e040a0030070103005102c1c90f5000300b0001d90050f0140d001a100303a51007003160301c0e0340402e1592040c94075001405944400da085d511520720002541e00301078880f425060003519603000508078814080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 146248021 1250 146246771 146246783
    0x90c14070804050f04090b0105010819020f03070f0203040e04020f0d0609050d0315051c02010306032a0b04030b150a0503030a0c0203060711030f0304080d0504030c050f011107060b0319 81
    0x1403d0003203140000d814402c2c00c00440e000c00c24040241d031b841c803030f555051113002c0c1404180300000304401a0400c0e0400041e80d090411561510103600d029002c0e04203a440a00045181c0d14080b49140000103ca080d504022070344032440d6074aa00f001901c69205049540140d4528000c8000a8050082821081c8074102800320b00300402c800900710342c43d40840308044c8c5031200c3d080180e40c8072048540038074441e02d1003091003401c450005802400d0698001460b0050148440d00c0185601d0b44c0b075084010641000427a441e40e400e50728642c1d0003a030001a214420075404158409040c0003140c0d81c844010b84204a1903986000181c110b0704020003a0022540e214800700c06c51601384225588040305040c03000c644d0040400c1c2503501d018000036515100400404101800300540540b1a412940a0284120701d40740c03400810303103048507504648604c01c2e00b8409016181c18011058000e0142c880ca03410300241e6110035003d4441c802d0840c2d00350260850201072200d0b410401044103010710 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 146249271 1250 146248021 146248027
    0x203090a0b0d0b09011503270c0f0603140f0a20123402030c01151d010501081302040f11040509090102040302010503160e0916030e03090307090c140708 67
    0x5203031101510f051480740d070f00c180380941c0140110101c8150300c4221015610700020300c07052103115003c0c503801d081c0844110340070000500c0c1c05c1026005410040d80c400304801c078106551110280c0c03c4c2e41d10146007a860f400c01d0710008003031210f0700040c66030040c9070620100c2c000940c45035140f1001c5030141000040707072001070070821010082501a1704071000880713104138140e0800403848612440410141e002d4000034500c00100e200b0000e480042c5010070003000034a02d005046c0318034040a11410801c142d449070600703402c4201030b002074100c58041e1100c091030303035440d000d02d00c0c01154204101d81c000d541d041150a0060f00e8408c0105c100c40c510074155560b07040008100351408002c140203900d81c0100300500c01030768001d098a80102080f01c982c011000041001d6480015030550030b03400040e04000c00241e60b100b281421842ca003070303441c01c005401d954030400e6201d120b503c0b4610b4240d40b00e1942085142e050358041c0700c0900301494201d08082d01800d0110041c0e000c04002e07640381c8008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 146250521 1250 146249271 146249287
    0xc1502010b06130b0f070b0a0b040506010806010807050c07030c0f03020a08071401050f04050301050406090b241216090b0108310809060a020a05010b060301030f060b010203090a0b 79
    0x2445940d0140740d007120440d00341000046103070505903640c002d100c2e01890215403810740e022044107449146a01c0229200a4507009110000034009000e810b40b0403030801c00031402d039500034003c05001d00010781d2055038076a292001901c260b846802141c4039881031200000208119120082c05000142e4642490b83e00d140100030124041c0d8000d5451a04046000c20150120401ca00e20042007800c199841d0084018050b1090182d40d10040d0154203000c200410055a60302c00215140b18030b02d02803046e140c00c1c2c0340e0f500740c40c0e101788030424500c984124548107141000c68101c18500101c11241555807400700100c01c0ca2803603219444854440c440d1905a6800c031164991003034881e0741050a800c800f1150044411804500b02c940303000b46580c41d402d11101104440740054050021660381541050003541c0b02680e8006451075481c0c0580c0020b9481d1010459040380d4002800c16040805501c3c1c0c0c070001c1250b0310036541940310421401b40d294a60001e4000101040c02801e5164806 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 146251771 1250 146250521 146250523
    0xe040c0224010e36100e070f0501030e0c1c03030c031802010c022413050306010e07050c07030506010b070b06220b0301020d050a02070c06030e060112030203070c1502 73
    0x2400e0380c000c0da103081c0d079001400354456031041654000315042d810390540e180d1041c4216030308002d03410040b013890483c0e100580c000000442d05141c250701c100400001000c0d81095842d29040d0041d80c102050882c41000103600c81c1c0c01020884140d8130a4031007a112020004820498040e020184051102080c00c00c1c150548500f5000080c2e9045c203009810810400d00401c43d500d090003414015025600e20654403200d00c07540800314460b05000300c00121110201c06c0d034200c540d01032080b0103442070120307450502140c09070480750250005842c6450702034054829410103080f10500341b00b41200040440c02c108013986c006d0140b058400d039200c2c1c190610700800b500003802180204500ca00071500621100596a0710349103020000076400711603c0001c1c064030030551400715841c286010700074881d403a5802060601c0c865070f20714400541d03d050907000e45541860340c03003464010a00410000140841d1203041500c244182ca14200c1169180c0300224165040349200180c15601d8450780340d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 146253021 1250 146251771 146251813
    0x180f1503030f0c0c030209091c050c01110c0a06050c13030803070801080a03120f0f111b0a1e020d0203030a0801030c050f03030d110c0d080604060b18100e040c02 71
    0x8079030319080100156a448045a440007031000038000e40407e03001a5250070140000040b2800103d0b218a0005541d0f50040060300180e080701495442e00040003105415081100c0d0030164010190100130a540c0300c03c001408000c03e4403402050070021140d9000c1050062409580301b01066a03c0f401c1000009001d828141c118401c15405400e0f01408240c101101e003807680c209090103da03e252030000000600b040c5491084079038108035001c605140b0400c00b920795940d00004001c0507a285e0980d4075615003d10344054400c410300402c5100f0350341162903044509001034951440c0702800e41c0400d195a00c541164400294004014030400c200391262200804007210001040103074417000070b440b0301c0b0b40c8484014803540c5206c3e00000705511802d83e0b1320100b110080e01c651340c0c034102c8041c101d584102c0d03419100301d15003140800c080307003250151410070b10302d0b0010050084101040c00008032414031103106003c2c0d081d2034180135560314000c0714044402e560140c418400071040a800d01c0d6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 146254271 1250 146253021 146253047
    0x114030f0406050f0903030a09050106050406030f121701180902060a0c050f061501030b031504120e03060c090603062101020408010b060c0c0108070c060c091707050604180f150303 79
    0x241c1c0c100c1c05d000140c80c00100380c0b90441e5100344009100340c0b151a006005280c030b1762260b9042400e188000090001c0d040951485a01a1180310410001a0007c55012204803c404004441c59006011002d00903808402c000d40d60140015001c05076000628150032184a034000034480e0b82c20b450822009000b91162083c5400c0100700f40c1c1802d400716445516034540d01410559903a074000d08542e41082403070b001001141540000341064107140e02c6d08286031400341d011601c84165a00c035410000780c824401c41c0c400c1c0425007403494400411a075a403005d0a00743d80070b41d400f8140d0780a0040120859101202c250005a0361071600c0704403400d4800b01540c0754410310342401070004051f00450b0303218000c402440c10319000c0e910070718203031903424003000050551403030940d07492015a00301452205441d150355814002c1020314441c9540c40d8818081c95400c0380c0144007c00c00908040440c0760403075400d080100f209204d00d507101d000c680941c25554040000c0003030801c00d1540100c0c03050307404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 146255521 1250 146254271 146254291
    0xa051f0501020c0f180c0304030f080c0403060f0b03070b130503011509152408010b0306010c060e010b04021602040501170601051c0209070908070503071d060114030f040605 76
    0x1515000002c0e450300310521200707000d000202c50b40c0c2201d80d0b4444400343c0108003112104040d0500160042041d042250224046400c40c84600181802050740d103102d10070380c1d4162890181156640ca0203040201c3d9040e031102e44601102c2038566050001c01c010b0403003400333166160400d009c8070200154265001900030391505000d03802c3c0309090206181540d8202d4404a02ca40da81c2a2141501c0c2d4554424000a202200e80d5030812002910011007500e02e980da0001690701c44071061881c0c0b01c2912454003003618850418002603403a00700001903283d0800005109001e0008103060b40c2c04034142d1048418054011011072900e44141303405040400280d00805c114440d4032a034515043c00f903076101e15001c2941301801e210344520043c8066001d03210026038100b2000250404280340121901070041da280482c3c103080008146007140c043c0c5d400c598500d20407d020203100c000182000b4100140b0098a00341c003c07041005501689000e007901900b031602d41001c00403030303401902030890 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 146256771 1250 146255521 146255581
    0x190e04240504090c180b040c031812020c10030e1005010501020a030c0c03081206040605030115031410020304030807090909020f040203130c060207240206010b0705070306050a05 78
    0x540300009180c841500d0095800081d261060700308400c010415600c1400100c1c03040004e0031160410350003c0a6440054400303005074618503106405841c2d00c6c0e0070340301c8100300c25240765002c13940459207820300070024010707201d0083c40100424103000c01c0000250209456100c4ca881c0103408004040c1000c50f42d040422481d41800e0001f921504040805020840000780c0d16090108140021008550000706d071030382c401c401c1c980005044021124188980c0c900880015a414103004a04c0400000440d10b101c00d8116a204255a18600c2c0e9100d0144501c2a4100b80b25901d840110b000300c2c0240c070740f11790f145024007000b09142425000100a1402c2446000058883d0300010070807040440300542c40340d80d1414003c0750a2164403001c2c10250300408002012074011070800c040d214641d40320320003507080881d01c5410b40d02442c09400142e2011380104403507111040584442c0d84168256031030150381c0c1d101c01c804c1e5107013a154090815921814410078a4034034041c802c0e1054021940c0301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 146258021 1250 146256771 146256821
    0x90e010602030406080408160c09140606190504030b0901090b0c0c0615012d030c0513060c02030319030501060f020d0e041a060304120305060904150b0402190e04 71
    0x501c2c0d020314400e2030b0034016000003050410049009445050070741c05100d415010f11400c1c01c505141c402e01c190008180303803600840350000030507142ca1003003902400d51450501101340c201d89038001c00006504100040c0001320000b0a1022100e005000070f0001040d01807203410709030380084015150070382d00803007001843d042c0e90700442d4003940015440d190718086014100181d400d40319420300c40e014081854003003140141d2202d000003134404140d404200c0001403030020358080c4a0158001c400100203001040325078410060401c500f03101a09a80c180655118a42c8103065284260340109880b5401441115030000b14660305c104244010407140501d18800760000340350f03100c0740d8015601e40c001441903800b2290b0b00c2900a10291506649107001d04040e5001901151100c000904050205110303290040002c1c0c0241d810100d0030004842c07120781000240189075005800503001e100410070100f01740a6601da1028907203525501400300c070208011200d028803920016443e02036054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 146259271 1250 146258021 146258023
    0x60105010c0312020307030e06090114070504030c0b13050a0b1e090f090411131d030c0d050322120206060108130f05010207052d1b010c0c0905070f090e010602 70
    0x402d84003607801a525246c295007200a800c174028514124443c0320140596524150301c04050007100c0000d4040b280c8a0410444441c400c40c4009800341c0b0081c2c00c1840f480342c403034005042c1c2d07000104d05540303c1c680d69000301e004440c190b0711501401001180c0700c06554910940c6400c00b0420700740ca14a011100c0000582d043c0419030f055005100d280c0010b01082154640782202000041100c10b5400c14000018003510b080c1140400f00301ca0200800d01c1e0700000130603102040070030b0001c1c10b000300d1504804c40d19038100410038914201c0c9400303c140c03100804140d00c02c00030b0040d00d0a070020807807544041d2034010085d010342e0400240d07e00300702c3c0b82a840003203642c496602c00104c03840c0400b80d081c030f640a8000c41c100900f0302d01400209941030400d50400301c08103c04194194054030490004d65160b5079640401110820480d6510f03070b1a41c41004d00340d00f26441103251070901e9880b0340803041100c000300d84d05804502150055003841e80c000c041000200300e020007d00140d81400c6000b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 146260521 1250 146259271 146259287
    0x3010f0312030b090a02041a0f1b070b040603020408010b09090303160519080103050d030c050a0309021309062705030403060b12010e0c09070f0207060e01021518060105010c03 77
    0x1070720701071600c0d0100075068403d81007144821401824001e1604141440d04020b40c40741c4100624444060210b0800b4050142695400c03c05013052a08144c050007818000305113070111035031140580f08010642e50f04000c041e2018004960300141c44901700007001d401c50b007549102c00d2151496030b0400404040c0001201d9015400303600c0b00320400c2d0707440c00c10f40b018090b60011000d40d00500080a44540d40600c1050480e0f0003841211228406850190304a0b0001108080040e600700300b4115280d0013074110806c0d0ba480a0601442c511039801490100c0d0341c0c4540c00c07034007951900c140e8031044180c420f9079450701d420b6400340a801812903032800e5a901c0f90b44001010142c60751603e480316a29400000f406036040b1000740000700d0401c5c6410b44038540350841c1840307120404e002c541d41600c03621009554400c81c0c0c00900d11141062415240c0300c491061542c114818142452862604482c506000b031602000000d407010003070540d1810305405070045410815510321041c0860740c08268 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 146261771 1250 146260521 146260523
    0x315030f1b0a0306231602070e04020a09090308010e060f06030f06010c0c09020403230d0e0a15020120090105030f0a0f1a03010c0230130b1e03010f03 66
    0x44661035040c40c041020741c0083d52004d46081e191081060b83c10888076509a45c4151403501040d86580d0010880340c080c820781031007001a4070280007440482c103038100d201d0f041800240146545941c07030020800703544054208400103152800104403c1d0084241e4076000b0340104d030741214080c007900215a10b0300004103030326a0110207001041c01c070f0340101517105140d5003081880f492075403035581210180d0b00901c400c85032030a0703100e10808051000f41109685084441c00b40503104a800401c80d11135841d115035940c0324412440c00200d0a000ca5001c410103100c68002040301c0d2207400800d10b20661400b490300e0f07040743c1000460242d03a442812641d1061a0183c2c211083e1100e51401c00102900c3d100501043c1c6000b81030b2046003001c3c3d4010985070000c40081c8403608102004907124a04298030f4404860b090100880d104c0c0b040413040410800b100180b810210241e8902d0b1300b0700709a500176460400000750901c00244029005540c0c48503803405149554540058000340d4569444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 146263021 1250 146261771 146261803
    0xa0803060d050304030807051506090a0b150310211208090c060d0b040509010b090606070f02100807110d0f03020706020d060b041e080309010e0a08060a020315030f 72
    0x1000034030540d075200034424195001421651070325100c1c50004500e0303026032001c0d5a40e1041e684080300440c103075943d0030310030344016014039865100c4a824602802c06885c0c62503004001c800c01c496407034850405140321301c0c02404030018481c43c00c081d41c1500028041031040902000b50f00c10b020401428016051124501e000c4030580e9800b401c2034242094401229403013140010a00d802c400c41c3e8000002001040b2000c1006443d1040c04900301c3c0c00b50310950350081118000540146003040c00381402600610a9510420300c0303500090241171300c820340b030300420b440109000400303070300050024003810a07000030000a41800c00c06003a04845d19209010550000b848500700004c903016543e407246039610901c000d50b110801c1c40300c03d4006004118884105c02850301c06000900c403d4030032108004040d40c0350400c108011116034062003140741d0000c004c40b20000b101a0100079007803250b415040d00580ba03040c0002403403408241040c03850b100342e010340030710700064801141c050103102d0b14032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 146264271 1250 146263021 146263027
    0x90a0b0402060f0d050f090a0f0210200d02060c16020603070507080d0506030129040203090c0a08060a1802060d0905070906030303021201050315010e072a030206180a08 74
    0x101c0051420b10440c0c103480f07080800865140030440745900024003480800d00d0245072940e03404803959075048400f80c050008a9100075640c094100303841c03a55032500141c41d000742c82042c0f047d40c1000e82d00160110319280d41c0b1241409400716410f000c4d0701d03040045510030381c0c9428915031585488002c4840003920500c0300101165595008104031080300d030344807028544034603e580454004110071982c040c029400c00d00c88201e4070601a0b40d524078442d061051191100707180b4284002900014401c079124030405103000e886507039920b5030f0001841f9a1000301081d01d0441090780036103900f060303244150410b101160006a5031403054036450f06000900103032107045810320502d00305040d03020480c00e601c1d0090100c240365064000300b0031000440201e030110390b0780364249603680d0000050f003c1c820a134100180b0180095130111030700f00c0b04503d04603002c1841c1050b80b6a96007813284443c40c013006500f00140406070144442588140714140b04503c07240600181c1d51508100800240104000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 146265521 1250 146264271 146264273
    0x1050c03040b04080a0e0a120b100612090501091b18060b0403031206211a010b09010c0309030606060e031c02100207060e0a0501060e01090b010219080702090f07030b030303090a0b04 80
    0x1c010000313000200800000d40c007540ca000c01e40c42d52000070000d0f01e0b209c9007a00001e400c40998203440c41114015030740d00c5051810303101700c40024009000200c50340c0d52a5007c480c007042412000205c3c414003a00c1c00b0350304503e040e51110407858030b1f00c1002800b9062640c100148030b0200d05031b13400c407034140c100035844100f2500f080d402007030640c010100c040d10741c09401403820502c650030213140d4030604242607016420a8282e4644078248141c003d480010005a621544038000084a0500c241400c0c0b0495440341ea800301034400ca90401c100086405841031024030f0100441043c080e490112992000c0034408000e4851203030410301c03442c1c0c6800040990400c80103500c0030702004628015207400800a2401c1e81c084c08040c4540c03500d65840c41e0010070040628841d40441100580082403e000710359610348400420b007800340c5131a4403c4c485071000d0307200c6404207071088440700211400d510f00b4640140c100c42060803540e010364800e1040007500c8000240c54100d0700e41000120941e582c503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 146266771 1250 146265521 146265527
    0x70303080406050c1303030509121504080a02030708030c07060c0302030402030a14030d051e07023405121c0309030905091008030a0c020f06030402060a03110c07060c0501050c03040b04080a 83
    0x41c8092194045d4428000082071650040241582503011190303500501c03144d07004180e880c2403005148240160309804940020031180c0105512803090040d02d0074891151036400386900200c894040d03c9500040150400a0718441c0d00448201800e0450940c2003030b4012a40d40c1c542024002c201c060a500c8000740c20030200240ca860078a0800b080c42203250044c104146c0d202c9959056099103040380100e448140082800c480c03d6a10b09484560119100c00c0c0b4580d040340c10045002400c4000760120b0351b901d9a00060740144040070040840d003d0310400001840c80035030180c020145020f030b50500007540401c4003011240220355600c0c0c1c44e110844020816986079020700c0c003c0c4800141c103c40310b44c0180c0f220340800d0003250440d1141d40b04c601441011705c02110000d502003010030a41c4e01842c000c7c3c1c0300b010110052a242c60800c055203888034980304030781d000701c1e001c2540c120700c820801c80f0900030581c0c0110041006401d50505583e40341060b1000303000140158000324500300c0c1684 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 146268021 1250 146266771 146266777
    0xe0102010b040204060512010b09130b1c030c0b100501021b040b0319210806040c02010b12010f0b0307030c0632040815070516050a0c0306020c060702070303080406050c 74
    0x141c0100115622661940043e145510080d5217a4141707a0150000500344014000d441010700b01904544481e00e0b454130540051030804202d0b5440f602445a02588171031000d801c090701c45c0310707032240c020981c114100301c2e4010b10010700389041490b0001c02402640d0313000c5545c10405030005038200003580394900240283c203280c09071a81500c5491244909a5030101d810a1914012011a020820001e80050004800d209030340b02040c503000c08280c003400d2640c0480b1342054288000200c410a00d800a545807130312454201c1642c2d160284416504080c3c883c0740c400420850050030040e24558820385101d440c5d00ca40e0060100100c0c0c103100001d501003c03c20705001ca0030350a24510551040410285c0142c06640e035107100383c1604503e40c0e180c1e071665a0013400307140c80391030428000381010010788035070604c00c0b03d040c01101902c1c000240030520380710255200c1c10025071100001556030b40782c054020800411984490003c2011130303008588141c1068110300b0100c2d65030703134031240c0300a42d00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 146269271 1250 146268021 146268041
    0x10e0d091e090513020a170a081c090819031b0f02070918030e010305060f040c021207140f0604120e121006051306051305150904050d0206010b0a020309010e010201 72
    0x1e410076040000e00300b440c1020700e40e91407086420704c00040e01e9587c54203843e9a020303070ba000240d002c40f42d41c0c0e0106081c00054007080d00c820541d160700301403401918003a5540c01504450114000c52210b8003c400c66440d1411010a450104480b00750724204c070004100c00007000e024005d02d0440706820b14070900a1b038028080c5103000b0f100300e0000c0300086110301c0364004203400150318240417030716640c401e010b080c0c0500e00082142c800320380d106003044001e1880881d107209511590780c000444503410b201409016010781c1c1094881100c0d401c01c103060206840f0303207001e6900000b04100006814001c0441c135140240b0785501039100030008250141d030710b650000340c07034844c0342410007001210340c20600690360300351000b6032a10307410101102a60380901440394406d541017044407404050f40d104940c030041d10f1111918400c100808140c1502c2d043d40d091300e290700038558001c012a01007022078010f00850120310318009804100030b48a006458034241044501d01094449038802d400c400964 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 146270521 1250 146269271 146269289
    0x8061c06020d0603140601180e0c0f011107060903020f01020d02060c0309120301090f0617070b030c0708030c0301090e03030411010806120601060e01020c15070f1403040306020c010e0d091e 83
    0x240d003105c11a00d81e01c0030244034844e089803180e0083c60030145540540301590517a0402002c000d10018104141d4140c04440c080c1000740091440000c03560420102008000c00d464003a80581180148024240102100340c10356000202490b101980010178a6209281e500d01644a0300c401d141e2900348030041541070103101c0040008221a540383d8040d01c01041d00250803c0015603c6260155001d000304a0b525641c03c5400100009a070f64801103030f000c0c2020844d185824601e5452440a400c20f0b19800606a0040010300c00b80745540305600240305008011825468107985102401070500035450420000302c000c2030300c60f11444819002e1100d900c040d13034841c3d84c49080041003d098070341c1e00c40c01071044901d402101d00700481d12503801d0014000e842c4c50f0040c151258803401403440403c4440d481c05103001d182c1103d062000e480034600c21100565594001e42580b420b40e84402016041a08449908000582c01c4800d280407100c101c07014005014400ca00c0b1135041c84140c2c8403943d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 146271771 1250 146270521 146270543
    0x50c070303140c0f0d0612061b0c03050f0703022a010f030b06041203020f0a050d0f0504030b0f07020307060c0531030308130206040311031203090d1d0d05060708061c06020d0603 78
    0x81042a0304449c5106001c03100c172450001e50340d4401c5402803801d52003d03012401c1044900540300e40e610003041600d029004580710300c051b45e0001a000e4003241500036220a04140448207587e10230b814aa00064a1809003c141c140e807000650511440c41500c01854070764100c4803c042c0203128030718451514000b41c0d14161114100f082c2c41e0403100d01c00310009019035000e5954280603205850a481d00309503480010350b10000d80ea120610050902819888280030000003d90b0b07600901510b880e0543d00d0945410700f031040070440210f802d059041c3c000b89205046245003541300758404483d01481d2051164035a4030600301c640701d00000294108400007408018400428006030f05140b05408907044188088001c10041c00280c07a8007140c0d0b0480600e4000b4107100c1d4040c40c0d0211141019801c000c5508400141038502003a0102c42641040041000440c1c02c040079541c019002e403840f51000000c46615180340401201c002c004070ba011a1410f1226500da00040155a01c9070300c00e11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 146273021 1250 146271771 146271773
    0x15130203070e0406060908031209120313050d03020a050d052e05090711061f0b04090507030e010c09060309080f0a0206090c0406142101050c070303140c0f0d0612 71
    0x41c4000000b50140940c1c00c21000090300e5120b911100700b11424140070354105641c1e040c18051811024018690302e1041d400c4030741c030141840c001107014800390200c0b030741c00c100c06181c05401c01c07900c0740031441810710600101c00e04036004000c646a10030803610008460340d0f6900241c050182166683c9010400d91800f600c500d01403400f900c080d103904642448865450038012a5007003c4500e402c5416080400030074051803051600b908010015168500d00710b44426440c0c84030b0b08240d00040806031600d06000c501c60701031048006d000300e6540244030098101d00090413a1106114407400c1555900150050040080075249140304103202a0b0752a01c1800c00250740e50300584400c8014040d110300300e1003903d054811181240d502901004010040034204484000104034081c0d10f00b12010200324440c40a208803845014070007170507130b10f502503420001d003100c1d038090000b03003c408142c00b03001c01c440210050390740c10b42000070810360b18601d940070300c030240c2810b50148070341e02005a0514 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 146274271 1250 146273021 146273027
    0x2061b010612031211090d08071203020405011b05120c0f01020f070b01060306030c09020c010f05091b04050f2a0c0102030a0e0606010804080d060f0305030901030c050a05031513020307 81
    0x55211070080c1d54040b500043c18204c2d1040324010038100c84000310820065005082c109100d901c01400f4900150500400341c94002c1d40000f104420400030b42d0000b000c2c450b07503800a4126880e0b20b80d000040c902e600b03032030745c516070b4605e100da90041d404c000100c1c039501500d0040103007000f4401a07500a5440307051102c80031034036420000084030401440800807071568443e128800840f42c0092442e0143e9240c8201e100c005d602801505010395200ca180c46082921405018020715007140104000d8066a481420044070685240c0c0311358140402d012803440044c0500f9000140082171707035080440c0081950a8040c1e190750702210035804620f00760b07440010740c09517224a8404100b885940803a414076038403070000300e811034080f841460100c0c2c00300d020880900b00b6180c82040c001819900d5020b850705036401c590003101c60f90b0001940300c00e9542d241c0070740031110381e85081c490302384046010043e01a00008081607005209111031410301d83c0e440c2c4070740072041c800c5a01196a41031440c1b0003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 146275521 1250 146274271 146274299
    0x15161b210b0610050f0304030512041109070c03120e0a1a01080c0a080d030b0a0f0b0c0f0303060109030308040f0b07030b0109050306100501081003021017010f0e010302061b0106 78
    0x180e40404003540010306604000102010042e803540d5013628110718040301851641010b0025030030410280034003900c04400c6c030f06a601070780c026807445d24803006803002c00042c0c5500a0014042248004400c00025000303130b0703201c0400703d402001048000005200500d0480350b401c024100d5001080512207443d001210700d410f03650002e0945681e04040814042ca0f18954802e01001c1e920114007102498441d6204c01410813008000d1008103070f0b40e024107032001141e500a60141400011010240481000540601c104802c003a5040d4600400081e010411510010342841024800507041003058243c1024041c2c1c41032100800d414100001002805440c80c040e01240381c40314042503924000030100c4c4036248a8030b100340640d00302001114410707806400100f040705000000310050750341b005c0c410b40302d50446c1e88081b0b9516184e60051076024040c2d00c9424106840030051210140c03003481c02d815a50107449145d40e80020700300303007019448048003859165180100110b113680c2d0381015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 146276771 1250 146275521 146275523
    0x150e1509150103170a0c06020c010e0c0414010b07030c020d030801060e03121e040306140613090209041205090a0b0307030c0509030a110d08030a02070215161b21 71
    0x80303401c292401500d55100d01800e00000c1c15000f0b00c06800720245154000400c145003403860f100c41482e83daaa01e030340a07608420b170183e40c203035180c2d410040429010005130b1004101103400f40605d25551000706902c0070180078040020800041110905018861055090754040c01c14000340d015810300903c2c8140a0090200080410040c0b000c24640003400c1c212501c001000503103001300312200421240f011001d0504000d41c14040000821114401d540c20202041618000340c40c01c4c1c000c0000941d0404070204d074940c6441d000c9005611078440c0c5d20350140d0310480100c00410401001c0e1203d000700e803071003039029500302c7c00407580c4410140658000c00842c2c07018405910051002c1d58540501c0b00c105030158030084901010400180c415031400501800849a0b81031030b4543c0c2806600481d40000b28503000220f60045007082c4402c0520041d8140d04142003c503004000d41e182ea10011010781034884000c80365044044404400005104000303107003022550401c82c101d005274607404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 146278021 1250 146276771 146276773
    0x130807050a0c05030f0606120703140102090907020a050705010302130905070906030c03020403030c0803070315080a0c060c08090409020609130e070905010e0a020703030605040207080c100612150e1509 88
    0x254074100001d60341c8500521728064a0b1581c0c4140900100409124800640e40714242000001c03840400d01c0c0141c00308440c0025030340f806114148480120003030054021944050742d0900881c5010030010f0642c2c0c07007441c000d82d031002e0421440140030915085282442d16100501004940102161044a241c0e4409121034842d030700040e000c034020b62001401240340c880c5500c0004806a00440d48520142400a0172484044618904500340d401103002503204400a205110f5580080d81c01400280f800064516983d5681c15150080c00e182c68012610b981d25041151b81d00c100340c2d004280054443c40071000000c242c0401f40254058104840c0070b403032808140340180d03001d43c50507101c4491540d03041ea04d4055428009600c601e909504040e44c94101003829070300c600092031042c1c01060f401e500e41514155031428400105d00c4048064a031030340410010146940d00e808007500100e03800c018414900f4214050b09600d0a200c1e80707406001030065a0741e0f13140fa0030a0060316010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 146279271 1250 146278021 146278043
    0x31e0b0307141e0d0b041406060901150c05070b030703090c0902071115210610020c0f01030c02010b03030f0318030414040b041d0303012306070605130807050a 70
    0x10140009a8100c481943c2226900c4031103c00010340c5001c0e5008618068462402c2603c05e4607590301c0404d06076800c8410554203102c241016000700090b0390084000c4032000495490031040490050200c08080d0501076894484418018180072105c0100841c8900036528601408001d004140d090710860710142035000101c0c1014aa01c25200c1659002c1c10b01038100d01d42808004400890a44c4a00c1c000c070104042c98004140c450301c200d407101401c00003030a50030320a0800011a01d50000b2038115070100103c240c0725603812540003540402030038005010b805c940c0c0c0c01c902601c6070303000261b0103100000b8603000d640c0350b40b0021803050004200401030070000145803900d034400c84c0324042c50740503081110880c618042d801401c0892005000160690900909440061207040c864007150408001009100c81400800003070201e07141d03001050300c1d8200006640c5001d54000981810b582d0702c0025000810f58103203921258020900f59195405444e020f41c2d03960030020121502d01c00f013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 146280521 1250 146279271 146279279
    0x60606030c0309110105070213140a0b092a0d020c030307090b0304050601061805180709123804080403020109060305060108040f030306091508010b0102070803040e07031e0b0307 78
    0x83d00c00c003000725920026502485560400446954101041c181d80c8002e10062681c5010420f10a820966442542420861405241c000c0032110310180080c01813040e401004100300802d24110034801c13014000809416004007a241e8601940e1070070f9451600c00140340364030420020103103209903050769a202845484044400c11030100f038030020310590141c4014816580510042200d68503146a40d0103002e42d180c00003801401d40c4080c0124180c000310a004083d0384c807002a002503c401c880d04840c00d03110340e843d1845914a0500021031410481190750021307691b6840301e801d888a4110608141041d052510b100e034003912040340800d1060302c0005685000f401541d201e0305c016180c07800d03140c0c0d4a84a012990300d0b011401c60825503034100218401540d40f0681491600f5031044800103418a0300d40e6086800090001c0e0543d800340508201d041c40020440f015690034410350407050b1030380350003038010300641240362400b51002011455108450380c410360744d822044040314106a61 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 146281771 1250 146280521 146280527
    0x1314090109090c0b031306140a110a0c0605090a02040606050307030507090b040513060905070306050301060504113c0711090105030c01110a0602040b030405060106030b060306040e030c0a060606030c 87
    0x1141c1001003c96295643c01c11440c2090703405107030b100500314a0040180b02a0707680104036515508a2103166003080180026681c030b62154003404545e4102c0b0781d02d0701c1c0381e10001800756091154000c0823140c03107200140c040e2070148808800c50b5406030060110030f85810004d04150011640640000e14040010754560311039260310007180c0900105d10303d41030801c01845070030b032418441d07108400c1e2180d100281c0350307905100b00f40c41644183d90001d0590305110805003958401c0d402076104505003c0c152001541e68012140740465582c4262000444c1c4c03c0c0c1d40c1d600713401681740120888009240c3c0107140c0b014800400c02184070702c0c40180489074200030000501c030207000c0d0716056070008800c410594000c50000c0751032807100045035601c1546903144010307644a6040401c0d80034000c020700041041c01c00440c1d000d004181002d004032804100820014000180240c0c1303e140c031900000f00e804400d20440703071140c02c00e41c15103a010384c490628001074502031052a00003481c103201c6901c801c1c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 146283021 1250 146281771 146281781
    0x20f190c030210051e09010e16080c06030c041403150903070c090e0a060e03041716080303040f02060304030302040b0307030606020d0e1809031306080106020d081e09031314090109 79
    0x12175540010740f050544002e15195a030080c42804d583d13603102801c40d41c0b0801040100c10020f500044201e600f070920448509000c81d40b04514061401407050000500105054a0584000a10820b0394081010004c0c1c5840043c4030361600c0382079100240a0155008002030000c07a002c1c24600c160555207203910f000b02e808c44100860a900504201000158030790450410729041404070b03402c044e200c540714500c0d180c4201020140358441c95170003050510350000c2c0c00080c09580e01941c218a85901c9036080c7e036841c0b000080c072800e0000001801c240c041d40c144c0c0d01038444c024201e40c4070315040c1400b80c018038040c044d1b20003500c28130040c1011703e8070a040244c00114040c180180100b100c00842080da80040d1684189000902001c2180400b14611030b0090246035540c0e40c440d458450081c0c182480d10142c00d003001450341c10005001400d010202c4001358860042c03945a950704075aa0030740c080d5200701800a500200c0004000103040c00480d0b0320002244c2d00340c1c89036660315049040360 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 146284271 1250 146283021 146283031
    0x40506060a05160320031201080d140a02100204120c0506270409080a020706090b0306010e0d051509030904050c0711010c14070e2401080a020f190c03021005 69
    0xb40003007224000044080320422407040c80b80c109420880142d07101d4241c003003042d14807040107900129000103c0d22110313410f2401054504094500e401c010b4000818401c004503648940030342c00107121003060700c20442d1b4400030520b402c0071900d0300c0d2501e0781851051180c402c05d840072211010041a186088000c480301020204681003611807101c1d10725210f030718170705045a40159560500c0002c07500080041100a0165019240f42030801c81c020b84505190f03040140c0540c0c091040000d1640c000c1e0070b00400c80002c50341840e00001918000b890046404568074100c103140d4240040d95800001400588108680a00450b41c0b40a004540b5005001024080e448040c0745180154044c006450750540510051a0b03c0383d482c0c82c40c20b14140096119000300c4207031004008500001e80111101c00020102c200c00c40005000002d00da80ca018102d90005540003905141040320b09048501841300d450000a118107001005844c2d02d51b0b0b0745040c1c01500580d044000403160034803400e4825 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 146285521 1250 146284271 146284277
    0x114010e030d2003030a051e06060f03090102090a030309080c03120d0c0c050a03020703030f0c0c09050604020d090c030615030f060b280f12030806040203070c0f0303020702040506060a 81
    0x10b000c01020894026a468072502d00c504007082410450007810300045105034241c0802007003604104e92059618482c0b45004c00801c06400300740821a030f5844100c408001e181d0a510741c4940302c0a82c02d034020b1284e0300c5056400442468004109034111400c0002c58800c801a101801c202000341915680c2e01444040400c008220b100b640092a910414403585189440c010a03407856441c1031800c41c00c4113003600980d220744010070416601c20f160f090317400300e10703d400b1005034a6592541c0d21200c0c28040c031040c0d151140001049902c550b41555800c030314080e07090060940a00704040c00980c240415502c86003070200a54200c88404030400840f6440600c04200000b01d864a0000f001da00076001d52100c411390b010034903805500b5450751852010045002110301d030120108c0c00c0c40c065031210a84211000081c00070940040000380c1c002019a00503a9035a03842c1000c031280f00d05940c00030010040800800d09140d0f1641c00b41c03040318800ea50400a60302c518040100074084c00c41d0071800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 146286771 1250 146285521 146285533
    0x3110301050d170f040e0105010e030d1d13020d0b010801081504050717010e0106152a02180f0705190e040608012d0605100f09080607080114010e03 65
    0x1400c0404480440a020b02081c40c07982a1096184240f43e100300241d0107041c0f030205041c40340100030700c841401060302b401c00b440000300c800042070b15034000700c482001f407160f48540751404102c250003007100141c00a00c80740d807855080031018025000203c40e104014644082300c003442d406024400d040c1e890200050005032000d070750401100c00c0007042184d0b03501401100103003803c9145032803030242c09860008110041d080510342c0c2102c0555001058852501022022060300a01800c844400c40010241d12443c180003c40722140c0200c0b00030b4001000c80071a0245114100400b802803400c0d084010a0f52905442201d190103a07007803104900c0c905640b901e242500a28600701003000140c4003259250b502d0b0901801c4071190099520b040d46008a64110103d980ca040092400588410030103142880080703815002c4079801e400030300c10f1404803900c509002c0d01c1142c00400f510070846031507207030105004060700c00078441c117440d410341001804003540c0282d0364000340002c05002484 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 146288021 1250 146286771 146286779
    0x216050f1005090402030c0d29040906060515040e01080307170c0a0609110f01030e06010504380a0b0a21090206070f020f030a11010e1201240603110301 67
    0x90128049070300141408010014152540c0b264005144100000781719144c689604000d1003080d120070103000c039030f81c3d80b501c850301e800d0124042d1700c4214090150390019010f03009140c604000c01c01600b0007903200c0e001e2441c4055158109000b0000c2d205114400c04c0e440e40d940c00b001d039a9000e0030384010306581080100f54220f402c40340c041c1103140b44070400c54005000700e0702c1d0f10003250780e204000d85941c41c00c00e04d000804d00b0b10610a41c1160b60031300e0304205980c00c101d40c03e900c80304180140fa100301d40720801040070700d61003900324901c59480210701d84141040314100c0b035181d80114001e4050407155000240c402c5494094411010842d201d0160042200f400c4c007074186010440c501e101da544500c8400541caa040c003402c85180f040c05103144918140c01086031404403c68810310030307404180300b40d0010300a01c0d01e070b13504001c00703007040c0382600d5140d40011400c02011040304450345c03070604440c15003035100007078400c8000180f0701600702d0384d282c4e81d046003910f4405961790f4249404000403c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 146289271 1250 146288021 146288029
    0xb09010b01020d050712030b0d0302070303140c07090203070e1203090306060d120f021c020303010504060909150b0f04290303090d0809060409020a090303020d02011517120a030c0216050f 82
    0x1b58484001d1319001441030764650000705404a140c8042d070041c2d020150600070941c11541c032103180e0b1a4041c0090a120310941071554501c0c09001c0d003805907402001040b45203010380ca0203006200004c0801284e04400340e45550349400241c0403501c248610030102e045400c009014400c4a50801a010588000386c482912150704075481d134401c500c144281070a0300348a00c910701c2040c040e40d60145d99254900010030058400300d41203808503528100e1408002041194030922180222001080f20042c80c2c00040001d55030305001ca030043d06042d014aa8003040c003c181028511050001003000440b40516641f40030300c4440030740203012408010046500e403005020402c41c02032203030b403420351500000070598004864440100b120b03400244109501881030b0500c48190780300803c620701a800401560003424410740308035036010000b01000e00c0050003034038880740790005055540c246000d00100145601c00c000c5005005200c5c40e224403060980300a000c2700d10082c061000c5c20059001c02c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 146290521 1250 146289271 146289293
    0xd020d030903080f0403061d1e01091203050924060d051002070b100b13061b021509040f020f0f09030a0f15051f15050909040b09010b01020d0507 64
    0x1034040c0401c505001000940e070700001c0015000c20380c81310340c07107525525040742510303684040b01c0c072500c4010311344d00303111840002c201030303024410104503004078400c052582c0104110500900f807070440f940400403581d007607000640101c0d0b1440441c0d00c9a0803d4204030a840c10042e1110340e00401c441c00b01e0003034a0325009150415000d07006441900c0e0340302080404076409801c04031495a060405c04c982c3c1c801481c01d01004041c3c031080c0307030302e03190306140b000c2006c40483c003840041c001803d24481e18031101c2d099501d00f0642c0508155200c848140143c00e650304440d10ec140300d1810590780c5d10411100b030090303403d441a8503a195040c4544840810041d800c0304541a0b014407607118000007240007132804001c40c600030311005502c584010103000c1a901d00030300008001c0502a4007423210480d001d100b2003107a0100080241107403005a04548074401d8800c259800303640b80091000b44103141e0513090140c141a07008102d03140c46000160780301d15201440e50f01194041c011070005c030303e0708101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 146291771 1250 146290521 146290523
    0x10509040213030609030f02150718080615040f0204080c040518070e0a050a020415120f1d070510050d0203060f04060308070302150108031e0c01111806090d020d 71
    0x981401c1d0000e9202c2d0300108035600a8485585603c03469080c55000001020100c01c244007501200000b080940b01e500000307400c200403c5501c44c40040001441006d0b400940351040c26030301c050604000802114000c00b00e268422440e0418400b04210b072231085400b2144800050007428290400300b1004023002040da15514050840c40100c0e61030070302403580504040e00f000c140c60308105c9410760440700000d0103255058410007003407041c0001e1a031100261034092415407039036140c40c032110001c1c1c0700c8a54040c0c039060500031003044510076200d4a2850b00608021104141c0c0d0703582c04c111185000c43c140c0c0c030101e082000011003620b104c0e0000d591001000c1c0090300300300c1e880d40c08a0704807113259105448404010500008155043c48580c0400c0562150b091165041000c49a203a22039550340c2c00601c0d0388003946110f40b04164080e50710300c0207400000c015040c0c1120303100680e580b240d26020701d8501e484007407012a140400a84040300b00152880c88503010a03400d00c130824001d400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 146293021 1250 146291771 146291779
    0x110301060305010903050705150103021e120f070512160b0309012414090103030801090b030a0606030b04021201020307080406110904090804080118020f0f1801030b042f010509 77
    0x140c04804120709000b40400c840c8170f669110b43e02c4140c0d082003030801050000c04000030010500400250340c1d2100038030907091a803048059403d52540000c1c043c038040355504d000c10f006100c401b00160102040030012100151150001c0d94a035400c5c86884984580002641da000d003901030001e030101d04061a4003404e501c0c000902100500c440c003458903c90110a0600c03502e07004180700ca00c000381d40462030303001700741c0e40011554150782c1d015014542c14020120119501c603285a030a50301006061150343c0c0140003008216103c1c207200000d20403c4400b640607488100d02220102c03014401c580c810346040e1380322900c6883d196074000140c080300d0301050312084103000c1031800ba80c8901c079014041d882a04000d81d11407400c51204e082d10f003c6038850300407014808004026072103218043c0d10031241291188081c0c45a00c0004401544210552841c0070064001008102601e0400d43c002d500524409083c420f101203404000c400600d0b07003c0c0f0180440c01d010400394041c001505441000030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 146294271 1250 146293021 146293031
    0xa0c090e010803180f010c0b0a09080414010e030f0715030905060a0510060c02030a060e07030f061e05090a0f060e03070c0e070801060503040b0903070b04050a021f0c110301 76
    0x30a69554614080e0007000550308005550010b21104880c401d5200000340c1e800c061074403040300040c002410f040350250003502d5600c0054100c05a0f58085030308194004000c8d6141d64440110340c501c1042e4610340713804079100704070b10144e0740b400003081902d0031406002090524100004024100042c3c09003109142e21070345a0400200c091001a2007040d240800180c9854215603980e13644c24240d1004003403103044a008000750301c020920305805a04800b01203051000d42d5070091815016900152070811005d54041c100a426000510b603005640c1c455404c0117900102401240e20544142e00140d0007510042d0006140001c0d80b5841c1d4010300000410780f40b944411130541d0311081d0704030703101492250300f44440500441115000002454600c05c590304145010b00503100c0908040c009a0550002410540003002221205544105000341c60f09003440c0859031942e000c00d08030712400c01083c92140603071015080e506001002d90310030508a1107511518510a41c01c40510b81554980c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 146295521 1250 146294271 146294279
    0x60b0d0b0f06010f0518062109031803010b0105030112050114100e1b03041b0302150c01180305090d050a2a0b090d0b070e09090708070b030c030a0c09 66
    0x30191090004181011440c0341040004040041d14040340060003000d002d95054480340e051141e40180c41907803a41c0e503a04140d80005044078140c10030100045a080401074800c0002c005840a0010050381ca1040701054040500781c0b26003903400ca0000d032051004010204260300e00d64151402134000103401e8006501c41190a04101d030000b00440c0841401c209107034044450030742c4560b41501030003030404030710b803181810721000c0c2c405000000e440300c843c0340d226840403841008590092218124881e007041142a5400903a8080a04c0d440c145c1c080c3c2c0c807000f00125074610ba580c103540303243c41c05001d50704009030f01940b94429a01807107402080340005071090144000585072280c0503034000103611141c8442c3d200c0740c024485c900b009010600745900c0750740c1c11080b13040d80b000d0f89005543e5018412039000e114551100e510510100c103104601c10007155000070303182d8003070550b01490307141c03003611960b84020388120300c2d0382c5402c000154041e15540e012580700306031458510015680c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 146296771 1250 146295521 146295533
    0x503060105270f0405091209031f0c030b190b0c150103380c030421030e0f010216021203090618090612060406050c1306020a060c03020f0403060b0d 65
    0x42e01c024007040d1039082030070001468040c25250442c0401c48050003103240020700240c03581074984100608100110311541c4980c1c0c28080881541600c140000f22040100501000317004e003260554042464903480c0c542c2401d0091032120000059180250200d150032044101540102e43e440b406e40140e54003000d555540700b0b030305802903008100e0346028a42d80d810304241c0001c0c45481034948580a900c0c2c448284003070703500ca6444101c41640549a940f1401d0801d100e00e10320400200ca1042004c021004a406602c21100c0e88024000c4481e9402074402507400c071300c901c500a110400344031600a00526020380c0702c0c072003112402d0940381010042e00c0490240c0d0014040c054615102c030300600c20324144050b4442c1d00001c121113040991100e10545503c0e50750180010300340e41c2c0c90324002414150544201c40d00803580c40000300c036541e0344441c0207466002c18070b8100c40d01800c0c10102c102d01d5100b03000303540382c1c1103034400c0c841d20b02032661780d03850001c0c10441c2a090700300541c040002e003c80c40b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 146298021 1250 146296771 146296807
    0x7030e0c0f011e081905070915090906060210060602030c0a0204020f2209050a0209060306010e01030b10091a191b080d1e141609030b04122d0503060105 67
    0x7143d0b031102811070500700201c140c03456500c2c2e02441740d607281078104100c0645c03080c4843c0469462809003141084002404c43d030390340d0302c0d0700103000c05410400002045039000503218000400c0030700400c80b5030b41701e4404903100c0c829006600425442504014050b14042c0d004080d00c541c245251440c0c101d07000301c8655500c2101006c448480000d14003040400501d0044990042d038001c0c0451414076188009140c03808090b2440741001684540c01a0036400ba03444842c420200400c0e400d4101020840149402c1c9a030040b05151084601e40150701440003080c0e4090340460020208a02c00354a4116560440c110030300300142000c040c0341d004200782c04018102c0b250b111801089200d0031141e80c855a030036000e0301e03010301890400b068001c0040581031507042011000003640700b9040700f0040301c01d81c4090300080c102040c00814402000010003900185910540307582000e0707076081d00400239400c821418076044941c2c03116030252076481400207540c459014140541010400000480314030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 146299271 1250 146298021 146298077
    0xe030f10090201110d0507030806210f0712150e070b04030c050f010e240d1107110d08030703050c0408031210090e030415031103130b07030e0c0f01 65
    0x207945900ca0070655a01c9400e0005030305400005011640080c00018518811040090200726140c0302003100c60340c0d281d0500503050907182840303188807422405151241d201c010080c03640d215a210020b20940c03c003642148240c2c00002c0d10001c440054003807805482c2001c505400c6029030714010071682031000246c40a14042d00120404170700b07007030a0000300500121018144261601625a5035603030041040c2440c400341c21980d0700c02c1c0007204141c0d4601945810000c0c2e41e0515050b0041ca2a60b000505040c9001e500c24101c0355200300c043c840024252a4003070000402000050034103401b0350011034100c0242018240703800c0d40c41075020b0440e0002648150700b6030501c0203008600b140702c00c000b8003600f03940d031040190160342d8455a070780740300300c2c42903c0d041015207801c1c42006000c0d0f070204d40514014861582e5901c0e1900640415071104007045900e8032410f404981e129219109030300c040c4030010024040088000304020244c090a05070604210384241603241050150a03a21100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 146300521 1250 146299271 146299303
    0x5091003140d020d0e130905190b0f070309080318070509041a060402090604060e18041202010c02030a08062101150501081302010903080d06080304030b0405061f060e030f 75
    0x106030400b00007400d04203041d2148040111200800d8200e03681d20502c6c0340300b6041c184000591342060f1511600340340700c00c020180300c600048c2c4400140035807191940c0c814603020650040903901c214054046035059180580100014000121250055203641c0941d00c0c1036000c03180a141e8138000a030031840101c40071a040d2240c224102c0400745118680740e0000d100300c40542c24070158001003241e0780242c1c8160410854000d0701281c0b075464810391003034110620b809540b0344e8602418420200c00c1d0103421840150300c0c180c41849130910200503580d806500c0d9442031710903102e10b410044802c521640d54026500840664040d00000344221a1764184e81c0204100c06450480050407a2000a00c0c840c10443c00d40d058070010b0380d200218030152a8031940e500d03155451203242400030031083d00841c03003622002402200740103d03003555600c03c0c0d01c100212070080e0707101d00c0071641680304148a20386403001540107016060007070310100c2141c500641154aa1526070031054642410103140010b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 146301771 1250 146300521 146300533
    0x30e0604080f1b2a0a03170d060801152301050f0f090904051b030613031110020721031b0f02010e03030a05070e01080106050a0305070504030503180a05040b0603010509100314 77
    0x184079810407203000d44011226a0561403039607c80e96180200c00e00b001e40f03c0b44000070229000f104540c07050700a0142c030380003000030f070620007441c0ca01a11213001d010001c00c0c40da00500b840e14075003112201c9220042e507d25041601c0460617001d15000070440f40c0c1500d00501c070024941e15250b400611450040f0000d04840d0303100508020310701e690461980c02a0084820040001108440e0b1000150b01d842c1c404142149130150b9418100c0704e10b2031101c210700004043c020b00003040c01d400d00541c2c0000c100704081d841240141c0444a0b4003045107200c0d0b500102e80b030510707170084a0124082220f4000454100c1c0c0011107642141d0080b1071800d4407940c3d400912002d40d40c4003054008008080c28440659414004d01034000e0040c143d241003015224800207225900c40c409540c0207640c0901203e4445c003142c150341c42d80081c0341c0200c500601c0d0408001441d41307400d00900c5071511002d000306185900704000e101ca100b00042540743c00149034103001000891417400ca0504940388405400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 146303021 1250 146301771 146301823
    0xf0403060f0504150612141f0603150207021c05030904020c030301090b0103020c031b0a08030705030f07140d0504020d0b0f010e060405011401080402010314010b0a030e0604080f1b 79
    0x6820640410461000c604d810821b0000c203151680c0710320025046800841c80c00d203685422460b02039080c0c4160980320380b4107090b87c07420000303812400540b131017000341d402106a00311298040740a1410041c2d40310b07000200d054180068048101d44c10350180c401d80b0329040d113020200d0103030b034400300115500707910001c0100104910f601c0b4454001c0000d00e001c0d4540800015515034a01aa840c2414520040340da0071131500301c03c12130a5041d5500c030011980b01c3c5071000b0081c000da04201d43c0f6440078101391001460040c4162454450b0229500c100703800c11051f05007490082c80020701c00c0f0b800c0320408846034040790300005070324402d112443d9141d0301c6605040000e4421701010388443d0080781044010700c4401c02c503204a00900c1030038a004d030f5a903034071400100d002d0940360381c1d0600100e841100204004031004000c00c1e00030b4080d1014490030310454000c0341d450b68120b85c05803c810701403100506681c01280289629002c00501c2c001c0d20316001c140d281801e130764280c111003a00f042a603900d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 146304271 1250 146303021 146303033
    0x1a1005090604050f010e070504050306130201030b0a050a06051e1b0d03021201030201050d02160c0503070b040305120a1106100306180c090c180e1008061306020f0403060f0504 77
    0x181e440790040c1e905110318202400e402446000c18007480401500c4803000840291280003550001c0000408980ca2403c0540c4851040458508160300180c2401303414a100d06100c280b42e000c444010300380282191400d0f00403150340c0c1001500e071110020490076180186440c0016111198503803114102140406510a20f801c1c804550f000070b060041c05000c0d03402092801480c1100e80a00b4010355421203a403482000707114038144d07044000008150481405605410001690303015800c983d81242c40700391045050040d480000d10980c000325031920580460000380c22720b0203190a16031140c01004d80b959080c03038811180c0f5035000300c1c480810001e1180900464a000d079520800104089050312110a00080d6004508140e07489000f0b4030561403107482c5a40700c1d4200d200000e200700f600c0c0c40c0c0300301250380180c80031104501441000300d42000040f48007030156101c000d1808d68010746a40c1e103c080c0d0001c40c1800b1000f48140400008a4414041c3c04101d8840550010b01840c19241c80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 146305521 1250 146304271 146304289
    0xb0a0c0305180c0105031e04060e01050c07021315050a1e2309100b1201090c0306080a030c05030f0f0d0c03020901140c010b061207080a271a1005 64
    0x440303007400c03045008140b4100420079031683c06083ca00143d90317513140740d10105a917110380c1d41c4c4124001c00b0000c010600445034050207c44510400a20403920f602d00e20322207074003442c040a580a401d800003543c5d000c520360320034100f8001e1030320700800c119611030000700c070b40f0540d038007003080d0031850a074020740b2220180084020b400c600d0424142100030300c070882e460b02c02c4804800c2c040c041040125429580010700100100381c1e20000f1951100e1609034106034120a00c03820f00d020f810945035804440c0640644015603400b4001010f8207011918200c410164840c025079080c0800c021003030301d5240010081003c64091a916581e40040c269000101c40d070741a00729080620512401c107590380e11906d10310340803209480c0e454844018070b5071240100804a18268810760010340010000312503909244181d0f0b00340ca803041247d44841710380060f10390300341000c80c00c0610180303280300000c0d40e0b0700d80c426814024111000004041e2880404c0900c0984409e0200304c00400208014546030b021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 146306771 1250 146305521 146305531
    0x30c04022106030a0309060e0120160905092d0a0f0201110f030301060e0301060b0406020c091506070b070302070b04051608070e0103020d020127031101030507020a020f0a030b0a0c0305 81
    0xc0503004c21039103004158400c0d50290800300984803400752016846104d407264aa481e8003440c001c03486040d030040f41d5a104038081041c0310100c6001c00100700065100303040c03013801008050300b030302d03000d49102c03c0f480c3e0054041d62440f6000500f400500c001d041013002400c611440c210102803489000150203050a50f070307864601e500c00c44640140d940b020040e81e044a1440c00e0240545801a0019000d807007a40c000c146d4502000c80c0c0000c80b1a030001d540300c080e410a403050781c60b40d00c030490003601c0548012109074100f00c6c204141800203400f61803103603100166103801400d100e4103640e286040c40041d02c069a0642c484241c1403002d070000307000f00d001407504000a00c0460720f8040300741c800300c4052201038450510a11502d0540e4000c031603009803510902020a9020409140702c4401c101a010554081d0200030182d802035010384640e60140030142c008054445295007080741c90710502e083c1c5a0002c2c5001c01c004001100d0182c0d207030290240707000226a51074000e10040446400402e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 146308021 1250 146306771 146306773
    0x20301090221070c060e0c060f0415110c100509120109170a0804110103020f13140f011b020303130902030901050f04080708031b070303020901020706080123030c0402210603 76
    0x30f124900303410804d5001e803180d00c101c012401c00380c01e4030184e041081c00c0d418650480400902000183ea48070020000e8910380d50020a500c080904211550403920491949075400f422012200d0702d00624440114035203807908502d045614000309a0980903040c6030300007603440f4443c042c01c0091010300701c80c01c525072044070740c141f1120020007030940b08060409004084c16002c88030080e4441d8044802c80074101c4901503613071a0f0b070300790b0701042c1c0c0007072150141107018141d500c0c000c0d00e8616054040c1100507500c04205c03003100c0c0c075460380c0d04048501c1260305200800034002c012a01d0740040d40281071054005813280740144c06682902c0004142c0c03c0091101d030700304400115040700351664a80c00079451505c07a130710300d0b140d108040128a44810040350203e0034008242d80b6400910200100380d0075608201e603204010386400f8401c2c0581840100a0302c00c5411b080340e40c2540001e2050010207c0e800c181c80030012600b00ea1201000c0e0041c03000c3e88004c0001c0f026030a894a0708048154 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 146309271 1250 146308021 146308087
    0x9060708060f010302070f0f050d0f0201050c090909100c0c020415030503040308070c091503060c020f030306040207050c0d08130b0901020c060304050c180a1503080f070804090203010902 82
    0x7800181d000c08412084505056000c19910180814000d50100e110b41c8020307884140358050030490354400c48216650001019090360020091060240d01c1c0241c0100203c6420160354108004a03a000204410001c4c40b62401144c0c484405000d400b5010000343c0781d000240d40603005010559480c4080d6800d960304003801040060300020854084a0304001255242c01e068503007450400820b5000003c42410040d0b00600054407020310700481c2d1160304200464200150103076243c11a8038031005a0f0b400610002c0c0ca02d091980042503101e10500964181e0001030000610a40d03194105903a00b0740081400b401d0010703000e00301c0000e002ca40798924200201c45000039a01c040461049010741400b02c003007010024204440d202c60036000345800f8034485502c0045180d4401280d0020519060010450503032a00140034016240c1010b810f07807418940f000080c41c2d80d0b00204080300d1101c82000009003131585031000d140a080b440304c016075104c0c41c1d01c0b9411080a5030610390340c0c08840c14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 146310521 1250 146309271 146309281
    0x22050f010c110d081308030d050618010501080a060306020c030a020c010903173004110109080303040803090c0907090801110a210204090207030206091603020303070b060409120809060708 82
    0x402c08000c040c0700031581100c40f81c100d40b030425824011400003c0d031811065002003241c0b10044058068a04079007030400c000d0341e400702080000060b9650152032040c480005011702e502c07d5400540c02000c100c000b007000740c1d4030ba03035903402ca0703109080784041074101060401c0c0e4a0390600415910003001d03e002c030562401c64440080241614a5032076060b100002c81c14181c4007511600b9400c0802c3c3c4d5501082404105482c041c1d86408075001c40d00700c01d064550802313a40c080c2c0480c8090703d94807401107003550788036070359084940c0c000f404858103807250104401e003076a60295143e204042e0b90780d8200d5924a03105160b4203480c02e080c1030840c4087d0500c01c20103071076440b1400c18239035542d00c02d00c0a5250040c072030b24030080c0b103281c014440d00c9000141075818140c0000c1c9150040c0240011a007118060305880f20400215000003503054000300034000101d6014603000f500850001d100180c45007180e0340311411841d107028443c0c0480c0d0328000f0404451010300c00c0941c040b0352405d00884d42d10f00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 146311771 1250 146310521 146310533
    0xf09020a05030a0b0a09020412061409070302010e24070314041809030e03011802090a050c0a0f0207080d03060e0703050601020718020706090609140a02060a0c030522050f010c 77
    0x249116007556544004c0706282e41c400500900511007600115600c1c0d0725084d400949819108054480c0780c241401200d947d100120348a100341c0140700a401f0250543e80115800016801038541c00007001d45400c8440703a480500c0307800c01500355a490b03902c200902d000341013403000c9807400d481e00724180800c010407800843c207100514030035080021003a10528040d100e660910406036019841c0c0b401c0500815040240c402c032960080340c10700392955411481100743d605c1150400b40c000d101340008082035024541d0144140302a0040c0c0d0241038847c100315251607544001400021780311a0108101e005043e01903400000c2458107104628041c80040d42d501c48611501c00645684148209200c5140d410f40e00019400b03a424022110320b4180314014100c07030102a10704075188140c409030b9020014400305820382c0036180d203040a4a41c807050303a450f0308408040e02804010003541e400d0702000c4442c0b000603681d884014903514203040a20a142c000011080d043c4a080c540d40d03008106 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 146313021 1250 146311771 146311777
    0x30218090a080307210b040b060304081e040e0712051f0323120c0606030303010e01091d010518070506340203120301060201050c030f0a0b01270f09020a05 68
    0x18110011590720f0700c2d40c1c24101c170444600711002010f00050110100d030071625070419824600115400d1000c0c01031801000700d584402c0d40c00411810040164101c440c003070074181040000130748941418990b444070002c030b14820450b1500d00044225458550070000c0d40f0485811643c0e0b00e118000c41708140042d0b8151514600003c1c0050300b400c202c003040c0d0701a0010300d1600750200420317955621405e40c0a00015000700340d02200901400000950310300b0b00106990480d2000301e1424542d03444d280c2a41c000303010400c9088803008180108150003182409074500074580b600d00d0740d880520041e071031420480d268128501c50601004007a903001c2409440c00c0889841c040403a42280401d10080b80c024003c0305d000750140291001041c03e00080d034051412284150001d110a03074401030340c2e40381444100c1d2091041140c4001150916080b84d01004040303106052801c0340b40303407114150884050044100f044c40c916080d0902443d0317030303110b48a001403d00000560800141e10f40113032480c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 146314271 1250 146313021 146313023
    0x909051009020a150507060e0f100b0d020a171516050306032104030b010909030f0323090109110f01350f150d0302030d020f0705010f020301030218090a 67
    0x203441d80c0c0e4150541d070342c041a0100518020700d005544400b1040701070a2a08680340a860315894003884001e060000700d04090302000301805883c00a04440f601001490305d015101e8001002005040058031105c203200003070240980000403400288041d1850403a4110032003111400e0b10007840045852180590001030150174000d40320fa40e80e4010900d05910000c0e000320074140482c0780645181e50800500a0364002c0c4030506040e0f882e01020000d45041c0440180040c151014442d038151080e0700000310b02d001031544d40031444060015026050b0142c0707810070241d545884403810410030f07035491034030a1419500c8040e20500e41c80040d02e16400081100340c007515100800c9500320050b105101000c0e414211245c003801c01c4007407802502c0040341ca0340660301740c000c0c801510745400440d0520b81c56055004524011082e211030740a50040340600d503d00d0b40c1402000e0010b9401e001d840365001d140b2100503141d624500402803069445c0c004103030b031001410705110700d186002c20208a82 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 146315521 1250 146314271 146314303
    0xc0b0601030b030f0604060c08090a031e030f0e100f0510050d032006151207062f010f0b0a0b0313020d05030a090e0610050301090504110a12060501090905 68
    0x1c51400b03c0d0901900400d10346903401140c0400040040c103a00c410140c04451b540c03003181d90390b1001465a81e00b000c0700080c000c20212070400d9084150011001d070705280a145c08030b484022054210280c9080d40e114206581112503150b07070180c12441180661850342006102604000da2520401b24050080d140075104a6400c1014140940c2c0e20701d5980f0b01c102001e1016502d1415481d072160000c3c0c0b91a40c0c05459180d1900152030004030b40c000070030b2201c010300f034002c0c90483d06484107800c128500742c03c2d104401000000450751079154201042c1d00740003040148091642604490081a080c2e2050300050800e1000c5464001902d520481040070039956811500002c0e4070080001401840b500c00010000151540134120030112060345000740c0c0360b41c440c8003c00c400c800380024840f0004200b030004001162094024130b4000d0701070481c10417403070290408190100c4a40d000101050007044618040010070721805006001c629000c1007140000d5a80d181c0312000d941650b029 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 146316771 1250 146315521 146315531
    0x1b050411040b04091104080303040b011401030b06090d0606080703051506100c0609260c0106090c0c0b10030501050c0c06100506070822090609140601020619230103050d0c0b060103 79
    0x20181c400201c8007e885084d0859442e45020f02e48241400824050715001c0926030a0803600c0c0d50181c011000f40060081c0b00d241800b90710000d01040107400b107020360ba00e903243c4a000559400034040b40d809540640007030300070b01d49440204680014085e01c418090307001d001407526016800f100040f40180d0010010840c21058144034074a80081210040d401d003194030a9524500c130300b002003d900f1071040091125aa6800310041201d54507070b080c0010800d03d16500000a04000e0b516a00952405219012540306c3e00c0303403402c54408468040c030310440014030440100040148990000b040c0310441310341400e00c4045440b0f4010381400034450403000c07800000f11207400800b103580101e408198a4950382e14040000541010710400011500c4c20603003402c04541c1c04210780c82201c06030004d0015803111f400b40d50422100e10048046541e0341d074403070303015100c4203007464044c1ca42c50a4261040c0d411814410300380150708000b003003800b440908802c00034840350a0701d42e0001007401e00280d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 146318021 1250 146316771 146316791
    0xc0201081005040203070e0405070216050607020418050303061203030610030b040b040f050106031505060906030603120c0703030801080a031205060316150314010e0109020d091b050411040b0409 85
    0x2000030350725002250b02500110800501c030b0b521480780241054111414800fa40358500240d8842400b80071300708089541c11024062030524400400349548041c0000604004900c4c039003044c004444d03011107041d080002032182c00c0c90a0b060381c941c00218a0040d61540c1015000900d00e400100583d00605031180c1408025542c2c80d4441d45100c1e00103003051100c0d084a5a50070300825003405880b0100307160012a80c11030000110000550b103014203000e02e041e5034141081210303040100700381d50500c102c400c60a000c100d10f10140c00d503940004002d2055500310700e405040400305801c40201d5502040d69507001c41da2040030440420941c4400140e9900c40f000801d041407802d200d68858034941103400601500700c029440c8624030b1070355041144000300092400c18070428843c907a0714001e600c006211035403e660041c0301118440000143ca11016500e1061840c180c5c41000c00c6442c041c2d0003084541030070b0064420701500314068914043c1001c00165060081e03014100c4420f5540c9420b0f1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 146319271 1250 146318021 146318041
    0x2030a0810030b0721020a140903010617070302011403040818061909140f130f020d050702100c02030306030a0305071412220e010e041b1205060609070c020108 70
    0x1c061600590303942018a01351402170808112140c0d900c406903a6007031198103000c400d1003500c01412103991070001c841e404010814003900304200c0e00d80e0555a800780091000ca0000c1030b00140500c5038044d10724645507000241035011080c101c4a2044010400c010001c0c0009003101c0305c20902106661802601c50042016030051a102046004054000004c8150480308a008071081e800403a50500800c07010b0040700600e2800305a000b100c528214044814030740c1181e03401840c40c0c0c0e40182004090340b000c5040d10030a03241d11300903804c000c04607000590380340102101d40909000075840c42c280074000c00d03680c5403c90805004c20001145580400403000608007804026000b15510524a0300e0100d402c0d03031000080e007061742c01210302c28028500c0e00b001d0100311040361304005075030717884e00c07100e881b1441006000700d54020310505040050807680c2008070280801c0104594003a016290451800d20040d01442c030560808081200c880ea101402640080d82840d00454685890440e2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 146320521 1250 146319271 146319301
    0x3040807150c0306081608060115050f040e0603060a3c060305161a09010c02040f050a020d1406030c01050702010903050607020c13150b0906040803031f060f02030a08 73
    0x1c0c030010307400c00c0010120154035030000016590310700c00344d90442c40030128104254045c0d204545103500403200420040d001c42c01900c0e0400300324108940b0f401c100c4a880001c0e58400d80084603503100f00e50074850766080410005611820382d0800b002a51000074084d070307059410034103000c02a14130385c030724031189540b4946c000494084072105100c52a2a4a0216111145d010034010b400e24a01070005040000d07035074880038516030030130702840c2411070001119219400070f0180c5e000b40e00c4140b10307215001c0920401d44500c000c0b000c010f84924244006005492410110b0020481040188901980c004c1006001c0c0745003401c1955680360b551006980c8501c86900103003044c00341c20f08000e030094001c00c02160003032044952480e1000c0c01c2e8020001c803141e081c8502d5203100c01400c180813036403e00c0024000008010b18190034140e840d200301d443d50340211840036605c10780d0940b0710042d651700d1030f510001c0d000604040f0203d0000d4200259030f4040d041d0881c0800c00608042411070b86200301e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 146321771 1250 146320521 146320553
    0x90109030b0f0105030c0306040c0303030c05070b16020c030a15020d0b090109061a0a0807110f030a02030d140105010f0c1509081815090603090709050117190803040807 74
    0x5880618128101c40c00c03002e07092150034000d00989000071070a290201d400c5214603480300c1e2900c09113081d51012001029a01d6941060080c20401e202c04107404d9880310748161405c400c100030358280b00350001d0404140046d400d01a903c50210300c5e002443c0180701f51500c994046006031110001580040603040e05046141c20034081d500105440fa86c40d003024041c0c03010140c00041da1001610140154030a0709801d07400510060301050a071441904d107080d69a4030401150580030f4403050050469001e12200000761b0710000c2d146031b0b203012a0007031107000080111114503640c034100010301500c141c550968100408000c0700e00400c4069600060800703159001001101d4081c076101d84160300070032255005464a4a00030030f43c0c5840074000c3c40044540700000d0420b504441408a0f44d0405017403e4200e018008001c682c10139203100b00c5008103100300c50341701d4200f55041200d0800d00b03c40940c0045600200c1c0200108041c5422a600a50b1101c4038540d520b00b5801d140301c02c8209060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 146323021 1250 146321771 146321783
    0x2090604080313050109140d0f080309070509010e0f130602070c0b0a0e0307030507090e0a050d02060f0c0903060601110102091809011d0a020108060a0b0301060c0c151409010903 78
    0x250100380c0e060004040c0111000d00303580081d02c962a100191200041441000e9003503205419481a606040c0142d0382340328418603414158000e5a40c540115400450342812071380c4c00b00c0010405031034100c00311f03801008003c2900b0030508020744070f0100e500700103042000c0856440d42000c10000141c0c11a104d1580051504400380e4550507106625400300900d200011101103100700345140c003052110880e0307805170080003a149000d04240150480382404007441c010030034964040760041c032202c0c1c043c2c015903000e002c00707203000c0552880603013010703110011a4030140005200354034000f508941000c804d00300082c3d000c10408050f07019102d000700e5290090714003000310150010600300d10780110620300003403002d6503c0e88001d41c6080d1400030b020f8a1076000d85450000355010300ba8030740c0c0101000d0808a501c0751982c0d1403034800c0e8000c2c0c0c00280082d03030300c05c8600180007040030400e000c6c2550100c401030405041000600b4004000742001803c5800691415544e0161038414000c0d82d00c44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 146324271 1250 146323021 146323027
    0xc0c01060603020307080c09030a030806130216020415060804081e0a030c09090e03030114040605030d110d1412070e040e010b031b0105040b0304031b051b01080c0708030a020906 78
    0x5400034040d400070f44601020070602008901e000c074084058032008d101c081c0050030b01c0b58954508a500c3d1001800040d0420f2401000c3c2020941c2400180900035148110500c8015240306100071544010309901d00303403d60000500541c1c0e8415519074001e5040a44140c031003c0000c0818a102c400c2e640d6440382d070b5400036151207a03a4041d0070806a00e44103031070780c068281c0ea0348100420754074003800c4403107a03030010001404203c0086400f0040340c580600001080c0e512040800d24002c04c2c090000d001c111f008182c0c140c0c0c0c4100b0065024a0029458008032600642610665600482440921800700b000005145600c1803101d914410740040050001e10011030400b4020320035260400e00900401344805609507030070800504044042c0e4a0341c2c501850454220702980005d00100d00304401c0003082c0c003034102090174003a4103d0150300501650300300c001d00303203c906141340c0049060050031000c000b400f28244065407102c1d50052001c80d0342e81d481c060794000a00c5a5a1001d44c418404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 146325521 1250 146324271 146324279
    0x807030b191a18010b04090906060302060304030903210503040b092506030e0d050a050706140c04081b220e03070b090609010209130c0e180907120c030b0c0c0106 71
    0x22503040c19028a0030390f2025004030388110100a005000d0107112510b56080000301f09190256102d400524001d5900040e40ea4131703640018015401614254001370040380d003482444085560500d022004242450543d01d0044024005000c02000580f418036100e000494801082c0308000d40a550340341010b00141c1d680c0c08070b160b000003034000c0c80c000034500501d80c556503000103043d5480c1f4840b0380b40c060400c074030000115007e5106c405c085070580c2d10303100143c02008403000c401d070241a4590405031105d061090321403a1075580211a0440c2e03461407815a03082d04d8881e82002100c0581c80161046900d0b20500d40260501c0c980c90800d03484006503110602c0608802c69010351134090175100d09031500782000f401e0b4001e29103003075441b40301c0b440e1548030004294040c0e4038022050130510761146403d4006035203041200c0f501e9a0117040f4004100c1c001205004440243c0440c010614802150362a22501040c4600006148841082c089548a03010030142c83c03059030800c1c000e1180c5034079 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 146326771 1250 146325521 146325551
    0xa050d020c0603010e1302010513090615020303070906030f061d060306250f140c0114100e0c0708040512010f1d2505190503060a05010807030b19 64
    0x1045014200500a681406480d868a281224100c40440f10140d581d5100d40c245241c40c8406020202d040c4241041040c1c5072134072680c80d40008007100300d00001c0341c616240c0303201c00380311151000c030046400400800017019080302a5400f6901e003481c0004035403a00c1118080106200d411492020150702000855251009442031040109078140c80c07450302c178080700608ea44c07401d964500500c1030306065188aa0f21607000394003030500310720b00f04d00e00018201c0b00c104c4584c03001c03070100096515480c40307030301d15108142d5040c1c00c8401c100d80e491000d4606020080b410b0b0001d0b0554060620010b1201c05012075030f07003502c000d01001031040588102e00d10300b2034000c04103050408455410008100418181c0082902c00c2079900b4014041d8219150210000031840d140c40701e590001601020805d0340300c0604020360058000030702c188903802d260415241800060040200314101001400090b001103900802c41e940907181400546484844000955580c441a01054330b48042e250a8440c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 146328021 1250 146326771 146326783
    0x7120e0c1203090a090504051902010909060b0a0201050f0c070f1b0b07170703120506010c05060907080f0106030305121905040f060b01031b0c02010513060221040608070e040e0a05 79
    0x14204c54080080b0303940c0010109a801c2110301074159000302040a18408151250420f0f40e0301c140761061a41d0349076101070701160800e07000320602c40c00200f2080509902481950303000f10308112881c0f01490140700d41e034103e1051000013000403040071019010460850300203a600c5031502c6031485a03603202c0c0710000660700112015201140382e8103604810000f90f100300d8440d1501552400580c00c41c4640d004041c1c00050020742c1001452039450340401c00c14082c0d14081d201c803001400d4410300c4c0c11021464002040c40032082a4907240d01000001c1c0c100088420181c0c80305e40c800001c0d0384908040c05130510031140762401c5800c0c8001c0000b081100c02540f0502c4d403151030100400394410b00118101c615040c01c150418400c050510703007103800b40b01d074035154501c149010362601e402944120800e0819620500140c2c2c0050590aa00041440c980d000d80c10815915070500d0320b420001041280050074031000d0100754000c901860b05d83d0340007255190301e064210b41c20395031300c5d240041d030b035407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 146329271 1250 146328021 146328037
    0x60204080d180f050306010308030603031c020a02010606110601060c2a0f060c0b0109020915070b09070b0c100b040b0d0c0e071701030b0903070b0f070207090507120e0c1203 76
    0x40c14003440031401003001a6201c3c00e583e400380081440b40c2c00d5503030b160b41d19400038042c581d151209000001e00b5000c42032403a407001c0c049210143c0c641e28800300290940d036054200c442844007560b640b100b003000001e00356044828a1601c07000e9034034203040c00341c03422801d85000c43e000701d640407052004945148482048840441c1c2106640c3e40d2840110381c446800103000744000c15590040002404a8000d030002c91802040e401070007048404101e801c0e4401c0708201c8040144e20100420100b06008000050511501c034a02e0500503140042d22050000e20400c400ca82e10f460300c030348903141da0b07210b07098044001e800040d020425050246900c400c07442040641201e01000900b69445208407060003110170700c07510070342d0b425641d80c8204003900a08060b51440180084d00200365503a541e40d01598001c14116064106058001d040100301d4011100550801e414424095480090741080d09408000040c0020f060b0101904000e00c07411800e03030003541421a481c2032400031009281c0c40e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 146330521 1250 146329271 146329307
    0xb0103030e130e06240303040e1803030108060a180822060f050d0203040602130e010e2410090302121518030a0539010b03060f060d060204080d 63
    0xb9140c400056001e48030f102100c105280c000c000880e4000300b5104507841d0b0004d5402c1d490042c0e103083e1005c01e103581c0050b846501c04d0b42042091240c2c1020300101c02c058440207502942c603540c10001101d0b514040034001c006501e54070720400700d01c440082e5050403426800403040d640d5400c0080c0f4044050308003034903c18942d010440c000b40d81801030400b00e00040b195161941480d0075105508002d4100520030341d809a002c0089800e807185c411401805840b08040305800c55040c0341d1aa000458001d10340080481151001c07c5050b084001880c8455400c8614100e031518012040300d4060060380020f4001c003d00e52803010814000c0348070041241c1d00c80c0c101e1015074440841070204400d00d40c41e41c070a07030010828500c900b031003400101811480c5828214000300c455000c031501c454034a91a58160520400040d6034035000e025840f03418000700d00514803030414218103100290081c1c2020300c00d014261400040041d69015140100042410b40b050a0400c7c040505070341e0842410780f0407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 146331771 1250 146330521 146330539
    0xc180306040c0b0a03020904020406170702150402061b0a0606080115050604090b0d200f0105070c14010210050f0105120a120813060507020c15041805130b0103030e 72
    0x142000242144501e8110032022038861400345480020350008841c0c1c420150200000020303038695000030301c024601940c49000e2031800388040131480e0405400942190082110642c0001500c4900c94000790126030300c1d9038403120034003500c448240d00c515840303071b501070040751134244100365110303008444020f0000c1c0000c0a8095000c001c008050088c2907100000740700620148150768400031400401805510081c40c591702d030020342e86060500d4011500c00c0e510750280306c2c00c0c000d0007207442d10001c0c200f0600b000865556009103c0c0103001d010b00c20450320502e895285e2003086260105c0003440010845070a010300001c2d0310f02401d00405004c0e08010103501205413000510380e098680100c1b80344c18000b40315108448440002e446003000341910710451010842622600d402011141c009190301e640c40c500303204203021054402c40d01c42030180302c2048030f0062181c8051181c40c1000700000c4a5550b200b81900854403443c024181c4c1c1c01441c008002c05800c0788040f10018400c441c40c1c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 146333021 1250 146331771 146331817
    0x90302191404020a050313050c030307060203070e0901050d0f0501110708091005030f04060509070f0611010b1c0201050d02070506190f02030115050a0207090c0203070606080601060e22050c 83
    0xb0592150070301070b50001e901000000c0301c141070509803000803440340c1c05070703194800d001c400240741d42c00c0540150b4045900105110840c1d41005002075a24000d8030342d00055850a00011100391001c9005004003440c541e40d80c0c10001c080d031000d120001c0307c0c051540c8801076814207080c00e8014110483c001c0f401000810821405030f030a403803041c40075001d01030750f0380c0d43d9603512009004090300d520030074400c401e004140485c40325610009030955541d8540c10040a031012401e64542c0c4110500409042c50100007030304901045000e0340b50282407181e035902481c0c0820000303224054018000b030286400f407141441c2c02d507400e4012418407007001d22620320f0382d07807081d004c9100030300c160502c20b40c118851820315401580500b00d54a00340c0141e03529250740303035884400d0701c240301024001038000290040410106206000150914500411301b5604101c0c002d070a8070243c8070240c1c41002c0c0324403004040d00c020b01c0b0603848902241002e00a42c00e11740820703038450701310012200d6080d019480c205 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 146334271 1250 146333021 146333029
    0x140403080d060803131805101701110307030b180601053103140607090b0301030f03122406020111090105031023090a02120a020d0605090115200a11010903021914 71
    0x1500414230382c05104042454440b14000c01c0840100281d12552145441c020074821301c0041c52151075151804101c1c602040100250220013206148401c07074250b09101546e603001c001d40f00309401410740304801151032601d410042000840f1500c1d071001502c00801000310016500e842d440e904000c0f226144c540d00780540d9414518003800341d13a00030500040001c911a079004900a50203801c1000e01c1526150042c0180c0380d224011500f00d1000c402d0024840a040c074019004280520003042041e1b901c501280151003000c0717119040040c080081454107440030031002c01400841402c045030a0000c0414810001e600b40d054490204200002c01645440c001c0b00c41d01d014801c0c1e544001ea0743c0d0028100250440500c84001c542d544501044a031120344800d4060001171455050070b800082000700700074004aa11580300318a048101c100680020740601160b50154607032250401d013000485080c81941d002941c49255280e041c048225004010400c0d5245442e0f1062801c004030240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 146335521 1250 146334271 146334281
    0x703030206010f14060a0e091003170a080a15050307080610050402181e03010f02120c120c0c0102071e0302010e03090102070501080a0f02190906140403080d0608031318 74
    0xc04e00341c80741c0309a0710200e00e0320700d004000006d52410800b140c0d40740c017070108041c0d8008440e01041d04006c46414014403810072400c17004031420401980c074112480b10024243c0301d0107400252465164440c0e43c85400840100101134840038007160203480d42c9403081d969400f010303180c3c0c0400310603400703001c2010304003030003120000401c02500200844a81c1e00780401400360040040e40411891054011540c003030180741141d024007a27000d600c1741100032a00c8039149010303045c424000c0d004c100151603860622400340d48401d150210f1500d40b654010080c2c003911a00740c0c02001820101c0500c48400c1642120003210780c0242e008000c01100080615624825180c1242c007680c0312210811013513204044203903014840e01004600a0380c003510820903608052500e0040448400c00a08460740c030452020081210b42785c1700e0f0001504141502d55840b80740009010030000084081d504941a0014402800044112603440d48107407100c0322806101d02aa059121104a00203018040340c059 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 146336771 1250 146335521 146335529
    0x60603010e01261c020c2b06090501150e090615060c160f05090a0b0d060e1e0d091a040b1b070308070204290108150d050703030206010f 60
    0x18005aa42400314028040000310345681006400d0900015042c80900441c02004000c60711034242c0b03184d801000c1d042890180c090382c0140714800005144c0020a050600c00c10900c1d24034100c0d244003400c1103005400da052001d0095030800d059006a12940340e243d00844200802c1c40c090340d217030300782c03030300c0d21403200303507003069902c1b82e10b40251140345031540003403004400c0d290499200d89084006200031030f849502c00d807502070207880100702c00e0600d5042281e20903150f14081004480c070b640060020a0304520181c40d2503070380d4440c045041e03400c0002c2c182084080d8100714041d1604c81c41182d881c3e10041002c000103510780000aa0034a4a014109410b442001075a060908102c10905aa0032483c41c0741d6600c401003512418142c0c0038000100618021a26960381e8a0140140020b6403a4010881c286007100a9008035640c42c4404c3d003120308800b4a80030b40b00d6124070b05400d100640d42420540c0c42200b408e07404042001c0001e0103401c480c8030340c0030f45402c0da03030741c060100300c420207481 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 146338021 1250 146336771 146336789
    0x6010608070c0201080730060509060604030c03080a05040905181b0f13061d06030c01080c12191d010b030607022e0911131107060213050d050601030b06060301 70
    0x100300200d0090243c0c041205030b4005180084900c003404c00c807d05242d000c14040700341e131080103000c9400c0038401e413680400150307886440d1500d15070700c0d004540c2151001510810020420b1441644544111002010041340600c12402d1105032056442560f00721a54644903042009400c250482018090643c0c01480303619201070301800d00904224215014071608c0d5140800328030455400c440c10342c8410141026030403480d14409161500d900000310606202c01441084500c1100c0c0085484c0301d00308254070110b589a0403a003500803485201c0c400d00850a015202d2515240c148100e0340411000000703100103101c1034281500c9000594182005801800b203003000004903030300301400c500a900751000280c1e00501d51104881005070105d41600d18551607020f06d00d001c204141184103903041c10011103660f80c0d00b03080d280c46180e1b401407203590049035200f0901c10840141d030060001514488920ae81031410a8842c3c2003408200d4001142402107002824114140d078180ca80f400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 146339271 1250 146338021 146338037
    0xa0e060103150f1202031c270e01140f060307050703091e050603090313030807060c0f080105010c03120507030516020703080702010c060902152502030a0303050601020709060806010608070c0201 85
    0x3035207204400584d0082e038042c428070440b00340401149610302424002542c0e8a401d44012182c12903103040d46031040c40300d103511010140014055942032904591144d2035040001e000c000115941c2d110211515500203804020407030820b070050010001e0920170381e1641c401035100c10340c201800303016000b50840c0d0200880c09002e01d06140700110b40050421088038207242d0306204080b8800b205400440710306002040c18010403140f80541002401c0d01e042205010700810801020300310144103da04000000b020081414002d030507518000c05080010300942c0761800c170140103090181c900c4034450034a44d001c0c0310050301c080780041c1a264040c000610307043c860303001110401c120080c15594075688294010040c0d4540c2c07180030070b0602da40106900d80743c281c51030b80707581c5a0300b20b00040030166249006c0b005a40106024050540c1403c00150940301c581c0100c0c0390241e6034001200d081c5c50840046960000004e20604941d40380d238890307a266440d940100c0300f4501c4904000d002c25016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 146340521 1250 146339271 146339279
    0x5030c1c080a051b01061401020c0916090924060203030f04060b061b0f01050a11030115030608070308040f271a1801170309030a080a0306050a0e060103150f 69
    0x41d03001015036442070314200e4180603076000b0b00781d9003103414910720900c0e82d507546c1c080011803e6455034214090090003e442200244c10115448800040507079840e400581003441c0c000c0e0140489201522601c17008001048079285100d00a100c1400003002c031000c07001700092210700c00021030f80304070446403203a592525107039202c0340074012020000381c0c484400c1c0504514424a005c00808000f10080240103604480641c0c0b82156001741c40840c070706040074a0506900094400c680c1161040f002d041c0442110903c120002c003055006038445004a900000a01100380f02070000d0b604081444828595a144162405040495010401c40c0c050725120a0100943e0007101c64007903c01c800040028000700180c501c0103440001400c151020005112100c00403515007030485021700110b242600741c00010759108a0032900400c10000040d020301c00c90b1003508540d0003490060511940f098403442400307103036103045a0702c5001030700e024103400d804d0910030880c004540018000140341410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 146341771 1250 146340521 146340533
    0x50c0d050d05090303041208071a0603150c07020d0b2508060607020406030506010611070803071112010b03070b03040312050601050f09012604022806030903110708060105030c1c 78
    0x310b00702613240c0401e000009040c881e860101e0003803441040c940340e03140c000b80342480e80e5182d8141c010201b0302c2e0501c00c10809032000244054103044c520034040b03059841a1010790103200d80c0b94002c2d004501038181034200601c00480034000e2018840704000d01c20300360500c3e80c00c8103107450000c0001b07a8840c00b2484904100c0e00030a0a1400540040b5103142c4a440700c0c1c0c90610203030310500000301c0180120350094404d000c3c410260101001540c6441d00989400745010f20124066210300081041a0001d600940c070007040040d0140c1610350b25940c1c0c0d83e040c50320f074000303c801f50003042410312019008040340c800c151040300e05844ec3c6041c0b0b1540708000d803050308041e00003810f22881c5100324420b0448281960800000403600f06024a002d105012000d0148007406248082c4500b40244520710f0004078400d0350000c1c0340c001440210350804075490004280e2403282406a03040205020740f0125649060b150300b41c0442c2c40c40110322091003410044500408050300c1158800000518 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 146343021 1250 146341771 146341777
    0x7020d02012012041518090203180105010b1801170403030f0b04020c0a03030e0a0f0f03050f0d05090c0307120b060324040201022109091b0a0c050c0d050d05 69
    0x50015540c0d403451903403041d03074506010f10503007191010380070a00300900f01d14052928251601480d1406441c00403200d0130750058514003503881a290044005030030022100030860014480d01700900c05560348052903001030784082e03421074000c040e4100f07101c0c055000341328502200328803d00450503aa5181c8003180100040035080e0402919140c4100c0d039a6568005801c0391919900505094070480c40e014003151108140c9010703c0c2c1260740e10a0120b02901b00f01e5030340581146112456001910b0115175611802d0302d181040d16010a004c6024000d940c00700d441502c50344c049801c05000f0030205941c03040306200340c1014255041140000440c008007040e00100c01400320f515007481e01c8900c40000841032500f400c07000150302000155039042207882c2007441440158107841010b88603c00b000c0c490b00305c12a004020840c0415400c0c1074607440312082c090081c00441d11020038120041c11f00e11401030949451048004003a5207103007608038400307001d60000040030a10070280007591550 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 146344271 1250 146343021 146343047
    0x60519060806041d0a080d0c08090d030902010509040203011d010e010b07110f03030a120c030903090303081302060c010e01060902030919080904020d0c030c0f08070516120201091707020d0201 84
    0xc3c4034680a22090344c020021034881521500c103c948660107900000101c8008091580410040a040c000244c6010030740a007150440d25000c50480c28600050303170f50340301c1c10072216000b6100000000d0515000d0b88000c11160280c00d16400b03503640c40705420304100302809a030300f00b400100a036600242c0214000c4200c2d4a000d003618006140c0400083c1c2560420540c2c20085002e182c60564050854421100d845001e810108a07144213510020325154035804014144002e070f07004510214550000030700a42d40c000d040c01d0b69688000d19084c080c041e250100b980f0385d070030901c0107d003001840c001e030f03480340e02e20b00b008005402e44215100760b000f20005c0d0072346100204200644441e100c43c0010807240310154800304e00c502da00440207044407a0000381c02c0c01c01011040800159901020310703900200c4616003181c0b42c50540c0c0e40e00f2034014a02c0720050495880c03086003000a031701034102204d841d01030605886009015824004107210302c03507001358447c000c042000010340c000d2804250304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 146345521 1250 146344271 146344301
    0x10302010905190e01080f0d0309170d020c07300206070b22080304020a051c060528060e0c0c0604080318010c170108010e070b0904020f0403030306051906080604 71
    0x38558030500100d4044c400e0b000001aa040146c0c01d80b040d550810541c40200c04c0c0c0c0c64200401c0882d6140e00701515203002e506081c401c40040e08280c80400c1d9010780d076040080f2003e45c2c051a81c0d5000008950400c100e42131444100000d600341400c0c164000c40345035940141c0704a00e00000c2c1d5640500540004000821201252070f03080c640400c80c0307528401203446510b280c0d683c1c1c20f0500422902c0805984418442d19250741030300281c512500c5800e84c81c0f94081c10105a40c0c40750003800d504a441d0740703e1414000030381b2042d0100080c06030464001c41d101a0350b01c00850716602e201d0003991050020006a9500c4007002c17400041c0300074001d41d48020003403050081c1c00d44107440c4a080d504840580c07000102c0051700d200c40c2d0305900d0302c03250050050f03c000f00a106003944403917480d8001d52044618001c0003240024030358441c2d80465004149a80307c46039035070b0b201d20b400713070040070b903409418010881c0c2c0903800c070b03807a150546880c10b131005500c48050ba60380c2c05080101800a80f4140601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 146346771 1250 146345521 146345569
    0xa0e010212012c0403020d110f030d02040f060207050105040b0a03021b01090308010803090310091a010807080c030d05030f061906030915060e070c03170f060315010302010905 77
    0x48035411010140c00f8003548031080c002140c00030007080e502070b00b01500340106440c48040c00006a000034450307081d0725075070074011803005207114818184030948154101c98040000d582110504541c0180140c41c0035200c2031105c6a2100403c0f80d0741c00980c010203021070801c00c02440703031100c0300300900300c40c003124940546005100403c0c40003d441440c3c003413000c0e0791110030031420540c0216046000d4124040110f00b0120780d240041e999200480c1914415a40d5003031403002d100940050710300c090501081c0c602107594030b04556a5425603407082a030b540c040c280d400d418070b1a000c58040155a419036406d402d64440d03201d000f00140016126940c4440070000c22030320b82c0702c00d8a00800401860b200001c03649030b1400c0540b0046084200821f61615092041c4032010082012a4002c5607618006022407040e1505407880550305e0310000c21100603030304201c00c00e0843c182c0c86100b803070168156081d480d44a80b80003480182800020b01280740d5800c14440d9040c59900b40504561f000b00507d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 146348021 1250 146346771 146346787
    0x609010b070809060720240705031b03070203060f0403020a03050a050c1015060305010e0403030e0a06020310140303210901090611030a05250302071103160f06030b03060a0e0102 78
    0x1800e40c002c1404503005071b80030030390344400c010081181c2c16072141610560000b00c00c0c05400c0c2d0203121401f0302c0c1c40800b60045611028032900b0010b0b2a01c4150440c82c00105100120038256a07800040d000c0340f10b8425500092a02241484824000ea6068005002d0034045a405a600340c00450410041000074400743d8000714003048448440c4a050000291175500c2c8001711b0401c40c0560850020706050a0041142e1040f8039202d03a406901031800142032041e000b4000e0500805c100040c013524008014004410248c0000c0b00c210f5000078070609220301c041007419181c1c083c45d118441e58134800d441c017000d60f9288000b50341d480002d10000282ca101956a180c04813007140500703441d082004020429000a244156a00a0150008910000c420040083c0078141c0080c21400f019000300300c0404000b60308080c40300900c0010103540700e203400c50f030001240003840e01c2481901003a0640000d0024080d1103416040b000146c080c01031035440308100300142141850b0032029642c200000c1c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 146349271 1250 146348021 146348029
    0x313020d03030507030b12070b070f14061009140f07022a1306050904080703090e07020616110c0904080f0a11100203070e0f15041215050609010b070809 67
    0x10018802c0e14000341d1401c1070035000782181d0310800e203140a485403058a20100300001081d9040b61641100c19989031202d2500300b801170249170b0005c202d00000700311040c0c92207001c00c050380300e040c1d86800e484180daa10b692005c01d91384820100d204e00c848003c04282c540031a031900c00da02042600440c1d0b90f031030f80300301d412100020741501300381b8244a4440c0324030f4034035003464040c02e11150094203100341350508001031000e11016000030301005000a200c42054001c80100300104031031280d030b8031280b401040180d01c40208540e500410a223101d180303030000d030007140840c0d2281c108600409600404e207003441502c1c0c10142c0180c40e201d909201d0625151101c000601d549600c3d40d8a10803a81c1000c0d11b041c0c60502902d0340000e440d8014070070090915442420700742c80540c00c8820202d03039403800d00420099941c584410440260024010641c0842d40040b0100035204007001c003107000ba1031007074904075281540c4030381d4002101401045091010300190140b14007919072306280c030075820001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 146350521 1250 146349271 146349289
    0xb040501090b0a02070c082b21060801050601082412071203080f0108030d0203041b03030201020306010e18010b030c2101050a0918080f040306020403061a010c080708031302 76
    0x2c0d622040c4c00162280400007800c4180008250a00c01012420414141c04603950701d49002000da82c800c40000102e41e6220300d0aa4000100b1103029008159403140004080d00c40c0c0c1c000c401c0b26600b000003051031548034004075485041c041d00414048400c400c0300001c1c085191004035400701c501040320084500603c8040300070301c0c0d003030a1800b40c03001d03c0c0340140400300000e017400c0c20507900c40c0c0100304022010003183c500d0000c040005a480e5200d00c0c290b84101e00e103503058425090b00349404000c00d0340541c011750186000340c8030002d01104410800401c2c0941448540c004010ba00042000c040140043c42c0c001801001c0c150804100081c05034a4100034918415040c0c10000104245e00b802000503003d0410910180611440d44000d1000e007d00414001c0c8841c4000035150030b02d540c02d0042d00c000d1a4400c006640e200ea4a042560281a4200303203400a8035400c5203030f1615600458070803103180d80c08101c0e641810034580322005c1507000144420340e0030f50203050890040c0c6d900121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 146351771 1250 146350521 146350531
    0xa0e06130b160501140c030411060c0303040b010602010f1e18020d05071809120f0306080f03030402100215040f02030102040902160c050109080307020d0812070215060d0f0b040501090b 81
    0x882c55012190a1a90039921124040031014415200740402c1098003021a603201d508188200c049445c2040864154800c0300b120605a00010080c0001c0210b10040a412210594000d2003010a140703108000c5800e0002100c604020346291a01401c05c181c000141c0485070078180c100300d141c581c0110f51403200e0b041e4126819048202c0a00c480c0010301c2c400603500c0c0981d1000c0001941d03a9407002003a451103074001c002c0c00a100c0d00d2191103480703904040094000c400950340c9201541e4112940c03500150780883c03041040f00340b014541c51000401e5032401c1082012032901c1c0d1904d0700c41c60001c4a180a00341d030555001c00010807090314038001064010041490030800200b1810400300030041034115504200080c14100881d08000099035a940d404446044d01041240340024280c803c448080040075005010852441c2c2c010503010242c00e0b200e03a0860842d620700d8100441207283c5e41c0020300e16800d100d40e00000c1102030001035401440b45000182c28901c1d078403000300c40c08040741c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 146353021 1250 146351771 146351797
    0x20040305030304060606170601050319410714070b011d0604060602060a0b010c05010e030405030d0f080c090301180b010807060c02060d0b03071d0f0108030a0e06130b 73
    0xc2800204400c900c05c1e032000300b04900e40a03406a088460000e41d00b000034008a0404c0404400700d00441910082c140c403d03c42d20800300443e04c3c051440c04822038085100d90b800c1c04001108811080c807000050100c1a40040c0484890352102002c1d9426100d0f00380c0b81d03120450622004000a4140c14a1406049461042d0f00b101001168140400b50002c000b82c0c0554140001003045503000242c0523001070307440b40040b030a41c411400407111070048940c00b410070340c02c00c07555580c100404401001510020340a85110a081c4501a00c0c0514072401c454001000300c00014400d000060240821110050010500e03070800701c03100c124443c12250a58207120100300400a450f410400f1170003d01d80ca0819071078100f140d4001400d94006d0030000341c0b0309520b40d11078162954051004074054100400700c109160300404001e12014000c031514225107da603000810b031003500200781c07284510690b441c0b14840d16244280400390700009003660720300c0042c22000c40c020090001034080d07868100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 146354271 1250 146353021 146353027
    0x12011e03140618030910030f0209090a0b0f0109061b060603120e040b030d020601180603020306070c060606031a22180b100302010801150507060e1006051c062004030503 74
    0x1119891103200c0c8a448101c3c580c0b0030440e03c4855282d241c0d040700c07411418100001d0f444150f4103618044c0c03003951000ea078440d0f4020100501d02d0100e6001242c1e210056a0360141d9448200c015104500d941c0910302c01f00c0c0001c18822a0701100040c5a94901d104040114400d0354175602c102051000c07102c50000308141d0150b42d14241014460503a40341001c400506d010752898a004e03403201018040c1d20368441c2103521100c1c10b2403160300800c2c0107544c09400ca0f0010b25004d00001c0c905240c5100c11181503051660000380684240a812081c440d45048407042d00944010004410700b0041c00401102c0c40c0784100c40b00d6251446040f081e00107400c1040e07410015031510b507140e42002040707400c808074481010700241c0d84c000c034001d05546480c0c0a400f0003025406084c0c0307807030043ca1401010542862048403455030080750b01600c0a0302a0b400303000c895100c0041284510b10104219113601600000d000032405503005880761141c43c0003444001d01c0001002c0760198030540050328943c1c000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 146355521 1250 146354271 146354281
    0x150314130614090c03060a150e100302120303040b130222060f12170a1b05010603060203010b09091005030309011b150c090801060b0a030e03090a15030605030312011e031406 76
    0x180200c42d8019030810b01045239480d14804880151610f006494a8540407000229680304040880020f960000c0c540c140082c0041502682c0381c1c8100ca040720072420400c0420410b4803824060611240e00070844019a9907003200609900c0201100140950b162a000904160424000005005001d0901e070307440d00c003800c10120307840c03401600100c1403900300038400c40c0590014402c00d220f01a4004541060814140180580301d6508050040c91000000041020b5800001c01280f03a00399400c0005558603604402990b009100c3c43e82c040d00100085005c640c4601480310210a440007820b07100c01355911791070116001c185043c0031300d5544400f010802d54201301d07120001e00d842c000a1000c14100100014203004449140040c5529520201d20012061041d03400000300900b01403009036407200c0c900a5a24500c2c0080040303890880c0124603802e021040721100d5490300c1d01c036881d99103804071044104039004441504541482c0c404000500d10703d03021403040600e60010030031403c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 146356771 1250 146355521 146355523
    0x306060212090a03080c1e0d0f0507050a060e0304030c080606091008190c090c030614060f040e06010c050d020714090112030e0102010b1306150314130614090c03 71
    0x82540351079040101880010b00c15500c0c0b02c2200b0503650700481a5458008084405107400c0569441c46102c000220800960032400a410324299100d9642d829202c036030820241c480c1d00c034040c030103005900140032003408280729400005140c00900200e82c80c00c0c2d5652540629896140c01c040c0c0ca540280c070500c08507180c20059607030803140c141c100030a0540740a003215514004400403420b00b0010240c500103010072035039544020020070205005584101c2001001004940a440c10b4029105141d40d44c50500e402500e40342c9203059a40b42c135150504034049881134004042504111f1000740403000130340107021310701c0484907540040c6419403c0251860410200005580c09500703082c0040104180742d521070300010740c050401e40c0e001903003900102e01401c8560051070700042c04214060f0311701c015911800880f200d0040c0f4069445d0415011015641e00307500031448040480c0c04201d4015025202c98030181c0705040000d204a40c20784500e031024012180c41070141c011010092a40c28 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 146358021 1250 146356771 146356783
    0x10203040c080105012403140412021203101206060f030305040906060201020a051207020f0f101b09180b190e06030604021c0503040806010b2206020a020f040f050703060602 76
    0x485800070700c015811701e081d10140c201c0364034a00380700980d0100d0341c06c2d42c0750281d03020f0041c0000300c0a0702c0d40c0514150070441c2e000d0170507491b030000510502029020240c449801c0ea8060b03031040c0500e07922107180c06142100c460344214290b402d039903070380400144141c05050420040d48039848054455241159181c100c41b43c0f07a214a003503900422050040c603610404403010f80192002542058440c18401ca1030702d45010300d0b00f01e02d4443c082c200b1564040004180c152205030400c02e100544101070728811640704081100c021030b20340d110a100319410703241100010316080b88000b8040b9064400241c1e80603840389558110902e811060189103044030741d82e58041004d070001e20007401c0c150f020030590842d010b100c503c64000c0c004207400300700041c021070b0014001c03002111401d503182c0004907000e500022880f170002045080f10705810500c00c4001d02203600d80d801804240300c46400384081541c0c82c0b00b80540c41903803404480d511880920900d4080c003099980003440604040020749000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 146359271 1250 146358021 146358029
    0xd0f0608010623010212070609020405010305060907080a021f020f2407030b0d1e020301051906060903050d2d0c060507050c120c010e0303040b0403080109060b03060f010917010203040c 81
    0x804003d0700b01e030f06a40c00081103c22900084101e41c2d450078039061140043c40c003001c0003984641070100000c20700c44002811341c003582240c0e0a1381d031050b950354100380e904d107a00c400085d0001642d880400d403140f14028080c05070120b6005840058140c0010039040200c4820402000310308440e52512103000034000c5940b02c2c0c031500b8108445801e00c00040c44801036a24010415112002400021079042d081c024440c1e602078024041420160300c6180d102c3e2104146060a9292610006420707104515600491750044003400b8a5501c58034121003411070100110b142c20b5600000701c82c0c1c0c7d205503a070703c803010361a0794604100044510340b40c01aa000504114204041403240502017080402c1c285400603441095583e25503000ca180750140030105d001142d1400040708000501072651101440b03148039541c0d200041e80c8640d03442080b10514007511030510720500004407142071070520402c4c041014140715906c0c1d40c1da80030100c036020420f41103240d903035004000c0c40100b000f0fa6030300e1000b41c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 146360521 1250 146359271 146359319
    0x17070608060319020301020f0a0801080606090f0c0a03090f0b07030509031309050411041103010801200a1d0a090f1803050304031412070c0203060a060e010b0d0f06080106 75
    0x10300780000069591100c1090012035040311140500841d9400d604483e00025818003003520350b0345440340641a19403d12444002d03018540c0010180d10f004120181310700e00768407003509079440354061004290019102a0140344c0ea4507407000c042464003605180701803160744107111a01c2c0c110001403c0c0e0300040c01d00c0709560b006010b490712030340c0d0300c011030f10a4424001d070001301d5a50303900f406000290030401c59a040f901d0643c059100d10001c0c17000714144d44c8150001d1103030354204854613140c0c4031009002c1880281c11301c40c6140092045446123082401035402c5031412800380c00240443d5800d5000150581e038440c043c002d9201140590802e1946282c03103000745510b5a18003601e14840103000900308903d041681d450b072100041074851503502c5000b034510900e4046005020541c842c5401c5c3d00c03074401d60001910010b142e0154400b940c0c200301d0003884070b0740707000d814652030340260030758808558a440b01c070890b512181c4186001800008004980203181c1000c0a01e020301d074009005003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 146361771 1250 146360521 146360537
    0x6120816020d06020702210705220606020703051902010504030b130b0709080d02150a150b0c030703090b0c0d030b010c1a060a060f08010e04020d05010519050109021806030718170706 80
    0x6002008c035443c0700300c0b07006554000400f100003004045010084641000f16032900202060305640081c2840640344154106c48850342c0032201d1130401141300c0b9009002981c00c00080c0002990302a555400107034035503014201410544d40c003c02c902084a0070700011301d54450422108000304040c2c00c0854207800602005840340400c120380f580e004185110464130b6002d84201e4001c001c085800500c910381120741c984200004058595205170001e03400624808400301d404140541192280c1c0c4420005080000f82d0001c20343c007401405c0d2240d03051049402200003c1342030394901d1003c066040c0c1d110001d40c0360404c100700d103e0700340d0f41000b020400c80032040042c441d004503400307064a207060445803540d0b40d5480001c50b0f007046410018682d50030034050000300c20351103101141100d000c8200303000c16a2116030b594202c8c01201b480e1010040c2c850408409403c00e60000d40d00980e040c5041c1042000000803180c202039180c5c0f100074800b240d60b90b054902e210074040180030300f40e5840d040710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 146363021 1250 146361771 146361829
    0xb0901091508061f0c08030907030b250e0117061c0c08060106020a0210080402190605310902030a0908040e18061611160b0c010f06120816020d06020702 67
    0x905c1d80c011400409108000001c50484401007254a005580c4609501280d1034404c0f034014070722186101030741d5654003101c61584824041c07460101c2813401a9524507058400d00c1c1285440040540004c2d0003440f5030b4208041d1110034521080424069807208107201d01d0001014603001e4164020011500644c1540f070042c1d668000b0001401201d140240c415150341c000183c081100c0100008203920030507000580740d4000029003801000c1d030a050840c0a0610380300002e0400310500a8200304c2c012009201418031903002c7c50b0002c02c00c1c0000641c0d08d0660796804803c0c0d0294000c03200059003102040b840c0c1c02e0700300305012040d1400001e08828204110b82d01104100c020884081c0141130b29000c040d010f08100442061800110403000c00f030f5a082003038a198040c000d800425401c00d580b054074142213000311130072a865001d03103100b000c1035a1184800ba8001c4003000c20025868815400542c0d1602e030413582c09401608016a503039203901c104000403030030785070441281c2581c40c1070386 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 146364271 1250 146363021 146363027
    0x9050d0309030b070207050603070c12020606010807110f0a060204051e06030a0c0e03011506020f030309060a0b06070f06050105041a0a050103050a0b09130b0c040803040b0901091508061f 82
    0x101c1260781c404094100c50300c5401c0c0c1a81090190380109400200100402c0120399000a521220a018072034245540702c96400490300d42108481c1140450a11008074664511420643c00785401ca05d0a0304d000840850040d07040ca0102501940c10030380104040c80f2614200300d51415040c4103804094041d1003c0c0d000c40c0b002c9c000240759152856854000103545801181d25840500700140208290039900391001d001028600070200148035080500c00c5407a030020490780a200381070001c103e00d0f40e50710b46403c040c214030a01c02d90000d002b40500c83c0000c50342e4030910079541c4200da01003015030509003807004450841c001d01e0700001000030b035103009456018030142a11003e01c3c001c50380799a200421000b07092058600f5030004d804d01c0030008011006000011414401c005010b00d613106c2d0807080505019034061400345401c2000104200001003008111841c410b041c0b0380156503461469845c40c0c504001c2d038030f02161750308081144510341241c00c0100302d00456006402100006401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 146365521 1250 146364271 146364287
    0x5281109070e120604061805030d090c081f0b01050702010e0f0111160305150906070c0c09020a050a020c04020f250b071e0201050f04020d06060503030a0f09050d03 72
    0x501030340142020505461048401100b9040003500d8004a010283d56055079104200c0d02038809500c0d01e1090b1110760b020045280300140c0100065080850210b40d480007000d007050100c0e0040c5000d00c000461100c14003121691554103034142c070406150600c48001c3e2201d6038062410080c0401100d001030381c2040040a800300700740c0c2d02c03261780312407400161100281c810040381144107901401e200606480c104005481c03140d0700307032401d05464030742d25414904190f4071080c8030f4002000046405101c0c0300c1850390f40340280940c8070300d580d440310703030504aa0100340070100082c0002651b40700b00da010402c81d5140c0c2d50580e01146400c0d25448045114000e6200540206510380e103a00101e0040303c0da400900d90b0050445402d50030098000303801d02d034510064085001a036146180803e0040c4506840b507508010000f04640c0c49a0030440d5151070164101c1e082c96075070002040d20380742000170f010fa680194544451070a00e01b02d0180580711254807a5200e4281c00203543d0000f5841042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 146366771 1250 146365521 146365553
    0x90303010f1d1503070f0b0703022116031403150f01080c09060a0302071505061e06070305091201050f060406090614041104180b0414070e0105030915040528 69
    0x4100030f408090000307080051a0788a02007001402c5004150703c0502401044900e100fa000c0340c40031000d68008068004401c002b103000c910b8180103451007506200708039a101ca00ca8548080c510401d46004003044c0c01c20f60720070708240340c241400b1540d410301012a90681509003400b0242c0c0c54074403500c5241c0d100d8030b5021030095a000c5404044107004e601912b1445078070266866043c10b100c1003407401880b084920b188242d0003a101c14412110b0b0410740072000c040541060302e407080b240c405a81c83d9004560054020300e01d2058032440440c04c1c400c681c0075807a507045d0b056043c02c00200308000d8500035003080d09030f2450b125040010036440010003c41a5042d03c001c0381240100e0084c61103405680d028018451a860103108010442d602080c10004100c4041000c41c0030300c8403010800300201c4400307000c0395070348610b59403542c014406181c0c40b40b03803c41155500c8404642a520b40d400c1602e0848030b660007040d010b0010441c0400050001e070402c850180544200e8a8901c90241c00080b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 146368021 1250 146366771 146366791
    0x601031106070f08131e0b0901090b03070207080c01020313050f190608091902060a030908091e03190c090203090715110c0f130b04090605090303010f1d 67
    0x3004101912070380d007500c0c1d200f0f07007021181e01d0140c3c860034501516407042c0c0f400c42130132080d2480401c01140d05d14211109264a2800020480c201a004070300f6510001025050040c03000e0005011039299001b14894142603000d070014619013000c1910701b1040c10101e0f415500148000ca0506c0402c95064081303a00440311381c0d5074203003003d01140741c0042500480003d007040301000b00e00d540d08540b41a008105010840e9000760600c113410248100544000b0f502410070000d114680744642c02012210f03004a0001d0b1802604200084d440721030490000040e03050030b840c2400901d0140b24250b1203080d841c40d0741603002510307900c03982910b110303000c1c01424542c08004a200801c0c20421580900030500001c000ca9489200c042c1c0399202049031086c00b841441c0c1d82802a00700140a00107105005e007203075408444101000005d4648488040e41159440c0380c2e02d000f04403503005d254025132a11024680d2541003860300ca2901000740c00200c1c0601c840840315410304902c05001e58170440080c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 146369271 1250 146368021 146368043
    0x180201030c05210c16030801030c0803030403081f090612060f0c020606010507060905240a060e07030c030207062f030c0f0711030a050f010e010b13051e01092c060103 73
    0x9000d00f20355001710320460707102c6480c600b9020704054001c201d05041e00c2c06003900030030180d40c0d03072a410703540d1000b1140100001c00c44004200b0403540101017095140c00e030000c641d181c9880300e01440403114140d00002080012020a6051100750b1090741d00c107040301441072000150001010b50340340030240c0f0b5a81000310000b00503080c001550310882303031154810150703000d0404188141c03254400e50ba842c003807251145000720300350003500c1c49540205d407034401181406a1358460181c00401520754407400789a0200600c80000d000c6101c5d02d81106c6e400810600c0704100d241040f0b01c60001d05c617240307550307540400031f015082c84c40806803510101035420559440019142c0540300814441a454240c0b0401d90720808004007c1030020301207460340002c0007c0310010a541c1d080c0c4000e01c0c150781d00700b91805240c000d140059004250b110701002c0701401d0054511500b00841c0304240d200c4e0401aaa400f0030500142190584a81910700303071004d04000103113606000d843d070743e0621000709070b00741107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 146370521 1250 146369271 146369281
    0x20f0f0d08040303020102040302041107030207030201141e040303020c03062809050105090c03010c0906050702043b060106030501060806130e030a2003030403050403080d0b04180201030c0521 84
    0x2204030a42001c1e40700c54440c1c0c503507076249000780c041c3d0003034082284228202420b00091100760002d81c1c4210350194000c1c0341d554910380064524241081074044800e4080000c80004000301c7e9035440741008444584d680d441c6542402824101c1c7c44c200e40d403280e040308050103011a590186590309415549892044031303004c1204000070180f0740d0009019501380130800001000104280300ca03036506034001e00080c0c1459400b01d54003071003030142e10b0110300244580700c05410154000410014144007410510704140d01030b016100c41014104040d01e4113880003410302d00280420790051a4606003030107994140007010b040d140b0700400c0319006806401c03110121440c05e0f001007404030243c100f600e54400714488028089490054a103884400700300e11078860020001c1140d200e281c05075030702c07407c4c41e00303603500c03012203500c070403100082c00741c844488075400da4580c89102e916490203801c1c0c207081c1007030f8800541078802035808081400801d110a00b07400002108100601c203441001200a0b41d030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 146371771 1250 146370521 146370529
    0x303010942050301020306060409020f0c0718200f0903010b040216172506090203060c0705010506090c0405060717070804031403160605060f1002010b040b04020403020f0f 75
    0x20328507038030300110440548500c0ca03803501c03441c041c0a40c41c0c0c005000c20654848041c50709030b22054034020f0b04850100802c01c0181c04a40c05080701c0e0240c280380038038040181580c40d1400c03180d0b40014a100e181c0382000181c41d00d1510400f01c0200201c00240c10031691200703510307070b140200d1460007131700f0000240d000c0c1da036a404e503c441d1110600400171503d486130144240350780cd59012084600031303250341c60b010600300c0355000d03180802d46508203240007030034040714203152002c0d00308101c8101d41c03240c40c2000140d80501141e4418000b207803500e521340c1064109542501c1c4040e0030540600c94074001e20060820510803941503c4054480c2c5588011604d4041400307065230f6500390b11060040703403000030003034000e004104507401641746004a80c510f032040c0761248140882c48290b1140c0000540008000707070807c0f40d008500a01481c181014500400c043e102a40081e100503550395048141e41c0c582071207004400030007541c1c1141814110390105024034241c103003040c0318084d40d403038808155035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 146373021 1250 146371771 146371811
    0x109050603271c17010501030207050a1713061b06020307020f160510081009090c080f1e0705031f060302150306030c1f08041b0303090e0c04060203030109 68
    0x1480354001e804480c800d0b080c0c0d500d50745003580402200c00d440341040c1481d80304080090120280f0100103a0070391a0200540082d440407074100c0d6136001e0040e89070040303080c264049140c1080c80c509142c0e035008102c94041c0d400050303081b01d828002c4049544084c08134548564aa80b58880f00c010303683d480d001c00a0380703004070b03400103400700d031291400340742c0c010b034458048000b1540191400714440d44800b80c1914280c40407030300a41166000303141005030341402d07041415030501540c07050340c1281c0c0340e4208505140f030a0500d40702c0c5030300619480340c51580d0240c00c00305403c860400340c242c2500300000070b51030310744402441c000741c800b4030002c1c43c2c0b51910f51310000c0295401400003050f840003080c3d90303400e50001c5900301c0c820f0003807504a603601d09010072314146804908000c0d40d0700180804041d1520710014101340d590301c844070455850000452101c2000c2c502135114015002d2400721106070281004005c601c00010620003003051a4000055074103640c94103034045548082003090b000ca0381 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 146374271 1250 146373021 146373061
    0xe04051b07080a030b150a0f1b05030c060c0306030d0e0a03060f0b0307081b010302090301060e10030302060f10030b040c0315020904060b0c07050108191a030d0e01020d0c02040e030c0312070903020109050603 91
    0x100272100ca10100311000004044000b034035030980d00542da49906c43c840602007101d0a0740c250700300401103807070a48904d02800b5540c50050100807160788940f501800c841b403c211840450741daa080000103890304102a000800060004042c070340300e8a440404030101002c010380c14542c01040c12102941e080d0880005040c40c444c00c440345e80740c011103c3c0b140300e5440c1b00a401502510021540d03000300c50404038030881003a002d0103c100d186640301d03040300100410a40d13200c040700d01c0120001d4500c001c5100b004c141c410025803141000000c1004640c07042e40103440280c400c001404808001140c1e900c1240c8090170803030702c203a82c6c2401d040702c040c1400300304080b06440c00d080350f107642303a01c0c2060446d545d06c1601110811301e45040c081c3c6421054079442e41c0540d004a5880d4140c03032007600b68080c41e500c003920200d11000324a1040380385810008500c007060b0404a048403901c060144240c2c1c0c0300d1a00d103000f01c101403a41e00068a64030103809154050100000000d05c00c50003038484140d40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 146375521 1250 146374271 146374307
    0x90709020d181217090307080d1503140c011706040203040f051009030801120c15030e24060904120305060d0f0f0c08010c0e04051b07080a030b150a0f 66
    0x200c2c80c1c919003240140707000c0441c02c012544452541d0b05441c52a058503200c1c0d058800190310341000da4582d00965084124a4041c1c55107031203c108405100800342801144101c4510160751183c005803420400d911804504005d100f500c620300c49101000c28940018041d82c005070750b030b02d81e820311040c040908080940341348224403280c240d060a036402039040d94060f50b1346501c513076200c01c0c1c1c0c20706184030480c3c050507a09104509010600c0d03035001458a0001a06000540d000c0218031107003020384030010861950b1485801460a5400e02c500a42c402c00444423468985440d0b40c42d040c1074140f02803030108044d0744200180d00d0740c48500346582943e401003500f00500b6928500720400074140501114410742a000000e0000014003498180990a40f078510304560610140700040c80014010302402440b21f0011802460002c000c010031809225001d0707560184110140903075508000c130b140114480c0c910102c0d0a8401007d90b100c404036450aa0403400e69170404880006503c2c0d004410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 146376771 1250 146375521 146375561
    0x90306150f030d080603010c03060605120703060807030b01080705010804020a1206090804030803070e061c050615030c0d05150603011203090801060b040306050c0405012304080d030902010314090709020d 89
    0x242a0413113032007440754400303c00030300900b008442d088003078a485100e02e81c007048080c4040c08060030808440c6e54020305515000802507a00d410b541e1500d0718a51054910600c0440180482c031414000100035010a00304050141080c0e070106440d81c40c0ba00c02c2c09640c00b5004080350800005420640388550400e00c082d0701c9980301d084c003400e00d60060343c0b03040c0030522a219150b440c0c1428019240300b1300b410422850242c030b4161003032024000040c846684003214116000c113007050a8080d5000c6e031140201f00d92149440c1d4403220482d40042c0850b5800b944c2c50f03100921990310b0b0ba040741d0548500d851405207204e10761405651085054001a44a5081c4000424110010000351003164002c58050180352103400c81c05105118501403a400100c000742c01c00c1404040840c40b480d060804400540760030365130355549007004645c007a800002134803008901c0542d0f9050007080a64140042856460f045c0342c0c02131640c4846070f00c0b072849241e40104400c0740e03404c42039200c0343c1c04283c81614490 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 146378021 1250 146376771 146376793
    0xb070507330c030501060e060c030d0f0203041e0c230406060806240706020a0c0c0303020a030809010e0d030b0f0402070c030c2705060a030f050f0f03090306150f03 72
    0x14080c410000041522454048654481403007401003604035074041c1c0340e03a03c5038840300040c07041640c0300027100000361100f0480802c4202e0203105d180f00c146000c04005841e070601d480e080030204e8000b84045003a503038114114001c140100b05d214111424000003241c400e88800c0510503030030b21a402d00c3d9020b031400d003000451640015a00d80320700c2d000c0b40c000403141c84040c602010b105100d009a12a09002c1c0161000904c0d00ea00402500900d82000c50140030745540e40101c0ea40d26400850058103d803084008240e0080381d01d0741c000301c80100074090803010007406541c8452400b007040c205522043e2440917a1103e1990700007090010b041550390703660506180d505841c180c031007110340e45131210000420300c0294201e008480c0704096490504281c040d80f06000d04009041300d82d211404400020000b00f803000008101071203040a0b0102c901b0350070020381021241000141982c1003000a20440c1e0f40200b03c45501c908207031001c0c6181040d9902164500140d9011244c0601c40c0c241410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 146379271 1250 146378021 146378093
    0x90806090609010b011d090901020909040615090b060304260403032d02030d11300a05093412060e07140d050c03120a1b0b070507 57
    0x103200e0342c4810300034840c0140500046540550660154507a805141e03d0140c65203803401100707801109020015060010000c009100c41c80c050390304035413141c3e0f00d400c82c210304514540303c1802081c9a0908200800c4840c0c0820b15510000b000101107000030700b038082c00f08400380081400c0c0c203c10713440143c80715243e00d8060480300715041c00103080030136895095810780515600d200800d00c5071740a5814002a854120040c04200400c200c00400074480280741c19551101c1e2001e6044200c200301d040c082d82020199160b6000c0c100d490740d6401c0603b004a00000010300820111070610705044481c1d0510b0310418500001100039811100c4c84c10005000040c4440d200d00140201c80130845401076840084d540c80c6540b251840349401ca004c4d402103031402c00310340c5030382c0ca005000b619520135800c80004e00f0309d01f485403011000d90b4041011101e0a5205400301101c1c040c0b00c4c02e4001c2d450054036a0703280090b005080350208040011200c00b0411517026007209501030340c18100c070000b9844440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 146380521 1250 146379271 146379283
    0x1b01021306031a03120c1c080601031a030c0f01030b0603161413090e0a050f060114040504020607081c060806010302040e0610090c0e0a0b0c010501080d021b0109080609 74
    0x100003c2c10141e10009403010000d44a120480041c0104100c0b40302c07110b411442e811a02e407074602d03400f4026103204c0741d10b04503080c2c880c0241c0c0ca64071141c1a143c040005800c68002920849084110040489007920001000040480704480400c0c2c2c03c00e00358012070181440b507005c0358101201109002240a94030094a014130594031114410840d010441c0c0250152051b007481d460100c41c0200301c00300d016402003c3d040103141c1561030107841d0351143c0c0e1819a40030b800c891954800f10041110410b0190140044181100d042c0710504185d000118507005981000c0e0410300006504400303102410059016810703502c2082c0009a501d060081e140d0400340700a0327000e18208171007a40e0541b40440d802e44118285210311441508018000780106540e000b46401e010303040c840c3c0c0905984080c690002000e03400031803955000d072802e806094034010ba011503041da110782e40b1801c040e60085500300801610301d8035071341c0c0c4000480040b076126585901050440c000c0c40184000d1038008205 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 146381771 1250 146380521 146380529
    0x21905010e0613121104140a110403030504141206070201050a0507090303080714130b030a0606020304081f090f08070212060702030f0705010605040c050403120e151b010213 76
    0x48003a110980030a02465118800f0010312145100d0070034040c1c803504600806142c1d001e5032450344032540b00c3c00404c089900d04041c840e0b09414581c01c01002940c18043c0c0f000b120881407405081c28610350b0301805038043c0b03009e09001c50408040d4109103444103041051081c2c1110100c803400d00384100068004c11003030340c010340c0d22410300000a8446014a040c2c4048079896074038404140d490b89801c86000b40401e0840040e50303001c01614450314880b14246014100c28061250350b410200ea55400b01c4d80039902000564000340410405040e000c520445903480e9032050702c1524a46610341e00042261003001450039048400304e1040c0502200070703000d010700c03d490000c1280401500d19640d008201c40c0309006900400000c03010b1101040036158803889400003041f02916034001500355205602e40f040058070214040050040b003003e44404100300c1e04243c11101d6420f4041002111010145040b0030000158031070206010040c1c0302400d001900215215a084000d400e240c2c201d85c42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 146383021 1250 146381771 146381777
    0x10510021e030d1113091e0506010201090203060a0e070e0903250f06020d1a03100b040b03060f0f07080f0610020a0b0103141b030a02010e0102070810020d052a090d02190501 76
    0xc404640000c0d60307c00c1c240f0000070818080e400001c481300f88006404010131950440d501c600307070840161420041d8501036580d14a0104407825184c41440c40d0001d00c0d8013841c40114007005000c0020030200803a80400b0710022a01c1200405081684016550810003131200c0000d040c03440501645030301400c1c103e40d07041c60901c02030045e89603052000c0e120215040c1d041d005a035048000e031a143c1d04c50300b140701001e400820400c0c0250000380c02c084080703c1d03140441c3e90101c1004000441c06038500e40c8500d86007061403107828000c414804e0300d0f00080c6000e005070700b4510700000e007500800c89015500d0b4400c01c0c0c0b0410350b8407440d0012680c1d0050446080130311581c00c14a00c410b0030181860000c41004e001030080312856001100d014641c074010f01d055008814004c11400b000307010020071b00e44964405a5680c169040300400c80d00000c021800e002c83c10344d031045068503091009803401c144501c4140c1c4a91080700020803002880318000c1d4400e07510500c804441100907084000c44009807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 146384271 1250 146383021 146383057
    0x627031106131d0a09120f0e03070b0307080f09060408090a0b18122806020f0c0105060a050f0f010c0804090c020a05070902120c070c120b040b010510021e030d11 71
    0x800c0c194240e890003107000b098840c2c103800030078005215807c40151080c0d5807421104244540012130f0070002c09400069a50314004104814982c1081e4040c9e0071000c1a0300e2032040d4a094503140d0740318507016000405180c2c2c000b0b00d1400c242d4401c55200701808022200c241d80d2500400e640c0d4070400040d000341c1c02030000309000480c00802041a003010304d89190880d4032507214651807a505003091004482c081d0382030204554400007003018004100350000001a6400c10500b003100f01a0542d00107846605410041000c0d61a0000b403044e140340d00b0b00b0502c1500000c1c3c60120240e001d107030440401c652401c040c20707054a81c0040c2001840780914290b42015844108001c160710a50703008003400ca009001140800c4008002420ae09000310075004100b61940b40c0013450204500050711701c10880b03424842400001001d0310700502049805610407d000d1002035140e448118210900603a40c1d01a03c0800000b80110354804003807180c1006903400e25080a000340d00b0030440b66441200403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 146385521 1250 146384271 146384281
    0x9100305040b06120c010e1903030807230d09051e0304061403011208070c09050a1d01061823100602060a0204050109030b0a0f150627031106131d 64
    0x1803460120900d088020340788012005e00195540c01150b0040b81e000898200c061504410348444807002c0c500c40c1c1c1e541c0582e400c2501004202101039501d0103007600b0340e11000901c8410080403184500a9034601196081d11404c0881c14034010540703400c1c0004080110f2480003a000c0001e0003524015100e81e003290b0705402d85081a0701090050348484540100340401050094024015052007040864082c5490ba90709a007a10010749040c01c2d0540c5502c0c024010a00c20141d5502859041008102103450a455258661524440141032035511680e5a140d640382055000e5a000d18111511290900744074089048003e80b00e010014000d40c004241500d8090085404640c0143d640070300300ca040d170303c4221040c0d0303001c3c107600c0d199940d4a0040140c20883d00400202154000c0508a080c0c509040078003200c441301c201c03070180c90450050040c0c01c100e52021000340d0340c00003d6039030000101030104996124041181010128844000501030380b10140001c4140c1c41c020550201d0720f407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 146386771 1250 146385521 146385529
    0x1302030907120c09061203030b040209030607030506040b032a010908030d02030a060e090f010f0b09010b0702060405060d06030201031a100e0f0a09050402041503080a11010209100305040b06 83
    0x410380d880391254102a40400010580b034000c030004900034512200b4007940c3d4840141107074480d52114001d03140301c501080c00c1c1a00b51044000000d0181c40661034640d10900003034a45500406840906030360394081489500c0b9580440c0c011000501103e800318181c10f12200f8108200840410703400044c0092845540318104480403104000000c40c141410500128041e40004001c007204981c0c0324000103009201e46a800c1c064500700300a80926061106c800d400d40348912850f950440c1010f0070065140c41e806501c1381154001e40400d505c0300740e20f06c002201c5214075407040d54003c1006c1000c226881e0340e60b01000c2160701c03d803001c012102c1b0480c0c26400040319074581c90703407210720304e6000743c4003d002c2c0c030003c075124000500f020b070741d440090000f640d616525001441e0341a80d800810085041c54400c087c0b03c00c03480030384040c86030302c0c56031580f111b4894500004104940589042c0e003840c0250180c0f2040e0000612490154846520090007050215400d40c1c500030761070041861418 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 146388021 1250 146386771 146386777
    0x90f020f1014091f2d09060518030d0513060c02012106030b0106020f120304050c060d021e07111504051e0a06051201060905010806010c0812010e061302 67
    0x203115115000d8440311000309500035000b00300303e6a08180b446600d8006006010b900c0c194904554480308000c02c0810965091201648240d400318100e49829240d5143c214404d00c0846d0380d5441c03d980e80702d040e00040c1032401a6240420307058801e010b00498010741000190012490f240d0010354010355501048031280140d074030103404901030190880d0700c61075102e01c6076071070009544003240880e45d96a81c41c108c16070903405080140c1100d18052083d0340184443d00c040000c0c500c0403030450400c2c3d1600b0307484000c0301d0340303880c810040018611049840750f01544c000c04078040302e14071080c06d41540e07880940d0043d1401c9410090b0400a0912481c141c0040c510491150380000c0c2003030305240c00e12240c14902ca40c145d07200c1c107050940003020f54440d48150042e0130a43d9905440701000b046041e0300c4a4183c02603014020114000d20107a617110105070743c0103809190990030142d1030306103100c01d880b400101208800c94800007107510020906003d00402d015281c540c5003070f0702c980840d01240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 146389271 1250 146388021 146388049
    0x50a0504090515030709050901150807090e15131103010218040b0d08072607050a0b18010e2107080d0b03160305070e0106050415030f02040801090f020f 67
    0x94000e2100740034030612940b066600220b06010020519480800079150810651003105850340312030030001e409000b03000e821400c05500702424a4241840e042ca5201e52113801036101c51592540d801c1c03a00c1c2c00801554503086510f0340074855600740f0001c4001c160708074020030b4035003803482c4540d2501d5040c14400c942500c01c0040d50040301c5450740040202400120303844941c0f02c60b54a5071040030501d00c200510440f0304c591a000196141d1500d81c00d2074144d02c40b100b9030140418002000400c00124000c000c680c2e0000483d203865032040b01260240c0740c0e40902880700e48ca001e021505c484400140c2d406545c41c600040181c2c0c1400000204661180702c0008004400c1072207414541c500941010742d80d0103005056035820032002403240314402c001e900c10f075007503403220004011810855401c43d0140c40d051170070743d2a0074100140b000c2100c1c0107070075080c10560f41e812007880003c0d5550666020b800d02d040240400081400c04088184051505134440d10708a00d0312051450405001c035000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 146390521 1250 146389271 146389277
    0x50301050708010b07150b060f07060501050904020121060e0106022d070608190e03070c06020c060910090b040f060e100206160903080a0c05010b0409020f0f030114070807020d050a 79
    0x260075606c0403000420800c0603282580c444200001d81da81f03e001604034803a01d0300f01140c80301e000b410650150ba0040c0c3c4018000e201c0750080c00b0160f60301c01d100000301a140c0010035403142c400c2d010040105565448000c94120705c8001150282d40800c04228651224040b102040070000c010a2107008040011090780e00c403002c00c00a8038061181c860380301400701208130480d60b60b00541801e5038559404551280c000151560070044000c000301e002d0701c00da10007400c1c3e5605400105500d0310a00b44118866411f6264424400c0c0c481c1c2c1040b400340418850144c0c0f202e5640c0036101c01c92186014000116014041844160030300f00c2d40020008c156600610207902d82c001404404803c039054a01000301c1e403031020000c5034440d402480d82440a40d13404003a8889800c0840c2140e120410203841a4200029400941c4e903080080030140c02c02c07541040c4e81071941c3e0000c1e0060400120025104a016007001103460b0400c259074800c003a15020345500758a00001110603120f044511004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 146391771 1250 146390521 146390527
    0x1081b040512120307020a0c060804030e06031801090302010b03070b1c0c020a060e06010f120203120a020f0a110102070503150a0908040b030a05012603030105091e0709050301050708010b 82
    0x541c0340000882021039034032020f0701d011642c042c0800c002d03548112245005640000c1141d010010300000c010020006071604406034203140e90000d148200390503185104882c0030010540c07ca044051105108030403a008101d0800a0b01e4084e029001c1c4110341031090161503070000d04031880d20b00700c034400b444901c03160350004181c44141c8028141001c5510440c030601c0c900c40300142c0d852180707030b400d030030a00d0041440390f15028829250744216080440c1e600e001042440042c1c800082c0035020302220399410b922070142017812407524003400d02c0c2c048940302d903100660074000c013010314030500f408c20382c241d40c00035445d603051581d00c41d04400204c02c00c10322400050380006150740b050340258820f01242d890555640f58504190300151008107046a403200104003ca134030300703005190340700b905d414609010f040c200155180d000510410303000300e4420f000a14150001c144094510345044800703a4181484a001800c840f05405050300075840e2101181c030090250555a0486040c00180380c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 146393021 1250 146391771 146391779
    0xa020304060e0d050712090501020d0309060f11030108060c03070804030f0c0611090405101409100305120d0b03011a01050c07030b070e03010f05010e130c03020405040b0601081b04 79
    0x25440180140e07400c65403241c445400e600b003841003c00781c02c85566603070b032240020700b895210b03208034442a009000d0074284c10042d598001c204940320840c60704001070030b2079107412b244000d0a8515046074441d0707d0505800a130320074403805103060f00c10703c00c11a40d155a4030b90b0030a00c0c0d480240d600c40081494000001e000034810f5003081140d0b0418503000c15030001c00c4d92120700ba640c440d55806643c4001254402d04d03070400d80324039030348410072114100350145080503214040c0c2100300964050301404000038102010700d41c2c06002507611400311004003441d6550082d00380c00000d1345080e128203000140d61145014011910210480c002c800080e40c450f600540d015400545070748800d0103080b1700000440c00c0b0b00c00483c030601560700e80000c0d25540384201741c2119600d0302c180807580c0c5040010f0110346601c058040c3d20200400d40e4219011003418010303031604444d0b00c000d602070b0620701040200600070000c0c03400f640081e01c03000041d80f42c0aa15408030b6200100c242c0946409000801c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 146394271 1250 146393021 146393041
    0x90612010605060a120c0c120315031b0303171b0703030914010c090e0f060d08070b070338060f0702041803020f0f07090b010512071d01050f03 63
    0x104111108400001d031a5a498010501c15000903120340041808041024500c01d168041c2003000380c07061918141c41d840ca07681d0940d008117506407040400d079503087c403d030400d0001f1a820010b5608140142e000d81414990355962003c6400101c0020344d01d80c0400640c003c800f002d1a020303699804455005485007600300c8825084884103404168607802450085000d0065040c080c901c00b00020442ca4000c1401070060b000e20743c409040e100c502000c0103494401140c1c402d82200c5d044481030f001c50202c1c2042e001d40d02420701d014000010310828406003c4d01944010b50001421403c100240818194038880c015003144100740c2c248006a20945460f100c03004000511481070030b241041c1d40c5402181c101c883d5a00504480e412901101c2c003490340400c07080610080c03040060602011140607a83c41d00418407882055a4440c80010280d0b8010300c20394800a003140c4485d11541780c4400020301035141d14a072006c01c00243c03401142c0f42d52150301200c000f8500c81944515680b22010070b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 146395521 1250 146394271 146394289
    0x70207050d060b04090f02010801170c09100b04081c0c11010819090b0f0f01051804050102040308121008160e0901060803282d031e06061202090906 65
    0x2c503121a40c40d50800c24035607031445500460381c058511040034210520000d004102c040e0040701c841e0020b94480d1481039070008020f115003109461111540c0c0341c0d02c4204d10b030b90301d01c3d4200c012a550082004500e40400103591194040f40a82460745081070190139103403050b0703811f40500f050400c40030908095020b5103d12b600080514078044101381c8078000341c0211000c0c490b00311200f51401d802d00c914001078014413038000c2c401000c100043d500d40000038003003085210142825504060029003803010a6064038004c40e00188426030320880002c800031f40040813070f11404000302403400414400c400044440030071603855103400345a410070f04031001980000f03222000355074980c030020440d00001d10103800011082c02c0015141101402d10700c16540d180040035003001f0b4203140030340e4401e000c10504400c515500314250191901c1c10011405403603c840102c8501c05d01c00c4603a141c2d422660300c45400c880070360341c80e00c3c00501c294800c2000da03c20800c802e80d001d240b40f400324503a0b252074024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 146396771 1250 146395521 146395523
    0x11031308091203190206060f0607020d0317010e0906090714130204380304050c0d05030c060f093a110106030b06040b030105040b15031e030c0114070207050d 69
    0xc0a6500c04501d0900d155501200b61044e400d50110440c0340507680410001e50080e404403480c1d0628020600450528051083c011f8810300305a44054145401640c800740c26181d80000d008403503848141c02c0c1c00c03c080030303146030b9a0b030b00c03441000445012020580b40241d8080122840f00c08000e00c0c208039090b18081200001e06500b008002545007200004012101c14842d5010409100540384140d14428410880381400d04204110000d90046400c03541d554089032460881030003801c2c81451401030700191807517407254405011481c03c2e000d64441c41092540f040f500b2100c680000c42c41364440507802e2a002c80c62401d03188035407040c11046004901072070320b80b45121480d5001a0b13030942c0c0706580240c0e5002c8609060080a00341401030040041056000384200d05055450480c03d4500800c1c81b02150600619560305940900001800140210107440e000754600d01882c0c4941c031030300112503030f50b281c00c0c09948102e410400c034610441c0b00350050013055243c4000d100c0e981d400220 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 146398021 1250 146396771 146396779
    0x40203070e060a0915080f070305030901031802060304050606100306030506040f170d090213020c0d030b151b060709050604030f0c090f0e0f070f03080d0f020703020307061103130809 80
    0x80c00b1031130303510034410141d01c0855101200030f0189868407603414200b1016403150190003449091021403000003c4490080c420310340021608030102e51210040d1600000a6002800200340807d0040021311760740221811503003603000b581c1c844401c0d000c941d0b4a200007041c941020002602040460344012141350082c41c52045003a510080340155901562004802c0341e0703981035240540c140840b009607410002e1174218508501c3c480040d0759240c0ba20140c00801d52140d01000b0380342c468141002081c109403880725150760000b01e44c12007102c02c0074140c401d00c0c0316190015015600c07400194080b0f49015082500c5c0074116160307090403000e400c1040c2d84400200c1000102c458491088402154034180002021112448441e05200003425640710b99030018000303001c1c400103481c0c1d10301241e42c0180d066a4618008090001a01d03c401e02e10714410310204002045c140c010005000c0184214410809850310740c82c10344e00760000303640081040f082c1151000005808000414401600034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 146399271 1250 146398021 146398039
    0xa060e0f071d06060a080c0c0c040501060201090204051e0f07180e07110c0102030a0309020a030203030a030618020a021b03010e0a3f05160c12110405040203070e06 72
    0x18445241c81d0807070384200140c41c426a68107071a282012070aa800030750842c1e4091030421010801400688003604075201c407000000c264603118400c00c40c100385508041d1042c041980d48241c042e000742400602a4040c508060001d10006d60b02944200b4092a201010a0340c0d2035400c60003401d40d41c002d00500034080740041c9030404040d1910a10002d00c00710001c0c4034249000407006180501e504504038080d40301048441590b81c021040d9441500c0342d00c0c0c0020344505900003e1700303400b596032020b9058000000e14030710b107545c150440401d8030810041440300c4d64500300640100c7c451280792800681003142144441e000280032822840070060021a650082d905000d0a02e004000e084460341c41c480c0c9400c42001c01e4004400e07150341032080b03e41714009012501d01e03080300c040300b44600304180091714a420900040010b0300301900500c0c0300003040d0712a0801540341814600661300d10003800e4820f845480e00c0e02441e031042c0d6002d4041d0001900d00514582c02c100d0103400703654030510304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 146400521 1250 146399271 146399293
    0x2304060302070f06410f101805010f063204080d030c030506030c01141b0601030507031106093001020c0105060a05060324011e030504020301050f01080a060e 69
    0x40c01740103405d41c1003c2010a0541d901c4800f4480710a04903243e002215000003a01c507810420110301e5482094001d5100066a646003c1100e0b002d040d00501c21907090301c0248040180158441c0e416288902e12032460a5180d403c156a0344590a100e100c1959200c2030702c044211413107480b849003507045218141080e407a46600b07070400454240400010b80d40380f540c90201caa06002d419081074007035020b8213a141d180307400282045034051520000da1700008600041344008400001d02c3d607600c1080d1038103075840e850710a4a03a0f401e8882500d00300e5920b9111740c0e6500e0b14108554118200520441201d01404000c61140d00040341c5a9400c11151010701c00381e050030700050503a0f0419000002d81c900c0c0080030840c614040380c010740d0242c401401009800c030840311008034142818800c0407951118000100c981204180d034214914040380e200c0300305c180d0190400350149100710000e00143d9904821008819400d105440390f0350b003c03021020108409a0010100e0b01c448401e4400705444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 146401771 1250 146400521 146400533
    0x206030901150b04060e0d020f04060305030309010f02130510020703050d09180504020607080c0106030f0c03060b010c02060f0a02030702060f0a02070603020a0801060e0d020d03020c012304060302070f 88
    0xc0354021a965140c2106806404a5000d180c001d4000081d0b22410107061240007031850302405086405003100c007040350159911207005462a400c000c0c0144811502c80c03410703903100d80003910801c0b03d40d0300709450218001011b0090300e555540b000700d103080741403910007048040f5490034551420b60251240c0800400c0b021311a0495548480c1c5131081a2440c03d001c01914000c0c64001c400c407140742070103000c0146d8680d000c564807603400c10407080d102d01c00b080c4803d005148661005041488105000c0204402207150380126406080200640c03050036005542c00340c14900300a6000204008100c41086a800908a00b2145204890401c0410b602140c441ea1280889403140700010900321040395041014102411071441c00307600388800c440010300802c006000d440107014081c0d109200039101c01e400510781e01e40040030003008807098200a902d07940c0c0c00307101a000508c00f032045101da40171144072401c0c03680c00d410b200385003900d03005d82100250000c0604031804c0c030542c4003500114070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 146402877 1106 146401771 146401777
    0x103050f04060b1903051509061509090c06030108010b103e032206090509010e0a0b032b080c0d0507050904020c070e070212030c09030a0206 62
    0x7072000407402d00700d90030f18400040644c20000144000000c54101d6000540c90301d45240c2c030741084458032040100e401d5402113500c90f0002d281030418020840c0c0c007411402c140c880b012090310006401e58800ea1052545a468030360ae91030514106110001c1901c045c01e21895544504100040360302150f644150706402c8a02e07441c101a804003000303480b486030442543c1e40c40100c1000b10265001d0300503102c040a08070035001c07904e680103a40450540e0801845400c00ea0710307000c0c146a031440000e0600844c9900d0300c102400035181000800d0420030b024628204008611442c00070394110060740c0c1007000035250900c0140511917084401141c5101000b199079520311a06940c0d6100b103c000d50b801c1480014000d84102d008160081610b607450106040c548a01d80304a0395000c20005039800b0103000c1020030782d85450000140100b0318083c8c1950f50b505210340001d28030750 = true := by decide +kernel

theorem cover : BRFrame.Cov 146223021 146402877 := by
  have h0 := BRFrame.cov_init 146223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 146223021 ≤ n) (h2 : n < 146402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
