-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4141
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:41:12.548057+00:00
-- url     : https://prove2.me/submissions/9662f389-ce6e-4c3e-9044-44da438a93cd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 744604316 ≤ n < 744784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 744605566 1250 744604316 744604337
    0x40501061e020a1223040f0312020a0611091003020702031c0c05030c06180105040c060f03110f07020405010806040b0f0c0c190b010f050109050d020402040e18010c 72
    0x160000c5410201400a450300100c25055201c12401c1000030100188146601c80d00a4025a40403201c41c0c00080400324400381c020808008000300c4c0614421841400183e841c01d0000818512441c0c0c000d84aa0046800120441d515001034070055a03041c00201070104100d0300703a207401000400c5100d014201107280200707030380110344c441e40070a41181049880c0d2a00040c01445000c20412294100e01925124404075048980b2014152602150f01c503040c2c1e07003545009418494035000750b51248060040d9482c04109481d0f80c41040e5480701403640c0c070a444080310030220b0080c40064800490195680c20910402c021500306030040d02455001c141088005000080903942081000301e150311030f40d5500d10031030300301e00c100035041c5003c2c008d01c0d54040c240a10b03084e551658030301c079603101c1540b40e8849e48180c800c0d0000d1b101b2140002c4403541c00708402c2c02c1c6004e0b07030650140060070162406407208400c0a2808059502204200307103c01c2500e03c3d19000e00c90181040000d00d007500244 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 744606816 1250 744605566 744605579
    0x506090d0206070305070c0e0f0105090f1303050f04030b010f060309080a0507080904110304060b0405101802070b1315060302010905060d1b0314090613080a020c030624040501 77
    0xc0d0900240100030002d1904180f60052041e0b4007699440b50450044035203d41c074841042005452000084100100218241ca803030340a003849003690070014013040c0d9504402c040c0300c83c0340d0b0b0810340038004104040381424403000001e00c0614043c1c41010550f52410030b001c0d03805000d42c1e02c10800c00d40b90040c00c400003116101100c0b5101020304e0040c0d15003c16080c818580d00c20314900c150700c01d2514403001488007003c0081c0d4895070042008015914111081c80261201101c403008901e404030824004602019031078409c1d41e00c001c0c1c0050805426680307281d1981c00558912010f4442007400004110601c2c080b500541d090070300c1407061528541c000f0b84105228003a1611555003c50780c5a0344051300d0f4409244000b40030841819030103071440250081410181400d0301ba80724070000340068000144d424082e264038000c0e4103c1000c00d4450034215041281d00c1e00840c0240e6030982107a80c3c040144500840c41511804400e22086290a140b8041440c11a020340c0c140130041010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 744608066 1250 744606816 744606829
    0x30303090c0a17070b1308071710060b041a160609020306010b040308120402030312010f1d100306090c08070f181b0e040212010e060a0b1e13170a0606050609 69
    0x44170002169140c450340f6040040c1424042030f045041c05210b0480002190840102c1243c0c1041e040402e40340031942410240007a01c6482c000e08240c0d941c100010072066a40407610842d08100c081264144030300c071180c4001c80f0b0202c500a58507030b51100708400552806004960041400d240755a1419141d562501924000c0d00d00c2c50b1016010b4000086c01c0d5202842118450403841d0001020340d070711415039004d008194001d40301103c11184220707000c802944d9225020b984440b112003102403a42d903d078001f07070030005000c8a094411207070001c0d29036820006034000d002e0804150310b40300d05204042605a04180c81d6201180c2809969450103054102a043c0d070840d0b460182465109500803501912890b4880c0304601c0403400002146c030300306c52a19000d54002c440803c40a0341d01c81c010102400744003294284403070050040c3d000c030139003003004052818507061100b046555684e030440005040351680003150300000c0c1240100003044c4601c002502c812540756041240980219a8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 744609316 1250 744608066 744608069
    0x60a05010f020615120a0302071401030204030b0c031008030408030406030515090402010804050718020309010f0504020a0902091c0506040c09150605130e090307050d0f081303030902030303090c0a1707 88
    0x2804413507001184281c035440f07094021941400201c44d8500c40350f1800a581d91002d01c40d90b1901000402c120850358824000c40c1c0450b90491404403490f1070b108184030f150b6101400305502141c0141c000a51144180302500c01032064001840d107407498842d0140c01e03192700400482c02c03000314440c42c4040b65120421250066020320b042951503031146003d9151043c260402c04902c1400c0d4616194443e264008520404610b40240000769a281514041c0d910948000b907008543d40818030501000340e018020940c1c00801e12a50210384124544500c103131600d0548594100340c00700014840c26030143d200818001d2010000300000750100c104203803040c00f44a0801100084400c110641d40c074028003c5c1c8100c401d24021401c094240d2a40c0b50301044044400340940028050600e00454000014020686801c41c2070750383c0180b003181c0313901125801c42c213040d6035130f031400056107080018500c40c0d64031030b0060107000707034550412180c0b01240c1d102145004203004401007503400030070500c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 744610566 1250 744609316 744609331
    0xc030f09150e1519020c060a0e12030d140a0e06010302011d0a05030f06090d090b070305090d050d120b06041214190305030a0608031921090506060a05010f0206 70
    0xc15001c02c40740003542c115407551281c0b54512020070079107050380c03003c1c90b2a801900503400b1120f05214803018018103000d03c010050100744000040d06017810201c007500f094004507425030740340007040300c401001c903040100fa045112039000f00704401403807075119a0f540200c004d00103005a601d981c1c0001c1c50b116904001140d0034000703000c0e640d1184c449880d40b40140c04003c2c00d4030b80d03007220740000310350340d00c42181d11140511445000040c1c0034020f08018064032001928030389441c2032518142e0f61544001e08072500078040c0310b4980003140d401d20182d041704459030780300303030500c0500d0000c0002d48080e1100350303108a800300410000e8070048010184050361004801001c0000c0a10903400c4c0107a00b0700701c20038414904804010141d100000f1032007520074034020440c5c65100c0c0301c055035074052403005c4050206503c6480040e10f014408850b00c024070300207811a010030102c540019180814022202e5500810601280c0e1801a0002c0003801c02840c140303010144a0000a41e07424000d000e59 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 744611816 1250 744610566 744610577
    0xd120b032508070e0a1407091505071e0309060e030307171e0a170105030d0c060e01020406050d0b100c0b1b030f04060b010806060d0b0d120c030f0915 66
    0x101c40c049400c500800042c5010000c1d1450a6030301d0005a2118900b04ca20908aa262200d1241450720305c2c51030034061041c50b980e4844507030030000000c144c120340816120500000340540000208541d60800401110b5980050081038500d0054041100c40c0c0201041c0404400110203c2c1c400005a03040346401c1001c1403140c40c422041c046251141038410011256080841900503400100600d2603594540d00d1103031034003240c28182164042030040139803640012429040d0248034080c06980c090285200042060483c1245802c80e403055006101103840811500520240c0b4410412013138030a480c840c80f1030a81031402001150b101c0001091841d4200104030b41c041000d0503030039800e10342c4039410b0b542c1c102821002040c40c42228115441405c0042d600d10551099121310302a4101404090070300b020341381da640281c20b0150500d60481c0b4071040b054081062605441c00700ca11540b507147c101c1605060082022113000c0450040c0646106c007001460083c45103232048041c42d01e0324 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 744613066 1250 744611816 744611863
    0x20606060a12051b130f081c0503060f0a18050a0212010614070606030602042108031801110406180b0c12220e190b10030c0c060603050d120b03 63
    0x104101444141441e010066000c5017460340c1d010f14038031103800ea925404681e8046a5510300f8140d64a0258606040c041c0458040003207042c01a0040d41c1c00100051002104561132000b056000300c060740000500b8440d0700d40008017058922400ea0800d521a10541c038201c028400f0891030b00b03041c420340b0104803484643e441c0c480480029030754015407003e000c0c4180340e40e0741080c038040e4209020b020b802040c0c001038905505446881103000c190701158090865a504040c0380e103041c09140c0520b415500d9014205c0e011381044001c1c400f8190585421a000c003070610039440c008681e41050320044c008004a018400d0000303290301c4902110400035981d0307043d003200041650b01d051140e48a5224070b280100d02808007840c024400c80c0d6495040380700f056010358480c103482e00b021410ba00140002011092a0b21a402080840c010381c2001c02d40f061255503800100c0e01d86030b006654071f801007441c500741c190b44000c9480c2d02e0714036483c05009141c44440081d440d18850f1b150482e41c44c042c4100b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 744614316 1250 744613066 744613081
    0x9010b18091b0d051f0f020c0c06030a0e0f0109141f09081603030903031112010506070302251d090d0e1311091801120f0f0803010312020606060a1205 66
    0x151880351940502a00c9117180203050000c480480078100c1c0f0041030038140120709a00e414400d0300e8007145010010841002c6d180d090101c0d6900141c1121002038481d001035503400303010400a0059642d038400051101210304140c8404002071100c040d440d0401c0008642d54030740c551011404c0f0341349203800500c001003860405086d10681c65036a00c060f44000c004010301d905039111910b0f160282e2424080d000000113030032000d106200384074a5100125005015604200010300b070524800d00484000029444901309284884012800800c10341d4205114500070400c0300940d40e001040042401e00b8000402a11a80c6041d20081000f100c184403aa4594030410a1100c1c80d065100800000c0c07205000d800c42e82e03000c0c2c0156030181240c0140e04200c01840c0c4040c0f1304947c51100c01e400c900c009980e603072a880b040b111064400700803031030004002c950113000442c000c6104202006e00d0f40c003c07a60203810036400420b201e204910900c62804607a4010812086a5aa107000080d46a59444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 744615566 1250 744614316 744614329
    0x1905130e04050604020907020609100902040216081803010603020d020d022206030b180304030f0606050613080c030a02030c040c0908010c020705090108070501053009010b18091b 78
    0xd024004903003058003803206104000c02c140d03001e03500a0f1032440c03850340c800300141e94801081d42c4082450b40000c3d8040901d1b038243c0d00101000b88000e101503c0d004c08064101c0f129154048107446100c4001040400c02c0908040c403544e1b1b40b8142e00a210051454001406a49948201900034006d450a10b0119a0b842100020120b54000307224280750210134428001d0042c0d000441d030b25082c11000c40c00020314000519840c61803000250301d090304585e02c800b0301c825180021075809444040110b801d55403b030143c03020003003501d10203505502d01030421f468422011082e90080d0441035005026032030201c0e02406000303042c0d03008580c00d01d0708042152201000c1c1d20420055180803000d0041d1503000c11140c003160012070b04c7c1c814590701c1d0560b5945410071840b640b40401d0b000c00071805402000300c54507407075003444010701d0083c0b041c88480c101e8541c8101c81060650b5501c3e0b01400d00c42c40c2c8140c1c61810340283c00c00307800c4103141c0340f001c0c00d030303075003047c01d031100b2004240c03014481180d0f64003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 744616816 1250 744615566 744615569
    0x5090102120a0506041d0d260403021605090709051512090a05070510020d03110f0c0d1b0b040b09191209060c050c1e04090b150402190513 61
    0x4612018480c40c2250b500310050070282e94040c401d070706100d003080306c8080d988407482c9000b00503806800c030485101029903000c030030040c00e0740c54015203004503055502280e103090f1099009401074000c1c105411100038040c0c00c0b9800403885240311005006540b036004070078500740c8800b510f541e0701c81402c60030088002d0060812441c0365080550400842c00c40108522072640d10031011204116212002c103c03020548480002c0142c1c440380910000300c2c0b01e81c10842c4110300e5841c00c10314002c0804030b14501c80d03004588400b03c0382d20041000060660040c0b2995000c00318501517003188156a0b00c003500c1c2d110282c0003400c4108a103011071901d4409010910b40008455888040e52019107082c4440c2c07620b40c003a92003c00c4160500203880d074051800c102140b603201e00030b0842d22211508100c4500005a28861b0682c44244400d00c96199032041404141c000c00305000705261105640003036040c00900381d03000364014030030104079410b000e02060880083c0d0a003251201403040d0f090b41c110026 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 744618066 1250 744616816 744616837
    0x3070311040b0d0816020f0a09050411030303090705360106140a090501030e0a02060a02010b1309020a18090f030801172a060403151b020d0801030605090102 69
    0x5000001040100301403140d840c441054a051212081c4403040142981504001400c8844108560207040e40d0740b59200f40c100381300030036402e40d1440200102c1c08108540d00a4048207a40b1010700040c0400d00a080b50f140001720300031441c42c44c120b11031a07124505842418000d80030700c502c48070081d0130304a02c60501c030368a800c01441c80ea01d0010000d0b9283d828401c000120b480c0c100d0060300524101c01710b4100c40e41d141c540c1884245800c00440c01800c40c001180601c0c02081030500040ea100030003003044400a500100b40f40740070100b00000142414192131140b03140452142c0103072a815111030407a020302440450450f949180c1a02501145000802e0b000c1d110441a04064100e010706068404145526642c0d11030510102e64592010402008600d2011300305044d00e444c0d0300100301c8696000e4226070502d0b0380ca07601d0080c503603c005000c031281600d90b5404064103440300714100e10511103200402c034440d9080409443c007e0306000140c00d0544507030004012201c02d4044500700000e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 744619316 1250 744618066 744618073
    0xc01230c01110918010302010e09070203071212061d0c0a020304030507030f2a0b090438222703090501080903041d0601020a02031e010c0f1e090503 65
    0x901c070310200c2d80340d03120000d924403e81e0701241d2200e225821440f024180d07039040c0c5507030112190340400c21100d240b008015404510040104c42c00003144070000c0614039181e9141c02d0740c0341e1503501c101e03c00c2c1d4840390403801501c2c061001d241e4050620140645d006050604925514456207a04074114070564201616510031005c000041112002000500d640a0458100c83c2400141e5030884008019090a030540c41340b201400050b0506000f41841d46000b0400182c41070b107468000580c00141034100b0781003849242680407507005641d41c0d003400704116520203404030100e22040b41ca110309550300d880140d84460650001c004c0b484143c446591005100040b000640743c01000b0308042d008580c0050652030101e024100008103031003c0e158a140b1864040130348a1000d4182980200400d0462080c1c031011005610240045101041840f038281c0e07503280e03a0405542074440e80d81001040029001d140b440c202c0d40165403056286688000c84002a824402164064003d40005500d0300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 744620566 1250 744619316 744619331
    0xa0f02010c0203160e0f4503070203120f03071404030c15090f0503030405040519110c0d0509010807120f06080c03101a0d0c0306020d1a030c01230c01 66
    0x105240400c980c44402030500c95038520325610076169003505c0031010310b80d04031400d042d000c2d02214040a4880c0311140301d061f41c0c012002c41018003100d080501d05540000841006500b0244080c04044854600041c9480342110b040b002601c0010414410880340075a000c29075004503084800954101324888041a01c4250303035160306404075650307000f281d4041d2001901100d1524802c0480354020003550400e45000180406840c00900d072034008001103144002c01c00d500c0c41007424610b101d00d4010344507990a070069140040540040061080500291941d6a80017444c103500c046540303400400b4540c0c1e0780310300c2d01500010b00035506140c20800c01083c285030028001c050010200d049030030604141c403032841154444e90002d4211502d24101205a04001c0300c007450b0715114186203510300c0d68039101c001c100d0300301d500000182c0345c407020f0b0310510b903040c8a081c81c090403046003d0840d05451100207000000508280c0d03d00c1011000c0708000e244100054454080005000380200c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 744621816 1250 744620566 744620593
    0x930080a02030d2c0c0105030c0a180608060114181002011b3b1002030c15041a060f0909030d060305030a080903031003150906140f180a0f02010c0203 66
    0x14803035040c803003a0411240c0130b00341910380000d25881246042c0c41e401d256440d40203038180154071200d400010300645010003c1c2c0c00c1c40c00a0a00c00619640d501c80c0c4050920750001000d0701103000000640c0d100c10b0020032507210100b821104103501c11200f400807031102003001c2e40034018003000420300da40e804d00180300c8103400c03a182074520012000004040c0507550340a0041c44852560281d81c5001c492203100d0506003609464210380d1903004503414201902c9200f894540008d4044030b0440c0400203010030448440d0b0b0340000513680344505115450540701246420533980105440340c100f1034041045000c042c012284414002041481410b480e030420039540d034811070300c80c0001846500004d02c40340c004020350380220b0554158905403407a544586402200c10110500d00c56a90044480000c42502c194030401624010144080c541406020340d449002044e6981c01e00c030412010f01888404180b615801d5401079a510001c03a150004950240b01a00001d406218490050382d05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 744623066 1250 744621816 744621851
    0x818011b0b070e01110604020409110a06050a02011104380c0601050f03061312090906080a0c0806070e0d0f0b07020f010b010e01050a0f0314070930080a02030d 70
    0x51a000d448110184410900440d69211420403045d0b550308228045001032a0580000d4017607030080176500e00351741c22140081c000f040c4562024011900000d0b0f08010f054080c01907503044d1b400012514106031404156600c454540000c0d8004405640031519111600c09623040c400f00c140001d460b19500c80d40d03c004c2d5030f0034083c014240f16200e01d298a182c00e10b8001000c038862418510b03021029019590340c0420200b08030318040900c04038100c0460078006030b104210080c41044000c1a05c8980c0382000b5602015681001500340c21200c00c00040d2070b04500c11854941051307400194024082c20003c602507000100201503410540902c00806c0d400170b04040c01c45520402008907541900040d40c0b07000303164460b1808181c0070b0050750070312406010664141d0798103040c0420085520262840d407036000300c8904010690420050010008111400c021000488090320051045d0191800f4940103001e00400301040012621501e510034020b1700c02c13001c3c00031000c0c03040001100d2030139403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 744624316 1250 744623066 744623071
    0x1e1219050c040207050a020904030e19030b0a0908040b071502040f0303080c1206042c1e0601051e0111010203240d0f1b05120d080907030818011b0b 65
    0x400c0d128080340381109260500c03c840e8101d44c07100041840062603805d12042d04c000800070b82c00c0c0b2422010b142e083d92514210301404281a4070030312110760852820928550015200d00703a400c1c684003190700021410b800311401d454a05c2d2515132210a03d2a04c000c03242c01032244444154004500010918400b1403881e050b079229884825550f07440d60a28029401001000c0c016030390410041209401d00e90700482490b0140c4130150122555504168007490100917100e100f60f100b00480603c40510b10300504c0d031946400d000c2c2030b00754541000101400061140c01581030307142c0c1a41d04803603004900110021018000a64881c84d10803103121707156104a480c07804a2000207845002890041d0319102081d074800c1100e484000d198844168007070000300e4400301145280c83c0800c050340d415103840c248512150040007100c80048000f0209603001c0c01202d81544602010700004041c00180d40c030003c28074608120014036100120b83c000084074061041c80c09030480b02d4280001c2c2e012070351 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 744625566 1250 744624316 744624323
    0x41107051b0301110c0712060603050a050c1e030a0b0709031e020f0105070209180102040906030605090c0118060f120618050702160b030c0c010510060201140103021e1219 75
    0x199012001d03142064405c10703594a003030350414a02800821048078121070031900480c0f002680340d403260380b50781c980703055601d081e54154880442c14a0502c0d01120305000b110540c4000034000007a00040f0b6606c0e05179504c02051050203000003481144134000c540c0c02150410301c0506910303e0314400034611070f1682c00c2617018940d4115840403d5000d503003100c40d5143c4c05441c4018981d903c40301c09464080809035603910355001c00c000200f111243c059100551b0083c040080c607814100005490414400c2907141842180d07900c102c100d02d030070800072080340e0281c100250b801d01c44807021103030303401c240e14801940d07440c107100400d040d0504c0904040c1c05c5846c80f01005141ca4006040e40d4508079151240042520a5014800d14502c0805140c04c80008461301c0d003401e065060309402d41d90b0488403000c1008034402c08010040e82400340b0180400f8460703103410f0950658012400c0d00ca01c0c401d071001c1c1e101d150842c03000729844902d02204819000c00070b48001c03e40812500d22625001002078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 744626816 1250 744625566 744625571
    0x1d0a030c08060109091a060409150f060e0606160303091a04060c03050f01060507060204090515090c18040b01020c030601030507061d0303070201141b031b0615041107051b0301 77
    0x1242a00c84d07440b584441e290810318042051185501c1c0b00c49200006009a0300917444150240010350740070200f8540201aa00c00701e88103c0050040c41102c25076800f1031210382c010780c24407e140e00c0342d108403003001c1049141c99012282e1410140c010380f0300400028111500d01c0034400d0b803141514a01405541b0a00d018441c03034601110440a8950640e800d100c1ca8036038034010824140948000d102031031080801508141e40c030b9034088225030f021105d91901c0381c0c000200f501c80d481c018024a0f400751600303140170b081c181c0f034202200c80780d0084841c2600583e038400311580395078020008015020002021180b4039078482c6441d5460f1141e9101d60380100307110312070401a04030140c0704402502c201800441c04d207903c0f5001140d44248076852014040001c0040e0700b81807449420308a06950550000c5a84080340d5640c105120343c4006102c80a0b042001403003201d00c410309621109080481c0c01084000070000c480c1000e00ca2160001c12030310618410000d401900070125070280001c40c002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 744628066 1250 744626816 744626819
    0x1051606091709180703270303060f0303120b0f10020c030609010c0804290106020a031b030e0405060303040b0c151e01060f03020f040602010f06090e0c011d0a030c080601 75
    0x90380700d00541c1000fa60142e08241c0450f14039515071019a4407030307018507011940c500040c212404008018601503080c6000d620b545043c1a014001c5100030002d256082c101d00380385403401000d08500c090300111040d00d801a645036a83d030410301c0500590300030000d61045020f100040e5031100f024081034000d020b07035030000f803110b80d040c13280c1d00300c40740b00351158202c964803565407100142c075203644d682600300003e5482810f040405400c0c0c0c007170705054000b45408501c50401030b040400010038a80c200300351250031000264810743c070314030801d0184c4010489844020019055001341e41001c01c4800c2c002c02c0c60460701e1000039074280800ca0304800c451050b26800b0351a41e8199101c00b5848105c2c00600040020354400c1c518880d070f200d15461f006040c0120317006031002c0340d030203a440040103030744420003100400703e50b03c81e002c010400507404001d48114400c42680702c0100200e07450500c0000d4422008416080c40c1c0310899220042c40c09a48940b00e1a103012448454000c9807203074482c02e0f00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 744629316 1250 744628066 744628103
    0x180307090221100503030d0504020604030f0506010914010b07081c0c031517150717040c170604031202090d150e1203070c2009071d0607020d060b0105160609 69
    0x4003041a0b800217805507281401684480d400341c5000380040307801000802c4000045840502c070b0080a502c40e501800d0507525104110b81510000f0202c2091f0510301001003220081075008c641c1c4442e13020780ea0729102d00e10f1100c56490382c0290010384080310b08144030740181c50382c19132001c101c1e003200c14050b004980d141d01280c2c56a0b00220314a5506a0000c8031655140f11810362055100c07180d03240154264003102e0390410143d0050310115400c402c1800144104002c40c109002c4c07003113101000b4011480c05440080c400918514140309440d800142886c05407620b01220702c0702034121001e09400c1682c108000020032295130340c0d0b00701d4082c00d20704802400b03a40007124010555595910b0f00c00d84c20380c8030031614120349086100c6002040041061a07164007000c94400c5d415500d0303544103074024035451181422550482c61003448200100001651608131010300d03980c11500005030341204c040140c0c1c1c580701e48001468002080b44c0d407a001c01c815900410402c92041ca04018146210b91 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 744630566 1250 744629316 744629341
    0x80604020d0609060f052406090607170d0506010923061e16122d0c0615150203040810050a0e071203031a030307030f020c060c01090215040b180307090221 68
    0x87c541c04202085407403d00c0c5031440280100754050140320070303281910601c1c010307164440c5003035070b9403146c43c1c004004056030401c2200d002441d14000c020000490340c48012014010350885910450001c01d0901090005040d00d4032103003c807810312940d40700c2c144e17849912040d02e62001c076818100b015038031061038030a0009140400201002602c400c99410b60600b9011414040d8420030003d0a044408900309001d00e881140c0c0045230343c01d082d81042e18440b820300d81c131000c540c02c0d98420803040200e44400200d172440d40400040c0061203885005014020300150040358102d440784074070120b11034041d40c40f02801a40f181d1401c2012610000c110020000408080766060304107000e1000464002d50070341038540320f035106560182807624005801c0307400c082001080c580d034030b044103000c60030440360792407002c03c4201000b42041d180407051103040c890b03c00c2101540042040d0b120380e41c0c4080142402400c04442d0541d2a4440302800d00700800c02c0d1140e080c41d4920803008956402d5020303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 744631816 1250 744630566 744630631
    0x81204151107090f02070b1f050a0b160c0807060504180504110f030703140706020f0309030307031b0605150108060103060303050301051915030204030209070207080604020d0609060f05 81
    0xc0c0040c103540ca140040340b6000740f21400410780b1450b000c106d50b45c0059800b549440c410040d814031070750090039103000b0741c181110a400c05801148a0b0b101403011001e4041074404040d010a401e03182c140c024617041441090503480380d0f40c184907043d00401c00e1038003c400f400544100d41c12155001c0b141e566142c00340c44050710003502d00c44003244c03034011070300340411000c006a501404961149079640c0d204105411595035860254004040c2440281d50602c01d115407141200000d60511810000180e200c0c455094000c0a008002601e03040d0105c0f000c5440c0392250304408204045e29105080c0e48882c01c0151368180000c928100080e051340c001d204200c252038040d500e0328216801c0c6000d2048580404c9001e0f105240707003460000d0004008120ba0036000503540e00580c4543c5140f05001c81c1e02e0014000c0c5e415500aa43c00740000310000038503036400350701215070001c0d02003103003003510082480300310150000f824072501c01052000307604154050810302a0413018070f000001c500d1880f0030704 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 744633066 1250 744631816 744631847
    0xd02160b0a090f0f140706022104030b0f060a0305010513020103060e040b04060b19140301060b2805090603090c09070212040b0306011404030c05011206080c090406020408120415 78
    0x10510f0f00049080c094401c07a49031712507100000c9021814a0080c940340c4c46600450042e44007121508561030f40d096048551002141305034101030842e666080000801080140d00141c1840012a69902e80341c6810007150418007c218600303010f409200c81140c5040f0980c0070070b040400001e031140b8241c6442e4419600846214031a03100e030350300e4102030203940c14021341c011510000c102480300d070708690a000b040503412040300d4042090038113003590800da020218005091048c03090049a0a0300d141d03407200304440e00085030010b444107030f41394010503070040c0c3c0281d004010002c41000000b0204c56422040700d100000390b5a07600101d94811640000800000041c8402c0142209480203190004014104a00c0c44810510840400c3c3c001d62b200b6118402603402c10021540c000300b0203242089000d8003800180c0c1499180e40d80e980a04025501030006031002030309100090b8162005000c2d10340c00c0d20721002800c02245003d4215006108200401000390000d03039010b03c00d80291410b5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 744634316 1250 744633066 744633083
    0x271b05150304030c051c110c010804031d0414090d02060906240f0301020705030a0e0d0b01051306050909010c27170f1204030519021c02060d02160b0a09 67
    0x101c60f03404881d4100b4807032084440d440351201850b0025030320003243c40840c0039545c0d0020740b840302c000381030300d05401c4c07000c054184907540f405d01022030b9102d1001a42c03d1031040b1002040c50503800854018075040d4544031010310f0701c0c414060061030106108000181a9080302c040d512901001034640000343c2e0208103e444506050f074404075541d03040040358400620b0003600780e04500c04242079900032a8200d0307003500001907041da04c0d50000c640e00301042042d5107405491619a5a8189005042c0036891060026402622203101d40740c001c00c0c0503081c040c1c10501142004d882040c080d002d040c98500c081920f000005440d12035052a00d0700da01c03805900703001914a8005207115568980c103208089004461856150920401c807201368a10454051990395185060071307030900300010f042c051441000300e40301025a4030b8402c0d40503000c800c03130302805029143e440041c04a02c107051740000004c1c00803851020110702001c40c408058040c100b22855542e4052014023191803e0364000e02c02c62 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 744635566 1250 744634316 744634321
    0x5010605090f030309030105040305030103050615031b0d020d1101030f0212310b040b0106050c100203090a0b0108010507140c0a030c060b09100609080c13271b051503 73
    0x9072000d42d5184010700541580e10700004040480d081d16000c907010782c0480e000100410070080104542503111015151308158031803a00000303500c03440503102201c0060368a0f80c0c400351541d900110b510307220754000d103038544924061501c20340600d058680580441d01d0032a40395003c03009802254601120540c200240b980c0f10050700304505500004000a8450185400714030b0a807600014411401107109100c1481c146c60201602c80d0705800071001c01030184100b000010f4002540d00000d0100c50340503032607546a54615281200040001d001c000300300c000041c0c800c406601c018010101603407401011603001289580c1ba00c00ea055661040c3e2200f4440c03004203205054100516102d08404070301400058006001b515003510b000c4104808507400300001e0781c05c041040d00410001002c1d00b58201c8490002d0b8102c81c0183c10240d5080d01c0f20040380051501000304101e041d50381e6024a8200940c2c241002c0b004003041c0c45050110710500c002c1364601d4040140c00c0341c0b040c520362192441c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 744636816 1250 744635566 744635569
    0x703021807030204030807060f05010617070f020f011d010b10090303030c051207020f0606030f0c0d08120106121a0a0b09150c0c03010b040c0f14120a090b0a0501060509 74
    0x203200420340c20800d6403c2c0800710000d01081c008004841c020a0049980380d00c0288100459606034401018010a190b8541024460300760940e40482582000b40c603000c031100701a8106007401419074855480d020300e407142c0c200d00d1501201a009102c008011004000b400d00072090111400722011990f0300c801040000c0c030a8000d903e24489a10700031b820b25030000c07050460f03030000755500b0015030400400746600c42030801c41c2a034001400ca009020801170840c5541e2103e5120001e82e018441010f8103001384044001142c04e80f02203d15408401c0d039480500500c190350303801c540c8908a00b000301070407d8031800300120209000c01000018090301e082c41e00c5050b40c4c080460107401070001c1c01050709440c000c901904903c610500588110030f0f002d01023601311646501c1c094415880c041c1d070a003da540c41082c11240902c28181a0000d074240004482907001d899282d82041071000100000f04105030401a07000348a81000003140d15018507520a8880034019400060001d10041401c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 744638066 1250 744636816 744636859
    0x70b090102041e03120e0a0902070f021207081e10020c010b0406150908010525170412140307020a080f040b040e01031b0b031303032417070302 63
    0x4182104001440d00d642d440454200202c40030b5003102d2001c00000400501500010b4072121407003501d00060703185903020014144507581c0c0911007103281e021820b07000b080303107410032030064a40007808503545c5c41c0c0500070256074040c1381c000d4022500810101d003280c11003500020b15100c4200e8050244080d000e0241b4000b5001700051955548d00c4090b02c1d00940c40d2072040c0c0000c5d00c1e08191000900540003009040d0380d07090b83c06114540c1c50001003003000b60409080740d4210001044040f5805540207088a400d003041040051004440b8140020070003010080c80d0101c0603074880310507041e06281c0d22003285c00100c809002503000103800c40c0000d094200100100c59055031058103198881c0f0081d5459003080d00200c25806c140d10052080c421405805c07810b1000031328084180504019032158640409401540398840446070081003601a40182d000151516071022140020810700e107003c45091040e0070440c000d010058000880104a00041d00d80181103040d00f111a02640c20a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 744639316 1250 744638066 744638071
    0x2c06010509150424050105040302010512060111030c0c041a010c0201120e12130506090d110a0302130f0f0e210405040e10050f01031a1902030702100b03070605070b 72
    0x192800188042d0703a42c3d0b40d105080d126213160103907801940318000607032040107454001c01d051080c14072003080180ea0000803201c0540300b40310382980303545070440180c0b1103668003410400d5600010800f044120030029a8606010b000c03903080c0700c1103403402000d14142441020107030000c0c101180080c05540102d00441c010b4545030000250140701d0b031242e9041c003100909a00c0750440000c1d000040a0030081030340060401250704914100003070703000951289080c50000c1031034400502c4580b055558170030100003560041e0640e0801007001495000800f066901241c000e40303084514130413510907100f2426032806000003400c02c0c4a000c504280b0194501c103070f0600e441d408010115440e01c4a02406c41c040c0c041d28000c2000000c911030040176584000e00700000075108400410124181e607004412020207040407503016101c0d4180100060398080e12039003003500001c20f00884a5000421441c0006055810486a0620f030b007015222841440341d040020024450440494400c070304241c5c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 744640566 1250 744639316 744639331
    0x50d120503040515130c09020307020d11070b030c07061d0705210708030c0f010c1b0305070f26181009080a05010c0e01052b09152c06010509 62
    0x110384c802000300d1500101421501c030030f0528500300320a41001045e200c44801b80c11074031429400c500c4c0c6924002c0d40c4002c0b14103548104000710011105560051000c41c1c00b82c1181c0d80040c1d034a2602401c02a52079100390400c80e031403031400004c440c0041d0344e00500e604045519000e00b4885140c041000107030f104044130054a4295404003a10800042040000801010b00590f80750745c01520740310708142c54901c0801e61a410004480e181d42d41c08245103000c507803442c0440d0300313400250404807003238012007100400c030f080250040c10034803911100403007003544903004161400e40c4006e0440c3c864010484071924242404914401c10b00c0c1002048415040c140b43c1203076655a5002c05510317241c0410015100c40c0d40d40c00303109601d50b6102c01c0e0b5030514502803e000b4501000c01d6212040560b0440c0200d1201841c07013240009000180c00c40461190001c0d451005240da6054400050000328002c030070a01001441c030f0302c005a101c61000b001c0104c40094060f41e8a4042402001c5d80c0042c043c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 744641816 1250 744640566 744640573
    0x219060b060f0d06031b15180b030703090c050102010605030a0803131a0613060501020d0311040b0a0918051e07090306090b0a0c0503060d110607020312070606050d1205030405 77
    0xc080d50080100a000d60b40e01e03c19020842d00e20310b0070038061300002802c02da09034260000f4203004050b48540b80c074400f020a850b141e1300810440031040b4503100c482d0407502c5506000030a000540b64180c00c07090b4024041c000840c0e0640da1400107a00700c030700510445805130400b1108801251001c005503602a00880a8032000c01590303480008203401e0000314041401a4000c1c0701d42d5050940d110340802140380c40800c44c0c2410b0000107961480300e00190810162240c48503a80102e1a00643d0020301640910686800d00807202901a0031a0b000d0f24042c0b440a11038003038954201c2c0603440c0241031400050300210f00040b00740c40e11090040c029004c2c48402e80c0000005000c9110300843c0c0c0d4020103480715203085c052083c105a4181c0c1100804000050060042c20b81e5031f0b01d90681d141c0d0b80071800e054903107081d070007080c2c5900902801a42c14041d2039001d0061095490040c03030350500c9400e007000510b4440c0708000d031810b45540080d04801442550620b000d014a00454016026078202e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 744643066 1250 744641816 744641827
    0x7092706090b16091a0313030c020a0f0801150b220803040b030402040524041a0a0f060206010e0705040e0606072420090f0105041d160219060b06 64
    0x8290080500399506540300226052016005500202c4a0040c0c00c402041015a40c51504185c01d103000203000101041c110004000802d40200c80c003555140c1d01800490001c0d80e51410390380b81d0603142c8140b1045500b010280400e20741507010100035a0364102d603450520000004017900803540035011009250509000300780c0d910b041026000406401c41650b55901e45481400107856014203120350400a00d41c00c1c1460304680001882402e000b52800203206130b0080c0402c2103034100f86c0440e9044800100c0c0820500c1100c078259042c0c0b00e40f50211952071760303140e0584e00485811210503000540621040c80f003102c4514455402c80002001d55080035259190001001d80165400355480c412010348800544903028007410300c070b04a844a002c44019480303c0300207204441d0f601d4421070f008100c0d140307240e000d01c0958025002c3d1072210480b2801d07154440c40c0910040d01c0402070030806404400003079100142644229080c18000710041c0307d02d0b544ca4001d06038500907968840802d100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 744644316 1250 744643066 744643073
    0x1030b16050d0e1b0315060108270a02010318030c060203100e13021509150d021902030d1109010c1704081615030b0a0605030901020702060403030c03020709270609 72
    0x110f940100e04440582981e80d2080400c6110807000c0d0000c44c041d0700411040b0300040c42c1011310f10b42c890300c20300300408aa52a4800142c0d450b081c0c10781d54040c00315103a080c3d21904000201c0e0103d1500c00e803000c01c68021140e504100092840c01c000340043d69802ca100000b0306150061508220601801c134101d90702c80c0303040000560100c0b0450552a400020031040d0320f00f001c0c03032101000d40074219038540300170ba41c0811800c03c0b2002071116407801c00280401e4605003541162075410816164031030403c03000790300075100d5001c201d00c0307003c8078108665044c02c10015800c070f6440000503180c20924030400d03900c0c0300195030f480c41d142d005140148800101c2c1c030802e2005c000e807604e501c129140007506000c0801c91b42400d032000c170800c252402c666a11240c507500641002c0d6241414026241e40c1c0d515007180c0a0310910740020740161010600004046d0454100440707107100360251201d0907105c0d0049000c072074009a1990950300308a101d160102d0a4208440b00a4010440411405440d46 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 744645566 1250 744644316 744644321
    0x30618020d0b040614060f0d1712011a040b1207020a0c060f1805150c10060902092d10020f031206031c0801060503150a0803030a0b0901030b16050d 65
    0x20001c1d1041103003031081004000b82c3c0c1c0700304c5207041d0074201c0040e00d0381840710114481016401f2030354000c0c040710a2400a004200405401e04a071401005684c0c40d05984101c0312038a0a11511109910441c2280c200c50ba4280c295015514008209400c01000b05a21184644094480c3e002d50049000080100b074004580c0c07000ba1a06454403c461030301c02400404298100b64181d102d000003413010700107651a040c541d1f87c07205c42c9905a5031640c0510383d05608094904601c481d54600d00480000e550b044c603005800094421140d941140002c0201e0110035403042c418518859442d000380407081c9402c88000030540310520440302036020200800380346034840103801c880d002107a0308229481c6070070007107070070300361b04a071040380024011a002511015041c00b07140f0902a011001410600c201d2511800b2900000c00e8600c1081c0d0ba11220743d1294000e0703c410380c40f242080c1400d116030400c000d10904803640103d26039402c2c0d03540070010000b0420040000108002000f10026144050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 744646816 1250 744645566 744645589
    0x60302011b0b2202090103030509030c010809060c070317010807050a06032a0318060f1b14030714070309050f060412060f150f1d0103080901030504020a08030a0206040c0506120103061802 82
    0x2609c58a40e00d810300d1081501e0400400d821904010491080003180307000400d1654000000441054654205240540350a4048121420308011100001074102c0c400511307c3c040f5003080c0e5284a011f0b0302c68200b00c041c1c91040003440c0c4640315050010060a214940403055981113247c0060010101100d034240399001e203005541e42070702d55289002071103003407240f020030070300e101c44400c0201c4136008050f2038a207e01c030240041420200c00034507041d0140540d0039080b16805d41341350303540e0300b50302e00604209101e005250044d0114100700405080c11000c540c142d8003c510300345200965a514940642410b556a50181d6100c81192200300071186003200507211004400c0f07019401c1c100708204001040c1e1074440d00607071401c010400700d0441401c44154060a18001c038840e80c0d10700104059000940c41006507100000b420344580780c0c0400d40e5270240e44620750b082c0185907150100865030080520001840d500c09004000003001640041c3c0703401085d141540240829400054540200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 744648066 1250 744646816 744646823
    0x3032802070b0613020301060c08030a200705010b0303040b0d0504050102070b0903070b06010c0b04260d0b1e09060d110405181501060206060d1505070201060302011b0b2202090103 79
    0x10302c1030060502e446803800004648080c411401d56141c008020028003007140080e0000c0c0c40080030074044405030f044003840070300c0390b17010103503400500283c28401d42c0300c0402500c455103004040807035441d012084a0072201c400b81114100401c010740c01c8010203029208686949d82000480001600e08440300d1041002c2c0d0045c7d9110540ca0501e500781d003d00410700ba04000c01c8410130360000b1040c1c1355094109400041c60804180301c1d450105030040d00c0340d1000d8000030003280400141c0006c0d0002c0c40e4894099503110480c500045403048003c0082450b0385d40324014030001112400c084080c800b0860244040c00072403000b0801090850750143c03940881c00d1500d203100550304d5010409802c2c0c0c045009180303c0c95616102c4005d440d600302418940c030404e40c0b90903440c2070060420542c1c00d1100d400000b000542400c15001e40200300500c800c80c00300d100c2c103035184904000c43e0211010f035038000020107036582e82c40a83c41000d2507040c1a0106000c15051f00c4400b688500e61568080c40c803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 744649316 1250 744648066 744648083
    0x201060602060705070b0f07020a0b0c0a030c080105031002030910020c030d0c0c0507031101020a050105240a0b0414010504121b05040c020309060702060915031b0a020303280207 78
    0x41940007800e01100503e400180081004504001013075816800c1d8407030484480c5040c50303110244c0407814080555030240000316a8014004031070704100050a00c1c05154400304031400340c040d4180d82c01c02c424850319034980c2180d2460210000287c000f9540804440180d915070b5089100c201c00302c1e0000b42c02c1d13002d01e500102d06400201080d1043c0b00d500d080c9810b00072a24402c03556203a644101c5400010048668407001d1210341c0d000300034100b40298000000d120f2450484450708040d1100c52030210700040c014903203020703400d10400042c25036031a13404461405050170703d04684480340038405410040c04210024529024a0002c0f110510541031040c0b00350850303480c8039550f8465088944941c0c0b404c9240c95040c0c3d00001141c941c0d11083d1015522008640009059401014105d0b03400489508070301800560b500d0055200f00b002d015400502c0340113503014101c40c000d2240e82c4c00560300800200d41d061608008064240c050901e88074030001e8001d56a2082c3e0300602c10031601042c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 744650566 1250 744649316 744649319
    0x5090a1401051501030e1b01031104090209040b120d0f0903020a1701051501020d030b13060e0103171e07150c11070506070b010b03090307050a110118050f010f021903020106 76
    0x1120f80714400b040100c2440d050284409200d840d5071191f008030000320011008a148035a140d002c1c1d08129075018168410075100c1d1b68549090001c5c2d40080c8034248a980740041e5141e162600c403441d44401221100241080348240c54151002d4401c003041c2000e001051030000010303604ca50b20503001c0d00307035100f801100210b0a20001d003540e01c06066022020042d4985400517640010760500ca04618900441d00f0a504404143c0d45c005854480407054140000800e0039142c040c402d80c1268401c803500220280200700d003030018080e00420495048040741c0500c487e041c030300c000d032081074052000c10016600c00c02c141b10894406103c804007007200b074001e0710120b02c0d083c402c3c0c900501003620202d141c070b1160395411200701e205005a4015000101c00b00d14240b901300140d9240c00d80c80000c40342d001b181810411028490009840c1c0021402c195000b5185241399400e000c807040940142101c4003440015503507810124178010861051034005032a102c4074444000040b070013900002030f440d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 744651816 1250 744650566 744650581
    0x9030903060406060806092e0f0911030d05090a090b27070e01020f070905040c0306060f030b15010e010e040f090b010509090607020309060a05040b030a05090c011106040605090a140105 81
    0x40c00400380001a00448007031500015081c2070300002008140d001880231456244490041940140f00520189040060010040e01a0800904c1d2900b2422900700c3e41e80101c0c11610b40c0700d4407000320b4000c0c4582c05c2c20480200b0076000f11000c10002003419034005c40350b54180250458002165881c0000041485000ca412040503e0815401e00c050b2404804010f421951603c040c820001a550341c0e40004d001e020100b1082005580c1c01602484150394464204c40090084d00094a01c1c804240c0899440c003030044062007030004c1a104c92211030320802c0195224609043c07529000b43e100e030022040c1c51a03c0c8182e0b04400d106140c040110f5051006110040750020131100c484d038881d06c24000202c0d000000d8452660342160400d40c2d0f40c0c03c050044501d405035600400c40240c0100a00c240c0340079079004180302c0c2c21001c080b281d880781c0c00301c01190a032444001581d082e41020300802c01181094001503813010b050011503040141c5550340d590380840582405029941d5003081c881c81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 744653066 1250 744651816 744651823
    0x7030f0216060e0118110f06040807050102010b01031a0405060a1a0408060f040f0b2a0705010f0b01091a1908041202060c12100b040b070c0b04060c0b090309030604060608 75
    0xd4240ca8000c1000c0242a009080c071490100170150494034520a2150b55945001c1d00c00502d8902400c2c07207407119510313080d403540c8000030b00031f5034059403c10f007040078994804c7c070680d510140500c1d11899262000b03000e002c003c0101400f59500950090000705143d0454045002e4070960351101617a103900d8411500e0910308050401c0c45c0820640b0140800304ea240d46a154105801032500706e079640310045050b141c414103848290f00b0161120021150050b10030151915a024000a1009091200780382c412100b4101c0e400e408161499810f10003c00060031200000d014010694038241000744504242b0992180710400100000100300800100ca204045005090300003048181064143d03a8468090700c4111035404185500162002c09480c40c40d03801002c900d2005641c0c0c0d5103905803141940e02854003651b080303000c030000042242e0401c08807000c0b51071580d205540c542159a4070303528103030041c0001c27035188000e101140d81a90305110281c020f9214001c00a0700702d00d070201103400d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 744654316 1250 744653066 744653081
    0xa020726060c03010e010e0c07060507090e06030f072108040311150309100c02240702010c0206060f0609010519030603150e0d03020d24031e120807030f021606 70
    0x1802d030140010008050403458590544400b048040c000f550b5100382000a40034a00c80607000c0c42c10f14051100f05c6e1303000303c1c0180c2501c080442911107540c5410516554000c001b07411312950344200340400c0f500d058030034200f00140c241001e100004125841c0c0b4200754205420a440d0a40e030509040264a800e610a007409003903810302030b066140140b502d98542d1080411880165120036450307620720310038080e07482c40110070030034030040200b505125401814125149405903107480000035110f0300029286201c3d00c0c0041c142d0003800f0719181440700507001105624103200003030007159031955503403100006120003550009aa1403950030148421303917248564400051401a03500348010001c42d089030901201c0c100035a03942c5106038040c0050011100c024941e044100b07103944201003c41701c0c0011a4000c40c1710150742500c0c090a0a140c0109040040c400c61140d41200c4926000c0e48003207521820b1818005100d1112140c840700b41da116903000c41850104058102c108403070703481580d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 744655566 1250 744654316 744654331
    0x5010e07060f120f021207111014011403070312050702030d030612020d11031515040b0102071a1213050f010b1507020a0518010603050105010f0507080a02072606 71
    0x1194003103814003070b05100100c80328140c60fa4070758404029803c07594049684150191302d60100f02e01c0e064000425042c03c2220591070350003a0170034a500c04559001d44c0320441d04c04100060345910741a507407034550314441c0d070f02501402030715800000300d0030340306118201074016115030f640c514482c0b04041c10290b4101e404c5050503c1c0400c1400584d2210030200c081a1f410303a00d8107401062410220340e6104c028110a505101d05420070010051078240320b80038510000080503825061020402175401c14541c0c0c80c01a80018010003000b012083c80c1000c007603000c103100b407a05040071040401d00004650042914840110702010840208512064a40d0b400c0007046115015030000d2440e841c03010007030880c50f00c0880c501055641e00300e0401e000702402810004012101945600440000d10481e8003091070900005025401202018105c121998030035151094507582c009aa03003007030f400300d41140716412000c104034002c1c0d028280c0900b50914240c060b00c088c00c0440d490088010440d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 744656816 1250 744655566 744655577
    0x90e01051909050703141003020a0503030a0c0803041b03080a18080d0c110a03060905120f0702090406140708100b0712050c100f0605090108010902090a1a0d05010e0706 74
    0x6190007030140a8a800d442000401140e01d44030054201c020380121601d03001c00da4410003c0c80a40c1d03801010341801c503442507400384c132500d50310010140c40e402980e5682c40420420310300c1100068441c801154442c2c0b05001c1e0480f10300e028402100b01074865007045509850000d6241c52a42c3c120000d4160001007041118a250501000c1601c0384c104800c800240503580c4070707000800807183d4050290010280001001595074200031014001401013580e05e8014a000100c107041c035407044500369030000302032a00c6c6c10265824440b00d644010000e8502d40c1d5a040140407940150340080c4c0646529650350105080a2046150068181d0303c1403c3c082d40c01c01503d40094580030150b100b440113820314680f100c64842440d400c1210800d241c0d02c0e254645410015510003a0340203070291901615a0030a5030b03203c1c00240d088940400e0043c0d4080340c1d901c00107002616a400c0320030340142c85089107120400c6940443c4144110b03142c11286a51200b42c030001e52401003001784002c01d40303884e21 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 744658066 1250 744656816 744656839
    0x509090303071d0d05101b0507030509090c071415011e030f0501060513022d1b0f1006080c01051911070b0f03040318050a09051f06090e0105 62
    0x900b5500082c0b07000704901c11441c24840942d51004120344103950170609641541e100700e0644c00003080c089a210003048046070007905201d11070016142e1195240e1505490f0064030402c00401d44c0004280800010080000900262960035840c003001c650340001e01d64248400340d40e91424405030800000000709103400340c0b0101150101c101226080180d141451103507003042805000f260704816044100f612240510110a030300425600c0e003680712102000c060b28802c60300b0004490019401c04105111802c108001e040303040c0e004100f200111020f07484d00c2c01c40d0905101400001f2180965294410401040d0a01042403070000c00d03e020761501032039210000010403100108420012080f040e513042003810444da81c00b804000c5045030720341e4120000300002e0361007100c0440000310044080c841c0e0342c401c42c1554043c1c0b02e0003030201c1010790030011454024940100150a84010074106170070480e2240c4c030220241c0119661440c1031350428401614502c41070b8016030289485a45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 744659316 1250 744658066 744658081
    0x20a080622050c070b01030c0315150303030b0d0b0a02091302120f0403090f1203030b0f1c03030b09010b03070215040203100e0a14030405040b06040803070228030602040509090303 79
    0x240c1039a1084024000500383c85000e4422070a020b214001407400c13503100004420b02030104041d50442c0d20680c5a252051400b000c0c03c01610100500003881080710001840000d0003508846107001c009490007d91341d003640c44488280c0c034280c5446c18155800240c221150a210315500b000c5180c46c5015480c1400080e40801603e0700245000259240c010120301054442c0300c0d07103002008200c200c2850300c0e440b0003603009000820300040b8080380c60102c06000c18108035541801c42c0d68000c01003081b1104002c10016040c1e80300c0301c01c8040641c1ca42d00c00c2d40e0fa55031209540e0207041031440d0315860345050301020345800d5410004541c00d0300d84804010050790000f9031038258010b841c0000c00c00c142d00c0d00582e407501c20a06402801c1c0010366411200680000020744100c0f44112401c3c81040894810300c81c65204034000c50103103030001c0203943c1c05802c0c4a1a00c44440c2e012030f4420785510f8011280102881090700125000e0b0b4000404020350310b08040340c250006168405185141420003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 744660566 1250 744659316 744659359
    0x3090c010804021c02030f06040b070305160206011505120a0f20040b0d0f020714011506021b06070c270b0f09040203031c051f03031409150a03020a0806 67
    0x10161290313060019201c0e0b0464400307000d201c0d06004280b040f03a0780c90915140c102e40004003215407100181c070f003000141d401504240180e40c01040380c0c001c0d003902d90030319003480c50742e9010030b0a41c030610008018909414168080030341c450004d4260016039920761078481e5055070400f00c42c2841d401c1c10031030180a080035031400c64040321100b41149a6490380540a40301070400e001041c0f00c6d051020440b80e0502c0303610311403458420700210080042400640380c1e81d40f494098020100180d0010080d180300c54608440d890003400f0003010306041130401e55402184001c19040b0002c03101c406440d03a0100c00c4000c01040d085003040d507091200e0000c04000c00c2c001e11701c075030103548600c40b2040480e003952020b004071458025020050011031142405850180c9000d969110008401c00e05001c0110042150541666455942c45d8140d0421400d01401500308907400b40c0d004c0b01198900106031040e038002c00f05060b4644000d0b861768400e200117030000000070011401100c00e800300c22400c00c86030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 744661816 1250 744660566 744660589
    0x203010b0a1107050d0b1005100e04180813031101021903080615160c140603070c1b030309050301050702150c0d060b040303021e0a050c06030402041401090203090c01080402 76
    0x900d400c00d0b00c0e8001d20305003450710200da80142d820400f03e20099051104030b5500511842c221741611441d40ea1703074400d0080e405008850300002607580e0b0400305042c9810741000b00b2a4060350801d0f52040143d48134044141d02003618001221a0a0010001c2058000d13110000580c24000b402a0050004503030664001c3c9610003030070400039600007245680c1d040f400141240000d1a9039480e54100103c0350006200104181c58958403403000050315400d00d404803084640260006007151038207001900c801141a030212003101d02900748003025081c1c2d8190100460090b541d040901d03203440185821110081d214008540182c030504c00e00d030403a01e60090f004442e0030314480e544d036655201c1200808691b00200115a0001000402c1c981d0000b0360458420440b1a2070440f03a0440480541c1d403000c0802c0140203420240001c660341c40e245010b1030340280003030404500c00c51040320981c1900001d82225044036400b00600c44020030402c9544140b410a003040c0c2814140780e000100c805290 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 744663066 1250 744661816 744661837
    0x20f01080702030d0e0313091e110f0d0501090506010c050a170d06150f080103111c060c030e070501050f03062803052404031715120c040509010203010b 67
    0x5004120002d100f00121404c078000503000b0844c0c141d03280c1c130a0342c40c0d610000d141d81c80001110f4020490340d00301d110315080c0b80c00c00b4a00308000b00c2d015100c41d02030450150000a12003052000c0d010411184004041210240e00000380369810500640100c41c1c02820450400440c0302e4510001034002541c0c280b02d40c0c00070700889110304094050500303480f03170303185010030b881c00e0000008542180e036242000c114007070303220300c1408045100c0c1169012424400500310301c528412099080c141a01190315600ac1c00c10050444c03445900e9080c240c1b40c50099002c00a84d44a4004100340d00034001d580290000b4078006140801440d040c0c2007900014140d94499002d02c0f48140e10580991001700201c178071003000c0340c0c48541c6d0b41000354032004145154454491140b40a0f0f814042e8189182d100b141d15480e400d0000000b00201c1010b03d1000301380c0c4444484416400440399611184400c500b00c4200c02050540000000e100c140e840240484c0701d03980c0140018090385078040161074410070b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 744664316 1250 744663066 744663077
    0x30510092108190e150406060b070f060c12091110020c240706051905090120070606051e0103230705221203180503071809140d02070f03020f01 63
    0x54283c1140b0091160907244406071140f00d0b424410000e180ea1540c2c810350041c0000c00140341c0d543c100b10054419400000e00034007481c110540022415071280c2511105450942118013495070048101c0da0007542c2900e85041c2e8090049107807804c030096501e0420148050b04000c43c038840400c405410640b1a000100c1c200501c11821100d00c1090310900e64100d10207101c1030030030215695030307003448000c01d003407a506100018444000500503200a03002c011092070b28038030070b40440d003200c4c0c102d0a030450b180d82d00e1303d200081c03e82c0e44078540b41d091503140050025003408040054102c907030149a0b014445105e6442402440b030b80d4071000c1d8003d410f07040c140d40c0c8150b400700b02d6005e042224045664140d0940740440d00d8a14513080d01c2c83d8900c1b0b07468090074021005030030003a58940344902076066104c58403d00040b8195400b8050164590340085601c6100b9510341070715042506400c245a4842001d5846659040000c4c070007c12804103451fa4080c1950003140402d021034120605000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 744665566 1250 744664316 744664351
    0x18080306120307060203040305091908030f030604090f121b05101d16141207150c050a2d0b150105040302030d090305010c050c1c09030510092108 64
    0x240110f90040394090001c5560f46014903001d41a40c1005101e1800382814100b981c182074020342d80389065800a0004500f810a03550003c451940000c02a54200d42c480055000240b4114810f0a0385407054400c2454205071480c01403c6030010045030b0f064600b1103480c0c0021800220700c07084800001d0002241c490f1031a80c0d4008208485000c50126119002914104415100c81d280640d030150002c251048070302c000701305c410040e080348406181c01401c1d080203e020030a660703480c0e0300f41c6410031010803009602c43c1810184e8010003a1600000880c2488540860b5540030845017120028040f2404198170381510a90000b0b0403426001a182900004e9a005100740ca00555001b801c599180708900b07401440428548004c07140c542c00d040f6060180c50040f010740d41001001c600030150009800c006414050303112940c0703010b020000002101084c42804030319400c3c03048500100300c054461814a17540700801c5030341c45202603000c3e40f546d840c0e640101342c240c02c000c150316070b02c40c601c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 744666816 1250 744665566 744665599
    0x5071b022107170c090a0902060318070803040b04080712080304060b060708041805070504080d1209050d05041805100b0c0718140906040f02060703050909010605040918080306 77
    0x584680c2081c52810014100f83c490b1100002d802c804001c01500d4605a0743c654102020982c0c1c0d0001c4002c0d413240090001411802101c043c9004d0501e07018110750110795030302c042504607400340d0002070044100040c207101e440c404000d40030092000c00304d0500a21180d4588201720301020b88010711898448121021648d10032003941c44194214010070780d900d5440208c01c654604101c0c28840c1e580c00c150000380380c9406502994210350031a80036003c0c18507914000c0381d0030341c0300c2c500403c1c100713544000040100b03000f0804282c42d245183c5030585e4850500c95000480206250b488038600d0914003048840032207941200c0032918170021030740d1600001e008260804078280c024111110198404407926485034020009407540c520311201c0c0741d00d0b1280e105e901c61808490181048940c0804600142044c000401c6418000c1c60700c02d003070001800003e00080c1c800e138480c4000500120b0240704071001c1d480f5510012040d6203c00325020f08a82c1c0311005804005c004030b10840c8080b10780c0e81b21 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 744668066 1250 744666816 744666823
    0xe10030b130c06090504050a1a0103110f0d0c09080d020c0d020609040c020c04060506030f040803070c0f0b061e101d041104080c0604030b040609031b030305071b0221 73
    0x40e910100010b0459140c04004140c1d2030341e4032a0501c150305040c0842c05034912442280b140e584075500d00892144964015806480c090491000e004c0b820040203160140c0c1001421003450110030202d0b500042c41002800d003c1107070061b0340d0382e403c1071500100b1280c000500181000c000c0e02d20340510101030000520380e020b96141c191300035042003c030616640d0301081030425050100c0c0d081107200e44403800e00200c0d0008580301c501540303200b0041008106808050740d0301103440d00d820400403a0a80d9075002401c0948c02c1140d40fa44c0803414044107140c01c3d0347c860f01020350801003003450003400002588540c41040300f9001c1c000d03024a041c003030003441200c00302000005442440301c402006409855540280304110b001c1c00740c00d56800030341c60100101d0b42101d0f0403c610754440e84660300c912004042c07400e4100e00b400210700c0b820720005840351001920a0203920300164603c0c22078005014080d0021135001030110f551138100059656a840130003400295006e40c10300f07250404d16514 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 744669316 1250 744668066 744668101
    0x15060f091c0f05010c0201110c121303050a0f02040c1d0f130e0304140a032f04050a09110901060c03083402010605181324020705070e10030b 62
    0x502c8601003034406016054000302c801100d190b00030002c01d21403030200000f40c05180c80c0f004c0183c0003081c003000b05600e030340051300207034021081800b00d85980395940c601c1d00d580400e0440e0001000340c983c600758a03103131046201590090600c10f038003070070040a44e40d8017440f401d16903101e221402d0101060351110308903110034001c0301c803041044d40f04030f14002d42e882d049440b032184d5851203541803048504110320f0300d0045030350080400703180009840078281e400e40401c81c0455001e81d201c081103031a03030380c6009841c040c0000307000005074200c481c1049440c01c5c5041812074003408440e0010018640d020f10300c0d802254261900f0701c402c0d102c0300e14021086400340701001240c0685154805003a000c00d219803c51441c0d42c0003002500d960700140102d25005540340148199440c00040741503440c6000c464101d0f210702039108050824040308503100764540c840d0545581c2c040b440c0320403c081007040c0c4000c3c0030318400e00349042c984010f9240201a403808000c0000700e800b4041342c100340360310440e01d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 744670566 1250 744669316 744669323
    0x31b02031b0913050c0108040f0b0411040513030806100207120503041d13110d020307030c1d130807031407082701020c01051318020315060f091c 64
    0x340c6040418140066007500810040d00c285802d0010403900c0d0180004207200d1070348240075000c0c01c64079000549440700010020340303080ba61a0100000500b8981101d841540700c0d00802070041d200c00705000807100d000349480d83c9400034008240200f0380245500ea80300b81e0440792610841207101c0c04904100180d8090548c01601038030850412030040040c0098170000c4500000003c004005c19207080b00595407445a464090300030070128456010404403003c014040c1c2c200e80c4602d41c0861f01d0410303142d2040d51244101e400905c03580c00b4002c3e40301c9560304150800202814080c030341520048040070000d0103150b00140c1d100406015050540c14016100c000c0780d01c3d0003c506101c00f45a020400030390a0400750011908405100c0618500036403041e401420074000c50001501c8641c0210495881c0100b224070000704031800c0e159544040310f004030302513180c0c1000c81d4880d4400d00d003440700a100712014010010454050016141e600d42d04803024010021450070601c00a0390512018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 744671816 1250 744670566 744670573
    0x1a100e09010b0a03050c041d0406060e1314031c05040609020306010603150501080403020d2307030302040317090d060f1d0604111f03110c030a020a030806010813031b0203 75
    0x7600b02488002d41200681c946040c412541c1e640507181c107d00c01c030300039410007150801c2201b600382d10785030301d61361300c40d1055034000b400f036440d0f000403a542c0a08891025001c4607086c0f800c400c00080301c0703c0c15080e500402c000d41c24100310005c40c030420b4914040e00f40c585a038030b40005044c040c1a030040d0403080c0c0c0240a580c0156103074403005002c2c251191a01c0d00040705c3c0c203400100c40d44500015442903405601410218000b1034007151204483ea410b4510b65800120101e01c0074040d400130a1001d210707440040e505c51031840c10750034401421072074004020051106001580300c500c3c42c00d4a540d40203400281c0704550103441001007174000d00182034410108041140e4078800503c45029170302400342803140c4202c280c200700b9841820040c1076504814483d2010b2803074043d4104031641201910103a0a04500a1005207950000007641005a001004400500d90411003c6810010070318000505117420344810405001c4068001c0c100146035100402111480340c58000141c2e008064 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 744673066 1250 744671816 744671819
    0x151d150418050c070b0a0b041506020d09141c050a1b0801051303050d020a0c0f05150c0a0905060903011401080f0f0307120c0c0e04061e1a100e0901 65
    0x107019034511485100c81c040d03894080402d2401d4400c3e0180c0d0803055024140c01020340e200d0606402410320308400076002525204d19911211181a5220140580b41c2c0240701c28400c2032402004030460381c0c88004c0c60300304055802001d40342c00d200000c5400c0c1e581c61054000ca1903143c91071404040b501c001e00900c11184075106000c2241d0034010171541b68000071b1056407254118000b6890a8003402804254204000c0c40402c6968001d004c03c0000b6080c0810003001c01d48a103240350610140850b169040721402c00428944150501c3e000a00031400d241400d800c05006030902d405030141d107218a1000c07030380f0503096409400285400820244040385540d550030095a1110703003540502d40c1c1d000303491044008030b40c0001a6020190800100c18400c0964602030701c9122650005482c8004aa41c022503140b46201040380071702e202c1c040000300915040c0c009044000b644a4400c1d0036801c1001e41081141c0703884034800c0c50581101c0c4400201c07140759040d180c040807072030308035007042c0b04100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 744674316 1250 744673066 744673079
    0x110f0a0f0f05010e1002250503060c03090f0601080a02130f020d06080c0402090a030206160f0b040302061006021b0f0d0b060a0f0b040b360a151d1504 66
    0x520402c6038403c1e00c5040300c2e441d0302001c20203003621000d450300050b4040050640c0c113403040c41501032058005410281915102d0000c2410701208a40710f804144000040c82520700d02041144d10003034180c00609015410300d850707a40c0721181d120340030748101c81c024090080700209602598a101d0501000c42d80c0b82c80d80b544010242a562050a8050040c60700240050815008441030144020403541c8880e0669080080f00c0d0055207458103050307500ca400d0000110541d003010b458038040c01410075949410300e4003e1400000514165002c880042c00300300d259000507450800d85039071300700c90054134081d8000c5804401009512940425014107c06c1400701c0d003011070b809800c0545480030ba46881e1103101060741000c0c4240c0c0b0614408200401c03807094280060580c4580480c009582126040304041c110045108000249400c40c6c800c0882c40c034041012400801e036008070190341404156010385102902d00d660300201e0f800040c0d0448035035494424891019100310407985498480fa03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 744675566 1250 744674316 744674339
    0x110d0912020607020303010f06032a0c120e100e150301121505070507030f1202040b0a110105060a170309030d020102040e07020a0c0909080706050106030e010f09110f0a0f 75
    0xa51500140c02210042583e841c03010003200d050301c08010309800007500e041011801000c864010b10b11460715000e101ea49100c030051450b210200c00c0d42d5244c242001c0d030904410000d000c150b08418064a009200004e803902403a541c4006028208642d1015480010420301913030a1105003000b0030000c00403034003c000c90740041e442d0340603906594114035080d4078181200c0041d284031011a00a10030000040e20500c204036503407880b454849060840d80500b001aa00650056940300c100804e0341419158031940450355100140024001e60400c2408a90148824080c20151506144041020a2041048500040018044468600c0320b110024001d4000b802050300c018480008244020301c00a02445001e400040462965140070700050041a045100311034001c010712102c804101e541c0304090080000303850101e0102c10040d6150b084600c2ca03c00ca25002c2d260020700e07404104440d60046a075041512002c840070b8620000440b45c49582d4414091a8030440011a4401e83e06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 744676816 1250 744675566 744675593
    0x160203120301440d110105010503060402090702070b0d0b0f03060f04060b01050c0f0304030c0815272b03020f07060b0f03030c011e020715090201030608030c03040f080109080d110d09 80
    0x999428040392030005e110750076241d00b031165583c5030b44007102003400341c0390059165807c039040d801200d00303a903030792804111990010354900c5c80040c0d031800c0e03c8240b03040c4203001010854044000d0165440c04820b101c02c0c05c0030250000c0c000303035500c0c0d041002d0303640140c080f0784040b45070030704171028061a00c508a81d603a005004c02c40350780e866040009903100d80010f04810020300214050b101790343c0c0340400d1921003403140200071248244a01c505a406080c000d4070076079222003480d441d09041042d013503018580c800e002c0300f00305413040004140b040d11020546080e50342c400300100c0c101605000060300b01c41a010307101e506000004000e44000415405070b510120b204440840031520b01401d0b404030b008020000e8000700c40850003c103281d01c2544989a11481410002038450b140d181c498036507040804011483e41c40000e050084000801c1c03001e009040400090001303a099980e440124092440e4000c80c640d2250803050b410241d41064403601c42c641c25040040d4081c50400007030320441d2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 744678066 1250 744676816 744676843
    0x603070503070617150d150b010216032a080303010303020f030f0d0b0d1704090b0303090a06051b031603120c0e0d050102040b16020312030144 63
    0x21804001101d080104002085a685884035003000e81030001e02d440040c4000c04040b014640b40d800365110396120350700502c0040c043c89411240c0c00e81803d400e012074075020a06415035005500c0d24400c940c1244182d41500e034003d9100400c0400001a07103c49000300c0b4881c4542038000001003280f601c00030246040300d002e5400c840c0d54407041c0494984902c03a0710540815045c080000301000400b40e0420003005002609008003940580c8802960150600040c3c10105000508010303400391030050402a0f201200a9440c1402680001d100040d0305c3c80740300c05100e004101d20314070700710100c0505c85141c245800e507551034021421000031010b0f4a02c040780824080750310702030096810312621a892440791183c0c00100c06090401140750b82504003140c29640800000ca040301c048805082c180e80242075200071803c15204040c10503420401c56540c5100601c010440801104440c50051a42d112018200d0f007118001010015400c80e40701100769681c00b0040460100251103c402c041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 744679316 1250 744678066 744678073
    0x3230a0c17040f0b090f0109080a0311040f06140c01020a090e010905100603020c0c130b1815150c0313050406050312180a120809010201050c0a020d0f050904060306050603 75
    0x550070000c407041401d4034081c040500d5021502c0008030902e03a100d4105110504490050071015000c83c01c0d51544141266810b0008c81c0900c1401c3d0940078200180d4100c83c842814981415181c0560825920a2400b0480040440560414080c1c11143c020b440800295a10001000043d11903030031441030340004c180d071400025046005110349070141000001d500e040304c0c0303040003c90281d00200c2d8001228019041c9611455940d2039030401031480400f0040740c0e54040b4410448003071010390325402039407009002c100c0070f00e406090045603298201c0392185010300c160b10441c058000c10280700024400051000d0180700b0101102d8100c40086400b40080d030b84031003c3c0f544902d154002460180741c180304156a01c07424071200c6a030070790042c0095464a42d912039107114005050010398240ba4002070344003c0e941c0c20701810754005403070b86d03032145400764190000b0360380c20040145200f04806c10030035100b9240301c0ea007107902c560030062060040310b4072414134900900080c1c840900c00d11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 744680566 1250 744679316 744679337
    0x19081006031101030b0d0b040809040207051e0607020601060c0c0f0308030f0c0f040e06120a080304030f050316122c010f0615050d18060203061c0b060103230a0c 71
    0x43c402d0083d1034003010050001b4500b507480d83d07556550908040e000700c0f00380f1001d003c1b18145803102d1003d0070070b60b40208010204070151907e070924084101c8401d200c940c0082c0100240326800083c0c072811122545071800561010341031600000003250010303400e00c080d040000041c0b1034404041d601420340e10035000529100c0c18a011828400e409035000d44010500080081021244026511003005450942402c004040030fa0800071080801c0318503400200c0ae200505500c40c0c041c181c100100e05103a851424006414002d80800c0c500704400c00c05070410340341010219400c003249c140d2294407035a81261512040c4040540d07103040c0443c01c7d40c6046900240d140c0180100811540c40340105c1d84003108442088405900c0221040d010503115400035140c10a02c07007115101c2c502403000162641041c400304005003180000c8c40ea00140e21640c5000841c060940040c1c07c1402402c00090103042c4100d110903421603000021626800c0200b0410241e030590000f030003000b11070344c840c00c000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 744681816 1250 744680566 744680569
    0x21070305060a0312050903010b0a121b051e01020109050706090614120106030509150403120506180a02131e03030206011d040204020d0f02180a050d11190810060311 72
    0x2200284400f03841c03100c1460000114a0217400200700141000e03001051480180340410f4013450581e2148142c0070082210106000704243d08100b407200c075a005090461a090005a00c041d81c85204001e208000000009507030003580f00c0380f0400e40c80015948455030f0741102a2200d08103109040104061110308034482c00700e4402c03203900b01c001d242500d0090b420960101c2c0100002821540e0511501204a0500c0b12820745036204502c6a9115004203c80c014000c040d1007015018a000b40c41500c0b0a500c0c82041c183d43c26440f03800f02c5001030300d0704491200a803905000d6031110100c5000a611403640c00c000c2803010099a000e81c00301c64036644d0f607100c81000d08800320140c1990000700000b02c4c00610b07084d002400c1c5010942000f180780204e060300041207030300078041c101407026110900310131820103042a0b802001c0c100c034881e424034411b4035100520198401ca0300e2003440c05a1a2040101e444038000000d02080c10445001820b2010803100500740b60006035103045004030001110f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 744683066 1250 744681816 744681829
    0x40320040513033f05011a041d07140d0b090702150708040206070b0c0a11242d040507051e0d0312020f1201081207080d022107030506 59
    0x802d0381c1541c84440701641c0c964020811030740032141018907002d184060500c070120384a070060a0f00700802c009a036501d801c4c0d50034021081502403102e0b6020900c4200701c030080c8403224034000303106410740a0303a6070f070344d641e0450782111070808601076400041100084440b1581c0010aa407600b80c1c3d050500343c98581d401e9a690070700d52520a07607036405200040700302d4403850005e5000307071014080a080240c4c82d610111201000c03980b4080002002c80d2103a81c2940c884039400c40614410301a10007048200104045110101d2070120f0000c000c502240d8a01015288141081041810ba81c8450000c40c60068104000e40e03054a0500c2108404115031618040c80917507102c6404090081d00e031640203008040c01c513154103809009204881039a031400b94001010102102d101140d551011821102850303c0180c006c074103d43c1c0a041c42814810502048480c090780007a081c5450703005490120000c0d01c9009900d80841c24143e0500d1a03c02c0620b450a01a12040e00d0030300981d52028203110b030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 744684316 1250 744683066 744683101
    0xc04050402030a0201391e052d0304060e0114030108070509150433140d020d120804021e0906130e060405030309060f0115140403200405 60
    0x5160f002900079030300542c09140c100e500203403012070b020fa90200e5911681e110b10310400c504900a1142401c4c0420850550410043c0041c5030000708409851520381958440081821004500554403520b142ca048000c0409041500e41c003103941d00d507124800213101400744c1d00d280d8042110402911005a240c0b03043d00e050315800c600921074586044200540c125014081c8a030381c1000800f0400640c40318000da65032a41504150240321103070b08a40c0d120280003014800c0180d80c0d808090140da101841e0300028501d048800c14441e08507400020020402000020659280000c01501c06904203081c09d2243180203c54407145004074800b8030558410340d00ca155130042c28000054550325055a05800760440ca02000400344a00c503c2c03185050410794007514590300100030064002810072545501201c0041000c140e545822a04044400b201d240340c801d119651141d084072444003000c0d24001c58001c030220400041008a00744d40c0201086000d000d10300f0320b800200300c10381c03c810410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 744685566 1250 744684316 744684319
    0x10c020304081f0b131a010f090b0307021e010b040b04060b03060405092415030f060c0703121e05100f0306110403081c0b240c0a0804060906020c04050402 68
    0x143d5034100c074072141d00b00c61900380c152041d9030b0300d1910200c1d0b142d80040b4103d41c80700c0f900029428203917030700f50030501d24086452410007101403078510080b0b501006075400c65545010f21074503500d0311002a400c005d8102a82840403440025101d0800d805400803c82207909880400400c2c40407000e020030b0720b480d8003400c465510104041103540c00c150340021380c081b1100d42910211240c0e40070620b008181607070019030302c41c1c16000380103520400c8038461200c0a0128001d00400000e0140503889100080c90015041c4011490506040c0a91b09200185819000c10014210b00c03501c540e540c1164003908c040ca140c50078000070030031808400e1030400c0e07403d401007955519180d696070381c01502c2888903d0340c0000c0c0071b02c00000020121300192000e42c89100040c0280100d1140c1c8408442080c61454411084580c1004255000380c1c84a0320356207141c60015601c90801e100e007450180030301002455680d00207070020b00176074840c0526042d22840d60950709640030410400064030801d9070040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 744686816 1250 744685566 744685573
    0x70c030308010815360a020a120c0b0d0b030d0503010815091c0c1505010e0c030c0702011d0312040812133606060f0305041a07020a02040518010c02030408 68
    0x80d50a180440d46030958403a52001c1c0c00d20030a0b6100042170000c9101030101d1140d01c9100440c045140844655024100f0180b4104585006807662030f512025403183c621092800500000150602d40150b02d402034040d0840d4201090201c1c01440c0d03500034461a07002d8060142e42440342201d00150500480410300107002480301e03501201c940001d042000707414810400756941c0002e042c0c2c4013400751782e0100100010700f989000040c0040c440700500310944804c04008020003030a0031020340d1001c0b0303020b00c0d0945800007441601c103001c813071400d09107500d40320300f250030740140d80f000000704281c4041c0f4080d54445000011010040d00482d500050324881c25402441008091100010810030f10810b4008600c0000031100100f40005101643c06480701c106100c180e402a47c0d450800e90f851130104071a182ca500e41c440340201c00310b08090040b20440219842c58400c00c4103c40c0540c0090080040d41400464520745103010210742c0101d500306504281114001300690782103d08a4019 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 744688066 1250 744686816 744686821
    0x601060503060105040f0f050a0f03120309020a120f060c0e01080105060a020c280608010303170a110c0c1f120f09080f0a140309032d070c030308010815 67
    0x6a4141d00700801803810003a05000000da950704800341031008210760f80b100d45c3d0683c10b21080c400025103d0300710041c024110101000001c440c60402004c2000382d140000c0c845e07440e480003803001c2840750310003c2038142c0020309105003c2840141c05031140300e014100000084041c081e00c2c080581c001180c04500d0384001080036080000042101c012584140d0300d80e010020001200c0e11246045400f6409406150414910130002110094159414250901d40c503556000380381d55101108003000340da070600032800301c82c010b0700030360440500180300316198580d4404040c0e85004114059200312481c0140600c0d411008560380c0c580d1030745580341890008030000c0030029186c85c2a15030026035940c0319403000b2a11300409000149160502c5543d100e00d07560005260b51506d6078084403e0504006005503048001300301d8002041d401880c8030440c80425010341038922007008400012400130f0034008111446210710f05680c03007a200c010140e601c0b0714405a6400c010f01842d4000c4248001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 744689316 1250 744688066 744688079
    0x90c032405060d111f0504030624150215010b07201807021906060608090c100c020f0d06050402030601060f02070e150a0b04080c03011404020105070c33050901020601 73
    0x4c154010a0001c0c200310740103201003260821041c00c0d84188000501c000c102031040204034060301d820f83e01501490301203540e046c2101c00592040b8468110960320003800070907080d0080c405000340c000030385602211581c0d6041e54a0140c0c3c042ca00440314150800740780e0b103100e80c000c007500400c1031018000690a05400d0030100903000c025141106610411494281c80c0000e03e810000e100d22486010400c1c40c504035001c1c040070300203020032000f9001001403008a8440c1180750404900902e4070001c01c0c100c038004221440203030b50b036080d04100c20921074014010b0507084240a00c0c42901145c0450b0703681c0310308031086a04c002031440180c0002408124401c1117004261b000484c00e02280030001030f0000041c091030301c41c0d200060000c0d002c1410001e0102c1071205604070301c001da000b405440c0d2011803405c48050003c20090500c81c001c80c0e04d0060106280002010309151340b0100c0f05c0b17070034001070403005100f001141c0c24031120602105520342d20550130394070b4066041e001402c00c0d07402c190 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 744690566 1250 744689316 744689333
    0x7060203040f090504050f01020301060525051c030227120706081b0405060a020a060c1107091d03070c090f0207080d09062c120f0307030207020103090c032405060d 72
    0x600581b941c2c072a012841d80342c86003e2000707500030019a02c88a81e61a0350014041102c03c6a0210419840e10b140d541c202096000c154891101000c09080c40042d80c1140d0a40023405810f0494113145001341703034016440e54080c419100d003034003204e5080d078007040c01690903070f00d6580e4090b03000080c100b040413a4aa4072036207180c40e90805c0c44090709045c1038440000c00d42c960010082a0300682c0400216000c2c000e4a100b0040c800181d031808001802c01244160703a40c0c1c46d5031054400e0180d440000c1ca002060129142d400b042c900b80c01d40c1e645910302c6c01c001c0a004c1060090340204c500c2e0008840c1c1d100f0b05482114103981c1d02200860422540300f240c000240000c84068444944600300301858403100c044040c04140d000000485511203816a58944020040f0301800ca92040001141403055082520343c000898580503070b4a40c5a440100c000d4481000300a003105241000407080103560010141c0600e90002d106404a06044e81141501c4007550040d4020160306c00c3c04c00410100c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 744691816 1250 744690566 744690571
    0x6010516050c0603150a050102010b150c07081e1009020109050121050c0705190c05091009060603140a06240c02090c0307080f0403080c032509060207060203040f0905 73
    0xc40964503810141c1011540c50351046175a000d4881c02c0000c035115501c1c14100800c046c0c202031000f0480444090080740d1000201c821100d10036802040000003044104110000f81c080d01081e500704460050b40d0703844034202d18142c0c842c1070183c0308410920054600c142c03182c0300d80594940141500e401d006407800341d0b006804040c1400c200920510401241c0119030290140f9002d0541d01d12650405a0400113102500c5102c0d20341d199044001c00c0c0f842810340c0940d4802c4031001e0098072040d441310348040c015880501d4a44c01c10100181541d0180c3c00161440141d40008044c3d40d2241005c40440d0824002d460b100000404e664007428201800707041218141d00303013025039500175000600c03503000480e05010391030000010070001d2644400d00d04d81100fa00c41005800341851342c0c0142407150020140d0200b40c9010002030300003501c1c80c1c100604030800060906106d0090740009010041d80c0c00b9001c050b2085850005130b6920010441301140c00c0980310900003410840d0340c0c0701400c0e02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 744693066 1250 744691816 744691823
    0x11215120302011506120f2009060705010c050a080114400e0705120a03050313120809070f060e06070204020f0d0c030605060f030721090515090606010516 68
    0x3c90000415080c0099501340151046890320aa200d86892000007514500076404546a0901e601c2410315042c84000c142800c280c0d41c1516214001d00c03010800600071440081c003d907080c5403410314565003260084c03941e010b140c0d0300c0c0700a980c1c0301d400c44000d100c007001910750072000c5042c1c00d0080e03110030b0104040c030315040032800c94125592001300d004004c0504101c00d00c2c0f6075600313003200c070342000f0004c0100602c404e4925401c3c40b1104081251207811030100501401000000030780c40910903001c3c0b01c0750302d9006400444800e0401030061a6000480c0d8022041c8158000811021240c1ca8a8000c4031042d40e19004d6440c882024880c16811000040307030030039001d11210302d8122424000e4455040070b06000182d0f107052540050a44101b64046805010700704503007803202c0c0750712088035407103411400c20f003640702004510840c20b208040c800208a6150000180c00c1120208419043c12900050240952171b01c05c1600c4d2150001e456036400302e2020091059080034249844484501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 744694316 1250 744693066 744693071
    0x2060304120306052214010609122612060102010e030d18060204150e0d02010e0402070312020c0106080618072616090f060e1801061a0901121512030201 67
    0x16160085101c84d0b04454000b14070a000c170220b50501e191520a001c0945004c004e0003c0c1945080e10152140d1014001d0084070852284890140990514810340d001001a04d4030810603002101010326000b071102100c00410b0100401e00641c414000d552910403100080c4d071412100b8801d04004140a09500c0c08c10320394580400d002c211288050802050106961f0702c51002241c1c0051604420384041c40c401c4440c0d0078604090b03640300c54808103850003a00d00603610012420103545d100070701d11240c000c0500005840c0c1ca004c07019001328080b241440100c440d00e844441c0b00c1126040c041d81d04260941c0b08040401070310000074036031144c400c6070000ac407400da0400d2240714106884900103aa6081005a0030054102a4400c451034000441070400072903081031000508544060079505032540e0b4540f03c010500c1c400c0d40b04038000c120585a0114651000d40d002c82c55401c00c51703519010801101c80c00c00d01c8103050180ca1103181520300c800c90404d042208410024000400c150115907 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 744695566 1250 744694316 744694319
    0x3020310150b2b090b0c03040c06050f0d09030207060e01050405030d051b060412110a05060f0612100b04051003080f0d0603140c0909010228180e06090f0402060304120306 75
    0x5100f44041c40303204001c1d01e80403444140c1410030603001d42c0080c0220081820400811000c5081c180d60f1000381c0c1c0c400e1404c0c560b5100303d003000c00c15502901000905035850400b001c01055000a000402c94005072500076a0924440041d591401203208441d010741000b402202001e108100800c000801541e280800c1070551500070319008089808450311a08417500d044290f0b00040e040c000c5c06080070040031b0300802e0703903100c0b81c5904010700780100350300e050b401241181c4c0d141c01c2c21100c9011813200301c411542c08442074030040c0015020f40c5000d80d2601000c1028800f10588050640b50010700d004c3c03409045400740c0c0f00326031248080c413041c0d81d611203020000449143c1c1d05182030044800a0480003280c108010a0041c040e11a8100760b00c10071004640d540b200c1d0041c03400e007c180781c407900d155081d02c1095a80200489a9038164904400e020a0890a550005005c1c0400703540c06200303079a4907001c900c1c0c05841500c0196220300248002400284184a28000707229030307190200303155 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 744696816 1250 744695566 744695617
    0x30e120c0118050d08010b0a020a030e060c03180405070f0c030c020a0b070803180615131512111806131409101401061b140304030c03020310150b 64
    0x400e04030b2022102500888007290543e6800175440f409000c05086251400885020180d0358281010004050144442d0305001c99502c0f101500c241003d46401d03a03030303190100884101c0840701c0079a424851807400700460b0300944511807101d40c01c00640c0700e42c03800341e1583e1400d5941250000c0c0c102d900080300240400e1b6081e16002400165215555041d241c1c24020b01024002c2c3c0301d05600f18565205004002418840894110129100352040d02540103000b001801420a40308203500381500c120002030390076183c10f039241942d07000e40b01d0103200c101700b10200003a100ca2021203144156003040429220f00d4509048504480000030006045190409c502d03504041103880c401150040c0c03054107548401c9000740c2130340b0300007a0444035056042400c040d0030703a9414818220704000c200101010098541618100d03892500b048a0301c1d182d032031514444018a130301049003e402184400288030801d0f01441c00001861030b5071580c40c07030900072507040300e07040801c0d4031001c503a0a50760b03040302c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 744698066 1250 744696816 744696851
    0xa0e120f0d23120603060a052401140c0c1302070c09050a0b0405012306030c0a050f07050a11010906021606030b0103060515030108120c0c0d02010c0b0f0403030c030e120c01 76
    0x100700c140c1005043d20b14080c1c00709820b10000030000c20f003480c144070402000c1c100d0070210056240f480380d8041a00d140300001240c04a10000c0c880914880c0001c004a80c40d100161140c0c07492401c46940001c43e1070305409134160701800f08009c0182d0780b03844080c030900d1500e4000e152302403805207000034030b4124000064107403542a808000c4c0c510307010441c010302103141f811003001054155041440d5060580c2c0300003a0340701d07503800a0200140490000502c422030821900b1030f41d01b100480d14001124202218100ca4488070140450350300a00090b04600201b191540803000000d020708d6a413800805070040c1c201c0704480303810165180804599656000101000030320103445080c0c582d81401441d030301c0c20304e5075050100c000f02d0520990364405800a80000704034030070746410740425500d10041c4d0303500200c00b5009200800d04020020000d00c44255944200e001c1d0742d040c0281d031800c1c01c007601182c01e03c20040d0401d410005407200145007076002800300ca004000009003820003828030401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 744699316 1250 744698066 744698077
    0x610050f0a08010609092007110a06020706030c0c050604030806032103060a06091203181701141f060804080f03012310051209010b04020a0e120f0d23 66
    0x800c1d0a0801846203036071000d1103030094401510104814000d0800c07240c8440e690307c0e4850f281c050f00086440c200a10540381d11040940642852021a29400f01a40340c3c1250300500c800645045258900c03144039105000031180c210018010680300d41c1c50442c0c0c00070004040135014410b0039000850031080b0142d80c40410744845072242c136420802e08003d4503621076032007507040000740c800500503424051900392007941d050802c8901c000c00000c10400000d00f81e0b002c405050b60031010b4840f41541904001d10110400301190881d6496031000820402c0c0c0070345505004681210030f0080500501e00c0d40d400c0342c0948003990600c02010250180c5030701c241c0241109000c1d401c004901d0b0320002c66075512a000c00c4031844100354204000801e58062041c0002c1800600008a4180003080d4003d010b081030141055544814911001c0c2c0880e803c1844107014949404000b0350300c01010410000e0280010054007811905c00400c40b4042403040e981e0b100052580084900c10400100801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 744700566 1250 744699316 744699337
    0x4180813140901032f0301050c0406112b020106050d11090c0316050d0e010603062c031801260f0903070201020c041e06030602070c0515030610050f 65
    0x24650601c01d2803165400349107407460054146900600c00617201d0a02c4103044044e400c0000003054000500c040c01054080480c0e4142d46000c040c0801441c03504010b100303507101c540310381110031617043c01395035600002d000a400c0d80261900b04114076441500324143c0341c1003440049496a01c0f800041e45030f03048000229648402403080305001d007010384c00740c2e6001d50035044c6036042d49498509090242c140002c25010407000181081074982e490740704180d0b00c41e254008004080d240e05e81080140b03003880180c0a4110044000c01c0031104100c4a4110f80b508000950305040080c81404e011a040c0c4581e01c2c1030040304003812181c83da0203030011030043e84144120b080c03400d201c0310060035400c01a001e04166081007081c00d02607600011003040d0107000380c1e80090f403160000d007401c040418950308038441031304000d40041403044580141010303d008a8503a14a9669030042000d80310841980412601003440000d10341e29040020300c50450705410800e283c40100c100007050750f8026106d09 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 744701816 1250 744700566 744700597
    0x506010e12010e01050f090712030306091409071403120d0204030b09060403090f05090f070e03010915050c0405010804141221060906150c03040b040b030703050f060f041808 76
    0x70000d803000d01138690406c0d48058407141c2d904022540680720107131802030810a24182042e20f08151003640078400078109400d00b004181038802c0203014030171040c0d82c085e08900c074101000c61000000c4140c05c4e03181c2c0006001740507069408d5241183c6400c80411440c03842c1c1d00740b01c0080072540184c2d085100c1c3e000c1402030001481c0c6403601901010183d000b8100344d0180f1142071066803202406182c1107048240d000c940355840600c1100c2c41c4c0e02e030180d22a095400c080071740d0100240c400d902c84a910030764000348456952603141e41042d006030710032580080d034004041000701d11a440c154284082d088180d23640c81040350480706065001016103031010031900c40860b40c200d1420411a002181255171110724202a00010001e20f4110800c54980f034000800c2200c0c0001001201c00501c10440c003036844aa48a1440400c0d4004460041c0842c1c00c00000a500c1222660301900c1040024203003184181c1c903005210050803215200416240c0300320f45030300441c051802a0a01e1040101030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 744703066 1250 744701816 744701831
    0x1d04080c030f070615030201120b03010e070605131d061e09011413050c0d1802090703061503060302030a1223030106091a0304140304030c0303020102040504060b07020a0501030506010e1201 83
    0x3001c11525080d05e0741c650555006000c1c80107070f92040c205405107900d20408a01d6185a0001030300405080c1030b002a50301c0b030b50301c000801e5600b21014101d86020b20414404850340c4504904c0c2103804c01e03071110007018000b4001841c903d4080c11019064200c040017964003250180030600f4a41e083c1c116051381c101d000d86221092414141704012007641090034080c030301300300301c0e600c0150040c900c440c4401500d40118041512408030100785040d002010390314a810514009401003007e402880000500001d034501aa4000d005150450b54064010541e03e481500c8a0400600200c00e1004000d40d66540c42c2c01854203060b8801824003070009242d0300c0d4075000020308054141d07840341290f101511207403141452a2415241d029410550141005940414003801e51040382c0000b0010f075000b003000f0081c507a0550160003038503016641000415110303810303080035000d8844025800417095209011070b5209403c91508200103060001c054220100000c40d2a005203801c03e40340e0b1340d107165 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 744704316 1250 744703066 744703073
    0x50a0908030f0d0b0d0f061a1c0b0106020f1915090c0608010801060b0318030c0312040c12210912030302130b130608040510050405011401050a1d04080c030f07 70
    0xc4c1d016840b81200c0c000d621440c03550341c07000d100d49544006040d0503501c8001225500220440c01d4480c880100101c80d43c0c070301144114407d41940c0b10686c0c08083c5403001183d018000104001c004c1d54810080400e0f014901e03000e6150441c4140132605103001284004c07060b0b8a6008040555214803a00031100307041c07034002081060705900044480e814002d0811400e0900011031b5000180480030f580900c0d0307407039801855032140c0c0c0d44034a0180300002c0c0f900360079081c00584034011442800c8018216507140c2c0c00c01e030315188604002c2d2081007100c28403000700404100540c9000000e05110711900d47d01e584c9030300d0b500c6450030305401194000480790380c2c1107264500800900f107441d18960426220f65030031414280079005540c20b0000a5020405000040102e941d0310395808170244070920b06860054082d02c4090251416800d5007400400c00340b500e5015002034850b4007a40900b81c01044441c110070450203402569101010052456241c02c1440200034074101d491030b0b266124142e02c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 744705566 1250 744704316 744704321
    0x1802041502210f0906070804150504081204050603060f0d0510020a0816170c040f12060e01050c0904092603070813030219020402271008040b0403050a0908030f0d 71
    0x208004510b2002c2250038180c03640881030b12088074050f9506519a4201d1414032074510032030700312641c80c0080b0346903e034046502a00410a58150b0421f9030100c400c1c0c12801c2845018a0280c3c0b540880c0c14400030300350341072008100804a0008014410320310660300d401d800c00d20a4244503040c02e0300014803101e966004522950014070441c419a02401501d10040404091748000080055120041454110034000f55405400031020504c1565a00c65940c0150b10144a007114010b0500035605044a01881840d2103420250140c81c0350241250400008140c002421200300150a43d01d40c11020206d03010036201e600c2d4040d40d9982c1c01c2002010f001030a0003003501807400c1462034802c0c0020740c04550000c074030001601d4420070544a10014020f4020f0200c0848013200c16100740c1030200e40c0d115070800340381c0c0684102c0320303200ca0610100c0c0c61401c00c80b00900414810400300e4002407050340200404046807070803040d02174407210f420b0308561000c61580c00300b59010458144684051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 744706816 1250 744705566 744705613
    0xd120f09080a0e090f072708011406030105060a050909120c030306030f1c051c090b0403120207051b041d1609020a0f210c02250f1802041502 62
    0x100c13040000707480c100d001ca100c080030041401c0100040346c000341603101c40c000e201c1e4035040c4203000300600c51515100e9903402044074507012944444c2040200d059420113201300c0d0301448001d440e0300074440c18002130004251018101c03007100e201c0d20011141c0c540b40d1401415104203120095503690410700c04040c03030300c41c059110350090741200e011034483e0761004130355000042003030038481d0b11030003241000814004409a40c8202904103980385c01000106031038288114480d441301d50307202001c2c0511500b01d0042d0b0a00824550040c03a044440d40e0b0891095144000000c2001c25445840380c4803010346c1101c1500502142d02c0341072400f43d4100c1540c40303200134205011045043c40d043c40030003802e035000c45441006105a640c02c0200800ca800f4041d00c0c40e2412000a00101e401c08900035544d401c0c0300b1200c2c4034250340c51461605241d45241400444d052520342c03001850400880251034494203086000b2250b0030003001441c1e1a101d5a045402c1c001c5030060700c42402c010703440c16194200c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 744708066 1250 744706816 744706819
    0xd080d0b150a0309061418010c02010b060d0b030c04180b07050712030c11241005012312012c0402091b070503041e0e0403020d120f09080a0e 62
    0x6004407828414281400e03200b4020b810310b8041501562030400c2002000740c4007616203500c220318204008180d84050002c2400d1340f9100070810048540c10490890b0815600c07242e1140303007006a1f2044075815042501001f1004007a541549044000181104c1c0c2100e5404108955440c4020030f00405200c0d26900c60070608090389401c40e10703a2503010074040c4403a07100900d40c0e00e10000c00714078865030403000113070411400c81d00070141440124005000d0380159008010008000440680d41c82c0e0321042101c8041c4c41c0c20141c032400c0b14030381841d0441a030003028903071010300500c5955001003008500a0000503404250085550412203410008070201c2c07140450031028000162607c0b03d40e103600820258407900d24420b4810f154819101d0136a001d010f500c8049000700d503006181c0000700e0702203101102c04204580e6258138a0000d11b04450103070150f000010020100383c041c40b02440b0b80054400d002500ba00404100700c1101d0340c1450079290207a0204200140782d401800a05240c1d50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 744709316 1250 744708066 744708079
    0x90603150f0816081f02072609030c011b260703081006031505090a0b130506010e100e04050c070602030f01061d0616080417060a0f1404060908090d080d0b 68
    0x800c04c18501c120860740c8a17103491940024910244200f01d800b001450202c90b52061600d96101243e510503000500300710302c07034050301d69182c0103503005400c4074200801d42d00301136410850b10349803c000c0a4a0b4221002c40510110111043d20806402003100034400e440703050b00d905200c018000000803540190091516050765001c4824040310070000b1602c003110b24480f190364100e5400054510002515080101204100c000c0d080907005580300b11000e9aa062100351000104200e68010036404030208142441d4001c8604054002691001ca40159285003042c2c0742e80712000c0764000c80f0703c541c4011010700180f201542c00340114244005080e8040c401082c031000240c7e4621419507880a4a44180034020030807036082e040e0717401051810003000c0c0300400f085880d83c03560f00c00c0320400103851600c0034070b0200c91641c0c814400e00f44112001c402856480b5075500c00101038442094807004800d0001e0b80040d6525040c41c14004d210307011440d11400003540030002c0d9032803509400d1040c0c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 744710566 1250 744709316 744709333
    0x50c0c0409080d0527100b09190b0612070806011202130506090f0406032102010510030320070609140a06020a03050f1c0c110706090603150f081608 65
    0x2d0780b40080e107650b1103c03500f00042d140c4403146040c030001052104560041208240034194060200c2c0401e884a400c031418402000880200404034504540041d007041a100c025a4400034a030300520f0a01000391910703182040c500c84030035400404482c9000060742540400509590000c0304050303903c948602075082903901c19803071200701d07028020640104008034104102c1c2c3c0d5204589000030f4005441001019100d04010b84420b01040d00101c4075000caa008002291051250700c2c800c5042d02d4011141a082d0ba8040740c100610f0050f0000c03021610620341104e5005208840050105403a180c2050b407610010b44003180000310514840c210803001003080640105004102a5152904540c2ca005021898045006502c4111401d600c09110f80208070f17021b5018400c242c4060b03c8801c0201c00b00c20407966518003030f00440c800140000301c10010319009401102004140450400429440b1b5040103c03140455102d0003160b840341a4144c0703180300881440c0e0280804e24007416501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 744711816 1250 744710566 744710573
    0x10b0310330f05250212070e0705070506011203120c020d020c041e0902010203070618030905090402131d120403020405010602030c1b06070f0c0f120b2e06050c0c0409 73
    0x14020303c85240025180e90041304401d4500080200c0015070080c40c42e8140c20030705030101c0c2c0ea40d0341400f450002c0610100401c000e24010007d6500701d640c41700051109a0900e02c607400c10b03082c00311088007400018401d4105451081c051141c104500f90f000340710800282d14001c0c50014244416400f841c0313800c0c0140140041040541004510300d20041162522480100d2540c80b4201c809007005280855034058080c0d08110744413440d0095a4a00c000b070b4851040110140061b01c00079441180d1020702c4001036456005a002404408484400008800382032400d00d0f9142e64a4501c00b20001800d008500d014854680500010b100941c100145020140c1e80c4050701181004034411851464a82e43d56840071164903951000803a41c01101074642590200003501915080c4813011b4800b081300c20020700356400307980d04414a070110351035807000c032044500d00c005c82d81c01802c1201910071000f0340c084502c07002003c042d5680b668030710f2039468041c202030b01a04642c5c4036600b4000c845021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 744713066 1250 744711816 744711827
    0xa0e0f0f22260a020c0108010911090f0406051206091204050a060806190e0a060806060102070303050c0c040920030c130c11120a02070b12010b0310330f 67
    0x3981d1114070084481e160500d02c2880034a102c0150750941c100040200801d0360100705010f85c0d8800f03880340d18644c1d07290200903050302c07921a981004010706100d08203251414003d130161703c0d04064400100140c45502103080700590692568a5510400034014448410000502180c45100c445800c1030f04050004a09000d14862881044400004107890740d44d021440c082903241034a400741000e60700c59142d8410041120189445841d00c00300181041000c42c8182c410341059020702034042c00c540d000e0310f80380c210741a0716000d4425082d0049840d01c1c0c0f0320a45400030f000b008445960921803000500601003501154005d410407482030344991512034000c2c6900d15010030100b0308c40001d040464103000d550b80202010311400d0594101c240c0c00b000203051803144da50a407140e46860b030700c0c1c009040c41a9810a0b500006001c010440038070502e020b5504441440b1084821540c2da600034194041618030046419955240d000c2c1048201c004a18220040d030034110340385100903402030907 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 744714316 1250 744713066 744713131
    0xc091a090f1315020a03090506090703080913020c07062a050d030209012f0f2b0c05070e0a05070c0b060108090705030609060403020f061b090a0e0f0f 66
    0x502c0c48060591404005030303400e91080c0300e07903010740464070f40510b840000c3c042d109000c8181c4060091130081002004040313544001c2e2038112242c0303032400b0700304c1c0144036844404046000c44250b0030300140e51802002e001c5140240016614003000a06200f001c0500c45074611020082e4803a014106c1d00042022410038400748980c100140c03510f105400581c0d1255000c60144101c604407000d440e01c1c90104070344000c0b1b9079102411580e408000c0020345544059070820a0b42e050100e0300062a49203491400340b10102e480d14044000c426556103462034900300e908180d40c0400742c0300400a0f014058400c96a000c1018903021062000d9500c3e14408108060203490421498000151784200d0802c1000c000f02005000c0b1100d918103c00e605d5201c120035a0304070010f02507030b100303005800b2000406034000c3c50f454074045804007000100074885e07030103c00074580029009000150b1503e514a46034890100c01c2d115403600e01d40910610386506000700f0012000003404144001360412407080e24 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 744715566 1250 744714316 744714331
    0xb1002070b0f040e1602010b0d0f020d053a0e0105070f020a0f0b0c07051206010e0717040602190203031504020d06080303041b050f1f0c0c091a090f 65
    0x10754480c0c0442c10b4012900c600d0f0040c015a00d2131100307000d43d204444004810202043d03008000d104444000c00045c64031840c1701404205c0900f1040d005468074981007090340d441102100e0074080e07140b81215045520880080d43d80c01e203503444100c208003045000e8000d110b036282580250096000182080c041d41d0000792500e07800740600b00c215115071880350083d12680c4855107000e03607a00c400c0c528561005950412502680c20006020300701003105160581e00a000791205a00300a515105400300074114000c106540c10103240389020007101c2401980602d001583c2d4107050404011014100301401d82158801c004104501207445065801000200d4015a43d02d01030840c00d80074203429040f5440da03002c00800e000400c002c03801c81c1c074880030020b400105441c0d030311000c2101491291019070f401490300b2484c4000c8071100d240500b0480c43c0350422800910b004c0e19400303c405140c0d00402602582e034280011b81d03803100c0714101480d8108842081e824640000800458107014003101e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 744716816 1250 744715566 744715589
    0x80f12031b0c01150902042303070e09100903081f0b030a0b0604050402030a0b150408030304020f1c0308011703280c17030a1404030c2a08100b100207 66
    0x80b0b81c0d01c400b0f4000c0121003003011000030046495080040c0258446c5c071440001030000c1c110b0010030440c409030004001e000402824050b840c00c4c801d030303a004000a10000650007001441d22500c45a40306040016010b40e8403140c0515007418516940260b03080054031858164200f04100d07090082140d500c0300340820049408442c103008240640a0754001076401030000c0204110360344164400141140f08642c030343d001c100a01c20b1645140315500401a154104100090148c140002c00050300b88003e401c0481800041c4500752060881a804400003100b8000421980114201030300c0581500700241d0308d480c1c41139a05401d07020b080f04507401c4260741345424411f418018104c2c00c2500340c00c858000d041c180c8640007441a035200321000c1c02d0080c5000500000c1100201c80c0a100c0c0e81c2c117445290484e034554460110366480c0c0c2e40b80380201d01c1944150318803d05115522001041064003d2011400d0f01800c0c2003600d018000090007072150000003000603a0004001085840c0603100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 744718066 1250 744716816 744716827
    0x103080a090e15101e0302031e15040b01020f0304030b04060219030608150415050a0209210705030c2d150d0f1509110c07080f12031b 59
    0x6a840404503800700b09200d001d4810044081441183c61035008070859200c4840841624140c0e105032402202c0680f80700001296184903009600464201c0b440e07102ea4410310741e22210b11840d500040350420b01c01ea140700d500d0036950a16000790750000109001030001401c000c2002c6d940c9000d2840060310f11014440400d0074000558119100b41c081016010b0f5115000d09000c1c01900c0c05200d003c140d8811044145038644c02d10b20414091076104413036a03100541103a9070000703060040c0084440c0c950070080c041041e0303591907601c4102c3c4c84200020120034180b80300c1038107010403a442280a60041c0c001c1d50602d98800c003a0001d00f4921000000e074034503407008404c854450712180740c0d80003100c82c640600400003a201512042514a0080c840800c150780004140c606426060400c1441d881040c00110601d8000d12111100c1c02452400c00c02c3c5034104ca0310701a81684100701c190040740a2420300001840708450410f140850745245040902e41510500c074800c41e249410900440d6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 744719316 1250 744718066 744718087
    0xc150d02040306090c1503020a0f18090c0e09060303070b24030307060518010605150a0201020906040b030403020d0309080d0e0f0615010306060e0d0201081f0605120703050f010308 79
    0x10781d030185803c5101082520072030300d00916601860b0095044a021281200081900c42c0c001c8410112441c0c4d03d005251598020035607840101e00b2a144010010704408074a04442c2d100d140991003484d80c554064030160b406000c0e2038803015082c0c501075001000b840003c1045881d0399900081c2c0ea107051007844003096007040640201d070380720aa041c000000c1e00024424183c210501906900d20707031100b5102c02030403850803038011b442103941100316925640005040500034003510805400054500082c001c00582c40381d006400603007000d40c0c0401400241603040110707111400c0076040811903080c1d543c450900c0381c0680c15039905496100c2c03d8007100340805000314040c0340690001c584140c105003021010081c100900b1034002460000001641da00c1500d0012a0791b0018104500404140c0c00440f0030b081c005040903d507203821164262813140041c4900001c00a036603440f600d6002094000c60a01c03000b4140408250400060200441801522604481e403002140750b4a504414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 744720566 1250 744719316 744719321
    0x807030f02150717070b0f0f0703110d06031406060d11040b06040e09010603020907020d080c0f07080406030b03010c05030108061515130e07030c090b07110a060f0905030c150d 77
    0x540201380c41e40811140011040080190a07501e21810b5150066507600038a40340c800000c0b9142c68007103c014010500c518080c0d488428a03a00c5403042d40e01c2c09404c06801c00654a45610444640800c0e4110741c402c080103004483e00842c0c01c44111096000310b4544408003d01d25401d40c1c0310f0755175414408020b9480c281140c00500407400701c05180d20b0880c0310240200203612050307020381060000110401d201086a022000158846a0442d20350361140c00054222498048520701d04002c0b2001180c0190087e000615150740c0126901413401c2c149400c1d544030018140a010040c0010700c0503090120399240e200c11032622580c08040340400150032550845035201c01048002080c1e600031411a0080003942c6085080540c551103110044007202c01100c403040004407182e4003031100303a501e01c00030000d25005a01e640034424030076002030041d1f0881d81c4044003082c0c5a084414185810001610060600720050108a149480491401c03903160312402024940029010940e00302503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 744721816 1250 744720566 744720577
    0x60f03150303030e01110a0c030c0c0b03010f0807082b170a1a0922141b010e011701060311130311090901090c0b0d0e1b01090807030f0215 61
    0x5180900590790740307060140c010007000084040550801440266000e01582119462002c1c0d40c1c40404407503a0351011100807820140482e002e0754844000151064200017441c0a072052040c2ca140d20313441d24650b41d241c40c00f5540036030f000741c000e000c0c411816445107009559580000d0b80d00b1211010aa03411a00c0050419681114035041401e0103156240c030360205440c09092207020b0407000894081160b0303040700b101c0a1007035400c0b180c400d455008900c8550310740984208400c0003100030618aa6040610318001c411040380d000000545035a405504200da05c507003802c000c11882103907009600503007814010501815218201d001d00c40340c851084500c8142d281e003150740d0792900c1c0d180010305c2c03201c0000c205201c0c0c0300d94002308084690620400e00615800041848454030304408454250040c181e11081a1303611141100c1c0b805043c04009500000345a4800721013210030005002a1001d4014503150785c021001840001d031000c022036411901290040c0c1c1c0020151034002181c23145d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 744723066 1250 744721816 744721841
    0x10f03050a0803041509050c1207050607110d05010519110c1e030405030f03033103030f020c01050a140106031406060d110f0d0b12060718080f0307050d020115060f03 73
    0x6e02900c001480740c0411a014282d4040703d0606480c001c0840e00c0d07a42e4440c50280650001d420400400002d812400441145001600d400d914441c03d03102c003800c46008a83c03400d1000e0031300c0146011803016120394aa02d050284126007001190381e1002d035942310032400b803e11851101d03800318042004009840090100408031186800024440307a2260000d552807003186420f007164040c282102c01c000104056051060b403a520500e440403005065881c1002001c01d07403c1141010391242030184500c1608001c8002c10003220b0320590f04a0444141e00c548100741ca000003400100c01e002e400a9003144003115000c0d00d03103401140c00c0f0000d01c1013a80202e64414000303024500c2c58801c60162003080b500c8002007050035200740610030b80c2c94040b07031140156040704000032400c85c040e600780f02180c4c0c841c1441c1c0c4440d9896030216482d21140d1031400074258404030b107a0b42082010070601e40c0202081c4000d100425940c2078000014083d40101c1c001c0c072100b044c040328240e01c00ea00490700700b0f28 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 744724316 1250 744723066 744723071
    0x150b0a02010911040c140901090e01030b0610020d0219080d1419021201050118080f0714030f0706120f2d051501051602040903080609010f03050a08030415 68
    0x84045020740208010a011500000c07801c8540348189071500c034032030b5180400d4488003500c00c1c070060440c01940c08001c1150503c01c040002107540c5a101390b60714061842240021064145081044010200c0201410455000300b0803440055408203c041c1303180c1d10401418003508852424000500034460889000d900d040c0300794100c046400c1d40240111006000708100b001101114002d900c50400e10001c145c0c103c030300401640d44500668100f80101c084102031a94480d0101824002000500a482d81c0840014403100c0000c0600d8548034904400902101040400160f1103030050b03c81d01c400d01134001000790b4001c0729500f140c420a0920360080024010140b41600c82030034403010003401203030b04808001e0401d800c0c441c60b80100f8807403590b0f0018403540720045030550701c07c0d0460440a020f0100f00b00040c2c4840c0102c1184600c00d858030107079460000140425000140c0c042c0b0600050980d042000c69004101544840c0d0002c100c25540e42da5408c20504410021840c01600751 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 744725566 1250 744724316 744724327
    0x40515040e0f01052a030105060703141c060f06030b090a020306031e0105010627212001080606040609050904082703120405090c1b030d0e1507080703150b 68
    0x110030181c2d810500404c178000e610f0b0428032007010a00e010900400d030b0000310810421000c40d00414100c9007404403081c625203000080003101e0344201100d411280c0003602c400d0140700400184140780c01030300c964a010488140103c0c000340305250050121000564008040ba40d143c83c10301640038405540c2e06034400802140780d00c0ca0090000f4481c05000814240d00150800340c282c80c4c288030241000d012a01c0c00d414070113080c51075252000a0021080704005a00c0058200d11080100002845101141c0c60b051300015280420007030003640700d01000c000512003035070445e20090941c1c000b9200b00c0e00ca59160301e000a500e1155070320040c080200007074a01590564440c000001040503016181400e06840d40c014441c007640c000e40d079020031104001a001c600450280ca11680740780355840101882400003030442e4054101824607c0c0c50711030542d500ca030b040260b0380784101c1103041d0401070700d4018801400004013401e903004058440050303242401005039081c000d41200c52b0b00381e540c0c1c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 744726816 1250 744725566 744725581
    0xb0c0702120303010e0115050316020c030a150605040902031203192d1a0d06150b0309071a070206070f020603090c1c05070612022a0c040515040e0f0105 67
    0xe410903c07503108507401000000c141c3d0301071780841101c0d0a0080c0c40c2c440c110b895590400c00020000030ac0401180b19045000c80151b40812034822981e000d51440b0040c0d02c851211482aa070b099081b441c01942041140001070310001828242c035008012404e4481e100d500916464101904440500340e0614006035101c0030401058402100da82d42c52003004030345035002d8010b40c0c0c180c0c561201e01941011441c4031504050903950b01c0302d440340c00b00240040b5000400726104005802c00c1221600100c20420003290800c22a005090f140581ea51401c0055031583c0d000d1050f404003e00800b00405e9150030804000319480110354000e11083d1a85400d4019a6503100e181c540688921036001e500c25044c10b5441441a113950804083d04017181085001d49204c0c090082d5411190390170400381a55045910560000111007c000444121001e55540c903003804460403910030340c905014411012501550080340c1d000640f000702d12840d80700016400c0c03c0e00c0004020355075080404200070b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 744728066 1250 744726816 744726823
    0x6050a021014190b060d0207060e0a03231215060904090b06040b2b080d050103080a0809030a0c020f030a0f1b0e0f0402130902060a021f0e07030b0c070212 68
    0x10750072191200c000360f8807040502082d115064000e6400c500d0400c481c49114038243c009083c440d01414002c00c00702d441001c2a46040350040066002071a54041000342482c2c42c0d000307501541ca61400141844080d0502030712100003e031055003104440e00c0500c2c41511258107523a12184000c004004406060815118260303085610078032581c40c1401c01d80d014948400c43c0303407002000000d403c0386111410700d0f80f00842cac0f0110307064850039030621000c2d034a05024003d160207548118850303501d518001700064607540c80a401800d00e60001e009040c01c565001e03103c1c0403859012202488174016400100303080c90300d2182c0281c5000d010b20303000014800400d0507140541c4603056104441070350781e00d004010f00b40c182c0d4803503460308041000c10090b01d450407102d401c021601a002400b006240d000a03200d030302207a03150380560030440d1107184101c6451803a1454148581050003200c0c1d28814131a1143c41c00d0100601000d020808509514108825100d403503a007c0c0010300901c0541c41080d94 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 744729316 1250 744728066 744728071
    0xc080d080910060803180103060305030c0705010305060906091504020c012d0507021911061c0b090907090207060e0703030c0c06050412080703020c090c0903060c0c0706050a021014 79
    0x8600c12003900e20320495040c8560b00494120307502039800c1141e407541b0314510100040e0780604040d01e40c0c90220118509000804404140800804d0041e203408009400da800041c02544942c91a000300031003611104a120781c403221070035003d9142d51407040090000d006092821044d50f180c90181d242c030921503001c1d4010002c0710300c000380761403800c0b0302043c1c01d4602c00c460769001a0001a139005001d034802000c202002d218580d00410049910082862600302da01c88a2850114910f03287d489143c500c14a000c0013011780e522221450304442c1e15569000724801e407009076500217182014025964045404180781a06a604581e5070b400e004000e1007103250299a884180480020070900580440d012070300300e11174070510100d080e2100e038100c0c0c0120100f601076000e01d0f81011399640e10804c86500c03c14100d1020b50300c1e031190009061800b1002005003e003240d042150b140001e00020f12142108e94900c4c09540d01c900907941241070118031281e1040c0507060040b6103104580442000e071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 744730566 1250 744729316 744729331
    0xb04060e15150f0d2109030819030513030f0c1e030f0f1805130f1401090c0309050309041d19120206071403130b1f08030f090d0c080d08 60
    0xf14611400300c104600c944038004000e10344180e041c6032440301020255034a522010314105001c42641c2c07a19084601e030302440d00c7c1d43c0752a080c1c128521400360144552500071445a0082c0d0314000250707805085070548055032000d22001070141070400c00c0d60300d40000401e604000d0481c0b090510b2401400080c0c040300080c011a941c4094241111b01c15801e41001034804141da41c003551801c0140030b8031440340e46078059178540b42c8001d0100c04025014000c580d100005c0c280601e51307d800d00c0041164001c00350a8205403c1202c10300110b0310000c183d03140703120111000174561f071042c201f004803c0d1041c1d40c0c0b003142d0700903000482000c034034281c0c01000c080e0055504004880d041003003240c644004581020114911120005003844603c000c1c50307000b10008402c04d0400140e482e66807401601300c801d074107460610790f46540c2d010304590000c00205810002142403140440700804107005201080e40281d05a116000601c51f104100c50003c080b4130050396a074a06148005011003412941c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 744731816 1250 744730566 744730579
    0x6120b030a0809450f040f020103110c060405010e070308030109050a090c1202010801060903231f06080c03010b06070b0606091f020d050a0518040f0e06041a040b04060e1515 76
    0x2e02c00340e0030b0814261140c81030b880c030310301700c2e61380d558507c0030801e4a03c0b010381c101a580c40c3c118190400303c0008005000d02d4000030500b0707180a10302507007558481c14011589401903201000000d2500301a40e0641c0e6119801056a83d070741804280182200c590140c0724844002001441d100640101c101e524002e2369610030716a2100401d13141442c0c94030000b0444240e8082c10310000000c02213803980c0d201e90406a5050140c0c840d4403490b90111143c0c8426641c1e81c802d000c00252504210041e000402500248120700c040700000e101400b5501c0081e049100703000019410b80c2e03404044540307051004020408500e6482800d440084d540c210410152041481c10107100307000f80145c40ca0340802da910103203032044440544a80303190f119219034025440341c0e145020001d00c0d005044c0d41b2a045401071070f0a2400d411701044e00e00c85898221100301002c0c1c2030101180d40c03c01110750103a0010320120355400f04000442c50300055450551411031260300780440c0c0c2841d01c6218a035440200d600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 744733066 1250 744731816 744731929
    0x31b1c08070f060b100c02060703020114090706030e060f04150902060d0b120f0c01050c010902130905120306010f260a05090c0f03032b060b0406120b030a0809 70
    0x1486171202202c09010041a0020034100052030802d0040c841d0034401d00c001f10b0380c0142200380650036681514101c540d9000701400380b02e0306034540320b80c08402500718010061401c041070303403149804014002500680c484030501481044640001e00c1c010781c00780101e84c2d00c050031050b11004240d500c0009124120300e140c220440c007400211009040e907104050304078240000c0065074030b548000300910300340d52189000c3c00035903181c501212036940700e203e000c1402a0145001c40c200036402c0c4421103d01e40070300500c4a680d070300c658203104a0030681030007952100718406075a06d200f0707000c0c290f03440410707131101700b042c29550343d001280940c1801003110a800301d40300400424021a038040d40c0c0543c818001781000103410b6081c01d00303010006005c40340c8452075a610f80140d503070b00d401c46007100c80001410402680c0c0019002580d4840d00000c2005500c0080025161116000c02902c6020003261000c0c035640c0308000351000820039000c14001d00c84401228a802d190302d80300240c07a2072038114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 744734316 1250 744733066 744733069
    0x7030c0f0c121b0602030109090203010c14040303081008010f1b05070f08031506340305030412052209181703040318030f02030705031b1c08070f060b 66
    0x2880c1c03200700d078001c1044001032000041100e001d00105515001c1c40c0324021480082007080c4011800317050503901c00b258644c020300615003583d01d07a180000c20422283d0011245885040a07103054130744c54507002e2100c1e01da036010700d0303035519050308802d001c0d520340002e0192000103503112400d0010004421074000d00c009605841600400102415503800c1c900b20000080c000c00045522130040d101888643d00e448011510f56004950305100e541c001c09500c0390340811700c0081c0402c4600c00314601c20203110a6600414034080035000500d03ca003201010b402d00da0003001a00c023107444501c032038540541c140080060040f828420f03460182e140601c80c1041414074081480c1458100c0c100c5403008118018134091036100420580412010301690912000001e115030002d50282c0302000514000d40101401c0c41c0780d56110511a9008401c90108554107001d00e802c0f001048030b2410304151344000280d0a00340c416802045aa80051010104800403132010145405a6003c0003401315210 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 744735566 1250 744734316 744734327
    0x42307030b0102030901050d06090c11070803040302130c030e030d090b0a0b010504030b1012080409050a050405060a0c1e0206071103040503070b030c130f210b010509071707030c0f 79
    0x2200c603401604100404885c40d40620000c0030207840c10782000411711358401e448012035003c0f119042c0014640d14010303d041c5010418000540701200c0514a424a141d001a9500740c1010945564039100e00ea03a51289010707038000345072100c0c18020399543c0d1402e02202d400a14108604541c203004c0c44012030100c241da80b0880c2000c0c0700607140e5070301e010b003591545241881d008080c0e0444210309030021640718207540d804030b9030510a414894880d802c1c00c00c4542503e0f40103000000503031a200400000c07400004020b6080480c40d0400204406500b1044a55245442c12030b000b0740b41d034610303001040344d000490910640f40e980d41c0c0c0c50140e1405840136164400c5128550380741d84036030814800c96041400540c1c1140d251602245041c448030105078521010b58007400c040e03d243c4408100c00040107402c0e060a48104086569803491030751400c010a01c1030007414000d486c04030002d00c0d918010a0012040034884050300394603e44808010068225100b50b000040c1202012480c1a030052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 744736816 1250 744735566 744735581
    0x6050f090d021b121e032115060a0e04110d1103040b07180503150603070f03050601030f080f07060b180c0307030b0a1d0f090c0603071d04230703 64
    0x80208244143d050b408010b0503030034400c03140c0207600800448a60301030002d190044003140000241d6201c4180c0c10b4440c280d401c450184103410900101041148031001d441f100c1018000c82d5019241c50700450300311101d0180d0341c20700350000d00e04981080d11210035000340c2090300c0e0b050401d004120b00081c20b5075943c0020f40300145902c01c8000070401031406006103921040d18418a090700030741d00d03000245040c140420803218010392000f03111050034140910005818500707564a0300a1541d9a1250707220340501c80541615100504502084160b004a60f01210301c40c410988a4501c1d00b010f80c014000000380320b00c6040d030145441c52000080b500395100b400181080340c15641c5e0b0040070780c050082405000c1d440307002607e010503c0c40080401e03004050624030242080c2c0303042030b81c0c240b191802500240301a440418013142664070682102d61180481c60b1407106003203003101e01e23041e0110340c01d943c96000e41000f40d940e0200c00c4080e91404004881e581803e1039031a41c85d019812280e88 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 744738066 1250 744736816 744736843
    0x30b010602031e09190308120f0c07080903030403080c1f0b06030106031a0301020c0304090e0307020913060b06030703020711040605010e21060901051f270906050f090d02 75
    0x15404100388483c1c4800640106103000e0708689203e104402d2000d18008070350000c890714400811a50b100113480e02c2070302e27404519a43c101450741007000800c40d4074041e40d0300c0100b000400041c107481c00d403000e0064a0040d075008445945503007401007016100c0840b464a403403209500010380d050340403540160710075100054040d038596400c0070001c0300901500145007404800e0440c5041e4540c07805d1000b403180c0100b900c09140c035907042582c050156400d8080c807414541c014090b036005030381d4440f07603550040b4810700c408118108034136208001e00072002450f5404200801001101c030342580003484801c1c0308031094050510403038104804c40300305009841c00034060091105540c24911071603c034048100f10003032107a000305020301e890100e0444403400d4a17511581440701c0c03003594502005110348a8000143c1c81402c181007610f1108403d041d0908801301000d5138220030306554000005030750032120a00903860046a900009003050761036010a00c95516060450f52000c1084e6190400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 744739316 1250 744738066 744738097
    0xc08070635040b0703020c151b1e031801020c07030209012102100203070b0a060f0b031e180a050105060a05060f1e09100e040f0b060702130216080301030b01060203 72
    0x466031900c07420f00d803008164006041c0d00300140381c60b0800410444440009018801145241001c040003113038007621066441950103008c2c4011071040d20f03101d0f180a0109508503074580d031b00c035407404400b07254009500003c0c0d40300080384058007501203900019a4000c0d201d455040c0d99400604d05201302c20301c0b2070041201c500c1c0ca4000185048588102c00654601c1101d0410403944c40d40070a513101910814040e81d42c440c0208241c24042400340000c000c000c1e210742c110301d0f100c403150130f40050100190400280c4040007030900b58488807084091002d038011600c610310289801402064103035115072142da54841d0008503494020200c1d440c0c40c03803900b001810700e0300d235a400140c4500c1e03c4100f2064040c2c24400c4600d03545802d035101000c00102d03034560000250f0304d000d00040355444050301c24560b01f8600c0c1d0610a0304c41324121041c0300e5054607014203880711481d07030400900400100c1d440e0110410104d00901524102941c1600e0186400c240741c0e0742e03074003816a87e0b4822032003041801d42 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 744740566 1250 744739316 744739321
    0x2010f0c05010209191701020c100c1403041a0603030f090402090f0603160e0612070806040f0513020114190810051c0302010c020d09120c08070635 65
    0xc0c4503260380324403580310300005410042400f00140e00f140d05a00005202c800210f81009150034029520444d000306030021460a0300d1025410346076030100c40148500c0c1e8031070388512841841003050301480402000c8058036030900b03190680050203511071501000442c0c3c0d011480c18a408800c07a80380000001260740381c09409810711000e500f02e5030007075a100100e420601000d84aa00007180305089a0f00b1480020010000c0a842903413000e5201d0300542040c4940e01c807815051110341d1f04203409050004243c1e84110028010341041015040200d040030203000408104100c519500382c404d81b1042c1103510405480c12042c015407285200e04403802d03240d904914014a551504010001078a009081c0c6400205180368142c00729114040f44444040080c90750a03c9500000d01d0f50b8406403070842c2440b40000c0030024140510211408640607081c200014080004000c14600059500d02c5943d108050140000548034107030f10500c001c5c81c5883c80446002c07682c6030700325210755921a42c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 744741816 1250 744740566 744740597
    0x91e1005130e030706020c0d022b050d1803021b09090d0c17030103030203270d030f020c09100806010f08030f091203030f09010b0103090f0f0606030206270108040201 73
    0x103068881c0c0c01c0d6018001044114041562070005000000e4004000e100010b05100000d1501a20002b07000b40b691503000d84c099000b40e80001c01c05294410b140c1507031109248a1030500070301c101c2c1c00c2484007140d20300c040d200305500880d043c070a02444401d00061203541c1418003041620890710a02c098001a00d5003207664007a02c80214007502400d07182c06112080c020309003642e070003030b0001e4005d1307440420320407000701c06000010140111070f1140318100d0340120102d51010380701c01d4001c081c13190141503d04c0c140d10810a10010001c024401101802c120348448548003460007640d01314040c1c48004200d148603c052007040322401001907280a1100c0c0b003642c016002090b103203500110000003013544400802c0030303601551051060b40c10324140205014212071204002506050801c608580070a0032818001e40043e08154100d01c02101e925141c2d0013400382d44c00c0254450b2011520303080300e09a02030500f038102c4144411081d600e880e0001513400d4042214003e0004541c1142102c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 744743066 1250 744741816 744741821
    0x405090a03140f040e220c0e010909050604030f1101061409090705030a080a0302210709050316050915100c0b150f060d1d031e21070509091e100513 65
    0x206ca40c15010b89500c1c02084402c03080542c52110030b54000795400ea050000c8000e51002030b0040c00d91250412140b405c5039074103500e0b03080003440a410300001c01c400315034060159420026040084000b00990303900d800d6103011000c2e80316840742c00364110600150b903041001500341e060300c07401401022005ca041d40d4526407580500111810160244030042003880a00401d45604258003000c0c241e52401a20040036601540d0000c1c0c420f5000c00b900e062114140340d0317004265041030b80c1c5401307296a0044c070900c1ea40c0540d9901030300580c0c1d40c0c454244a50703104464002c031a10500c0b01c11450707201d0304c1403162070b8200040e4096228025189215451800340014014010714920104040480e0203880d100501c1050f80c1c842c847d000001e1f00c0020302d0101c202030607604081c030946420440f95420556200e1210458456084038041c04250000c0c01941564039400c0010310b0350b80780c0e19002d00c44843d0920003280e0b400d84880d40001246803130340c0c88001242a00c0e07003d0f0182c092407260b407001801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 744744316 1250 744743066 744743071
    0x30806040b1c1a01230a150507031b08071e08120604090b091e0303010e011401050408240601030902030c13090f0b070906091503050709050405090a03140f040e 70
    0x65440c8031001280c20343c690300800710300819008007003050009801e200f011181400840c8184030300c00e0880f003400b1a5400400c3c04800504610340292910000d00c2c0c2030b544030620b44055400d0b85041500a0b0800c04014010901a40308103a01070002c21000e610002c07007402441c0051180340240400b024404414034100e900440041010820381002e480b40312220105450400098200400b0b072095810402540c10404641c00021071456240c400642e48140c0107010342650040080c00d11025a8800d40070781d009064088180c5030b8a660307040e0401142119030b18103a0b20041c00500007507240d806441030208031a005405007006074401c20800c211036002d042d54419543d56500700401080c451455003107090300c1841104041e0a100d04054122540d0b0352181080080c016820b01203080000c400807214030843c14003280f2600c40b0141176807002e2158010540103071400381080003030100014200f1609010303490300d0f44284041444858148141041d192882e8010842003168480c0a401c1c02d9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 744745566 1250 744744316 744744323
    0x51611030f130816140f0d140106061d15030402240304031d010c030e15070506060a0f080304031202011b021501050a05011b0212010c02030a17040309060e040f060909030806040b1c 79
    0x2c420341840c0e1b23203480c9004010201d1209982d580c00040c407195800510f01e0311420114000c1000e8000100d0014808001c0c02c4403c2090b03503004004501152280700080070340c042d480e4040c03460b10207400f199405940084a0907400603611040303100c481c4000c030b00c0c12505c03018180c1d6100f5043d181c0d0346065410942004410381c2040e058804003020a090344094004980f0610180c107542c240344003088058042c2d6040210644124002040fa2140020460301100c0d030040c86000704282c0140d080c3c0c014607281c00e5000800900b007683c144e000e43d000c119201c2400503c010741440b42d0700c440510115511718060716020030118901c0c80d0241d44540942c62040384001c010554103e0741440b0301d400e50b5100310304880541e00c00704441100d29000002a001444844d000c07070100d180c01d8078020040b22071481024184241120740c00040d4130349800c2885412059481800100d9a80c0f81c058010f1441c2c9409500080c07100010a095182030300440b00f80310b9009040800d5215943c1e480c3d07444841059088 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 744746816 1250 744745566 744745579
    0xf03091a1602030c090703140a02040b1e04030219090c1806050d06051c0210030506010e040506011815020d020a2003031b010618051611030f130816140f 67
    0xc13020f981d00c028101d40f0882c40c40ea4042481c50071044110380c5924040c0242e0980e500611040c00980d0b04e0805451800030321410604c402a8410504071040c861170700080e4125402d00d8030003100c124007014240888800c0c1100308201c500003501156280801140141d540c2c450380700c200049031041c0c2c0a07080d4074215050004c2c0c0c03242c1c5c070070018406070884900c50a0300c0740307140d0420003503182c80300450540c42d156081c00d00503890001d000074a03000709203106602c40c90340c070070200302264810b410b002074920100307810b03038051601e820b1a500d521148442c04c1c401845001c010264036440411300740b0b2400d500c1403078845244803807045810315460036043c1035094442440201000d0b00102d1921840c2840d02d000003030907d007000c414044c042000040d14004074141818001c10300c0c49103800c91803944c090715100001466000c8424110b111b00e019114480d64080f03a030491038280748182c4421144440220340c0c0d407142154042c5c480c907490f07120780e00c160003922403a400e550403c105501100c06006116 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 744748066 1250 744746816 744746833
    0x120207080601091a01210207060b0d03021c140d0e01200c0c041103150a050d0818090613150308040603230129070f0f03091a160203 58
    0x440d0300d4000268000300740c044c1c40d91441c100050102c1d003c0c45190500380b03052041d45040081c0c00d0103e501280b01040102c0d40040c0b1201881143d03480070b003003d90b00030f12400c0348040da810002c0d0b581d5039456a0600c111458103003003040301d010b21502c4003c04460480c050800f00200c0702900140b140d004004c007155219443d500300c00120885c03590440460350041c03a15003166640c1c2610b0400515031043c0107616000c12146d1180c01307801a84d90021040c5200c450300c9a050000c20350324035079907101c6070f0001000c6200c1000c116840d07028120345442a1070707125034404207204104008030f003951025001b082121007031068101e1034211150081c28a0300500f101603584d5207a06807913002c0e50000f800250349100780782011503003a1980a5240400c106d418142d4104558502c0074850051100460094201c403c0400065041074560036034005980d0700c0100542e0070710ba040b11130145021000580809400700d002c46401c4081008124180081800c0c6400100040c450180100c000d9074148107800c1c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 744749316 1250 744748066 744748079
    0x222121e0501181205030c030a0e0f060a020405130b0d031112040e01090b0f010e062b0506090901050f0604051e040c05030c2e051303052404050a120207 67
    0x81010005245a41149030f6115007440e0703680070800301c40b07803041103410024042d00141e820245d0360024491140000c030b01c0e08081455240c0303022560b504c0d100b40581c0041084070310090f40600f08641042e40d4080098001c4a03054040310652480325611601054105001c07d100300010701c0540c061104841284c7c066010142c40c0c0d800c5179100c014114500c0b4014001c159050140d404110019607000a20151001c0060b110291104240c0d0041b680416290408440c61440700b007114602d1484121400848030401c0c05040201da245010304110000b20307042c41814400d8038030881d038080310008681c998400300000b505001d000380445103a46814440a8000780b120540203601c41c151410340141382c0010b25013080410500c19108410142120f02c00d01440d0201200241c12070950021503491104282c809001d03640041580340300100c0040100038000980c03440000301300c014021401e92681940c9101182220000d2070354200501a8000076444006186291068016074100c1a10303000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 744750566 1250 744749316 744749321
    0x180a0f0501091109041101050d0204090f0912090614030a060e190605100212091c030503010f0b0412030f0509040e012003040302150601050912010222121e0501 70
    0x114291032596560b0340d0581003103014065542c0e101030a0764004800d1802e0346814040314a1562241d061040009240c1013109031581141c0103000800e03c1000214014401360700203103944041201c0716115040b080c541240a03810f05411504503958140f52241c80750b05507420740d040908003c190729140c84011945880522041c0d10612044040d0315022a1500400f0196045540a540603024074190041c01590210305006142e081000341c2d41c4e1000020301041c445510901400006031b00e240e0b4840416a025000b14102c0d43c1c900720442c1d01ca600c4001d0900c00c0c4c0b046128003260005040010310020380550b400b24802d01c264140903040541080204045d00c441d942c00d58810b9540e82c3c0b4116910301c05848041c1041c00e00310409040d46003681d800786d5146001504214030028001c00100e03640c2c481e00449142520160441403400a8000c0c1d5034003070341114000845013103019128030103902040780e41200b02c4680d40308110003100d480e00c81c01000a0704124249140d20b01d46d006c800865402d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 744751816 1250 744750566 744750593
    0x20f060a03020c06011a07080c07032405060613090f060e0a090314090f0d0c05030a0b0f0a09080a14280f08060a180905121e0909180a 59
    0x1501c0159980282d06201c504200058110400b40c45aa801d10482080c61000f07480ca51030b0300500c1183d5480e0710103080e80c03038044145c0c03008042c2840341012445a560244200d03a04440309401406961925800c0200d28040e848403030b412495003c10401425482d60414140d190110a0010300c82d52154801c010390f44049954042140d00c0b0400d110400d41c0c480d81140504001e039194504142035203002a1881c8a8000890310603146442e030f8a0900c00d0811501009000c01000c0340c55011140c80c0280c00120700311910362002c1c010100103a45c014042c0140414903906c808014038154201200761400d02100a00c5070a2341824030084118610100e01c00105031038101c001640b1800801d0700600c1c05103400980c0040105134402d0020135120540c4880646501000340c42d80e103681c2018020092000304c03009000c52150803490042440d01e40f004080c01581c2c202c004181c03007100d4801d45040c3c03241e1140b090300200a280011440804001c0d181e031445007040580e152a24240c40d16101207500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 744753066 1250 744751816 744751837
    0xe040f020405150301030c03060c141c110703092706030b0604052203031a060a181703030f130b0a0b091501021903031d03041a0c030f07020f06 63
    0x6040c0b280c1d182802d02e0b000b03c4403203449201d18540c1155a1501c01061a100c014406034030307a818009518081c8421107480310071a03a40689a440348608080d91704214800031030503504c0d140041d4211881c0400b101c81760358154480f0800036242120b000303034030072500c2d8188514901810b80e40e40b012040b80110402103010f60429601b03810800108812194054240406103401c0780d1601c42c3c4451699a440c905c41e0075040c0000d0741c0601103a4550b807043e41c214095400f4600048001046030800c40c01004000c1c25940b2500e4141c44d18881420360000840507480340d4400e20010b074120124140c1e10382d12080d10f9030425000000380d55590600b04003078852002c03864a90306c8030021400c00000381d9910109000c0c60343d000c1d0b0640740c0040c0d00c401822840c0350116041c0c1200006040c02500304000d10070038100004034641615100c5600c0303402c5806421308450400300d41c001101112402d40343c1080e0200059403420380920300d602d441e42d102c0d840498000c0a1505480030b2540da240c06460300164 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 744754316 1250 744753066 744753071
    0xc090934050d0b03010c120c03020909090d08010e091b1c051c05040b040b0d0605100f0201051807051c051e191226070e030f0c01020c040c0e040f 64
    0x112031082006443c0d007111024002d82c5802c05110f8415402440440e181c0c1c0c10f4031000880350740a4604a0180c4500c4081980101082040c40400ea00004500b030603103085585810440c0d8940c1c02c19210b040069600c400150320090010349025050141c8580b41300c0020450070a5038a8000c4141c021031350b495040d41d241e00144000d140343c00903500702002a00b103619003e881c0038104411084a40180d000b040b08410001c00d012420b400b0b240c1c01031014100c010300c2d9540f00c0702c4881005217540c2c40d01c401c40f00154200340205424004001e808403208918101074241141010203108400c601d0f8050150380044102c900c41c082442401100e515245020004000e04c1001c01400d1904811111601d03440301c0c0800e084011400104e8034034003030865440d003d0440304500e001c0c1100900e0094a90543d0f8000d01c05002038142c1207020b10842c40015019107400340000050f454684140041d914090781003001c2c44045494194000d08003144107061a070541400c081c045821504a80301c0281800d0303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 744755566 1250 744754316 744754327
    0x50a060b0a0f03030203120603010b1e2407030507020d140c01080708040506010b090420041d010608010501200a050a14010605010203071b0503150f0c09093405 70
    0x5000724054054103100750940d042c2c2e86560340081d924407a01180003005030111004c55001e960a40000000c184d000b040c82107242004000d107000000c001464605c200e0100851084514003804054502320300c0d005002d00701045510b041c3c440b0740c401c1300c00326881103c426006000880150907000248042e030014009400d81000160800ca03019000d003042c4019001080001303040010a0383c1503500d0b0b028056114800d40001c02e01502e080c0501071280c0c0c4400141e02881480070020300100c44665103034681644c580d42c90354980c00d40038042e8900258100c80180201e50003015483c1416000503008041c410b0741104207400c0c80f41182086420790424034014042c4102454800502ca030b400c030007001668a4100040e61b684030b03c001c01071404c0f58101364034420940102c0020010320b0080c1c15580e0944410103100c910400490b501555400c0c03807008640303400c0540b0195481400081e150540540b515007040c54205250740d10200850a404681c503a01c1000300e8403000d2102c245c0d107860ba200c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 744756816 1250 744755566 744755569
    0x60305060603060906151b150105040c0c06151508040b06011e1103070b07091d04080403020607022101020c0c120703020907110706050a18062109050a060b 68
    0x6a1014003014030400c01482400f11503558541c6440d0045811106060483c1c0c464103100030134040c0f00c0a048030760000301d66040e41c58002160214501034100b1440e446c581e203c4040104413404980300000140b00035407130310002111940119406510001664101036803240c141b00c40901c003201d0b000002d000c80042c4001c124011441980000c400d0a01c10f200e60300c145001161030503c010030000b085540c8030016240101402103c1016403c90350316081c9103000607000e4091001c034855802b8071f0000240b00702c4170300c403018615800303150710800e45c80c80c20b880e40c0c00300301450304000400d0303034000c07407a1840712401c401403030202e20745080c81c0c00091b0303e510274030448508000d406001503028002040000f94984004a004401c2d0395044401110719101d0340c00c1216a40e100c1d5110031180d02c0340010200340d00e500030010304060300381503039000801e0300d0132407001004902030702c00d48000c11544d546040d1383c032420100c1c0808080d800b510000e41650180c480c1481c2c6206000152406660345c00000082d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 744758066 1250 744756816 744756821
    0x1507060b0406032607150501030b01060903051b1804030f0e0306130813080105010303020304150e0a03110f030a060b032e0510051906030605101d0301021605070603 72
    0x1081001c40d41007200038510f031206800061101c03001c1c40c15411010094400d0301c2e40308141c50401d5009100c60800d150326424540003000207010030743d80300d070740391000041c0b2a100d881204240d036031242c0540701d50b103e000d07403080d0f954440c40c141c40c0d44a0010210355198428580c110ba11450090b40c40d5200809119009400020b0702c41c8140c1c02a000482000111200b207030038581100d038014140c03569400300b4603070301c400000650020780c1c00d942408000814168002b01410560791117154071400080300e0081034a412000c2d00740b00d41c00402003441000443d42c1070000305018080945243c64a01c08640001d080c203d0030706049810742d5541000740302c142803c100d80402441c4091100040c041d404032140c0748100c07508500e181300c83c2c55500054045505c9803044006000c041c041810b8003211000340c1040c00d10a02400340000e2400c1030018040c40c0800307048111060f00c0e111442703a50000e410400214000080345901590200105201c0700203100c105100540504080c1007540e061440003401d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 744759316 1250 744758066 744758081
    0x110607021c02070501050f0306060c060f1f0806041b0807170d05030c0720090903031f05060d020f19050703020708031c0905070320010206060a0b0a051305150706 71
    0x4643c82564140104d0741c000f001c03a07850360700e412942612503441c0000241c0078810801c02a00b280588000d0100e0a03400880d201c1c01416015040b0b00f032a100340f000c0000c151001d01c65018198800c0c4003140c046801c21072072900c010207800e2540b03042622034000314500702490b40303d0350145024401003241d0303030380038402000343d40345510300580b85040a0003003076007d0180d842d01500200755a20307003000d400c4074444400e0003200c01800710441498015103058032a0011903001d5024042e154000c0d28810807120b281060310b5008051034203049440d51184000d402ca41c000c4080d0860800c030100345001181c00d030404400d0b240c1c2e1869920815850000c1c2006850741c0016941da00074000207404c0e0301c02116400b202c1169074400140e902d014244940f81c030001d940060170302c4d000c0e61030315094420200314007030313910100780c0803140961140000c0c000d910301e19100d0000d003007800b841300c219014460002410b081d9005403440d01400e85070000116103075807510340411102000a01001002003a026158 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 744760566 1250 744759316 744759373
    0xe04021306020606030d20031e0706180506012304060b04052704061e0f06080706080c030406090309081c110318010302032a030402120a050709050711060702 69
    0x1086c0c0c21101340181a01e55094a9402d0200040c40940c0740503d0420644212808d0030345030f070380c039680c018054407800d62191b41c00f900e1302810070110030900c00e071115000c440c5943c048000c01c550b038a81a007004442e08580784200340740d40e05808900d080d40e181c1c020400900340003280c40f55207a20301010072241c294001c2c004130180008000d207440c17041660719000c1d40150400d8002c544540310455030201d41690600c540303035040c5003070f801400041c0d2640c0200b080e02c1c074070403c48120fa500e8010035074450100f150703988501c200401c0040c000610316005801c02d9446800c200e074003240c85503962070a20707010040081005411080321401141c0c0560703451850075601000d14900805030700100c05040840340584d042c1900003000ca40c075413048101c08110740d4504028080c022a644100b40025482543c081c2d1203207910a181500c82c4c8008103002d900c0e1a44900142925841c1400755000b034407005000806000c20841070a1058100780400c0303101c0c0d45164040e00c040c040c4900080009503001d00c0e0301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 744761816 1250 744760566 744760573
    0x2120915060901060c080d09060e0703020f040b06090411090303030106020607090f0b070219090905100c26100b071b061b06020f04150914010c080304060506010e0402130602060603 79
    0x4004160700f20039103481c500d42044034190b4031f440801d20100500750040006207640d10f0f01c503191104d00404140300c0300341d170b108a07240044c842c004c80402c010b40f50948025039020030100282c00d80f41c03505034010b60801190910090801c00094002400c0da0801da000e0030160b000b480c2000000c075808164138025080c0188050031150070541c1c40700850040c14402030240400a4200301d404240c0c2c04040010a00d02074240800400ba14140f5115080c0ea00026822402c250708080d180e409801c1c0e500d0759120b03e0618482d0800c0d04942080d0b03858018010241d00380c50070340042401d405030002081d080c0e000d076591200701a070740c2c08118003140e0380e079004104216602803c1082401c000c0000ba00031030300944007684506a40d00c0d109614810f6600100b414800d881e1800c1000f50481071890444000c400f981444130071000040d500c04421040040683c6010400180025400c0d40b103e81c000d1810b15144814200080104049a001d001c8911407018407050400c4100d6040003017503404141135024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 744763066 1250 744761816 744761819
    0x903030f0c0f122a0a021507021903050c07030308041a06010e010c05190303060819050d080a0b180a23150105070f06051902280302120915060901 64
    0x3255260203184000f8150118150204080300041d50020740104045a06103134107074880c40b0360820580c00700e84104054052400c206a584a5501d0540d10070390282d006000071448003020245c0f02d00782c10808805102c820300c0810042c100420200c1c0180d482512003603c0b50910b410410000402d0aa04150080809007001400d980c006510140880d081c00c10010181030344c40c00328205803044980c0040d0400ba10140d0082c9030741508404101d6420000ba02e10952803030550850640004502902c168842c0440344070092207000116481000c0a60002e103095203600010222440246401c0d800c1e4a204148406000385105810800405203a0034400250454080d168079200802141440401d42d4410f07515034007500450b085035a210341600c58020311071400b88014203081e1180c220007140f440c00f0000e4401c4a2080b607400401c44403440e908689039510040c034a508088003041010b4091220041e107000e1043c800d405101160054903421051001c3c61109800003000e09210b194200c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 744764316 1250 744763066 744763087
    0x18020109090203060a051315050d0c031b15090501091401210e0f0d0311040608040b0a0e0106180b0423090a0c140907091401080a140903030f0c 63
    0x3030310301150030700c07000961aa643e80000641004070345c0e0099030001840240021881b840d944031036040d240c82c0c0200e0081382d403244184020301c071000c1c50040c048040040140702060356009500710400024080803d005e449134064000c14180c0a0f58101040c40d01906004541e0448850700c05050000c403003c10002c03250b80020041084003841d224183d000609400540c41f483d0814540900000300721501c88004012869450b02000c00039000240f0309609052049a036004590465466030780f0001151903c0d120f102d084900509290442c90390340310300c0d008200c400e0051034010152003511000202811401500356529240c0e114400c519045240503c894928810249a19038401d1004255100c9001d2890081c0d00340e005810319549040c0003071a6407614480d94202d0b442940c804140740c17980182a20000b49078003034140c0d410194103185180b9449020155441000118041181c6419002c0c5c904813440555492903c0d40000042040451980d40307420340003014030001074904180c801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 744765566 1250 744764316 744764327
    0x8090f0c0307090f09170415022d0708060903130b0406020d110111031311151608070602280c11090a1d030901020c061303030507020a08030a0c06180201 67
    0x850030b00c65a00c8001c1c06004413181e01c07180c500c82d400600918042c030b802006a043e41c100c4d124001250000c0e02030b500c141032000c10000b072410420641d100003118442c004991024000e020030216120f50301000841601c2041207500403050b170700140d5910440400c640c0a01c200607004202592810402003003100d0307001840242c46001450281c41c164100c4981c5c40c00347c220020808040c090100600c401c12011400000f103542c450650038180c006488188503007a88140c801502c640307001e0020507940103d82040941480c0f1a05031030b490f01426907152004c0741c00007804407030408590304802c4d41049412b507066920720418180040160b015a440300360b650300c0c008195001d100180017080107045150030405241d481a0b20304c81c05c60072204001a66a080881a54018401d04050303c600b4207003502206e182581010083d113455046072000c0d1b520b544420340c100d03040074440d280052180e50a00180c100da02c1306645204418440303090034400e9896803040100c0e26403030813080b040141e8109 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 744766816 1250 744765566 744765569
    0xf0c0305010e0406051e011401030b01020a0201080406050c0c0a1406060316180b03030a0c020f041e0b010509130b0a1d0f0403030b030703030c15090f2d0308090f0c0307 74
    0xc44c0810705548142403451205080b1840300003e081140011804044195284203031035001c0c3e80800c0302a07000d0004a90701c1480001c0640450345040208000c102290449035002d04070541301442c00300150710543c0b400a140f203054070086801c2403000011b2314140819034129008800500c04440c18080ea008203458034032400c0c03105242007136002d089402c41e41207040d42c4000142903c2c1c80c0d140e00d51018254030300f4540c0491052051005048051400e882940141543c00f1240580303405000c80d41801001c1803140c1505101c020b100202c9203555800440301e070b9031044070020031000086d07014005007100603000200700d100e94103014015960318680d4203510000c901d100981903181c0d803c0640023401d46000c07881e014010701c90080b0034035420030301d4855018861032007208000f0450150304112250803070b004016072180c07044203001c510680e6a822610613004c9841b8091030851003040e1806101c00821000300310700d00c04210038043c084c060b05615003800005000e003030031b0490020341c452955 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 744768066 1250 744766816 744766823
    0xf080c070b0711030d02030d150f180c02030f0a080a14010b190309020d1b0e15030c0a140d031205011404151a0708040f0e10090603030f110f100f0c0305010e04 70
    0x9c80307800302100e03003c0120010051048440c0e900702c56840e02130040400b901201c0000700b41d400c3c40040009244008100c0d0074240c500340c030340d5040146000d402c8918680107400c40303590a48400112228194841c4c10b01d00815050405c269942141c0d80d90504c000341242402e1305042c030704159400503896810b103d12106038050038803d84503c00c03070180340003401150424142100c02804112118110702811464454100c1c1259110700b841c10802111000e1405121700c41c401c5404405c540b42840d02145801d0380c440c4c2400e070303d005c030b51442020480d60240c0c425510b69005c00f00804503401d081c440c02d0030401401c002e0711300c5103050140441e03039881000d503400c0c0030203000146a414440540266005011040b44005016682e801c08100000341a640c15a64420180000800740058421141200d62589440e014116590010b540e980c0121440340c0c07045c060f5031100304150714240b2108400c0610910001558001c05400f402294010a0b454042c18682001030001150b0f940655034007961 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 744769316 1250 744768066 744768071
    0x1e081003120320091908030d1d01020a0905090f06030d11120304050a032c06130b0a081f0608040b061807120c14070f080c070b0711030d02030d 63
    0xc001c00201c004000c2c09418801d02450702c8910301ca104048030003004d11400440704405603070315503000e05d010300300d0303030300ca0541d040d403041102040d40d030455004171281d14206d41d030310020b5103010b8400e1800c0e41d210310050f80001d404014103010616045031034a030005020680b9111f40d207400000b10365643c2c002e03501d00c024000a003032041c6000740104011080a03640306102900c0782414a0000c2da00c005c11001280458403140325144101c8281c148440c0d06154500b96250007048142844030130f0348a44240c4100040300900802c1c2c0300c1280c0010300d25010303141e60300c0340c642c90701986000c00d00036150030b195856008803000700000c640c040b400c10780007030f00a018010180c5030300000641c4004069803041000c03c4160400c01501c0d04035009001d68148100b090104449641080300c01d40303503418100481c0741003030103c0d00104850b9017000e21641c0c03040d041e0f14944864922003a142012646c041c84188a000507008100151039986a071654001e4009202c1c7e00ea407840c0181d1a400761000b00b089465 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 744770566 1250 744769316 744769343
    0x703020d0c081317060a0b060406110c04020a0e0109081b09100e07110f150115090819060609060609030305030a02040306020703080a0c0206090c0607060e0d1e081003 73
    0xa8004102c1d840000f01d005207242599440404441e90040c0c4007080480340110f0001945a03074080c0241009850b008007540e26203810200140e40c042001d001c41c900b5480740442c0c1100b96140ca10041c501c2400b552149140c03000390000040c440d409980100c55203400150112a0301d402c2d1107500010341108851150041d035034810704030040042644000701c681042814840700503000b0b440881024a4517060300c06058215070303450307901c8042c5011b011181002200401100c43d8001a2221944403458882d40803541c403003030345203480d041c401036020862540148000300043c0d4882c941c018280c0704410300c4403d281002c05405d143c100d100c0682070200000028603c40318681c12500690b500c80300454960040b070900804030a401c0f52421092480c0c800350a070403e00000c0e400340b0449881d0010254409180180040b1303801403013003100c8883c0c44d80a0b40c610010240101d0020300007903035480e807a082400240714401c1e01c48030070710400c0c003a41d00180101d802c030801091040ea07800607000c0070400d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 744771816 1250 744770566 744770573
    0x90819053007030504030b0a02040e07050906120103060606020c120601050405190c03090c09150303030c0909061509060504060804081809070c0b151c0516081f020703020d0c 76
    0x64072401c14105040c0400280e540400d80c200014105490044010400079681c11410b04101d00c280d00420095820120004988078070400042261802c0a42820305041010b546001580400e801c12101152142000c0c05041d504100d0705980100c100c0b450a0822140154182c40390810b003d070300e014a45a4000400e104940d05024040e034200708070030404002c0c01c1030010014070051404a51200c8480c4000421080f40c1c002c0300c8800382d40944036641d130b03491644c06030014a03005045030107001d0510b60008010600b441020024648500e00c5001d4601d0403000402c0c086058000b2402d06c0001d000610450f030713000040f164050391150071503983d1800c8988000011803400c10066011144604104440f0b6200c018081e07514414500802c1c95200c4038504800c241c403603040540c0080000815541031100d0400c5561900c0c020015210344000c07160b00240c0303c00503500310380640ea0000c0c1348520102a189880350100658101c21400e00c480b03a54000d413988a2449500104203c80b503556050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 744773066 1250 744771816 744771883
    0x1d06070b060d021302030603070b0414040c11030c0f0c0d0506190207081b010b01032d09020303031e07020109020108010b07051e0d1e20070e0709081905 67
    0x1d103400800704103961000a0111001c6d5104503503a0b070080c040c041c40041c01144a4040c3d8003502d561044120300d1811400a103c0208204082c0d4030030402c0003170540c6030440f418802401414258006480e13000a2501164904001040018003a510061042c030110b03801107103094022040c4079003031a0115080c142a40a4080e4400140120a002400506070707d0405244588188004005d00045400d10015000c460b01003020b54814414018055415280c2d404070a520a007204130000d4038400980100740b41d5002290003188080381d03141241c1d410545803030850340c0540584003e12614910740d0008200369018481d250f00490007048003030410100340000d070800510f402e0030919044002d80456900c1044a403004082084440c1d0002404881080200610705944810b01a001ca0015040d06610020440d641e2800b5900b00416004003c3d00900d0060700726559070b0304210306000006041c00c110000c100d1800c00103003011400503801040c09000946004407400210001c0c459a180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 744774316 1250 744773066 744773089
    0x40f080703030905100c080601090b0f09010216030809131808030903070b0907090f0605060a0e0a0b1318050411040e120d14010b0705100209130213061d06070b06 71
    0x5a07004050300b050310002150306c14110380da001d40c2d40021917203078000190740ca6055405040d00541c2d0402030400360140e484014400081e062044400c4016000c040f070b44419402c0e0412030f6120070010b184542441d06054050060964500402402c2d1100e1880d805e0a11104001080350401100043c10030009005444d0a60b4015800e0480c620b0031f046d480b40c48950760300426164600e4950301507445c504030310415050ba88041c0c0201e28114402c80141d420001c8082c500b6480350840354045021910f15014003680982c4c0712446400c00e0500120034413a0740c2c003140d216142450501004049002c545c0341e0390a440c4c060f40c6c0000c021120350034803400c2507081c007006180f140c0001005421000c1c0c03a841a180720700003002031506030340c8444401d84103104005024149910901e62842d618120368001d000000c00104082c00c0d0f00d161200d07003002d0360020103011103415140d1100f004040d0f00714144050b000c444020001d035030100c0310f00007501d0703003c0d800c0050003071920940045d466445201e000c41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 744775566 1250 744774316 744774323
    0x31a04020d0506211e0106081c1205130b041b1202090601020f1203091c0c0506060105091c0501110705060a140103020117070c17090414040f0807030309 67
    0x550301c542003507203000501010f45819025200c0b08591042003040d408400100381268000b6142c0701000c842c0c040c030700c2800700705110002d550307841c0000b1720158108440581f030030b1180a04403484220b4200a000c403c0962400300d000760521042050322102c05881d441034540c0041080c0e42c83d25641004420345071001e0113000c0c0b090002070041003c0a41c90342ca40141442140c1400f00b941d114401240c5865001004130116406400786040d9011568007955001c024003044030750642240310300c20342d076014021200c1c021850503070700b00042c0001402941e03813106080c00c2883c0740c040d42001103090041079480243d0800c001003404000c0200c00c2d04a00611254140c03032507180c410034101281c41307001c02c4c0d400d42c07149031800c1c036584082402c1c40380c55812250141c44030186a400243d83d035500c0074000301710310101303d81211203400007407841e824484698905016a511a480308084c0030403640185140a541d00d000c404100c002040301c10001886580310712844e4640255240a5016014008004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 744776816 1250 744775566 744775571
    0x201112208010605030703240c0e0108091b0f06220f0609030b0c0a020f06040c08010e0606030c10051303080706050619060f050714011b05040f06031a04 67
    0x140010112440d069200380ca540584964603952020010308807041c03482003d815412120b401c00100342420010160140b0f2556041c641507401c0f001c020484480c10341c014041540311520f0441964000b1010b0ba01048820041c4a542e146c100403590009540a01c54480d0302e1821380e81080380c450100341d54125001d5603e050710140244c0c00c1800061141c000d00f0b9860800e0840000d6984c172898405080f240c0050b0302c0d294903116064080d07240c4c1d00140102d410751042ca81c0071404448200885d334455070045016005190030140c049003516401c0d4040700c0998460410700959030f4000c0b4600c4050041103403818105019582c007603034240100401d440c281c0000031000010b1151000040148900c0b8680c100101e81e541c900b00290007440c050843c0b40c40c0e5071028280000c03400754480054451075030030300a0030848150345020115590380914160b07030b5103c5540300540014640081c14003401d50620780d06280c10034020305419151813041408042c1c0b2100d03203c0901d841280801580003014005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 744778066 1250 744776816 744776827
    0x203120c0304031701060804080f072901090606201501080114060402070803060415150306031205070f0b061309030c0201020c15070b060f0607031707090e01060f020111 74
    0xc800c03160800c03a010360100d10081d07685908941003482d454140d4825449583d200d0301d503502d81061070b420210715100090030402101020032800041c00c41800c02c80710b10a5070840911071000350300b06c41a07020304040c504200f414000550010b050759841c16000c07006400221940c01c481c1d01d00540c00000003c15003594001180298064002c4941c0c0103421600360303507a440d60428841248201103024007640030500c045000da1805410510075509413040020190b40c0701c62aa04a042e105070214001c41d40c0c44c1030410412a0300b0403c19105211400d01034103014281d200c544d0204e91000e0000d0040054100107903650396100780304400f41c2000320040203c1082850050056070040b40142e0240c41580400202d0b89480f000c0c04414500c0008070f542050700300d0351542802e003400b4046d40d130301241c0d0b071907100959158440034007a001d00a5403500059240c40d928a400400f000d4480e0003048540e16043c040e000700310074140d0440c0e5252410b80118101414101d00409001e100e014502c100000c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 744779316 1250 744778066 744778081
    0xa09050f0f150d03110715050711060405061614060106170f100909020f13060f0e0702030421150e010b0a05030c101404060f1e08060f01020312 63
    0x5078481d04041807032480544800380440ea0ba800c2d4442626480000c05140700c0000f480780c0400c29864030940e088a00c45902d9a8500025001c60070020000030701c0031a030030041c48001d0b810702000f144295613082c41d007820440403901c14850707484203601010b039100c060400c0000032585500201e031900b09035515541c503004000c0c00040c6500031051041120f0700880e0542d40240070742401b4211600100303424901c0e0882c2c0d100500369180050340d00002d0064001965103441c103084980004448000417520f082043c5040500040d03000001050310040c01c000b000394001044030140c40e03c95848981c0320310f401c42c3e00407441019000c02882c0c0c4160440d0a206400e02d070b0415000a55a88000c2c040d01e0902c405204448480b4414542d15500c0b40c060540d16042c142110b400900c050314042d181ea11425064402e01c1d4407980c02980059601400e04004a5001003040080303000385c01201c14007400c03100300801229001c0c09041c0b14030344c801c5a038801c0f40e0081048540c80c1a8191039108580381048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 744780566 1250 744779316 744779341
    0xa0504090c080d051c1406190f090c030e070608010320041d0c0f240f0a020601260d0807180f2103050d0911091320011d0a0905 56
    0x201404904c80b4940c0320b024101a00070011401406d5034111155602d1804201d15400c9510240c0c4a19054110126841001003039101c080c0400c034002281c1c50300705010040440c0c80c40c1e0345546031608000e20038000e4680c040c40880c1101d0704244c034511040f44051413011000c81158525500500d4070240d08114a8240700e50b034240000c100c190b41e003140b00c91081c4060f540700340e88101e9003c4480c0c04103003044010440f02e440e160000c4040315042607076280b20388038140d010040c01d10141e03000360b00400ca07044031102d03444009080036181c02d0041da0702c0111a60399400c602022024441800c00003031040c0e2240220b04502c000d01172004c0490360b42ca1700b2000700e40141d8015a9400039041141641d90301d40300a08001e29540750745ca152800030b03d180c61b0802028280d10450341e8003c81c107050104d80c0d55860380640182c00c02920010200e01500e4000c51a403000050380f541510a40c100b480641e80001c0c49000080a00c02401221071011001422100ca2a04087c505514101c24130880c0e00100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 744781816 1250 744780566 744780577
    0x30902030f19020618030304080a0b09070f050108060118150e030610060c150f05070f030c0e0402070c1805010e071e2f16060305060a0504090c080d05 66
    0x3030382a00c0400a0340d00c0700c182c6540010101e0000c0e003021082400060030b00c03400510b00c1c0e00c880c986003000c0e008240c1c0060700b0b640c4150f005600aa0002000714107112700c40170140d400c40c02d402c0007004a1454030a0390b28401d501442043d0500040703d000650b0b69000340140092030341100030500410751110035081955000e21031820005842100414017401d002403403d000f07021000180011600d440303802c6030300c101c8105085420b444140568050003445000c0c0308980c6824910105152900b0b400003403007002500726403010542440030111185030080c010090f104004c0c1d601503131b100305a080104c0f00344140e522078000e00c079103400742211041c42c0fa8050350680e07415a51b502c10740d0321034100444000300c000c002e60b90340c44950025009006d0050960001c0d0203110a1030350f841006081c254041e02e0f1070420b0703c411a810005d07080c07003200000c0d09000090480386c1010403160510724049002c07000180565800355540d20342407000c1c0002002c0c0034004000c164111481550303000c0004100b41c001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 744783066 1250 744781816 744781819
    0xb04060b041403010513062a020a060506010f17060411070501020d1d0606131410030b0606250c05031903080115021f180309031205130b090102030d05010303030902 72
    0x41c42054002e03107810b028450244400c903551071100c441d03039200c42d80103041503503a51900741c010040119942071060084143e0904940143c0920383d403500302481982c04c014031440c1001505007805a0f41c3d0b82000382c981d54018103e520856580c0e0301d001140042c04440801c3c50300803800b0034500c08020b0150010003c03025840400c1c040b50180e14100b083d40d0421207402c0d1390035040b640006559082107004592a11a8235101107030454503810100c500c82400c0e5000e4480e100c115070188180315041c40c000b900140706441c014504080301d8400308031103584959003d10031507074000d80b4043c8000701ca001000b4180007015115034090441d001403042d5040401100454003200000032440c03030300441d0041400e495000760500811500d0400b4080104d401a55512a038485804481c50402c4054001c090702c00d480309030311641141441c016803c402035030301082001c20000240b00d05013141456040301c084110450f2039404040040c0e06601444000a00240c0340c40000018980c0c95004030303071020300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 744784172 1106 744783066 744783089
    0xc0c0209010e0f15060d0902060d050c0406030608030f3a0f0e07030c0315020d02030c28090618210201020d0c0201080412030b04060b04 60
    0x50a8000400703591414040007400305808100a07002510080101d04400d01e00c00062030703500c1b0f011b031a000002d850700043c101f1500c5140a58002d20900311050002d071405842c1c3c891a40c05c40d00c280780000b8244200050342840c00710403512020401510249810b0803280e06261885ea4002c15101e03504540660443c2081c1500c0c007039401c10060000815021000d84240082d0b0f9856803c62032135130007030442040081c40454952046903032020340f598480a5012002000f07002d011054407815000000f000010340e5900020690380310845101890034001c41404520b0342c00800c400800b19500c14000d21900703000b08a800303440c411084800c0351050316195004441001c83d0299440440d912900c642150780500c10a0038651441c035202c0d000c081c00380c00081200c174003e00050032402d40d03111050440d522a0b04000340e511000f07041845100c0d500e0312000c4507035105118a10703c80c00c = true := by decide +kernel

theorem cover : BRFrame.Cov 744604316 744784172 := by
  have h0 := BRFrame.cov_init 744604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 744604316 ≤ n) (h2 : n < 744784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
