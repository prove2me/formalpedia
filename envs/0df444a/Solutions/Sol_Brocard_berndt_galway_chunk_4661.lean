-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4661
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:19:43.290977+00:00
-- url     : https://prove2.me/submissions/1dca15ee-cc24-401a-8226-0af54ec0fc39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 838129496 ≤ n < 838309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 838130746 1250 838129496 838129507
    0x1803011b0c0b04030302090a0311090a090b01062001020a03020a2327030d020f011a21031926061311090402181f0903380402030105060105 61
    0x50024001e249000703020070250800507003018840d0b015601c543d1400791040c19696101d1420a91041da1045454021080140020b844076010f0042c0f4080d0354001001001917401c107001107445c0000b00719403024181c1480c544081d0310000f40300a140d000c01caa034005841e4681d0341401003005520002d5403010055008880004da80c080b002ca480301415501c0750803508100803240d1362000548507419605004100c151101c0a801181d00e00110400800800450005403680800035240f2440c1940004080a10020f0740003100000032458079a075080360b007400d01c1e07000501510703000355022000040100070300c00310141c0c2220104444410b101c002110b03520b4910003088a656124962002868070344610095a50b100c0080b0340100311301410566a0304604100c0b40d107101a40d46504d8015180000e10b0f0b40c0c8a01080500007216100d641c80300040c900e152104070303488080740201e41507900111141e1000c081044c008006840c400503110041e860903004260031034400400d080d0511404210 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 838131996 1250 838130746 838130801
    0x3060106050906070303090b04050a02040e010e030910030603020a1401080703110703030b1c0c140906061903060f08010e07090213051905120a06061202060706180503180301 76
    0x791019288291403044c1c07140b60508085010b400d00c5c0c0701c00380030003480070144024090f012805d803134518000c1c1c030244030700c006070f018260032114000007020f881d820900070802186090000c0344d2080042d460003151868032600019100c0c03000d5808039408105200407a5004d5800040f0140d001321a030804024100e5500c0c00540b05100e031002c01420190307110603c0b565942c68001d4500c81010040d02480d007002540f4082030070480a0140340740f096411440c8440518103904c80034400d00e0081c1c0040d00741462250f9860115691940003410f1649500c00400e5800e044103a90b0010071040f4001f01e1240c0204541e941448660b801201006004009004101100003100f004230f030016224084005208404c052040809070069503200b50742c90760310600703e24005007480040b0f005070320401080d84d5441600305510038001009410000034000800403403440e50200c607110400c840703240400201a62028199449503000601075035a10040c02c009040c2481180c80407000c1100d82e168840c00b850 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 838133246 1250 838131996 838132007
    0x203070b07030f170c0a170c0a140c151504050420030c0a181b030b01111914010b090a022203020631080709051e0402100e0604140f03060106 62
    0x40c800488005d00042441c078070752051100b149013040a0b4003d041c07d044c21480400300303600c691158000584c084540c0c9114114a604451007415000000e001c941c0640b003e05510b218028002c0d0062103c141c3c42c81d04d00d07120381c041d0b14801c510800521100300424900b51401c801002c0d4013300a80c02841c26401640f01e04400d00c0558a40041c1120000c51003507604024210305404404481148040c9441c042d4040e000711aa11509885607100c00c0c0c04000b44a546403102071280101e0b03d030110200001c2440401c00200000541d80040b0b101a54000441e040ca04207844d403420f402d13800640c0795910030708502024040101c40c44c0310403500d451a00065620b00071034a100865100e0607107038007680204c2024520024000802c112030b1107545202e03443d2185610701c103c1100c0e6003460000b9683d20200c07802c10100740c91071042d400042d01da940900c2410045800c000c0140b210b40c40480701c2c42e030380d108050401413992074444d03e580c126841c1845020903a1104060081e4072010042c400580c000c2d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 838134496 1250 838133246 838133251
    0x501020c071d04021525110307060512010614070206130503060a0b09190b09072d021015120b060301180201080a09240506031c0909050a06030203070b07030f17 70
    0x200001758070380e8228082d44040150100c1c02c0c03403145522501c0c00040100424900c0d10b1020100e040d0b03000d0a540f41420350322803041070082c01010041d00010b10925008201080008000202881c14851640e001c078003a41c4c8608800304c108141080104064503041061a611005d038003000d0040d00020b0b001308a801c0340c00b03003040185500200c01042d1620b007540c08214040da000345002214240710341c019200080080803c1c059140c6801c0c8a28142c0040792500480820f0394000d20000001e00307183d000408400e5014076507000c04101c00550721408011402d030844c018080d0f15101e0426000305400c40791404030010000f1001722082001d81e8208d60f000b07512a01104001c1a58034251070952100003c085081510403043c404d100d43c4280340d5440148030340c80a03822170f1800c035101e46880c5606007405200000046a08500b4080340280342c100035041a2800c030041038964507640044e09040b4160080d07442914049800300034035900c031411503107811440c10400f940e1a80b03c40f00c142e468900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 838135746 1250 838134496 838134529
    0x2090102031219020412050609071d1f06050a020c03070303140a0c06020a0f020f0c03030322020d050309010f08060a05010e030307061b1101060e160504030501020c071d0402 76
    0x40b200141000d0b00c4044103040c0352072219400c40d030b603603180ea400c800201000c00080d01c0c14414880020744580c00000c0c10400c0d20007250100307411358182d102c1040c60801c010014103042040304144030105003a0403104019040300d45815844030f0441074028600011140041d219030720025041004c20f0300701c840b0040c40049400915030341c3e6000c10b010b031909401e042006044c6440083c0c91031800e9402a01e5007220794140c1d0039503501e1003840120325510000030362842e41c190010008111300d820481041c444010280400020210703035500060b0800c858440250f800760800281c40c402907900c0002c04c41f1081042c103000d041c900703240e0b002c40d5001641c1d01440781407001c2143c2c050341507034007001540c2d0000e90000e42440340031104440c14005002080c1c1c0740003c541e00381c980c1034044006020325025114444074400c1c0c10355031280303071129003144401d8040070f200c010400400031039130a0004044c05003000000709031540c0f8051003592400c04102c0d5881c08120340300240b00c0140d03600e101d1038800000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 838136996 1250 838135746 838135777
    0x90405070f260c0f07120914091509220606060e09041101030515120709050601020a020d060510080609010b01180305150402011e08190608070605210c0c010e010209010203 75
    0x10540c44ca00300f0348529100a014922484500c900150744880800151007102c0059007a10f11140c052204022054a03041043d03090a42d80040e1818a44039150740603442c0280c00200010300d40245d0f211a84640c002c2d680c15807030381004d00c03219401a510514101044c0d52540c220310780354860021501d28501d03a0781c101034031040828600180d0844502c0c4144d0300525a64468003140800ca695001c144102c8032100c0c20b103800242c607507001142911181c0e80140c50034100c4441d076900e00d401088018501d000c51040490301080100f420802c1038400c440c180300008a0805150025196040c03004072607007540c11185041c0700082c2d0110715001140d0340007030200442d80f030742e10042e500088014104d0000f5200100e00490551303002001501800c9224094104c040c6400031800075110a80500b1302298030449040241c540310b04002c0c1000240c4446500ca9520300400048200c40c00f03a0391110003d20114989540b084e0030f1080080e40e00c400c100031032411462000107900c0307014541003c0017119 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 838138246 1250 838136996 838137007
    0x1c02060a0e0705040e0c01020f1906110c01020a110601082b0c120f080a02070c0506031803070f02030f07150507030509030a050312010b03040c030f020402090405070f260c 75
    0x180c0400c60800649001030050052588402e080c0c6c1e81c403845191802d005101c1c014a6002c038680101303a4603014410b01007003420b9414680c81e40000703480704040002c50700c030040000d000c1040f000c0c8060946481d0071b5aa4034542090910042e141c4041a08808a25006032051031000039a8200d0010558440c80d80c0018402c3c60700c3c8191003440c1820009860700203a84030308a8035582c131460a060500c045c4c0c44050706a140c00307180c041280295030004180018480040c003040c5015009164006510751105d43d130320781c80300c0049080d03800c00f01c0222001c0c03140b02c1003041186000d00a40c08035041d40401000701e036181040e500200405940c140007803020000d1100d00f031610400444840c1d000240841e000108a480c00969aa2080031050203c508010010581a0401003224041c5810040c10130819046450313103071400c903010030204da00c0380d8204100740b06911140282c6105900d1038aa61003500d4010304040d1070642441d001c0c1020f03083d1a601459264000d01221b40c00180e0007403401e4549 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 838139496 1250 838138246 838138271
    0x115081501081f08160812040e0912040305010203060a0816090c09091b140f0d0507050403120801050306090d1b2307050f090105010e0f0307090204171c02060a 70
    0xf9040451665004280c100045419203000500a28121404480400d1159541035260f15403606161210300c4a00030001001100da40340340d0a174109003050f054034515090f1f16040b4000f6480303070307000301e81994011040000a02e000034001e0300400703900c40580403500c0101d80f140c03420303a414020611000d9540304180081d600c00c0b11860045d03d55001d0401941c1209031400702e00180104002000070100c100500d01d20782e43d4030941d0b4540030b20007403460601003850812005044010f0440c0304001c0107100020120703070303105280184407096440740351955040000b450b08012009140400c1d0303500603a0f04164403030340700701941c00b20346c40888102e0701900c140ca089044810049443c514940781c0705041d007240c100c01b0810b40201d0742c04840c4042085d002c84184801c0c1203013482a60b001c2085262008801c0c188041901d007040710081c14be51001e80c0b42d2012404a8010f40c00a40c1c506100c444020181c210400c04401e5101902860780b003a8091180300030b55604000346841145510340d265810311 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 838140746 1250 838139496 838139521
    0x80a09050c0607050102040f080a0201090306020c0a0f08090405100807030b0c0c060108151605030c090a150201090b0a020f030711161d0a2a0903021008011508150108 73
    0x4070800140200d07540d002900b000e50107034005000d040700e84502068009020000054240c103200d0341070311041c2d0b0342440e40d29030303000039008040c094015008066620b800030b40c0c85042801101c0c030071107d40c0d0321340712450244011500000e050020344602d41006011a100000f803450441c0e50144a004040c2d860075480303030007406143c0c0c3c6201107120f40d10010940c01c102054a0401e5800c1a4500c0c8603651180e0142030f80e0383d4080d142c40e0210b0010008034501068490080c41c01c8907024104110107965020b10425000d0403582c00340051350346103105010051464412600081034500070350425501e41500b0903a03110107801c100070301c0f07452034240034a010188907440c90200c5c4980c030741c00d00c107554404043c1c035000ca41c1000c00e8900c21038000503281a00502c41d440801d08145034010784050008280450070806006240503c0040c240010041e40c50311452150b051f0150755000d0a5490915a00b81030802d926a800c20300008808101040031700b404040050042460890703115110103002901 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 838141996 1250 838140746 838140763
    0xe09070504271103010812070201390302071a0c060a020703090b1305040b040c1d0d050f0a03030c0f050a03050402040e101a0102010e030405060d0212040c09060e010303080a0905 78
    0x802401c004520f0140100c00024604035281c1c00c05a40a011080c1c080c00594420000024080351041c400d07500d1794425511108000942d100920b6402c240000114405440c2e07c642107005a000d81c000741304a2442040e42a26001109001d90070041c0042e40542c84000007410401d0701940032034000241441012032000610460100950b0340361030740785008000d011401400c0c0190f003403954003001e42c10603118003050a002c90380c600e50066940e08490441e4044603400e16480024600440003288003841801c030300281c0f150080c1210041481c001e0203540340001d40da070604c881c88036603960407a00007044644203545031500050681d5188005001425040318800041c400e045e801465001d540d44007500800080c660361094440030300c01203003650b1031b200926146070003d001c00c001071700b04a80074202a0704400805410849010420075500004a405440140c081f5038104180310841c400c0001034001c00062414543c11518080d043d08405001c40481c1d66880070300c8800c1c4981800300f000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 838143246 1250 838141996 838142069
    0x190207060c030519020a120302090a14060d09170a180b0c0303010b0c0a0b01030308040201030b060412080d091407091b08060d031101021c050c07051c0215040b04030e09070504 77
    0x41043d1f200014002d410144d0038900070450608041141460300c0050000c8101c001c19151421603800406005008100310880780700140540c0d00100c0700c00d11001e404450101c1c0d880c1d0340c01c00040041c0104c0d031075540c1c0c00006489010881130140f01804402c0b070b41903900c041c138030315a50105030f0045c038980340b03c0c414003400d03100e80e20001104159000340880d00841c000da0f02440101250402c1280c5840342e8400c42034841c14130300002c8005228600034010540ca07040700004c1141240e1601c0c80c0c00031103400403408a810401d000d120f0644280326100100d689400202c51260050b88082c0842d60050822485058003194403c201031040308842e4103440c9d9000259158101c4a07956101032410900801241e41841c00054209076541e090b102c0c4142c0290003401001403145544400b03c182000b000110f008a800300c81d043c14200030098011880b40c25002000e18283c2030051444034000002403040341040181b02c076a55204090300c0981c0d90b180c0f408808030000308440c3c0341c85074044c0800c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 838144496 1250 838143246 838143263
    0x31312090f030c090e0f07050114090603070512090d0e0f0409170d0609090c03021203040e040807020f010305060d031412160e03030f03010b13030602190207060c030519020a 76
    0x2c000c000c3c804030341d08111400c1310410320424072a402e5090b1100a08540e10905500c0001c0801c9290300c41c00c1e0008280c100086540d2070031850b5000300d6400d500464550700804c00004500394080d01c12003806a2040e074180182c00001a0400c006280128501005100360000f82c007003c190b40c1c0f240e020000702c2d640010401010400c419482d00c1c3ca4003c0035003403200070f2520500040d991050701070340312515031107402c2c4044181594200800129440c000540f1480140004158241d00102840c052402030321141c1d1541500e03c10070201a84941c90b090405041c18148019511801220000680c0c14180140d203410380d074150700554000d00c155140310003400d034140521000d541c04040f00000203941e41c28100b00c003d00515580c0d1046c8048912050300404c010006142e031800903140d026580400350300d01c0ea650381c440344243e802000d09091160313140445055025010030181000f072001e030078003404040060b10050300900901540710484c0014980076014280700f400740b80f808a9002640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 838145746 1250 838144496 838144499
    0xf0a0c03020f0316080702030c030d0c02010603020a270b060a080703020d0908071a060607120207050409032105060d03051b0a030f0e1c060b03010f020f0a0e06031312090f 75
    0x341c0183c4900140ea13100801c803008045400b280c0702004440308100800b00031860240000984401000060013000c21556545004030050752440890310090969500301030501c040e0b02c8101c2c4a0013416070a28000c07501d002d00c048442c1c2c130b451054624103403070303420040000c0e03503201c0040d0081e2103100a030141162800c0020809c0040b10405014454010301d0441200003a1011042c01080181c426680c0020305011020010303030300c0320324950076042d02d1055407034181c1da507004a01a51150380d030403004070700c0781030f1140d040788020a8000307940c6800600501a80c2405000b00710060f100310f1000c1d080190004d8100310340c170b44a1720b50218000300b08003102c8084806003401010243c1c94a4a940094200a80d0303035954681300c0302c0c603007070360b5181c1f00001d4a50000799541c0000b44a2841c0c096059502c3d46441228000320303101901e8861200c046084d074820fa240350007014810000661031080e00d081c002c1c0040e40c143c02501448450744480c09201190402c101916040440e502101145641040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 838146996 1250 838145746 838145761
    0x130506090109200102070e0a24050f0d0308011a070203070b031008060411010f020f011e150b0f03040807060507050703090b030403080a021819060807080f0a0c03020f03 74
    0x44240c00c0c01031006406020000f030f040700e11075860600b0f45005906c1210184403607090f4554203070f00507011040c002201c021514040e087c2481158141b160600711820800c054288030042c403913400c0013203848481c2c2102564010b404124103026480c994948030000341c1030142c4d01401c0b28495078000b402c5517130705c40d910711181003194030448011407002810280050480b00008203a4016a80f0120b00c01902182000445040072841d138908110710400310000c95815081c440c8180c0d0400885e03081d00840c803801076020540300300029503204030412035020020030003040c0556205050080a4641e01c2c3c6031410410124005d904001e041140f070b140030300011540150007881c0045c840d45600d0032099a46c50800ca03103000c12130340030b000704a10b0b80c001440b0804940c0104101c0303071a8030b410352911390020080344448a0380c2c0b94020102402510500c0015080020582c1c45000c516101d00e040c41d0011250010b404050080c0310310513207400c21501840d000e601940c905a80c10521980ca1703107000c02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 838148246 1250 838146996 838147001
    0xa0b03100f02030601200307081c090f0b011d040807050115060e2b03030b031e0703060e01050103030c03081e0c0a270302011b0c0305030d0b040b090f1305060901 71
    0x4031a0340c0410700342c011401d91b5464040150f042401c95801441c2030400c56210a2003d6020166002d220903c0700c0c1c2030040000b40f44a2808030302d000c1c0c82d40002c102c003203141c0400c1003503042e044050301d000d4840e20342d80001044030b50701d0313882584520300c55180c0c011860703c01e003d0600340150040c610000c000201c0c015910030440c14000078110790300545103031000c401c3c0c230f000c60050b48010070788008280584086800b80e04031001c42030000d01162080e980240810503800e141110b4031455820126003041400918044c01e50b0490902008012552466802070050560304c0001018400030800140c000c1942c44400c0d056a20620000c090380e00c1c08a0604400d68081842500840c15140480004c013104907181100218540d8041c813140341142c00565200380c401c2d1707409542d5010502c20070001000e100c8414004c40c4540010360f181c12081035080c1c2556403925019018610b40008510240d4440c2d00072a00080194118615074803101c0d865a48640010300140a070302c01e800c103201c0d4100056 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 838149496 1250 838148246 838148251
    0x1b0527072c24030402040f1b18030c0b190c03270806131506140d14010525082e03020436020a03030f03150605040501090506090607081b0703060504020f04140a0b03100f0203 76
    0x203500011594040c00c37400d542c0c0d2850b0f000c02800141d01e640520032001d050081001d542d80f24090710081150f03469440f6450020300301d030b103400500c031b04180460401958180c000040c00660409014203401e04070704030b9001c0051201c15114100e050740610601c003030410305051201074075002b40b0551600300c51b0303d00c0d150b804034440d01c0c4020f504100d0b10400b6118000303032130251070340060b4092111750343c0d525000c40c460051400300e1801441c5800000507520340c0319003103030709030044c08282c9007404104001c1d10304213040000340604590b804900005a03038000800090b207a050419410031008424105c005040700480340b1102c0c0f6941902040c26038100000d04100c500c00d0365280c9015803146c09203c4140640500e41e07130482c0d014000000042c1075440074242542d840b03032558444482d950f03c050719051156000381c3d4040e03500c209000a506204074000c0d072501c400e54050242c0d840c803030b030440d0088000402c0b03c45038a9541c403035402d0603502880307201003120440d032051040e40c501455810095005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 838150746 1250 838149496 838149517
    0x9012601151119081309090b01050909070e040f11062d04080a080705030f040b0a080a05040308041b0527072c24030402040f1b18030c0b 60
    0x1141c5011103a107500141045000109a0030f0fa02248665600d5a2007504502c40803100724402d07003004100c4c14004d22859007140d029900805040d450501032044140d0050500320094112150070711100055018003078105030b00550006001e80b450900e084000d12404203258442c4002541c0d82001da0f0902240710800e8503d5041841150b050140c03a0311446188120b0b100c41d080b00c5000d078045040342014000040c025016a031070301c0d002c0b100044881d800743c1c000740c60b5008049040078445a12481315a4441d416400406c02030a050f10301a01c058401800104050308242111000c80c5c80074014900904001d021450950425046246403c2e42c191900914200c03100008041e1032140f03441d445941000405011540781005224045251818141c3d8100c03008600040c0c0b0310b00351441280400c10410301080c0c41c2c1c1003502c1080103484454102c0c20216003020f8140c0045980c021002c4807035162400e0140c0e0103013107055801e02d403020030761000e0a0711010311000144280d4200041622040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 838151996 1250 838150746 838150757
    0x307031a030f0a080f09060f0414010c02010c02040c0e0616021c02210a021f180b19021603060917040807090c0e03161406030405030901260115 63
    0x20038189640c54810a4010010b50703c40160140452210340040a0424400701c2c03032842c04041c000407401d19440440c110075481e800140402401c2074095090110f02000d280031851079245030002004150f04440180c80760b07a64101d8480c002d4010440f01e8010040542615155000035804a0100700707030b82c00581c0a0014040ca00c1203128210f860290500d134024a2215180701e07240c0700700c50b1182004020490b034882d091912000d40d44540c140400081d1980401a0071907000d40018021069070341c04400980401e0000c1c4281c44481040d10107041601d00e000d644028070041c12850b103011083c00d1245140320300c1000c002d22109400c1401401c0c015130a0a81c11340460300503070a248030310b204406094000d070790240000303a40e42c4c00c80911202030389071400c031b002c0300c400000c1c1c103100c2251611106080400700800c0840c2c85d01036021401c2004848a604528040d00c5140e102c3c8141c8422904003e9042200d50130603144081c040986010140c5d240501d6131901c14461248001d008802d01058 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 838153246 1250 838151996 838152041
    0x70b0c0d0b03010b060a081b040308040311060705121602090c1e180d030507050d080f0603070501020601030213180f051203011202090603030d0f090c050a05151e030703 74
    0x405015121900381e0152170a403800d404500304647d11000600544800042280055916420300c40500051801150410781d01c40c030703601e802c08500340d950395400c0c080c407028080b0a000c1a80452403422400c054190b165460b00d181d48001e00b5801400c5c402903110249206000c0f08050a40c007902c01040c1c03c0f1080200d01c1d41e5105071108a00910f441c0e001c09085a85810810b420040c0da02c40025110303003441400c0560300d82da15410103400c00641c0001840300b10400c9603001841e40420b822803010341c0501030480c1400c000075281c00c81400064050a40401c3c81081240c0d294400100c101c54181185005074541c40c00011101400c542981c2900c1880100004600000101d034101d0701d03030603072011174000c40340d017400f2803c80020038056241c0818000d440012100f40985c010307c2c505602c000030760441500d400c028103903094100c1c0c3d020b480100e4080c4910349401c0c0c01660801444c01c049070304d40d40381c03000c0c403c405000901c120b8142c41020080c40b01864041e00310004c0960521040031860 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 838154496 1250 838153246 838153249
    0x1a150412110f0604030b04150f0f14060a050a0e13062306090f1602011b1107090510291c051308040b070c0305061305060702070f1802070b0c0d0b 64
    0x11300030703030002400840c0f003203000c80c0010f5244170400c0d207050310114000c24004180f004160442d2528590821803945550031444680314420a090307104004413030b05036180303040c600407400600703003402002c03034003514040882e02c0340c04031407820003031a0341c400c400380700c0e803000c1240f060202850401074010404660340803624500c2c10403002072041e1031600026050f51303520300900355850003501400c0299581c4038904092120b14420303402501445458492001200c03650251502526903c5a240d040c50201400340314032410318100304890603440c1c0c40354040d4402041010702d83c40c00c800b000c0191000034140c1c03030ba910030100e00c80710980c0380c100410060391001010700200c6551000141340e1401004140301c020880301c0a0710605e80140b1902090039126650075151441c00d0fa406240e500d0054000010440e0800c14103a01408034800b80001d540b800c20698a94802400f079900e8111401034060742420180d8156444a5000b00c402041da0802c02440b224690103203242a01c0241031208510342c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 838155746 1250 838154496 838154509
    0x150905060d03050927061809030904051905100f06050703020703060c0e03070e01080f19030c02010c200103110f0306060f040f0608090601091a150412110f 68
    0x40d580601500e0071011942d03400c60360343e4800c107200c41d4803c03004e900c0002d00504026440c8200d00c55040b104542c2c0c00d0000c1000940072030802041c001c10b240700700f00040b211000c425035a080340d00340ca0102c6c82d0703100d064180b030200c1d60b244071807020362b4581000c0003146032110042038102c400428800c06001d840b1181100c4074800e0032400382c00350344449410400929258440e400c5400b282c40c080400d100540000380c20007101d40d1000c0c0741c444400c001440446424828404a0744c503110007010000c0c500403407025201240c60024060165540302d80c02564040c6000d04107166201c10200b42e070301048400a103004081c15005070009190002400003410b15104071800c01c00851007040c25507403400704103c1c842d40895484280300318107003c00035200c05100c40510103000f19860348400da1514101c458a1304105902100f029402e0030703945519404185503a85204800352141c15804028481e04c40311b510950b841a0702490321150b4150034000d2454000108002c2103400c1d01140a4620803c606d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 838156996 1250 838155746 838155751
    0x90f120a08130e0906190605040f0e1e07171905150106030c050912120f071a0103120e180702070f09050c16060902040c0e040c0212160309050310150905 67
    0xa00350b102c4004204040710341100c6d9061054005004030b45182ca4070f003c0b4007a248100140300d9041d449200038051510280600b0703034029a0b1010008040046010b5540e0711003c03403042c0041e00d40c92180392000c0c81c005101800c845590100310400110b002d25000c4d684110040030001007003c02000454594444e024145c0404001d40c1c845040544000412000c1216481403a402d40b04d2480201d11240036040907103035185400e82c2c200d844014a0078040d207000b554030076000410420000500008100c0744081d25007024174a05450180c01d4003010605501c0e8070f00100481d20605410084041c0d0700041a030141e07521900401c2c54a42d031030301040244c1e1001d5415102449041c00f1403100503101c0b0603611443d41c05284042000745042d0042021100ea0703006d140c000583c2d040c003500d079605050050320f40c1aa001e02c000c1c000c00904100540040c06500bc42c00b1514184024500600d0311850111014040c001d00b41e8a0865000c031a00d170081201d40d0b49416415102000007440320724a1040c5417 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 838158246 1250 838156996 838157011
    0x9010b01020a032a0606080c031b06030703091a0103050d0f020a050c09060114031312020616050c030405130b03071505040501030c1b050d090b0906090f120a08130e 72
    0x4090303082661304a09620384214404007644007800000b030228025020300d000422038135010300b0300e120f4004141420b140c2e24032124038641c0000d202c1d8012589400d02220f030302c0100d038540002c000c0c8492401015400b80b8080b030140e84403042c00040144800440c2000301624144c50303a0000040c7c88000b40d842d220010005811500440c1a10034181800c2c1e45141d40280c0502d0880346128120030b06204540054401c42419000315680c40d0800c4039214440030320606500003402c0a01e0810405c5880310550315000c400c2020200301000301107420000d990252000a160b00303020301c204840c10300184210b198442c072900c51a80b0000740003a0200c09001c00705003503640d0502d03007402c02d4015006000f400c400700040004020800da00041920409840d8034441c80181c034440d0b004e04001440040640c000b01584c0b4000c00560100d43c0e18001103e444680a840440e2400030002c0091001a88181c0c46e03102800340d030603031404114030600101400c01c080d0301c41c2d861050b1100c2c01c24048050413074105 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 838159496 1250 838158246 838158257
    0xc030c0d031a0a0510020c030303041b053106051c11060910050c101a01090e060a03060f0612032003090f04050612031b10020307140a09120b09010b01020a03 69
    0x18000c2d42880070000d561105c1e140101c842401403400824615072044078141d84056441000e0340b60500410b440000803d804c075086070032000c0a4032550a001d8030110301c1641a0303054150740c19188440d81150700103210040c000084402c016814041c4804091001c03a000025200c006040f40f82c504103844810001a20100000410030310179101a070200103258298031032440c88000d110120300030380203d41c402c249e05400c92428280094050300c01c0341c001c9203101d08201c4c1008681c0d255606010f040380c3d0001008941140108080c0d401486117400c04421001c400301400d0901d40c00003024195a880b000c400f205a400440c242074880c080c1e0000d82e41d00c070036688198011340c5841d410060300710300000c01c0c2c11300c0724140d012524690760000d9001e00711001000c01c0008540c0c03003031000302c00040c0105800c2d440c619104400034030207190f0980c10880300708007003810315009104880050141c1080710000d0403026040c10801c01c20482201e4420180d0700b84401d90310385520104690201e00d5051320340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 838160746 1250 838159496 838159499
    0x12110f0301120303090204020d0903030b010c03020c190806011e06090b0a031109031e072702070302121c050a021e09030309060d06090e070303091401050c030c0d031a0a 74
    0x181600c810384000540806881341d5145c0d02517079841c4014024030203503030300004000689160180a0340c0203090401d0502012032480c1d03000c40d8020440c0b12480700c0071a04011582000740c07076030310351409a4000001720700c034040012954481c03070404400314044009180480e01d0f070700c40d02183d05107698081c0e00701c140c174217002c1d00308405d010707812403038803ca080d0002d1800c008220300800c0c502203800c51b8403131940b1503400390801402c5e400d02c4001e028008010102000310006c1031034000b4200e5400c11060503e07070004240e002c2c5882804026980030b18072140613070340c2d200d03802a4102038501e200c43c0d49030f8074030f01004500e54500c0ba1003100c1e100a003404030581c2c2031740c0000307515030306070000844d454040c0010060300c01c40b03a4990000304009e440e007100000e855805c140b0550b080345c17810301036440154415201400880d4100008404551040203031710301400c0c0d50001205d0034014500f6030010342c0300205441203581c1c004070307082410500c5941d003000200703891010a8241d19040d10000e4104000300070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 838161996 1250 838160746 838160759
    0x16050105060319030e240a080f01050d05070e0c040503061005031002251e140c01020c03100b03070e0f1603181e021c11010804330c12110f0301 63
    0x74107001000040300080403851b81401c0c08a13a9105440340c5000580344410007528410b401c44250250409070341c010b00c20000c2c0da032281d5542e1854066002002e1010f400514a41c44401c210750151001506540607420318401400003c010740c010540b29010f12a5007910144091007680c24002901111340c6c0a0700b504590008103008851040e203a60b1588108611041c4100d4000e0b07480382e114141401c3d040c103c0005507400e280e040c00d01641190040c50000c001c55800003407500d8492848400000c41145c0b050001340382c200d050740300e00c00c0d04032440100003200c1940a02c45101e40803070003141080c001100c030120121001c00e908610030b01007072400d9001142801d003035400d03174040f85a8202c613140483e070006000b00046020305014651845034107400c020600d9580c100d515000e0030406442c2c01e160b55002d40c407080704a410003103107040460105030013010f00120300300240c411320200000d80303408100404028001d10412034050400901c83c5080f07007074204844d5034040302d0b1207050450b420f005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 838163246 1250 838161996 838162009
    0x705070b01030f171303050f0609030301061b171909270204081b120102030f04080a120f020405030c0105090307030305031801061d0c030405060c0c0316050105060319030e 75
    0x30402d07207815040a1004c07000308003600080110001c2d0f82c0c1d404200b5440c5143c0545804040c10003c1d00640015041c06402c60000007074074159415802c2110020070040b41c4443c60b06411640940b0700080b0304030100110f5001d8008000c07005032400f04201d011400001500c4058462040c07500e40d201c410b040840c000e02c1c0d804904d84a03e003492001d458035a644c0342d81c0c0e1a2030940c001c0310b24a01c0440d5025102407500032101e0351071742109402541140b0300445420004940104044c2460800141241003184954002c418a05040030f04104400903c95507500030341240c020b03180640306580b064450f542c01002502d800c424010024805142195011038040d0009001c406076108034020074040c20500307010300c101801d100c454000349031100445001980c0001b5102140c3c803213041041c407010400110703140c0d5201400981e1140ea40181c8a5481d140d44112070003010404200007240d0704100040d00464011102102141e00c4c001c41c00c218100b00d2280c000005001c2251034494a04900b01078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 838164496 1250 838163246 838163273
    0x703060c09030506010b0c01060f12030e0d1203050402040b03010b031207020117090105041115091002031b0f0606150a18090e0d1d01020a2003030a080a050705070b0103 74
    0x1494200d1150ba600e80d00d251a0507401c0c0c0003001043c4001c034468545040912952004003140d41c072440141d0f18020017010050129140a010855120b104401c9504d8000700c240c19907034001034000d10520012001001800d083c4c804910983c100700c01c8424500c0c05025200c080c00c0006d014105190032144690b6555102d10170480c103101d07002c21740c10440d00c9080f001c00d10030f9143e04004101e518003858001a0415061500c600c81d841829041c4013102054007a10300c2c030007050722003c0b0701c2c44503100c00382d1450041102241aa036620400303040d80130404039140a010980c80300303d4045807603010801110400241a41c200c00f041440741d04840c52140c2c40c9800380f641d42d952218040d50300c0705a540305681000d00c0c0701d41158000661640344903401145140402c48074000042c820030280c0c0000c1d110308004802a20030304043e2032145228006285c90000b80e80e00400710796469051850140407200112400005c551804000500942c0030780c1c1150f6840342c0c06a240f45440c0c0c250343d80c196911400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 838165746 1250 838164496 838164521
    0x60305041119060e0d2315160f020c1315082103040c030204090308070e0f011d030c060c01050f1510050f16060b030709090c050d1b1d0a0509070306 65
    0x6075089140414512070500002902c04040c4031b90f40480c06440614001c8202070441c100a0110704000e01c40390b50607800040340b181d525001030941d0b00108200d01d85449010039a912100c20a0141400c074241d600c00115041c22940941440d995005500e49660212000003d05080290642c2e2405980c6004580c024414101f80c03014035201c1d00864111000c4210480205041600380a40c054001c41d9031519450219294000114980002003401d00b04840c0402c031018402c605620b03a0754140540080c000b0040c24454892001030841c902030542a104402441c801c5000318402c82d00c1b074001c2d10040b00300940010041150b00b01d0480746a8030807448210710b0300c000e10101041511076030400710700c9802840c0c08a042c0541000b0142000208d0344461041841d01c0f04060015000c104140c00320b500c01c45442c0300105483c02c2000250403031000c007071641a480300000c40c8030b40c0080c105080721041c003411001030350340310104030003180e00c1540c01c0d40035039115520420001d4419000a164640e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 838166996 1250 838165746 838165759
    0xf30010e0a0303020c152404020a0c0318030803091c0507050a02060a1b060c020606120a0f031404031a060409080d090c0f0308030105030f010c1e021204060305041119060e 75
    0x31042613915515401f62034035281c08200788510100481102d6800001c01b1044400b10315048800c5005130100d010b0b21001018000036110300c500c0c5183e400c100d00029034010058503031724603142070441d80320006200550f20301c00c0201c010300d0340d40348200182c455803680003004048000c2c07903030200301c0d607500b014224004000e12403000f15045062010204a858400c0c00040b5030980840c00107800c4c00c43c001c207194040d00c2c5000300c10b00070040000b020b0f81d008ad000702201c01900041e0030111401c1c211400050780b080b0300040d0010400c095082d180e5004c259450000006444240400094030754800d4041c100030707000c0c03207030021b041001d600540c003440c0301d0717004070002030b03650169002200b441b941b066903202c0c0040010401c5040a10841005050200c020440e001c5001c034080d06841502d01c42c0c0304000420213503440003038001c011090140780c81a440302d40351036507204020081d010454040750840d00d41100301c00c1c11b080c00b15405c0d03c4011150506084142013900445501044c41441d960200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 838168246 1250 838166996 838167013
    0x40e09010609061403010b100e0904020f04050403110f0327030a060e030904111e031806040b1503070f0603020a05070b04031709030301050105030606090f30010e0a0303020c 76
    0x30081c2c41018000c0c400380c40c0c0b1404c8801c4000806003121030b442081409018208041058a5880b10382400c2c104030449140815403a40c0c0007150000c010241c103039070014a0101840141a000074200a100040104a8124103005041d0944902680394242c80c925149200c0c1070000150000003d45610090122042c819290b21030200780c1da40300da25003009400000d408427090400e4014091b44110720b920b150b1402d46860721710f903049103003454010f241c0000800820708a1860108880d403100602046401d5801d003414500c440400603a000400046102c5425080d0704010030820200c800c1e4800c8d110136945480ca003078010703501541c0c504080010801c85500064464494180207a0103a03444500130910800ca180380800054030000d0207600a0004205d66a40b12080302d60100043c0d6000c2e85a0b0481700c0451842d83e0f5001600d64444c4042084220400c0502014100800341034000d40b0340200c0c000e4464200c645921400d1002d0f000b802824000ca4025002000703040914070444040c40c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 838169496 1250 838168246 838168259
    0xb0c0d1d031507021e1e03070623130f061802040e010e07120503030604110c0f011a0109030c051228060b0f030c090c1e0705150606040e090106 63
    0x182c02e4203882c88415114180300f000b550420807105440d140b0f200d500c071003421307541c0010760fa04a80080d0f4201165411160440c05c2d03418010f48010035800031050100180051450048590f41c010183e1094400000600010f8012842040854200252104901080d242c03400a40f107220030442005c40410160001a00c0701d11440030301c245000c00001c0c1031009240c9290074040b0560203130051424a0b00d1080c04a040881240c7d0012401c031000100301c44200b91000c114040d00351a00664011602c44604c4d02c04107420003032042c0d402e925020141e1494030015603800260380000742840340546828040c90400d0001c1911641417103007111100b229990513740654403429a590020405189450410400d4064a00c140508403034603000c0085000100b550303028500b000b50b1042c44d9100101d4042100042182c40205036110b50708441410301c480300d026540300001c02c80e124440c00300d00c45a500c0e21016401e02584d40100a1480e091406184603840c14002c0c060f10341c15507a40c2000200c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 838170746 1250 838169496 838169503
    0x60b131a091818031204020406050111062a04060215101d190203100815010e070c0201090f0b04030c08010c0c030f11160503060a05060a0b0a1115040c0b0c0d1d03 71
    0x1764560b4069004841ca003c0c81840251601540464148a840c0780c40948042c004201c29912007460390001803c08184880340300140741d140040a50a00b000a021580343e50100e002940b2001c05856118161100250301c502062140b0414030202c100c0f00105006c84000c0c0000b070380000501340400c2c0340b4180000d05070221307401541c08403401610502c2c00c0083d640b05002541c5405e100c000306000c0f40d03241c959903041c00c3e9401850203040100c611800000c40e030041485001030012107034410445070300c54044d080c00ea88607000554803c4816071001802c12414003070050901302c0c558418100b40309a540c00d48004258182d02c07020300102031510002840d08001b03000c40c007805108000d541d20310304410f140c1814400340041015038148420800e0030b468400303d0108484072441401c0d0385000d249000c8541c04662040d90701217000380d181824202e2a641010350080e40103a450403080d51b5101400042032060201d004103542043c07000b50502800340030f0700c036003003042071130300c800c0d5100c502c00002d04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 838171996 1250 838170746 838170757
    0x140d0e03071208041e0503070f0503181c020f15120f090a020a030311010608010501080d0f08012102060f0a02010c021c05160501060b131a09181803 65
    0x150384007151035014418078410b4402204068186100709092a031500340101d40c0380700441c00004403091002c400c10100700210342c0480c0d0040c1c05c2d070742100000c2c50702640300c0d401000141c00c45050a0000701092070003202904038802580e00c580d40ea01840d900b840003266100880a61241214901324035280c11800180404040400c000e00c05140c8101c002580d800c016143c800c142e0300c0b00750080c0060300c0380701902c4140c80d0181000d040c03003d030000c01e0b18007400b800c0c1c11001840d400d05000052007400050401400b9200f07864a0888090300c0e042258280c2092280200d031080d211507a44d0f8205801d03804401181c0054645460003108110314000f6074004074141d00184e54030048040e407180d06200341c1810301c2503202c5200091020b003030010f10b240640c540c00200c00c02d4078981041042800d41c0401c009103891035020351500c1440e44241032820151103060413001283c002042d400c1420700845046420040c100030200300030003034003281101c00400c0f030051860100407040b0110020806404c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 838173246 1250 838171996 838172021
    0x4051305040201022a0904050f0a29091005090309090c0d050105030106180e0a02030109030906030e070e160e130204031505010b090607170d0f05060f01050901140d 72
    0x3825082500c0020b281c6441d9850154001645000091410211905084076a20300303d494107243c0c1ca45081c40e9040404003001c43c0c03500e106408560080010000513000280c1d000f1b0118640021003d040d0111490120f98034001504110a500d460700c1c20b503030109400c100c0b8082100d00344807500000c25120303042501c090710581c00126404201d9a1980901e602504040d0000c3c00841c3c81c00e04038482034402612a0041c4544400c1c201581c081c3c208210f410041d0010024000300210f402c000c0c00440c00c034010800024100b192041340b600b00018408207c61a142b941d024655810080141d0b480d0040c00d00300401808084841d030781c0d51415000011820303000d03c01079440f4075505d00143c09180e21005c16402609200041000c0608a826291a55030988010340d80300e00c00d21f0000d03070744603281504851070f42000c20b00c4400d68180354400110744440d42c1003000151141c904203e91020402c1c4610300080041044590a510654001d07281e040d2865006d400e003507014115006482c49441c404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 838174496 1250 838173246 838173251
    0x30516080f040314060a0b0108070e01120f140907291908180705091810050703140906040f1221240e040b070c020612011a09091803040513 61
    0x50080310805c3c09960b800c150515000c105298003540064400385d80145000240203507003681800f0707640a040c0c011039aa500810400401d004910000d0040007000390ba45584650500000c440e0300000607080c007500c441d0003245000006006080b050301e01540d911760000c042c00e0015180d200c0032002d170041680340d1611545020701e0800c042021241c1d00094a603041e5100a03010062900c80000103034100c0d418209003810208243c0f05186455980310011348224545400c11107065815841310480c160001c0b16500c80ea142d08440c6581c4203030545002c0c00180d0800014000211030f40840f41d465899030070117803402220110041c59104020b6001044141c40f49915648641e8a0203032842055038010020100d80c2405840e086c1c2d40e030b0040005100d614031402260445004080005042d50700521440da54aa0740b0300d940c103800001c2c0300d5003080e12802402858100301030415180c5400c8090000c025a80e644d40246486032a600700107013090004000c0890b81d42c449030722886d038800030400007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 838175746 1250 838174496 838174523
    0x206071502030907150309030e1201021612080609040b060f120d05120f10031101020a12180806060105090d0204061d09070906060c1101170114030c0904030516080f0403 74
    0x40c15009031748400d500201031a01c4d5400d00000d0f000104411022020390341c1002e40c800590080b402803050810aa5418041c89070079000c02800030b0360407101420980e90311140d41c40f135200780b211140e4107480042c4200d09080000f4000d0503c08684480c40000419110003400140400750812950b18540c1001030f00024401034180034101903660441d2861000186901d801c01c107210140c0d0084c08000c0c0311030303004d09000c42c0c00da00c00c11203046540e0300302400e00702080d410503014004164036100b800200b901d4150008007000c0100b041072242d0410385070689860500020444401c1c0e0103d000c9030f000750360302c030042010160000e10b815540382c1038008000c0e9080420400d484e00710a075019144650038000306001c2e0681c00f003c054081035110f00c2da000105640f01c01612540385038240c84d56414441000005c20000a0441100324007007903040c0c400e0b040b00e40d0180030007000b003210003401140c010407105007441c45224070450f00300c1c040c005a60600c00102e07083d4103650302c1584103a820301e003400c51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 838176996 1250 838175746 838175759
    0x60e0709060e09040f170d320103080d0e010e060403081e100b0a020c090a0c14030103080306240d05010e0106170708090304051201060e071404030206071502030907 72
    0x700285001045801203c00d10780b50f9140c40620300c010074001c024008002e4040a40c28040e41580e5030080ca482d4240090f400d140303400b80020044525121000415000380008154144500c6041e00d1b00300701003500c1d003601048a1000781c9022841c0041c2c43d9a641d5092000d14400e1140c54010361183e900d41e5024101082c0e504801d00c80d44494014407038100c001d000302c43c0c6800ea0799200311464813201070b40b503500c0d1100983c24000311907001a00680020104400c0010590104030002e030349481e440058002802c1c02c190310f0100b400010000ca4040012811920b05401914a00b030000a1040704043c0c1c6013a03900d4140d00074840581c0030175151401400300315244000729000d4115071a00400e281c03d84d202e0010003040240188090000040126407802c00030300403600600b1000c0c14035001428003c14090083c0f41c0d5100c1e00020341d844402140c100742c4100044c0352001d90b035054050405046400704050355001140850721a10703054402c0c1032158a900181d881003000d2409402d01a01d0708a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 838178246 1250 838176996 838177007
    0xc28030f0201110706080a0507110d020709050901020418090206130b03040209070e010f0f200a06050106030504050307031b0b0a0203040236100e1602010e0309060307030b04060e070906 81
    0x1020701046404c000e07018040681d11200301c9520000040000c00c080c0c442c200e05548800c0744100c005054081c2d1502120442d40004500c011501030107000c0100f6940d03039145034201d02684c01413000d61030086540f4074807901c2541012007001c1c0028092071030491640c5e02c4094804055002105c8014080208001c0d4541100b805a1102060506603108803c01c00000c0005e0100c0c8041000e002000303a0b0b01d405144205000c2d0b00c000c6441c48589c1d03400017500016079841411030f5003140c025051a00102d07940f486401414000c0d98490001c40c140400780ea0292052055446d4118810700c100c01c014020854000495015020104c8016560b003814010701072215a412a92101300300441c4a00c0c1c6000b60040002115461104440740b0f2910f400040d030048070125407014100e61030701320511907149148010140148941d400801c130f881103074440c55440380940165140d10101c00c0c80090708043c06900005120700c0700500020300d203911180d038401c0b0b5160550b84a0001a0100070a20000e50810f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 838179496 1250 838178246 838178267
    0x100e01240c0c05010518060a05121f0303050f0f040906060e01210207020f0d0501020c160b03010306182103060e0f13030c050109030f0905010309050c28030f0201 71
    0x51801100c0445941c03030ba0014441940b28003410804005040d07105441c41c00c00400e240e41c401020700c1c2d0380d00d410480003032030f64014000c0c202030020040007141038000c0c0450344050701c00300b00688003840b9146407801c1d251030700081e240c240741c244100402c034100c5860f400140090300303e450f00020154204071006018080341071960341440009140003844548021003900a452105805640c1e00c5192010600c1450a4021aa040aa0b60b01100b01704101074019001400d000700c02c07a078400890714184d0390b08a90320320030b01c0d040748070420040c07000c102e0381d8020f0302c5241080503190708052459520740c00c044640008030f8040d0110b41c4401400d1a506000e50f00040ca0901582d904604207601019224880076003420107000309820000201030281002184a40d00075000b00515016800c0160450024035140740c0061031101c400b03d134540c0248683d080fa030750410014400c80403010140100301d6100107108901c3c0c1045501c0300f00861352101084007941c418100d15018000a100150486008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 838180746 1250 838179496 838179569
    0x12040f0b030f01140d050601090b0f06071203020310080a060c0f0216152604020102241302061306020c0307080d1e05090d050a120206070207030b100e01 67
    0x10070500c06840c004400460640b240c440314140b40c0d079807100009074100d0004100030124000e2100000f1001c2c61a0700441400f08203844100132030651b1401c00c2411301c25a0401330a0304540034105800c00d200b44d000e5644011060440c14503251144071603441c0240b40d60080b50450b40314034007404840e50004034549400d195000801e455400c410021201901d14001c42041001230ec0f070741140319220781341001000355030742c0c0f029500384030900c90034034000b408807000d074007500c00c219500960081c45680c410240341c90461401640e212144070031f00861a248007640e00074000c0c8550050000388141d2140104402d8006205440c44901071504210170b592024a0a80120740079100450308400b00001c0503094440740c00c80070200c200c080d00c690250654042c0c100c2101b2800404019002401500700f03401060640c004a0714014100d82c2d500d41250908011380003064104002211000d040f500240340c3c014002da000d4030b84254480c0c1c420240d001c01c10345003064500b0740d800c00c641e60188814040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 838181996 1250 838180746 838180769
    0x3050d1101050606070f1e081908190507090b130302040e06070203310f030303180c12050c040e0a0b0f01060914030a0218010f0e01140f030a0512040f 66
    0xe1880001d00c080c0641ca82c050011a4480c071ba003800c100c3c2003c20000e180c40600f1011b29000b440742090203054200e0300c071f103005c00c0c0d45a203058590217000e1114a842003003400745080ca03240020300014050031010b428001030201c1e030300c001708440306000d002c0e240d4a8149035100008515600400c4145d6100d007102e04002d411150500542ea80c0c080111044100c40d16114124090400d02454016031000280c1d212140604001300d080c691654034a811680a9901440701c0c0740271076666084058030520050120403044c000700880c50740380700f149140a004009070741004815002140c10354807420341124583d0001c00303a079000c2281480d004c0e50030140103490740b09590f0500f0809040302846000b1f4a0003402444c80c0b4500e903071f408201c680c501c0ca50242155102c50b40384594107401c01ca003030103581003030101c07000c0210714640c00b014118121181840c445210041d114140120100698240382e05405118034401c00304e902088035008039440309105903512031070244032031b480e045140c03c22520040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 838183246 1250 838181996 838182001
    0x4090311121606020c07181e05100512010603080f0702040c182709030810080f0304090f0617030405090709080a0b090f100b0a0b0702010f0e0a05090103050d110105 72
    0x1080004030b03081c1039800080140e803400c4902015180c0300c403550100c40c071080c40f15445501c07250382c1d800c25000d03c10051344e000c2c04c0403481c080341c034107075541280c240c13400d04030b1103004100624044032445030350514074000099090712621500d245500080085c484108000f40d00c108500702480b0b0b22032004003501c0c0c2608061111040c004600c6841d100d600000031651003101d103501c4034243c01285030050390000300f1604415240180c1105402c540000c0c0300030402500090140000c40e291041c0c2c1020340c051880d00e03040c408050024000e2110f80b40507281c2d102c1011800c0400e105c106403101000030001c58481e85008204501500028002ea0800c52401c00401a410001030141c17400c99222100c0e440682e02c0e100110b1400c24104000d400c2880340118030740258003264483c0c0d00d004403d440e0000c1d05501c501107843c4c684181400240041e2004008a94640c4516604c01e400540140042c285650740c1000a03903042e800c0c4c0040d41c554003c44005040e1540042039041ea61081400074442803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 838184496 1250 838183246 838183267
    0xb0f2517070201060f0905100b0307110c09191d0f060906071e050d0b040c030b0a0e01080c01050c01060b040311040b0a0602100b21060118060b04050103020a05090409031112 76
    0x105451040c40307851500c83c0c003c5900081c04014100190036000c027040e031130b8506010020468644c00356052000e006420354441e1600303040034003522941d66811006103803510901964028148107155000c02d465000070382d00c084100b40210365162964000401050400d5860142454030162080301801000d44002c448190154030603020300395282481030f20744450034210005002503200e9654414503284210480ba074155100c41480d03002903459180140d00d52082e01a1524280107401c6c10f80d02c1102e003184079600c9103004000c804886000410305e40d03983c0110600c20b8010b50001c035424009101045901e081a101d500f401d400200c0e140041240742c80000380d101c03645c0038207a000e801d031650102c482e030342c030340d10300101c04070030505001e80f00358090b884030944583d401e000e001000b034080b40314046681c00600600307081d18050040180b8051800300150b000b903104000b11408c2c40400e004c030300c0d80b56969100340c060841c040e8a03402055001018082d0819401c1808442045030510021648 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 838185746 1250 838184496 838184519
    0x3020c0706020f0c220603140706030b0604050d1e05010f0e010902130f06050307030807050d05041406360a090207200f030708030a0810030b0f251707020106 69
    0x386090380d01c5441d9900f03007401780803d052020140303d5920b003070440c000200000c0303010380c0501551a03415294010b89400f011015a2060042507500c00c0c400e00c424000c900c0c0010307500110360300c54401c02080444680ca001e000750010501501d5596584e1a524074603c03541c0030b600f4048954800802410801c3e5000803064000403240c01d0307985554a50510118a065010300040d180003002c0303070329096a0307183c43e0840b43e0115808941c1c601810003071001d201e004005890030345007403e07030341c80e650034140003440043d07000b070b200c40030241940688070010b00b014010003404c100030806400b000f80c80610148216404035520101e50148104607980100b03003e941e801c2071440e02031540944180101d07000904000300a1100d0354940103403080050490400001008800800c2c0c03103460f0344e40d86070200e11000c50300368840030f001c010740e42000804150355054401d0344070130980580324810034140080306007510020382d0740020480c4000786d1140c01030400c500d00d41c481f0031440248649810061111318 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 838186996 1250 838185746 838185763
    0x901060518010210151a0f03010b070201021006080f0d02120d09111210060b090906091801060b040806090d021c050909071d1206160207050303030703020c0706020f 72
    0x1082007240c54034007160320910450700b10661103a000d102181a210803410b20145a118110004008040d44030010984400f521025464141103a0139a0b10305041070700c0c80c0c0d102180403070440c01001d00c2e441010b81c603403203204050f24610300240380505600c82d40501d000320581404056501613004002401110360071190300c02c13a00c00000c1003130f9400d440c10700700c5960f1101201d684411b415000090400340007903102424030200e40c060002a580300c40c4a9028840c031100e075504244510700244440c10114002a0420410019a43c0c07000c03103000828210f8506030444196038800013002c00ca4481c0811440b0f4114900b100036041092810101a6407100c0b003000074940d800044036208103240c0a034041e03c1c5a500702600950503072818400c000c0070307440446880411418001a440d81c2c500309180c00b030f65140c0700d44000f44000d48540394003c0c012403860041c0300131486412004111a103080c0042d50003441c3c1078801689642c0c51a40480c10171081e80c00040442d4000403800621200010b120f08 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 838188246 1250 838186996 838187017
    0xc0a0f0e060a0c030c060507081f050607020609011b0503040501030e06010e040b06061201060e040c0f0f110c0a030b0403030506031606081905040c03171e03060402120408070c0509010605 82
    0xa9001d80281360507200304d002c2403405018645000100b02c0300380d4201d20200d00c2107011080c42d44030301c0454807003214503011500500341c005000740706620041c10544001c000451050504c1400620850500c0b080c0c0064860300310754580000c0b500300920f503094040e0901d0f02482c64050b000c02e40c1440a0100c0c4034000501c040e01800c031200105506803a007c04440c0440390220481e100ea60311104094010340b0b024071403501447c94030281001c520310500100c009940c942e510240e07501c0c4602001c6a0076410348100c0c0321b60740286025103c003070343e45080940045219108528003483c0a0030007504039480186900e029400115480c6034404502e0040d4054a205040085050301d4031400c0c0903000f0860180c1c0c00d40c491a140a1009102e00421243c085031312075220784802407910207400801d03000702c100a01c04400141602141041000061070b4800c4000c1d20040c10a4a10301e940c529210003540d0594004c50005403000c00d01884a0f00d00700503007002c0d10500c0b120f5140000c010301ea4407a428000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 838189496 1250 838188246 838188257
    0xf10140a02161401140c0a1d0a0510020604020a1d010b0304081e1e1e0c0a02041806060e0112060f0b0604090204140409050a1407030b0c0a0f0e060a 65
    0x54142c1e4541082c001e451030f00608500e2804412825040c003c0c0000d4120039111aa49400030710f460a090341100e009145580c0d031240310002c3e0190081206030303080407240c0e1040344050003103956202d2420307808003c002a40108401c2c2000c1c01800350810342c1d500290b021101c84420828003140002100d4111040380e2402c55590b6901c0c1040c1065008040c0385580c541c084a62036145041010007410090fa0021070f6815850a803200c0c540ca24031034178400c2600e80380e41d030101242003115000a80210920b54080c0d809101c6036a0000b000c964100d05003000d4010035920100500c40940b040b075010304a0200100a030307505000358140c0311040b00760000c1440e519000f0004601042d50004160594040c1040b510b81d40c0342d80700800a50098028080201185840031303d103490f1601414a5198100d40545601003007604c0380c0ca00356a01100d000d880d032003000000400507000c841c29510480360310160701e88944409000420030940602003008006903141c1e00c80c1c082d9608000c0f18189100f40c10300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 838190746 1250 838189496 838189507
    0x70203131d0601270e0105092a0714030c0616080910110705010908030a0b271f030606060e04092324010f050102060f040803061201020a020f10140a02 66
    0x2030104d08004403000074840d41a00300001580c0d29210340d0329040c0c91045400c42040e681c0c44030380900b52038000300025106610a981142014108001001442e00594424182c4c2e11954001455a44280440b031303001c3d0b020a0400100180388020001300311070301c0c64001543e06204070010384d900030281145640903600c0c054150401101b108440c012035005c0001d1122000301d0500151030703001121111411410100b0400762450864550661085241c0302050916041e00c03210075040d070001c08000110742c601040e600ba0026081000000b903208803c04102c1909195005001d81c020f0604203005030308110210000640c80006420400301a00c0514840402c03d0b26480c544101054068020844c40b0b0750800c51241c40c0010a05984414441c050781c20758803030049039510700444518504c1d50000c008a000116100c0003960069001005480e4400440800608a070301c402c0190b00964803088050300c2412041c05541403078003007188100000f081c0b04141107590f0100070540610950700058 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 838191996 1250 838190746 838190777
    0x30308061003021c090314040308070b0c090d0f0210110d0e04060504060303030603020915030d0827010905071509090509120f0c07050f0109060c03020c0306070203131d0601 76
    0x40e1035058a1030384d000b144101031000140c000b441c00035420340008104a00d004445200e0b08226070442e5404240c2d81c1ca0003000307440c8d91500e9003000e0080c40000200700302440f4240e940048150b502d40c0141d1601200725424810864074119041c8684184100000104182500880c80b801c0704022810a5000808200c0010700149441d030800c0750311914015000c0700f415032561011040d41d201707640007a010b4844400703500800a1098045034142c0c00ba910f4054418855440d49400400c7e80c20400c13a8480e201010000c03d03d140010410642e540d01d541c0410301604100300c1e40280200c9021401c505401000200300402c140a105900c2c0d03154408101c80b06800c000600d650b20a200903180c40303420307400c8080305590000807488114443e4010200d094038000301c20745d00710001619100c02d250700c0d043c41980e50342943c801c25010340c02080c10001050b2014003015204030841c0c0d0256a076400f00244040c806145904620705014004201100b007020000607960019001d081c204000703d00c0f0384 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 838193246 1250 838191996 838192001
    0x3020913060e010608100f0204030b070507061e020a02150103050606061b06010b1b190b180f0d0f0c02090c25030f0306090e060703020d1d0d18030308061003 69
    0x301e07034000b0390710303003000007480110215a8080401d03000b4018002c0040f01010b10059015070b01000d01200c02c0c3c2004115002d005000034001e00c3e2003042d0100700f01c04c025030002915100ba000c16201c482d000148056544d50501a101e1100241d071403060480d41562034081d40c2d10001018030f405403000240c1e900c0c000c0a91044003000c49410b1044802c07940c0c5407106160302c2d030401d515661610028004244503034801141d08a034104501182c070120009079110f280100a025041d18504d5062903201c00d80742c4000c0c4680c078425050400109620411004006c05c0c42c2e8140383e0060401c02004c41032001a0303100009281c02c054002c1200d0780f40c210307050300ba03c2c0440030320b40b400e10184103200c1070000b01074001c0410528031600761003c20a06943d105000c5c203441c214184001740f5001440084da400c0d00030390240080016042c4000f0b04000c24442040b08040103469010459121070702d009412170303001a10b04004110180107520492441d5009030100e00080d0a03140300c0c9200460080d41e0500c42d0303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 838194496 1250 838193246 838193261
    0x50405030123070503010806160507150501290f07170c0f010f090503071209090e012009030303010e041b030b0a0c11031815070b150a0302091306 64
    0x400801c11981d50b050000895000d08801c603114260310340002e8540c50144054031704943c05100907019a50310300c002e100b0340d200400d00d51420710074140070407000300ba94045896100152500001995410001e2484450020711104002c0012004d10310050107085000d680c4181100c620343d075191605850019400c0049208511080b000400c42000c12880000d60131a00500c88000b0011000364440720703815112814070250035540200050030004140240b41e40001c4007030318000e4003035600c46d0300c081c0a49803e940796505680d1282e8429600c0341244040c038611410124281c0d240c5045a00030913113078001407040d403500314040760008003404001800319070400c20302c1e1a407101c480d459160486845505903a9804036515002c4802e402c2c03801085081d103a02e40e820015418080c4030b214a4096000341d000740d86d0020031200c00c1e00404071401c005442c88504c200a0b01c01c61349032540844c140080d82000c014400d082d44002080941c40311440642c024083d0440040b01c00703400d044c01070203450403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 838195746 1250 838194496 838194499
    0xc0212030a020d02070f14060103080f1b03030a09030e090f011503180c0602061302030601170c0a060c12180306020c24011508100918050102030403050d110304031e050405 75
    0x26280c402c00c8810101b02861034802c000500d1480c542c43c074407590340d40f001d01008002000c10402d150b054014000078050720101d90794030000c492900e90146007150410343c0d054006a441d40701407800c045c0c00401d031111008050303924925900d00801c00d8032601c0c206100309454608001082001c4510036040001143e0f0a207080012001c00e034a84852400c1c854030034040107000e01004a03010385013001d041182d803500100200703216420a080706100e1121404198003d00c180c00c404682901c6e240c6c1c1c1c183c0103014a883d801c007005503030b0502c031050500c4113030f100301040b2103900e1220705c4d541e555100d40b0a0303e4010400607140c3d240c90303c5061070308681c18403075400c0202c80c610a40c031a19110002078140c8085c0f2300181c03041c0000c1401901d10b084140d84955402c2510704060051408951241603000d07a000b181003174600341521450301326402900d041d000150001000c000d0520503028425041c80c80c1c41046182d0f1070151002009031140300140d11040000080c48000e00b44650240c8018080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 838196996 1250 838195746 838195751
    0xe0d170f040303050301030c050d020f040b030f10060f060906021020031906140109030f03200303091209030a060f0605040e010f0f0c0f141b0303040c090c0212030a020d 74
    0x442c0d0030003038a41e400c00d1004480d0000c2941000c18035050180c0400016a4060400e0701c00c82007040c10080501007a03001c264041c81100c2c040000110100021014807a031030304002041c50910441c601002e105401000510024640400809900140140a440140301c00088100800e03c90501c1c8040002c0d1441c0350703040200c2440442031404444400c070112856041040a81c0c0e070030030306002c3d0700b201c05c2c00b4007190f10968100302007450f0f08040003146200340b50201c0e9001040403d040c1d00181310070803c9690780f0100401c24003540800500780c0000c13800d10401c0c10a00003000080c0da610759824000c0800351200305011400090740c000e10050040240180040d0310b1104c3c52a0083c50824112518a42840b40b031041c06e001c01e100c0c0d12040380d4665030b099032038400918240c07002d1010b45414003d442d01017040000c0038440031403000010040394003860f640c1c00c00b0301300554401d403507070001c00c034181c50b141c00c40350100c1d000180e01408419a880e155100d5a486000d08024001c0e560600c0030b035030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 838198246 1250 838196996 838196999
    0x1b071a1305121c0518060105101b020a080105040510061d0115111b030601091404240f0e0607141e07050105010b09011202090a090b031006080d030c0e0d170f04 70
    0x20f550101e45c504410b051030445409a80c3c882c01c01212503501000c96010450b07030107104099450002d980021a4005020080c2c81980d4070000c9085500484003a1040c5d0003100b11a09110200e01410000f0f24541030751000c60b40d50b01c103800c0c40001c0e0610600048541d80d11702c50700a02c0c0200f05909451070960140d50391040c0640810340c0c0c030038500080310b06c01c0c000c0c8800420400c540344141001c800d00ca620070304c90381d5195601d03820044544604440004500000a14624114020500c01d031030340f488045442c034424004149441d80240c010001d00c4944040f105680711300f8802c1d210b00200080702644640409000d81060b44903545025095500340b00003c543c09851030020b00c000c20080e603920f2200115208070388101e019140b441c980c0480320840401c200809a00860340611000f019996011600c00c640c43c200c0314641e01540380c541115510340c1e800e40e0184500b0400d4891414042c06251035240000c103890320241001700a900b01c1c96096a2508090b81a00d040032020000e6590f131302d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 838199496 1250 838198246 838198261
    0xb090108060a1103040f061107171810080a0b0f03070b0301060f021b040515040911040507030b03061b2a0d05211b071a1305121c05 58
    0x2070104a0300e031038015042a0791001485500302c202d030303c12a042480800c84c0b0000381c1d1040c5c09402a2012441030020500c400da01040341da000040d12054400c01040d0740300c5802c00e80501026039007a10b40d2092001c6138002c0d0320702d90001c1c22a1380c0b24400d038000160031848400040d50a0020010f15038240c0b01d29034020561007003c80096059402c19210040000e00140c1d08a90f00e14112210b40d64868040032106414241174001c103401c8111105071071410401c04000c1030803140d4045095444542c0d00c94400e0090070940710381d80c0c00440358a024030030310300c011000ca584d07440060540740f600707901108402c24120740107050710a0a10310001c07031010030707401001d00030945a00c0f614902c1c240c0a00e0404070324103409107044807003010340ca039a941c0c0c89403031060000b000800300030411005450701e40c207540c100d000104000c040d558852281d030700200b6330224881c00c0c1c400d001001808d01280c440300c6040480d100040848400d5240740f5070390360b034800310002090240144014456110300704010301200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 838200746 1250 838199496 838199503
    0x15040b0406092c1c030e12071118090718090210020a1203051e04170c07170c090f0a15030b070f0f05160602070c0f15050906120a0b090108 61
    0x7480c5100e00c4800050fa8080e80651201000b01c07081ca013030042c1c0081e88032103a00907003040031003072030350704c150f8070b100040807210205a4008441100c884c1e1851039810030300d2070144c0c180c2d002e0003810281c041c403500c1c00703031981580c80e1050b01411024034030346096095003400382d0300607043c601e81c050100e043e1002241c40295960341c0f0140b045520002151141841038401e00c0741d184100d481c0424a4811201a81411407000c0046e00544a007031595486007905000040145050055480144421483c0c03111001544804580c950600d800c00700c107140007a6034280e10903130800305403020050980c950202c100d0080c00c1030030419006a410301d00002c140003021100d20301c10307100340d101c0c4172401c840361008a0307080a003501140702007034040c0700000c0038040016452141c50f01c02c000040c80c0801075110010340c1c0b0296404030080160a03c004e1041384050140010390554904081d414030703901c1d0001070154041c07501c00b186502802e0002031401080d030740100d052b808004e007070660156102c045850b01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 838201996 1250 838200746 838200791
    0x1e0501090b090102030a0c050313060906111212060a1a1b06070f050906120109050105040b1f03050a06230f0a0e060d0309150f020d0815040b040609 65
    0x4600d06420018400c00d4040465080c000c0c140d01440c50605458400d442a6400e10f42c1903810f40b20511001c545d094201003c44040d00702500c610035054505000100b03010341201c40f04181c0d401403000d03080c0c1c41c0030b048151583d8030f0500708880035580e2440042002c803040780d8041b40000e0045642514060441c0000f003200b0b10075401c030a1501401d0f162025514581601d00000061407080c202c00d02c2d81c490741c003400640707400a10b0103140464814298060310170a8002008466644004001924040c421070f00c01e018203403a07008585c41080151009612003a101405154272000000d0005142e940030902400100480c18550460904440c4a04415454280c040c80c02d15002c0d0141d490503102100442d5840407400c041039446c40240303c880d4074481821018403c820f10301055a445002c1d04070380350f404a9803030f101c101a8103800240743c40780051540d011b000c048024820110900f1741c3c20348a0b0b180a480115801000c2c0c00400d000b080e0a52040c040c0034603003285c08201c40300309004c091 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 838203246 1250 838201996 838201999
    0x903030f1818270307031d10050d0207020a030b0406020306010e0a050d140109050d170f10050409030207090c120b2e0e06030a090b0702062e1e05 64
    0x508484040381404034107000d502c20750306480004000224006a0b201c91800c0844440d8a01030000745100c0a8525640001c0c01c1200441c1002081c802030351001d810403941424111001d44008041030303c081c1c802d01c154220084c02640009408080d52180f000003401036074003000040003803520f828241c0007500140c030402e0000324008000c036014036061003400d080d90b5004220350b0f884503541c1e80c1c410340310010b500c000000d5504c981c500008a02c0c144044502d00900b074803000008a0203500000c054400104a40d039046d0b01642440340000503960b0b44410345006845c0020601e4090805030328210440d800341188904000c40c02c9042c55103c580350896a00c06d560a0081408400800c040d01c40040c145c44d003082000c100740600c007440401d03407100c042c5080c101007140c4404100131400560040350040212516040d81500704142250440d600c80c0803440981001c0c2040d29060200c040e080480310006140c107074100c12800540c6c2010b400405620289000402240240240d0001c0350b12890b03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 838204496 1250 838203246 838203277
    0x3060a0501051e03030a1803080a03050712140c09010338010c02060304030302090d0c060201050f24010f0527030d02160b0a030b06070609061802060d02030a020903030f 74
    0x18000310031083c08254a00080c040c5003000c0c495001120401e440c54072010501003100030000220716440000e02d801c021070f035804507070b0f441e007607102905400310039008823606031a006000a2800c0c5e01c011658110000c0900c050392500200012000f62030b092591208242002050ba8403c04110214500c1d440409800c0300812106800542e41c100000700083d401550810009001038400d81c028501420010108810a2001d48a400d0b0401a036041a0050b070364500c03d00608044a0003450b40c8840003d1030302d0f414000c040310755244d100c004031219051040e205911081e047c000c90640b04008403c2d0036002842580c12440c68003402c808072141c0c0070740a044050112130703202149144000d039550442d2207016240c06841545680001035007020113a454400c00703080d50300c0f40700820b1024002c0b1004104407180c1e0a01d00129040381e00500038011074001030000503100c480540e50703524101100140c80f03950b4003402c0c40280c440d01c1d590b160306003c0001d05c250603030265405440d20940c0c50200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 838205746 1250 838204496 838204519
    0x10f0c020607050a0503010b070c0e0a2306030a12091d0f071e0e130c030e151501230304050718110904050405010902130204061b03050301030308070c0203060a050105 73
    0xd5030f0a129441a103400503a081005204900d4081c005210040c49020340c40b0b00b49989030007520441a06441c3d54020b5a1940c5c0041d2609440300840e140404541a040140d4103000000942d6080300304401054000c40b1308480c189203000c0e4880b000200307143e0386040b01941030039050200185041b501000c0e00708051001c80d241611032000b2107211000d0300c25a0303105210000e416134028440200c2da50340000203818001d0490901d0040e030303c50350080d44000c20302d4808884010304100c1c2101610201c6210a4104151170382d40d0f10072802d080100707081041e0300c200fa0111010880d00c040c60241c10540c40002070100300900040c3c00b804541b001e03000c4c1415214042819825590b10304100541d80d1020301400b02d45240c40c1c0e0040c2d42107449040001602403080d404146a050821403c2580d2680401c0821400f81c08c000c003000020348404421810200554010b00f80b0b0006000240c1000868000250341d81c3c000c580c42c184064000b4100c80c040d290038031800f0040e01c424040c0174040d1030f03207621 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 838206996 1250 838205746 838205761
    0x1401020d0e0f07140910090f0e010c0c0b180a0b070804150b030a02040c0203090a0312090914010915031b031e05060114030322140a0b030112080903010f0c0206 70
    0x1c660f41035640c0d10b900c84200c56541c008003c040c00e0007410281008020f45000103001c001d07807080700d0002060380d2002c03030310030703902c01c803c44c00c550b5402107400038048003492280009561301c007180e1344800d02c80407427400d4a040700c01542c980000040018079045030f40e428481d50b40c3c2c101140d6071059200d00c01084121611800d01d0050b14168154590158407210103000103180c550000004030440c1c3c4100da04016144002075000b150642c000d8a0444105000d00042d0313030b20480482c00307000a4402803041c0c00001d40380002170401480b40c02042d40d07540d1a0503070321f401d441c44404003c581109050912114034440150000400c0c8401c0ba101e00000d000b003404180020846a010b0b5044405030602d6840d00301da0025030000d004507594503000401c1881071841280c2d00929101d65400040c01c2e8031800c1010300701405400c2c010242c8a003092110402c10034507098101c0341500d4a40c01e201c5404070042c42c1c1120300307020b060140c0d0360550800e0303040b0321061259440a080c500b4a5400c81d112030300c601c4c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 838208246 1250 838206996 838207003
    0x9032214030f03070f03110607120c030b030a0204110405060a090806060103060b09190f06030614030f03041406070b011d0a051e04050a080f0d05070e0a121401020d0e0f 74
    0x41c0300c2d5400350418002100407558040d6a416518082d00382840116003052640d07082c04802c507002c0c8041884040c0c0510285958401e080e40c9540301d0804012800085d030000340e88600f4030364000d10654a1798808140f501d14201620014000680130036125403504c800681800741c0c070301408d2a1442080700055440d0700c00d0140c03030700f101c0c50580e1243c50000440184009850b02d8030b000a1180c121000c001440650300001030001c14080c1d400094003410310030720105845a00605070307c241e0148842d410200c03030100c200c504880c940c2c64451411144a13012603103078081e02c03802802e10751215000085c101188401d90003040c825446441050f81d90024140446109440f15200c000701d03c0c000d081d1119802d2182038000c0d000740b003100c0d51030a6990b109504d0380e03c00d52009011040212b45d0852907081d07401015044501418803d07100a2408003080701c4403800e1040040010a001c100803c2c031101d80700856590080400075503070380c1c00200e0410080c00b4021032898031442026401c0d1a05080030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 838209496 1250 838208246 838208263
    0xf020304080a031a060c030a02060a061a03090c0a060c0605091b0402070f05060c121602102c0115060513060c140d080403171e0903221403 61
    0x30840303810b20029200c101c00800c60741c0c0704001240000c202e0301d0700036500d1801601340140000019a0b41d0044018000e0a054003d030614100307900702041440311200d190419003c500c0c10058140e200d5444601c03c501c0e00c0c0c1600f8030940c0041e00007901203104c40e440560000030500902080c4a1611203025075542c510032400d841d24000c070b13a0102001c692420b03400600701c05000c0c4028000c400310740d8a60394208401034507407503a0200700251002e4151641c50b40191b0104141c60810702c180040d00000e9114400560f80301841641c0c0d00aa0319030159540040620f100c0701a1860071a0740081440380c020480141540103000c41004005280341c030400c02c803010105c108828031049840c201094074200e100b0301c0101d0b01d540020801004406041241e420310b8a00340d41d4204203400c0038103026100f844118080f10303e108200e81040440c1084d00b40384c14411481c00c80100c0c0c40e948084400e030071070040000d07080c0d1400120307040c07024005042c6541816100182c0001c8082d035180ca0800d41d80342100e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 838210746 1250 838209496 838209503
    0x6040507090e25110c060a090e010b070c0806010303050f1b03070606090e0703020a09021608030c03010f140d11010203040906080c13060806070f05040902160308241306090e030a02010f020304 84
    0x300c40d60800c0d50a008014000702851400e002d6005030712785544007411034090b00a000305080c04955642804401200003006041c024041c055a5040d504d0040141c4900d41c0c01140c414400141c1a122103212900010980703202010349484004c00c5c40c0c07510181116120701e0103424100707080c10218030f0000c507144040b07030350040c0405407c915081180001e50401c081c1405d00c094800070950100d603c42000314828004d07010550755960606008030a030000c5500030a005103000d110070f20f81a141d107070303035441c4003604600800c80e0400c002c00100e1071481070741c000c02001428007000142d21880087c10103100c44007201c44ae02032040b081410700c111141880782c013803142c2c0058040348815015040c482c410b10700d02d2034400c0c5400e4507140440182d900112100c11100c807806886800c3c5580080120380202c1140710b058000030b000711980c52240d102d009124450703465501c80c08541100c95102c2402410b40c14401c0c022030703543c01400d903225000040c2260141d4201454a07450942900c2100e100383d50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 838211996 1250 838210746 838210753
    0x41109060d060504050c04090f0605011508010b1812070306050f0403170901020409021201031e051c1806030e16080d08061c11040609060b0306040507090e2511 70
    0x242c40e0400540b10140060342d071402032174059519500c65001d80c071a1180221342410900070140f6080c000c4850580c44404598000001c0c00c0d02c09510841c614110360410200c00d407200111000302400000d403a08090f40020003100450380d414000c80c200d03040368040c0d05c00300041d564031075810702880012600200002d102d010081d40384424400c0c2150030941d00d400060405880780850f008990100c00d50510422120740100104520074100c82e01da12003d4000a690310143d565a660b5030344100c9180f003103600012050201136208000e10705034181201280e400c025500c40016000309141d15004400f4060211551303140c0c0c0b4500300c0e080441d4240300080c0b442c10303513003a01110402c20103414a0760040c00007658989000300d401c034688003280585008042c3c40c607850200000c40f449030344800e00983c20031408004a40c2c0e0107050780e1b8000003d44020420303030755290b012258150b0503004054180322070303010301941d6210611105201002d88041c0142e0f1900d40900b50740c0c02c480c950003481e05a2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 838213246 1250 838211996 838212019
    0x302121911040b090d031e122703030b04020d05130b070212070605100b0a0f1b0305091507050a030f121a10050c0f0604050d050c0a0f0809060d0504110906 68
    0x1c15605048280303000e1f1604000082c51480121b5601d81c003071448000003650148480c4000c582c1d4460350a002030700740004042d0040013100c150707808001303e10150626982d0b0b03040e4501920307250100c034100d011501d01003209240c94800ea04070548442030a9a0015005000800c2c0270300000e100007000b26440110340c144141a65002c015103001003590105040b21180010b244d010f81000d085210003c1d05d403000c271181034410003070002c201c280305545112283c140920100307802c1000c451103070310b0951301c0c00200744100c0c0d0141d807075102d0301d1801807441c030030328840c4003e15600003900181c0161554404087d410401805410703548140b8055101d03040103003091081c0e103800c440b25880c544160400c1402d10000e500e03031380e0030002914400c0c482c07034001000700400c1007824000410b03409980c0c180300382841c2d007004185640e818a80402070000b502038512a09000c1403005a410078003004082c2030790b80100010200103001c00740c800322080c0410b40700044e902e162235244144512000741c00d000170301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 838214496 1250 838213246 838213249
    0x605120a05240a12052b1d030f0d0513050904021e0f0303030709050a050d11010c0611070c05091810091505090303010510031509020a0302121911040b09 67
    0x1581c0300b40b0080c0d48a44102800181c2041410030b12200d80e004501400d034072045080605110258400300600d01200e400c28078884a8020601800450401e41000c00e56100351010a15280400c41210100e214030200808041e510600078084d041001d0310f4204d20640c0c0b40c040c44400c000645000b54040d4507a400083d22108442c40789001d02c00080c0b40840119000000c68215801610044000391404400b0300c418140240c2d5003000b08030a4032072241e4002e0301d0f200c8003610300361204250f041200d44c482c0641800f10a4006020941c019001183e50340c1c583d15000841714800c0c41840d014200740d400080380000d00e411640c0e90500030700b014048110101c000c00c0300a05a000d000c03a419001c500e0000c286801d54440d031841006840025a40c2c0d5050008100c65000c61b04d00d49800c0508207015124500a90b805c0707a021100080030158845a1f9400182d0290141165444041c5502400c1100303510b20950361428084034a03008201840c415002601c280c071890080542903d0104690700300d1307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 838215746 1250 838214496 838214551
    0x905070f030c050d0f1403041403031306030c140d0f0b100206060108061201050c0307031103100515040b16061a09040b10080d05030402011d09041b0b040605120a05 72
    0x4034030171200d40b80000c1040e43c030030743c1444081050b880587e2003c40c1c2448040003a1503021403055046000b9030030b22410f1107409030940400e0151104050b107980410354541d01a14002030300807002c148168841c25542ca0240040158544003103141d803d1070505405410456150240141c81e913014050540c0d0303020040d1a8074070080c290a81041986901400d030a90a00c907440c040c0c1c2c803000031150350b41070283d0010152801c07003091008580e0f00b04240452080d080c1403e2003122400d46511289004480c44401c1c280100d0f0b000300003070364000030711070920042d41c0584024288102e004100f4001c07901d41484178a001c40184541115400c00881e0100e50f1070014690b011500070601103004da1035200700c41c00c18488000c4100401c1c00070040c08110743c0c21542072421f5140342e54180b0904403101000940303c22014001906810800c0071070250f0018000c5004058181c0302d946580d103035500d890007803866000b04034103401d90000c2c001055000005009140c002d9031131280461042c082c0900b0b0501 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 838216996 1250 838215746 838215769
    0x1050d1a030111040810050606070f080f03090a03020f0105090316050309040c020714030d08070c06091421120106180305061003051c0f0c03031404060905070f030c05 73
    0x800050841a150181da400d025101d162400d480d01c49480e1480c01d074081e440c0c0b00030300140c02412400c00d4200200fa480b80400d031120540c002c2c642c40142c640754101a5140d101d070b00e1514111074400020401ca10a00107200350125110b51700f150020000b294200e4201c500030340e000c0120341c00812000002500c80900705071854003a4055928010401e000182220900703001c40000d40c001c1e013020008201c00d0313503942500b80b0054000d00b01034000420f008048450082c410000e11101c100c01d00b085c803032254003500d01c260b4480c010b500030050300056550354032160440300c0031198000c10642c3d446d448150969003007251030943d503405d5134244042900c80da0034400d8007541c0800c00c28400008120200034640c0607030a420803032034105040d410a541890f400703071040601440410141c9070b4141d404038202030450b20074a040216880c081c90101c0140c4400d2030b0181103d51540d080c8002d10036543c0c441c500c100d101d48121070f00c0b599502400141070400348030180007d060300b0010005410039520050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 838218246 1250 838216996 838217021
    0x9130b0906040e030906120609070309050d0c1b0609090f0905070b2d1902030306010206040213020d1a10081b1b06090a03030b030a08030c0f1e090f06070201050d 71
    0x900701904c440100d800c6c0e4008040c4061821000300500c195400d00c0302806030040f54514051126501c1c42e1100e0b44e40746403041071113081044030517210052000000113041201e90b9006029210f50303448000070030011941c016000c0c403510b0005941d01148147c4a000e404079402005840041d00d0021003140507007041c2605106d03401d0000c4109d00000072903149040581c2960742c5140c940c41034065403500d405d0310301c21640940d4000c2052240c140e0300017615032750142d411581c42d01c8a00c000e00c2820081d0080040c041c1ca03590900d40024000300c443d81d01e0341070070502a2100342d11111044003c0b580340405130341d61002150b550720090911110341c0020700c0348003100070416801c5851110011314000d011100940f581d04a241c10104059042c0581e4802000c01c178010081d1598a480c0e40480b4800901002901880022482481782206c015208213030030040c184001c42010410354440c56103c1c4041c1032003000190311a007503510382030707040d242180e406070764007400c11201c0241c80c0024071480030f109 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 838219496 1250 838218246 838218253
    0xe1902040f4a070e0c070510110903030a05071a010302010c120302190503071106070f03090c05030118060506220b032506020705040b01230d09060209130b0906040e 72
    0x440081d140b0580500c51041000b006140c2c03600140d41682900500303401290ba0b4100081c00c0451000546601c1c44045a040007403840700c0600c11404c184030325469681c05020100b50300c4008d90700800640341c0b9500980320304005d4410391400364031814090000901150014000101084501d81f503441c0b040000e0a005107800704103030036054039091010600000450000030040e51b41c0d400007445001c800f05e4070040105003004400901107002c8001480f00705540c41820409000c8010800c100801c005002081901201d0a400c548042c00c0c11081d10a0b5040c1804500182045450142400228083c4900055a0145643c054400011855803500c6003c4c80b03004d21400488444400c0e5440440c42812140341100c080d0030180154080d40c8102c5c43e005400100d0b90700301d4a90715070207110042001c0040e0320300c46e07140140d00503c074800740e0030b5103402c00200421000e80e00400c91000c044444109504450140101f6503405072016900a8030900c045078050a00d0740043c2028160300d03094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 838220746 1250 838219496 838219601
    0x51e1c140102070609020f010206040c062d05071a0106050d0905011b030209010e03060105060f0304052a040506030606130e120304050601030c0b0324040e1902040f 72
    0x282640c201c20f00566400e030765500090114501a184005206c5c000e00140c10705190544902d049840107216400c00c0c0010010440c00c606850200d20240c1158940c0c00e40729040001001840c0350070103e000c43c0d902e403075610b10014441c0c40602140c101d942d07694650f03240044040f030301c5020f0851140c04441d150349800c0e103004004007240014507003041a80e00142c507807048a0005228490301e030312050292b0010001405183c903031008440c400140320f000e043c0c5da51200c1c0b50007440d00c40c01510440403001107000c0030080001c2c1d00509849000111014042522030b030042503100d520540b1413980c08071070125002c1d01f885254022200140b20f0f40306a80b104055100c0380c054a5004582c00c54040e000600140200b01000c10004050124000080d095181610140f02c2e200c62410942d64000141004902942c2e07481e04100c07112400501503400e280c00a0800c1c002911007044d0480c480c500b081c00e494130700e090602c84d9510082e0028cc050310030752214821290298101c020110b40074078500032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 838221996 1250 838220746 838220783
    0x5120a05420718080307060c0207150507210c0f0c230a121e020d17030f0610020c041a0a1e0504050402182e051e1c 51
    0x1c0a0101d00c41001c1c80710001c0c030b40803000a06a56080f40d569504055628060190301000000e55210a5020342c0c0011002800c841c141d03d012010340c852107a12601003800d00c80941d10030058a880e91145103410516550240722031005074050010900254110000401040343c58400c504200e00502d1403503512030303c0d0184014507041c4903400003102d1005005403120f40c200000420001c0071600c503140070341850b42c3d8814480e030061448844404400c509a58255618400034034040e55000282e05440c0c4218a4421803a400c219070000354194400002101d50070080c5401800644523800360607e80b04410410000740740e4205880c608a03812144404242c0312040c40c10060140704030300c3c242e241c44c0002c083d240101e4907040240a981404180001a04c1c4c00b0407030001c200c101c0b038a416142e9035800071b6100790011901c80711861181403100c002e19081007280501a900f0a40341d800850951075907a9142900740b018658002005012551a42076030000303003103580d4855020316404d100703240d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 838223246 1250 838221996 838222093
    0x11d011710140f0609010513080618010b01021b10170c09131401030609030c170901030e03071703190f0b18090a030e190e0105120a05 59
    0x692001c071200301e03400103101d41c80405558400c4240c0c21103034400c03d40e00c0003000c590700c0d01032090f010703051101c0420b06651044022242e60060714100b411103c2d18036016a110900074020701c3c0a040c90f500c2c1c50981c2580d54030104c0c05c10044c4918514844a100c03442e02032200c0701020001005c00c010010044513a00283c0c2c5d00d00ca40918070019000781c654400340304210503213901c44034086145180c0380b01724400c1c4508401c0e00d41100d41004001440c4200750406541d02000c1d900c2c0100390f40f20010141c2c1a41107100c028020028080c2d83c02c0040c001c2d882881940d0b840703043d001a00358455890890038200803d40110303402085292901d60007180c4020707034000d03210392040d8158000e4a0b40031aa20b0340c2050208401c8890b428113407247e0303d040c094003450700c4040072003000e0100200032503806480e031101c44e50354806409556240e43c090f0383d0781007010b8003c0e50038050140706200e55651400d0002c00003c0e1090b80c5038005024019050440d0340c403080342440041d8141400c420300070524140380c8200e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 838224496 1250 838223246 838223251
    0xf1b0804030b10241106040f060b0102030c190219080a0323090d02010306050d080d0612081b07050901080309090106020115090f1b0c05010b03060402011d0117 70
    0x41011544403030861900b401c80520081030309032030030040c0f10100502481c400c1c0c005024940034078401001d03160508102d0310301c1410b154002852003150140010044008204400d040c014841009000291401203844c2d110707030401f100881e0701580d542e030500000c0b100610386092000f41601c8000c5d241d11107143d07904c00c4c01d0303000e03901c3d5820080d007140074107403c500c10780c0b10b1054901492590740c02d42d10241240340212100580125280c0d04182c003164029440b0070080d14006000c5550004a8600810940c0c030440d1408501801d000c0c001580c044d540080400890380440c1d0682070080340110320101d070072203149400b0b0621130080000b40c20303261b411010b4041c01c4000d010b075589900702402c0c001e00007410786c084021685405004880c1400c0602031509840240d80c01042400b0050442c101810b0f4054a603108441d036003d41da44080d4202c1c03a50721509114800070310000c40d501d01010b8548a0464000e4045407010f1204101c106002072868489041410a40800001b140440d403208008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 838225746 1250 838224496 838224503
    0xc0f0f040f080d0201050603010c08010b0d0e070b0c070f030309051003020708030c040801051003020102061b0403290a020421060e15091905070509060a0e0907030c080c0f010f1b 78
    0x11400f8048025030a02405a0125045c0c0085c04401d0a021000b024440b0502c529001d00c280030030f103e0700a100d560807120000c1e5246003114a820303110030142c0071940c0300350003004842c03041040000b440240d4500705011240c064941c00d182e14502011310882d0030881013100d0406a0130062000021404005140216060b9074125103450802d12000d0850f54040e00148400e0403d1000f0030050ba40012082e40c000e400400707090036020341c101722401c1d9002d1500018065116a03201450403000160031820200744081100ca0310b40b038003455481284030720300a4089083c240311500c88010782028a04000f80cbc85203c000807075501c2c4d000704a05190180b164404c0d540d44d22000d104e00b01500f0005050500e01c0f1080300050004660345840d40d40d5810310a841c040c1c1e0121000884c95683c522101c030040c18041d9000c006850042c00043e204d020324002150420303405440890400e40014030006035040140502c0c0d0300c004030a006580c00d2808000c0038040041092a940c120322140c600b54018512 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 838226996 1250 838225746 838225753
    0x42f06031b0f04140a1d04060b010219060c0216030804050d0816051006051009030210021609020d0609140f0408090a0303050417030a09060e18090d0212030c0f0f040f08 74
    0x4540c130402c04003040c40e41c84460401443c80000192143c0c4401c0c803600540d1010001480b240a400141e06100d428269141206140c0351001c0520205800c0039407a001c941d402e49414901c03003d0301054002003800040c207454024081808a81000e21360300491500030a80141040d1084400706038078000301004540d290400800d070741000381280900c00142c40c0c1101d44017400c0c200c00c50014950301052002a20840c082d18040746640c1c001d0080312005009414041421a00d441104000e0b610514400211928081c000102c440051081400c41e50140020051036294000514800e440140c001d6881402c2040304500590340c21825100441c820b843d021340b42d03403602c90041d014100146440c0d600b0781003000102c8803d940150400f007500d2250420039000c004540c00300b41440c09603140380107170304219070900030740d160005100706010380c29500322440080300421304003090200741c88107412040d007401020795188009010380080d07801880303035508142e40c4129144100c8030550111543d40c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 838228246 1250 838226996 838227029
    0x906030a0902030d020102040b0f0304080405040e06150d02090403120b061306080a05090a031409040204060309050c150901030b01110102030703051806010311040207050a0b042f06031b0f04 83
    0x6080c0804800c0034200d0001f1424280f8101c42010244294050100507500000000d000c1160500558000e4440600204030001404441550f1040c0c203a6110420301048021000c040c6058090386d0714260b40980105420344581c1c0d402c4c1d6200294849a0f0b49850300c6003648000c54950b40302034260344038200003554602d071900002030034552001d80114655400c0c5820420701c4100021440310050b818609407040c103450b090144494011790043e40d03849800047c0000b40c4642c980c104141c502c4c0500180d50311001c10404008102d06643c1405155a1003480700c00c0307207580298480c9408040c10306002910180c034000c001d0882c0d00440d00f03140401c0d5030328103004480d0702c0544030030501100031000340455411a140d80c003440400703d0340c0c107114640004500c02049824808520703400e520000d141454141480c008000c112041704604002c0c80c9010180e03030402480c07806401403000036058903d90740784c18040c04090320000070810340101d020061100030f5100da80080004228546101d282003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 838229496 1250 838228246 838228249
    0x2060a21020318010911010e06120a0218011106061c0b09010c09050a030b0a020d020409020304030809060606070b040803040615080d020d0921050f0a030206100512071a0906030a0902 80
    0x26014183c43d41c0b480c0c5c9094201000074010f0034501040c0c43c000d0034102c911001e0342000440c940302c2c9170107802031410482d0512220104a4001c2e10301501d48000004180480500440e50710064460b94a85940048041805030071308441000501824100020208842d51102c40d440c10302039403200d0003690340381c032020041a4000c000c0f0000c6d110880c1e40c0d01000d451070700c1e070b00da0f04080078144084480d400562140d0550303980d8121401010580400d548a00e4039060180c11003400301e0300c180c00b038003461001a010349016802c41360030a030310441207051612251250151904020411505681c4c0c8004001e554640000ca40000b042c0c01c5004007120558084001d0900341c6008d00b01c000c3c41101c58003800000174103400d0b60600741d50b0144480600e9101c0c10060314041642e55020818000c82c1100c50501d03501003511807003150f1742c0070483c4c159941d500c14010050b0403061014180c0d041140144410101d16948480d5004621402d90030505d507031000448960013510040b40d8159103c144c3c0085 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 838230746 1250 838229496 838229521
    0x9080102070327050607030e010912110102120309031806090406230d1502030604151e05090403200a0515010815070e0609060c011a09090a0302030702060a210203 71
    0x381520010300c400c0c83d80c64400032805602a400009051217000b240c00c0c1c4150740b103a4502802084442d402d13118180d0141081d400100d0304030040350050207843c05038040e144030041100d024810050055241c03426400075182214541030505501080801075840c40303603168018075000c1c100204000c0040a052100e151000c0c0228a15a0103007483c4003230480860519960907802c050f2091000d0782e41e60b00c3e280004e008004d400c07001d00308400d5028020400401c10b61345000c420740207513219680d241e115010403c86240423079000700020025111013000c1c2616000e8a04007550701800c846005440760758190506a00b80341e4a0890b00d0340d4801008000c40411a150b42c0018506541c1640c0c20400302c000c140d0500e00301c9203802948000307035140c42929a4000ca81b004041003000308274003854828000300352202c00e0341207445845008041042d021000c0755156201c0da158004524040139070f42848969001402d2000501c22028004c4462108000181001d403000c5000140d580c98950031807540f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 838231996 1250 838230746 838230797
    0x6090204141909050a1217010b0307090617161103120a27080903030f0c07060f02031602040b04020705010c030f0c090b03061509031207030210050606031501090801020703 75
    0x80b60602c1c0d001d101055020070291507007074000000610700303108600280d607440d101d12101d6102580301c5000262103040400a540207824680d40c50720714947d103010840340311148844103400708645a010854000d115103654021003a2401c148016a10341d550303c0c0c0c21070f0404100080740990600400039000202d209200c3e4a076150a11004d4000c4101e00e41c000609812800510300d00d0001820101590204281e4200321018400545d4400c0c0140070183c40d071071284120030100da0034220b118030960011055a04c10740c02c503013024112141d5502000043e15040300b400e5080355081120f00d0214500380103a20000c2c03d980c4000c16003680c485142c20403600601c02d14030400c0600342c018410402e62808a0750082d2048820300742c00302002c1007c81c80340c03040c00d078032640c5403140f0002802e01d818100058107800307020b5026962400d405108200590300102c1d059a40040100001010a40110000b006000d010b00d054250581c8a11015003281e100010a401080c21962071108411001e004940f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 838233246 1250 838231996 838232041
    0x215040305010f1e1d010f1e050c0f0906070209010e040201080a0605031203060a210b090106060504090e0a020910031b0812070f0c060305070813120c0609020414 71
    0x201c00800c84c6024140390704070060a4030416228441c55a00d865030326507190303a042e0b070328000b00021b0107020303c91401080459484110340c22844200b08080d180c1e481100c0c2700d081e440030309038641134074092501c4459010000c6c0b141e1085041c041030002d40c4640390f00f98041d0030361440e100381605150001601c002c200804164002c0c0c1400001d1200c0e85001c1134021503501c44003000380c0c0704c1d210382c00042c506a1050f08200280c0c004820185403000341000d806c00305034040c82d40410192104010142610380324003a030004210204020001d260f03ca42c445102e1885540c1541c00b4403e44c0c0c1d0000c0c2460306c0c1902c60325050061880d040c41031141e00444240c101a4250460071a5440c0c41c0149031a030304c41800c0015940008955032040c840c0c00b0514010455012409249040c2c0ba410301030000d10381900d0031000a0010000a1651640c0c5404800a19044030002c0310502c50301d1001c58411292200c106c54440e00d45500c0c60058480d4096602c1500220340010100d1810040c41d042c600345844440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 838234496 1250 838233246 838233251
    0x9190801110c1006031e020d151e0b011d030102120106030c090501020102070b070c080403080a030f2d020a031e0e0d050a0905060306010e0d0b01090e030a0801140a030215040305010f 80
    0x200b00044040301d0442c46840401b18a40000c0014000280d00542c00c08003c0c20020000e0018405d5000d998031031000c8040e04e010442089000d80040d9085820b8402180d000c01c210404800300d41c1c4200202c5032500034014000361506540001340c070509102a4408070100e900c9a040242e5580c1110b94140a40b40c2807000318213003905034139480206000031b04000d0512651904910510400d281101d0107550808502596000c61311802401888204070300d50b012071070701c003200c2240310f1201c042d00e04080c0340301e040041030050524108000c0d400248250b040c507030b442210b80315500740a5156001100c120b0070014506001c40042410820140d51000811204000150702c5c150040310798000d4900a4401d00c1e200d50324000141e90054170b807101b10364051403444071a4100013100640358107840d0406c4003800403901e042e00d410380d00d004842901c00032910301401405100c811003122300003018018004081c0c185c2d29004101401d1900f4000040b8540c001418010310000340100040300130000d1b004c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 838235746 1250 838234496 838234499
    0x3360f030f04170c1e0910080a1713060e030f01060501080c0c010b0406030f060b0108070c030c060612080307110304060c030302090310021306030609020f09190801110c1006 76
    0x100c00c441c8200e0252455403e040c03440c89122030310401a03040d02c0c4c000a00068001c40d4211100b42c0746001883d40203104400c44000900c03640c1915800404032450000205031701252640c85616800c1000b20300c4415010501100600b0020080d00d140280815110b211403158001c09260074518000503400890381800c50400c06c80e41d1165000d58030002042545448039051020079000d00041c22502ea40301d8200100401808404103403808490b2080b01c040200350284c00056954480840c0e102c0701203500d41c1c0600010901030f803071000c8d01c144118400100305450b0040200d81c26150710301a10f107880702000300111070307400c030949814101c1494015130529240800007400d100b10054010109500404c0c022002e490802205480301202001991103920882c42551410000e01c100030000b4101000010022024400c40e021540705210349850146008103021119506c8a400c50324903501d840e0002d000c40c0281b00350b521030900191156540d1320b401818501e054285101c040d0203d250000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 838236996 1250 838235746 838235767
    0xc05010c03290120010e1e0d0305160507050c040513121103032806140a0906030b040b09030408030a0203030105210706030c0e0a090e0d0804120503360f03 68
    0x311040c54050080104944d03140c2e03400c0240904070700d842e071259601c80c1100950428030314080710081c1c44120401c490301800003240807410f41e0302c02d440c0d0008485a003107100701668070070401081d005005400729885041c050307000c503040364401c40d0f410280a06002c031030420442010074411800010745800788110043d501d1142c0c5911016080d00660034480c43c01c01422001140307051001c00e820001082000e0343e035104021403a400803802403140c5541c442c00301c2e22281602c9010250382e005607150040e995155603040c0785020181c404142403101303020004d0110000c0005005092903540a10303103951419061080c0c802810070459040302640c201500644c1d40002c2c0d00045580c87d1a01180f5030910790780035100600c074a91156040800e170f89021445440d183c100c450b50f59468000c8650907003c005040b640003d003130317500419900a403090300540750b01c030754042e54000120020060f4207820042d42c2c40840400d840550076424824000c91126000500955880c00c61801c09940323010003000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 838238246 1250 838236996 838237007
    0xc1b072c0708060d0204091208040302070b120a02070503040e040c0906050a23040b030f0a1e0519080d020313050d030509070303112d061302011409010c05010c032901 73
    0x300114007a010503158442996120b4001c100b501d034010000c40234645014500500d050002c403410740161190742c0000942c007011320121102075520100084081d110140b980b8041c1d8801c1e04245e405100c03c0c440410038110f083c41e03d03405181b085810305e04103031410b08002e00365492684501d215000384c8804221a0482450260400080948080c1d4050740840001c005001001c489900761103070100c140c01d5a10001102e14569018281038504490791003020060b400050000a2081d00800060f089000c410600700a4051140f072031241401000b580740d01c02c0342c000700c0300402001c00c0b5403001000d10000b800b00c0540a2001e10703040c00607181504849070390303851500c0003c4c05c1010403081804502c1081c4903156030310f041c010311070b1007261010f02090301c0c42d01840403000b001d01841010513224820b41039688450340e4107841d154001141d0300c2040c03c1640001620606000041981c00c0c006542881618508503958030002038001c0840c0c5100409400d008507200d16501c60320984442e41c0c0c001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 838239496 1250 838238246 838238251
    0xc030405281b092c0a02010e0907031b03020711030c0901050f01050d0f0e0d050301050307060f021011032a09040507020f060f15180c1b072c0708 64
    0xb4038040b011180a07660711000303010340d9200401403072600c8060341e0007810482803d050802d16960f0070081c810083c40a548074400c032240280803803602251a5028102a034030076501224a06001558070302c00341060b2605500140c1280000e5400502a010440c100051005030101030307009001803100f9502103a40002c0600801c1d124005510001001347c0c40303401166484402081c0a00c000b0741da03540810040e03e0818a140124040e0030703480c4030214481c034252812a00024020281c6619182040d03d450303642c00341c42000c50040d41441c1c45240341d01d0180f021944440c40195941c0c0c50305010f0494014124545a88000a842c0300607045050701c205a80c1020000c450010307460b1540304040c0d00e411540c005034100c0c3d0107442c0c200030140c0b04200500740300340444000d402d40a40d60303808010700084c0e006003c4c1c041d00e00c3e5801040c0401c81050140680041d180101c03244030500c510500c4c80c2410940c407885032405244a4880030100820b030780d451f0b130a400c40805595040c248400307802003200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 838240746 1250 838239496 838239503
    0x803030f010302011d04090f060e030a08060d030c12020a110a0f05060309031209060901050f04050a1b0911030105190e041209030c0902070308060a0807030201050c0a06050c03040528 80
    0x645c01d0200d060103280300506060300018020001560390345440060000c3c486400d550241c41c0c100f10501128000c02168402c1d00c0ea0703a0b42101a030307035910810105801c803400c00d5081160054280c000030341500550b100c8940c8580003460950154034140100c404812101030007031000c510100840185404c0038015104115540c0e40c60b583d401082c10f2650046040c050358400700081800519500402c0c06409401004028421039607040c0c0d0384842480103990051041e480300c02030101040340c2103a041350101c5511700aa00c40c0c1d40d01e0722800b05550400f008a60b000000100400c160f01d0552000b104142c40034040c803401d1407400032a0707021084003c00141c004c081c140c1e081040e0034442c181c0d0741d0107142c0c00400300309110303102c1c401300d8000d42000408038081902a808202d0f07a03c1d029810008a41c0c808004010487c210b0b801180e2680111a1034140b51261000c204009841405202c0c45554003141640d105c1c0b8082c200b13540f414640c4447d03c3c403090308450452840040322a900001c1d19003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 838241996 1250 838240746 838240757
    0x60f010f141918270b0a0503060717060d020607120c020d030f020114060a170309120a0506160203030a0506130504110a0f050d03140408010e060f010803030f01030201 73
    0x20090030016a100c2d40605441007501601c520000c80d4220301902071210300220200a060303207a00f4461002c1042c40070f01c08010b2280100141d1044068004419460b0f0140101d10aa507407440820f141000507504d0201051000300340741401c41c130024803154004022030700c820303000015801146041c400c107e0050b10444840d060b5000ca980900e0400e2840c60b170141956040f0700c000e041c001e105001c442c900c0d0340154206075001c802d030011414118040c0c8401000d8020340783c40e00c54a140c03840054640b0f01824002401290041d54078042d880d0104000c00010340003030902450600d003000700051103d002c098161040b00c6330241e00006481d40200103c0c800109911084005051501400104091a42130604000420070b607800d0003040d05100382e80010205407600c0800d44140b03440e00440350460b4602807161b0210f40f0550403005000b48068005241c42c4d00c80405600b502e580e82c0040c03195910020038040c1070051400658010000303503024500b14141100c405ea142c207410310020f410420b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 838243246 1250 838241996 838242017
    0x1d011a1c0209070e0d0c06030501030b01140a09150b0d0204050a1e120f050a062f091003021207020304031502040806060904150c0e18130b0405010b04020d050f060f010f 74
    0x11242c0c403117981e03900d401c03900d400c4045582d400004c001d05000d0004440071271441000142d19030a0b018640e13840d800045c5042c80850074900618018800c0b0b150054240141c0c40000468444d444018901102c45400c0941c1e91030510081c041d1500881c1d1200703254204004440c1c0c0c100c005540902c0640b40f8019058100c4012414400a00001c02c0e40140c024086d010340901080340542c40101059061b1b0008035103086054500c180b01400a441c506840b241040320400c02d02d000480034201c4111410014144420404860454003080f200701e000750340300060610a00004070740954486044940941c0b0340703800c105070145c41c0e000183c04039000d03e1442e00458100040c800d014280d0740b0201c1410010544801c10003008a02d1843d0964064000c01100100a081114441c0d104507440d2103061440c508998410205080040043e52155a5010540029a560700040680200300c580204950030240c4120720311810240c180c03071083d08805000303003440c0d8210500c5450b02d2102d0402c20003c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 838244496 1250 838243246 838243249
    0x702240c09130b0103060b0901120518030705070602060a0227280e0a05011a0a020703060908090916020c010e0402130303181a07061d011a1c0209070e 66
    0x240219a221a0701a00c030b0028028090510b900c040b9801c14260307418001941c0c0c840c0c0510091092650b0140018094200b240f4400007a40100e5048402c8481041440820303800f0542540c01c07a003401c5070140c015845c1000031581c104076098214441e003100310710b84800c1d80b01c2101c00124a0701011a418140c43c410a41c5071b60b0710f159442a40822481c4901d101c480807265000b040340f9001c0e01c0104446100800d02950382c2e442401d041e900c010201800b6140c00c46004140303508524030050440c440d003a004000a40d081c05040f20081c441c0840d151101603007810440c0310704d80284030105204004c02203241d15a0300003040811a042070078082e03910f8450364041406407140508035100200e8a0400104040c0c1c07146038201d4a500d10780e00040c020b07071902112003046040940c01d103030303440082c0051408a80c4e42c2e4090499400894084a007085070401c070f05003907803040c0000d40078411602c445606141058140b0300d204001c41c031080002070403941e001414454000c0c3c21070701004140c1c00144000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 838245746 1250 838244496 838244521
    0x121e2319021e0318131b030c080f060103090c0810050a0c020c13050c0f0c0a02120f2515031b0219140a0218042f0d06290405070224 58
    0x50356501740041c000d054480c85040414881590300f4400640f03005040b41080b4450640f8a0099201c8052400e060b1240d00046000e4190b071201a204040150230006012008018240e0056091030001c02c071031900544041c200e0b40c5a04129081d50085045c0c44e5240c0e0350b0030721014105d602c520002510380c455a185821900418000c0709008000098010000c8400102090450310848102019441690240c0d8449031001804885580101103007a070024021400805c21a130440480720b405964140000121005030070034000319030b0355107a0313140c2c04210962070300c4074013a02d00040c8996485a2035016010340c0c0303401d020b09141011300341080c04460034444106400e8000300080d410018011013124225400c0e17130b00b1140070a8a0002182c2e01880c0d500c82c14607096015460507682114006100d03481c04280400c40f526560b0740583d071192209a12510010581c08485100350929a03003400200c4002130110310955000c400c01100803010411301e060703a40c44c103000c40302d403548904090a01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 838246996 1250 838245746 838245769
    0xd0e0c0d05030d0519020403081801110d0806030a1203380d14060f010e0a062301120618061403120703030905010204060804121e2319021e0318 63
    0xc17503000141c00424020054040d21001c0220302421907424142c1c070043d110100070381e0f100c5c1190380204a110f410940603042d5030b0b501180181c242d54404034195107a10420034907403229004690307aa6000c40d18564244000b50480003a080343c5516444580103400d10040c0080e6101c1c800d500100040041010b010416000b85040b00129003041c01e01400800360010240600340c403000040001445035100c0f030150204441090314134080c0a0b90100000501c20700048085052201c8102d041c1c01c15402071182100801100b5400d4800704101c4101c0401d0340c0c0164001e5580300120136261803d41c3d00840c40b400901160fa08555885503d490705601501c84902c1c098600d51020900041243c0c1000c0407a201d988038410650340416490b130181c60840c90604104c1710700305031040d20704103d40905003400e140d49d80c408030052910140301d0314030a2540545400b01042c80e006004a0505030100314840070703040400d12203180c1c0300c0f5110b13109075039014014a0806124a4440054154540d0201001c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 838248246 1250 838246996 838247041
    0x51017040b0708070e100507030509030d0302040510020a050d0c1a09060a0609090c03020105030a0e071701051803073c050d17040602130b0d0e0c0d05030d05 69
    0x100034603260910440400701141d01e200429034400c001401988112403d102400d00240440a07080310800212403a411030303e0110180107003001482240e5a0420100f0101c1c040c56a01694175804c140500c10001121141038003907502c0000600000f900100301c4514401c0589002d00410050741071191080111180c1001d0342792075401400081c1c1004118644101c20554040c0181030355040c0403400c40304010300240c2183c50f60b0000b4001503109000558000440c0302c00801d10a120f103a0041c14060180d104080c04815000e0003030f181d990038000c9980c800000034030060440d03007500c2466280e1103040c000030902058800e00300440e4496210305910000c840b0b0298020074220b40c2641e0100c1400e01060301e503481502000440c00f4814039403406c01800a400c2ca070115140e5a60300c0340690130000c1342120180c1624001700ba280b410740c01a002c0c481c90b0001c041064884005820300340680040b2450041408145505c081480081110307802c5026217800251680c23501d1041080d446800d1210703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 838249496 1250 838248246 838248287
    0x3160e0604034b0305090402041202090907030201050a18150507050708060c071b09050f010e010605030c090909010e16060207050406050315040318030f1202060702070510 75
    0x80180301e03141c054040b84900c140f024003070f100d00796114a410a4450390840c8041c480d4086040780c9444609000304295203e41082820161110005401e90b04903400c41c04559030011080c10a51405e80710b8640c00c0a03c14000d01016030a540000b00a4030170300122400788042103a02061306440344c0c0b8020001c0c054501d500d0032a60004070001c0603907000b5102500c251003508002700d00c80c01b0100d1903038040e42000b998245044401d49c0c4215945d2001c4030440454404d0401c001526004c40c003c8500c03912180210b204070358107044c01c68847c0700301a00a88100881441000450694a4100c40ba90401100c00c80403035600d0044190142030784208030102401000701060300b0607941152001500e40300e800b543e680030749503c02e00007140c14502c00d0036419882b01d2104030030711280c072081a8120780649810102c1198060b1a241e2a03070b041c0d0b00444000180c101005d0500c190602d507070360390340b403944003600ea03600340980000e40d0350100e4000c691081d500e2203240c501c91030050201c2c0b044001219150b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 838250746 1250 838249496 838249499
    0x4032907030f0b0a080d0e0604091103101a030c03130c1715060f0d1505010b0405040e0a0c15090302150c070f0305121b0f16060309020603160e0604 65
    0x207000d030140e140c107042c48a0a0811080b102d00d4039400d0311082e180c204004041041ca6100c0459003030a1412405401031010040491a11194012b100c043c00746000855542c0c02c10b0b0245929861040d0301c121070400c600e04101c0100c010420031641c005150300d520a480e9101d001d0003040c10f81c55030000074504000c1d001d0014030540c021211600c402209030075220944840346035a00300050488803150710602c0b0988400c2c45183c80104481c02c24021001c0001018180004204450080c1c2103205541c0002c0b508020340e03c0c050190020300c1c0c50100107408242e020f80d8840c5400c1140d8000e0152114022444a80482c445c0200c00300860700140b02071311500380b10040e40000e6115041c4004540141680464900c1001c4076074400c6030b07840ba00500e099100403101c820320f50001c0c020b4074040d81207082c0801c0300c81d0342003004031a0ba0101c030000d42881c003615548034405070065030200061508115229025035514800e5a50110f030341a002c0031080f0a0b443d0859080d070554100c1940706202240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 838251996 1250 838250746 838250761
    0x321171f0b0d0c0305010510020604080c0109021009051908030910020c0a060806150307020a140a140f010e061e1005061b010c1d040b010c150e0c040c05040329 70
    0x4080c400711584c07010820f590300e50090044038441280e242c0c1c0543e1003039000c2070010303078218000d1011104a00000a00a0483e400a9075170b029031f089040c00500100d00078006454940d086140100000d0a203c6000703290032002c546900400c0413182c410900f1081e00d58400740280011240d01e90014400310510743c84000203000355100b5a42d040c003483c0318058001101d404181100e0160307206800420201c100759842d089034104460400c00c0c0c9008032420040051944039044000c0b4004101521b03591600101c0c0b60300f1142c2110f2040c880e54082000d00c080da10750748800c0400541c00c00c400100b940d50321240e10151441ca640b0140c2c00a000117030308440300c0c101b0035644030501102030083c40650740700c0004607070005500e000c407030340d8588031076003c0b00b140390a41c40404003c0060600c0301c200d40841c0c4500d111020b007a020f00420a403134441083c40c4101c2404529440301c030884080002883c0c6190082ca14062400001c0c4501e2020460051221030303c4100c8102c09130340c0042e9020740ca00b212 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 838253246 1250 838251996 838252001
    0x7080609060d050313090e0109031b060209040501060509010816120f060b030a0c12020301050604050f0f0907110c0108010807060f23210f061c0503040321171f0b0d 72
    0x100750b80300149020a514140d1906000c9e031004950503955403c018158a4503034414844644030445000d5420400800e0760f03155401440e0007481503456103a12500307150005428000010104444030502c0340b8807450701500020003807035030100040300080414100c0000e034000e10f143c0d005080c4c0d40350080100b01d03420313407140c01051840304139030349148422942803028020381c0020301905e82d105100340f00c1170101e0f0600c1c507410810018020510700112003003101113050728034181c40f402c000405820032000001b90400001c00c016000f0320706801c0c82d61500850648621312405402d0800c160301c0040d40b5100d1107407055907010820340498803145004a8074103032640c0d014503e200030003000007a80416403000c0380f038880e110314103030561704155545280030002c0080c81d070010746440401a0190001041c000c001501c0914031a00b54030741903082c18017081e0260b11043d014081042056644c0394110038064402c0d68011041d030b00e91020380303051090303c04001240e030303003100032210000302da10100000144c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 838254496 1250 838253246 838253249
    0x7060905060115050310120215070309080115080618071a1c0608031206220501080c04020306030307110f0402030411010f02030a0c08031302030114040b0c0307080609060d050313 78
    0x43c86a0b48460319602c0301a240740c041100d800384c68002e1101e0800848509821140c0710038401002c0c182c070414504150034541c0c00c000010b40010300c0b14042804940c009220720520424070040103028145000001907403200014000140200f98010b484440f12042000303070040c0c2585048801106011680702446410075050989108a11001410250054810314082e20120405180707040c0c0811a649a00706018046542007101a86442a138840703001d90840c100740c4203440840c40b035240c018000c0c81c0004101001d4800d51040041c072101d5070700002100e40761507102d014802010342002c00150003104074021a600580004100b01c204107141501608582c8240c031100c809910002089070b03039000364490440401c961014000225165101460340150801d0b039400c5102c109601203070a4038004c0b038900c41104d03244028481000b48500140e64080d856101c1e4a04501c0c0c445001019008050100f0f800382079100c0210ba02c5880e640317419808141c021040300c0d65600ca103140181040c009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 838255746 1250 838254496 838254509
    0xa030305180a06090e0702120301060c05010b030607052506052e0b0414150c0304081209100e040b0406031b08120d020a0219050d1403040c061103070609050601 70
    0x9180c044001d5103401d04150b4161840c0390b0320381910310308001e042c4880d10f401600c0c2d242544034000c443c084801042c8000c502810b800e03610f0319840381c0c640c030b001401d450251031924440c0c1c00500420190660100998420b541f800040d204642c404140003a1808030900c030182c4038904040c100041d03084031040c00c00d59004040712100050b4858264034035441c90768012075151540421080220591000c00e001e08658020106001e4441d45940410a903210156805080e00081020020940c1c14040c40c0750300a4032004580c986030044000a00c0401c103400c4260a0003100000c481c11034445501020408034003900400c103080d00c0723042580b40301401809600203000c80c407001091018001c43e0300d00a1104541100d810010443e91080c065000380d40003100318401c5c4903080d29400100b100b07401056006001500b400071400d60000e011101c0d070289280c0f800410000c1c0070016640403a0b4104885140c43c2201e0540000c1840b141140b0803807501501c51414010705005202003c039095040ba01c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 838256996 1250 838255746 838255777
    0x6070201360501020a1a100503031303032d031505040905150115051e070c0e060405223005030901050a05100608040201030f020c06060a0609050d020d0503090a030305 73
    0x161071004a80d03410300007000034581840e803c0246d8042d043e1048540d04280d58031030401c2c006443d0000310380745810a0401201c015103080c0d041081c9a002000c40c0400c24000741c6007c041c0301c40e44009110040b1544030502019503a04100b030318000c8540b40f0341d01501004005000044150038003554804101d545500011920f50000494841c00140c000201d4215110907042c0001d80740312102041000c0c400a500003001c002c0e003030020385c003002d07984050403600c251801c0340e040c01000d02088917130081656800949520b20846440d000352803d200741344c2e1049490700411000080b84d5101001c0c110185411182004d1111540b900503020b10b11880c201c100800c00d0740d54030003008080c1c0304203440d1400c031813250000521102c0e125100d40d69200d8011f04001c1059400311044808907404450340340d8090b00804107202e80c6181c10180100103141a2a001010f9801c2100248600c0c180c1440244244810707003460f02086000d0007aa40c0400c002483c2092065032420003529a90107018901c1c680d41c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 838258246 1250 838256996 838256999
    0x14010f0207150b270903040504050f090d050a0801030b3303060a0216080c15040c060e040e0606040b040608010e0328020703021c0501090503040614180607020136 71
    0xc0244e6802009a4581400034485074241041a407005024090301e550740001c000c04946a01c4500403035008a010b0308018031189031403007040d0b003004502e0100d001084020898210b4443c2c7c0008401e041d2034020062084c03540303d46060850020081c80700e81499183c40303034070301c1e001180000248400d0314203900356001da6507510000b10072072003071080d0380980c121150001c00200c2e040f40b0140070300c0314601c01180c2d40d640f00c003840c04100c0442120102c1c2e0036002540e06005683e03001d8040c0c4500881a030382408501d0b40301e00c1480d02c0c4ea900611250059558925600315603885420200003014450005c10003940d400110f03a03200d40c0020030070034020100359000001190304442080c40c0e40d000c0d5015110942c2550300300a820760140c2e161100c007454080c40000854400c3c82101249441000156692840d142014054643c00000c9099141c0d0070f101c0300c41d410401c404014454030b021030344c80b640c0e90154070060f107240c01d18800c070002e954071603050084210102005071500c80510040154400d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 838259496 1250 838258246 838258249
    0x100c05250806060604060810030b131a090d082205010507020c180402011202190305010614090f060702010207240e0a140f1302120a05060a030c0314010f0207150b 71
    0x101001c1d650f4641042c000c21040242e58400c00c1c806400805285011040f2a0360346c42d654500101034034000440c040146000080024101c1e000d8202109490a40f1042c42c0c020a01c44d220514851079205004081000545c41c0460b4000c0c0d030814074111400800c18000790030140d000382011290320001d48198080326104d4078042c0504070203910f03e040180b4840d55254011201d00318405000401c1c60f0f0280007280700103940d112460340c112855640000d5540c0341540017042c010f00000c0d8000c120318200500c4549840b090004c04c09220f00341d07202039a60401c1c6c40105d05d09003056001d031401151940c04582c0d0b0303c20b10345800d0340001e000c0d030300c0301117290030340041141c203919a1040c420340c003551003030518150034803070341184d10701c0740c010190203004105402d6441681c2c801030b24503103d404100100300c110b903203038403072150001005c1d58a400031605554412a00700510f0101900f41c000e0000c400e0341c0c0030400d4003c10341c4078969503800e6442d072400d4644000070656880709602014108101243c15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 838260746 1250 838259496 838259503
    0x60a08030403080f0c160306020c010b04051302092d1006050310090e0703080c030d0e060f040b04080408120a0f02120306060a03112107050a0509100c052508 69
    0x281ca400100303280ca00000c032541c0034403590001c1c08070401805918090780c81044d10306c480c10000c40c051100945e44584418600b82110400303c00240309501d0001800042c0ea8405002c07034034298160344110071501c0302c0c0b1082c030754801e00642c000a5448880003119a03048080b040a000b00641040c0010031503c411058030b450004850400702c181b1418010001010380e078020f5449400c0c128280d5811588030748804802e98002010703021544d00004000030061118460400f03942c610101500b03150a02801c03180c1040d0001e04080c026020220210f400d000003d4201c90040150008950901080040c1040c998010a9454000ca200400c849521a002151000a0203101c04442e841c680e90030081000d0343d0800f280000c00c060343c40001c0d00403044080003c1c0740d811948100c3d401c040013180340047d5032080c01400901004014000c0019140d00181a2101035400301c0b00e8103214814007000b1034116035840c1001d051807003580041d10580d8241c600c90880f20142403103d58001d078441002956 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 838261996 1250 838260746 838260749
    0x604120c09020f0d05070c0f060204140a1a09060d0e0703061118091306050108032206050d20030f07020705041104050d0302073b010e040609030201060504020a020105060a080304 78
    0x58040704009130b0000c2d2002d5400f83d5409449030a2041c0c002010b40c4690500d0101040c0840d08190b001030140240711201208070031620045a10413407103424441d0344c441980214107a429001c00210300207407599070f4001a15000c02c45070341c041040750b001e070b942595140107500c03040d11814600718841d040a51000300300c4440c1c1101c10041c810b10003010042c4461044024002c801e41054842420300060b66409102d0003002200c3c0150348600344400c518042c08a0540035502e103c0c0d641508001c031541000c20707224452403500002a0040e0307820002071082e07403000603840411000100b088014064041241c0c0a00115400c5444290729001800300f103070f022038000c8401040a100c100280d1401c4d01c2000b00c52440b0344160303030110343e403031001520418640d64454072310707013070070081c2030b210303203140c9030894406107039200701e2910394581404199040c1011300090038060300e403034444040c18001d41000d402132030064021540d603601c10310004d008100039103030b40b449900d440c000024a40340c0001505c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 838263246 1250 838261996 838262017
    0x320906030316060b101e11100b0301021b01090c08060601021f23041a0601200a0b1005040501050f4212070206070207120f020604120c0902 61
    0x519100540380514002c8101c1a81110440d480b11000398a64036000c01108000300355440320000054910840c0c080d00c80150400ba04001344031241420036400011a11140c111200740010000d800f2808030b400b80c17050314846034501407098140c01e09681d0541c48200b840d406114080032154850900c1e07512140e040c2e4015005031322481518110170010f81c501c40e17841c1420380c000180d03d0f82c28001c600c503078038801b0f0707800c8001c55401081109002c0f80c207250407210510210040081e140c8600040c0100ba5050201c91003c03181c64070042c0100c004000112201d07801006440b0b0707501c0c1019800610661501440b405281400700008040c14031140001401c1d000030058203217110b01d1038410b002c4503440c03104045218810804a2040581100c00d01800c8002d2100d250341c41c0d105250344850940c024041c03400310f520040410040c50b501041000c01d4036a01100040380b0034490400035401c00038000080c2d0700160004001480a030111510000c0a10494000924075076035201c6000300d008169062 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 838264496 1250 838263246 838263253
    0x7091a0907030912030c0c05071d07030e0703030c141b040e01020903060105090402060f0301140f0d05060703050c040905010b2d030f0604090503161709032532090603 73
    0x1103500c18086c2d0015015400c1c0303450601d140303042d0b0341c03521864405242e0066440070744040d801d01010851440059010100d82814001c510080351304550304c000610002d010801c1121006040260302c04181141203145800c0b540c4140809880461640d95800c800b84501c0c6005140c41d40701106000783c1c4c0c071a000044c054240307070f0700c0c140a002c111640280103c0c0e01540400590400e02c112002940c041d12020507692003400406091011044100c85203901c5074041c0c99000e40051000185140d000b4920714021409480c1c00d0000001c6000f81e0300300d01074039410700002040c1da03071030300004c0c0042400d0710b00e4083c2c00e91220604a8a0448441c203252200d130b0302040000e4084c44000012600800c0140c0005101c0c003003601c606040d504061703130703800015184404000a01c10007031545040e0110b513010551509814034000b070364450001006522510036001302201030b940c12076a80c0028030310032801d0640c01081380f080c144000540201442145010a884921410801d60301c600c90305015004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 838265746 1250 838264496 838264523
    0x20f0a1502090118030303050601080a02030f191b180e09030414010e0a0e19020c0330180f03040308091c061d06061005120907091a09070309 62
    0x4403010758000300c0701605200d94003062900c600b46820303c8000850195500140d1418410001450000080c2034614541c1c010300c14418010400f00005030403000402d02c02807480d13000c10420001c0c003240c6890080180c02038199003200703600940f071500074042c0000e407003640c2501c45400c1c0c100ca02041d501d05903694801c0c001032012980c1150455903000050401e21429552807000130405030454200161f03803000340061003003100394120043c5041c60311140c158203002c082c90b50b8680e01d00a400782041176640040346d074a6203540221000344400100351040c80580381414000c0b02402314100668224804da4808181140d001300a0f101680c1d4000000c1d031034070b00c51008101c40340414000c0c5030908000060000e000501c20f1003440319034050b12074034880c1d441178031034500e08201c0002c05030b500402d0829103102481d64004c1c1201c49282981160307105940b102c009151410046401601040b4a06551a008801c80d40f8150300340f01e5040300c0c1c0711496a20404220709980c4e60450040184451480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 838266996 1250 838265746 838265783
    0xf070207030213110a03091110050d1d01020a0e030d031506030c200c041518380f03030c0604060216080f030106140c1504110306090d020f0a 62
    0x5210b4403d11411004641190340740c0e44c01c03210360b11800070300d070119a55924000422800301240c6103420750846070348500200550020300580b040509801071181d03910031020b109a52090031704004280c03e402107444100210b00902403082100b0703828402c1c41095000080d0610a00480c004200101c08000f102450524254050003600205009100d114184084c201d49040c8400ea1911403d1004110005c8400e062000712000c000d041d907102c0411040078010000b003160000440c1c850319500254100f11042880c5a80d9482c0c1e4034802e060300120b61004000c015049000c800d000c04444149081c8940b904242d52840342c9801c494140e00642c0001c2c000c20119800780c0041205891ba030f140c103800030760340c2200b0341d032000d10700c0c098072000480107001d0280d114101e8208148080e13051440c2c6119900c0703103a81d40c40000c0c54000e00c00e141c42e00107030401100c245c0d42413074002c024003280c1490800c580510345035446c50f10000014800c03401401c11080c000940c128025400185600e5425903046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 838268246 1250 838266996 838267009
    0x61202070305040e0702160b04050a030f080405060f0c06071106060907020c150d050f071b0204060306020c030d0b0303210c04050307030309080d03020414061303020405011503050f0702070302 84
    0xd05806002052200013480c000385100c203845404a503018265800f86803449808401250b000f110f21050280410301098844c0a503100640790809540700a80da664a80390360103100d945c2120381c000502088201400d50340c0d1303002d81b03107143c00c44060761b10a5417603a83c110352102d840788402132540d00c1400801e9450801c12000c580141d21441910609030294001c03c2d840515000c9001202200140080c0c4c99042486065044030203a0f4801025040207600140385070004401c9103600b52103408104219a145e41c4098025540040d040d901d40b0203594010380c03250840521030404d517061680c003401034503000c4110b40c101914411512442c2e1041c0170f10f80341c00c0c80014410920400b080001042d25501088024010340c82a0f40350000181441611418a041c100c1181c0a250050006201c1601001200218200143c2d1240d03281d800030a250540400d89620207034220b0b10b00400031411a0140740c1c280500f074043d440501581d1600040a4959035084540b00016000030205000529000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 838269496 1250 838268246 838268257
    0x18060706200a030c02191104060f06020a021c020102070308031e0c0405030c030c061c20190206010e0708090a120302090f09010806060f130e0a0c050d0b060f04150f1e061202 76
    0xe88001071271900c03000082c05140382c680150025030300c03031186d2404618200c1c1e480030314010000c10075041450140c0c00071f9030340c034081d00004000c080c012000862107000520004540d0b01c0d03820030f41c00c1a00749801030305560346c0540182c6010b801090a2008507080010301440f540c3c0028005d140341104501c00c803050501801800a07a494994090764283c50b01907090107405e442401c01140c2e18403006c444480342182c001d01c55000d540100c801005011216182c1d198094106e051800341c0d0b9465000721410841c01c0040200840841c507040440a5030550240c901003070141d401001c103075050001c101581100340318228240e406840002c40700d050012070420820b401501c1c185012150b1481c5074240c0d0904080c03c0390310f070701c00b00510052005500c51800101000d80300c1081301c40c00317900c5445d5102d07001002c06000701e600c01d41e4080c9545480c2e1203441c440c0d0b05400c207404825191441e2082060340791003400c000f840402e0f0407074401c00d84d51003000121402078440100107043c1141c8c40000c0e4105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 838270746 1250 838269496 838269499
    0x60503061005210a02120105013905030a080103050712020622120813090902130c05040503030f130504020f0412020d120f021218060706200a030c021911 67
    0x22a0083c0c0a020b000d031002400b4034508400580c541030b440c8022000c40c00c0c141e010034100300051405140740e81c00310401d5001000b805070b00507510042c0c1e01080a030f60388502401883c0740710002d2203202c2c11703921580f05d90680e4071400035252140d949116032401048808006035004600f00501e4101c03810b00ca650034500301844042141a640d980300944203079602c00300641e2010f0002a0982e442410044070f04040c04050340200020011a00407800c5554000b0605045940c1c51150404050280d03050f140117000080440b56585862182c021070346d009690341e007007448000038011542e49054007d841c0c0d600346031131619003483d01e07042019451440d020002c0e40c0012400643c0004260900c6140c1d461041946036210011000c45009180460112500d8208407050001a66402d0306a41c0c180f82c02000b11202503c448681c10294001d005420156103604418102d032025844100094a00007841d80c80c100000c3c3d44e07504059032105581c90b09000901c0c00c10b0460000101c0c99120781020090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 838271996 1250 838270746 838270777
    0x1f061d030f1f0f06120c0801050106210f0c0507020405060603010b0708180d032708120901020c1305090f03070b0a111204080d2003011a21040c060503061005 69
    0x50b032003044021590150007a428170622400c11320103011244421800400410008000d2980341c040c00400040c2c01920030745500c1e920120707503c0c3e552140d801c020074503080c100003041413000051002c0d242d0350100710100d014500b03100c002403041c90b1143c1601d04a403440c00d0081d00d8058196a044103660152241565428082e0b110300c1840e02c07480100e8898074802d80b2034111081c0600601500c3d10600412590185c103180000d000c21413004c030b080604090300e00c00c1161164000380040c1c0c1040e07048600c003074200046002c8181a5259034120502480180085d1408a00170051240e00c901c43c14101424000c480b1011945c43c10b001d030722214840d01044003a5041600c50808000c07156426102512600000f080c480d101d084103106000010403210414811505c902d01c40c2501070205102d03140d0600054078980352884240c00031150380c4214281568617440c2c0c1154050038540064400344c80703071011701d000421140c1c020350889010702002411800c44204001c0f0464040d4042c41ca040040e54 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 838273246 1250 838271996 838272011
    0x70507080a0804030606140f010807120f0f0b19050d080c03070605090708012706091b090513211806020109060c0903031202031f061d030f1f 62
    0x280d003840749070300aa10500845582d20300c0d45c2404400d6030041d410040d000c0c0603c41c0540200e07a1421004000c0e600d0a09080110b592640e0b81514441b08a00e0503e2250b81030600d1034003141d8650388101c402c400d26140c1084803450510520001408043c101181c1c1d01116805210310b140404181c0d010038802c0303880c03130b1822488a44250942c0c0200d0021a51961a54148509030a0600c9600007400c054002002808280c0d226220455203a0054000680742424540c1c14490690050601c050700035101525400b0a030301c50030080c800b184644021549007002240c0c038615a4900c0c1248950048200d4103003c0039540d0030708000920400c84401e000c0c031213004001082c12002d000000704034903000042e103180e0a00b410750a80b1101440c42040010003d41880020f03040080105010708001005840707940b561100d803000c1403032414021064110502c001119540205c8007200c80004107040100000c207181459a24105100c9041d0240c01003c1c0d01e20250381e09400c0d52402c4611542d001c00d146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 838274496 1250 838273246 838273259
    0x7080706020a050c0609032a0a020604150311040e0406020a0e190303080108010504030206070807050f192d0c020a1214120309030316030207050706030621080a0302070507 75
    0x282d118035107050201c0c4010486203e041d030184411640082d214000c0c40c0341c00e58013000305040c43d00441c8100030750b0101d1807540551110401110b18001c0c0d028141d5545e80d03032942404000c88150042d80c0e03001a0030400360001640c2854262401c4030311b032000702c68030307500c0b9139803158003942042141c0010800c00e0f454000c407136a6054984914585000106165070b811405c0003401d000e016001010b041c1e042c4001d0000017940080c10503440034461400b1003150301c0304d10046511744949030700182c1d12000812106011040c2d03510340e2168a0309902d0b100396500c6e403c0340039005d030403028a14101000c0c0c20881d5071a110700540452a01e10703c020031902146440d005c1003000e80b0808501601e00c8c1000c0704003805c030711504010305900c0310b9802448504602e05030460558900c00101001007202c145103003a0001d5000e6016106201d0f4040151101151201c01c020001c0c1018401c3c100300e0b045211380520903040d403414201103a0342101c4c0c014605094004240d01a40c401c50b4212198801c4040c0001c41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 838275746 1250 838274496 838274501
    0x7080706060e07090501021516050c06070305060f01030b1e010c0f111c0b010506160b090d0f0903050318150a05210c030604051513060f092007080706 66
    0x250142e891414001d0400c0c050003803800015400c014155442440d012402031001204582c1c050061524220340740c81460701102c0c5070182d0f403100d1407244151800d02c11000d800d42c012030f111f00010b035540528505290011010b44908440d842c1d000560103400801000c0c1040401c00134003010f044c600c801c0318450791a1034111410a4080e41d28084143ca80030103860702078004030380503130000300450f0420700c1c1d611400305c4031078180b0a05d4400c0300005592149c41d10151000720102d6000303410800c0078684003841644600c080741038080010403c5000703801e21406400c1980989030400000c60070540c0000e00c04103e010812142e5501811040031038aa96000c000104910b02084d56002c3c0c03a01c0350b003255010031075074001640e2035140d0010100700c1025074440c00c0d60b5014408840c041001d8840070303c04050700b151200c64a401c400b000c02c612103d03815079081102100c0c00c040c2208541541c03800c80804440c00300449007076640c01c0e460082c1110000c0710107002041e0003008420b2a102d0150707500000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 838276996 1250 838275746 838275749
    0xf120b0a080a0b16030b1503041b0e0402190b0f071a0103030f03050c03060f0409030e27010b1201033306030b1026150717070201200708070606 63
    0xf186059082040b950448601d6507400b104284d007070900103001c0080001d260128500d011aa0440c00800000c0078070500c4441a002229054055512170303403143d0030301a1958080f0303001c0c0e004001c0780905c40b20315081401d2010403074820490240c24201c10110950496001a00650f42100d66440040304503c014210500941c400c1e02d48270f0269115110280946400401000c0015810b0040001588408030340345c0c110311040720001441c48691506481050001c170300c068100145c00c80790000000203817036140590720b0070054021b2036030343e0b0349003034100b441018082c0c00302809030001000000d50650850301001029021811000e102a4541031184410740d070400d0a151117400800c24080aa84610b4010400c040540d0700c0604140c2141c24070b41490315030b07004049200091040024007807004410480f01c0140d0145e6506080500400090782e00310b084410790b240c0340c04166058014490f001c4c40f6103c44540c44d095502001c41520790750881c1e9419542e4407010028a000100360740f02381380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 838278246 1250 838276996 838277003
    0xf010c0813060f050a0905060d022206030b0306130f0203030403060e0102071106070302070b1804050915090d091e090f0c11030f0f03090109020d0809030c010f120b0a080a 75
    0x100d14900d0000b00a01c01460301c040f51060000c2041003044880d03006410105a401c02e58215544070030081a0074000c1c4100801f41e02400a0400424015480c0b015901c1c2240d00d203079400c1c001803030214100341c1c403035206850301c0030094005034629000a40e44c075248103160340020181c034101541c03601c80a040c3c0d02c103c5d054401c00d03507000074001c0c100001c002d035100341c0d1441a9101401d00180b550080d5a400f503034007601610309404030380703608015000d04640403621000342081c403041c204007070f03003c0d520500182e00a0041504000290003408000b506410310030883ea40c0039100362826046007015000901c0c0b1f40d1301400883e0010803e0101e50203507103800ca40d140000650003030f87e110001d00802c807075440d4481c540c108105d403500404070507054400300808240544e90300d0320b6040007680100925000250031103044121176040c40102e10181011140c103030107944070411741d44011a01085842041c9010030b441c1d58107030b0100c042c40d5101c103c4480026100c0a00c0b0b6454040300d9151804005044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 838279496 1250 838278246 838278277
    0xc0203060711060708011d2d0604050901090803070e1c142e0b04090615140405011a0d09050633010906080702070e0124020f0303060f010c08 62
    0x12807020b074042085580c071590350701e49030341c1c03e5061074000d03800c1c54960100040d02c80e042c00b020883c1e9813007074460801560002c18811100007070b4100b80034840103080741d03403030312603850f00002540f80101070050104075030f4003001c004d284d50390b0780500351042c0f91503401031038200303d0600100102e40001041007403510b0003500403414600c003010314649425103104426408104c1145600910384903d10100d95403800c9100215040b5404e001240c0101082d0754052300361801c1004140e402407016000c0c0c01640d1401500c131740303251305031030500c0180c440a206484003c07910b0341c0d44c203055500c1040501003d0081c43c5004c04c0124403034844a182200070703107105840040c0c404001b042e200056095030f4445d1903031251503c07481010000a084101c4a00c40c0505000c114000911168800d1000300060b00450f40c81409039612303003802c0d0005000010700c80c08030300101c0c444150701500001d4120729090004000310b03d03694494090240200010507802e040c00340208080000840d5800a041e8228414440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 838280746 1250 838279496 838279517
    0x100c112b080a1113170c0102121b100903090914010303030e15010b0a0306050a030c0e0c0f030709030c0b090d11151801020c092505091c06050c0f03010e070c02030607 73
    0x10304080208404041e0215032110903e05400c1c8d80102e142c254014044034000e4450180c0031400c280a90f82d984080f03c58010341d000501c108200d50304c218611406560340454a07901c0359180403c40e20b1409050744002c52450041002074403a0704140d5003085110180d0300464200417129283c41000c0c3c0011001040208110341c503a580351140c400240400c0f6041c1030b4a5245440e0440b568000b4011904000c0590000902c0410310200715010314641c1816031ba03a900c1c01d408010032902e500e000c22aa082d45034600024041303d2007095800d10000100541c58205199072141e06640f640403d007034001d64140707a00c0d4100762004000c0c16580707169040601d01d01048000090400d03080803146032150b6030702e000f4400d0a05c49102d005500546a80e071175040303804468001d4401e40502c11302c06601110040a80489002072107011140c6481004248510b4554183c1000b1034003c0c61602e000320f0b1014070041080e107500600154001d640f505200f40000035580200e41000350071500c050100f10182107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 838281996 1250 838280746 838280759
    0x6020a0f08060a0b0403080702010c0b01060908160503030d0c020c0d0b061201020307140a03110d1d010e0c130603290a150512100c112b080a1113 64
    0xe0709a01000840d074941d000ea00300400e010300742c040c5d070101401c02140450b0000459000d443e05d44055a08a062080550395810004001400c2400741ca810b80c01a8840c0c1e00100000e024220140c4200074042d508041203844c0e408010708004818500314480d01c204109181c4462034208600c3e40501451a2549020810b210b15484405141c0500307030b20410030443c40f1903001c071440a40e600340040080d628400706a044000d4104100030005c00440000c01e9078001c43c5c01c0c1c0c800e0f00c260403e50071440b41002d4503e4082e00321015186a00c2458020a410b80d00520340681624008601510300160294407a20741070090549140204c903541c03266600181896813000079036902448003801407201402c40310300110b48a18601c581405160f51400c030401e900424085203c04c884491070401c89905c50400040c40c0c0b107480078905a19002d002e60f189183c40a0424400700000500b0300500b1280e80500104c91440700100280d000719a200000300031114684010800301050a9490340704509115 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 838283246 1250 838281996 838282007
    0x1e150903170c04060c05100501060f080709030b0601050c15010f0f081204030602210405030306012003040b030613060803090406140a0b0d021b010e06161b0f06020a0f 73
    0x208501c0030080c0707550030041141003400440b8181e498900c2d001c0c11a5980d40741107442c0c01213800c600c804060600d800405c950343d0210418400050a6640741140d40740d000c0c003550011428000038207a0311030400055442e5025100034203140d0341280071075050603032032a401c0014401c03e0b04600904001c0040070081e200140282002500c01000540608030300c2000b4030001d44680c4c40002c080750f4010401000b4151180c54a81102c01116031a00b11498149040e9449620441e40c05003c0b8603038040209400959602d5030000117520001107103041c0c241b4503042000c5d00000d1110f41d1144a421010307005010754002c5e00d00402c9a1030040d6100e9480408010a131380040d04203055030f4410080700c45841da14510890b00b00d0782031000060703a819a54142401901c0303074180c041c0301031203002c04207810145c055000d410a81030b0b400079140d507a11221604000010a403040d0b0300080d84640d10784104000607139494017100d11460500301c0a0000e9940d807810790b004040820040741e10f44290b6101e0740d8014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 838284496 1250 838283246 838283267
    0x60408010e0a05150c03060d02010c05102009090c0304141c0f0536280e04030c060b1f0201020a1e1d040902040501030c1806030f1e150903 61
    0x200442911403174030340d00c8013001d400003d041c1c074401c403400307180d031801c0d64060040400460f8100d400c0d2000c9818002d501c0c0050700c061010340400a042c405600f0b0034004d80000d46400d401c0081580585ea110407090980359040900281c4140186000904000504116401800a1805041032004d142450240160341e031205210b00f4801c081102c1108008282200d000d40051008200144810074494a4070300c1d00c561002600f10b08000d0f03189200030ba40451140c1c000c0803400d407455415440d6803103141d0b1140240e500a0100e44c843d10b80e1000562039400c1503011039005000d0b09000101041c0b00c0d40c41903010b1940c0030240c1d5001944010103584082c2c22003000e140a000c1c0c075507441d1307000300081070307440d0300e5040352a0001030b81e81901c01559540c01603400c15400800078402941c40b81883e50481d02c6a01c21000e24855000c2c00f0000d80c1e4007406940c0849e500302c1c00b08880d42e030454507034180c5480703401170302040300402c0008900018402090a4159210a100000c0d101d043e03103000b50050540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 838285746 1250 838284496 838284523
    0x1c14010f05040f020d03030b030f03250b041205070203030712110a0c060f021011040510030b210c030a111302130b0702150f03040c140108060f060408010e0a05 70
    0xc150401001c40c0802d6003034543c0e183c2c1034031005a1711016080880044c2600c1c2102036150158004071540d0181c00070261419054000782403550303402c40c1c05010907041d051880140000e14500028010404405115600440c42d0401e0782c80c000700ca41c0040c3c01e5601402c001c07074000c0b10010210841030b91001d11010f1a00204005041b100070300e8a5018110440b803060310204491203180e2400c25100f070104580c034002e000d0051242d80c200290880300c075040307802201c0c020300a103c1c440350f6640c480d01410300c51074405403003040c8444022000c0302a0300790951a401061185010710715071620200b091101407400b41c00c5960164000c80100111b000c2c2c50038400b4011401482500c0c0040c41c20349144080300c290340b410981d94105403010458214030764404403490000420a03110400f007c00045216521482c608336030683c90382040f4400038921054140000c280c44002100d43c18503241500400c44010145814503503540310017801c2d901e400c1000744040d0007000030041040310801646915920 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 838286996 1250 838285746 838285751
    0x310050427032003030423070b040305030304051213050105090a030f060b030606010e1e1c0b0a050a020a0806090604202503230d0c0c050c0108060d03030b1c14010f 72
    0x14951601020000300f030241d41f0140d5443e904000001ca03080101c0d0008103046141161615a2414080d0312600111400d0300c050250301d0042a040410038215810030395111408032210307013030800455040d00404c006540010007500e000c408203121202d6508582e11900d80441e001c0e100000b410b06241000c1d055a05000c40300105282c1e5a60340b200100c04181c0440c0c40c00b9000c1d0b0802c00040c040819175064103510200044480240560494a04c0c8035680e01e02e400c0c0300f940c40b00000c10080707100e52440c00b00020b0f01c260100d60b051601035407054210a0040000c1190b208075407030b80395821510301d1100200000021448000d01c05da420352807540e01c0b84400302c0904400c07a14050b0500a542751800c07404007880215040e070020040a841160440000800c00740d6005207003d4425a02480107031050b2080b01410869036206503101c520500d009000100144000d43d81038003c0e059100e009a031002840f003c26490200c24062682641c0c0540031120001c250745030500d0031204c0c10318250070041e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 838288246 1250 838286996 838287001
    0xd0b04050c0702041a090408040807050913060507120e03090109050a05090f040303091505060906151e1e04030212010603020a03080c0f071415031005042703200303 72
    0x40514040d07440b110740545000c035400c00c10408484043e00311885a540c84183c60040c030050141000103401991444000c0700e544617200c9007041542c49089480701c0d40c038075221804030b00141490304119007040e030b03d08260303584102d000ca0020a459071400c00d00760f5540082018081580c0c4012403c000f0401074601481190a0038040354205200405003070382803c2c800c01280070103110b540403170809508840c0c1d001d4024064602070028001c191620740c402d5444001050961070000c000180d000405901c00e4508410010841c1c0280400d600d0784280001c00e003c0c2c4195080a14603401c0c1012460185942c0d903070a41c41040031050ba032402090650385010410303c0161101110901030307075003001030151aa05e4102000b8541800c1c110300100038000e00704001946031420420644e09030040f2000001e0307240f10300d0030340e1072400202c030840a030450304101045242840d03440307000244401e0754011310f0301c8131401e05d032020a04120000c4001444009448600610302050070811400e803001561860 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 838289496 1250 838288246 838288261
    0xe060109051b07150c21050a1121090a05060103050f0111040e150406150228020a0e0405150907050a05090601122403060218011e1d04060b0d0b0405 65
    0x480d60585140000f540d11046851110300440c010b21b0b030541d1608007410314110307018000010b40b406441001240741002c9440042d4041c001c1504c842415150003940303020312030707108442418405491a5014000d031186500410003d002ca80d0184d80104010300450354070110321421242d00c001022840da0050100b449141ca0a40495401200102c00c8042950441c40000d0052025501403030064100f2004008242d401255100b0300d1400a20b03541e800300c40548542400c9040914002e42c414030403a0227002c0b660703000f0301c5039400502450845004024503030b00c0481150042d00c201c0348560018104000c3c914080580740050001614540c0b55400c044002a00741c113070ba64550f05599840f07040c0d51400c8403400170841541ca16148402813081d50fa414101c000350b00640810440100880d00603200354001c0e0040c541c0d089652100908405089400300c4000301e40d0740195030031040b42d02292045554600404024182d004109580c61130440580421142148040390003641030800f0040e0b01d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 838290746 1250 838289496 838289513
    0x30203060f03071203050a031803030b151c0906110c0a0b0604060f0e040f05100c030b0306160c11040c050901030e011e0b01050408010609090b0a0e120702040e060109051b07 76
    0x1341075141c2000741d220ba09001041d0041c0200c08a840700300383c0090800801e00d6410b0b0065642048141c0340450071000040005031903101e0300c0800303000d0700c0208004142c0c0c4000e9500c015050780c000c0b0000180800d074203008141e580d00480d80715042d6889400f541c07041c46a036211003500071004880c20080a840c1280c80c4030040c0c45403140c1030305101100001400e1100461808008540c008151000b28103071140031f00082890540280000e8a000424001b0742400242c01d23000d40020110141d00d0044660119580c81c5001401c940d001902d20198083d40c6590140c2c00e241515901c4494840140c40c000504032848002902c0060381400c00f4010740700000d02c06418980807054002c982c1d4615070005903468400d5a001042035840c24400050b1285598003550089205000003000c9403200c0c0d1195003545d5403042c001409421000d486804180b403c0300034a03203a88003500c007084102030b6503150b03418075000b64014034103203480c1d03410000740d04028111507050303200c4050006d08040c5540c981c23100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 838291996 1250 838290746 838290779
    0x918040f030c110405010905070e0d050307110105070b0c030609070c0f0b090102070803100f0b131e0503030d05190c080f09030408030a0f02060105011d0d21030203060f0307 76
    0x14440b0144001c428042040c50290003500c0281c824012940d4802c0704500501048031030400141285044800c2d900e04201d0300344034145c003d0011400c0c04c2c001e40380c924840405400c681d0500004101c0c200c00030380061112480341141e494215180e02d403800c148101075030001e110400304010040020001030101148100c041c0d0040301c100440d9441c105e2050091013802c002400d5400e0100c1081070006e400404182030b240130900c83c0da0035643e907071100f04040c0a00c00d24801c100550740130074090390441c0c0c800070100f07160324003081e01102d964101180c1140c1c03080d1003c0070450b40718005c0011400e04803819180061030528208440d4001c4400106208005059910340e0031421012800c01c02040003510050031510087e40c2c2c0d00d001200f8041d2056005807207020150007000d000240c5580030740584900700410b10f801000150040040004090444504030b50036404000480241c151242d0401500030b21340d1401070303407800d103602008116410340b100544607900020040c40008820904000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 838293246 1250 838291996 838292003
    0x1140106030e0a2301020d05040215040f0b070302030d090b0a05011a04030212010e010c0f0906031802061e04171009050d0c06141306200a050f1204080918040f 70
    0x4100c0d9401c2d2103030f00500300300440c510f00c2660000c559403c0d03c0c1c6140d40a5800717944200e2f04880028040040e800b51070159109038501c0e85140030701000b00644420040c40104d10a2042d213240c5910646410101c1daa000003d80c1c0724000c1904203c04800356102c1c0c680580b410f40090b80b035540d17100c041c4503800d00c52030000034010681c00480480081094009202c8442610001c1c0200d4885180051000d903190042d200064144580050b84034003a00c0b4115449808008000281c449030b005c0c00305035401031030180007200c03d0700d0302c00c0c0f54144c0c4040038002401e079425259594800d0405420300d04120704070700100b445e00e00002e100000d64000f50104840c07049080c42d0b10300d15c102c0d040800080950390f1074000708610303603070800c5011307141d0b00b281c069403911403401008024420350209552100509c00b41110341e10800c0b800807512700070400f404098148c190310f02d251821903013103600386840564046a03c5040801c1c0f1041611b03003682544100610302a080b22280381588840e103007502e46003000b8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 838294496 1250 838293246 838293263
    0x6040b0406081b1203161a1e2e06020f060f04060b0a0b040b0a1e09061d13060504050f04080711040f09051608160e0601090f0801140106030e0a 63
    0x4a071261580c40e0003400c0503c2c0714085d207469001d401410b06240c085001e049480c00100300310580980c1e4100700071401801031041c0c041e035401d03201d40307041d81001019200046007100c203000065100d200c03168070703420130040445540c1c0c5075152640c013a18004403d43d0480154002400b0018080c0d694083c16601617088100450303a9001034021601c410000e80000c85000340000300405c7c49688500207014401aa9480500c0150030450700c9141c1a150030b000d070005001d900302001800c2c0b00c0c2c02d1449100203a1002d02e81c00c2000e120018a0410103a440e844c035a584890040040389024400c03d580a0b000520b60a420300d0b207603680154903c01c0c004020030b1032844041c41c50b0302e07854641c401d05003007280072020040c92185080941e620203011a40e02c4407660791880215203600041a60820341d0200081810b409051141d609008100200301c58100b000e440c0002440403036004a0300c005000c00c600004807603818520418908005810040070706083c03800800800d44001801d14140b904500203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 838295746 1250 838294496 838294543
    0xa05100c03020715061e03030f0f11010c08040501060b03071e020106091d060601050903030a0509041b110c031204120c26010e1501050d0f051506040b040608 69
    0x1500240a4400041d125002c49101c100d951000742d80520141e412641c80301c18042406c0910381d6128406020044c0000c103540300070b42c070319805420907403221645414079078130321032030283d1040c21100c2c6c020158000608400c18082030100c20703c00c8601400b100a051480c41c504080090940007500e124000400c1d200b961802101b4400c0d071055000c1c00d44160280160f05401d918004400481d416420690084001040c0343e507005104492000390081c000d503090a0741c6071800da41c5a089001c0c07541d01f058070b603c1042c0512000d43ca0035801752099803241001c110807100c1c03892a007120414403d000740d1240c1031016550008500b074900302c13862415001e0031001c0e6842c0011440110703510000062150b02c0300c02c040b41d2061400d08a0301095a0020000c4c0ca030710890040c0d8131109415011050301e14640107003c1810306001c400a454001d175440780c0b040030b25580f181e180148404014602a035448140310840c03030680281d0600c8401100d00b4060740d030802c002181c031009000343c10906103060091 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 838296996 1250 838295746 838295771
    0xe0909150c07050f0d2007031502070c06110a0f060e0105010f08010c0c020a0e070c0f0501150602031e13030c1e0509010f06030c050909070e0102060105030a0510 71
    0x2a41400c00c5406100e16142408031028031142c0200000b140e040c02480e846441e000c400150140180da000c2d40c60040259107040640142140f20311480d03440c6c06408804404100b5240d00d82121800c02c001c010303600c21090510264085d2550405410031501c079107502030440c00040e82c2c0c0d010940001e400701c0c640015140207001080c070400841c00a501740000000c40c485481180700c11510828000d110b20381c00040b04484142076100c0c02580649a56000e2116440320034170f40e9030020180c01d05c84110711a5485002c1000612807040760aa03440d00712070801c1110050030a8010001800103600f84070f0000c0640300115030b2460561895100801c01a400b06418950300d80115003146400c40215140c00c85000f0400741d004403285400e4002100095600345800c401341200c03402c1c405030001e0f40c107221046000e04031800000c0100003062064145640c6c0d241030311030044038503484c0e040111210030000390400c401640014805c0d0060344c0c04d640420801302c3d10745c1d80d01020120000710407080301d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 838298246 1250 838296996 838297003
    0x6030a0305091c06230a0e1e0f1f060b030f0406051f0303230403030906120f02040806040b07030c02030406031e140910020f07033204061407030e0909 66
    0x6402910581c241201c05c01034400300c07041a81480d00c0741e00c814281c0d90340c4d840048103840b00c0d400008119404102d80043d00d00241d00800c448042e60010b442165003460001031902c0040304081d15081c1e21008001c503a030601d0b00c1618001e00007900b00c41c0c25468030410101e81d5040040c03000d080c00b9100c1c8005443d40c4600910b1840601d40d00a24105007034403428002d044010400019042d00040d82c004e06041801d001510b044076031664481082c0b90030400300319101111006541c0c0744c951286515a8441540e00160000d441c15a004002e03d01d1b041c200b0000c0c81e00c01808040c1890b241401801c50750364080110f4066071110306010403000e42c4003030300c04104400055203034031440c501020007080410a07020103014420790411965070b810301c01c915104034826a131608013004010020000002c0c00b0b20031107030462698000104400421a40104010600c50180201d040000070280710070f94010038071850420708100c0203800c001c4184d9016007074071001e81060344680381c0f0b400091450709080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 838299496 1250 838298246 838298299
    0x60f08071b0f020306130b0a0608030a1107091a09151f021e010203010305060c03160f05071a0a0f0501120204090213020c0c0108010608100612090503040e040b06030a030509 76
    0x83d04891080c43d03c0d0301280d0aa1b081e5601c115041e00030030340450b03900c10090290300141c511020282d85024032559050f1000c00003054a14480d0080c2000011214054400c24059503100040643c148042004208030840c1c01810544030a0000480e50315036100d0108001c1141004303600c511681207459002d928041151000382008035295a81706201981034000d141244d01c03c00481c2d8650b29440400c800c02d01044400c03039034801008240c003103480e1191030319411a03c900d04001d031078102c0644a070464031030f4150030219405400030a02080d0b41032131084c0000360249103002c110550400500c51000300c0000c41c01791195071228400f8040d540d5441203040740040c0b070042159a54402000c02c1e48940f5040c8007180462550000003522500484038503108116009507645c0d0305052100036101c403500c1141e081c2d042950340d201040015003c2000744007030648814003490318505880d0101c400d0a0042030036009400030710041c2e00003500030040c1c0c0c2040e0405c030740401030000d04120411110005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 838300746 1250 838299496 838299499
    0x11b1809061412030c0d05161415060406051f0e060d09021e0120030f120f0a02120708070e270a0c02122809060f08071b0f02 55
    0x400200003902018600403003550401522220f10840a10310b142da00d034060002c4021064025115117031a6078800c0e0004c062007071090f04100034000e01b42d02d40d50740303080803d02450480e610090740046003411022945500c420100c60a2241d07508046c0071850001007040442040b01000040c2c07034003d1700034101040011400f80c03a003034a40c181c1d10301c1040548100b041c140c0c0540840b000700105423461006040518006031615044a2002c070038000031178140d14940242c07400148070344050b000c2e01400821000410120482160038012554201150042d00309a0b0300d0307204000d10242c405580e52843e5220901e401d00210300ea6805d4002d40758810400710705644181d00d074801840070081410601d214001800c00c800141c0c0e01c1140c0002280c4aa10a00d0003513800032205100c0d64855600420b1900b4100030050650401c03140460812350480c03027000041511900c05100043c1d0202d04d01640c040580b0700212a0b003030111011300204122000880751040c5d403c8032406018801300e070909090360 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 838301996 1250 838300746 838300751
    0x3071208040e07170a0c0c0f03140307090e06030303012607080a0303020301090b09060a050f0d0606141306030c0e060301091403033903071206030305030a0c02011b1809 74
    0x1440c000040075112100c0d0a1138100b2031510100c0c20019061088051400e80303034846034040d160640300c0c0c16114130010011000c0140e00c0c00c0c101510031200002d5805003116440d104501c5007420701c3c1d0019070030028030582c004c0d4020f000402281d28880a000320500004000c0e042d4043c111b11110304026180e0442c0c1800d00c1600351420805030300d5070096040750641d0604020080c01d007003c0040b07544050710050740c00341001100344003604c4c200c40f401001c6400208009441c8d426a5030b84015a541580156114204041107490b50f003400d65000108804940b02044018150782d640c0748651403a001e4804013003071910000d102a1400d5002c600040d400c031000000080d03280040990301c2d4004c9491581000e5140c1030005982d4a0b60030080c01e03850010192055448144010801608001c08032020001070f00c100a12040141c4a0480654003a80d034060781c0f4a01284000256560740242d0b404581c90f1841940c0d01040c0d1140103507100c240352505411042c062181440c000305903400201002c1e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 838303246 1250 838301996 838302001
    0x181503060b0a0b07150b01110316030f0206090d030f060512060a05010b0a0f03050c04050306040b101d060f040b0907020102180a0509060120030f0c010b03030903190609060905031209070503071208040e 88
    0x8ae02014010304041c42560741c00d5218483d0a01280c036024165034a038001d52100801d50b1011b07000303801900c01912010760004a845c0d4840000d503400341c038100c0590240c0c1182c0144141e041c100c0c0983d501400e286c4400605e414010100200100303040c42c0c02c48201642d42d0003090382c41d40f6175800c54006000040460741c3d10b00b800d062841000c071065a807080700341ca020700001030303940e09486070045155002c0000c1078143e0783c480500840c103c0e426000d942c09a941c2c2040b150719510b003625203024404075800140c03941d078095502c0c3c03008882c00103950b219010700d40d0208099500c009009a00001c06c5ca405880d42d21818118056041c01108000c41400b011800c0030a1007242c2003e8071084105000070b11104007240145602d80c41001c010507010b0b000318076240d00743c0d40c1c11403500140500c038280000d00a206521a4402c90b034100100300c4447c1c02c00145501841c2c0460b85444d04919003201030092140780c0000681e0ba02c550f84500c1030020312150500f0240200340003075130010021449410810b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 838304496 1250 838303246 838303267
    0xc070506030f0a0b061647150406061e03060e0627070c020a0e040c0614070812150f10111006030c06120c09181503060b0a0b07150b011103 61
    0x5201d98450b82802ca05100c402c1042c100300d0301c07915440f40c1d62a01d245121f0701211b111460303ea0000d020301c0c10034124041c007034003648540c45154010065561801d08000c1c0c038030020486080c80f817403018101810514107012000b6000d880d10b40142c4110b8540604d042401780e2a03c000359483c107802d00c001da040080100058010001c004003601c00c4074051501d0f6194040300d40510029a0003500d10324943c9024000b960003170745100d50002043d5003481c1424041e1340c03503401980c04041040d044486030014414045001038209103505001c80340e12001892582c0800e01341a5100c1007081000304c14003540180b09400d000100c0c0305081c84070140100d540300d0402103607114081c0305542c0002c6c085e0200c0d0000b1400362281903038040f0203039611880d8500d405043c080310840c54004d850b034503607128803d0b8100c43c42c41c00c090300198407980010903641c0421080014100d059400000500410041200001c01072030000004115010700040d841c00c1c0703403004880f081d550319280440ca00c40002c14003601b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 838305746 1250 838304496 838304513
    0x10063006170105090303151c05010c120c0c110d2003120301230111010e2805060a09081209060420010f080405160303050c070506030f0a0b0616 63
    0x19203001e4900303100d0201c00d0000742070807260b0484031410039400900200b5040c14103207440525441c1d00604080300542805940306004000c05012601c6070740d11003c030450b4903005050104800318020b42042420f49441002d002c03101c0c074842c0100340d03401d08080590265104904401c0740e540084540341c8850382c41c481056044891001544240b01d500c94903560006c606048034140c5011603409a4010003003405242041c81006456051129102040020800910840d103190701450700414140408045042d030814034001031203581c080e450884004224002110f5402040c20300d000100d4612508002d041802401020150312080e0303005d00009500000362280103501500f0b45801c10720317a04032008640e50303501076164041040c1311078484459029107150747c2d1050081042d01d040f603036411502c00d1094242e400881c08964003040200e00200c2c00c00c1010f01a02060f1034107440c60600100800345800010008028180c6a071203102d02e81c1c60307045c1a2250000000740c0c510808145203041c695 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 838306996 1250 838305746 838305749
    0x1110c03130f0302031b010c020607110a063006030206031603060b0306010c030c05070801230109050702060c0c03071b080d1d0f01170a09031710063006 67
    0x4000ca8060780421101d002d21802e5003203940c0180245003080003070b0300c00091021554825814041c1c400144400360711802c00500026214201440c03102811000f08819241290020820051980401c10f07001c802c0355161087d05400ba21000c5048502c1c030b132004080c1500d03800c0250044004414401c580160b10041032501016803014044203489900c06d0700c0e9804119084c0e40040d103c140c0a9010a004070314400341980100e00303075054580c9800c00345003074450802000c22070218504040c00d250026522503400351508039810300250400300c000a6890034040c00c1001c5401e000185500070383c10401c11600720680c0000001d540aa0800714903c56500703034410340c040d0713004022141700f815110781d00c00070240500403030401da0380c00e580c0103101c4100c260b100c000e07060210002144c4040981085603522581d085080411f2910309441c00a000721000b1030b042c0c0050816405210300180c0d2400700300190382e03040c9000004661078220500c8888941c2d210392088090b4201041031801c1c03030760440d50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 838308246 1250 838306996 838307017
    0x702031b100c08040e2205060a0e0a02090414031c0f0e011808131a0304021219080a0e06033306091002010b0603090705031204081e01110c03 62
    0x400706421820195000314031a1030080140404120a005000902c14520f070080741581110310480004103400004c9002c2c108103407200d070b01c0034040051100060088007200080300700a00706003415503022a4030b00001078001010748170003150017640110100181c968154009529182c0502003c0455005141204c1c804120b01d0808034004064041401858071840038500d03012500109512840300344c1e0003101320700360b51419031280000c90418940300e01170054008031003550b90307080910406c004500c82419521080d01b21081c2c01031920303514003250304035940045145a8a2085140840d07002c000c10020550010740401440005185a00071007140c9001c090144074001c4d030440010f8003d142002c42036403000c0c04020840840c1401542003a00380258000410b52142600019409810450309130391240d226210030019481c00300806408005c440340071914060400c0001034403500c031110840c0c1c407140400e031600c0040d44254402c415451440030103a0720751440d40791300358881c0d01c8048002c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 838309352 1106 838308246 838308259
    0x6011d0a0914010f021b01110f0a0201061212031d030f07020315040f0b010b0a0e010f111014010b1305090405010209211903050412080702031b 63
    0x30300642c0c100361000d0380341e80941719852036640c002e1603000c840e0382c18191b0000a64112004a50f400c90209c00f4840e50380340b201030217a02401555010181d40c0d4820706d842428850100c80003a9034172006e41e400e100142e041161201242e041d2204e03000039410401c20f85140407004001021074920207400e0701c0d0600504854100210ba0851303003903d64600e600003200030030400404180c0548100d035000f40c14008850301c01032440050b1105981448500020302c210107000d480d0a51448601408440ca00b000d4914510041c11140c10b4075400c0700b81600010035000c078120709880241c050105411809464801084033580c07002e001500da0303543c20001110240c465110b00080507007000320880050860801c40c2e0f1402c0e80d01d928014100542c036240344000381d40070b801c41f801c40d003448003150ba0301c10741c506240503e44521100290301d8440c43c030349401d0903081c0340707a03a66404000716000c = true := by decide +kernel

theorem cover : BRFrame.Cov 838129496 838309352 := by
  have h0 := BRFrame.cov_init 838129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 838129496 ≤ n) (h2 : n < 838309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
