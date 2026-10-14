-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0806
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:54:17.408093+00:00
-- url     : https://prove2.me/submissions/b0dfb2a3-d0fc-452d-855d-2c222d24953c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 144784172 ≤ n < 144964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 144785422 1250 144784172 144784177
    0x40e0d0504210f051c0201110301210c0b070c0f05281502010915020307090905041719030c0807050421050a050609010f060303050403020603041403041401180510080c 73
    0x20f4003c2000c504102540c1000341d100c1c0d01d04106404000b101e90902591248148161118103d140150714107590070010400c595440b820300c500403d13101d44c0141004241c42a45080041030b10a00650755990715103480a9413801319030102d144402d0540007003259855400c90506000ca0411003d0740c50b8140300003040d0810035540041808811401500f8840d5405612040140d40142009152915440c1d1450701b41e01c01102c0d507000045170007108015080268000e55000303489101c00e00c4480030110b64071000741c2c00c0b03041071069a8002402140e02e19400d80700710700112101d4a8021034503d411300014000e40301e54403a40e0310307074803100c1c102502040002300e4200c252a404001d60340f00c1580303420060380d502000c0c2d805205c907502e0420f1021102c0d019205400403240d042e01c1e201d080a18640822909410040050318100800300b203040c0c80c1e410510007400900f40e10107400340303a800c03040d0004000c090b0307030a0101030880b00c4500074401c582c4c41203c840412145803402c9a1940d03559000c00d030850 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 144786672 1250 144785422 144785489
    0x612090519030207090902011704080c060403050d05130c051302040b070606060f0203270102010902030706020102041e0308030f0705070c121703041703100305070e06040e0d0504 78
    0x41c0a500300c4040050800c503650100c042c040c0d42224041a240d6884004603146424001d0110b0801c0d10303402c52840c40c44403010b501c40e0180701d0040c2080ba48454641c10007900700c42c01c8002890014100030040d440b4480c06400948450300c4d448849419034898960340e5140c0a45813244074143d42203045520b2507011a0013a140c03003240c460f1950340394074280000e0724150003110042880794190703c883d80d1000041d03806030030b9800000b0078680040c00402d05142c0302061501d0465490b07401c0303030740503841c1042004010711140c0d00040e0307102d00d0564002c24001c000114201e4031540c40404101144101c2c09890300140c9000d030082c0e03507884030101580d08d0720a145d0000c003050303a24200000d42d01580c2c0c0071090380600590b440d02c0e03400003d40940403a44401c40c2d00800307440f000307000c40d9101c5000801035984a0108080d0405c1c180d00ca07291541382141540c01000c00321150001c00250342020b003e0307982c003611544001e2000340d100500180150240b40201b40c0654000300700c0c001410050385a0010300f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 144787922 1250 144786672 144786683
    0xa080915071b05100f0f110f0f060109020906070b27010203070f030905030324060d060906050406050612220b060906010806100e06071b06020f07050a061209 69
    0x41d1500c92401d00c80c102804442c4075502c2404040000f26810f0001c040140003d01e59140c9103c0b40b5a90000d41c2c01c44170b003402000401c0804a41654034107010000c0c40d034151900001007500c1e030f100d40d54491030000140c000d05080d90050201110b1501d40380305540c0925030001c0b0f51407041e50b4070122502c281200c2642588020510f507041070140d030042d07000318051030103551503c4100c040d190050b030a950034032a009141b44d00400c00101c4040d01b1208000c2070000a50100e40218800c1001070120781002c0d09124032190b4510040026000c0c922031400240010786003400071500c0c000c00035000340034010001381c2001e01b0301c00180405140c9920303000c3d40800c01107024450301e0b460400300b01c0c103032084412501070318002c80400d00030b41c003c25046200c2d1100078101941c18048100488191a0425680d500008240084000500c0181c980d500c0e40603401c803150b000601d0b0250007450500c20429000c1141c000b080140210f403101803154059548605102100c04504108403000704181c0001404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 144789172 1250 144787922 144787927
    0x3060601030e032a0618060601090509060d260406020c100c03121e060509060103090503040612090b010e040c0e010303090e04110a0303020c040e03090a06260c0703110c030a080915 79
    0x103e9501c86c100c0319403021244400c644040d9612030066035900242d020707035540a40b2250001340c007403800d9805881d542e441032155108076500e4400c01001e400040300600343c60200800c0601c1207540c100300c5945210301c1101d81200004000001500d5030034505005020411001238000ca5510680c01030315400d4030400d0505c904203406c0c1001070042c0603074080d2621660080d00401c1141d8841c1c081c52520300e4000024500d010328048041c0e0340180154011066503032190200c3d0b0100e60407892803402402da503c40030b0454a001d00e4a21041d0203d504220300c40300c800401880429807010001003610010b83e0380011984881c28000c501801503041c10f580480040c6c004001c040e4007083d141d028103030941e0f080c8540315903001d88548038000e2070107180d0004020002040303030744d20841c061107042c1d44850407100032407000c0714822070744a400c403142103d2000000b5500101a80722200408031004100074041c1c5114003000240ca4121800c2c0203042d104000c0b03501d4000d56505803011a030030003140800da5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 144790422 1250 144789172 144789181
    0x50609040c020f0a060c03060509100e070c08191b0b1f05040f0f060501020705030c0f040209060a0305040512180f13020c0c03010b0a1521060905040203060601030e032a06 75
    0x5e014009200c01c4e440000d086c01000075050400541543c01103100c9816001290b0402c1111600844d009124401300507140c965440071031350200c0204a4410040321402c0107010300031000d4102c45000e491008045540b00d03c01001c01c084100d040d070080c202d80c0f420035984510f00000d95040c9690740009601c1403502400359000308155028004440030b00ca000d0204e59580c20069071200d085118440d00764100c404150390518103008a045401d00080005082000c0c0343c2c04114140c0040d174103c0003080d0f8440620092280800250303280c41d0b8410505884c10103140201a4000503201032180075601071000940303503590324000000b010000810840d144c0880c1d0a8165407100b415035190b002e5464070540d0000c0d0306008116205840c5031541901ea05a0010000c807003a9075105010350865511003600f0140c0503035030050078028136180c140404c8904090041504145025020906141c90410b890741c100038080261881c1e24043e0b011716a8020144002c00c4d0348540e50304104009000d64000c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 144791672 1250 144790422 144790433
    0x106050907020a11010e060414060f0a050715020301031203021804180311010603080906070c050d060b0405100509011e090e07061103030c071707020d141501050609040c020f0a 77
    0xc80c4807130103100d07510544001400107599400e50141080d4000c079080009000000003003d200001480160021317251484850714940316400c59502140040c2001512a00340315545a03101000b01d183c00e004c625551440c1e56650302030301c3c40746466082c96004910603000b84001c00011a20b8200a001031082c100804854230340c1000c04642140810388060503c24210f41c144121030540758070080343c034038050301c400401c502604007040444601c3c0d24140d01088a444142000301140d110307200220b180c020020400050300c0c00180740c82c602d1044402c042207150f40e10543e060441d5515148120b6005034101c00404e80c6c08a034202020702818800902603004002400101311800741d901c5a0300b041d061180785469120540309846140b209002c0c98021603941c80d01414044441d8503514a03210803940402ca0f41d40c0009030958031441045c11801503140240311600c0c0c80c01d818104815558100400a00c0602a480d210780c0502da460010f00c10f03040c02041b0440607032030180b044405110051804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 144792922 1250 144791672 144791683
    0x1090c0b040602070608190509100e01020415031503031413030807020312130b03190c200a020d080c010e060c070c0e010501020a0b04050709060617090d0903110102010605090702 78
    0x2d4000502c5001c5001800f2407081d41901c0c01140d5a040102c1c2d07c4c40300782c030b90101402d00507001c81424028a0030350300310140d880c459100382804010026898520b0840e80410304694030031000e05060400c100d6a110500115041040d00d034075080031000400b110790311071418090008407501e003600301394011080c48602c0003d82034140c422000c03102c0034007000d80718440a026050740d00c1010740034600300b841048810800b071684603002d01c191650001e80d5200c03480035a144510040085602d540440c01c6582d40600b130140321030003c900900d100c4a0642c00318070261155038001d400c00b2408030b506d40d0011400e4026041003034005003192020b0a03d200b8044559003d24003c4130342c1d010704d2a0000b4010140c0644038106c40d0160041c0518500740d850b500c0e0b403400018030488079030040020201e8604010300c0340070041c01541d41c0d01c44450030101080c080c115405007007006140d0242c0845101507a000c0c4291083c0d9038080e03242058140140c1c0180d0252515801096100d9140c40c104840341d64000340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 144794172 1250 144792922 144792929
    0x19050f1b06010902120c09060d020d150524090406050901080706080f070905010c140115030614280e010903030506042306120a050f01020309060c160609030201090c0b04 74
    0x10303144982d0340c448260040f48178804c60608101034910014511601d0000981400c41c8090000b9150411009a40c000c83e84041c2d246e0a08075526046074040650440b202d9024140540f420a29940c52600350110602c140083c207540520020720f4044645407508800000c04020b881c0951558654044070b03161076050217180006820500082c0450b4401c007000350103035201d80c4035203080508000045480c4800c0303410503140003004030603844070443c1c240300d803621030300b1600c42e0403205a08515000003a01d02c010001e0f0041c03200c0341c0502c5505024086544030b040301c5641824690036860300300c14007502400d1510070455180007511820705416811842c800c0e07400b110200501d02c04801010078003c0386480c03000d000d048410000356242401501e041c0c40c03054000071203040742481d507903040c81d2400c1c29030390004e903940220600021510401a803600b01c0654805c06041c050305040d240d0a000f495540a84220340b0382c1d6111050500030342c413400d50550000035150000303844504890301c1d940b0510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 144795422 1250 144794172 144794227
    0x71202121e0f01020a0e06071a010b0a030e010209150318100f0e0a110118030b090c0a0608010305060f0a06120c031707020d060b060c0d09090b0a03050319050f 70
    0xb071050742003500c1031080b50b225828035120300440c10004000d200c8140c00802e4202c5d400a1a011010003410b89100140c0c000c10070718001a076a1205280c0040542e004040b282500da070040c8509050742c0e0318880e1904107281b107020300b607803030307a0f0b41c1c0d540d9080f946402050002140100350b40d90034002d54a42002c14140c18240301400080c410600066441c2078008000d4800a032460840311150710650b645108902c24a04501c0b13229181d031280c4e52641c1c0d05a44010700c6030702c1a800c0c0c40c1c16050200e2580003d1240f410080217562454076039540f9000000c2184080208400010b60420f274a0307801200500810350002c07140d5480c42c07030004098032007030200fa43e481804048208120710b0440c1104d003d5a4041c00800d400ca4642d680c0740b0207800928003a9522800030311a00303c0a9404000b02e0101800d19511101c00070301c3d060803141155107090703d040c041e50303001e841800030650000842d0700e201e0a0402004a015030280100d030603001d0b03260313030000107400021014010011179a281c4080751161 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 144796672 1250 144795422 144795433
    0xc0a020102240708100b0a120e010507020604080702010504031a0a0f0e0c12100504031d03010219050c070e01090c090909030e10050f1303150b0102071202121e 70
    0x101c0c1005042d0314001074281c480801040064005407003515105d0f040030741509100c500395110074114070716400080b940000200442e05180d0002520f0242d95400050301d1b0013086542000030f8025201c0d41c00800191800c02c0008441045902c2101103400864000301c502150b1600004009400102076460b2250310f4140001101142c22520503040a102c050300107202000c0c1040501c01000c1749080ca1440c203004200c1c66010f82c1e07586008440c41180f01e503a4910300740c4105004004c580446c80f00d8036000307038814011301244201c1546840300d15035481c01c0054403044203010042c81d04030190042c446204126000013581d5445030001c540c034004c680c48594100307440742651130403a00c0b10b40003d000600440c0005025050001c3c94081d110154a1300c00d10b4080c030035546035065480754141d860314010041042085c030081e0030001d210345881c42800c0c000c14441d100002c0d901c44c803c1c040e070030314000c44c2c0c2807980455580c15084d0202031540c1c0c0c151601c00026848198000c0c19248200c9454043e2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 144797922 1250 144796672 144796693
    0xd0c121a0a0f050915130203010f0c03020a020706030203040c05210708100b01030b030d0f171014030d0e06090a0e040c03060b060c03120601030605130c09051c02040911060c0a020102 80
    0x4220899136041e10311700814503680b5464912a00c008141e01070303070103558400020b001421140a4030791b59140c00d40303000d40c3d500c0181800900c0c2c683d19901140405106209100015841d0110102260800c8030301c1c0e40c00001d01e20800d010300c41c00991250300c40c8a104400140c0303190126040d030044074206002c20058071104010340564284c11007003541904803080d444145070003404001101c84441c5408041760580c0c01c0303018030102c0305071a017588400540b20100b106a400a01a202c0300009a002c1c0219501c1041d026101303050404510340b2800f80421016243c0d180e150450004208101201007541440c3c18050540c8459000a440803800c01201d2803450030300008484c80c413a614401503180140c003960711208088003a0001d4105500ca401c0058650b6600c9249080d51107c0500020b0242d90030401074140c115560095003d0116068898113580e011031021840326015a004149000f140c9040300c108100d41e0b80343c07640128003041c062401503001543c0c8001c24030070307003c54000102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 144799172 1250 144797922 144797941
    0x21040522061403151509010308090a0f06050a0c02011b06140108150c130f061e02061012051e06043c050a080408030a0e0d0c121a0a0f05 60
    0x1902c42441d501a0300c150b19074102c14a2480c16540d004120340001c18006031000e0010300706070420303401522074807008907010f92a450001580001400090305641e040ca00d401d40148c018054111034405020000324a0b07000c1da4040c0c0281494807800700340b024850502e510b8040014004608842c1410031920000b18a0303180c0081e0b500f071381d801401d00120b0300c4e43c0c1c1c0740c2400d610b9900980454040075805c4000284441d201c801c0d50b400380016072070708041244030700146030b4400c0701e038103a01085502000c280030100f0125810002030f220740e0740b14903c030100d1504140f4940150407510054406109401d42c8a22402041d420b000c1c0b403160201d800c50401807400a1066902d5403c3c950004640c2c402d904c030030701441281d00d0450f510078402d44030840034503100c004564005600000551b00700080340c4800561106084080b030030f080b1010310352420a61901c1c5020b16050141c1c10800d040c0c210031009002400100404080126200c090b4510f441910400507040c0140c032b566880d800c2c01d01080c074960 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 144800422 1250 144799172 144799199
    0x40603060b0301030b0c030411030109060506010305060d0201120f110a1709010203100b0a0c0f050303010603150e28090c0614090306060f0607080309012301082104052206 75
    0x17030308104400360765103c595030038603564000f400407588801000141c0c80181c900b800341d030a10030701030700c8001283c0c6000d5002409481c8002c01e072500c96080d030b000078070050f80c00c0b2480c81034603280c403000000c0258648400400a0808403040401070034049014103841c3e41c040c03982d4041d0b61140d40a80b042e07494001c0d5060a034041036a51070700c0c0d0503d10005100171007800000d014446260f10b85501e04a00b15150084901400c0000790780780d410010041c41115090300030b50300d4120b015a101c1110502d000e02c000b140c1c0f00081c1016203101d4040b80d10310703101c85207951981044081e103801000a43c001e45000300c00d000d158420000414a41c8035580110450a81604e0403000080c000c1c265a5603a01e08020045110380b0703180303521000c1801040d001c18841c0f0095403042001c00000030b000002c900403002c0040030301103c4022945000014400c9860110341e61041890245802d501700401c030000d1015405150011030700182c1101101c60702c403c401e00154404812440d04001d083e0301d41d040c401441 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 144801672 1250 144800422 144800429
    0x50d090e070507030513090c08092109040b04062711250206040909080705010e0d050403060506060f190f020c0102072c0c0703031803141c020c03040603060b0301 71
    0x290302444840080703070194008004c140704031146109041e4441c8006011640c682c1d20003000274a0500800000410802c264210182c0111040307000440b2140040000d00c04c082d991030145849040b0610540c41c0c98026601524145090142810342e0340c01502c42c52159580c80b51595090441001c0c0240c6502c00300c2e008891242032101407103d10201c1480729010004040341c0011081200080d4205544142024a44615030701c9035a1200c0b414001d09503a0500311880803600000c0d440c0e201d8540240032182160f9100e40f02050550302c030710000700f45000d03240700702d900c1c070340700040c41d101c01d0032000007a000140081c0c844155a417020f500032650f803231010741041e003d40d1100c041440120794540c0c11490040200fa407103071580012050711100700c0400da640c00203043e00031818030109038150003599205688078030070209010031510000e00c80d40300081c003007504640006810303c8103429648008404c0b0354070310b0190340e21a0016440350707996100d4460310b00001d150080218800c081e94046030304a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 144802922 1250 144801672 144801677
    0x30f01150507030518090a02090310050c04050d0501020408010203041226011403010b04020412020112110f0f091002070f05030105040c0603020c07170a110f01170c04050a03050d090e07 81
    0x100202560207455035440106000e105e03100c0121165140e0b61803260f0135200d105208005603e44842c1802d0605d0080400c400f0751b80141000300304582100d84100350360444800301c4500c05c0440c4107003825402840340750403580d80c550000003004203201641c4804415890240c2d95814154040003240c454214851310140805070701800411845418698040107250010300000d10781c21980d00040407a07200303900400170449842000e10556811400b101900c0c07652020500880249002c1820720b440380050342000f004000c070300346061113214000e070b681381032024240b80102d80001e0b00280d5101c58910031143c85aa403042c3c049500c0c14103001c2c0c40e01840d07000402c03482050405406901075001a100c803851485984c00004000d540101c9646c005944040a04ec1038800742c1401010090071450080c090550341400035400d1740d111401024000d842402c644841c0ca5803040b00c0d103207100f1940320b80d074048400310000c42400b40201e0025912451500c0d4003d60340d41c1c1d070440c24102070088074030502 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 144804172 1250 144802922 144802927
    0x3041e050607150b01090b120906010e010609060c03121a0a050609060706090305130906051017060103050606160602040e13031d04060b0309031b031e0c0a0b01030305030f011505 78
    0x242040d25801c042c000c2c4d001410102c214941307991b080083c1e5005100074a00e8241118117024241c4003d010320f40c0035141d42005c640c0c60390b040c19409400500184669001c01c40114071080605110b4414080740300803080d0140845141d0101840454044200c4075100e21540b0070000354520b04030b400c54845001c061b0a140c03c2007400c0e200c4000400c04110141c052003010800000c4082c1c0c03000c005009030141c00030000340c69080a0030f22241c02e845200300828010039588156440101c030344d01542c040c01c00d01e40401c02d030351000f012984a014100c01b480010f044607140c102006001d8010708140c810341860282c060351940806440c410750a0707406004a004052a50000c50b520b460703081c44410050004aa5540c2d11500d10204ea80105d0b5150382942001c80c0c90107100000044009414030240c00840c103040c40030141c1d200c0c11607000c4224070541030005800d1a6210300340b11010700c82c0d41117140c0b200c1660f03590401401641c0108c40c21110307040400c001240b00c48192003400c0003901e00d60b84a60 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 144805422 1250 144804172 144804203
    0x50c030601050f04110f0c0d14040308030a0c2703110904021f020a1e1a0c0414010201060803030a090201090e01080703060c02030c1b040608011e02160503041e050607 73
    0x2031040e6aa404e0201c40108801d40074020544002c021f5401100f00034010140e83d450024000c0d00340c8003850b0b01c003442c2007204201041102007a01e03045894030400051340c07a42d01600b40e490710360b0603180004150101d03900600142490b0003803c12603005441012100e00144100071505008560080d40008480c84001001054031f003407240341c0402e0300403a107030b092580d1641a0030b11400014040c80c148440209030070004016902c0c042d440d220a0305803468100f88600c40c410b40254090710005003022707543e22215a00c00d4000b140206245420389030b807030815403941005006490b00c10307804252034079800100b0806103000d1f90b04039a506401780c1101401c42da12807000e000e6440c0d11800310700c411b104004030384005200c10791540c01d141a83ca0041c203240380a101c01d0307034284c1d80f1046075a40351107500105400340b1082203109000c5000e0042e5a01c1d554410360740400e0007907a02411902c03000c41c1c0842e405001a1031294110700b100e10090140f5a14010040d051280d90700080203166801a940c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 144806672 1250 144805422 144805429
    0x903021005090a0b070503090f0306040203071a0f13090b0d080403020105070807021806030f01060e04080912030c0307050c0a060c060504081905030a18051203090106050418050c030601050f 83
    0x901c1103540c02026203035007903511a440c1d4185d400c020000e175a20b8100055014071071800040030300122100b82d0280696141c03e40000f03071524264810903185446000e05e4000013070740003049405200700ca116040e1030b242d004601d080d80011601505207041c0c903005018000d4039114021a592a5120464178079041c255401100c840c5c206150841c6c01200034040440140c0c0c442c403c42d402c01e4001d0850345003a00e4208101450510441c0801e00c1c20b0345490814442d010300c10b01500da109820054186d40d40580c40049081c01c3c801c001c0750006c41c0004100c010742d2100200080c40c1c0c1c0760150044585868900e000c2182012651207041c0c0898015222000040c0854010369441801406110b00b003225011125440040e40b0449000140c030000c10084a00180d05c1200f207048440c002405880010b42c0d0342e541d64011403680c801c140707034000c4001607004c40c007500540046d1001a105122007202082d99220140309080300310f40c0f500540e07007642003074100003a00d181200d0700142107a031851842d9003030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 144807922 1250 144806672 144806677
    0x8030f0711060f1602040f020301050d020f1306060c0b06030303190506040f02030a0204030c090c081b130b0306040e0d020c060c03070204090b0613061203080a0b0d03031a010903021005 81
    0xc20b40168041c45880040a00d04024040b21a070f8030541802c0c910f058170400048400140200480c544103100510440e02c1d141d110200c1c559040d00c0b4011503c4425001a000600c501c030f4203050503051280100d00343d0b60000910007460b10600591409480701c100300740e00c902003103e1401d0341c0c803010342002d40c888050f03030011a00131201800c00500f002c4043c80101c180d0713100700da020101070b40000c1d0400810a01e100c2d903600a0401c503100300603410401c0d400a0a10202800144100090101c4000107904050455130019821111002d1299540345081c3c40703500125030549c4501d1034400034502016000c10040501c110f03e0f8082d00001d152001000f5164200800b40c01c5644001d004080c0141c84500ca8000c4070350003800c1c401c5c030915000e01007201200d82d1089210b0241d003040b104000d110700c001d041060a5505060144007075546011b90402803007107032060b036032200da100700785400e254040d4001400c0f00b011918280c03030311203d02e00669484985100003504400e0800400c03000364440d102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 144809172 1250 144807922 144807953
    0x60a0908090307030308011a0c1506060c0a05010c030c0e03070b1605030d0f0c0c0506070e04021611040513081b01060f0f06080109050621030418140108030f07 70
    0xd039081120040202e85055010b8108601003102c000c01441442c48004940740040c0040c20039030300d4070120500d640d488100300720700d290703c804448011071410350300d050035198010396450490f68410b410381000c0d4040d01d5174101c6100070922703081081041502c03a100141c0718060280080401c14501180d50b6401e41c0005103001c0d0340c142c1c101c0480001f4800f84003d00701e03555206000305150780c4401d4031900302c421610f070803000d00c071440d0144400540003258866215280303060190f03402805401003006442038440b0756240082400999007000740c0e080320080120803c6d0340400080daa650040850741c0a004405040444207000000703520030345140104104820750f00101710300b6514400e40c030f40e00000340c0000c50f1811451900344511075204480c01c0c018401ca4005200905001011817042902642c024820440005117850895800c0049500070000b60494034100c81c0620b0300e5100030103051401d0b44a0080c88000003c500b4400020740388403248554509203410455074a0f514035000008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 144810422 1250 144809172 144809183
    0xc0f0405060d0b25021e0a03080c030c0708161a010f0306021305030708060a0f0b100c03030b090a020405090c030c0906031302030604030c05010e06010b09060f040519180b03060a09 79
    0x220541000e07219072401d901d444c0c0150300181070f1a03418201aa265244140c9203030125400110f242d40400e030300001c0141c01c00e0828100c00d583c0d4498844220032486802c0c1c0160042da0300040c0804d40801c0c0e07819480000d0300812122620041d8a000070f107440e003080c80380342001c0c00302d21010700100700b482d030007080d84403111142c1d00d11860355900402c1c213000d900e6000c2800343c0c2051042229103080ca005500010441c00030070010b0b40810b500042104c1d88074428170040181c0344420b07904141c0658402507555600900200062405007460006540a806031a006042c1500456101081003041d80d0060310810095400c08010b1420b000c1c1c0d6403c010200f542c1884000c1c480c0001d07031810700c28513000f45d0003652a58518266400c180d8291740d00070445c211b80d984201d0040181c0c424032020359855041c2110126a52868000641c2550040c0d4010980c8201504103800414152100c600d0444044241941c2c1c0740c0a0030b55200c04075040d411886030190400800034003100010b5100403205407081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 144811672 1250 144810422 144810451
    0x80a0e1f030c050c06070f2a1104090515060310090503070303090512070b061e090a020a0201140903070c080601030309091d0a05071a0423030f0a03020c0f0405060d0b 73
    0xa03042c00d145c84801d840100108010038403501d20300d58000010100c480b2407000440c031001c03141c81c04a031f00e034905500141c20361134030324204440c5075181d8119940340740d007201c2180e828058611200304801d40c1660400c5c464450702c40f03402755007413040c0568414107030007101a505191041e02c1c150050021a10100c8050241401302103802c0c0401000d001c00f50f0181080b02ca0b01d140000600200b50070b51a140c1c3c9034840c04140191040d500d07189850340c803000b288005602c40241040a03400b50440c00d002010a240d21020850302003400000380031042d0040700281c0007150707226181a2036080038040540002d90052082c07102021917003124141451020360482e2681a4414050070080241011200760300714010030800e03281188001c84059091003036040c030300341c5800540075804044850340f100507681c4034200c203020741e414400210a0500318044d100351600728075000303480f5480d9002c010710031004010800f54500303007845214880c0d080070b0704e56050f001003030b280c03da00036074020a00b62900c0e008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 144812922 1250 144811672 144811687
    0x70f052103040311012618010f1109100e100e012a020405010501030b030c040b0307050a1511010207030905040b15130305012019050f0304080a0e1f030c05 68
    0xc0000b00021030040d03811044826082c030005040ca072030200f11600540a035002848040c84002540ea040340e911607044840111402415000d0f10600340d014900d640313403200c500d0301406c51500070a05001c003140d801040c6100084162840c4030860181904030740fa00010440c124020f800d8454030650504014800c0b640e400c65405940420030340b104507011941c40c0580860410703000b0310780034000074201070001c5800503003c6030f070781c40750031a09501c20b5440d4940c80388030347c9041c088080603141c0905001600d580304d50a41d5255590704a1040c00155602c1003c0c3e07407000184203603039007194161ba0f032109030707450101000040c00c400240d41d640900c4210f0190003404000c1c004000002c5880c10f12a1441d245003002c0d03084402c0d581f410b040e2a051501448000902c440407180072101000709480882c1c6007000450312790144100a41052100205020238480508082c1c40921141d0707a03800c004494003001e00c10b0700010500c04184d0f50100103450340100e8000e4000310f9102c0d8482c6010b6050218 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 144814172 1250 144812922 144812989
    0x406030302072c0106050a2c01050f09091312030e060a0c050d06030c050109080a0f021009030b0f06041d0d0807030b19062a0b0402010e03030c010e0c03070f05 70
    0x83c00c0c0c0c40400820700c0000c611422070380284010090f508508840c81c203c022110300c0c103184403c1c0080c01410030000040c0085056110001d59260501c00b801202043c6018243d0300c140301c055110a45450700031120041d0410320a020380c02d521100c441c090401501c40b0310240300540b84d00d54000c0c0c2400014082c2003442000c900c260b50096010301e804d444042d280200140008085421090054100c4c6405902207025160450740381130341a19600281c0842020845010308182c1004001914050a004000e01084050f502a0307a01b11010000c03031a4007003181e44100c1c020240900b8640120225801c0c4074096101c240d4000041d09020030792200f4880001c55480440caa08801c040d01000207106d031f2540f1074101a440083c11410541749810400074209041840d02c004200914600c001011a4850140c10701500400360440380c0781d0001b804a00c0c0030341110038204259108480c1010031919000420900f219a00d80f4462141820f00c4144194200782006a41c10380c0303500403481c001400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 144815422 1250 144814172 144814259
    0x60203040c0e1005040f0204061407020103020705030d06090b01031a0d0302010b210709090201120504110a080d0e010503130b0c0708041e080a080d1a220b040603030207 74
    0x10301c80f15141c0f40714181010002103c0c0c070800090707409403040c0418000c2c1030300034010380303650074188003029240c00f80c510049001c4d10640100611600002c00c51981c881e40a801010540710a800c05000389120035004400b100c2000d6005003e0030086490503915050056a9050040c0070384000300d00c0c0c000940102e0300000000743c019048184000940340600010f00c044405006800811f002c0700040784c000805c3e40b0244d400f0161410780e1500424208040b0040044d400b80c00034081c050369a80e10001c0d292908024951440801c210010050556108204480c407606c2d8400b00c000c0d402419032941180b50600030306001981c00c0421080e00030882e01400392009220003c0d1200010b80310300d00c1442943c2c0c0d16407060304c15034013212a80307001030250016540c065041810000e868031070108010300020a0300e4031203170012010f509044200b11285429121400f01c02414040b0300d81420900007210444c0c0300c0600182c11603a0103201d441f1a82900820a0700300004601240e0004107802c138199 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 144816672 1250 144815422 144815431
    0xf050c0306090a092a0f0501020303041b0806070c140a03120c020a141c0c0f080307021f06050a0509011a0c1f0618020310060e13050903120108120403060203040c0e 72
    0x45e0b030030101001d81e50050000002406466020810700d40c50040003039034a00001c1c01c01040c07540c0c0d52600801d00d044010401000345a013504441315400c00c0c08000d86034031010101580c10f021016264640524001021021203034184d9a000182c1c2e50012920010900c89051108500410002001281519100309a070340b40403009840e0104680001d0a000d2080940b2207040c098610850f4000c141440e100380e101079040140305507070b596992012801d1070304064600103002c060030b905071a00c401c1e5600102c140c80c42503d110001076225810400d4145091080340481c08400c4041424055500701506007041800100c0d01c2010100e0a50300440710440c04600c500e6036a26002c100303110454a8140c0744800c050000c52450410750550280403d40d4040c040a00001c8402c902883c0c5072260b109010032401401003202e42400744029807250702600382d0801700c0705440004103510310007042e006188811241080d18041c40d40d40d8000103904010020b4a18000c454000035920b8010016540304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 144817922 1250 144816672 144816713
    0xa18060906170c010207060807030b01200607120612140a200306010501030e030a030522210207050d0b06130609020c010510060e01140c01060602060a0f050c0306090a09 74
    0x401c1402d4185460300510114841c11903000703000410840d6000303010650801c415140226038001c8110050315a0588415040e0140302408984069902c01280c403500402080d80c03890403080100030090309842181c000c89241400c0ca805940000d18003020416180f803a03a0140d481c07000700d40d100c0305205060000305040707558580c4114138840c41d052103c030340075240908041001c00c0d03c040400d80e0720b0080c07010f540213050b43c4501091654441d00c003a44415817a4580c519030604085c13518801d800010360740d00940c8035070125403401e028004a138010540b00054408034002e080c641b90800004c030040d00c00c6820215074102c046c8005414003504002e4110000302603034407280941c2ca1421280002e0940a0388070f902641480015801805080c0c42282480c1060720b0400c404a400340c0c80c490b454861002d0342ca08200098180d80220b103c500c600c442c0f08080100305115006102603980440b80d12441840070030005850340f6108060342d4200071040d43c001003200e85581d40340c041005101c1d52800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 144819172 1250 144817922 144817949
    0x318010b0109050910050904050f07050103060b0f0901030b030d0216080c220207020d0c0e060d08031306020d050103060603030f0201020a05040501030c0215190e0708060403081e0c03060109140a18060906 89
    0x200e842040050f0002840c00b3b00c1d0400c9a1403814122509500400c1903e90300204009062812030b07203c3c0c0c0120040f000020140c3d0550b15082c1030196036200d040c1603c640c60104050001004200881c502c0c042c1c5201901049004400c00360541490030580385e01c01c040e0f6402d102c1e100240e220000c14620803442500b581c00107030305000744a99103802c002c0a092140d8102741ca15400600c0312803e481d0064074200544a81d942c8900d0020068085c80702c2c5010640d2600c4000414803c16400c024112402038450703091800700e041c0102e00b40e100c1c4404007404110104010802c951103540036811692691050301c1d06407218202012814005075100310f156200300d240c2403441c1e8410300c661400740303844c40000c0244c41d140400450301c604008001070203112030708001961f0000c0c0025110000202c410b0302c03422038a0280a03000f8103410a0b2409400188060004034182c004000800c1224900a0255a50900e4040303041507130007420b1005c94009444da0f200103071503486809800007400703500030b00c0c91 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 144820422 1250 144819172 144819193
    0x8040608071209030917071211090115020601140a0305060718080a05070e040c05060304030c050c0418020d02040609020d060302040b0306061c0809060a03020318010b010905091005090405 82
    0xd1203140705032500480b8920301030031071000a4000302d0300400c485140d281c20300e8801121180f0740c14900958852200e0220030382c107220412a02010000f0800422a40b245540c1d0720780a12084020a01510002691001005102584c00854a041c003404014864240a5280c3c0d440c0e81c01d210f025507109011030752030034070320f030311804103000c4d96026250000050002940503100d803a590025882074110062108020405002c982d540340d00c0600400b030069035603030420340307402000c1c5460098165105d010311003810f022843d141c0101040c840c10704c030400c01640c3c20343d000c10200794003403101241c1c01580d034040021203108600191002d05504500080d04604d58014007099605c0307000074034843c1c1c12003810001c9554407503034201ca0f40081510fa0f158100d043d0704c1c0448880c4116807400303610600115106480300c1d81900190b1140401062803604107005241c000e01303907880036810038040380500509100504081d03401c254000e05013652070b450f440d0b494001c6111018207681c1034031940c00100840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 144821672 1250 144820422 144820427
    0x2094204060510090e06060f070305041d24130606090e0f07051204170304150b030a05061504021209070303020f0c01020a1101210b0a0902091c0f0804060807 69
    0x3100100b0b001e0303540030000c2c219000010030324600e500460b020140510042281c44e12801c0545115038442131001d50b94454034180a000c4e6001441007106000f10a19484a41005c9001080c0109030800b1400004612041c1c900748503402e07130b20b106400083c12003d52200041900515004102d2500c0311100241845000c5003440001441390040c00c100c5420b00c40c400f68400111000311031050b0801441c0c0d1507500c1e154003001001060000f400c800130080c40240192894003510400f1664402c00c01b0a55810501d91240051200500b1640100e00007800d10011068548400c2c04001c10040c589829032880c002070000980b82c40791960303c04501442015010091180301a0f15503005000c02400309000039a0350082c008001c240c000c51841d00145c99009034100300b8032007019079480100ea0488041034006000340b0519610400980c0400a6410000e100704c07004000b0190905142c1001d00170144d003440c41c400405c40b0140f803042c28039004102c807000034101a002d41d984a005605004100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 144822922 1250 144821672 144821681
    0x21010605030a0f060902010203040b12010f05010c02030607080a0b1c02010807082203140a0806040606030c08060603090c060d0b0405240405090f0102041e0e0402094204 74
    0x214002c0e444998000b001c0741038008210603095003c500811580d41e2440102d081d400340303500c4601c0c10703400030404202418004468605030740e5400c040700511560b40004540d02032278070f00f01035010342014005c03a50345441011300316448261188040303148441d003170100704c80042500c10088981d050405076070466a00040103070700000c0318a89072907075007401660b4402c101410f002c08200707450101141c1d000c15010300070600110298242c440e8503450309441c060b00c401d1045035854800d9151080c0130030128080c0c030414030304020380d50710300c0c0321070351030209011403940050040c030154803903900d104c0c185680340300040c4201e41d9074050105901c48000e040c081603c1d0040c04180c000321141d4131190240c2035a502e82100c0607401c45004c200c54a619a0140c101400c41d800801039500010740428002002034160a0356541c42240e5000565140da04403d0b000c4143c1e0000e42c05004003000c41c402e01c48030a001001e01e007003047c43c0032280c401542c0181020070400d1400d6003180500b000802203140a108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 144824172 1250 144822922 144822929
    0x5060c0606090a060312030216020a060305341b080f0a0801050a0302010507060218040c09180b01090614090406060903020315271204091401080c060d02090f210106 72
    0x3c06000107400d41da0f80310421102c600030f000405070b000c2161840180c1c40300c0702d46003041e009041c55a005845034802005000f04449003a00303100340640b20403200b040171503412484008618401c00840742044221000c4072a03154156040e50750f46501d030040740201000300802e0743c0690b100303613480360291400b61001005900040c4294094942040941d810404072400103510200059440059024211070500054170158100380307400201c9a810307802003007001c190380c4500304001440a001c460b840a0721000115180050b403103501c100405400380341c04501c0071b405114401e040c0118180800c088801503800880001ca030200100154203052102c5900c03042d0a03020795400e441c00c40400300d01044a020781d02100e60000c0c006001c2d1003010701a9581c0b0071030b03014480355665905c60b099005080720022691601b1102800010184c0000504802582c00508070904210004640c40c0017134111418032908000c0d0302000726002d80c5c448050038071075041a1540011060311448050846034182c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 144825422 1250 144824172 144824191
    0x80d02030306150c0a080d1503060509010b0316120309031a0103121701050f0307081032130c0b0d090b01050f0d0210020a1b050f22110405060c060609 66
    0xc450440039010400310840c503004403031265102c400c001e203000101821241c260382344503170210200030030440e83c0103103000751044c200900001000361304054a641c2140511a040c210b4490b040098800705104524014001c0c1007a500d007d65a482d240c1801410880c81c00314001004010b000b0807604a20403200348811b4944041145618001440140810300440340b007213002c2204c01e82142c0d81040741c2000b900031907050750a0340f0200d4001a001c1c089003065541507444940038402c01c65840031306181c00c0016000104010303240c1c0c100782000c0d0b40c803540c07080e03420007034244c00800c00e015500000e04600403684400a80c807407071420600010101038001910034103220701000041d030744070004003502d190100d441d4014482d5000043c1e24240b09908001c1c212800351200c204640e08980c180021a2425610199956410f00c00c0203140c07040b6064a04001200041c2ca186d82e443d5a0300c003103400d144240c0b1203842c03d40c076a0006003164020803a841e40710340c0950100003103070800c80d20b12270f00b003038500c0e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 144826672 1250 144825422 144825427
    0x609280605091026010f0216060f02090904032f0604030305010602010608030d0e010905160e0601050f0a030504050705130c090806040f02090c070804030602030103021002060c04120c080d0203030615 87
    0x10303000e400c2d14a003209030b0303c0c96030b04111340da400340d044213600c00152142800011540c1c0c00c0040369840d0090000c003c103490b02c42c500701e0a013840003518000c80754103540092442a0350b66842d901914400201402e01041900c5d403041300c0040c1d8880e074600c441034641c0030004c2080d480c181c90004c6c251360301600000110f9041c3b510800c4002c1c00001611588116003001280d0f0f01c0700076501e1801840f102c2c6000d030541c0700705803c0d0400004900078101c243c1d143e0a44071004c2e6900c5000643c2c1c64885e03103400600c07100e07041085501107031003030307002e590040e03c11070650300c0765580e400c001110f014541000c42001540c401d071003071405030022200300c01044054040d283d50326103a182c00004410014010b405500381c400020326001000c411605025401410f00da10340d5240e0911200940007400101c0c00307404000903060521b40001146480f86184c0c034a040e02e02800c158950400ca413558000f1142000340e268082640c600c103000041c600e104903030095440386860000c1025400da1100c00c0c074801c1b6000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 144827922 1250 144826672 144826679
    0x61b0309020109060c050a05070e0405070f0506030601050904150b1c050405032b0606050a090605130302040b0a0801020c01090501110708120c210603060703110306092806050910 78
    0x140720302c211001170500c48161005410118107101d04140000d20031700071102d002c50340030b004401303581c00f45000e0411694010f49074100342120a480c0d00905c0d83c07010007840082c0b501d41c45000105002c030005040401c2e5045441c800103240380c0329030001c282c084004180c01c40035040101408241080c0440c2c10300840c203058440c1500c3c0c2c482c64841c89000300600688421381035004903465513808551104205586c0e071350000030550782000c050b81c40000c1c14141c0000d4040e109030107882d0031004414110740b40b039185900b004000d200e420b11300364028055007c00030700b6030710a10107006045000303000450740003c1480e015007120701441305001311000602c004c83c082a00c04080e17072508403c070900f0104a40390a04445024050199a600792400d041c0050090f0460b03c0f103074501420051b400c03944951540c150507826949000030781034480e07000b8800100d143c5808400d442d0419090203c1040308403d500d00d070005841005070120049807518401c02460801c058015445503040c020200340c030b0304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 144829172 1250 144827922 144827927
    0x3043005070602070507080a122006070f1407080904061d04030537020106050111030702010302031905090a0b0c030c0301050909120408070f05060a2a0c03061b03090201 74
    0x79488041e02003540418950100030003040310b00d024001c1e400c201d46014003140780c00401008600803980005a1500c0c8400c2d6800d0030100c20b011466025000e08665a50050704551400800c0c40391010044a03405104101103070710300034a5024010001113235100188400e020940da62070b800031003c54414640491818140c5c4403040e0065898504a540c8540d01c541c84020b115514020762488070f10310070b80c410120015004000c501144c3e80090112075580d2005481e07a1404460805080c0c00c200301c5240158429802540e109038180c03134107110448801440340c00c46204031420003d0b070340803004105c180004107011035440b511042103c0c0c074515240384c0b041000c3c001032040600603003126002c2021400244141e035021003070310709040d4031a030b540d03071500b40e40303001911445104070011100800c0c10704121045504203445512260000d00d2865210030892085142c00d900e9804100000800078080500c84030065004400c041007080080c8000d00d54805150305c11402d05181810580050741c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 144830422 1250 144829172 144829177
    0x1005330406090806060108040f06020c03030c190e0a0605070305040b040801090b0f04150b0f040c020c120703080703050f04030f050c01030c030203090a1403090d0b090606030d0e0910090203043005 86
    0x49c0d202008085c041c12600e4004080e005503041040140004801c104120a140010342a40c0c0307441005c000b0041d0b49900251628540440b105400003060300092280c0c50081009001c03e503c2441e12171300c0c00380e94549001030364020b6049111141d4540140009201c00000080c0e08144211180c0d60030303050680d6001a020801c1103a150200c4c0c5542003600d031955202c14074503a80901810074000c00142c00c0000751a888822501803103403205113032806545000040550907258000303045481c0004c1a01c040c0c8058001c00491800004100070110004050403100590148100d005007940c06e984000903040e10740550500301018414002c1000d102c2c03000a12608c819000000d4200d034030185042d060862003841c80303031038021654036445401c0100003107909125401c0c90042c2da0803a211070041680322540501c0d014005101c2d410032030300350719103c218140c208524054040b0517541d96122502681c00c1180c040c0c0b5403003190180d40d160000b00401d02866080000c10440c2e040c085400094401d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 144831672 1250 144830422 144830431
    0xa0c0f081c030e1506120109030e190b07032604111513030b0a1a0102070e0907030b04030810092025050604050c010203031005330406090806060108 65
    0xc200704a41004818000e0b400030b07042407200f0054400b0a00c401005000b0b030f1900791101d902469030820145003900d0184103070700b89079615641704102d040780d000400031010f0b1100c0d100c6501d0700d070040340001e003101c448004000d030234401d0301c8601a40c400f50050301702022810075506030140e400d01c100000604640407170344848134102d035104545541590b401c2c1c154013038000010044150f289000c4180300d00f00000f58810044101c080c8121480f01da45240b440090040583c00f50b80105800c1c0001d00340e21000562244101d0b084480d100c0e502e44038a55010410f580540108124800703000036040007031581805050190018405c803181000585991072292002204550300403841c0c0252f2240840400f02c1550b50414004a209032428541c1d280c0d101560201c840f44600e00040c2c90950010003602e1207140c03400200c03042e151070a808d10141045010203035120740102c0b0404041d000c6105000400303541180e002c1c507280c40c100f017400b034000e2102e90410030703140e48000100443d41c0c1c0c1c40710126901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 144832922 1250 144831672 144831703
    0x815011b0201050c120301060c02030c060f12181b041404020a0b0a0507050f03132903090309030a060b0a09020309070b0a02160303050306040f020304030c2901080a0c0f08 75
    0x740d140c013450550410b80400d214805141c000000001c42641c48610202d206d4000c034150794070240c801301049518418039520004d484028030100480f548040800c036400301104014128504100a14a08240015045100c55120360b0203d206509080c440c80c0703c0e04d00781e90040c400c1802c1036000a400d2503924450740110060000708007244900c65400d9030405a400b00c2194001c184a07038209480f500850442c20038031082d0b25001808110b100e0030442d07860882c020340a00f1002c10b07a8400341a600c0200f1185292104000d21740e4079850070007d12511038001d210025204181a04010044895a004403085801072050009855000c20b8690440f018a00103a41e00c0c0d06400f410380c24080050981d00a80440410010505030031000440c810300781100e040103800c7c5a01d440500701d01080d10080c00280541000030001102800e5070501d0200341c0490800401c0d024852150040c801d0f0003036680d680041030b00c80304010300b400e10040508010030f158582c07282080719042c0e448210a6000d0b14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 144834172 1250 144832922 144832927
    0x904050c060a02010905030c1b010801140f01031d07050405160815010c0209070504080c040207031b061b020c150304050d0807030f0e01090213050714030c0f0403030815011b020105 79
    0x41243c000d60050418503409015241c0700d030005440d054039121048a040181207807641c9000c150b6110f0480d1074103a0f11400c2d404038001101c075060240502c1604001070506548003200034280c0f002d400f80106c4206004001d0011504000a100c1600c1700500181c120403030b1601d00c14110398100c803040380d000e001d4900c1ca2000c10300c03400048507004c20640c0040e400c05480005d00c120282d20030000d00a8a0140044550340c0003054140000c13845070010150018025035010140090380001c10001030f40103900115519a01c481011074441a10f212603015034007480d000708241c00c007582446104100a201e040c2186000d40790151500e1400c0c0c207030700c1080b0040d800212110301036849032212115550041190003151501035000b4124168141c0c41400e02c0c10035082c0083c558000c840c0300c1d100030381e0f801c0140c002c6c200114100307800160421201c0c40003070000b00f4264003503002500055000307a03103000d007900b005900710042c01405401c660410144069045410f961000020713019542840c0090303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 144835422 1250 144834172 144834187
    0x12150c0c06020d0204050402030c030405062a0a020f0118111906050304080d0f2a09140f03030c240105010206010303050d0b03010c0e0406380f13030c050904050c06 72
    0x717114039041031b46d0051000c400d08c0000ba20b02d00c055885148a00c0c02c03642a80c841c00c040c0000004c09082040e2040c0004030702940c44040d05001c0c280804a82c01150403110ba400769090960b00c80e50180d402c0140000490350501c6a0301c81100c89414041c0e03041c8101c201c4450242031140c1d0140103050911034000041400c001300e040403604c1400c80c11004100c1c040f078800c040343c0503110b038000da076004c10103c0b514a01e654040b078200c81d80c0c607030b05a00c900ca4a1450700c000403646000c0042c046901c2640115006804c6e103041c40104140400d910281c5416103042092a03050402581c84040d80690303140180078990f0005105810749805084c011740340d06581444901425111381c1b015015401e0000010348141c10100720754615808481c02e00c0610f4030341c4218000342e0046038503600b0000d0068462030360502c81820100c51143c0310030219103040c54511440351302d907024407500102c5420480040081c4200b00382c100c00030701411074140c01d1340c0c00c0944445544200d05031119206950005840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 144836672 1250 144835422 144835447
    0x1200a03020901021e01090b01090506031005090f01110408070b04120615080a260a02060c0307031103150112051303080606130801050f0f0c0307032412150c0c0602 72
    0x141e420b0074002c0d11013000f10044000b2903018020071f42040b14959410000401e440070030b0302605104880c080d00030080f07a540d0b1000d00000e4207020300010014050502d6000d0b5954007805588003031b104603d4800e944501c3c09058034500b800a40c03100c1c1081106010600150b11003234078000304c090304010085913803810418902213441540d030042c002c1e0700c5118128400c108003141d07042c17a08003024511184017603810400400c140704140a110060b040140003e4a0181150280d40c100399246000601001100e04c1c0c120f1030ba20070b131920f401140400b10b4490403581e002c240758840002c081c2c0706101c00d05200460b4401d290148000400740240c410001e901e58a400c010760740c03c0840b04010180035039176084040e0080100303445000385101c254000418806003901141e0003880c800c6005440c650350603801b1001080c2d00550f01036204c089001c00011111100f070402d018100d200c0c80d0340004042440e00050850402100c102814201131084090940011142c1d541b260440809645c2d5000480d14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 144837922 1250 144836672 144836683
    0x5090c0901050d0e010c090609140418020406030f1407150503040212120d05090607270305071d070306050306010513090210080906010b03090d030b010c0b040303020a0201200a0302090102 82
    0x211601c07915141c0403c05210054100d01d0b00f4182c07d032920044141c982404a803025114000e048201400c0d00d0b110915050903803114182c031041402041010400b9070000d41510102c0c0d009545c0b20524000315028400c0500c0c80c242e241400000409a10f860700310344403641c402c0510300e20180200440040c040d510349241010341003980740296103540314209500840f07a0825050406401d03c5c150000351100310000d6070f540989034545440280b0b0100c44252100c4401e04686995015182c460000020350200000005090071004100c0424540707080b40808a000420300c0701054280f08081016440200701d41341035840a555602001c00c985410320090009554000d40002540c44004001130348a21914045c0c81d0210a07540543d82e40e851b40c202c140401d5581c4425500071010014096009034048541c0040605141c8121303440b46e202d07103050b22801c03682a80420340000c0e4105035140d0a216641d10000d100e10400b007100d0901c011151640a400d00220a03d42d00082813500c50317008105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 144839172 1250 144837922 144837937
    0x30c03021f0509010e0a080f030c0d05161209020a06050c01021201090203151203030c18030f0a05010b010c05071206110a030204050a060c0f020d030e0d08031008060105090c090105 79
    0x41122008039103801641c000e100440c0c1104255217046604103003448046840c1060542050429080031440881c281c020350014054400c15281007041c00c442d40c1d01c5024062203801a800400501c2420100181100c81070f800c0141801d440d08564600503550144240b00741c40e410301d0059100c500380398039103009204141e4688003018607c0000500c800c21a0001c43c4030345814040c80c0e0b071000c4414207100032038200641d458484d400030302c0002e41001890014000d40070f10b0303003280041101500c000c203040500d8a0b8040525400400c422030a0200901070000c0801e02883e10f45403613403460700c0c0c658542c03c860082588224a00b510b070b40500020780c1040d009007211450320b9036903088594001d0001c0d405841a1409003c012200145890082100302002d43c0c001800c3c04643c0320503030800c9000900b0b618110f044c061400207514440d203c0d00f40120300e00707110307510b070642c1c900f056444040c10001660191205038031140040c822511038802d916081640302641135207907084100103071241d000f02d90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 144840422 1250 144839172 144839203
    0x9021606050a110c0705100201020c07120f080703031406060a0c020d02121204091103060d06021e0318010e0303070c080d180606090515060a0f1214090d030e0703030c0302 75
    0x8000c092a10040741d00c4040321b0080340e41800e42c051920f0207a09074052904d4040d25900301c0802000400c8190701c04221480c804c00002080c40e006545e000d102e500803800c10381c0081d50304c1c01400511100c0f4070a2a82156048404500b072071300e03d031340040c0208803100c402401003482c419032508540354581c80c10450010801610313520000850b00300c64176049485840611400c0010680b20102200c003120302410b406045c440280056865500281d03000c04001d10751840303003408030b06071000707940c01950040c40d04010000001d0031f9149800d09440c1070f26080388840d0020018800d00c41c0d0031401c03642070240c4c17003e2001d0301c50105131064001407011150141d0391051f070270600002c00600744e000005403050502c080046442c2c0ea503c0400c0c0d2941700706000d400c800100314111203035000301e1200d0102e54070b43c40d040c0d16036a24405090291020030201b4000e00600505000c809903060184044480591500700040e1a5403d6050340e00d914902c40903092216224148061520a00c1010841c08452 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 144841672 1250 144840422 144840427
    0x905220b04020f1e2d0d1104081204081e160e070f17040303020d0f020705070608010b0a1d040905010216030e100801090e010e0f07050a09021606050a11 67
    0x343c15112075038404a4403014a1283c0d400780c0c0c0d04000c000c400d545a040101c0d9036100e8003c0141c2c001c680c2c6041c40c80200220420500140141581c24024011030500d403010071901c4130302d884006441d00d403101d0102044e02c6030600003403081e240700003000c2d1140d01002c40000354985104000360305000e4500c031041c40001c4200d0010519414901115001d0161541c40307240e40803000303d080340c5000780c800d1091403070b4910324040750109100e82c024120342e42a0200001c1d224a051844a040ba130003010100e0341900020410403166401020741030060001c181a07a14080c25440000c1c02548000e0550b801032800b1300007801d65441d55841410307103c0c1d0100007196603002c6c0790240300702e01c56020001c070005200ea85600c0940d00b04840d203035540404c56251840c03540d08000540f0081c00403030003040015943d62035807c40450003040441d4810110b0380c054030a06041005100700900a5001440c10034010024000410540c003020070740e0a4001c000000d1540318001c0307400240000c032207020722001c0302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 144842922 1250 144841672 144841687
    0x6020415020109020a051816120c081806130303090c0506040b09030c04060501020c0f150708030106110106030305090103150b0409141806040f050c03030d0203090d0905220b0402 78
    0x15800300703858134000c40d150300c1c000c3e40e5031007000050150f18904900e0062614041488640349650031403a41426040103907d03c4e40d04c10b4513200700d41107080703040300060200c4180b150f050340000b1000c3e2000b24160140100307191101c0a00c00c2012412002001c2595a00400d07080c401080014030180600800701176680b60780e5211a013075500a511460301c28011034502c01214075082c45000111001a0083d1000040220411040c445050306482c0c1251a0220030b101456400c0001c208541c45004919202d504150008221034041c1001c079000742c0c9012410b101094002040d216180c2c403d181c0480e40c610042c01c0480000400d0f4415222102e010a012030501d800d070b0403c3c03c00c4514648071404982e900160200a0800300c003014240e0f030001000310b00450030004d6000803249c090001c90350801c132010003281c95680b00300420002da45e408424840340101c1444110600b0001e807516204460038039000450685241605515646081102841c0805d644c0c200b0b4142070001081192218103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 144844172 1250 144842922 144842927
    0xe07020319081602060907050d020301090510090c0801050c1911060103032001020702060906090109080607030204030b060f011202090a050d0510051f0e0613020c0d08010801140c030406020415 84
    0xb001e0301d01c1d074500040c0300d0903002024400a2243d00c42d001043c000c02d801450402844000c08441406036055500d4400c0704010030020801500d50032141c0c40c000a105465043c91800d10b1000e400003441641003d05011801c40e00f20141d030fa403401034039940c0408800076102582c1644011241c0f081602505000200341130708040c802112100301035120356103001925800c2d08038818404025484001400302800c00d00b000703030203400c1c2a203044c10003514994a41c1c247c203240410403241280000e030002410700410902d10700e0941c0100c0240e8000c80400318480020300301302038a690340395200d54003044a501680d50000e05030010b000181c44117290081504020340c07940c60311120f9038a0310341004040f841482a440c8201c072a444600d07480a41e00d818100718903440180680080e6102c80c1c5a410f82480d890b1500c01801c4540c040f500030280d1100e825400382103510141d02481a992400d800400309110300c60b4141d13400441d46120a0307580d9500d14112009000316000340a040448030345002020340c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 144845422 1250 144844172 144844187
    0xc0f010e2e050c07150c050304030605091204060c0209041b03060203040c0e010510030509030405180405120a0507030305060307090203041209050f0604050402280c06180209010e07020319 82
    0x540040a44000041d100c0701914584a914100c2c00341307501120041051109808140b000b6250a2400c0139012006031291440c642058005841095907403052186941c0d0402c04081c100304070382c840e80e0405242207809010804201d0010b0700035030769400010f082000750340d26000202060500000c2c071303c0c1c4038100000250012034045448055051021911940044c00181203a00c000c040709001044104110302400c0003a084e0341c0e0b11300c014840442d540e525480c09441c85403414908940c40e2825044c082d181041c1c616000c10205020030158524035071040485109a030182030210700380d11100046440d00000e540001c01540c0b0200a203c20010f81d1690203003d816990b9884112079190340420490440e9160051303805041004204000d06150f0003400f42c0750040854000e0202c02c1c802740c83c3c00052030350040800500b190010074200300d028403403c40308071a1404440001ca6065001c40e200c40418011400d50310703074000010b40b84610800844400c600c80842441ea890580c82c0040c03c50b2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 144846672 1250 144845422 144845479
    0x308091609091b0312050c011b0e031011041406070b07050919050d140109021f1b110108190c0206040201080f07080c090a050a080615090403020c0f010e 67
    0x5030750720180c500e1541c042d003050783c082d40c2e00520f64058549001c08103450a0b404010040354954072803005140c0070705881500d40822485458000004488404250410031040c0d00c0d00b4503585480300c2d000340a1410804c3d00e040da82c2e81850003074104a0381000542134000d4840c000c212060b100c003089a5135a000003e4141500d05036002c036a2070b110052134002d41d0030507015540c2c01152001802c3c02061024480c00182a102000050781581c03e8020481c04644421091029182c81520700750140e80911042080704507e513602c40240340a648981c4044000030304a41000000320210319030100c00980d410300060300c035900b00201128400069180d0344100d4080c0d010688003000100c3c2c262092803542d115008907521030341c443d0340b4900c40403082d40250f640c42e60014a1003402081c40d403591680e000107402440c000300340301d18158a44215032180c2d0942c0e07a0180380550b0038800025000a54900c00417012107054048489400c0102d03106c05540c0a82076114030710784140000c2010903118900b05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 144847922 1250 144846672 144846683
    0xf090b2509060503070c0c0503030703030e070b091309060b0607050d0306060807050a03110c15010807060f0207061232160905091015050c010b090112030809160909 72
    0xd00401a50492010710407100800d00400009a40d03505c1900c0d203220407813141021011013034071a00840c1c41d581121a00714042940c51888020880c000c10000d001400748a810901d40320508001c01c0c0b480b40d200083c2a000ea031100000b500300001900702400e848805807400e52110391506289546003400840e20001c00d00c0c0c04000b01d0883c0c4108103152142405482da5031a155201e10210000c040305010010403030414042c3e1901c1240610106441116811000030107504010049041680c0340d1700020a0007840e007298600705402180480c1202e0050924105010365107048601616402d0b560f41c040c0481d4405041c900c81d00000c900d08400028200081c260340d80200d5010540040701c43d101c04034603620001c00091a207000003d034886030f130f207114a00c01c65a6002e1150040e61000680c0c0118202081c8158842c0c0c0c01d100706007011108a50594003949454080301e82c000c40600050100001c1c2d400040106a0800c01c088010040b03100450040303598000340c40080610401c1100c4c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 144849172 1250 144847922 144847981
    0xd090827092a16051b060301051f1710061b0b040813180e101e0902041112160504060f0f03230a0609060506091216030812010b0a020c01030f090b 64
    0x2180c11b00b001503a0503514043c0454a1031803551074107051909010700044100515042c581c110b030301d628000c40703008488607040c0c06101d504043d0050302d0000e110039805d4000704081d02e048041644c7c0001c2c5034006400500aaaa6103207862500c90b0080080c7c1041103140c28400d441c0001d8107540d4850601c070030002059078040150314020605450401c01c0000e5040c0160342035450034502580321541052000b80000ba620b10311071407180b03164005030a442c0303090149508104540d000c0a03034401444c02c4a10748503250504080d0081c00711a003124501c000c011050912212450203a800b020740e114048000c1506003480600081e5600f00454548019600f0080e0004000882c2d000322026500005c1c01c060800c1c03036450622240300441d50900b1b40314030949000c040381c04000a10307680514050f050b201d80c7c81c2420741000710401c1040e4410403040204000c00e07520142e012801c100c0400c024030780800c4001507028a00050282000040e0083e1500018006039068001e00042c0b284e08020343c1c01d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 144850422 1250 144849172 144849223
    0xa0305060d0c06030b01051c02090a0b1303260c0c0a050402040e0c1812030405030105070e010c0b090313080307060c11060403050d090827092a1605 65
    0x800507855200040800300600c90500c11a80690000000480c0600d0301c80c0c145000100415070640d080c0e008041c506600056100c45400c201c1d801101526541c083d1510304465030078031001c1c961042c80090400c0b001211414640d80311038a074000711030181c0d004140c8a02400400c0d80d00d40c1210940c60b07100d465035040006140c1000c0c0251011941c3c4150b0740c040b180d072042c200d14600e501c480041c2c0c1c04442c18401e00d815030780d90130203114110a40c8500441d1901e040c03200341404c58801501ca0400d1001013a446c00d204c0c4c0c0e10240240c070b001d80c40403d14940380c41e40e003040307441c50050980079052009120004618541e0000c081d02e9401c1c000c03203041c0101035100d0b209551007030403581d5140b0103410000004d03020a02070001004049000322001909903000c0d11800501d4100403000c0303c9491049161455416020000c031200c15003c039003141160400b02c4151402c0302425030f079820303031031013405009102c64120025100c241c0d41e031b10010211000a454815211604e1000c82c100c018134400750310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 144851672 1250 144850422 144850429
    0x110307081503070611070b0a0203040303090b0304320613030206101409100902030c04030201081b0301170a0506010e04050706050f03070302090303071a16020a1203020306120a05030a030506 83
    0x120301c000e000e000781c500142000800c40f81c0c0d407040a2012014030594100081640c4084020003250031241c1c06991124207501d402045001168845424000288180b04c04500151104c0740d441b009110601d19000c16241f401109150713194030711840c0d00805042110120340050020300441c0b01e03600766400c59a500c2c9003402190014000d001d0321041d04a0151610306103500500d40104010780c0b1145219901d154220503680105c030004551600484c0400455802400302c54220700045005000540303140000c1c159400140b00f4024034502c4202400c111b11402e11000011070707080303c25a09590f07103860180c421020300341c9040320648a6807900013200c0b4070960640703100c481960032031899612006811006500b050b9451641070004105c5900012103088000d1004015005164000d00c0d180512038020b03003081c1d80c44015900542c90007800502602a06c0c040c44c0a03508005032039807221030202d544001070040c02d00031441820072010034071400201806405a5030f40d4207206a81d00d030000d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 144852922 1250 144851672 144851701
    0x60d140c04080c0102060408030609100806040305090406061b0b06010c02090c030f160905060703170712060b0f04210c091b091401030c1206031a13030c0602070503090411030708 78
    0x80c023803903400e0010803182c0c07904950b216042400d100070303021380d113458490003801c1a2003600c0c00c40c013040b400142c2e40c09030304041c09800b00030000e900300000c52110499855003940305401d0b008000260840010300e44d0380c0544018568581c014018403590724100400c6100c991003650000c2040070250001080322550b1144202e05170b620365187da0b55246807605000e0746030000b10b001ca06010001a484104048512006115120990301c1c1c011002d4101d100c1e6003250301c03035003102d084104100240008144000103da0880e28152600030050302502140c0c0110100884006c011407904540086c80c11402c6e00040710800c451650301d50315201e0b15005550700e040c2840346040c02c003241c40b20791105601035449504003509a003083c01000c0c0650800800300e5a00b07030070440344180d0360998203d0895442000c1da0f4081c0401d10160740c40107054501811507c0c88882c01040c164000888804125061040d5620f010019105200c0681c0824400c1103a41045900c140066100000180ca545a0003038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 144854172 1250 144852922 144852931
    0x60302030a141b0a02150a141f1211060c0d0806090103020d0201120609060f0306050a0606020705060a050c0d05031602010506010f1101060302100306080f030a0e060d140c04080c010206 81
    0x43e2038071440c45062406410360015003d24055004681480f030100d40c018001c0c0e485a0a41040050440c40b403020f00e4185103005003181201030038003270f02c1542010340c6c43e10142c140c42240508942c03181c81441c12000d080c1c0b0480d961a04004041000003a020000a209588101c01c0e111000b0540d22481440107000b0300340b10282d845a040104800994060105074600c1040008040344140d140c08000040d40d02030f1340007003191100d000c1c0400c140b003a284100e40e0094251841804a6481c19500950785d0606000b004d01c643d40000300091f06d140140c04603489600400c050316800c00290300c000e0003d41040342e94006a804c0d0f0840300e4641031040c80307518030507a03050312900014150304100b110740301058143d040a56681d44004000350340d175a0000c51203062540c3e40890403c0c20420500e0509070101e110781c105520a00c2102c130003e03009026800960801e81d140b584480403082c940010f085000d81094240711840148192843c1a00c020300a94020000b103902c2c0481281c012a9100342c100c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 144855422 1250 144854172 144854191
    0x1b0e061e011407020402070209040b1603092316150e030d08011a04120f03170f0c0a09050405090a11100912020d02120a03030506010507020d12050c0106060302030a14 73
    0x40082c003060381c090000d09145400030b40010708018a0b036021981b21041070b101038441c90385101c10003020606003016a11422041d103014429001607581e1b40c041c0c01c0008400f4142803881c2c43d940d100a03501041221400b1009000440d4861303540c424808021860040040000d1080382564a00d4100080e400a10804e140d40f9080f00e686040c5c0c1641071000e04405060403203c0801c400141c840c01c00080c03510050140202e18121403082c0340141440184000c800112450081042000d2078118000c580c00113229218039038071880401d08445903503840c0c20155215290405000c4814800245c1c245a1440707580000b00200700242000402040e81800000041020105000d1980c24010380f003911480a03142e1082542c09070700161111145440c000e010f42e10034241c0c00203241e070500403582c0201c0d007800c1151409003107401055100e40c020704c000c2c0c01e040b0083c1242c1c906611075002c8035000d540280081240c55116030008019500950313003d49000d0407d00f60030b086409810003540144039a8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 144856672 1250 144855422 144855437
    0xb150f030619080d0201060f05040e030706020304020a0e040809151804090230060109060509130c081009050c030706021504080403080f030103031707080a091b0e061e01 74
    0x107100700099401089010321550015641c00900f0010402c04802103900e01c0e00041486402c01005110014141d40190311581c100707070603204015804001c50340c00ca50401e07070250380c0e86e0325400414000030b21070b40050031640e041000c010500100b400039110048084039041c085050f500000e045501401c1c0d28404015074244480100e40380951041ca061803014014100603000000100107000794002c0031181c0c03c0000100130850b540c244080c0e400351081078410070031241088080794004030f0081c810000005500c0d1600103001c41c1b82c3c3c1d40c500030840311044031188013900c0402000381a645400302c81a101d03018802109103030210f440d50039564141c7c0200704030450203005401c2240301510654403e40b0421000c408254010000c0c03089292145169540303514500d40105440003040d14414a504030109102003184d2000b80300303804c112001408035401c412070602d0084031031070341c0ca0b425a9064118001609081c030140151240c0f4044a401d03c022104601181c440ea2402500341d0009004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 144857922 1250 144856672 144856681
    0x50618011203020f030d0b0a0f18090204022a0115030b2806080703150221070224070201180b04081c0c0201060e060a030b0a0905010908030a0b150f03 66
    0x5041c0c03440c4800d8000c0c81120001c00c40b1000b500c1c01d540c04814580a25601c5030400009401d09190850041c0ba01810a03c0105c0c0307480c500000603441c9080700361a05844080900c2507590f150192462a0071580302c480320310002c05c0e0324501242400002d02c07055400d00607a82e921400455801d000c80390443c0300c48101d65105803203e09206070317811404140c4204881100c9010382c80b441544007518201e00144015800d6041c01840703240717428104040c82e8010007848500d82400700608900c484031403400300c01600c1d0400103900b03121191007a058500801c50803000c605d0040c0128500580701d940080000205c02c501d03242d19a1940c0d00007810341d00b01d080c04140020b0050004054014800c06100811190380d810030040e5900210000c0043c0e4444900740120141c4001721034000303c00b01c62015002e0328503500d820b0710b404014805100c42d46d545040c034040c00300c290806503515500540b01e9075a4039010031803000400d05648154019a41141c881103114088001c49030b11006031212030b801c5544 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 144859172 1250 144857922 144857939
    0x8120405060a1713021e03030a0c11030a20010207060c0f11060a0819020301080a03080901090f0c06030509010203150907110f0106050111192d030804030305061801 72
    0x640d1000b080050b0741d6103100c03000702c041c40720500074013a078040559203119900400030607a020300d603a160460040d4403c1c40a80e074000040b94115a414201354606607840d08007140c0c102981c0e403142c2d03050b01822242104014000d03a5041e440754415501c00841e2540c5001265a0000c80c0503880c040303044d007100316000c03c0300300114640c80c13840741c0c5002000c0001c00c00030400750341080d040b6a0104200320180302c18640319561032a40c000c90707048214115031520003810354138510f0380750140c00d001c2c003a004200465020f400209070300d508104004440802d6240070003420116215800c0003a24203004120010010300031207000c2d10542080d81800303008141003103100301b800ba1070303030341401204660700720619418480960b2408021740005940b900c0c160001d41040454400780c01c080d0442a020040d001200d4902a00980c000003848140b000e221a0000509140300c005400204024500c00403d43d00107420b501c107a100e558180a192206028010b000301d095a04040c1d040d1030000500881c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 144860422 1250 144859172 144859177
    0x2004030b0a1b050a021c210e0109030e10080f04110d060c090519030b1b0403050304080607090b1305010e0103110c010e0706020a0503030c030c040504021903060812040506 75
    0x2030080e200000d071101030080818580b801007082c1800b141000c5008560550144644825180d8140501050384039411009082262400c1503604c05603074003500c2c3d44400b0340e542c024555400044001c01c0a43d0940c1405042c0500200f00944031344140080c01c3c00ea9440f03002658042c0010010120b929111991085601d103000c02445800c2850000082c0c0810312a015490398003085881e0140802d00305800d124401d202102c5845003500d444004100140846d490389502050400b0301c2c00c00100305021950940c403803580050b002d0320020501081c1d0310808200203000301d9035500c0b00ba0a00e6074420182e25140a0b84400306520014100c6c1046035501510088102d40d5052400040e140381c2c8a0b00380d402c640140b41403103d660b44d40c01400e40f0b10702d020003c02c0060b02250004145011480e55a00d65a22008000c401c210340044086003140d400b213030546014000c020425510307140c00d0318510446800300030355034001a042c40c20000d444100852106080c1503c0b14409180c142080107004240c2d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 144861672 1250 144860422 144860431
    0x20d06210b10180b040902100801090c0201020a05091e0925030606051e0d06080f010513050703170912062e0302061c020403030908010b0603070801050f03070e07030f2004030b 77
    0x2a11450345800699402c03e0231105d00103903482352440740d4140000c00e030440302501e00040c00d43e841001a113902e660828240c0b00c16520490b02141c200392403941c01007880100d00d59040c4c002e164881842401c900b10400462205242194110302c0c06280c481141928490300c190404a5420440d9241c40002c03680e01401c15802c030050391b03203400204840c090458140d9800301080d500105200c06480e82c082c022180c1094596407803241e440c0c03007030b01c1700f81d159203c034400180485a181d690b10300140c0c0c1002a100811b4006100d4091070034941d028a031123010071502c40081d4902c072011000140b04130074034004144a61024040b20314110343c2408080d50040f8500100c0003248880c3e240b50340254001800514800d075280e0440c01e28004a2500f554500c0c5a6144a81401d1080010302a03202c00c01504544c811541810068803000100c0d081c80b40d290070070509848080c1c1080708103505600f120074110800441001003290141c005081c1d8014071b40e40c503142c20400c0001b000466261000203800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 144862922 1250 144861672 144861679
    0xb0a02010e010c120504030e03060a0c0210330806041202160806180a0206070c0614180f0d0c0807141203040e040804120506040218040c09020d06210b10180b 69
    0x8c0b0b100e00d0300040c0c5041e10407250840007944451200707020076418040004100001d0405200842803001c81ca404966030150700e0011412881c0000307483c41052041c0070050a00300141d9074242001d00b8008088003000340c101003d840340f600042544640e0303a820004807076049028003d591111451912146264070007640a8031481181802680d90200101800ca219168030300034140b0f44107000d807001c0b522403000300c0d242c0320071f01050841c0118050304002c102c504907500801b110314000000c9540d0707840c46c00039181c0300240d90b020820820020f5188141c81040c264100040c00c085c0c10401c8010101c070000d4541d4105000c00c100d140050100541c000740720700c60950525845900303003810341d04000f209560a5018006101c1542000031a0784400c6100c014488018505619000140e4545200c1c0844455000030014510b41c450780c40b00c1c001e850100e101c4042d004440103032100101810805440140610001c01c80c844941151442210360203c189072220f0301c0c80e00060024a0b408503e10740 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 144864172 1250 144862922 144862937
    0x7050604020402161a07080c03011505030a02070b0406050a06051512060303120403050a090f080d0c02040209030703051f180b0c070b0106050307030e060c0715090b010b0a02010e010c12050403 84
    0x24030040b003070030039940710881005c205103403010004040c54009440d0380008481080148801201e052402003000114148980d403910b40f03a400c1030082c0f040700030180c00c440a42c001d00c8204042504002d001c0e0850031700c2800f48945034070400c006032594012070703a8001030070020411a60459a01e807540694000c0a403428041c036003540d841c40040443d01100054400102c080c00550003000e510040c005840d203207800da505008041ea940c603d40c0c56000b0500980200410840d41e03290101c036000c00c405819550010303030305d1800c00e41d296a001020400d045034412441103900080c4911800d0048141001c400d80440c2e440c2d100c0d607080c0242c11200082c008001c0640428544c01c0f00078000d04032030b0742c3c007030390303850004002811140f00b85c441c0c00311501300000303004003581558291115030b500b1030355561610365040340220081100000090180010500014031a640c51001c0d20382d1168540085c170000c048400c101d0f080350201d103040342c04280b800340c41c10400c45182d0b11440d4414844e081c81003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 144865422 1250 144864172 144864217
    0x40501061b0f020303040519030b0702121b0705060d0603021c080304030c061103070801080d14301302011d03061302030c150423100509010207031208010302040b030307050604020402 80
    0x150848c8400100e08820b50b07015034100204440e03c1c1183c0d601001e10f10107403540c0d0381418003c80301e0703100d00301c0769083d03d00740c40d0043c55255009000100c01404028074655854200801b000e001d0403031071005a105514070001c1d074005a140240c09a127959014070701d107103035607500d540a4518030408081900c120340e0f01c1d51400c007404001402580540000d481d4015a5890560614a803900100006040000300c45e001035105401d40107591060364003840d4080781c0e01c100364200b0720190300700d942022030f8514241808400c0c040000c280b60001d000307070f84140200541a002c0184115003402e4a078144e0b1000c0e0003da41842814008040301b4402000d55030300d001b0200005008800040340703200210340c005010401040b0341d059100f00300d2903a44200b001c6100d014001809602c0c0d0448000a0002c0011903020070781c0f02340300c00d0300a10b034403038888041a000d0b004001e0806409000c05c07806140f801045807442d25002055030700b05680900285030503543e990a00000c0d41011016007117100c080e40e000c4c4c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 144866672 1250 144865422 144865429
    0x30c050a0b0a021902030c2d01021804110406050a14070503031e070e031f0e06011211010305040f1115040801020d050f011805040503040509090309040501061b0f0203030405 76
    0x1e405240a80d0025850720035041c400101c1d1250301d060002135620804c1200354012010030071060290202d89040c80d241007100a950300e21a01079000c030025440000e4081c02929170304412641c010090790304221902000103240c005100382d00680f00070603814400710545504c50884403c0b181010b501950a114490307030741918607041540d10504c4840d040240d0b203070802417004150f90200441c5030020840d080440400e80740d400f103280c0d00c005506510f00c514500045a00803880d00d140c1417003260000d42e501d8403001443c1494250407100940c0409070000f41d0f40c0700780a5507000d55000105642d0a5043c3c1d694041c00c3d104642065400003400010319a10f84044800341008055840001d640d5107001001d08013100d00050009100010500060080184000380d050505164500000c0c0c107848a051841c03039400f555118079406850081048078644002c80074100640080c3c406000a0362100d00c256802550102008604004002d0050210f40303840c81c107404040c00502564a0181c444001c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 144867922 1250 144866672 144866693
    0x60d080c011b08040201080609100605030618130b090610060302070c0f0803120c1e3f09060f0a091403070606030209011211120f0706020d090603090f030c050a 70
    0x480214803c1000c100c04d658000c030b54664003000c100c90308101803078440310501e003c0d1a00d000700400c204002c40000d45686a48002c00c0c030783c1d21104d00c0c034182803a0228110b1518002040d04032461060240419104200000d10728081e808120302021007a0a21708210004c0d00212000d03034006d0348844000920040c0c100301c030300107048204060760b80e9006040c03083c5400c50024100d2802180100010030a0b00b01180124804105055609070b071040c407003140c06500c214140001c0302d1144d0701c1d02e0541451004a50580c1d5401c42c50300c050340e40b80c0d40c2e003002076240c4c40201e900c0440d0129800004d180e10b4000e40c004403066102c1c0c80040c502c440321f6489903281d50445a421030b40140e8030501070040d0300d001540c250040031a1001e02c03950f40700a0b580c40d1102640d01c0341030f50103a10070040071400c1e0601803055202d00c0c10300c00c040741c01450317649070000e50f41c400c1c0d0900c04001c21901c10703012070143d10034000e0850f420382040c2c80c005011000e03030f800c0b140400c04490a4405000e0030b840311000440c0c041e00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 144869172 1250 144867922 144867971
    0x191b0807050d14010501030c0c02060304030c02060403060c020d0f0e090705090307080f0109060608030315040b0a0b03070f320a02011506050a0e01050301051e040e1f0e0303060d080c01 81
    0x1120f0159810880050103c8820801541c01d1080c80c01e04000107946400807254003650600e810b964a200601c0401d601c0e0045070001060310b414003428007200c660014848905488a0382c0e8102d405900d000c00b0354503894000810790b046008000050380442c0a0001081ca000016040700c00c042d69401440d42003c41040448800381d448245c01d50503c00e6500450010b001982d010318698101040b1208030700081650550242da10f948a1243c03541d925205540103100079821143c0c0c9141a8800900e04904000d6540c0422002c0b00411010607600d100100d1030140f2580c012200c840120254065070002440201199200d0354581c0001c40f00d005d000d80148400e0321200e40f2103442e080003528042040e00c9042c100a000e000410250781c4070341e91075000001d4080c0d881860f030740311000304018110141003c83d5602c070700e952411003035004000406c481c40c0402c2081201a002d9034480d9181d1106441c81640181000d105402003038070800181440903c45000080b046a0800901d0721b040c0d4004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 144870422 1250 144869172 144869201
    0x708060f0d05010615081e060d0609030507060e0d0504090504081e0a0201060e060a151125080607081f03020a0e010612060326040306020c06191b0807050d 68
    0x1408014181c00c1c150344c2c008103042c5c3d081c040781500d413601950401418403444002d03101100c0c004128551240e10071140b8594210606001442c150701f009005548002801c40e46503207030814043e81c00c10042030086966007a40d42c0c6914040c42d01e05078002801d0040d10550301200c1c100b1100000c60018091081002128089036480d102c0c1c1c1c02010342101c600e503001500003003201003000041e6440c01c1c1c001051b503245111008403180c42c480100c0b803c0c451a10005594407400c1107031490500c044003c8041c55181040701c55041d51548001510751105803100d00c085011100440c003442824218282da001c0a2010100c0507580c0f0740000b1a850404d5019246582d6042c0041c03058980c000078582d113541c4180400e0080500d19924040301102c074045490905010340443c90341102c42c0801c40e4021504001d0a64480300c0340100e5903200c01003641e5040d002d540c8144081c0220309039000d407000c940c4890b07003071502c5410950419100c3d102c001700010b040000805c47c40000201c2c0b0322520146a04a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 144871672 1250 144870422 144870431
    0x3030f1d1e0127060f030e01110417030c03030609190501030803040308070f0e060f0912031b070f0504180b07030b090702161502031c02070203070603090b0708060f0d0501 75
    0x110014143c4000c194103d1821400d2040040c40301c00083c0380c80040307031800e00d0704142c0c0c1200c485044000b004c2d507007050482942406952408010305d480a00107441c80c0d04c1129920103280342011799644240b0760404211b030000d0000075039526007000302c01d611031081e901c41c90940f0800c030f081d0720403110300342c008490703800c004418041410350006495501016034140641d000d602424054021040e00305818458580000c14401c43c402d4002034524801e07000d88205030400c403030030219850707411070345040701d805004035400405610b00103806000c44810340b1070000d810307040c402400058524050f0000f41c00d0b1682907140001002c4a503810f1044000c6c1c1e0340024180809010041041400340c24013045600c04005400e8401b03409140604848a5060004900d030100c10140e043d80a20714000780c083c5402c54402c00c100c03003203800a0441d40d1084081c0c8d125103480300c60640031100b000101408104e00c001c00118250f0043d90002d401c032400401021440303000c2c8000400c0c0c80d812440844251b5144d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 144872922 1250 144871672 144871729
    0xb0a030e070b0d110901050327010c050408010f0204153002070516080d2303090703030212031e06040f020d020a0801080102071e080c03070b070206070903030f1d 71
    0x182c42810541413814000a182503d100e0000f001400f000d0500900d003003041c07042c000c0f95a40d41d10b0700211f008500009102006901c94040c017a90014450a0241d500381250f18501000e5882200d0a81c1d44500a5901032511800c0c1101d80580100c7d4083d08504540e001d500c01a00c4079140300e602e4410781c8405030f90340c0700500e0014200118401c00e1404c01402c0c10b010311040c00007081c0c24080e407009250107154504801c00c0c40007001600300d0501d0ba80c2200009100e0490008501001541e001c2d0302140c0500c02c01c981d10100d188411280d00324441c03100c1a40b0640e00090058994010078010404504400941d10041c101c2c3e01512503044140e60024030345601d21b4100d10414010b04010000b18145810307600c50402c400b1403000d1032095000b10700d0740c0b0f000b048600c0d401d07a009091240100d03510f0f01103500d0302c02500041038406802511501c8001034000e8801c00d1200152503040d0345032214402544001c0d25404c240304d000e81810403100d0610b82300c86c3c03102c85160b2070400c9141030000c040707000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 144874172 1250 144872922 144872947
    0x241e10031e030203041a070b01030308060102070608060f0d1a01080c01090905060f0d020a18060302040b240d02040302060708040509010506030c1912020d051801090b010b0a030e070b 80
    0x401c507070030003072041e1030303800c0008242c010054504642c81e400c07030f2203541030451060581d641b0a2140092072110ba480022040c15446a080d521509082c1c0031190001d0710303100d00782e501d040221600b075800304000044584909019041e103031071034800d05400c2181c104900341c1c0c1f94040803d0b0012002d560200b01d003903000307680c4041c1034001042c1e000030400c082c0c1000b44c04901611031340c09600f40501c60100741c1c00e00315180e1070302e550700500803241088030604022013407001800711440240c0c840e6040601a10b05460700c494402004e005074180d1070f403906482411003000303810103040540c1083c0c1c00d000010168440100900d8594410320340300e980c071814001002600303041038200901036402801004002c42540007110101c51b004401030140030f40c3d140044811b140e03040c04810340d0700e0001c100801204410f030821402007040907051400721104224150803100c151502030000c2945100400203440c0d0320000701b0030082d45150100301140380b48042c0b072402c0002d40c0880e84a49000655001005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 144875422 1250 144874172 144874193
    0x60f090e090a2d0204090305070f0c09050a051608060118031a180d0e0d0c14030d030b1e0a0302060301030c180b0901050f120d03021209241e1003 64
    0x34052480c801d82160343c0c0060040025400c1d0f4000d00440c1d9483c50881418040c00c2610340b01d903804401400c9841040c039009261001d00e10880701001d0814010502c10034603400b40728440c464154190a45929000045030051800f42400f8144841040403004000304d01c0d181d01b01442c01401e810903030128240030a91a80b40080c8401000c1600f00300c415000320011030b019034121160728001c408000303050b002510720344e01008014034a00d03003400c0c001116a01c00184c030901d82011000e880408001200c2501030b150518800e550140d9088c00d0703200006030b8102c501c180014086d041a2a80340c5139404100355920a8000390380c0e103040340400b0001c0c072010300071400c000e01d074101043c0f020407952004504c3d0110107001d0b19100704e0004004100c2602c40030064002c100c655400c940c40d8403a04180680250700c0f262246900e0144ca00003c3c02100700081c1240c2407030703c0540b2043d11080e4011125074401c8000d0100c01c0c09141c24110040d0f203071020202280202b0045014000c03151461421074103a6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 144876672 1250 144875422 144875453
    0xb0a05030705090103020d0c05101e0801050f100c08071a09070305032a010c0504060f030519050601020f0a0308060a0e0421020a06060306090c0519060f090e090a 71
    0x90744200000d1105840302001c60381100d5043e50040d450140c42e1400036003080190f04140d401282019050034111744c0a40c1c0b030640038000d21480900c034502008110f40b004030034000c1130380000980c4000720140c01c0080100e092800a803a0900c0207003aa2303a12504560710000d006c1d21408180305207101c00f400ca4903030094222201310020302c0d03000d181d079403400d40701d019144902142d9035283c09a43c92403080c03c6022011b82844200070040d086003814003800580150141d000018a03103104103014a000748100c9020750107020301499020640c1440d41c0203040014032184c114041c411070036455400030042030810300d1198888815a02d17294040c411441855031140481400c2c0900f80004110181e0040368140340780640110410042141030340f80405d00c0c14000c04c030034030702400002407040580c005101c1521402103c1c0035950f8400c10407004400070918010085601c4a04100d064080c4000e5044803003d0b041c0b002c0240d5070fa584819101c001110300000e01c0e04a90f0b0700c001004600022900d59 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 144877922 1250 144876672 144876679
    0x1180824090613060903030b0306090f06010501090602120d060b07060506041b0807080402030f030a03050604050709030206180d060c08090c0301151701020c12041a070b13060905060a0b0a05 83
    0x140f034000624058804070020180400343d4468401050601c244c2085003494001b908440b80c5013170061081d59611009040001070f40594000407800b584200c05c1c0000300c0769140d00804200250910481a5038030507482403060a907901c0c1c0c0007480d419000003030090036015907030010f014a400c1c030900080e100c6002c40009844c01200010b02c2858000d450190441481e103444051590b892000c64580b000b0955a40320074400031580e480400c1d0b00d0380020344282002d440910803519020070030364044295010096010703c05000541600224851200a0520051008030058041d0701c4c2c00080710880c012180000d00c1c0c10b400c010701d10000708001e0384007117029002000440c05540c48101d24005034001e0700c00c04090720784143c0c80240309406680302d81c444002924188a900000c0d94082d52180c85121841c0c00403c0721080440752160071355060710b4204160110690b40c1502a03083c4480c9003000300c940e41da4030303800003001c5042007200c02d11170120824000b0342c0001c41001c1101c001e01c1980943d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 144879172 1250 144877922 144877933
    0x507050d081003060b040f02031501030605060910270e091603150c0c1b031718010818010501081b040b030a060509032118010b0d020118082409 63
    0x21080b0904607084076003050000901c1181c610000d0041c018001d045c0c11014000b20510000030310a0504168a090981701013103815601c2c3c092041c1c0f1b0203000a004c6e4030006201c0d1101225025002c0e02016030005038040e0000c0d01c0c1801080400341042e00103000c03c401407010030a40507002c012807403100c80405030640703811b881c50340c8030310620701c0702c91220304566110920342d030005000c0c0f500052226480030105038100d85c0c0074032582c6105142d00c026034039a41a02051018000130030200e5060f800740c0803909998000c180019500f03450040c4c420025484e0300821122400c0e420701c20107010740f14117030190407458180e640701c100e0383d02a041510300c151719080340140035a500052811a00ba44500040b07880d03541c910070642076010340003c100c4019854000011000c2d048070003030340b160b044e48600f5407210030107400c44c500701d03a0044c04464000111421803401356005007901e140c5486070799026400c0c0d603195030a00d4207102c89004036002141603d0040041c0142e4030200f583d114600b2001401c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 144880422 1250 144879172 144879181
    0x203040e0a1803050c03070b0108210c03070219030212070608071b020409141f0510150c0804150504090b0402091c11060406020c030f0f1f0b09070507050d08 69
    0x1101440c92482c001d091100c00140481c4da0384c1d00717006a6591503089041d980c01580d550070b081d503c45620b10541d0a00c40311000784074503039000c10720a0390007110485005604010f881e07424016005142114080248800240007005a603241d140068000707145024080d000d01d403440103040c0e004040c01c480107100300040d000402c0001d401404400940455021071503110300c0c00c00c1d0700c0e841292404413071207001d0794005600d4050750303151071401c580701c1250810481d41c0d0107800d00c010b0311050103a9183e440c0d5200012150034803504031150a54002d4580340c2c9003a036200303036122800c0742142c0504049000458100301006e4503100c0c484807014152420352410301c0744400900000c50648042c1407940001c07404206201240000042014001e00b00782d940310b40315840070303664004540e01240320340b0440803c01c0008001003070010040402c7d40050040c8070028421400d100300780c1807100010b80d5610b0405a0320365034501c03c28000e540c2c0c2c0e1a559a544d2440c105142403c44002c00c0c0300a001a000912 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 144881672 1250 144880422 144880451
    0x306041a09013801090614090a09090804080705041406130b060307110709020c0309120c03100f15051f02010b030109080c0f0d0804020409030509040501170f120d0e07080a030203040e0a 81
    0x15090344150091503503232242002e0014108400580000045910303108580c420482000002c0060312045401ca840081c0e41d4003c00003540c84c05420800c00d4130105d408107920703007000c0c00040c9003c0c514a0b404101440038001140c115002142c0c1c0a0005040b4050762296000c141b082c40040e00c0d6519081d454903100204982d600e2080300c417024042c103420360f2800a0000144040b81f01000b0003000d42e07600000064200c0042e10400f55071010b138900d0024035100b5007030310403214412a6801742c0314070102090240c1442c8610700441e0200c00b5075407204000a083d5600f841004507940c42a86040d0302e8440c002c4000c0c0c0b8040602e41079584d0359000c401e450982e40d4004e91074540c0143d04480101d030f02c007040c0c030f0304039001c0c020300d210aa0428103110021034016002040603040074900340413203200c0f04590ba4181e540c0d0044a8480980b20400c0080e040b00c01a260003200000c603000301251500e540d41c6110b2868030400d4602540180c00c042401e0112150040d07000b50401c0000006201304880d50704030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 144882922 1250 144881672 144881687
    0x1a0903060f04050f010f0b01031b140a09050406081c080106140d1b0c0318030201050304260a0201020307030b0a0303050a11210c0c0306041a090138010906 68
    0x18607201c0880ca001404201e0f0801082ca8543c0c03d440c000d000b6940d20b640d030b020240c8203181400713002c2403c04402640d9030007480c1c0c0c0c12244120580d28401180c02045400320a40e12900d0240c08219020402140c05d45a0740945401045080d00400b002c810408259010140652011081248840040101951000019074240072046904c4c2d80d40c400441080000d003000300050010511091001035003642148491541e24080d0b2078100355038029025414641d4901e01000340410014000f03d000715583c2d030441800740c402d6a030340f13402c01d0030701501b1000250003641d00240180e400004000780d441c1c4c0360040c070180070b8042e51038450340d904580d009440ea0080480c0f400800c1702980308961b4a02040014514804a01441c3d8050540c1c10401104030340c4080d0a5015074030508240100c507040014000d44100d8028014425021001c07507030071031100303003c1e0640d2169922401d50400c101c804003d030000e074030520300513500020703c5560050078551800d11054144103245200700000c9422629 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 144884172 1250 144882922 144882931
    0x140610051309053301080a0509190501060509100f05040606050313022b050601080304050a1502070503030f0705010b0d0209060d0f0b0106050408060906010b120a091b1a090306 77
    0x3008a15907440c03032020440c0e24545250905120304902c000c4100c0700074200b202500c0e04d0f003a698030300c0598070080c081095070801e41c0d442e00b00d0b0b817103000060460f020700f15218264520aa001140169642000810024017036502201d1290324000c100402c0068000c018010b000035601480102d1030304401401c180001441107400c442582c414a08559a40c9000c1d0170034603100440c0a58100c0c62074140440820342c08040b00c581c07090400100d014500042178604560380188111122802c090b1901c0205240da030001c001d61140f2400420b5545e41400507140c0312054038035054640405007800350030349205028150007901c80c18800360140e03d490104a07403100d0300f910028404121031400c2c4288140c11440a0a4159801c0000c54aa68400d00500c21510740700201e840d80d0f229042941c2e100d010038820000c00d140100301200e01d01c80b51040c2603070701c00e01c0002c00040019031a02c8201c0f01d14141c0c500c0380d42200748040241701c4400c184510030307038401e40410840e0811100502107039440c03c2c042c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 144885422 1250 144884172 144884189
    0x11505060d020d0e060105030d090807170f030a0c02210a06110906030a0509010b09010807030201200a051011040506070b0a0603021815090702060a1e1406100513 71
    0x48000494007103404a4084001c0c4100800002d4480500c20361580000c0c02814401c0c06003249540f15140f041140382d00f82d80e108000303031640c00c0c540001d01100c07138100c0700340c80b0310750040042c0e400091a0a2002e05646e010075200c220400041d1301c100040000c443e42204032102104042000790f0b00000b4030381c1e485039031280b030008144803540700004450041d11034032131f881b603000002c000070b030125900100d0180d04208000c0c40812000820400f9205003402440041c0d400124100003543c40350110340922841c4250814900c0040060310b41464482501900e240d809020200403c80451045904100310400010708003400e0100255091183c5e101c080e11074500e040208101c2d03c559031100008590080c42c0400c920800d1a00da0050101180c103003041e20b003c050300003614200383c21203d11500081d409410b1a0b65408243c900070110024074880750280e40344200e4900341c452040c1c80c1c1d007a00030f2194507030350310b8200c080040d0360b0150143e40c000c212007070003240d074406001c494820a80b060300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 144886672 1250 144885422 144885427
    0x20c03100c090927080408070303020a0c09020f0711060409090f1a01142103030106080a051003030e06030a090503032a092d06040b0406020d0212091c020904060507020d0201150506 79
    0x281482c1c001790040790800da03202d0040d9007000082540005410881521a0b4444841140c0c2c03030584034100d00900a800442c070104101004c001090046103480c00800200302c6810075032118000c500f2500c0000044840d03450800b021814400c0c3d048501001101e03201c102040c0391b05000c83c2d00341188400c0300d090b02410480241419205000000e003542a03000411aa140c1d030751327110001c0092074240c40c080c500754604808625013555500600068a4140d19880d0321250003200780310150303000804981e90307103591301c0310710000a0090005502949a0026240c2000d0100100601148510313402c0300f1114402c1040d94410348401c0c140130250b2400d00400d6160450003100310055400601d18141d205074001004600800001c02501c195000759089650010580b076050341e540e600310342c415050010512510700c4a150030714401c120110f000e1007804407c0c0c460b0b80882ca4001058400300e034107c0d102c9040111040c1d040008444158031032009008802200781c1000300c0804500500d40140f000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 144887922 1250 144886672 144886751
    0x20c060a09030b0708070f0302040602030412050a0204060305030912071203050c0316080d050604050f040615080f060a050718060305150d06050106020d050702030715020c03100c0909 80
    0x241c61000002d6810681e1030206241501c0001d281c2c0c1e400f201d202000c6222010135030f480e00d10034400d40d0300b501d0294005518280c00c01101030100038060600b11140d00c2018408030050302c0d1401030000541c494402107444044000030403003100031540d036649040e0b004032010080c0c4620404120b00c2550541452a62084408107007400d501c60784400004207020b020007001000b039080010011401c03525010002c1d80c5440702040207554003900e00c56050700008001c100461a03d80c0001d5041915859004806036107210709810315040512006040d0001001c11461a03014002d49901248030300d0182d0200c0c8000310040041c080a01408040694420000303c1c8800c3c44d600d4402d124000030103004540d082850120060902400b440005000d001108000382c0d0141c0c0549041c241c3c000c0c003902d40581032048140c080076007092034008501c10088034030300c161000e1003a003c0900140702d02113a10030440030080d00d03050385644559003e9213840b611208091000c007042444100d0707903060702d112242 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 144889172 1250 144887922 144887927
    0x405060306010c0c0824070f1d1003090501060501020a08030703020c07170a032d120621051c080f0403090b0a050406080108030a050f1c0207290601020c060a 69
    0xf98820001c000d9010800003003a18240001c003942520440268804101c41c804061100c107039007540c0c0e10380441c4080401d100c605000c1c50b1160074201d0000c24801d211050200010b401e81341140048020a680e03c175101e00b440000e005e0341e0301400d402c0c0000c2c84001c1d0703269501070103444001c20312400c15901003000004101e0601000c8024070f18a42007904003020405030b9a151485003d04038041078120181080c00140b1a072002c15004203211007501c007400d00c940669a520642004062840d55000c0100c3c100841e82d90440102c554100c0c81000d506142c640b080c900f00d880d8440c22800191051442c039400e40c8146130742e40c8603140c4040302040d92070328601076803800f070180c10543d0b13000c1000c2031141690741c1c064068012500c41d42d503a100d650740d8950f001030312482409400400120f0400070f030a549039900c0010404000030394200592080e00c0d1035186e04903000b03910b0807951030a00d60000748102500106000070041d1081c8404c44504041c00040c0d610084074488034010080855007a100f81d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 144890422 1250 144889172 144889187
    0x114130201110a02100c051005070e0108060f0919020912010b0a0905040b06040f0b03060a0c1407081803031c0b0a051c0303050603190507081504110906060d09061a030a08040506030601 81
    0xa2300030520490074040d4014004011500106001602d84000240c5070f01e480300130720102140103000e00c5032a03191160f10400b11403290b00c9409105400300500c40a41d21501a00061200c9180c00000e80c3d0501c05c0421015651759031016a06508240500021913000316205403c02030840c3c0015401e044452460050014400f01682c540100c2d01040302c4900180c1003801e1580407a83c82040f844864114104c880c06410400707000d51505004568609112042c074a40c0404028110f80c140194009245210030007a00f804c2805525410007240600b80004200d020b01001c030345201c4641c0189070f01c507000b40c581e6480a002c00d900e0303c0c0071512540b800d0107060f042c840f10814200c501c3c0c030b05060182c1d80310101d12840600d4803540c219000c414024200300d900841d030010721b01c02e1004030301d410808111009006282d01c03010130001e000807905e4a1040d150154460100441c2280703031280c0c0f6075003d012401c180c90103a0441d0075642c1c00039880e0011035040d100c00f21081c513201d80b26800101c43ca80d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 144891672 1250 144890422 144890443
    0x32a0316081b12060f0f090a08030a020703030e07060f090b032e050a0b1e0306060a0f05040905041506140a05130e0f0f100b010816020114130201110a02100c05 70
    0x740950340a0100fa003840003417940c07048500c43d00910860300c50301842540c507942d000025203800020301c041000300c00a90010480540030780340c01b00300c10049060141c140f2003164851030220301d903d010a56500e0b000154000203201c0740c941c5900b18505076240405100700c0910b00080b07501c0101070b01454101c03000d2803801620700503141c0200180c91303041c1e200c10340e44400140040580000c50a42a02c551a0112842070350080c2020307003001d91300b0000ba41d205010103a04030a0001c2402b000c10441c000384201c0380320b2030280c220000d60300c441b20303045030841b039040d002100180c0d4010902d404d02d8564807941400c42d0b001b90350b00e40c400c001413202c20000b0101030081c40480d02601e040c040000f08006854565900c0e0941514180c54046040f4070482c0d8010361440d02245000002031840141c0740b0704000b82a00d80c1c0008640c003080d1391202c0d00300700012039002d81d1091551801000b0765a000031400f1000070000700811003640c0c9600012035540c80304000e6420000d00b40303000c00410005004500c542c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 144892922 1250 144891672 144891709
    0xb03160b13090c030212011203090509040c180605040b0102060c031f15080601080a02190305130b010e0709080708030409021b100501231509032a0316081b 68
    0x581e0340001e0f00501079844080c2e40d14001d807080c0c0001c6003800340210036244041d031540340c8280e594944401d000449100030020340f81502a1100020240c0100300303128101e25110f01c00103440b90414007000101c1da4211001411903004808020344002140704503030f0450131b0355650260940c002c0c2143c1490308a160040d4030b4040172031903030062098100d601d50713005403001d80b2244000d82c1d03090a410200e0080d0b10089101129134031010400c14040c0d48451341180b01402ca0700c0d030090b1103840d0b6000300d0100ba4450302c90600c8680800c02c000303500090701c0d00500510300203014414a883c01c9160740b030042d400f0f0507803019400142030400303008680700c21700201d10a00c03d444c0070b0541b440140c40100000d100f25045201c8180d52005032300050b01500403450380c000c0c0010040c040c0344407082c056400c0031002c0c6416102d501e04081a100c80d40c0701c100208108021517000d07280d42c040505040603550980070b040d44c03c0c0380310203200e035600120b8039058031085c14100000883c0101e00050018181d07003800e111 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 144894172 1250 144892922 144892931
    0x3010902030f06220c03020d0f0f050a020103060515030412170108010b0a050117040308040809041a03011b0c0b0703020d050702030d06050303040609030312090804180b03160b1309 79
    0x341a102060541c841c100e038190102a00b2280c50050844c0411801c005242c0c490a5000f031005280c1a014002507500803181c041c003041103995401d6842a1001c82944c8980c06a8664021581d0500640340076120a840c415009103041e0b80b885024040030b04020304094034482c1a4160ba03210b0b4501e440001030f4000c1d414a01d503901d1078020300030810f940c0d0b600c0c0110500b0700041219401180d825607405012051380320030355602e89007103480d407201030012600c4910030090121942e0310350241e1648406d2a01000842c1d001c000c0c04c050844902400d040300c04105907510000040d084000142d1507604800400c203a5a60040124003c1c031404100c15103c81c9070030140310200340d001003c2c00c4034080c1b502e07003001141d0b03d40c010035580707009610842e070000d1403c55007800024070496814900700410000071588404a40d2548105c1d00903400c4181000c400182c040d041ca4586d0041140840095000d480c1800044003d9420b02c0c1c0786000702610303000009060020180d41804400c010200b0320700821 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 144895422 1250 144894172 144894193
    0xa050d0e0f0a080c010509061b090a031202101401030f0b0703110d09020f1e010c03170903070b0f0105090a0c170903040f0902270a030c0b13060c0209060405060301090203 75
    0x540981113801d001509620700000100007000024880707001d5641003403000c400e00b6200b40e50030310315402180840d40192905500000051500c070068440600f00d80140c0001507414945400300e034420241e0403181c0c03400c0300041010481040b030212905e40c004280740c00940d12060268094070103c0c1e9441200036000484009807800303680000611031003141d00a10b40d511070001c20024131110b1401702108890040180c0c000e6009002d010b540c00d10a00303000014950f55a0201103081c4226610910380d00700080142c02c020700e917900b042e40101e03003400c888a99410080451104040106180307004e42da80c2c034000015500840d00740302c40f140034003118845440e081d51055201d80040c0300f031001120350042e021505051170b0007961080b55500100c00196420a02015000382100340e20a802a03040c000201c045140480b07103602030490450603d59800340810001d9180c1d945902030020410010001c13001030b600c1203000d0390080c5049a000c18a40c90355400070380140001a4020340c10b115600895 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 144896672 1250 144895422 144895433
    0xf0304060b0103060902090f04180206070b16050f0d091505100501020105150f0f0a1502010608120405011205060a08010204171605010c031d0402030c0705010506060a050d0e0f0a 78
    0x7400d6000e0780c0a1100582c2d5004d66802e074082c3c040242e5010000394841c425504140d40141c921803540c408035807540741c072900415819072000c6001c1c3d0301503012800b004151094400100300344000c51501910307140821511391070902500c00a0040c854a56054200b800510301a22841c605c40c00010042418114501124040702d0701c00e42d80954280400503941608580c2c0c069120200070303210a9042403400c0400014211030800b49900000070480030410480c1403086180d40760041d000020600c0c200b01c5961301d0000345000203054800100000e100b580d03440621102e980303040c0703400400c003921010002949112140c01894942d8400324000428124242d00021a81e04000965070704107000e00c900e035001c0c5014003903240401c103031040c0030340024410900300003544030321100038240182410008017680e00580c0c81881e41580466040240002032040c1d03138001d1030864089107041010403000c1c20714000c00307800b00c2c4115a0b1b45904182041e06000c05042c0d18980d009403000000b040c60308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 144897922 1250 144896672 144896681
    0xb1317100b0f030c010c0203030c010c09030b062b15020309030a120606020601170f060112020405240f030f0a06140c030402011d0316030605011a0418110f030406 71
    0x41124641400700e0000d003800c0400548071002c502501504074540c40c0c10055034209001c0308101e80622013000056441c401c00c0c45a1040c0026036922032603410314500780a03403031803800740c00342d445a100341800e010b00f6400c400c0500e400007940792000b4004801424209103541d10400c1911400c0d000004005003103030040010804100646c0b07401010420b900004400c89000d4003d00d40035920000040c0440d070f10a21114000341400300440c3c26400040d00e030141484400c0e440341101820702901d28046107014060240d200d0b8812103481c051548402e140c0c100b0009054019005150b400c0e152840c50b00c041c020481c13402801812070708aa1000e2070320900070142c031281d94500a15110210b06c1c2c480d50007080b01d01980c4c05130340e1141050103201c00d19010101102140741e0504ca0b03840c16014449141c0e0b038150056010b48400107036589444803501e104071300f070034417140d1118007000103202000b02c0381000c014001548500044804042c051070300c45202d407041154640c4400f10410042001c990070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 144899172 1250 144897922 144897943
    0x102090319020a05060306060f0712140a1706030f0105090a02010f02070f05220507210605031005180a0c08011505061206030c060d0b090105030f03040b1317 69
    0x40700c8146810748603080142620030710007944011030740000c00c101d01e41403000d176410140c02040c240c54000801400144d41c8d1040404032481d40c08059411905a0048001c541075007504000d01e19014040400401a041030913288108503c900702003240358900f0400c410346401c801000304000d040c01c00c02160b40d88080041240001e050b107501c0142e485c8003103944002c8848043c0b407140302906007010416040c1d01d103455145060301da40c018101400440c002c0900030a51505c070310f0041a02e1201081c2d01c942c0304801d400c005424410308000546000410210b0040380042c0080c3c99114444c1040b050440000d00030294401c41e0901002e10011000900c21100342c40c008002803c00c0410140350fa00551007021340c000e41c244901c20124544031b2660794400001410b8500d03902c11040002d21982101e40700c10012503558940e22018245094044d02504044004088000302c0c040b0055070b910031401440616070000c100582904281c0500801030024900507c01c0c01034080f50490781d078401102c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 144900422 1250 144899172 144899179
    0x501050f01050c070e0a020d0c05130e0c0906030a02040305150a14010614070c0509130501050c041505160804030609061d0304140604090501030605040210020c0102030403060902061b010209 83
    0x22040c0c40158001e000725034450074802c0141c0b00b9a450002141162070000b048110590340030008915801c03041d12079003031a8040f130f446042c1c6440441e14207c90383c1c541c07a005103506901c02414844100284425100b44a10850340c455403503813900c40c400081c3c012640014202e2054103290580594555207040c4a0980c6101c01c22410f4000000031524117000c1c40340d84080f8007181c99005880e04040c00820350307070b40255060782920b80d50705c4c0460750b00e24044031100d080c102c90300303840c40070442c0078040c0c90703007000d000000b490910b401d005200c02580aa442d0fa0030501400042419094501500302000c00b90400540350b16680e49090010146c070500c1d00c1103501e070745040c02801044003000082506132030100000c504050400b054181000704619002c0d074020b4051000003842401030103811701a522a510204031401d1178410b020710384945110391015500075806055140c1d030b000094408407600404040341c0405c4a00200c0c1140c81030091304030500706000c1101055000540003040c8a40054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 144901672 1250 144900422 144900439
    0x906010608090a170c150a05010f0801050f06010c0c03061107020a080105100504020309030909040c030506090303010605250212010504030e01020d0203040e0a1b0905010e040b220e10050105 83
    0x8124a03450b80ea40c003a0050425000d001d08000341100c0401a000c02c420031001c8800c1e40f4041b0032412041901190f80d078850b952200014030101c150b41881000808114000340524149940c00c201841e000400d82070411880c04c03914010312000d580400000c0d45c11440402c1030525014040034140e10101060f4000c0829040014019105200c4d41c1d04c030700343c20003414050368181810440a075102408164076840140245134650743c0380300340e840c084d520031801e041440d80f842c0303400c1c0e05010009042881a40050004204041d00081100c6a00c59405108001c0040c0036a82010640c031915003e500034040c40340282c9142e0301540401e000c0c40c0651035081c030395043d8400490743c8506250483c00142c0040c0001c109041038240301e150041004100403403520a2400c4c09081450301032046c200160728441c00704a0355801c0000a10842016201404003a00300800f05540710020061042d1400000c0300300c509031891544101a15418a8141d415030490701c02e80001034003082c09001d02c40e9144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 144902922 1250 144901672 144901681
    0xf040b060a08060601030b040e010c0c06060e010605031801090f082101120209040c1a070314040b0910210603031b0b13050c0307060504060f14180d02090906010608 72
    0x71000c58084580d00c000401e41e0766107010046020b0f003c4402d6560b0826101c04da841d00700030083c02800f10454060b99900c400e41c483e8104141980c039690b0005400291407401404201e6010f01226808000910300c480c5a000c03162045004011402c0042c100c408803502ca00101701c0d00e10010300d1f46080100c542c0324102d00980e4446003055003881102e42c40c3c142ea20050005060100036150301c68061240c03a0400766a415a60fa410075010b90301010140307001500d0400c154212001945910400c0b00403801e290800307046400f54401c400c5018410b0800100031150f8038400c03034409240e0040c81c1303441c40d01507402c500b80c200685010300044000c20007a01c00e082580c2ea844071802c181c00d82244200d501621518a074600c1d07a500c1b001e017078869029601034500c841c0c42c00c100c00c1005014030b81d54155217a20f000c400404988641699404100d40074905002c400e0b07048055170001001c1ea1024a01c2a410a0010750707200c980841c025048142007040141c0c428000c01e540d812101291101c1c00c40d5500c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 144904172 1250 144902922 144902929
    0x601051c0812190e030d091112010c0206010f08100207260c0c060306210a170345032802011d0d0302091507050a0309080d02060118090b0f040b06 64
    0x4c071032a02c41d01e17402807000d2901e610503500003041050080003018102c411080206556038034210081e00140e44a0741e10360201d50381088030b680145030805442c521141008204c0c1d0b1180c0c2400ca14002c0d00360049290010300c07010190300c1c3c081005120002404814903031031400c03207800c01d1503958118000d0700740d02e600b10305062040385d11440000304161a06c0c900c1000c2400180582c0f135890340c5c68821400f000303001418074290050b101068034000341d12840c200c44803040c1e150503642d0451030103c1e000b0915086003213901d030f0302c82c000d0308c10401c440c5103000001d83d10f4658081c083c902102c103488002c103803545001601449081c01c19590003444110070343d210700b078003140071210211401c2d8040c1c0403010310b44d4425400340020040c001c1c44400801600030880605401c1004159100e03080f03120540c04054020b82028001d0413410090243e801000c24081d4454005108103030821000c1d205000c0440002e0340800701059000c1d80b81c127024101108004c11414048a0488000e074035040812014075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 144905422 1250 144904172 144904181
    0x10306081518010b0310020304020913230c03190516061d03070e09010e0607020c180c0c030a02031801030605101803050d0c110f030601051c081219 65
    0x100382001040c89440da803207401e40c0d80c8422902c03841d040d541c900c00121250ba050203602050000d00c0e60168407030030a0700410143c1c0902800c0b60400303074104000d610024003c5104072804182d0650384074040441e00f0b006a09223807030706a0035941801404104110320a5455036543c0490094040b641084200c13030300d00000e603502e406203c02042040c04012070030b4442001c85044444050240c6020355034400500320000f80586126200340d465001400008204000e00c55012041e031009000030602440460450030782c0e07902741c0122412290000310040d9480048421000341031040700e50720748406400a45030703005204c0d02540d40c5540340340c20391a0740c0709000d4001a04c0000f0035500140d00c0c0c200041d0b801461004010401d090030150010210354140180313081d021050716000101e0100d850689024a16100014030529000d1a4a1036a4400090244c1511000d50b850000340c50030700c4000201d40035a0350018800c0f01c000030851415000080107600070042c481881107504000d108803c16203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 144906672 1250 144905422 144905443
    0x50a080105100c0b0907080d091503090c050d0c050d0305070507060906020706030b0f030a0c18140c0c150901150608040b0c0a090b030c04050f090106080c0a05040510080601030608 79
    0x19100183d520041849903c01c1074001c00840211407003250703104841424a0410710211002c1002000c04110800c1142001c3c4176000703007850100300300c8807a0f60300e040305240749014140c0190541c0440c0c4041020304040701740940002402080f100103145001402c2d9400401d003241d246c02141000614a80034291580c01c0d42c06c5078015200c3d1900b414400c42c000c14244e428164000028554140aa201030209445060150070314400e408c1c14110305045110090b410076181c280f403c02040404821008150b801555080802d503030750910310121803410300000d16042c0e000301c458041c085140d02c1540a402804c0c0c0300e000800d01142c0e80c3c0310070390302c00e841202c2c06420002128001000c644541c8000d0001c8802030902488007515100e40e060690000c540c800c0c01590009420300403440c1c15000c01c00e8a0101302d503020340360341c10b00000400d043c1c0c001c1c1c44440c44076404691171803094042d0085d02d000c0c101c0949404034030380c52030740c0080107500140c3e030141c00300389400c90103d440c03680400e21880c003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 144907922 1250 144906672 144906677
    0x140f01170403030203150d120201051501020712020604180203010302091e16200c090105061e030402041e0b040f0615050f070b180d02030a09050603100510050a08010510 74
    0x3035900d98800340c000e5800101000c03c111000b40210a2903500c1c070301c2c6000100e00a09400d499900d11a00207400c42e04090704180541c02c4c0072105110716a4001200800d450040343c1c0120f00c0107051010412074001d0350811240d25400c2d0195070402c0b1150340c00755048034003c9408108648a0600c010f90031900203042040030b0b21100c00140007444920404400508a0300d8009400061001c220032100100200d600701608964540c0c807903460500c40040c05042c04552030741c5043c4603440c5421200c401c2442d4514080f5011001505643e500d41c4404102125003054240c0e5903030302214003009013550b00d1014070584c900000f101000e80d1911414081d200b040618403594000d58905907100d404c003011143c0048000c100030800100c158074000e004051601c100d00c241501c0c0d04074181004403840348c10007107500910025000d2680000c96100f203c0050f03490b01c0d903d4076580384070005900c2c190000b1b600b121400d01c00d61201f03a4440d00401950b0aaa91401c2460344ca600401c0820b64403da2400300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 144909172 1250 144907922 144907967
    0x612050c0109060e06211009050906070f0f050706020d02071a0103050c01110109020612070f140409050703090b10090609020403120f1106010807051002010507090b0c0313140f01 78
    0x10300d04100006110841c0c000b203c01000350382095a0681d024002c40d1f00804140c010942001402c001d409944d80000d4503101801c03251411020013840f2400c180d4040007000070088101800700e0007030302240d04150300580c09641c0d4003541c0307000724060352020408030360840b12420540700801c4150035550503640d004000c0c11030241c00c5401140d403080306042201d915543c03203101c4001039851300018900395441a03850200c9203031030f09025140b9900203066509010030750703001026000c640c0c03003220191101440c001030280c44101d07080300103103021680240f1691811051140401c01080307031004544540d41c0a01903541c0319600c2c0816406a841300500b001c804a04a24129014041c07403005060729203403540060040103000c52401c0d80aa101415541201009005d030382000f10002115040342d0000b8006030a00910040c01e22000b40710b911403840011400010342141481202c00716012410901000c544498101e818206403100ea28402e552032030301c2c40060750044846810003228400c6180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 144910422 1250 144909172 144909197
    0xe0717060f03070b0c070b0403060b0a0b0a05030406052206051503070503060a0906020c070603020414010516020f0415090209040606020a170306040b100f030b01031104031b08010612050c010906 85
    0x194213401941c1280d4480c01002c8000c2000900c04c0040e100443c014ac60104500c1d0020050085030034142d0011150548100140700780190404100da820a038452400100c90741d58256a1000103001111001100b4080100d00188812a000f050280300c50306075442d0030366070310010035a54901c41c6c41140c1e0160413600c000b03200689154048101c032030103080f02510700704216101c0742c1400650341101c400300341c0c0880d00740406000c580002500c5102820f1480c07070165038000550221400490007442003681044614968456070041581074046400100b4000d4032003110340080d40111400e0b50280b8640000010382602c0003481d01c80356170700319040b030301c489140c00150010350b0300041c034094215071601402d0055031a10100e00d500020190f441e8030100b40801001070603151604440c5040504103960708070343c04606c508540849a1100400ca601c101907080c200c4001e005900c08003c80d4030b044030010760304000052020703015101c0c1c0b05455241c50b0b000019500001c007401900e000841740b40911 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 144911672 1250 144910422 144910439
    0x7080d060608090a061802030a03080a111303111207120302060f04030504050d0c050a0b071a0103171606090f0b0a060b0a03180609061a0d150c090e0717060f0307 71
    0x280b5480d0380b81c0129420701c0701d054010030b1525427400c10450028100c0810444a65020310030b517003003c412840b60071300d40f2216904000c201300103401302410f0301018400040c1c050b07880002c0041e0400b520b109440c40c1365980d0744041d643c1400350000350050700070500050000c080250110b4403441d0f142c1c60b0076040c9030501003400340998441d10211611306524001048540d81c018040f00140301e4a5559540e8510a280520380c44030303401007c10348510120014000900300a00042d8000d08106000d51030f00c5506100250003044041d000e4030581c544180700040c0503000010707101d514022002024030351211081402121714034030410446001c01e07c90300000034402d40190300c81c0c00340e80e61202240c1071a42c03915800c0321603490040703070401e550f2031003c07030182561810114041e000719100d401841c0b2a441e0084055044820310308116542c0c1d441d034075001c4c010b00170b100c05440039a080c0d0f101407400c0800a8120f0b0001240781d500304031100c00040c202d182048101c5650440a00030300021840d00204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 144912922 1250 144911672 144911681
    0xb1b030f01120812010803041406090108010947120604021011030c01150b0705030403060e072d050d080910030204090905160501090f120501090807080d060608090a06 73
    0x450f80c100d01000300444800b003a2000fa40613040d044d0145944e1450038208800c0d5070281c0c0b40c0c0c14010807082c00104c0d020383e0008c00c51811201506004a90700c15094410841c42c0781030050314520036418a0900e007203120280c000c9030804000b10031800c424203450b04111034001003040702a11640004000380050601e140d4074080d8400e281030800384d040480348211b0450b082403104990380d82d50307004e102c031032400340800400c0140210165146406480d44501d03460b82301d2804040c3c0042d449010200c540641009900005c03c0030030308410000106c5860404503510074400307110111103103a008161460213580c0c814101e9400001a4605440324040c4003800075007010020500d80d00340400503081e82103000b2202080d1040000d40344c41030b1001c8180d100d5141903008a410801c0c0084140301c809003c0e0888825105200072043e84554686840390241400180041061502148101c20420240042d10462401100c2803100b50707200da5044440f04800c9410040e030740c0c414010f19004c50b60b81d80c803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 144914172 1250 144912922 144912959
    0xb0301090b0d0204060312180617090703020a15090812190306030c080f0f0601080a020111070306150305010c03050c18030111071a07020d05070201080910090b1b030f01 74
    0x8200d486100703500040c04451a40c6e0050347d1440140c4a003a0807142d0184a0784030781491046401101d5003407020040c401d0018100300800042002d0101d0b031480010400e80d002150300405112a15440c0c3c4121b603060700799070781000c0100c0e8000a02003405640440c455805810480ca13450400b00e001880803445110b803855102070694421010000c1640070a224000d89655002042c507030055042241ca800d0b5020501c1c4c216810140061064500101b01c481c201602443c0420304c01c20350310400c600380ba005520082200d1720704080351141d102250700d1300089a018030000c11650403a0b02007641a00d40c210740c4002d00030710800c034a15a072021014079031080c080203030002075840c0907441c480d4002d500c0342c0c100307447d031070400150681d1040c42000801e5201016101601c52130600d0100a4450301031010002c2c1400842800240703c0039041241580040f641581485203503007508002c0a1440c09407000d01410748070b1201e90107840300c4a422a8064504e50600c409035a00c2c01420620700f66030100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 144915422 1250 144914172 144914179
    0x120f0c0a0902120c220303031a090906070f090f090b010914090a0e0f010501030f0b06031f0504031704060e16050a18110d020306010215040206070b1b0a0201020c0709060b0301090b 79
    0x91503a81704841030344051446910006031060200c0c55803450101150880c038400c044042c1004194540070440a421031190700b40001e02c145494000d52342d6107017035048503402d00403c0000040000c002e402200030501c01f030329030b140c20036190400311003240c003034007042904070400b0400b044100b2029030280c8000e22001003aa006086070121135804d643c0d00303900076143c1100d484e42c201c0900c84a0034556801000490041175007400050491144001040380703a0342040d99503000030181030094004c141d00084490031b8520038646458070f2030003043c1c64060742c1c6051040078801c0940221403d000c50640f4001003498070018074098002880b030035602c07054443d103601c0d96203405000006a02424900079400c501503202d2400c60b000914215511120704001c140e1030b02800003507100c4004a500d0303241c0050780d06166645010341c680360041c1c03594154204103c0000c0f500c000c180e040d800340403080424004e0b11541e558a0000d00b054910303602849002c0103003080100100300079580201132100c4040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 144916672 1250 144915422 144915457
    0x170403020115030308041a0912090f090f070906090501120905030403060903050304140303010b030f0703060305030c010609050c07050c010f0306090212180a050607030b120f0c0a0902120c 82
    0x2c46003810031040c0d403003140410300c0c44051204020000c022009640d203095154200d5103811881d1a9888030010302c40c60f800c0800081004842d00ca200100f076042d00b02600f01c082c0c07410825100f103102c500840c0c2000c0061300e400c4010550130f104213039600895205075603101485010884e60401480511000c0710365210030840040090034600440c41d005000751079043d101e01e02070410107134100302c10549080b0740d04108010700c5404522816660810300d40c1501c0002551100000d80007040c454001038103034400424030394034100e015003111007900c90382da034280455100c0c1c0328203940500a0883c028020f800801c5005c45a5206600d20400d0300c105140c040361007550f0b131400101302c0c0d0282d000903282d0b03604101000040800a03035001e01c101283c2c8001d0001080545071140c032010007030041c03401c00d62505069002503580c17180c190300c5040400f06481101f007001c1d00081c1e8442171007840c94000c11042400003106482403003a100708025030800d074151a0b0350380c880c1c81c01d50750005042c1c04103140b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 144917922 1250 144916672 144916691
    0x13020408070e100b1c020c03090a08010b040c02070503060406020309070f0609030308090d0e060313050118110312070602030601120903030f050c09060d02160f05070e0f01061704030201 81
    0x4026071401814111036000035410310b500211045141c0341c000c500040c0c0c0820040b96890009212800440c404240068540103501078003421441141440d951203118144041400003040d4002c04c40c08a04880c100071f054580c41059803100f0103445856410f820046c00100840d81e81d400960303001202c101554020750310f9540100070302003c1d030400000202301e450244105a0482c3c04280c010902000401003011040001030000310b41c100404d0203000044085140300f50400b0001700226441002488000480c034401c0d001e804242c07105460b50a01c0300510821400c0128010707500b0010031011034542020340d00c030b4030040d600c0542070f00d0411030003000e031002c410801d10940d41290320968020a540c500d400d104e43c00c0c0c4801608101c10701c941000504102c0d82da0f00c0480f18225464480544c80e0505000c80445145060102400441e10b46041808111380842c03188242d03400795420582c01c0d1141e02d40070744214024040c8002041d00803a5040040034400847c5500a22078400030440440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 144919172 1250 144917922 144917939
    0x60c0f07061202091315050409110f0604060813020a0f09050a0608010209010906081003060203040c0f0b030c27040c0e010914030d0f030902041e0e0a0b06130204 71
    0x800041808550094002800003551005001000c00d091050644c01d1845190000d0f400910f82d09040400c00d9aa41d81c1c00a0120700c04068001810024802c01c0b2640035800c02040c98030481440e54030400d1000c01920749894008151001e40d4603d03034801c41b4940d1100301c5441e4554076420140c2e402020344c8030000300a96030a69000203048140320200705814525100000e441e0550010704560340144103480860741c1c0a04501d0880b9074a04d8800869102d00440c201d4109181e0009483e0307500000411040c0100d9038650403c980401c0d074100030300382d502c01e508a403d0000307440700803102c081044004011004e00c03182d9119480140215012058614001021070715000ca40c400468000a030a00c480e41e003080300342d0001d001540f0340ca0b400b642c0041c00261203c030101400001d200c2d4526810b10128882e91113a0815503001d441003000103130240141d000101c4d61008003102c04e04048101881c01408140049440e0744035202d05900e41380d4104000e9080984080424202ea081c00001500c0a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 144920422 1250 144919172 144919183
    0x60106080a0f0504030f021009030e0112060b04170d0203160206280306090c181e08071e0b0c150903091e0a05060a0f210f0614030d0c060b060c 63
    0x602c00e8940701e50303a88206c03901a003131042c000f401c640304914050600011a0308900c0e00c101003c42403a186101070640d4204000901568005180099011a0114a8400032100706002034982c80480d44542d0340c0d003d040303980784955824000c5118140d042403005003004c0c0c020389210803017803944207402252103103800d248001002c00040000c0c0c035110704001984c1e4038422175a80c0705042c60428001c00d0520001c0d06619a144550396403200000f07034140740214081200d4014081000130740c1d40c0e0559400d00000600c492694001c0710030710b60313000000c620f8101d1080710b46040f05040070b0a003040b001860000c5006004003422124001040b0300070a40da5814030002440c152150007900d4610403d080c00903d42c4c00360000f9000329070400c9400d6501d41c02c180180034003540c0707240c001c2401000e51004c0302e5210f0454403030004142060b803141d107161029000722060303a102007030720003048000b04101551140310360500c02c00b1840c04e81c161004117949400104040c4400340120317181c803c5070031603545040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 144921672 1250 144920422 144920431
    0xf010f030f14030a0918060617100b07050f07050402161709182a07062304060c021b060a14070503040e01060f17070f020708030f0d1409060106080a0f05 67
    0x803044141071110000303200d0302c060170386e280100030800c19081240107804201c110f029034005c141104c5c0045c05280380310b804580541010411591614982d1918035504c00064030420b0050041d400007056500341482513481036042c0000d0a42c58081607101c20500440a11880042c0441000201102c1d03c0304c003840f01002c0007600d030350392141c40d1844c00030f804000708507190441d500d11a019128000c202000b80c23848a0303044100000c1c4901015000d03460071039030f04a681a54912981080305106041d481580c040075030383c00b90303a0500b90107084c1013036543c90400d4a55104a082c41052152403284851b1089140420001031508004d138a40c60328541065000040c2c0c599103000500049510042c486056480e50520025031008081007004c40c1c04010420000c0200380c170201103140340300308001c40c02004550143c940d2015140d0181200c1d5000f0241c50042e6070810259070542000b2880c0749110325000c0c409082d6070303402c100c012034050398003802c500401d42d15441d0700b482d4002c0b10310130b46024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 144922922 1250 144921672 144921677
    0xe01050903040602010e0102041d07020c0d080307030510030213020f07050a0c1e0b030a0506030a0b04030e0109060203070503030601030c1809090b011e03080c0f071701050f010f030f14030a 83
    0x210b41c034040001382512011011000c081c0d0043c001005500e143c460310040d803040d820340c04d51044d07444600032032401c5401c030440c40c4e008403409085030600215000a50203280d0943d01030081d60b1b1680c0040c0c147c101c95100c0250000012101e820b08840303698081c1c0703400344444105c0e41c5450300341d42f5120301c0c01d06009419140c0d10074001003000929514070340c1d85a04140760182110071840c040d80b844041c000100b240c2241501c8000041c1682c0d410721036a11a10350289041425082c03504000700300148081130280030500401300861300a00000a40e0501a8480d0007113195940d03d03401103020f403043d04106410701103058605100364640b4607940001e005218030009044042c1d0801e88859401a409940c240002401e640d0158009005000a80b40c220804036a26554090310601d00810b80c124224580140e020200b60070400781200580c1c2000c900003800103440705228002e02030000e00c0ba40b140344005030002c20007d148202030401c458003401e1116050803240148a0a5034444000e1000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 144924172 1250 144922922 144922927
    0x60103150b0d05130f171c0b090702010b0a050f0a03171806070b0a1a03070b0301080f0303010806070c080409050c0720031207080c251e030f05010e01050903 69
    0x428000c80c85503030f40c0100808245040f4a55a4a03082071544454001030900307142c400000355003443c0d4001f02c9003070300890384203528092803c8291000400320100d00910403281ca801150609205014040c0e00040062210494600d80010483c0420400320b4440c0c010304850000808140c0020b40c07007c11302e01c00b2400036600c804490b0449032940004214a01c03450090243c10040b4019a031100e6110004039800158640074079110350000307514a40465051050039804105400c02c0b602030b504841c0000d00f1102076491007481e01c5c0e1203010034042c141c0290300c600e0004000c54410034020440c18000c0c281c1c0e5207020b4031080c0c5501034410885040480503070004504081280020104ca5075095441c13606105220400004e5142ca1103410b14a0407884c0100c1c2d00c40c00e0105280480d01c0c04c0c000c0c581141c1c40101903034038540304454a61010300300c0c40c81c100c3c4002000110700282444003428035448001e441d0955a442c0c0c01000716440949680d940d588448070505800d00c1554001c0001000568 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 144925422 1250 144924172 144924187
    0x90f150304030f02071e03080306011808010e12030402060f0a03090602120405060f09061b0d060306060608090604020307060503150d03050301051e061812030d060e0a09030c0b060103150b 82
    0xe1170074a041d40f0200628005144814001d8801040d06082e240e1040d20643e480c0c4503500104d5550700521400d402c0040c1e01071000982e094158480b0032500c00c1a02901c0914501c524414824041250b0194000d0402c210310407151071000014014030364a03040020f40c01e8900d843e0380c3c1c1240c00500c0c0c42d208010032101400244141000b005900c001d4142c9520182d1800004058a82e60090080c06c00c5403043d1071400e84061007842500ca56000070501040b016a481c200355016080074403a0030042020480801c030006030200f009480780d42c002c0d00401c000c030700c0c00c0b20803a034650004040c140e2003a80381c0d042d404181d40f60242250624042da40d0680c6075410601000301041f04500550142c2e01090508042c40d2509820780b0048250604200d09aa0103c008500b100c14001c08810f11804006403812403030440303a1224041d92604006858207070345a00d1010111080e4110290100301200c1030200000d0080703008a51004d411b2601080344510032000b070b0480042c50304204816030012032401e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 144926672 1250 144925422 144925427
    0x403020a15020909161d0102030c0f01020307180e040b04020402040803160204050705160b06030f06010f1a0a0219050102041203020a0209070813061a090109020d051605090f150304030f 81
    0x1250400b01a000301108a0078406001e880c006c4890248020480040f40c2c0041c1e0361300038401e946001060b00e00781c0d5030030300c2d001d9000d500039401240d0751004941e080440b0b101c2a002c0d02004000d441c8203035000103898541c2d8a0310080035100071b0040741d000d6000c00003c0385958090024041591404103142118012441040103848005100008022042c4104040c0196440e86103c1e1b00780c000f02016016100c40022906001c400001341d5040d1184800005840c44505d61903c21180607003046400404080d2040035548100742c406030040c0c4c00390401a003c09000e50701150b059101e80f00051400b941d50b00c903408500c158900580c0960400d400407415410000c59540e800502803501d4200d5250400c24000e5501c51a0341c041c0140350350f0301860901d03005001d5500300c1508010190803140d0b0b5210a481c01944c0442e0b035800d186410f020104003c0500f4204010106180d45c654070700b401c0780c4c20207000c0081441c1ea49a9440407400503003540250b205402103000b0350017507456000411001401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 144927922 1250 144926672 144926689
    0x70602091507060c0207090b0a030303020304050a05160806070c080a030209030a0b0109061e060f0f1101050c09040c08070210020a0c06050720030414010f17100f0f051005030403020a150209 83
    0x40103400e0048c1403a440d5104100301d02a01c0c4d06080061702e03511241045071400c030301040020300520400d000150040811503410044420540c03c0b51407554600b681292001d0754500000c2000b1411300918a0b600c2c029000f400140341c0140480d01001400d072540490b20f00c0c281e121040e01559410305000070801507146202111601581e08682490540c0090460085034804410043e45a900e4241e540c2700e403003444a46803144000344568200b0421004041e40040101c40c402d910307041d41804498001d0072100d1183c5556006003410030904510040a036100c24110300401c403d91000030001117240c0b103100e003c0ca240c1c0e61040c030140c8104000c1060220581120012980140010840d1169450310030100e03503000c1ca400c00d08a0180a0251109810034010380442d40600c0c080000301d000a100f10b9040b074604a40c903240c081d5481c812006148083d0041030780141511000301400f5000f18011900680b0a104455100038251107040a090204445600103900014502603516050f1031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 144929172 1250 144927922 144927929
    0x6030f0c021b01080c0409020d0609180203070521100e07050d0c06050d020702030a0b0403090f0803040b0c190f050d080105090f090304150c02120c06070602091507060c0207 76
    0x700301402055002c40301549000c0c0d2514100314082000854211400c800c1e6401000c4c190010f41d20307507401b811200060b00003401000c0c0050319040e0507600c509004d036106480c0d10f802901404065040c08180101020110701140403000d60b5124194640010410798140f01c2c1c42400000710341d2840003907a0700b401425401644191022005400416900c3d03410008444150400341d694400d000c403031002900031068042d41c903004044401c41840081d40460303104a102c0c0e80e900c03c107036407222011018100d07070b80a038011b1070f8800d001c140300d980c086800800044604c0c0d02191401110480c0e062054049000d04449154542c0e84d00000c00c1000c00c180d81228031a41000c856540c1050003081c001c0c1c00080400300a00c90342004603120340c2060040f01c0290251261081c807180d8200d8000e020f0000c2114128002c03400c10341c6140202d40040707043d50a4074401030409141000702d80302d0300e020f50070250320b40e03500c80c90160803401040304c003500810007148194000714114031038541c00307800c05c0d80c282e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 144930422 1250 144929172 144929177
    0x40b0604060303021b04061212030b03060112021201020d050106050a03050714090d0f02130207050f0106081504110a15320708040e040b06100c0c1202030a05060106030f0c 75
    0x1003060000035004601304641048011741c0350648400c00d80060003070240750744007005140121a918081c0142c0703c0c01c003440e048481e1024002118500c0c14140d0310b030403d1080204043e8003066420051a0000e2a8104d03507040400240c107000c40c10303c801c0700b224400ea10000100e000041c2c0f2041941e00342c012158000c3c124100b4074a845c8120346008110b01c101c841640c403800312080312100f00030042c07120820460700501802c0145209035040780080d131103450103075418071854507819403040c41400b4507015901d0030300c05001108580810f0610f540e0003d007003113607101940c265001c1c150721fa40198000a01c048000030246110b028400b41c01042c84042c4c0902c1004482c200c404885420781d01c00c4405070030107680c00d0303a64040307041c40c50240c06560010f4011001d07650903c8184040c82c00c2d014050130703040795031010440604038240c030403101d8044000c00e4181280b1081104112800b00740001c280094103980c0c2c444034540e1050b0608509801010210355103864081c41946544162010000c190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 144931672 1250 144930422 144930431
    0xb0d06020414030609160e18060c0a0e0d020303090f130c0203030a050601030c020705150c010515040608060403140d0e0f010e01050903040302060d0c05071703060112060b030612031b06040b0604 85
    0x40383c101c940c001b501821240ca9000c4000c92051001d01c0f12903510444958140c4185080200d00324205034440c0c60b451001031000c0611080d180340088070040500d90040045d0f10b005404000d00020754040c0e0042c0b6401a90410000c03810900c502801e4907146090303019690702d29140f140c40048610103070490f41014079080d0145032150300050700302c09548c001c45000a14003012240504544598000543d1a5082c803060203172a2590400d071007418130003210705005d1251905849603032002c0c11100640018143c410360034807103490360010000d407960b0b01000710b81daa001c824424513061441c401e10f54669910010560040000c2c4510380d085039044001c0c40c81c041c0f85da000a24980100030030080900d0341e8006801e60b8070f000c0c03c203c81c20542d000c8000351032903240e2103041d02075030030864400e4046804080c011803400710501c07540c03080e992300040e55815078a68009204028610304c850900342e220410040c0c41013003034921142070000da228010006850540b612041840001c4c10490145081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 144932922 1250 144931672 144931693
    0x30702061902030717040203010626061807091a06030403050c0106170a02011d100c0302060a110a0e0102100e030703090e1012081306110f0d09090b0d06020414030609 73
    0x4642e01840010088164115112400080d0041005a02000707008200345202c000004d54504580d80f00c2e000300040c0c607500cdd0b68a880f080d04e500d117000352646081d001b05d0700c140050052944508806440000c00b40c14130030110010902e250b00603203040d00807600101c0e40c2c4004440c2401044040e10799603480803800c3c180c044005a640c0d000c400028140500181e0001c8000310040e0403582d580c00040c580e103070300c95140d0710240c403400d4400343c103800501130040010b400d8616402491510200b404a40b403901170751100c11910600290031041c1140510404640c6100c1d80d030003000039190041c4042e5542d41258038003d404002d46500030348041c0c49520400a4000b01070b88844115003001038100c5d249049458410f4144c0f080c905628407003d262003001c14a258807000081c88445000c0840704401c41001c0800d90301c01c076002d00c000028440c65405e00c244d50f0030741c00c80c501c4464090036141c0a520140e850105030781058121410000f41550b1003e2646001c000701d80d008843d03d005406c14010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 144934172 1250 144932922 144932927
    0x1903060204090902031b0307090911060a0c120903020f0409060e1b01030b150405040b010c0501140103060b031522020607050102030601080c030f0c0304032a1529060f0307020619020307 81
    0x558030512509c01e41d20000003040c04071100c00c041d11388100400d01c59a032070898201400181240f2000d940da44110080b4252141c042ea04142c00d036a001000710740c4081952040101038200364004941d06601c850345c8922509082040000f41e007480e07010900150803150004084501005240b88a0f15101d4000801264000c0803101551800e9a0106503031002a00689140c80c1703a80d0010429171134113024981c8804942c011034181c0b441041e003449070020f4036003010b503121101c500c02525403038184045126114400e4088a86c0c410545100822004075000584960841038058406035000400c00c2255a4071050103688203401080250460034061450802c03003a0080910307102c10300000c0800d0506000f507250501440d03528035241d10300d403070320b00f180702003040c15080494681c22103401c811680c620030300401e64091304802120007041c42c154044904035070502d0740716410036400c1151600100441c0e000390311540254008282505000507850310b180040e600b0b45103010700c10b01c240402d241e07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 144935422 1250 144934172 144934183
    0x9060304020d02030102160b0f010b09010203030f0a060807081c0306060504120204060302040501140406140f0f19080607080705130303120b060a210b0f1903060204090902031b03 78
    0x1501078407581800c03082c501c0070034028880c90011140e4004d51140082c200100c0207256441120740308843e00e160b0b40d80b0400d43c1d01c0c0c3d00510b054140983c0060000542070400010070b06da0202540401280045e51401407500b4420079800c01c05140d00034100260348003000030400881103909141c00c124040c034200c002040d5000302d0241d480f400101194200a540e210341103440a550018404c10407035071f542c0401ca46107503102038040c0c0541d0030214002404502c50303050414600c0060300704030188000200700112041030300c045950101103030825001ca4040082d041e00a000050010039080c10441c102401c0400c00030700d10030070400d081104804d408501d07100c02c422070760f02d418543c0b00482203d81d21006403c1086413076403c40b0010800c2c0300c840751f200041084011142c01228852008181e01109540c40b031001603400c9800380715552007500303005007003244016180070704a5034146c41e55266404c0c0d1303016500440c0070649a0030301e40c080d45024016981da03403507502e072244036040e501c40101e034070784 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 144936672 1250 144935422 144935431
    0x80103080706060806070923060f0c070909060b09010b031603020a0302190206010620070509071206150e0409150506030f070306050a1803020312040212010504030f1202090603 77
    0x89002090311002c00000d5004000a0702c00d480035034015281c1b02000a18090151107141c04001003d0040c2c4a00304100d80c4000100b54083d2401d4070b00342ca1045c3d00009a405001880541e10030321f1000500d64096104500d5802c1c8507810208034285000e00f00203001c101a003151100202c200140728265060a140c0c40d546410382c14090786800480030306400034050141c03601c3d00e859265150043d05507020a00c00d060b20b0050322071400408400e5155034419500e01c0c0e4800050f44003c100740128a071002d4525844191340c80e02032540120841088141c492a43c4a00200c0e41008900c258040d0009541c690b203c0055600b00545545034544800d50070740c2c528200140c9955402180a607101404480070502d140c2c811101000d035603180107001010215001542c40c0e19014080502600111600d0b81440d0540d0040d81080c1140c2c10902007280e014100701c0e4004020380074214030200c203019461059002c1e031201c04001c0c9981c2000f5090901c150340320600c0504c100302e07800076940d4403000d50f80c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 144937922 1250 144936672 144936683
    0x18130605011502031c0605031504060e012003043207050108090a111903051f0207050a11010c0b090618060717090a081306030c030908070201080907031728080103 71
    0x170040951a00c00502c4c0d2900803a425000b442c0c003501000e540881403a000340d1059204101800130000276a00303e03641c50840d0310042d1450302c400f190400b04440915000380c0503204010b10890a22651400403a00b072500185946c521644000890014405000101405c0c01d0403651468821203042d2100c29000e40244401d424008001007601d03141100c0d82c4085506204083d100c0e224140107503104620310681140000c010300801c02c440f143e0081e10400da40c400000d06404010384c2d0f440ca40701c00072088150400c800700486001040814074040d01070131202c4c4c064049410654a84110b8400751407800c20700b07911003000e010301c9a034003d00d01802c1c581c0301941e0301810341b240a1541d0500c0c82e2050003428142e004610081a6a803207521035003150043c1d18100170040174443e003903060310072612000e01152010322001c0c0165020325a0140d200d070700c181c00ea4030030070b480382d03a0080c0001a000720018010004035080504500034285020300c40c500d00308911800010020041000d003050000070030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 144939172 1250 144937922 144937957
    0x8010203100302040513021905091005010c0b1b0d020c0d030b06030a0b1906021615090e04020303070507140a050a030b0403030209030a05010e21090307060e1813060501150203 77
    0x1003400c0309100c80c1e64029401002c0d40741e0b10040440b230710303220002801a00e2091011101007441c8060b41c048030070440740107071103e121003030306074070f80ca034004000404072a0340d0411982e003c901c42c600c9000410810004450068841030618a00c61616001c140060189072030304008426682d2903105480d0f100f0540e6101142101d14030b4042034151102115210803414101c2c0041000360b00861030b001c0750501c03450042c10041d90780d4842400c0ca8210751140300070401040f402d00c045140303174203d05e9000707001030201e0345480f1003039403620320340b060315482051143c22070818540746207042c4880c5401841d08444a000311411902c07151f50762000940002c1c18107600044115164400707005482d501c5410400070410b940301080c850751100c07480d280d80002d003003590701403005840003c0c00303403107000001070000e026850a007101518003000c2000700c03e031320004081c04d603c400d141703c9202602c01c0c0440b142100d400441441c1c01c2054072410303009041101c280500030b41c117135a03000064a000c0c0c980c4600c0e040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 144940422 1250 144939172 144939181
    0x10080105060f10030b04020708040608060108071b03110a050607030506040915050402010c020a061d04091e0606090c11070e01050d030320070302060609090705060919051c0b01080102031003020405 86
    0x81c0244031030345e4146d030028000301300e007821b000070140a07008170340450700c50460540c0c5100044859450841707120b0302080710b02d03e40806100591950301c0c40c00c1e2080c1030000d0178104c007127260f40c600f440c140300c115090780c40b031010444c1580e45070142d9034000710305840910a10103240d540352450928070021a0f842541c4000180948e8403a800145107640c010701a41041d44d1034440050501c2d01230000094148140c02c03061016084ca4811200080d4100e0344440c3d900b01480c54241190140720070503110f03030303440d10000301d00142c1c28030070034070448003540701c0f501c1a901c01d4541c64200b00861784014607280c0148010070503911013803422920940e140c6000509411510140310b20300c401030307035421801c0c0d1001c5202d80c02c050300051202d026040895882c20540d039140c0c1c4d0540d50b454503008464005c10b041c440384c807560070502c141d01d007039941c2070041c0300c201070302d40000c0707013145000100d04a62012b280c1c5001050049880502d405404c4080080d0720358604804181c8120401d4070000b40650303501d03c0001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 144941672 1250 144940422 144940427
    0x60d0b0118150e0a051c1217060d0317160e03010c090501050a0c0602040b0904140403050f0a030b041802101b08071b060801150206010e0a050907080d03020310080105060f10 76
    0x4c01400d0000d00c2200c400c451201e010b606510350300c9088031485490309000010030f003e5000307a121010400c3c903015260750b40c00103014104801880880a10420120000046160002d018030894100b00c0541010000042c020f101d8055007100d58040e074501030b5600c0e0910703031004c40b901c240d070390a01701203a68a8086004540e484003c01d80502028070124020566440e01002000f021b03004440a0281042220040101100603107000b4007080d0104080d1682a1500014004115960400190702c4000c240406d003500d00030f00c0c040c14000e40d40640002186001600f01840d80998076001d4014512901c1c4480c2501051070050311050010803c1000c21040b000e100070b134030540c1903101c09401d5481c0c8016200792000e0280e03040c0f001001c1e01010425100142c0076040350030b024040d80c065201d45420100809028060b410705020706840482c0d06001004141001c48182c1d4006030f4a01c0d00084d182803441058102e00c0c2503904290521085655010521b10310b20b2040710004200c500c081020b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 144942922 1250 144941672 144941689
    0x301181a1b13090c0f0206010608060d0b0901140705040608040206070206040b161403070f0206130b04080a02030d030c02060a0e010b04060b070b0a09081902010209060d0b0118150e 79
    0x855041c0724006901d5420790980780e44041281d401040038041c1070541c070784c01d6407140781d60045180180d0255004004c0741f84102c449680001c40a0031031311022500da1200040354400312421100d036034440d0484080e0020311800103900803560f180150a09040540050514030050400303803240b00301288220555840c60b003100d0042c0030345030340c0236a25840990824a0801d034107005403130701c014400c1c044915a8001c81101c50641c2c3c05040f0038901251039007080300c41e030003100008030f00398907955000c905205c6d02030041c009005524001c0403102d809104251900b603260903120109420710b11200390143d000980c6da41c01208801011507819000c4034124010180c2c48046031384241800b8001400016034801882c00900400707004805076110a000b80559181081c0140110800c10154000ea0304465450761146028400589000d4407640002c105402c01c8610300700c0c26035110105103181d03070031031400700b000c0814441444185103070130004005d94050900003005d001c04505040342c940c0d110000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 144944172 1250 144942922 144942961
    0x19020310050915150907050c07170307060c090f0914010b07110915090a020c03030403110c0a0320040b03030904090201030b060a020703300f050702040509010b0301181a 74
    0x914841600d4103201c1303485041600c5030158092404032001c203008910480031146004011001000003600e40600c2c805226001300c180c0c01c007400103209401c00500540600c4001160b20307a2007441440c02d181100307a09202d1039020b004074034684810031034400d100c3c00c6010304440200140c3c81c0c0306c01d0341d410034000c2d039403c555425601800100820400000300c40c91100000e0068030407004035a1982034407400c81c4154040324030b10358400c0c0005000244900e01d440c500440e2403003603d800261500101d01881215001128502412400b10158450705120a40320340411101400034440f078502003a124071411000c02d00039621441c1c00c4040d64025003140c00c8404019000301d50b986840a4025140c0c04140012220314a01181403c0804841c100c4490b4000d010603180310003041603002a5040007011103540c041c0a01400f00b82c0250b40c4512907e88102d011500208504000e03900305800c48401c0c2c1d80a090005404072407402007820281c003891410a5106800504c0d1101c0500030315803900b028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 144945422 1250 144944172 144944203
    0x2060615162405150f211c08070e060f09061b0115060915110f070e010b04061407080c0f0d0306050105030108031804061e08190203100509 61
    0x8444042002c5101800b00d0004148881c07449410610710310402c1d10419984c810300204000c1d111411443c00e20608000103000510b0390003910303168609008020b003031080c80e46c03003504411500d40b10058138403000c5a10702c0716482c056500340307496140a04a160400e481601510300801d41c1c85881900b40d007218040e800040c00b09844001000362000b10041503810010a9400d1070103036110820f64000c401c050b91708948031381ea41303d41483c0035403010001c01c1d5051410020440b040c04480c200512032a0707200705000c001342030b103070b0304050841004400607480f106030180d04200410045905c400d060007451081032a0b50360300e60f040e00f0320140780e015000e1007408a008032200302e203010340006100140324107580c0f410300c80c46644000650f04d9000c00d100d0120b95030804c00076540d96801c11221280c008a00400006800da02d07116540d07411a100c000c1010903040c03c800c1031003500d10030000340003030041814800400c0c0009901080e160a110051b8130000d944500106951450500c00b8182400011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 144946672 1250 144945422 144945457
    0xf2a180f0c09041404061103010303051803190f05070e07020706051b1911030105010e0711150709091512080c01060e1608060108040b06011b02060d0e070909020102060615 75
    0x11303c1c0d19a4580c0d064608440007850b016440301a00070035020399040b20b80540315141032030203000300003854210000c10179030705000311204020f403914524005241d2a004d04040e0700415614a425403418006400c0141000d0040b820460410343c0090280141d400130f150040e264209800c00d040700c0300c8140b41d840402c0c0140d401c2c6a030b006220210054500340968060000f2400e40000e16088403001c0c05400601e0814800080b40607005000c4034800d064864102c65413021032160109201206580c581c0000d80c03290000c00980381c1c58051420f4141c0030312800c2c1d0300c051801341420000803c10794000c26511011134907151014080d48001c00420002c000c404461401c8000c14243d00412200da201180c00341300402d000d0b5103d50320f003503c01e5034044001d03c0035840d410700540351409048100305040c0c005244040060300c4050107010038080310200410320089450700700342840001e40000940c0d601d41112400940e80c005003050b00001d09540780c1e1141d1a03100d0443c4142e10442c20205400d1004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 144947922 1250 144946672 144946691
    0x1110051b01270f02011b02100e03010b03070803160302031b01020a1205060901090b06041205010e0c010c03090e0a0207050d0807090609050d02040b030f2a180f0c0904 73
    0x190403141540d18030100e005441a4860700000d012841848050020f030801c0340741c42d0055011755400ca8111018a030802d51584190f40040c0c0c03070406180c608070000e903c4405800701806c00b401401e40c1c0440480190000a0504080680c0ca00500400884104d203550b2071a043c10700030f01c12503c030003000c00000441c9519002e4458045c2d84003c858038001098168101340e4042c6620403035028000007071156140742d00c0d003100e000242c80400880e40c2e0200c0d0030040003a03043e8182c02c03441900751242d4004142d03403400d4030364030303042140340c25500781400b02820000c00060750150484040c7d4818940c10400d0fa00c6014003080280101c13000105648510385140c001d05401141c454031601c07450f501e4002c01ea07100d10f002c0b580341000c3d10815421601d14040403005103001e8110f41d00100c2c004d81101c10a1094007406c07480c1c070300314048100c48050203044074240000442211603100401b1b4a00c42001e120300300c0c1083c6800d80040510f4801c0f084800400c0d4074039114800c4071151b001c01001400010ba4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 144949172 1250 144947922 144947977
    0x6050f0901180b0306180105031e241b09011403040501060b040306050a0b100e09060607022206090b09010e040c0b3c19051e030a0c0903111005 63
    0x820340342c403440784229203405841d0141c540c6c1e1050507614060041d21401c0304030f0440420110281641c0c070010302802d00b11010a05100031149541006c50400d500039081845164090b12030703900d100c80581d2020031142c2000d9070000b521a50f0502607045650340c1e55100d0800900614032030f04420600c1c04001000404e22045411481c0607143d001010041c01da01402000900c452030626000415000e9603048024039001c1000381d40f200015100e5468620725600080c14030004200e8144a81c00905481107682054815600604107410080003000c02c040c0002d90007103014450815080d100900040030440c440e10240010059882c9007904d0358000e4881582210b40c80440300081c03181041d0808c0100e101d640c41c0100410300500d210b107401851440c0e0b85800c011807c2a2007400300030041c1d50102c1600c9240520003d02d01c0c56840d44030304000307440c0010b80d10f010b04548208011002c050010903005039944bc0c1144080b6074103058000d0080003621070f030007400f515110045100e1301c14040650b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 144950422 1250 144949172 144949177
    0x50a12111801080702070806010b180402040305070f09020f030a0506130c020d030c05030f0c0f16080a120506100e0d020405010905070207060c05060c030a02040306090507170706050f0901180b 84
    0x10090301e40e030f0000e61380c094049075622001d10400d0360070f9010500410003a843d030070003450f03001035804140042ea100d68012405030f0340107030b00850b001c1e803100b54204049441d103060311000e09040481075142c40040c039102c002901001e0040c1100581e0351000c80d000350b4400e140d0b04044260031a0900407900100c1010f52148603006c0c002002c607040000070300f115407040045078800e8260b020240400e0715055602c2c1076540080c1c3c1641c07c01002046005a410028201e900c1128415480d07280da0344400e150040606500040c0c00305418109000c0c0303c0696a0400c0b03603041d41120340340001316859020002014214880300103904586448004603807591160007036031251840340c00b2902441e99039003003162a80d60b5444058459080000401c4407041d41d08011504105d06210150130180c0741d8035030404855086500700e50384e9104550810003200580f1b12401556800b0002e444464903180014205110740e041c80914004005803590045e070050200c1e203525402503084203103c03620f604c5c1c2c510495 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 144951672 1250 144950422 144950467
    0x9091005040f0212160e090c07030315081009032a0b06010806130b0f060c0d0908070501050429070c06020c0607020f060703030e0d0c1104020307050a1211 68
    0x5a09007801e040d0304070307a54000c8558180306090f0603500c40d6a8070320382003c890f40c030824800030070038185c0318010706a1f201c410141c014111080c2a0399100c110340740180c206c0b140402600d00a0482d09d004000d00c4601040003c0314511882020400310111324080304c44060802ca00040f8110040301d501d5500b900440d01ca22130b81c0304d0200015161502c2e40150386486080380e54a07401403121101c3c11701c2c5481c0e034100006180014082c0110a0042c100007449030300241c01e0b010f1b5031340c0882802000305030302800800040002c41d01030502c00e800d02000074034030306c01c5004805815064210f403180e240c0140410800707410301020000d849070b42518005c103004009100b50401441401503004039860004c08449096a001700708640c1c07941404280096504a00410b6050503500c0d20480b05100c024070402d030080400380d40b040c405082902e40b1006072005c2c0103006000c1d610520402c0100382d0850100c1d01e004400b410520160354655420f130014000c0c0101000400ca8082500780b80c81500c401c0010a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 144952922 1250 144951672 144951679
    0x70201062c06090c040b0d0b090708092427010c02010b010f0305060d0221060a0b01140418090804030507060804060f0b031510030609050304090507051c1109091005 72
    0x6403551000c000401c80213489510100c04200700400888035840020269131455203000325400c1080f00014040100488100d0b01082c210390400000007024400c1440c002c900e80b44018511360300d91084147c1d00801410030511185000f000d12000d5046d5103c80101580711009001041e101172000f4041c141000120307011170b074080c9541d00c455009001c2c41d03205036405888043c403400c450702000091a903203000c00303159020060381c02c20b0b004030a214840c49031003400c0011030001881c03400100703401009010b10100000c01e00061040918100300b6040d052615100818011402c1c1803440321403049a1000744144200000081c80c07076003062030302d441180103030300402810100b2456002611401d002c1203038582c000b04a240c05428008d0310320f9070400c0f6640034004032191250b5584d0110b9510f181d003510f613640003050800428a039030050f80d03448149864298107080c4909120606409445c050851154481200d0503c2c9810f02c0155190350380c00420202aa0404240082e8210024000c4500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 144954172 1250 144952922 144953009
    0xa0f06050a06020a06111b070e060303090a05040c111f050a06050603160519030509010b012303040503120a0203090c06130605070f0c0303051206030705060403060507020106 76
    0x2031925000c200c8404031038054019150580d03550780c40d20010043c00c550003020f240184112146040040c84203014071070240001c01c40303a42045c0d031a0000740001494070f07100c0d510800002c0210b499220041080ba0819a004a068450300308141c5200d03045c62032100c035600c60b0080b10084c40304441d2070f4401b80d403a413800820280e120382d0411010358005015083c1c0000003000425290300741c3c0b04400029151500d81541050040848444035800100441c00000d8440d4107110700f03500c0a108035040c0c160242000855065881c504c00810354900031740551070500440083c1c203000c020310459000c010500d0b01d40c1d0f01850f2800c1d4000081d00f040c0d5401c1101d2158420180c0941040c0d804c0390b400340204038109003412703e0414200c446a00016049a03a500115002400600c07016140d9018500c01c1d2105900d803824a40041d0900b81d00512035031081c2d105240402c40d0f41c48503412101981d030400004070320b41d550020142d01512156106e5031042c9844d058841c982c450a0114950000c9031940401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 144955422 1250 144954172 144954179
    0x10e1b060403120e120f070905060402030603061911030a05090d030509100f110d060e100e0117150903090102010e15311127040311010902090a0f06 65
    0xe1902890000400700c0c4861425240000e025112005003110010a5800c6003550415400e00b05032506841400c580d00c00c62043c0318040740c90041036401542554110300314030b01100003c0da0ad00000d0001a01e00c03102c85041b940d0350090760091900100c09a04256a0341404031504008120465420742280908458841042d00c84c0c010240141518001066004203042c0c10720014a0002c000352210341e9078050284e0f4540301c0401410f5002450b4a000400c14030304480102c80010007440c14845020b10803050004142c07501c00755055a50001b050800d0a03854610603180c82c018582d2030031045d448000308901c0c240d00100401b89411b00307074001d00c9031924000030b0590f0f52140707080702c10010740d414002a2040c02c004001900031800c07840840310000c410b6150003030840c9200020307601084403468508150400ba0a405d0a401000d841c0c1c0401800030558180c005001420040422110403805007422109400031030b1417940042c44c00c0322600306003500d5030090140e50140e9a82904100001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 144956672 1250 144955422 144955429
    0x3031e110d181a0106080c07020d060c0c05010509010510060207060c060207030e12010906110703021b0a03080f0426150a0e0f030d060608010513020328020901020709020418091103010e1b 82
    0x1241592713800b8106505074040380d920040500994040c0c0800c08c044c40340d0200c00301c0d4090080300d004d0780100d0000200c40c200f040009500442030b030080750a5600250781044150791000410003c2a008a0016220001490212440c0849046c0c207584000307a001800d42210040d4030003545e0b284500310800c02030b110341e14010b000d401034060250168005298030b17074264000d02034050b030143d00104400c840c0c94480e0340300d8400b9040901e12400c00e100c041004d005000c1d0511024003036482d140c1c004404024101140b03036a90190aa140844002c00300201c2d44010890b0003100040c0da41006460100c0b0341c1011a90742ca4000c1c0304151030490a2010014101c0d00800d800f9060322005440008400d8070f0000380406988007030015000c110b2000000140064454507407070103080e002c074001d0b0b03490045d0f100080c600038145d01314403500342c410002005080c40d811680c8100200d001c2011502201d41d04080ea07082680a200300e42550808203c41a10f0340c012480f40342c2c010314000d054800400c03c0d005d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 144957922 1250 144956672 144956677
    0x1e070c1a161b081e070b090c03030319020d0b030304060203090a0510020a0308130b0103031709012a05070203030d061502010c0c03050306120a03031e110d181a0106080c 74
    0x718200b200d640240040464402001880c88004020450180d2803d1302a8440190b011440075101150f580f014840c402c0c8013400211b50640d0210019415402c2040d5403685103420a0f40d1800388a50000f00401c400202e034004000d05d8600400f542d8850317944003000307500c039445501214468041c01601081c1482c04000208041400f13900400b000c00c140c0d03505560351100504a407200e08103800000d400502c510054034043d42c40b994421900d0a4400580ca00241000c0c0c070850b1180d0500d110b0824400078444801450b8003407000414852242c007034242c5640c46600b4020713416005c001510340058019070800c10449050030650084221900b604a080310004400740000030701600680700420300c201d02440c4c000724000c084007951410907034842d01d80a0780d4101100881d032143c2c0310030301d8140b00c100dc0b0018800310b02018012a901c00c03104903014450070048019040da5603040c003c10380e0b010408100340b82d03440340d000403d0b20b003940414845503c1c2484ac07000000c3c140300016000302007d805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 144959172 1250 144957922 144957947
    0x216060212030106050f0c030a0210050906060f0603060402040905090109020f01050414010c0204060e0f0f0105010c020904120e10020309030c0a03150f0e121801081e070c1a16 77
    0x16007908503400e200044800ba0b1042c0068260100140051000e05c0030a00081602c10050f4008007079050050083c002900d200400340c042d160441410803c00703440f2a500343c180326070b003110300340ea59a0b15500003a0084c001c5400c291350403881c241c10003008580c154000c41e002c03802155288800c01c07a00004403040d10660080f05403209100f80c4544440d405640303441843c0d80700402c0424a06e44914081640c44c40845d0f04001d00e004000912070120480c54800d40944428684802e410700b0940118030300e0f140c05000140390b00c07083c055641d8502c1c400c00e0200c882400c010103e0b284c4910b240710084d501d40004941d5442801400300b0324140d0f20b803420303082e8202d030790141030070500d024030845042c0105080c110740d880c00e507102e450940380148280302c5152a15808400c0a442c0c04a1003441d0b00e03c81440c5005a0600401e403080c0440d4541060a80900c691802c520322010350b500e040440b801042d0442c011700406508034074a200d4901409c01c18424040401c2040e140c400300310b021140c1d0100d211 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 144960422 1250 144959172 144959203
    0x3150705040b0705070b0304030302070209010f14060d090b09060115030506010c02040921120b0a1208030a0e060a0501061101200a200d0809010e072d030302160602 72
    0x1c10000d403910700001c0c080d4a030050f015680140d0ba50401c1d900158022941140003a80c000760040c2149040002e03076001d031000f94540d10295045c41d444403408001c40040910408001c01c8038040528a82c02814007590b001c2c00004090600a0500d6070301c0f0710a00071b04005070108051220200d01c6445410b11905050313403448501e285a40a200050070a04030580d120304144681d05204064941d2400d554030f0255140455180110b000d1000c480d01c4240e480e01c94808014100146144445403140040d04040d0642c0d40c2c0d19402c40c408010080c800d040e0f00725005031000c200c0b0b14111644154100c071010b483c0c00c45002c910180c81070807105118482010380400f0030008007840d02d1440078082e84001414041100300c0265500001030341d01c8090007081e903100c40000b410159000c03480580240c0400028429040d04422684c3c446649000700080802c01400c80b50300b002ca000c0000c1c0b881d007130507030588409170703160f0800075100c0c0c8200e041c20054007081a00019241e20001d0261910039080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 144961672 1250 144960422 144960427
    0x50a111e1e0103090c06020d02010e0a170f0706050c0a0801050324070318060e0106060206040f0602030703090b0702010c080c070b01030b0604060b040b040306050f0f040b1909050a0203150705 84
    0x442082284141c842241410140e80d9002500001d60903003481d805000250000d0036000354441c002030949941c90000c0400350407007018040003aa001c42e100340d9850b61001c4031902c17a448181c89001034011810050901420042407280c070404610081c40001010340c0d07424420ba03294820f140c0d40d50781c0720404110310220110440300c001c001e01985d5070449414500814600c11041800702c003500c0000e0141c0d10b40d40c0d141060000c02d07070709104480060003540003400062800d80c40d68034622290040250030240c0000c0040c0b4ac00d48658400090715500c44e25454090802c00070007802096030410342e44c0822a40000316440718040810b86aa0651001759a013107603003155100000e540001e8a03c03078000da00c484021a400c1403010290010303003095400240c55a01d1828010143c881c0502155510240c100501c95245500c40314035603c41d0300610001025142c111590100c40c10400300104680e2501d042902089004100741924074021411140705403107a40d030079040c80304165406404500304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 144962922 1250 144961672 144961699
    0x17040b2502031c020d1109040c020c0a1206060905010e060f030705060d02070c0308121e07050a0507020d14010e01050c0901020703031b3c02030706030f0603050a111e 73
    0x108040e0800c03c00002000d0b0801c90031340400000c0e06d00308401c9202894020909041e0390500344104003804006100800c2109609000724803901a28001d614017036805103104400d000080c4c101000400000808008541c3e464800f1390034920180e421521841e00c0322804d103030500c0c00003442d00c00d17110014665480c020b55103190034000d5210070401c844204400d8ae000010a000a015141e002580003040020740303080ba03c0603d00b04c80d915003a55401c201142480300c1243d0240644003035403400d040c60b03941c4030201d000051201e030242c0001170019202e41107120322030350107401490303503241d01c80000c1c030081d01c0d0383e01c005407035024900c90107006a00444080004c20b1249402d503603070190001c0002128503454a03415490703003039060b02003520303015404420062400c66040845e060106141c40e015047c40f40e0010f9224405403040c0010581c4030311049144047c00e5005000440d03000d070850300142e4040c0703400032400e6041e1202c50b21403c0404003001804c0d407070b420780b103003101002081350303c004c000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 144964028 1106 144962922 144962947
    0x5030a11060403051209190c060f0903020d0b07050c010f0504030906020604030c060b030709060e091207080702060a030e06250c2117040b250203 64
    0x4400c0c200004030b6070040a550b21200d61781d180000c030f40c0310281e0305407403c0c051603d0851410040000301c400c100c51080550211000750712801e091410012041d2201402c44c40043e4002d99074a10180001d011001c00c1c0f42c1c44849800d00508003107850140608444d44140b004541603568000d01060541009200d0010800707880180307140e16165600a20000001500030403042d12000c4c8003445682c00d100b9032010b0303c0c100d803040102e0366441c1c3c3c00e0b00810000b55445c010034006c03022406403100c1c130300045400d40c680060486207441c1240d424400d007070f0f07c015542010590380c2e0403080d0040c602800124020566000c41c0c1002c0ca07081040040421080c491b0380d410f10158040c2d2000203060301d02140c109400c00c00403070100c3c641c0d0860a507108108c43e521141d0301d4140c2020001040f00440b01c40d40918210a01c840c000300d400c08030400b0714a0f240c004800540c0c82440980300845 = true := by decide +kernel

theorem cover : BRFrame.Cov 144784172 144964028 := by
  have h0 := BRFrame.cov_init 144784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 144784172 ≤ n) (h2 : n < 144964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
