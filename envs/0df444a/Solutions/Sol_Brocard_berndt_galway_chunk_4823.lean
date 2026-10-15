-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4823
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:51:11.551792+00:00
-- url     : https://prove2.me/submissions/b4194fa0-cffe-49e0-9632-74841d34a299

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 867266187 ≤ n < 867446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 867267437 1250 867266187 867266209
    0x81308010603350427050123030a021f030507050307090b030601031e0905120412081b031305030c0103090b0604180605011203140a0f0f02160b09 64
    0x60580c1c94503209100190342c11100e184030f558411904080c110000080f11000b4080c2065854000804500050300710350090081c00c59040c440c50070b8840312580100d0724104c1c1d0342446240c100420030396840002c170210226440d040007020b030554a4a000e25000324001600c14001c0c000000f6814070440c00151b41440340c143c1050152514514600313095000424007085d41c05041d502d00f41c000041030700ca0307010342c1c000a43c8000c4503518808080c3e8498051000f4048208161b90900411151004c48111801281c09581c03038101243d170743d13800684901c0c09580200003046180c1800c1c01505150342010009020f021180b000c0c40c9042c6800c110606052400c00340802c2e041c11b0412211200050b10407054a600c8441502d00045107985541291640d4440301000f03041c1e2450301001040ba05200c4001c500c0c2c1c0d600070b40711040d8054014020525502c202301600d0001050301455940380b0303100c0c0040c03203071955130741c412034402030010700b6202440591175201a40d04040003134000b403503040c0345103180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 867268687 1250 867267437 867267449
    0x1503060a050421021f0f0e03040f2106050c03041103030702090601031107350a09061d1e03060604090c03020d081b01053103080a11070813 61
    0x4401ca06041d6519071201d000d0550380e0030601000003140c8003061082020007281c041d101040b0b81d04011070100c4000901201c00311042480c10320022540c4090000304540844207004e8580d482146050541416081c030100c0c8200419070152401c2c0105050307000715800348941c0b013a880c0d40e81c00e05280101c181044940e86138003c0c0c205202940140e0707115228241d02c00400c0c2000b00c3c0d01d48103078071803032142d1040079002080c0709030b895024110701c400000e042c400c240460400d0610034550615034030007402060080350003c0e5507440144802c51042ca03910030600c0402a566040c041508000b03481e01b805052070300c82c50b1490071000304031850100200c98004a06a504120304041ca484079803075425203001c064000d2640000c003008100414007120468481d038503013402355000401060f8040d00c8141e620306400060752180000c0c503400421040003816107400c1e209001c030b0590b81d0a0301d9030040144250642643e900c00f40e2000e060300d00c01061480e2054102d181c0d04d82003808c1020500c80943c00c90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 867269937 1250 867268687 867268691
    0x20706080615190306080109080702042007060c0201061824120b04020303120f070e0102070e1f03060507030b090f070219080415080603010f05071e03090b1503060a 72
    0x6052507407088500f842d20070f0002034072030a904201078000c0c10301c40d400340307a03030350319140c068401e22051780090320404d0701c215418820a000112840740c8404030941021041e141041540001050703079101000742e2019000200d00190b035510349001e003c002c2c280c140c0c003550700c3d040071a4090103601c841d04001041304544080032410701716034046031f004140b40200310f900720001040a556040044e07441e0301024940240d05490440e52440300907109a6000c4089094140700c00b10541c00410307120b05035060380014840036507a802c00e0018629918150b81c00f9424912800300202d0b43c5e41c0141407161040ba100800d1660440c01400008500100304a121209210901010030b82c046544030311440c100c0c80d6804007100d1805c200e1a584207070740c000c0c000101400300141c2401d41000c0c84501c01c40f4110000c10607590b0049810098806c02c03070720341d0005140c80c6500c2c200009040600d40040085180004504149580701091075205450080c50100b558280d8001451308000c840c0e0301010010381 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 867271187 1250 867269937 867269959
    0x10080303190902180114220c0c08040801020406020d03110304030c140604030305090c010311120709080601030c05150711010f02070e010e0414120909040204020f0a1d150904020307020c09070207060806 88
    0x240034505000252070011954944070602648c2d84100290304c0c0030703600b00d80025a1641d81c1c8035021b000354000e1003003201501407026401003090081c0314650580c3c00c505c0e462495940c450390201c0b0a079607064021076444c3e09024030200d09482c20004248950b200c0c1e03c1c0040c16081203001c1503d805070807200c40341003508040b4030511040d802801c0c0c415007507012507501002e40328248280c40028154100c8007191051600000c03e01040207801d408441c400d4415014010307004601c00400d01c00e22a010b4003000000e542c84c03601c0d521541c600610016244150750304507480c0c21510200d41020390194003000640c2c0b040c0000d00826101c080c0c0f009014100400d070469540007099020b01583d86075900c104404d40000b400d5444680441c1e440714400446155540280400901481e2a070070704000d1000c2014030400c2c02c1c0c101918240d11f0303803100c0a20a400c0c000300301d04010183d40001c2c1020114020804441540e03156003034803038000c0c2d0064003c1d1112a051039402001c8600050035207116050b4001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 867272437 1250 867271187 867271219
    0x41401051f090209030f150601080109050408161104020705060108070e091e030d052403160302040f090f0c060f0f0806010302070c0302090114040510080303190902180114 75
    0x18141c0300316080c5142c05a258015100040e052007040c480302d5a00340640c8034041c0444082c140d22601c034001c26221080d150f62520307088000c603441180c00502c007100c01c008085203803400c010181d0070607110340c030040c0c1084042008202a40c002c10b01c2294140c0c0500c0041c400d1410034800507000e0001c007080b680341842e00c1861169a01e1620302c0d80c040610840006d421801c2080c0112400014442810310150030060200d4612092017544500c1810401516030a0741ca004540c0000030128440170108440c02c54003000024402e1076600701c4240d589002c0c601c0064242c0361a8071a0b075016441141c4854613085016044440042c0c0e68001c100c054003c1e10085a00400201d4004100b841c006884141501d495910040207400103903000140c0301c000504480070410044c4440c0c4299400d00c080c1d12104402520341c049402518459001800022961069942039030404140104040ba048401d6004510288022180801c89601140050104c0e001806d04009009401d40e20300c003104840d21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 867273687 1250 867272437 867272491
    0xd110f130b07030806150405060a0e03011b0f0e1c06020901080f0610050c16090c030b0d05420a06171005180f0106150503071d0d0b04140105 62
    0x145111b104004040e1206101c0510606070b03406003501803c065964040190702806405000741102e220f0741c01c04484108440661000d48041b05082d01da83c85040d108181c2030304c0200c405a003c680000b020b030201180540f040c00e5826206020310310059036000250001400900e004001c1403c0b80d41d01414081c0c02c2d20f5005a0340f200002c0390be40746403502c24503480d090a010b81554080003544184502080894044d4050340001714182c030b080004201d010240704200300d40d6031002c0c01036000000680d10441c02c46002d0800e01702d8401d0140030865000741455150109a8805098030909030100300300281d040c402c11000c1d00040305205031242011400b80c0d51240001009001c0944032800b04014800b0046860102101c00c0300380d65580c196441c80e5802031420380710b502200508280c5800455003c1e4046034000c3c85181e541d40c03001011040c0701031861404a20003500300c030a103040340c404980c21100e00c80c05103120740c40740259604003d101c00d007076a02c0500400791924114011001d214100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 867274937 1250 867273687 867273691
    0x21170402010e060d050708090709150b090d080c0601030318230609040c1e091208090f04110309100b180a060e0408030910050c0f0d110f130b070308 65
    0x24a00b181c03141c1401d8010809a0003860301510149080c0030600603200c1d00914554407680c0504216002c0603035420300c107410350b42d02d4484401c0340d0302080400d00c03048241c48000c1c080c21b040508110f071000749640c1c5080040c1c3c000040084150000c2005204240d4800e115020341e22441c1c441c0911036041001c0706200020707903060b030400c180800e280707407101d078480a058030030100700100108140260744001910310030030b507520004803684403046200d07454060340320385059500c0011100417002850303130b440d401039100c2401c0a509ca03c3d0b40845002941d40d5000b81c40041495490140c1c480c1070081170b030b5160082c00c03000c1d20303201400c2c100c1c80ca6241d114100c034950600c1180b40080311ba91155100480103001d150002c03266150f001c02080240f014050003180205c102404a407100203081d59400110b40007569415445c240420504500c41c8155000d082c0c01c9200c5d4400151060740a1908a0f080d03100000181c1c11503004078003d0f09940018907144010007592a00030324056907642d00806000700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 867276187 1250 867274937 867274939
    0x50f060a0b0a150c12020a03140304170d020f0409020a030b0904050c2103030a020a08011706060d1407290405091303021f02040509010501021c0f05130321170402 71
    0x718140f1001014450400400b4042e001090f08003207030841e0800030340300c4007281025004118118146401c1054140c1183d00c116080f1403034a20301070b40d5110080c440e03803280c0450718030150280000d441c04403c0b400240002c007002140142c1c0c0e08481d05014058415941c440b41c8240c0701c1e8410080441c0001c60340a8125104071981455036204c0c14120141c41301d948070040c400d2201104005041c0c02580c024000200300703071640601c903aa10b019480320180307903003072801c0f40341c00c52000314160b8100100d0010380988260310040c0300d12600c1b00c02138640b40f15980314110000000d022040d101210344001d40c0708500852015181c14100340128043c220040c094851502c0824481c01c2414400d0040e80e2074104c3c0d00c0000d0307103100901540c65002c1d4100e070080c944100722000000500707600014841708a02d10603204089030107160041503401000c4055070700c0a01004000000c0d890002c1078100016600c55041c04074201000d00b5105000503070200800244484030902050800f2210f0703600c0d034801d0b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 867277437 1250 867276187 867276209
    0x20303150f130f3c020f07060513020a0b04080c0d032a0b150f01030f0b03030f131509151b1208090c18090a050703050f060a0b0a 57
    0x40124040ba8800c0c0651010600c03503031905010400d443e08035080901c01340b2600c00d610a0751505405411249400e0401c42400540c1401c82c59032403400030b4001c0c0a02540700c20510b41001915142c2c078080c0c54003260090038600fa800000000c40c9000e076250b00c007824400400306d0030641000101a0703100c0109080c10b1281030300d40e81250816106800319000004180c030459120480b61003006005002c800c0c0444203881142c000a041d255411035882d03401034014008c003843c4092800550003015040000500c0725144c4518900984040008050130308003104481c0d03842480e40300c5e00b2203010803a086030a8030f098031214078941039408411002942c0d41c01c92002041d03030b5903042c2a1b40095a1102c604020161441000d090201c08209001450203644940c04555140c01480d51201c00401400d41e012040c2001e4040e1007000003c40e980c1305510101315400f01000c0e8890520f0102a030b44110350b0760f407042d030211668100c2400141d03000503200b02e00344110351014001030b561604a003c0c203080c0300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 867278687 1250 867277437 867277459
    0x1a0a0c02060108120928080c0306060618191203020c0f090609100e0109021c11040b0714030711031509070603050703240504062c04140709051602030315 67
    0x55100681c05d807031820603000000400f2010000c00081c001e1b03d00c19002a8051010404402c0c140480c10f5440350f0740092686240441e1000c01e44080c140510710385402444200304c5a0f44c90f070b48400208007070a0107404a02030200d007813400a01e80a00004014000c10800d14a0303002030303d4074002150003d504480450b81a40c802c0c0203030f146482c0991003000e0350b030194000080c00c6d00290f40107041400028120080541940b900744082d45d01e14513900c0c80c8190204400c0081403030300009007400e06e2007070030803848151043d601c052039508904001e031240308014241c1401458204550540d60100a80c642007074644403d02c0c5445000c46d1280805058a07103001a44041c0300c0d6001c590360751068503a140984841b580265010700031401201e005238640400414102003d4120101000041d4981c45c5c0045005000c40c040c0a03010380221042070a60401c080c00d0081846484003400d001d07840041d0700d02c2c0c045941509c44030b101c1012400d6400410601c0100009444401001c0c0340540d1005411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 867279937 1250 867278687 867278689
    0x9110f030a150b062b0c030216150b031006050a080d05091c02061308010f020903070b1e160b0105012109050c04060303031d010c05031609031a0a0c020601081209 71
    0x5105a05900184035417801c0c022284d400c082c0545110102401d00c1000f4004610600768220705c2034080c0c00240103224550317200010751050401b03508600900c80400c0b401c0101000c82d151101c00ba4001c1003003a00d4501c01d00180c02c0c184017450003480c0c5040201132241e1141405803052207050442030082003500702014120030040c5500e4440ca80c081d001603035078840f01c8601c134403011180c011520342d9400c207001c00c10003034014026101c00c064020050181c5514241402c0266409030244215040d9101c9040349607031030b49070290044c401104c0140031084a14035014400c808140c102034140004124401402515150a2400e030482c030140015980881d0078000d16041c40c1109503540a400c1190100c02c261303058101401c29400c819190003443c00f0800ea00d400c2e12022000200040c038288000350b2900744280c01c0d06a0400c00741402c201180e03ea8888140c00380314080907521050a22082c050b04000350304c60710440920074801740145504210555072250381c045543ca241b9603004c9088486 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 867281187 1250 867279937 867279949
    0x61c021e0a0b0705030304050c09190906060519060318080d0c0e091614030105030d140403050109320606270a091401050c1204030302070609110f030a150b 68
    0x80c2401d144026103c50303062500503500e9100301c40440d110300404088c3c40040c00c1c804581401807920f000c1c03a907032041c41000b0050080407410700658940d603c895001405480b0003c5440180c00c601075140b500d1810400b000e020350f000005142046403911444401086d100c1003501e00050038800003081d54040a001125415540e000c0740e03a11100810601c1110100c8269040054a10703031030b280c8800b114095500c055004c24481c06801d90805034120701e44034482d4200c00790780706a445401d810981c41ea03c0389421aa2195030440e04591038004812850b0415400b11801048607203006406000050025071070ba0005410140221000008210303284000c020945160f01c20403202c3c483d900d0f02c0c2156502809400c0815180e01c044010f980381c40b03040600030317103200c0d01701003440f145415490300940520b442d0050090381007544c01c0c896040060710038040e03401902d000e0381d00810100180d00400089240030040303148a5480302c8018800200c440c2c04030614080703003140000e5080b68500200354 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 867282437 1250 867281187 867281189
    0x402040b031623012102090a0f03060903121b0e041e050f130c03030e0111030c0d0e2d041104030602030f07030b010e0904020102030408010c08061c021e0a 68
    0x1c145100c620124a1030700c0304080d246003058000300103507202200e0006440640003074031754030340c9003089072128402c4445540007020004005007115140650341d5100981d0070030b03103400171903409840b904444141079201440702180e405140c2c0c1004001096503d84044d20b8010440d4018408003d060001a5903168404401c00d40d0300c0b400c1c41c200e5111803241d40020301c400c03103000c040d2031044c9010580756000162041000c517030042d0a020803a00f5502d040d14607002e80030f811410011007006034044400f0600140510905100092619806840014121b05844040705005200c00d40000805c585003100706903040c880440c100201c0805e9001007405041d40400c0c402d041800050000104002c5a000310f03c01c1510b40004180c94884040c00c8013522951070f0030382e0018400720072403000c501d09694201e800c9481401100e00d00b5a580c0f80503825a04195400004100c1020030000b40d03003400345641d2038110000f001e20680500c83c0d8005610008030a1012084049103400e1004949901e02180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 867283687 1250 867282437 867282463
    0x609050f1e060d09060f0b3a050309030d020309060d020d09020a0e0907140f0f011e03090b0901020a0207120519080409140405070501050c031909031703010b030402040b03 75
    0x1036550460b04030f454016040108007103410340d207026401d5031010f4061045113000c010060510004a40350741d603140041c807010200080182009030071003101d1840ba010407090511440103140c81e10f4003002054101600e0030748040039500104003800065862200701c07148010048001600e80c0803602c070450042c40c04c03144c025041140c050000c02c41380c0401402030b1250007030404880269840361400a410000c40400c00d811400300a4080c40d181780401110f42482e40600d030900c0800c001e00000a844801c203070035107010031f5175000140c0c1400122602268004082802540780c1042050001d56441151085d000c01000303010300c1804210080c80004100203484060401821032400c0022480e4414800c000e030042c9400c11014001c8002c0400300e22032900840a03285075450a00156803d40c020b0120440500080281e640c0054445035401540c213807e55811880c9030551034104003a13620041111240001400100031240c100401c5075403103541910302085502030400030031700c1d0503945242c007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 867284937 1250 867283687 867283699
    0x6061724451807030b0a0f0504081e090319020607050f030d061409010b0d0608070b0a03050c032a072a0603110304061527060609050f1e 60
    0x5a603050949606099128610004001c410384640c2d2102c2e0071540341c80e103070a5994100507010000300d9441e0701942d6100b240350b0f00101d07001e022202d00b03d045031030483d02203402c0d00c0041020000b000007600d040806040031903400d860304844d840003958441070b8440f030034040e901c5900e1034021910340c90250b84800364803c0444070301c0c0a0010210b600c1c0c0d040380c51003a0743c5626001000900d0441c0104028000310041c02240d41c603428000424044e510843e480404503458100010300104d00b00070120080c0f1070562019200d002c6003034000d007550000742108a0440e82071040c061a01e09044e54100340c1c80480421070b03036000c141003140070b0f107004814000d05241e510030b1414000c178550310940c07440602c082c0c0044110603241e0707400340e0484882e140c039160480002c0c0001000115071703922400c0215543d0040304102030b03544c201400c1d0391002d44041044441000200714060815005080c0a414079080c820f403881e0500011070b40c810700f9642d560348140461f4655052555441d0101125024060130b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 867286187 1250 867284937 867285019
    0x6050a0b030f030a0e09010510110c12150a1407030e1c020a14030310050607050a020a06020d030e010c0c03030b0d1b030b010e090303012706061724 65
    0x2c420707100c2e000a51113401140401c62030040c0c3d4982490854141c800080c41c00400d0000318104079030407402142c600c00c0c2c0344280c00b81001617584c0c0340882030080c10300b030005200b02c600d00500100c40000181846e40c4160820011113100e5202501442c0d014604d4500020300494501c0c03083e2170082d201e0210b4010414240e60841010ba0104017940d0084c000d40c070010711004083c04d5182d6902c800c81d94401040c440c0c40007032005103001c0300104211800350003115801d96160f00010040f200310380c40600941d100740b041288458150082001502080008100850001c480505003850b10300d4018201039485507c43d400d40e461508256210b6082201840d5a000e40d055172030640305940000d8035200b8810000051004900c1901c6204108150256055910b08031010000342a61144a01072144002d10a0300d03101c5507125020041c2410794a00b2b69206084024011450300684000700d55110000801c4000ca961b403401c40c01040241d81d04250f0a03005201c441c00410301306901001c980d08100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 867287437 1250 867286187 867286213
    0x507030b0a050a0507110d030b030a0206130501120902030a0201050a12090305460c1a0115030b0d020f0301090c030b180712030302070804080a1203230406050a0b03 72
    0x200c82403180f24030100402c00b03625000d5003036510b4100d8214043c140e501050100c0c54007031194204242c20b00c0d01800302c8040d1180c5a0000710541c0212103410202c07040420208007648e409003083c0f4080c2d41c240010400440079401003a26218601d9019042c4900047d6070b08100d88100301c40c00090107450810043c20040d403400400380d034005d004405110040a00c0ba41a1070380850300c0601140380482c0c405e1601e044286007080369018800a40d0034007040e42c005001040c400003070720301c02c1007400e5074150a41d8181500103030303001c80800c1084205880c003d4a01125156501c41642c5d840d011030b030010028070500002809000c0c2010024070f0003003400e80000402c90904512070081c104100f400782d415081c0040070341e9039501d82c412004a0f842074074150002c00d002c2e50007800e445026030f0040c0d01d05500d40c41030914106000c50100c0d15818050030003290382d42e143c40342c583d050040a026510680c3c03042c0b0000e01c158005000030300086c1c1d0b6080441c1c003403c420361203a0140480501038548407100c41c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 867288687 1250 867287437 867287441
    0xf130b0a120f0213030b06030f060f010618080309130b0a060c0b061c171603050702030d0f0e01140c12070c080703022b02091303030b030d020c0d0507030b0a 69
    0x7501d405981e40c101103100200c8002e500070f54107131348941d40c500d0084601d9070300d82c030054030406000c00380c06004541e030104007c01c0620400307200c0e1440295185141d450420002c080301c5094654542c0d60748525014400183e011046450191040791241d000032141d081e03e1005185400003280c0c0188070300b50020f42250800e81038040d041c010b1107050321990f651006c1c0140407152115040724000d410480c1d400092a440c60706500350f504612040c00c00313690f0411440d24407400001500403a0000c1211401c610302007000400c03080040c41e100154044031180a805004898450f030f041c0114208041a00000c480c20386c7d16080d410411035a000700e0b03215191829500507402900d11009400010500002c0018a5021207501411940c000020044807000100e41c8402c0d004545000e140c0010169440341865401010703403a80c80c0c6034228103890041e003200e0030710301c2d82d60003070700b10304c017182401600170400c080d5001c402d85001c1c018118601d0120700740324103070f08010000d0038032505100c0480d6040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 867289937 1250 867288687 867288707
    0xd09051c0906180608040201081b07030c051603030801122f0a06020f0a03050313020d030f030e010908040b0c03040e09100608010b090103061e1107020907080702030f130b0a 76
    0x80d03201e0842401c0740800c1810030b41444d02401010030301e004041070041d4858a011580700442d00404602d40e0354411300c017140c6612400058000030341c080111018400240204160244903200c0480d0742032440e940600007880500c142030300003003100d1f0b064043c00480124a12004044c8c0e482d81e13155030300d945c2030030300301c40a915505000b90218000420f61a0000071007406140d5400014246186c1c55641200c2c6980010701200380d0b06604682100107841d250040d10341745100ba2140ca00e51010b014005044402c0c1540ca4010350b81080780d5840071820070403c85050382c2c1e120030300356070364071042070035618621680d07209143c0c0703640300c000f0042c0410000c55440102d0324a841d00b07000007592216040d090301c0d01c1c9454107500c1900070f401000002e003c2d5001003284450a4000fa00d181e118851310b074226801d4003c601c2210100058400441c9058010f80c0e40c440d005080050950038800c038025520300592003603100030840003a0b5641e2821406a06130003d044041e4116664990311900030801850 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 867291187 1250 867289937 867289949
    0x12021b1506010903080d0c0504030209190b1914060c0d0c1b080d0e03010e0d17060103290a0308040303030e0105060909030703140708070803100501140d09051c09 71
    0x48000c1901d540c0b1521282e03040301e401044003800d06184150350f00c01400405105401d0003010000000184c9a040c81c10380720712010861510701102d10000802503500314005140f151041c121070a078080c40e6140c0c054155072048558500c1002d240c1d0100710144150a83c0520520854045040c0c8551000455500d03d00c1060030518254900b1009642d0b0111802050441d4006402e4115111301c1041055400c0b60010004141c2c070003181c0405003421144014500050704403884403249000e00070005030880400c0c40c0410000820300244000d4000d60f24504445d00617082d49044150f1360200700c4406950001205955075a880c0343c0035000741410168800d0f25400c000001d8014988003c0035442011008055440c104465408030b8440c2c40200481c280d2070307011700c01040412440340103000704a11620f622607a84c10b1410608c100444254002c604010071545007400104000080c0d0b11641c004403c04a11720855103407050510010344400c43e00310000c83c0605180c19440381c0c4032811284 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 867292437 1250 867291187 867291223
    0x30609050f0c0109030b070c1a070c1a0106080403081305011a011d01020726010c020a020a0f0f1a0706090503031602030906040e070207120c03030e06070b040312021b 73
    0x4060001074411039031a200160841b01c0351000100f40c5801082903882c041c0c481c1c1c0c65000d00d241101c1203803503410703819030b200000604810003290030803251010300c030b00010b44003085003425850b01d14000c254080042000f000c111403140890a502250001c001c181a03000000b40001000c4400b00600781c04035440c0b1500050040c002c010045050484034115600180c0c054480b4070304006c145445102d5080255108001c0701040c910808000c0c807403102001c55550181403600b0360b0380104444800c190308040e09005a140e810092690601c800e50200d4840000b001110b4400c0350400402c0c0c0109000541011301b0022450f0400102200561140300b0311041030300510360111040340d4a0181c40c0f041a0000c00800c410b2024100a01400c1e60040c0300344129089aa1104514002801492022110241c010406200b05034005505200541e02958404d041201c143c0b6050100c0c5406000a02800b910203100140061280c04840f90940d41030038841c08a503603241c00303079034035400c4201e0100a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 867293687 1250 867292437 867292453
    0x3040504111908100e15040b030f0a080a021c0903061d01020a031401080307021c11060a09030515070f0c020f041103090c0108060a14060909040819050a020d050310030609050f 77
    0x40086415540200c00c1c40c4a0601b02d1210b000500000789180040c0c41c1c3c0c94070400d035803107202400030010307400e03a280b1940354143c60310240c1d0006482d203411801b8100c1c116500c4500a00c02d10380c8842d05034112034110030040b41000380e21003821050b40b1945104c40c42c55000003440303914160513030460301e409d8001079900348450303a031071950715141e0041c04802580120420586a0b11804004130800c1c894011401411400d18010015284c0c1d0b100000d0000807640c902410820300200340302c030301400d01540b90004000d01d1701c0940108450691031014040c00401c050b4030040d07444886030b00420034005002040040015007094155400891301d0380d40074800c10035030748019440b800300359000e41000342500c808141441e4075455840780712880315400080900c217000e25692040f41d0035002e280a0400180e80d2038550ba025a00d0145110402090190400c1140c1d801503000440041039682c0e0b1034003580325160312140241c4920317203a2000d0b105a0a0a4405e4203000001c14a03c001040d0001251251 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 867294937 1250 867293687 867293699
    0x36030c06020609070906080d0804023c040506010e10110609100f060605032a0d020705060708061012020904062c1e070201090b16090e04050304050411190810 69
    0x6a601401071f040b258001104482d8054042d108864100d1710081508500c041402c103003c081680c030380d503c030782c3c0010314030f0140000480075040d207001c03074400392400d11551a00c0c00001e041400401030460080d45105950500b5503c204008419442da04098030303000d041103803455a40791103a201560081c0d107442c85000c4581d41038440d01c4115501034032010305607503800d40b000001108400cc49850310302031010504444e00503400921884481706001078070381e403a0341030562801c1401066101400104d5040c000c150b45c40048020b003090031840c1120440c00d00910b298043d01801401d560841e0801c000440c0640c14642820011440311170856004015071090036440f06040c4d0385c4c1e8184420111864603261148815941e0100150001055945841e0346402c4245000c40c0c2c80b46101e88d00b18505100c01d9448480c2200030100b00951800e1810192500c81d280d104501c2920711071030b0b40303030381c81107640580c50140c4d03404001044070b0b40b5540b4110100a005400d040f1868409030013121380200300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 867296187 1250 867294937 867294941
    0x3060a1d01060e06070f031d01020604150e0114090a1713050d06021c0b13022505161508010902040b07020906041104080a020f0136030c060206090709 66
    0x280190104851401e91816034141c1e14800d042040541001d0200f09039070208030094080d40015200e503881c0d42801052000c50200011184182c034115080f210078030021400c0612118140c60203400c00048801d09025102d00420407405080408003030002048014a000300300b45071100d004880e0380380c18110b184c80c0b0004521909849103411819103030203100d24140b040d0120303000c4e80f180b2401032034914044440d2012030328018401c104552201801050360030485540034078403c1040e030542c285039189012010b103510445040512400e00c45020b410b0060410480c14009002c0840c6c0d5102c41d00e60f0311400d280411840c000e004100103500000301c103180d91084900b201d0072400c0040c200301c12075003003000a0101030401640035807119042240507640354010002024100e00401d4443e07464410301c11000c840344046818410b0030b022944000c02e002c03080b07507036100000401a40340362042e01416150b18050708060130840d00c1e444040361180c0c00047c0c550042c505c1c40300b210005079440c01c050003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 867297437 1250 867296187 867296219
    0x11203020d1101020f030c070501150b04090504020f10090609080a030c110111030c030c060109140622060f03021c11012006090705150906030c0d1401030803060a 71
    0x4010303407290901001162151039403a884001d031000151800c000c81501c410640c10503541c40c0c01032400095030b10104502441640d0301407100a549403160342c60811200c030580601c1c40f8a0001544810014085554848841c07640c0d0500031b00c1c070243c41030342c10f40050607564030340101d10208071a420b010500c0b400c00211501075903407540d00d02d903140c8465510000c06001c0c48500505009911103198000201030000e850280000002951658404c0f0980c602e0181c0c10b034045a00945800201c2d0707070501d9070495030b5174071941c19500040070341c90004400c15483c42c551640a035080c94400c1c003160540041070b84030308483c022980c490002c2e05103201203106d071612078001446129002e26110a950080004540c1c44444e824a0414658010101c5043c80c070f08070341c00c14076a00850810b11280c500000503249209000101ca82481010340c0858003921000d0044000a03501040242645007160040380e41d1040c40d40e04440c5550b03407460410b03010b40059802e00d205031014000400c8080c42290181 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 867298687 1250 867297437 867297443
    0xf0b030114061809010e1f0302031b06070b0907030b06030d2a0804090507021e0a0201030518010903110118050601033e010e1c14072303060112 63
    0x72560340814010480b090348448510b038089a0700101810007a5242c405280c000d20201c1034000b030600e00450001400b041c408500e80c0500300c01c520a00260310002000c0c2040b150b9a14200180311030000006d203e400360480c024840d01e4444100312407000c000c01c440007100d114400c1d03180c0c3c5807519010941c85000c180f00400014904070709070442208481120350064140c820b940c015040d09403680010f0781d0140e04418011501c801c1401719041c0c5c108600002040f503840c4800c14100090180c90b00c4a64910001e41050303210b00101e000442e404480b10b414180c8a8020801c8440380c0c64050031020342c501c1814204e501c0c1040200400c9101c07407005120540c4038002e4819a0b007581c1d02c00c40c00001451881444c01050034280c40b050b844290766031441111b034003007680340c166500300051281008981d0140145c0040342c01c240b0f040c200a05190203154040f0400c644081c9418020340341281c1540f2540c603500c0b080321803000302542c0b41000f01c04000f044c0c1c1901c4490fa25045800380d50701d18a0401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 867299937 1250 867298687 867298709
    0x3090f2b0c080d05040c151e050c0303010603052d06100e0a03081b030406170717070f020c041a01082a0313022e08090303160309080d060f0b0301 64
    0x10069400154007039a4840c0c03142240c9011b05403142614600c0d94000c0c04030b20301103450003600b44032540c1c3c070080000d00c402e850f1030f0480c43c00300401c034200e49a01040c0b15000a142d203c0c00402c0d0008050740c802e0344440c45610f458601c2421001d9000b0440c1d4095441c1409071401c641d55810b01d030321842c0030744100070014110240c86450360759038081380d85c403100c10444940344030316070050414001e000510090003641d84050209910b0745100066a6000d041001403000070401c00450000c05031815600c031045007046140030700b001000f81c2c00d1031031032041c00307a01c00c3ca020030f4420011501d100049485000b80e9600c100e507035441c0107050f0940e820100140b4051a0760034a081c03030081d02d0001715406454508801c1c3e0344002e99001c1011100701e9108030b45803016030703846802642c1c2000450b070018541031915059500f0170303d22a940b0ba1101804000700c00c110918507803050342c084e420814500d81c1c84a1a543d644100d030a500e001040c543c000c00b0b0200300309501c001404451081a203040e11045048 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 867301187 1250 867299937 867299947
    0xf06090b15060f07080f0408060601080a02030708070c1509060e0c040b060405090601120501060503011706070914040e030c0c1207030c05040207020d02041802010207060315050603090f2b0c08 84
    0x80010f26082190101c42012040022640414040024100900941005001c42c0c208440050480c040042034845058810b00c10030401c1940500074682120490400e5405400182001260b409880900b500c0040c14401d102e020041300f580900c00540b00e0105a99a2116140c1008107a81071140c140394020070030300c014065898251706c1c04da08a581414220141d8809241034070541e1400d078414000303d6004001040b80746c0748001c0a601144c01c0801030a00e80c50002000303450b001c0303070b8080c90313100300100001d5000301e4440354400d0508491150480e07072108164100c071943d03620f40800181c00307030660004a820310030002618005580e440380c2c078103414506150922000790040f95060740d00050300502c1c84007507111031144408e0305040184070740101c40c207400003a1a1500d903130301600401d0301c1e002c1005901e0518030b916200342c450444243c0c0c1da80c0c0720750300307454900f003405a400c807110b0241000d1900004800e101d43c4294901d00540c0c6440d0541000003030311585031480e130182c81d40b501000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 867302437 1250 867301187 867301207
    0x210705031c090f0c1e080316081b070f15052217010c031401140f1f050703031103010509271002040509010503010b2b0f06090b1506 58
    0xc0c1c4540340840c603000019a00140c0c2d1107080c3c0c0d10300360300016100c0c1c2010140c10b1103400c541003178009079460b80b10381c111100b6207044910760f940c3c450121542840c40300040220b04005a000454030300e0325150600d41c0e030360003c180e20307542c54403580e10607100c41e10440c5000182c86410441d40103080f26050b180c0d2410107186111036242480060713038410a05542c510041100000c00b6407650500f81c02400003c1d083c0c4a65078041c0c11030b8803880600c403003032414000401040d100010b03030143d855400c3c7c61034402c205402000c501040800c03c0d11030003507480504003c0c00c00b58004c000e0000d00d4026070703060000c48064050700042e40703c00c0c01002d400c00600d800203694403100d0040300e4003d00000c0350380040001a84542030800c625059040542c40c0c0000c1c0806c185d10342074902c2030140c0000ca0082021214542c00589400f0390306403801050710b1388503690076403a00340e100b0b1503100d5908051020824030152801d400188403001c011a08030701c0407004551055005288400d0480c00030308843d241032940b007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 867303687 1250 867302437 867302467
    0xc0301060815040903031a0f090714090d03020102072306041101170a02030117190b0919050c101106010501141e0c01061a0702090a0b0405070221070503 67
    0x14141c0700095282c00407003240d62143e00c1100700050280d60001603445e60301d0b906140325003d80380040c1c0f152245111b03145041e6600c1c2d070183e8120302c440c1041c62007246501c0d1030703003183c1c001d54038174a621800441540302455019001010303520704c108442181e169140d40e011000c10480203688045e41d0140b000100019403041c40180e0350441410034001c00c044074055048c6c00c0104540c040c40700c83d00840100701c00c19085040444105482011305a00866500e5951213414076850240800081c0b002085082a09001c203c158100b5002c4600d01c049903420f0055648150408a83c015030079140f0300401da034454840303240c501c504440604816460074004640c004404000201100c0040225405840d0100303d41c20705004800003031a04c0d12036605425086035510340c4010403481c15030f022030382800703840801c990003164100c44035a050b4680c1108040140000680c071904149131a0502c4201a0005903429986d103200301c4090f14000403031243c142c14050143d0090480d482801100d40110f048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 867304937 1250 867303687 867303691
    0x6031d07061d120d020c030f030f090f09040b0709090203060303160203030408071d1b0a030e1603060203041704120b0a1404080c06010807060c021c0206040b040501170c03010608 78
    0x110466104580c1d4540010f041801c1d0142030303070400c0d8001544034284075014002c1c0320412204501a02c581c0700e1111b06140c036803050b08092001c0003000144503807141e440560035908800b0151070070082d0728191508109206080d11524040f408020707000a5008003030084910544029000d0360078428608030200300443c01080403680341c00103000124031071104015480051084800c407501c010301202e03080040c1c04016050000210100e61034440d03190780e200403105d202c0071070314000590b40c1d41000d07a542001080140f407509040d00071800018041d180d0095401680104003a000d91205001c8168552040f0703c01d00e030b00703800200b4940d00401d16045c2002c0e0b00603480c2c1c0d030100e20001542c40c80c00c02030004a5040750ba99034040b580000458041100c1da0140000320300512205007400c1000d0210070099000a20586910441503c0036215050b19154107501074141925191559030042c041d400a0050301e0000b8110001506010207554103140685036021010340b960b402c02408591034000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 867306187 1250 867304937 867304967
    0x81c0509040e100c030b0306070206010513090816060f052215020309330a090503130b0d0b01021b1504082a3708030d0606031d0706 58
    0x26030380030031107806401e001c3c04000180c540d00015100c400da1030041c04035000c5441e280d02a50202080201d229000030340541580c10441d0810000008201801c0c003034040840f00404007080400c2944500c0c0c0b018850042d640d01c1150140000c084181400040301e00480e000500840010f04040d001d203240300001c0e4a0902680c80b2080c0140c05005420a0f41c2c803e503003018480c2c1c070402e102a03206900315035480f00c0e81444034403960441d03495000e8101b0813102a142244003544e81d04c900c010401d0400c12a80128028038821400ca5030340d401d410860b80285906401260401ca02a48558800303c2c0b1032102030080c7d1401c4107402c07044030504c600c8120b1116445121001040b0120740c4c098100002048205245140030b0b04500e001c6140c2038280c6110461406080c2d4035070040049074881e1a181c040e80e0740807000b07500c070040c2c4004420461100d9808030183d40000103600d00144002c4d041a8151035641d201031000d413034928100801c02c82141d00d4a035680c4c01c5a03c0502a080c440d240811403600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 867307437 1250 867306187 867306191
    0x30c05090109024e040b0c07050703170c0d12050702150a0b180a15060f021c02011b030e0c01110d030213050405090a0501140705040512070f080610081c050904 70
    0x41310072a44001d9001d01d4a0b90404500c00004000030000c002520076440f1640d02c00c454105041540d070b0582d00c440c50f0000030000e030381d004040070030240280c040d5100c0803c906e04460b0261003189014010303402642700713102d4950506000981c01400010098070440ba401001c0d88950313643d0342c3c40401042c0c801500741d48007211403003031071840f107944200502941903084002109142c3d40700c0346203034211580c020300070b000000a10840c0e25401140003040788250004012034842c07007900480c010011380f11261414122948040c0e1090b500d81e000e2a1408580000c5640340c1701582c00541c3d04820140f01041c41380e0044001d48440ba10980103026426801c0c1c42016201351a0340000701a107000702e03441c80340ca500500b03d100600409001e800135280c6900341e4443c1c5401c1801c40200a03208a0003524082c211400762000c1955040200100074440b0150316101070b610f030950181c0352182a82c201d20580c0c86083c020947c1c07900481c50480040031690b200c440c0246040d019110342e00007050041e4056 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 867308687 1250 867307437 867307537
    0x705010b191a1e0301080f0109080301031b0806090c04061703030c0d0605032b03141501110d030902010810080a2a030606051c0506010306090f050106030c0509010902 73
    0x100100340e10740403c0b040040f68075283e42c10320a8803441c1a0340ca65442469a042030b4800d001700380e0200481341902e42140b01010001d1070030002d1a540c0320f0f2a40003d4891003980100302c1452000f00310303491000001c0b01d05021859a031810841059030548400945410810103e1920035400008181d40101c050021801590b10000242081c0c030080010112820310701f140d80f184403011203000f800c0d48042c1030812201c1900c034543d04030f581004020090300480801c11481d030340c1c043c040040c7e140724407000312043c000111030010081c1c110403804a01048141c5c01050704041445642da0603290618010410031070943ca035446001e08001c5c04010307e000616184800e20b010540f00ca01a602440c0003049461502c414880c41c000e10710300f1035525502d4a42d0385000640e000c94110b0450380c00250109004002d414800140d04003100300502a42c6400310000402c0900b071098411150112103c80c4580ea8884d12030040c5c0c4120940c1d850b4030a00d421440321155205442200b0380c40381700009113400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 867309937 1250 867308687 867308707
    0x909030912110a0915260105010b09030f06010b090405070309230f031312170414030c15071205090a030606051908070308071a0703020705010b191a 65
    0x8003241c81c16155041e451002084500345540c00500408220000300111111050703a41e01508190141040d100300c1e00b02810880b02c220640f0841c8800d00b02d000b00095652054620095841100400c2c024000e0f55883c003540303140440d030181281d080405540c0f908120404210050038001c05410605036214011400714040340321011490300254001d1007074a468541c0140740000209084105500c20807462444070702c1c0040110031910400300c06040e000051810107103aa1210300501a06000400c3c00241e0061182d882e01d650401035003a954100f01c2c01c420f001ca04034652505800c020810402e0800054401c034004c4d0710103042d0300d09207040010203000900c0d21b0341182d2065401076103c1205002600d458514608024080c100103903405140000864880d0000d01c03001d000c19201281c48418040c440814502c0c68000700b075840f0103841c0c100e001900a4002c118181c40035807a24000088a08150342a08441d503250b010108000f0b02c2d140c0403420105850329656003510052000c1542 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 867311187 1250 867309937 867309959
    0x405071a130617010503011803180902270a0614130e0702010b041103090a03120609090b040302060601030902060415020a080c06250503180316083109090309 69
    0x5400306a0b5202030780f02102151040c4683c043e00524400d034508809200b90502c00f100da202c82540c141031880c01d8000d0000e071580003805551010902600010340342c50030515409620312215081d0780000440041c40301440300d008100d0041d00c02046141407590400784d0304002038031034024030320003020060351101c07818002c0c001c0a40310200981e44944122100d8a050301034030303184043c81d030300c0744c6e0551400c407030310070f5880c80380f0900078042c0495031001841e64852500008003510000344144451034091502b08514402203c0c01d5006004a00200c2d91542c4039000b04124144c0040c1031340d0505041c4401d621810003010310300e9041d13128094242c2c3c00556410301070460000107902500262820701c8414070b0420841040190224400314949599034001040d40e800c80e1541c9a1340c04a440640c40b20351451043e00180703c9400d00c1d9034a26401c010624008120701035008112140e0a842c1d409401030342503d0280440d120f11140d0418001c040070740c2c5c8000300e03d60192038400380071a614021060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 867312437 1250 867311187 867311189
    0x50d02060c0f161404092003070314030d050105010302070f080d09060603050109020f01020d0516141b0102010b18041115030705120c04060c0201080c0f04080303011a030405071a13 79
    0x10980f442002085075030840b03125181e125805a506029200d510b1303a4460001c0740e03540e522200c1c41c41b43c100d50171043e2010802407014590080d11080c4910001c400650799030450001c0d00482814140041500c0d403090080c2c80e8440e61001806018142582d40d0b0161500448040ca001c00d80d90345505e00441d6541c000e500045019400011781c0560314018040202e42c2d03e6011815548406403222580c1e500004850002d25803400110450700700785065404e400c600c4c3c210b0b16561041080c0306c0200ea00c018410f08400303c00360000c2002c850194240300c0e07442860011281c483c029200000c001c5403450342c4240d02c5840017006e00001d00d25116a1300d116030801e4a4a200207a000b159103420740e80207016181d0409080e1042070300346403910a0040c11001c181c2d4000f4104800640461070b55100081590011480c5c01d5285d070f1503503150002c1596a030401d02c9000e880010210b80e00310074001340c40072207005503000300c058000b282c2003c0e00f500601d107500608506250040103e0410000c1000f4944 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 867313687 1250 867312437 867312463
    0x9010f11011a15030f010e070302092e0e151617030a060b270111030409150e0f18030c03070803240906010c03090e040b16020601050d02060c0f 63
    0x4507809034002c103101c4802d103444084600d1007801c01c00d001e0701c1c0e8280b001e0380d0304480b4100343e804030554644d18110b001e801640c0c14290440b080707400c44080d12050650514050f003207d201c0080714a0714005c2200c1940d00440d9098001888040704801c0000140007420744c06514440032120300115a290006880d03080d80d0211560004400e1200302d08241c051200209015080141081c405000c1d092000440f2150070130801105107d80c0c2d0b40743d0045460002c8000c2c40c0050340d4940d6980c201c45006800c1415800085260216012502403103c2c071901d40250650380005a1542e070303074244000c4080c1a1411000343e44418010b40300c40c3e41040000f011404c1c8110301164607400c0c2041c040c801d842c501c07084011120302c61400c0c0300c00e40c1c54111815500c22401d1800c0740340304603142416524500b49030400000c04600f2801c10041c0040704100320300813021003804400305100280101d803220390030701465034403011040d0700ca0090b18041c0d0151000c4582c4409465103490328400c03052821a503c0001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 867314937 1250 867313687 867313721
    0x324060203031b03040c060507061503060501050f0402030c0a080601021207121434140325050a08031018060302030705010302090a170a1e11010c02030309010f1101 72
    0x3e00803414000c0c0700094800140002d0450500d40e80d4031512503060b000c1c40c4200103002c82d1000510499812000d42c406c048074404241540342e06200c03000d48002d002d000d000798a4081c1101060400b482103a1055004a5480d8108003199008551a05014001078110312070032208604024044001309200c42c810056000c5c0401882400b81c86c1d40d00d20075000307000201c10b1264410310003680400070340d03000d03041c4000f40c503032462140030040b0f001c11170802a01250504041d894000d40010040004d818602c6100c080c5a003094019086600c66480c000e005030040034076a070000326820041c58015010b00e0600035032940710070480d2280482d51100280140e182c450800950400f4000c1e034001e84401c0c41c084d4a000d00030b50203d1801003061090b40700c0340c8524178103403140e071005100c3e5482e441d40c8500340520802c03040c000326030710004a6070141e8600034607040380c940039801580c5100c03e00e540640034500300308502c0c00560703401211410020034409111042c011303684007889000544ca22000d51 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 867316187 1250 867314937 867314941
    0xa0b090c0a030b0108060108041203110f12010905061e04090602030412090b0f0417030d0203040309030b0a0c0f0503070207150908060c130b0703121a0f04050412032406020303 77
    0x5003618903c914560500003401c0500a880c2d81c0010256070050704407180c40000c40d070700d510072401064450510b194010300400c202540b00b811030010b22508a101c0e00072400b40e41c0b540e07100d0702100c8040e6002c50348030b02c8070400801071070300f001c00c2c0400070360380140002202042e5480c1e03074090307900c01c03101110200300303881c0d1026003036402c0030080000d082c3c8070280c241000903901040000b07108900420701544940e496540e9011410401c4414500500b24150348a041c40d28028280c600f82d804116940c030420000108401c5151041030801181a030314014a14a4084203640710b40c0003134044401c5000303ca0b004510b5945c0310501c0125558144d5803125140c6c6088280360401202a00000d11340800b00040d401c0401201c2c800390540c0c00080d45190355810038039080c0c91030500c440109849900b00112042d65100a0035400201042940c075640210446000c00089403000c4400a02c2070184d602e54450345442035000350744000c44003281c1c1c02c40c203002c00170f0007100c800103600600040e480001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 867317437 1250 867316187 867316207
    0x7170a0609080c190c0501030b030a0213020408100c020703082d090411040e0601050a110106060815030307030c11120304090203040311061b0a050409020c0c030f240a0b090c 76
    0x321920140c03192041c1000c500341d00c5d6590000035001442424100742d04c4d504d03941219901845048080f59008021031585110b40c000c400194001d445040800d014007000c03103501d290140680240100c40794081c2852900b1130340e0b00d0358540c0000c400740822610102c1d8003c132181c080c044040b80030390380403041c42d00c0d8180d00e8200802c0e669051600818801c06000c20408503c0302d000d80c03a00b08600f401d00c07a40b5400700200442da40326010500400d5582008800a261a000502c003400789028040110040440c0c5007407607580e101e1120002e00103190140888003141e100b041c4030000c1c4000502d0009903403482c82506181d900150807045a0b542c2c0041400109900062016034a0000c1005450349127030001041e05403103011030aa19540f800007440a2040340f03d0012540500b100303003803c548491418408566480852000900078070400441190740040041c28140c09500355003410000140008560359400018000150060322961380303004560f5900c0c803042c41046440105516440b0140e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 867318687 1250 867317437 867317443
    0xf0702030a0b1909150c03020f03100302011701140f12030703030f06050d0201171314030307031d0d0c02030a050a030c060b041a041503080313030212040807170a0609080c 75
    0x1801003007191502600d400005d03803211120240031036880c00003c81c009980c100303030302911130326420180f009000070401060f50002400d0b041602c0c001e80e6070300e1103190f845805030031000e02805020302640011510140340d14052031580d22185010b02501211142c0d00707401031641c0c1109000302c0100f900d54400e40803c4c4040e2080c540101000c03101c4824a489540010781180f80d0b04820401200c100320004460304000c01c03164003a291712a0000354080c2040c95141d80300c1d0003da6a04000905084040c3c0c000f4814420362540d40d48420050300c0f6602059800b61000400d08100701c0c0c0502500740300001240b424054904854005c1c0c4400c40070103221308d48042254085400c0d60710451410240403400c18100a045c815032400b61800180c502080c038042954941c26440102905800001c205881c6450a450304000d44a90220351450760b5201144449004500455440758000318042007d03009a801e151444030101050703c07013a00715a12480706a5407100810b56607118002a10849a1020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 867319937 1250 867318687 867318721
    0xb0c031210150c080702061602040f0509060105010e030f030c011b0903030203040905130212160501030b0f060703090902041d060301052520072402030703050f0702030a0b 75
    0x2100c080c01c44030b060403a4541c1d0071821101d180304000718040b02408220601c022106483d4004040c070741c841950f09106040c0e804d440c4002c90040f4104141403c40301c80f6409a9030248480101800d1140c0c00c220044807141e60741302c041076061207528001121001c0034001450120f00100c00860b1800115842585004d91080220208141d2404c208042036000c0262020781c4c04002002c56a500e854111907090000e0782806940580c0b40001c0344410400040d4039180150b000c54008000e43e90782005600702c40300c1c83d15840e0008250f4540700030902c8d14000502800b0310904008440c562548080000c90704281c00060a00c5503000001405550040c0c1250b80504124001c0c40305142c8000b118256946040d05000000504480c12086170700950300701407130030450314100100d1182c181c641c55540f146486680c49640c40752000190310104440404001042034005510b07221482e5000c036030581c8290404e141c100c100f80403680059905206001c0e146c0e010302401c0c2540e003402c0405604030f0002d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 867321187 1250 867319937 867319951
    0x61802091b030126160314010e0307080912070609090f020910140903160f0b0a020a0f0f0f05010915020a140d020702041d010b011815090b0c0312 64
    0x140401e15860465041c040380e041d1841210310f007401c800507807401c51448080603420550f5000b0010207882c1d01c90380200c4802141d000340450000304030541002401c0301c14a01c00710115800070001240401c43c42c00050120500240020500c500078803030359420404660800e000046401c1020406160280640c150540358650114501143c40c00000c0d840c1e2000c0400da014004070036020f42c01d0840d0b88040d01c1101c1405800d8680d4424032001c08038140146014081c7c40400030b549c04280540c082040c0d80441c0e200703400800600c13200ea1141382e1107103c4810200c1c2c0e500c0249590800050341408030725085803182001040c47d150700d1405070106000d00c001c2000d041d2060282c0f500060340406504500018501c1e00340c9d58203210042000680b03e6504040c0d0040c0c18a8001c04241111101e10030303440d11910020800e100040c0011108078215200900c9000e040c1705040c004046425030030309a02d0b90502b81185240d81d1000002c9080c0c110550404994101040ca02e00c0c503030b449107016030302086c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 867322437 1250 867321187 867321211
    0xe0a050c090d021011060703230402030706110304050607060504120e1c05010b060c240129071406010512070b03012d080102040501030c05120a0b04020706180209 71
    0x1949201046200710a40c40203449085090700d219965400b1780000740140304510300750b460501d050b080c083c018000700d54a402c800c072281c80300303603014010881555018a074001c000c2c26030640340c000111503020007588200894001008001078075650680200311a9201d00c9020980d807510307040c08008803015105a5040c8045820900e5256450400100d00f2076512000f0100c0c0380b410742001030043c031641d80080e400000024054221803c0010141400490f41e01305c0c084041134500d411060503421b11440d16104110010000d842c2454024450b5089052044a041403d076445c0c0f05140110640c54401d25082400140502d0900300d80e0b10708100e8000c402081d4480c40d10041000b507210510854000c0c9184418200c0007803000f060b078501001c0b2903005550740396144ca11140c000c0d40300d40700e480e01180ca4030846c0310a4500400a4642e04203174401e1200460b80e030071000303002410f007403d403560388030380c0c20088403001503014890070034082100d8043c20a2100148140903401801515400c0c18203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 867323687 1250 867322437 867322447
    0x60423040b0303030f1b09031b10050f0702040f02120f040c06110a06020a020a0c0f061b120c0809040f02030a0b0904050d0e030c0901140a0b160605060a0503070e0a050c 74
    0x1001c1a6000d9406c8000c04079800c0b04420385c10000380050190046440e810700803894501c0b540003605034050711000003101ca800581600540c2030310070744030312072240d489098140030310405460180d003c0c1c2003822a00001520302940c4580680360b41c10200d4115982110f00380500c81400751051404019100505103c0600d44140c0c0c80c49603200030103c4000c0c40070f900002d81041c03c0348203000050311203500ca04070f414226280c018981d110b06117070044500184c00000380c890503114030450700e8249900401b0000b48132001e10300842d01c040c5400c005444000040001090036100c0b4495804682d028460060b12424164000401c2d6141e5130f4801d0301c6210040306100c0820030200e151b90070401d01e4107040300e0808000001c13a091020498446900001e403100000d204807200c1c03040c120a0f03501b100d1901e00c0b1921003a84040314011303900603864401c120000440014000d070720141d009a40280742e00b5150399240c002a14041e46a004004109200c3d0140148401c0301d0054503044145401294200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 867324937 1250 867323687 867323701
    0x203010b090d082811160303081f0f030209100b04050616200f0a0f060e0301020d0c11071409072d0822110d02060423040b030303 57
    0x240240039410740704510288050702008040001c40303400460502c840400e5484c03616401c02681d50a48404000c2141a0310880301c022001c43c81300384041c02490100c0c103243c02c5450458030240010240301d84c11481c501e03031003403490400200380000e01441071002e80e0745046205004a080e0003034014039546172030000500c1041e04000c181c2e025500180e40041d11010001c03444160a5103502c4040c140c0c039a101c01103480d0020003241030303500c024207a41c00100341d60701c6e0092100c04074051085200150141d823003401424482c40a81d03030750940c0100050304048440e02440c0840e56420700e041e0104201c4002d611801c003040c05100010450940c00510840e00000801c108060003827136402080f1900442400000554990288020010141011551005c04090f1503100140d4120707580e40707000c407100640e19184482e4402d160364040c0c00300402d44480d00510212008400049038002010b0001040407156607050080c44950b5a00b50030803110104203200455501c0340185009030010000c1101c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 867326187 1250 867324937 867324959
    0x1317071a071b0b031929190806130c1a07020103020a1b0b071d0d0605070c0210081b0405010c0b04030519050c010b090708011a07140307060f020301 65
    0x16908001958545850b1150300d400751401a00701440340500881800031035049183c0004131401c40301c0c0104080b002c03110014207004614038150002c00021104030440b418010111441020001c5c280f0742175580340e85845080c04812604a15102d504400070000e01c041e0f800e0110050400f075107441004044289081528421414003038149600047c400050500c240104400c00115550981ca800d90519141c00f1828060342c55100254226020710640440c00c2e2401d09511030043c0510b94509040d51080b0150800810a000380b1004001201c0940c6540080401040322030340d0350891480c0103584030030b004c0e030100d600304410442032000b4441641c2003148113450355042164141c15548a00c0c046038180b0035108406508080701690241007a00b00000d803c41c40661002442980364940c01e200c0c50441c200c980000060401c801000604040c0f1120f030b40a140c416011407600d91591241c101010041d4240c09103540006000418840e0611a081e0350b04c0c1c0c1000f0649c507652500940b242 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 867327437 1250 867326187 867326197
    0xe010302010c0b15061b120f0904050903040503150103052e1518060e0c030c0a120e010c1709070308091207080105040c1a04050a030303090501021317071a 68
    0xa5151602044000085501c04241694005c01c501e40c1d031174070100305801c1c200210524046a10418400b18100c0c441001038507a01c820000100d41014449c108100182c070000e40003150b980820070012449031000c2c0310000030201e000c0740700c0040b945140b4005240c05149002620305400f8029a2040307842c800c44102008541c82d18007007a016012813035010403143c00d612209050080c1095544000f6903500100c044a40034540c03440e283d0f803004040c1a06101c211441500c0c1801080b41c2c1c8401409010400903d40206c6c80c0026181030001415084407060385100c070224010280c10001410303000701c4d1540c000503e40207004800d2555a0b240780600410300d04512801c200c8983c00072800341000100014010301000f444142800d05080914070040d028034150103107480d005140c503030524001c1702c0841c1d00c0a0b101c41075180c03450b1003c80081840c42d00440b259502080000382540400710114080c102901d00d05802105428900e890400780f40d2060740150211000d480106202d40c040e60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 867328687 1250 867327437 867327443
    0x2160303050403200706021002040f050108041511030f0a022701110a061506090e010605070204060503010510150f0c0219030503040b040812040b0313110a0617010e010302010c 77
    0x4034054440e0f140a5654514885090041d4088100c52403501c420005444003100c205800381c440340f0110000c07c07030030383c0f10310300070b15400c503691000802c80c0e540303c0d42490764010b000300303604000403120310403000a4541ca4981d5031004203012041c085148141000c15030810f441240462030708001d0740c622301d809910317810414074042d084072607058281d008407004520007074001c080d680d81d10345034a0240c008040380740d040300c0c3c0c2c00c101c000c2c04110640166501c00507030300501070440c144e84c6428030486450340400700487c1c015848100c00541030b1024010b07a40105402c4c000c0070241e074108005d0102d064290807031003080100303804400441c140c002070011041501941c50012201000455000200c090343c0002c0c1035100000e0b000505070880d0340504195010070b003d03901c42144010041e80a80510f0040100c002402c101151103846441c0314000180c3c850847e45102c0c10b9180c0004425500503413000d000304008011904c1d04656410b00140035081d0f5142c261015410b40e00003e058200c401401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 867329937 1250 867328687 867328691
    0x60f140a0b040e0313030507141e03030403200f01140d020c0a08070b01080606091b03060f100c02040b0a0812070f020a0308042301081906080d030204081002160303 72
    0x880410384840c3c002060b10712079842240d9a0350300d2954001d00301005e0388401e441c00c0c0944e640128040b05010020840944000c0c80301ca020360034040340c4000402600c004039450300c0104030020002d1300d202410a0061b0b61900702100344102c3c2010700c050480039004803810800c01c0c1e40001f400421550503100340480d004001a01d40f1681c0c80d030140381c500400005040c8120100d1080100400e141c40d01c1d05a999250985140d03481c0c900902400c224180c0346441d8030f07011101c4440071031082001450780722074024400b901100d08000450500416141d450000801b0349810780107504181c002da900002041c0c1e08948028548003003503455135182607010140d110700107900c3c2d0078000b0142a04824a40080460003503994918100d1266401880350804038240041c080c0000103403c030410b251782a068461034050380d10b0b652801c004240210000c2c2c65180d0701c04000c690454100f000e008520203d480050744c0f2814088482c1c50f0501c0d0b64207481c0e940b0f00400001107006144801142515490b00700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 867331187 1250 867329937 867329951
    0x1a0901020a0c0b092d09071709010506120307120819141608041101050309030f0d0b0f090705040302063a0b18061201060509040807060f140a 62
    0x101c1c181210340c400603040403041030020981c602518001d000c1d164080340c26500904d04030494030f0500818440301d03da42c5100c03018208840c1802c64119921200504d08030740086040c1c5015403002605441c1254180c2d9600c0c104900b604004010502d5120060000c40c10304160360750386d0031880e203541c000100f002070340300100d284040d1480d0010092003002c0e10901203504030000e41e84c0b41300c1c070869180f00000c0004101119640c002c44200303010301d0f0001200700e698558030380150389a61010788980302d10300c4104580001032601d40043c010040d0400c00205030340c04850308110a08017030703d12181c400c02102d03091000250700003040f28200c07036060303800e0342d12401400c680c00d80f0300000314803c4c4030614901c4459420b03d0941e6407800a155034142c01003000005c00014485880f000d51000b803012a0b202000c0b0301c5a00d003003c8034004c50b4608000114602e0707160310208040d07140076102101d41c001c000c5528400c1060794004d00c015081109810018107a01c1c2024402181c005424105030381d56520f1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 867332437 1250 867331187 867331189
    0x7080c0c030a050105150d0812270105090f06100e04050102040b0d02090915030a021207240207080d0c03030f09020a1d0c031501081807170607091a09 66
    0x4405030003a00c0c02015508004801e060142c080c003001c851041400d0042c0b414084203141c0210440c0e80e4035000b91146080040f0540d804502a002502d072030f8a00c0c98040c0040102c100883d0301c006803403417610021569040100140f8601810f119103000c2d290003201c20402e040c0741d11030f5500111401c2c0d084140c090b4441d42440c0b40244100c2d000080480030014621150401e15001003891680642d0303070740c50541d614403070f0100801104803d00da1503001604c1c0c10f0051300e0179100701840903150a050f1561103941d5094043d0300d05012a50000d07807100d060280d240c2c5a010311041d001001d808002e0450480700000c014103603d1529001000c2c1982d41d408003200c500190b000c18141030703005d0140c583e825181d10941c0d40c540400c801404000c100706001031000503101d01524000c20b005014508031105601c01540c06c0800208501d9961811000002c2052402c101000007801c103458038824101d60b0501d01400c0181c02030201c018401a01d8003008a1407500e07814589003140d02200c01e4131121340380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 867333687 1250 867332437 867332443
    0x70918030f050d4d0a0315080c030d110604080f120f01090f091e14010609020304020120070303030c030b1306091b0804060218030f0d1b0807080c 64
    0x2000040c452443c0c2102d1180307120a88209115860710803c0808058507282c4000d941050340e4813440108080070503042d0780540c2000f02805d11501942030200781c030030030b07400c1c07072081c0382d51036404590309034401c09070009182010b00c0196558100c03460b004001d100181c6480f41d682c1e2010b0030003801032000280c005031100138141650540780024440244504140d90855a494400e014a0307154507c0d200b010707912410903100d509046a8401150760320010a024085c00c0720803924400c0ea090320f4205485642c440082c4a010081d0003a403038016224101800010300e203401d0500d2000881820140050010800081745400c6030b17410701d000300b1400002c81d002c8014080b00b03858181c002c0c4501040c00780080468210205841c0e00800230040b1442c059103090054200c1103800000c0307022207003c507020500540040c83c08840d100200d072000e0035100c002c00c2c0b07003c1c10a117550307440d604074170a00300109a00015145991007103d982425103101610f481c03d1510800000070094a0000b604d1840d484c818 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 867334937 1250 867333687 867333697
    0x30f06120c010e011b03090816030c1211120a1a010303021c1206121412040909051c05120c030915180f100605030d0903020105090d020909030c070918030f05 69
    0x4201280032104d092402a00d0790301f40e03018400300380c021256118500a88042c1c060110b0707400c030170900400c1d498041c019041a9104105680e825022050680c0c0c1e521100d0080c02001c1190b0000e00e0711103e981070a40d6074a000c0c1100c4040450111300400100e0f50000b800c1c01c1031005407180d00a00e06400d80140c070390038030391a0790018442c1415000a880e03041e6040c0310741c10354010101c19416040c22000780d44c4964440d0f0742d0081042d000c0c4401d02c100030079540042c83c050f100b0f80072034030052001e0300844410307142c01400b400001c000240d4a54174110000780e4070b07009034003028190300f1420b00c0c1c03d6450700e1385031040b040d00d14000f03180001008001715031211b4160311082000d07600840e907688a03241c0c64082e0404000c1400f07040c201c000495040000d00350400c43c07842e0740d03500109070440e0300460302a0f004100040d400a0307103202c4000503a844a4042e0300896041004503500c00d881c400550030204075a1140080d5460004a500404203880c40750580940c03600c1c2c408103c600070002580d050140c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 867336187 1250 867334937 867334967
    0x9010e070e040e0a0b0609060a170a0c090603030e18060f0a150507031e02030d0e01020d0e1011090901030209100308070803041a04021315170102030f06120c010e01 72
    0x10a90780c0c41c50340301c0c0411300b403283e90f00407407070341003582d403004103002d0445401d0754131030303006000e4010410004803258400e8a01c4c504160603280c4036462a21000a41c10b01500300030b0380107540740310030420140c00400d40e010300d4a05488030044030040320400f4102c5100188041d001d10300180340b16480e0394603000341c503001d00010040c061500c840318200510729003002000f100031070014880e10304403070140c000151200800754025441d0160702e00701c0390040c0c150540c8841566400748103c0500307100030300801c9043d2080000821086000302d1031882541c01d40d0741180740c142130802c0b103080e40d80c8504d4a414103681e01030f105180a03450354601642c6512040e8006422104042402f0f020000b030800190300460092001a203038254074030200700501401e4400960001880039000302140540d040100c0b5a9461a40d960f040d0b03980c0c04003801070300c20a801d407448903580042000704400c004038920340c010009444100d0501501d240740c0f0b9039425002400d5040c48201000781115070704c504483c0b0b642503c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 867337437 1250 867336187 867336191
    0x1090506011e0f0b12062d0604030605070c0302060714040b0a02070b03010609080c09010b070303090606081f05070c020d030503060a24080c0c0a11150f0a0201050c070209010e070e04 80
    0x9038034042d0ba0520342140d000403201c0c5c0f00d2a0045002441c0107104100310032117041928800300c19a080c0c0c41c070380c099043d151380c2d000101407100101044d41441790701d12071029500e8403100c240803490b0007402d02200400354010b02c86100d000d0400c4410741015142a25007060032030344d403041e80c14010b0b81b07080d03c0ca034000c40380300c4800800403a213582c1c4411960101c4680c3d40844020411240810071217000034040e0440299040c0483c00c0400d10a030000704805004039800034060740c4411007581800000c0c2c001c01c0301104009002080101c0b64480d00d5070200d09442c184c0c49070300791540002d43c04200c100f0040e040000101c0403541c213a843c0c41ea0100100341c104075110b40c442d071005841c905800c00302c200c180480c1007580051610a0b00d04101d5030303501402400b50035844415500c07a2415140b049210360405098080c070b00034103521000402a80700c1070a02661901d45c400300003400d4410080200350955014018200161502c4007458150341501d0101d0006640d000811a40312036109000d40d0700134 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 867338687 1250 867337437 867337439
    0x106090203131502070201141c0608010c2303060111161d060a031707080403050105180706050a0203040b3712020702030a0314070605101701090506011e0f 68
    0x4042c1034100c1549100b0f41030800c07a0003540003410700720700a280d00070b40883c85509905441c01c16000080c102800e201d840f401545d281c0410b0701044602c0c07900455500d030f542d011a030a03010303000210a03061741d020461540741c025200042c03000900001d8a07803414040700302d01c401d0b900181230107040c4c514a60695940c00340d0b0350380c05e00038607072280e40e00f4040c45c10301419002c14900c0c01d082d0074180607640c001c1d400c0c180e201102d0562074466403101c8000d54100c2428403010000038400e001d2a8041c80650520340076203119001082c2c1003c2042d8420402d01c48104208c0340d00b02e80101c181c40444030303c01c040c0c075100c940c02c1600e9962148422090000415080303040300081e884d10f01701c0c1510f840c083d0f88411074002400602c004034400c06d0030296043c0d0090050300c000a203e01404044c5960587d05a420b00342c0d43d0740c40c1e8081d95000c2c2c910309200b9119180c20700000000c10344103030b60b514142000b800b682d001a00e030f99841c4c21060050300c051759007520703401000325401d00d0444000c0448004d151501c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 867339937 1250 867338687 867338701
    0x1020304230901170706051e1c0b030a0b04030804060b190e0612120c0c090f010e0708060f09060f10030509070801290d200910080c010e030106090203 66
    0x100c0c0900210380701d00d09907000850300549584c60b06003180d0f0580020a1618140002555542c10511000300c455244041400c0074400e014040d00d61038980c410f0014502e0703014540101070718200b082d543e01940c8200c1412022440380d0948641107509411718010f180c03074904011000e021038400d000d0700130040fa51268021040c1c03c924404480039062202a251a85001c01c5070f0340d02c0c41da44444041d4480a0055810407400000701600d003039400c00c0310080003035100492003070141150540000304007407004000c4016402500c2e40d0010107860100000e1801c0400070b41c00361000307074003140500f0f604400210103031581c5902c020440402800301143c0d4006d6007006025090403a0500d00d2030040c40d5000503101014000e0001852010742d101181011a240040d450400f6100c810b6000e06800403071008240b01c0c10703185202483c034208070b01040c0c20141c244180c215000e0300c40040100910010007540e84041000103141009103402c0745248401e500003400351481c0d400c0b03005014400414030403a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 867341187 1250 867339937 867339989
    0x20906091e01030e0708101109030d020304030308011a0d09051005090c0301060e04050307080a051e040302190e01090908090622091109010305040201031518060503061003030e01020304 81
    0x16000903a400d0082d0304d0416903081c3c40340e40c68030803199280d104d211401d614400d0307908a10700000c010803402e41450507041c0028a01141941031102582000a0601c2419481040c6502601c010000c1c40103401150036064450b1050390740e882c45260741d400541c01007107024004101d002240c420240803e0400342d000a4a80b001403000034429880d00300009107038081d1700a800d10031034016010710b0800d801c58542c078000d50b20a26081c4e003046010040c0403c1c4001d03500602d45804482c030040347c1c8560441c418440800451031402e04400307907104040202181c05d0060740c0c1900c03c04000810040c04c00d2074805640c0c01400303e0694003101c0070440c101032410003030000140d000324010394a4050b40d6940d000040340c0e00c40301c90b0002c8050070840c000d0154041d1b00601e4010b8810f140002c0c1072460f603070b5910103e41044d080310b04013810000002c0c07512940d500406000c2d02040b00a89418103089828a00300c011a2100600b840800806000168000d005a600410f0340d02c0c0c1c45801c0917003503c28520 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 867342437 1250 867341187 867341239
    0x50411031005090316030207081005010f270b04090b190606050307090e040201120e1b04061202090c0712020a1506050f09190e0705040c0219030302090609 68
    0x8041d1291840000150005005040c01212a203000c0c603d414480034140f00f4514102c07a0641c1507204400c8009101c03042044023039158444a0400542541819048046180294000080c5c40300c448010f4580c1d84034004035034640103814900050504d80d840c01310780500100301010344a89000c81c1000240e80d007061010a000808107020407045444d840301703030340380d0000341c54003800a00181d03000d000c00144101c1031a04035005042c0842d00c0740841556400f5103c070041501c442e90403d20404601c4584003040d80a080011542800014100200000744501099010f48240c940b84c0106088000c1758080321030664012a69544e0490b0f900c1c0080d41d1981044012214903413640d03502e468240191089505441005240381035500c6440108403003102c0250140b1001d10341d402c140340781c00000d0300c10352014001d840e0182526904e000104002c680c4100914010764000b02d1020010840704101e13504555414200140c507200c0071004504a4055080060740080303160001e05001801665900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 867343687 1250 867342437 867342439
    0x4050c030d2316120e090a0c030501060e03340b0c0714330c010e16030305090118090f05060f040e0331031a0a020a0906050913050411 59
    0x1c2042d8442e204408030a10a08189a0103c550490340b5030008010007000002c214252400422050080c00000e02109059421016031940c4401a075001c03505806407600500207410031a03844560314010980317403403801400c4852030100340114000030366100c04901d003c1141c1c00d08929650740380c0c054800aa0300c0050480e48910560800088000ca41500e2408113840905820812001542854010380d410607081500a81d142c81606401804c00d0162004826042c004500c80341a0601c203810a8103000c240d0106000c00541400171030b07009011a5507109003032904032030940440c02000704000031074002090072410700c0031300821180150000c3e4003484048070180090740c40c074010402100da068808448540052105d04841e80d00c518501c081c0624698030104110a6000f10080f49010350f0000c86104c1091511403840a90140d007499001c000440118600804a000981070504a22654080190010348580e8640725145101658540803605100c00d0500c3c2c5400d0700072001c002281 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 867344937 1250 867343687 867343727
    0x30a0206011a0f0a0e010e04150501030606050c0c1c050312010609060c050d08060f060316140c120a03060e090c01110313120204060f0e041e1a04050c030d 68
    0x2002ca210490080b00c007034400150429141080940e001e8841481003444a81440200080240d450b203480c0a01c045441e0303907004c0703201d01a0500001408444181d0001e10070000c080c0b00302c2c16480c400052001018000f164818054440040c813802d00300710305540205580800300d50186008181c2d002513068a10a440740a1426141c100840d000c4100700300140c41944041c50500034503018a00c2140c01500c050550240c0d00c50210120b2029841607902a241c2c2e03010940420344c203540040c50101c08002e0303101051818041522240ea50586e0608000c002480050b1400c82a402a88000010041054600f480c0d2600d000c00c42c0c1c40d0140c281000c1e0104407828a028031420000c4103d031213550114002e1015142001c04000140b569858102c1c4c00c107948241c081655040509060010f0440419000b4180740c6443c0c006882da010040d4031118054503502c500026070910010030041c59210070100c199a20340c00c01501d0700c6603040805030940200c000c0e80386041c0c2e1200101c1c548040e00141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 867346187 1250 867344937 867344969
    0xc030e060a0f0f02030d090516051525120c0c0504050712021b03070c0906080102030408040b0d0f0615140414100905040510170a02090c0c0f030a020601 67
    0xc0c0a51445041c00040c0058120640140311502a5144602a0314548102e1741041d10700380880046880c204402d030380c80e6000100c01104502003030002c10103043c09440d591202c0c0c440c120394a6141c05060b40001d0306501446050000d102c5200c1e00700203254000c00744211a0030203101c00f91040b01d4550f0151102805503601007101e0403d80030750f80c050300d06541e0340c0d261002c2e0550319500a41100300340c40d04140c03840101021100f81080545065406124400b04041c5044451011501950b00540707090740140f0030000400c143c5405d903405c4440d2620400d58076059400c2c0350b40141005e56500800e03500e400c44c041018000418907850080380c030b44681018030b60320f10451140d405544103402c544450510050710714103014034108070501181c1409010385840d10b0005042d0398044034000c0c0104981d2404105c01c9201007101c0d910302d48a600900f0644d001e5401198002c40000d1110f082e0900001f906500443c0070400e100b80f0795004002d0b05d0326551030000094848c90288240045940e519003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 867347437 1250 867346187 867346189
    0x215040f141203070c1407090c02071703040320041b0f08010302151606020316141207110f0f01050901050906070f2f0c0910050105091c0f030c030e 65
    0x10b203141400703203803a015401c2d9a12400e00712003103801660308441c004000700640d41c01400420042c030140131030705008602c8902101c0001c5c600304040d031242d588115491121a11442c01000301c40a494200ca450f1902844022400103410781461035580c020f450801680d0701d1b030b682c00c41684948881c81c0e50b4002131074030030031003101c06d000203000107548841081c0c500c451000d01000100707980171506d480c05041c803840da11040102c1c1c10403a81824020390301c01c50100c910390b201003258254070180401c036080600c545008034035040000c2c124028000b440d079810051020410007918405d6802045400781101c41c01460701815042e6400d041940c203188c0840e4007040046142e501c03c4820b541d5a507a41c140260003260410304c00007010314810401c202c0e04a111040d4851f0f0029031100b00c000300140e005540a102030014000c080c0c6c03076a946102070501c5142e07440b0040700e212200454400a000c1d80343c01c00184501c41c10325000b01150b28041c00c0e9001c046d04800b00c02c2145000fa2038100340c0b03590301c0c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 867348687 1250 867347437 867347443
    0x406060e030606040504060908130315060b1206030304180b150c062806080f07080c012111070c0e01050103050408402d03120215040f14 60
    0x1030100d41c1c580c005500040880c02c0541c0003591150040b034010510040c10345540b42030390301800070301960b03920010b02030080c070480700158154080030940820150346403441441046c001d101031070a42140d002c0c0861200d590410640700905911202040140c449803c0d000040c03509140c0c01d400750040e1300720654991050001c0d40d00c0810501e0107044580d0f030b0b60301c00d10000030b03d942c0c22341c1c012600710a040c002d0320154440e040140454000920800b00c6403190349103070100300d600200c0207a206203915041a60b2008100c83c000c10f40d29940641c41140107000f0005e0010114081268180400e400e07091240d11104e0404030384c0300384c0350056180d898100450aa03041140d0143c01880d0401281c0d0181100740e89451000e03150700240d5071050a40d43d20411105100708454503a002c0c9000c2c28084840d0543c03c11500801200504c0e14030b208c240003800848440e844003030103800c40c908009641c94020b014006081542c42c00c1c0d060240317800d2a01403554507009201380c820086c045200d801c044000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 867349937 1250 867348687 867348707
    0xc02010b0a050108281d01051f05010509060c0303150111070f05130213060305100906050d080a09090603120f0302090d0b07020a05120306030c0d212606040606 70
    0x1a52290034603a00c0081001202c2c0440e072144000300817080f032580c42e001c40c0b4031070300390ba0305003111a5007240640201764a00b5a14094270520800c110f07800403140020801d4a0401283d0f000c2c2441521042c4080000386076001c0c0038428444d42c000003040003500802c0c01404031440758240c80312402d842109103025602d080c2d501441f081c800c00d130340f8244140d28080d8400980b5001e84030703015145c03144149400024080540c421000310b51500c090042c16540820b8020141c41882010403601385040005502c5500441e4080c0113143d00068004205100309444009400b0503d41404260703940c0c5080c103440035200420b82c2c0040d51800125004511a000311490404000c7c844910000785880d00c03d5000c0f0060720302c2003548034003811000094410701c112010007440003180c2d510b07131600c60180740c180341070705280b00d00c24032001d268000026030110104030000c012200340c101580300b940055074122480da04c0ed50ba00300310f134524ac02c2020380e080c0b01d9030306c6820182c2c0c040c454141d0320041a1603003c00c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 867351187 1250 867349937 867349939
    0x5150108150c0711031522080304141c0801030c0e150f0f0307090614100c1202120d0c0e04110d0203090a020402130303030b060708180d05010f0c02010b0a05 69
    0x825000c40d5204031180064220240514a644c00c0d01d50a600040d24001142c1c946050b02040030003004020000e070517844000b2070300c64101c11100c0c551950b452011b0300c4020001442c1001100d000e100007502040700e0820401c104100f0b0000e1070310501c1c00342100b0b034244070840381c0300314404001c5404441d41c1043d40c0100c04100002c41800b561408000303c8002c490841030300090703004900001e42e0707010048000140004580014160700b8003403850710000014910038002c80c01c451003184401d600c800c0b186041600481654610400500c00700e08000319190400c104541c0806e60b684040c02d66440507007000d50644695803d8603000007800266954022007801981d001c0c44403c1c0c00c44144d400a5500c02c4040701030324440728890b400501240c11090403a440b400d00000c0920816826200b0362841c000215850303400c001d81031b0f80780706a51090301d040c2406500222620480754a60304203034552954080020322040c65861880f000500c00c82004000640c02c0c485000b0403828062049000e80d44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 867352437 1250 867351187 867351223
    0x3150507030209011b0f15090c080d02030306190302031516031a040207060209061303030801061803170921070b0301030b0121140102040608060405250e030a05150108 73
    0x2580c09025001e074013012030107441d40b49801b030b001c1000880c40c4440700300c007240c2d0b1003001500c2100da0425000c030342da01303405c060120740c4140d4140389201e40000580b43c0c000411543d000000440c3c1d40801e180940c29880207426200c1c80170f00f10080311070b58075094416260762404501d41d00c582c1400700e06941340f05549481c82805540640403d050640040075041c0c0202005894015210081446548042e002c20021584202c2c107104150340329200340d00410f17481c0341480e22607160681c02c1d200c40d00a88002002c1002242409054440c0001550721030300009008401c001982002407110328443d0880316540c0c025450041280e15107441a20f05032900080e85650980c24008582010b2041c021600d072505404228070300000c0441c45141c000c0b401d80e90026880c0c40c5000f40c041c00032a0007811107807045080c4410880701c09030808600804544900012a040e141d00106031103184082c2003094042c0070f4001900188440040ca0a01d42d41c030191804219a90741d46955440c0d02d0240300900a2039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 867353687 1250 867352437 867352457
    0x20c010f180c0e090a0b040807210203090d0609510e120304080a02060f0103120c0314160b01090903020304090b0a050402041509080d05121f0315050703020901 70
    0x901080b0f030711030303001e000d0404840c580c00722500c54050b12041240c0407100003200240010410000016092002d14541054040d421245d00040e41f20f000b0160114000d1524142c09000e020717941e08104466a00483c80d81080b24180481080c0b08820107440c15900784c8224a81e00b1900d40b00240c0004401c180e881080c004002044039006005207000a96a610802c3c0c84c0601103400e40004502903407085412a03a01c80040c2406414182c00900d40d61514440070f00400115040c04015182d91503207103465000111381e4074042d110004001e501c00135000002c070314076030140b1f024180030405600585c0903010507a602e4158105498158100600582042c0010002030081c0e0b0003099101d00c004010207101c54031180494226042a481038030104504054452a990010131003000b5142c0e1402600b082d21181d8000b5001d4801c000e120041e0450240008511307918000c280c61051035006806105650391341894076400c01702c84041c9440d0361400f0f0100d03480354003234803c4440700141a100c6995003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 867354937 1250 867353687 867353699
    0x30105281a03060a0e0118180c2c0c0a121508010902090c030402180a0902042a02060603030a050901030204090c08011505040312050c010e06010f0f0506030f010e04020310020c010f180c 81
    0x504218210010b000501c3c814110005240c41e0728040640600c0e491074002b5094480038a14000b041000b21050040380f00c103000205d02884101c2d40c03456280d06100b41e101c6ea102c203c620040c04415907000111000d44004a0581c07070640100007400d000312214501d40d16007641c2c10142c0d110a6500960000d82c1403041ba0b0282d20032500c1640c0301c00c0002001440206035004507060368560001c40c4d21152030380c1049041075403800e6003620304a809100404076031400c1c0703011982e00d108803803880c000d03c5408100000142c0c4260120303000b400702c8505c140000ca0510078041d181070001c2c080d50b1483c00307042080803111485507003070b90101e03a0040c0824005d012034140c00d4a0f00c0d80b144041c070f0029501e800b217003900d6160070007016000305501040303d0407a600e403c010340c00c11810744c3c00041c8682001c00c103110000b1080c19803c1c2c15900c0400301d203c0144c81e180300080c90180130044c180f40072400842c810f000b00e007040d4415402030940010a11070b403590000c00380f80c02c10001c003005200f04d881010910003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 867356187 1250 867354937 867354941
    0xe16060f020a060c080a1a0f09150312032203051e070204021606050112020d111810180b03100c0306080304090603110105030105281a03060a0e0118 65
    0x551024010b80d0300207030481d164501604c003c0100c90f00440d070b400d402d110380da11003441858042a902100c044840c0d886100041845480b146018410340d210404130702d51820403040c81c001b00e000182241e107590b008403120002a00b04a50f041e602c40d64000300201c50f1018000b89444441d81642c1d507e2405048010100800c0071908070f00940d04010720550005858a1005101c0d00040040d003c881a2003440c0c0b04050300d1058214561000b081d0300074100503242d11040048c00c5134000843d02081d0740b841d01040d440300d00a01c048040c070162a00b40000c0c121164202d405640c07811208480107510441500d05807200003140d20341591140c0150f200c000040d03441000381200c0e03484c0215081341c1e210b582c40e1440e00107800a40134a940c44200304204003c140e100108401d0a003412421589000d0000e0510150034002c44a040b501e00c105040c2040500c003408082d00762084141c240d00b00602d0f01d014030360002c8070054010980090701258002c0c001c00b015040340d03030200c04103820070700200180c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 867357437 1250 867356187 867356207
    0xf060501080406091b1e0506041d0408070203061801051003230c04020a051c1a150d020406081602060c04050d060f0501060c0c0e010b04050904050a02040504050c03010e1606 76
    0x11039440100c07020340192034106180d4010301745046e42e100c03d041c0c1d014440d60b00e907501d640100d11a01080200300482c1118411100b00204200c4034001103940354102605141704210000790705010702010003c1024481820030715108088000304400c1d519445010040d09480c0005131034000c0300e50b0101050701c254104c008101060600f9507003840c0c1c940707012030242e030850100c50012500104204050352192840140203440c1c0340e40c18001c4003009500c090291041146090103800c0c80c0c3d6411601072244411600172038000c070011540d6650307848005241200a40b0f40482800e11031802c1460340b44001142e50191042a0245141610704010803004103611082295050388402c0c20b5a194601403007050300030455600c0f8081e001d105c0c0c2c504241d28a8050f040035100030300e800f0050010010380380c2070b074007582c1c4c09882c05401500c0e06e040051034001d000000a41c001d081008020070020086080301507503030194002c0c03000c2640002540d8481500100c078990f40c9600c004104020b074401c805480b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 867358687 1250 867357437 867357443
    0x7030308190902030a0303020c15040f020405070c080403110103051617090c03030c01150816031203061e05040b04020406140304061d0c01140c060403030906180f060f06050108040609 80
    0x19020b40716a0110f0305259054500343d01080c1c1c045003200e44800140a010101400c0c000201d180d0b140175510b600814078003280180c02290340c5c400040f009405045590003007504850352544907560f91a1411040500c2800d44e80080c0c1000e012400b00d4407e002d40c100d1411145e02c52021440f8401000c070f610040c024601540346c41381002c3c0400d2610180001c00c28108051b001180c00c00066508543c0401664403100310b0790300909420004030015171390307541600da108100c030b201902e42040c00ca02914094002e41111031400a110b004240242c0c4900708030b9005541c1072102803580010130040b030050b4421a000310700c411a0b5240c410403000020365005103e50030003c0c2c10401141d071131566500c0d1151841a55001d50078080c002e41c0c00c039407126081c040c1d00e00d6540c90141d01d60200d58681401500003014907403602100740801002d40c00881c0361903045015408004801c0c1814204015481c200396001e501d020a11010f00880307002c0c0c00c007501c4040e10f910360280c4540d61502d00408244d0b00075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 867359937 1250 867358687 867358691
    0x30b010c110f10051e0c1e070f080c040b01050309210c15100e0c040e040f12020a0b010e16080405010608150402090709150e13050a021207020703030819 67
    0xc8502c0b9a5405201075550480382d5680b03841d4011401030b9000c040e03401c2d00c8051489414404d030402e030704c2c00140515045800d08070350840380b6003401e00d0610b040101d4001c0f13092500843c5000c18184000521003511040480b030a000e0307032000c10019901844140c91203030035504000108404000f40c0c40060801c3e0000c184440d160218030fa07403044c14903480c0306019040c00c0c42034003800701541c1e0b100c03411700c0540510000b40869083c8940c2154032440f95205204c1800510380007c1c062041c1000000c5106070440700d03a0740030740c00082009407a413803180f0080750342c0c1d0a03c00020030f4520710388564030b01c00e0000341049165410008030a4480c140c00030b00031140c84d03480305008030722281e040c0207140f000340c0714003007030785071424144100000690001c0c440420803214410402c103441c5000c0120211910301c0c18a003096070001001b04900c02c8204050040d02d0341003d080c03102c0c158903603001700b030648a0001c8407007036600c480304126150200c40c48090000740601c004507096aa803003c076100e034803401c6100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 867361187 1250 867359937 867359959
    0x20a06051804021615050c0a030b03210d0f021c27060614010203031e0c220302010908030a02060432010c020d0c17071b140f01030b010c11 61
    0x3000d91340143d00081c1e03400c076101208420401116050743d00c0b107450003401c0c4014903107400c0700006805046500e0f03040680b40d042da10050f441c2070240b034403011082482211001c1d45400c1028660780071050008100e441c254030384081d40e006d0320a4071440034605817804140820312403443d010f00b518039208030450420100504c1c1d204808101c1004680c413504012854521388481e8020221010750001d055400420030080b2031050004c1c6041100304084112041e9203d01c070140723925010b00e450140c91080d01d41c0000c50030140780068001201c1c800da07525040346486009068a074040c0300c5100d00580d01540c0030600080c18102c4100803103643d9000e00c0c401610040503c442c8006d11580416a079548110072400e10b64103000d19001070540d414540402d01d00355543e100480031012080d14440d0012611004108461032090a285a80c2410f0300740140c42e10341c4082070045800e2580d1040c0ca08a07140341c06075020f80242c00b074214058540c00c1c0c1d00c00f100e40381c0401059090020582c080c3c10328103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 867362437 1250 867361187 867361189
    0xa03080d0605030f010e011d0607080a181a060102120d020702030a15090c05040b0d1e0f120207090507140a1119062009060705010e030d0f1404020a060518 68
    0x12130400030104c02c1c000706d070503001c440010b421641c41c82e10041c1a11202d941c0407500352400200560045920301c2c0414007540e5500c00c01005200050100c00080e4408098809210505d4120000104110f5813880b01c1d0700c07100016641c42c0c040c00301e0380300d03008414826808078200c0b0340c2c064503186002405030740303a01c5c4e065034800749a80f001c10425085c43d0341e41c03d47c84040c0040803500c10064030017513030104010842d510020b18004214000103244605400d0300c0401142100038000b5a030350700650400300c1d0384051410645c14040c1c410814010300c90f054000031408514000c450090b00d0a48031610301c03030144420300d040d9501601c1640300b4412145100925000304005800e2180d081c01601194000a231030440141c40040b003007201403258030f0b1441c5410148844c102c0c1d02907402107a00b40d6070f890341c03440e0160240070851003506803404041411440210281c2201001383c00602d001c01c0f00c4a07100b845035015140036680a900108402414025140074000410242c07101c07200d00e1b54200e140314 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 867363687 1250 867362437 867362443
    0x901090506010c0b2215230a090f020405090c330c15010902210903040b070c030b070c030e011707120227010f0c030c0b0604021b06041106090a03080d060503 69
    0x5400302c0b09075181011b030780c0c1007040c144514018040c8200105204e240c460b24562503440d0702405146040c0d5403600181c0800010005402203980d02400521403172414145181e220300101c0a03090240d000b44154490794a4005190b460300881d6240300c20418100c40c1204905070441e4084003100c1c0711b5803680040b010b0705c404601340205800c0c000036996070742c0020300c404602d8800e5403078601003000406000b10580d0110a540035038100050782622100340781003042414846500c080d248076060310500000c0c99105107410300441c0a03844207840034480c1001110341024048646440a02807004a41ca85104210404495000441c0541418118140e170310413503014645085580c900c1c1e0030b00f540b2558000c03e190349008640c1c10088005005618050110409004018010303e6440005404e503690b60341610000c50001081d003c0e00c40c03003071091503520b10080e68242d03010a40c68960004a2520300c080b6580e00070043c102c0f2221303d05d107554541d425003107801c8008281e5110040850703d61010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 867364937 1250 867363687 867363751
    0x90409050601030c05030f0c0d02151201030b151012150b03011d01060225030b0a020d0e07080c0402131a03070f0c080f0a020a0803150901090506010c0b 67
    0x18801030520742d4594070707240441c90507070790100c0e010342c102d0200c6151251011408000301d08042d5248000301d20750348001303003202c0342c4030f000008001808038503141c2082c0071201c214140c9120f00b8280340355844a050000c11001e10510013a4080c040c06600d018061080100754038ad0080d00308040f9100c140154211042d285ca5080405070740004801049050a85004845d4040c11106407820700d504003400252034540303501d64012009850440301c40c000651088600040d41c00844a46142c1003861999019612044070240325034100301c4808041c05011508400b12000c000003020b03039101e10401d00c00030350401da055202c100702d20f08d0002441159400c200e50804102e5030025a203150403d8007400e07003c40b0b190038804100c010303a03401e00000c0400c400c48444c21408401d298844807142c00c22840c1c50482c04004111402c08000c0c000722852040b00702d4605241220000c0143ea02c2d0a030800885004540c0706001404c4048038401090920b4511604031640103128a502100400401010325403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 867366187 1250 867364937 867364943
    0x301061503051003021c030c060612120906050a0e0a0b0f03070219150509101109030c041107120507050d0905010f08040201082e03060906270b0606090409 68
    0x21500c4910101c1d858410140d002c25081c0280a4160a580200310030010001d580f401440c6468214400d050140b4102107085902c84010f0041d1a2506001e40b0303442400e9004440340411102600b0f001405420513009035101a661141001c0b010f02c81160f080c1c0440c12400d80060340d4410100b00d104c8940020040038042d080080e43d0380c145100001d2a00790904000c210409241c02e80e10f0015004e500500b4242c00102c10108039600c43e5000203041686014a410040b8907200d40d032503402c0b801d070300036220f031035021415030300c944018600b440140c0311400a4015035060401940c030000318001c804000ca1100c40c6003103402c00c10325507039040c40d042d002511040450380f4620101f04070345c0d0024030442c07110038a01c2c00018a0034558000781c0030300d42c00740a00f50366400310b2643c040c00c3c09040005c0004250706c0309418030040e81da420284010f001c0010103541d05401c06c0709100e8009403469401440c00110700c510801c103442a15102c15401c005003406d40d20100810514006a44a01400712500c1c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 867367437 1250 867366187 867366209
    0xc0323070e0a030f0213020c06150a17060a020f0f030a060f0f0b0a08090c100512010b0f180402070204020c031308062a070507080d0807020a17130302030106 69
    0x301810301a007209181d4070300714820201e4040910019110f1680441d0740356069030805c4410062440c214064020326a030945188160340c100009a01c00c040074101c01041950b4020906886003104044d03070419042e405070940c00300c004210900d10b82e90040540c400506801410101516a0407881d5441560b02d0030202c0e448440500820020001c0741009200b4542600410781c5084040100c2d0301600300c418060262080000b6440d50061011940103440100609030030000018050074640150340c80e5400340802c3e0b8001f25078404c0200840c0d400309400c1c5055401c204075a10304100d503400565070b568000f81c00340304510041c0c65500151011201c10009161100f0038031109601c0780c041c561109005610550901400303050150480d0340400540e006801d60318075804403111540b1512600034020303c00c5441c002280400821105183c000d01c1d510042c0c0c40c1c0314100201c0c1c0d00d54941002a203100510000448900001402029181e07802400b284c4e1655513034000030700b111660b5000c010010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 867368687 1250 867367437 867367441
    0x10506420307020c011b0209040c090203010909050f061b030702030f0403110f0406051c02030a021005030403080c0f03180a0f030305060f0415030b3d08150a0c0323 72
    0x2d6018000d40301441001c0c0791001460f0043c6e800f075011001045e030040d020340051008201446118100c0601800b9080da05540d0307541d684034100020144004140e0383c1d8000c07045420114180424182d0040c2402d20301020129110406030341d05910141c191000d40c40108031480c003400c446030241c00118003584144000e045041d09024088194114180c03045280c014207004980d20014500e01c64902484880407001180c80424a819209100a58001c2c00d0501d03440c001703680310340218443d030721a41e1880d02c103450344c41c1001d540c1c0c01160308821400b036042c40003401b601003501000c48001c2d20303102112011001a1620843d0b0a080321341900001e40711010400581400b2140541c482d409481c1000021200900408420f90501005299660031004a44a40b021b810b0f0203e10094880c0c8507018003020703c541502e04850314510005103001c082000504460104d03890807148080b40c4c0d400c0b800c1c1e80c3c240c14040181039100148003031645d034442c000250301c0725400306030110000505024040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 867369937 1250 867368687 867368701
    0x4030c02040633091a04090b01080103050d0f0c1a1017070e040302011e060e060607110f03071206020c010e0c01050a0e06070b16030b030105064203 65
    0x142da00340e00180042561610350710b0000c0700850b00d801070701d60046407000e50300d10080d00c00c444101450b400540c075a588048031140314900e4400400031940c1c0c8030420081c1421210041d110400248405003441d0000560006814001c003480084500307245026400c1403000c3d520507542014200400703a1809a1400308900f00201c0300c40c01c0041c140e4080c00741a03110718543d16954400c0280150014075400d81c2c00704040500035044061860b1f84503084942c001481c00c0e070b8100030b092034413a07403500d0712881021404604000d0700b12181141c1050ba4083c44001101c00e0007044c1d50951041c0e501480b0f0490700061103503200c40c400c000d031440350340056500d100303824525007904c00c12a91a0386940100205880c00e03a0840210350a461031801c1010b0108800000101c290080c00005413040d4176910812980c20150078101f82c0602c0603131410400c50802d11b082c54202c801c1100d00ca6080035032142804c07403108020201144a191010000410307600c401c24034640c880b14021420100d02001c802d01c941 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 867371187 1250 867369937 867369941
    0x105090607021b01110f2a0f060313030210023c120912130815040c05011d0303070302060906090d02100207110307082505090115120504030c0204 64
    0x1c0801c5100400c19410503002c01441c10750040501c03411300400205048a4150520200e054265003409840000100708040c42d01820701511548041c145d0000034146841c02c40013420203407001802c3c0ca0300355610001c1c4200408556503043d415031280800030100300f80540001d100d90300881c5123080400008004030948035403101040f10140084141e402c600102d001c0564110071003442c442e0340c090b100c4c840c4890030400240780c402d000f200001000c0c0311448101898100310340d0018112420602d0364885403a40c03980030348008101421aa104020541c8101d80e0480030004c00c03500b440d815408070f0006440c6500607801200543c116104000380280305009069200c6086030152412901c0340304000e46515060030a040b20311f074081100f00034082000c01c042440607000e41124030301d94541c0380c1c80c0d5848079030003c40440941e515010f1071100795140c00001c1190400741901410340d09210252404180e1503100d0002c2203140035401403404074902031980164000e444500900d925401400b003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 867372437 1250 867371187 867371191
    0x4060e0d050703060f0c0302030402030a02010513030c0b0406090501050c1c030204091e05010803030712110702090702070e0a1404170f0f0903100203010e060f012025121e0b040501050906 82
    0xc0c1f52040c010440581c50204401d800e07940c0c2482c007180d440c080340d140200200c0302608060031009102c0004034050343e021000b00183d4075503403503800700382c0d948000444240c414506060001d4018407982c40034413854101203940e45038541005401d0035250750036542100c011603209070900d05101452480c3ca0902d06c1114094a03601015515600c1c040c540542000c40184d00c00d800b00b40c3c0c0300000441602e6450649402c0b0740d000b41003007424200440020f550740c0d03050240c02c3d01e1910010100306421014030480c400324541004503565680c03141c483c45540815840031243e0984204000500c010f510401030403001c10b88281d02d43c541320f60009240c82c0410010318001d1044c4100700500490b51181522a405101100d2001d003402508004070f83d120201c11100896103400b903e81c414454000c2404a001c0b20200322405080724140c0700302540a629200c1d080d03c9940b400041c030042122445005414491601c040f0840136950340c03108100c503000c9500fa6602d0b507480043c040d42c05002d2183d15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 867373687 1250 867372437 867372461
    0x51005030601050313260705060705031e10030507080d03060f0f150e3001020f0318030c0318011101110409090204270308070503070504060e0d050703060f 68
    0xa4154036100001030300f1032001601180c41141e00c1c1620303004014010010012004a070814158076184035502131920b50040c1000f12294000c61000540c050701c26800d403441000344600350000c5102040310b030f0000e0b6034080c0c00c0c8108510340110203c040343d02001041e0003055082c00a10f02c464404600404503015500401111602000c0c104a9101d480d0300340c5042c0d40840048082c5001c442c102a2400300a0300107098101d038000c0d841c4000e44560400d10035030800c4003440155113005c0e4030003080c200d10500041d081e0100c03042c0301148072013042188445c42e014540c02164a001c2601d5500c0d80f82d600303c0c01c094039209107400c42580c5156800741c012914044040c0003440944010b0090f01103a00583c011020102d9a883d5841c0956079140c11168041c50710040768290400e94400d114401182560305130b003c502c2c481c000c900154031903001c5038840c1e90a992118141824210203c5405400c0080b165110080000317410108005004210086115110000780190705000460a403180c0c16854 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 867374937 1250 867373687 867373697
    0x10f170606101202070c150e0103181205070501050a020318010c090302060a0302070209090109050c100c0308040c0308030702011b05090312090d0b04030809070f06021c0306150201060510 82
    0xc06800d8540d82041d1a50150509020440d03803c9801250002c0c0560340019014841c18400012021041c5200300120401c0d80d46010391074150000540030744825111800e030751324000a0301c0300401e22515024a00c811686015841c000040e141c590075500b0a4031504c040540c000306000c2403200501c940c030f000081a5000780a89400d190010b00a007046220107405030000258100c080c0d4460741c11502c0300c960045c0980a942041c104081c001e008448048401d4130800401c80450320301050200301114050ba907210240f10719950468802d84003a204403101e05059101100248500029500c078485036800060031200108201000782c03410544a003e00508100700300a54402003070030b50401010150455640d500700000c01c1c140300000d54041d00001c2490148020541e000e803030305004110300003c407001c6544540d141e24901145105003c05a8400f0034908030400143e1412860500c06040c0000c9496468001c038102068890300307240181d640b004140540c0c03408002d1b2240415840c035203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 867376187 1250 867374937 867374941
    0x6090f031c0e1f0e01110712060b090c030103030507050114180c01030c0504050108040219080d03060f0f2d0f0603051e190b060a0504050418150209010215010f1706 72
    0xf20032440d86485000c1401c00116404c4000075034081c601004108074444211492540d44000d80d17041420240d508071111410420b0308185c03441c0c220101030103140a040c1c0145181d00c0c5039401d4030a0391102604031110354840d80c40c010301102c11a0038610901c1c0a20704007048040e2100043c0c203002c403042e00320b41410714140b44c40c61159800003c3c3d605840080c201613806480d035000003940d000b19001e58904030343d4949000b0601140124503a400c1ca40540c40902c1607a0b2134036411440c40c0e17901d0050307507450843d9041c10442c2c8103029681e82070009800c80511201c02465025042011050b007102010382603001e0f007009180d0307051040d198844018035818004030f00805940d004054042c101070040030201080c00402c000c1c9600421310420300a08180d5030fa9000361010b0000c0d00700c1e00c01c05101e00c0c94a0070901380134296003030303001f0666802100c550314965441d410342d0080d0010700c20f0b14114032402480f106c00a0724108075030b0291940e08407540d44189005842112100c00c80f0600b801c1d5000482 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 867377437 1250 867376187 867376219
    0xe040504150b0a05130c02160806271b01110303040b0705071b0e0103020a05062a1203010b0d0e0a05030a1d03100f0c02071406090f031c0e 61
    0x6040620801c07011000c1241e04002c0002000d0b411190009a07203c81009154138041005520a201e100c1d02c80d001e64240c3d19030111502c0b4501c140b0302c00d841f42034102c03000060307000c481504100c858140d08400b4140f0048140d050340c1c03130b040c4189a41c020700349803004405c41c19a0440c00504980304118000c604e14174150703036030460b481d0303000e00040140180070480b00c00b08a51200403046032105041680c40559403920121400d400030b05c8140e0048103880004a07050030858116019190381000c21600080c0c0180c144a42140c1070030703000c2582c003072540340410800341d01d002580240007a04420742c940806900030b0040380d00350750080c0c1d40c039440404100000382012003a14042d010b6814503c03c040e150950171070180b142c03900056414010a02c601e68401400c3e0302a0038031034410314040240381d20400c1c00740d07134070f22040c003c14186e00188031907030704c82d49445d5000703100ca201d01174412154880f5805c0800d140c04a8001d01c24200d403251a14052401e034400154409d60800300c1d840c003e01c0389100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 867378687 1250 867377437 867377453
    0x308070309053f0a0516150507032102130f05130605030714010201021303051c0e13020d0b04090305070614070806040e070b0307030f060e0402010e011b0f0f030e040504 74
    0x38803665440d8081c690b80450f500042c040f9602d0729421400381c0b485000703883d0f090212441e0502841001c0a6940200d0340e0840c42081903404d0f2030ba2544030f500c4581201c04400a850000c03003084032205808124882004841c443d400004011031031141040034100010052802c00c3e00c05040031203403620351300304025680001c80c030003124074812460b1184a04440100c0c003a01c6209003003c03003080b9446002007001800900118061908000700040c100c13410b20071034405510b03446440d40144140d401240c0942e040c0e00a0040c840d103640c0000c2c0100c0c0800c0450b003135500000c1c0a80c04140f0206c0c0b401c7c00d000701d034003413000300c03032440301e280309640ca4000b0014148400281030f00d4015941d5990004406408002c800c000d007070391180603600c0c2d1401100003000b5000024a40911509110001600301c0003c44200d0049905864010b500704910740110b0b01480b92807084454004414030201c04610b0704042030540d0782c003404441128000505000d081603000c203001d90300542c6000c00300400b1031031007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 867379937 1250 867378687 867378769
    0x30c06210c04090603080c100b030d200f0703050d0201090203031b010e120d0c0e1003020f130b070c080313030204020c01022209051605120709030807030905 69
    0x9021140d92600c1e103071162500e0303000382d8100403895403802c4c0010040c400c0c1c240140440d680c802e004c60b179441c01900300d007006855144100c550152710001200322024040d2007010803600e9030454402011811903001403421045c0d19500116030807444c014400d009050000b1107072900039000a00807102c943e40400e03660700c2804160090100c90500001c00713800c082d004000c501c0415812903111004d200cac0e022210350f221281c3d00c1400c81c0b411005228207030140c1c481d01c9078124020110320483d021780a0940195110400d06a4983c500f04880388005c0343c07141c1120040d03d151b00729942c452005280c0100051040d411402150b4024481d5260b04410310b00c03080b007170740d5050301d01503218078451019a0190050300742212100b515600c10f035003c050119448400c81d82500018040380d11481582c0c0392008046410130700040007088031582c1e10385502c0400e0380103059403130b01e00c003c01d03541d844101280d008070800701d00103000b90b10300700003e161810035240c4038115803e001369081081b041c107043c0640c01d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 867381187 1250 867379937 867379987
    0x9063209120901030624030608010b031525020a030207090b1f0207051017010e070c081806161b050105040303180308030c03011a07020f010c02030f1b030c06 69
    0x800100c05000b648607030407800046c0310020880061108156004080b0f5202840c03210020b89440030000381248140240a01c0140107000707072580c121b42c408a03010840c001050b61281020075074440c440c2000c440080500245a030f4050000e803007286c40c0080c1060700961000440505000303100720301d03a0b910542079000000a41807c0ca000458070010703410a001d940c02158802c242403a04000d03250003c41c500c032291500c1d12070800b82c0c0c0c0c0318070481051900035181744000a83e10a1144001a4081c009001c1280321403030380d050501c0407000041680e03101d942a0303989410035000311801c1000b46a184242106402d0705501400d042c100001c2283c05144800b07420821601c50b4045103207420702c3c03004041d41d041400d40e50703039281121000d242c40e40288100321a600c1c0c900c242c501203461400a4030303007495004005401d801d508200458101c2440c280c00e81c4c3c0350046006004c60800304010703600c80001c011304040c0c2085103400c02c05040556080f4400d02401d030410001e224884890351120741c80340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 867382437 1250 867381187 867381223
    0x41a18100c051608011104150c050309040f021803063c0106110729030a0e0109050c01092705070c0623150a0e07020109063209 56
    0x50210200da0040200070041d00328015601052002403000c90380c0c2c070603906807034021b010301310004060031140e00c40c920030040003102c3c00d039500c1d8000c1c2c860380c03c02c04114040c000700c90511542c040094202c400044072400502d50004008800503d120310800e016003084024000794a032103506891a1103a81d5680d402c04d510814a0220400d0809010103044050362500440d40d070311850050490010903171000c606103e184030002c1c11040c041c22841d010b040c801c035540504440601e144140d504003824030074420b5101c40342225800800d03c9001e10250040c401803603511a070381c0000d0441007283d0048140070b20142c800c100401007100080e020200a404005001c0c0d40701070003128003503401d800040400303081508945295004402d5100901c21408261442e51600010000c04050509801d6003245c0c1400007040192038040c1d82e183e00003075500010900950654854040b0303039010100e10f10504442002907000c4162881c1001d000031031640300202d504000c0d05d0306030745010341400114101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 867383687 1250 867382437 867382459
    0x1908011e05191a040501141305040b010c050303190f0209030a081806040608010905220f0206090a09020c010b01020a031b0c050d1a0c18010e0f0d08041a18 68
    0x200b40c0301400c2e4020502c84442d0880a05100f102071034644c414810180080c0c1d111024070000d0103000c1c100c60700a003041c5c1e204011b05103001d0038000901031a6411905108150f038650f4081102400210f2048100d94440b010078001100003404071000130941306421881480504140d0710001610f2428542209041c0c2c0c4032034410b80c124510310b48511400b9008103002c80d0001d0780caa00403002034103a0340036403420300c5142c1d10b8015401030102100264039010b0502c0d40720030301054007080b080500c2ca00241c94503103080781c0c03800424000d602c9644154081c1f6070024a2410444007131007642c0c00c400092014102e0300b446600c00500c0d90303000654445080b4000365480080006104c05000203001c0981041800080e50070301881a080040c290f1040b946520000b41032202044101e8a00300034601c4040d079420026001140e40d00003003a512500041c80b0805011a5580d07810300c0c041640c41039012503510b9041090081010001c1000c1c1c0c07030801818881801d01055201403108102403c1d41c80200da0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 867384937 1250 867383687 867383719
    0x60105041a07050111030906090c0a03080a03060503010c0e04050c0a08012120040c08040506012105031308100e030a0e0301020714010b0f0612070309020a09021908011e05 75
    0x140c8030360407000700213620309401040000740600180d48035295013000d54496603295401d05131107040d2001c481e80c1c004540031060002034800c2d400b810b80890315250001c0d070b85403110f02083c04c40341c5903014000422400c9100300c24915060041a0340300448692403818617a03880c0b405070201c2c4040c080d15914a02411500c51070460101c1150a819006a00182107103003140e601e040c00004106814042c40c02c007402411400d01030780c14140a664802c008106903031800721090340324013100e9002818569803981ca2030100300d080018002c2450381410018002c0d02d81100382e490001c200f0654103640b070810f14071450388034020055130301c44045820400d49032807603d00068024415103a004204207070800c400307030350307100158440480e4440c183c0c0e811603485480d030108982400303040d40c0801c0640444000408061203500b00c0504284050100354150b920358004a0076030300000102c2200142d0b403000040a650300c40c452500403c0c040c100010802a103801c0404011103901a6034082c9110064007200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 867386187 1250 867384937 867384989
    0x3140f0618012a2001020a030203040c0b07020108060603100f030c0825030b060f09040b0603010c1b1704030c08060a0f0903080402040b060f0708040e070801052103120c0913020306010504 82
    0x740041c4c0d00215034904000d0406002501300340d40a4840504a50010508040c140c0484100680585580809968142c100003403503100a040703500810601e200080c00106a20a22000c1c0d031082c01c2600c04036040500191500801c00c0c814a03240e11850442e60344143d011218105494000b05510381c030b079499030040307640c804400030f4258003c50311008210501c401d003458140105e501320700921803205072a01c11501710648205031101200500252000034036481d20f241e2960104442540c2450342c0ca407244000c10003070f40d0042c20301c2e400560400441601a21a41c803030045020030404c090440760320020b22001000708024000c9503501070b444401c0e43c9020030f07203660505042e0b54070b03510403144c600700b84990098481c0b0f02165809030041240c09000380c0a41d4140d03130f0007420001d0048101c1c61101000c1401e1240c0d06043d000400c0408444480c05d11201d01c141212a455076551140e1800d201c0102c1c05120303200c9071248140140410740e82d0010444044400b02c541c80e40159444040c0100c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 867387437 1250 867386187 867386237
    0x9040e070609151e032901051b0a1a0106080603031908090c100e040506040612150b060a03050403021e1c0e13090b091603140f0618012a 60
    0x1130001d01c20040f01c56154101c82d10f5100c81c83c412500d010301240e202e81514034040019400301e5018031884400c0303aa410003803101040c0c220111b0328030024a88402080c0b078011040c02c1b124001e10001401481d0304414040d8000301c0584c025490030903694007500c0c0f40010080c82c201004221000303d040e9000030005181c1503070004200f849419154a4054412070350a03031030034083e40c10000006d41500e8644500d804071240382001462926040e910342410420910980c00c10555402c8000600e4840705c0107001e4184070360b24001018203203420064548010140c91907101c81492242000c0c03075034003294039190381c00400c10000b010300e8200c4003a90520303000b482164000c440e0740c01c4003d046246800c00b640b014050210903400c0e8503031100c42520380007251349140034000c0c120303020800907541081c01d406144044041c0c03401112001d00141c10003109036108800d203404801da02d00024002e02c00e03880110680d5030b48032400300d140c070400c0010741035460196080c010540d44c00c40c288041040d10302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 867388687 1250 867387437 867387467
    0x106020a03030b190e15010309050c04050c0f210a0b0a03230a150b0102031201050d020f031b120a02013615020705040203010608130501020d0e0309040e07060915 71
    0x700790398441d40305d04003440f0100e41420300200950240f100c1940684501c40d09035030005c02814114940c401440090480504601446d80c130400131300da03600f6a203030058030304030004803c6800744c4001111a41600c1c4030240000191074a0050110030950300c0d28036403800c0300c0c3d010480d408030000305650400706081d440101445c0d4001d1701081c00c1040703040707030b250500243c2c40c44082008407001c1d00120303a640981e1040034401309003640140480c0c9040300488041d40d200401522244686030301103424030031920b11b00001000480c0c5180b21078076002102401c00b484890050001540b1500001e00d40c440441848440d2030403940714101c4c80f0320300f1040e124096545403d4100da9583d03103244550b00e04080788844014018503501107218541030085034120781040d5104025525000304940c0308030078407881120745650801c02c1c19002510ba008040e11101510065034032859400140000c0d50780c0c002100c64143c0010700244a074036000100301042d03a0780300c0d0f0040c0070345540e440140c43d2503402c0c02200b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 867389937 1250 867388687 867388729
    0xf020903160302030f0d0804060509100e060714090a03021c0828030c05091207080d0512060301060f06110a020a12260406030e16090b030f060106020a03030b 69
    0x4401c00846019605080b24401c1d01107074084650180301e1905d0340d01d00c541a000140f400e10102c1d000c40c1c0305800158100079101c00b0b5507003550f000c01c0824219a9889403403221038024104100301c558202008442d080340003000b540c03600c0c1141e00081e400900c6808020310a245589a070001d00300c01c0a400021154030101d0070b680e03281d000d0390810003456003110504105114524205050b40b00c1e01a01030b040c41551207003818034001c0b004200515000440a42040c807a21701c1c00262554200078000304541c15443c1c060740c9413510042103810107030050441e4020b0f030419408000050310b9a40b0030f811074000b8a03081e80c803102c2d200851400c14549203400f07903000340c00300e0020a945006402240440d44aa415001d623000d4506168003101c2c40140031001c4d03120306000170020240079030044400c2c000c0410070307560a484081c1014103241c85d9500100600f9964801242c20341c142017084200301402c2000070400b543c503046c0025aa1142c403880182055101e20800c20161111280400728580d05040d0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 867391187 1250 867389937 867389953
    0x9080c060f070b010e100b0702030304051e03120a0f1b0f080d020703020105190e0606010e0310021b120415050f090916020d0e060910231801050f0d0f020903 69
    0x41400260380c8118546e450402c0000c580c2070b51021110010340c041d000e0b5007007078903110400000001d850b4121085030540401c00800c3c1c2c2e000e0001140490030070740c0907502c514020070b0041480a04030090320510400e9002c8062820341009480665941b0803c040f991440358904440c2500403d6850b0410354004200c8004254040d002a0f12172444801c00340500098410050165070f11101c011b58a50007440110f005035100704140c45400b50045c0c221117040d01c0b80350b8440100da0000441c000415141b0070b00c14a200400e11940543c13a00c0006001c3c18942400c1100352442690404582032050002d801c41403c0390420031380c0d0840000420b220340134600f081c811145012030300140070040c020401c0310340140d4065051042007200c090445418041007505024407510306c28030380b009201003e00100900304094090300d0404496502e5940c50314034603018100654081900541408030034040711409021a4003a510f0304c641c0c03007802050701a688080c84c4020f1043ea21607035003500400d54 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 867392437 1250 867391187 867391199
    0x7140a03140a050f070e191215020403080d0203060a03060519110307140304060f0c0f02060907140409020a090606110f07050f10020f0712060c09080c060f070b01 71
    0x1c000008520309400100c510395507800d150b81140c0c81110603403d0081e180d404251aa40300d001c90720485040075005001002d25a00400c40c003c0c5a039005a28050900c130b0035008216a5000c070406440c91044207505041c210380c0d940c40c450145000150302c065011001982607a5018a20030040d500b02e08c08011500b8000240040c403008905030000050400e1076070356581c0d41040850380f1031202603031641c144c02c6c02d00e50900e030070340d002900684041d0780340c1240100e40e1600344251065480191114444441c4520000c0e061500083c0514542c0c0c1007540208038900c10300d501c6c41d40d4002c040b50000f921200c0d52001852103a2181c010380302c51440d098021454039004010b000301040c03500102c4045036120707244e42d6641e882c240104e582043c0004548512420100e081074068519801179511408240140c585040010740c0441c517105800d01034041800840d00c5040490f070300c82c3c508041c0d41420060029a81c00d1000c07090750044070000f402c0110304002030251100994003015100281d65148 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 867393687 1250 867392437 867392441
    0x7080a020607090506040b1c0e03030412050a021c1e030b0411071e05120f070201091d0714090306010305030c01290f060f07030810080a0503030103060507140a03 71
    0x25019000d8450900402c400038058140c2100b02c5000603d018501410480440714035008400718400c0203083d1408005080c4141c06003a0803213190100440d2a0300d09410965084491450b0000c1404030070032045c144943d01080d9660042c0c84102d42c181e944d03149040444c0c1146600300950b40030741540f046524080e030b15820032000440229801d000d10700071300c08485518422600020030351600383c40a01344100d08503004010090007101580d405070300141c800c031a17642c0102c88402c01f84500041c0f0808540c0c1010142020f00350340e00364541c105c04041182c924403100a400c80f400d205031a10904900620f03901120300c40c51014080e20f4031545d607450076650340c0e0022180c108042d400c00181321800040701c3c0c21280400c0c40741103007800e0b2013001010b2104c000030890445403c520f007080722006166504d0010300c03581d4401d550382c940f80c1c45c108000340e010b45040e03005401d8a410014144d1b01080c2d001060340c3c1580e420110002c2c0640b00c092003901c04164010b5050310368600032a222203496019 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 867394937 1250 867393687 867393697
    0xf150402030708070f140d05060d0b010315050a090b040f080c0d080406051f17011103070c02211002090a0305060c0a0206060a060504090f0b06040f0614340204020708 73
    0x540b617072810700724128001e40b94401d03042a01c0c19001400c0c45449840c070740580165401c008064503060503102d050300e4000004909030015103110b10305045c279048058030761280e00e03442544c01d4000c000300300c01c941e15405198400f400140000c0082841038003030050880c01c440340c0103130002c221000301401c070801510801040320203540e51883d1000143c201041c0400440504640003000c13005c0c1410003012440d410601400c1c03070740a41d6102d42481d5030408060003107014280c0da4440840c15040c40c41081000f02903c1c0505c1c0140240c90040100044001506821094a48030158032140c40700e011a10f03c0300558000b5000f4441c10051001400e4001c00a04a5602660030307a606c03030740d40300c09210a06215205140015100b00b00820821040f903214101000d003184c00400d01907900d50008810340c2103900248490f40d40343d003080080e80d403c4801c0c078800901e41c01480b8103100161481000700c0344401d405000344241c907100c92800090614091214a40c000c20071529002d0609049a2075001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 867396187 1250 867394937 867394951
    0xb0a0f06031d0c01050f070c0b1b070e071b020301090308100f051302180a09020d150f1401020f010e0a0308090c090109020d060803280809060f150402030708 69
    0xb42141c0c2a02a440381110305411811220041c020040e0980046031181d010118149605405000180016022101c2d04006000007500a91188290f1440c034114009146155800e64000f11040108203045030384242e00891500f0034080d00c801020301c1c0c0c0c000c00d60301e440c000d51552130101e04100f00740d08440180c0c0201d038003023003103404a40c840703031404590061809041e60040c003800040c404415250000c017141c10542c00c10345a034142c1040880c1070081e0641280c000d0b40d40205200174801003e21420000d09030071945941d40d980340140114031441d09014020b030340c401075410004164002c01558109a100030002c00c42c85105103000c0d51140c2001c0800c40c005915480030640d08240001c00030b985540082c40d4800607440c050f8280c0096001c8400f142c40c0e692540c000041540081c8061300c1d0220085d10395403882c915200c02c1c0d24030010f451030118103100e48a0140200640b00185481c1c0c4610244024500c0d9150000001075921070b8401c00e43e885400041001000c642c004040345c01907403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 867397437 1250 867396187 867396191
    0x703060513080304081602041e0c0504060e040c020111070c080d0503091e1c210c2c0a080d021e030d09020616031707020106050a090b040b0a0f0603 65
    0x15000807100c1a0040201e01500b401018004100800e010500070304151103904501a80481c240d404107003581c4560390011a01d40c408500038125500324000c100c0501000d2400c0b501c0c0c01c0c10315202034607a94411000301c0c000d566840810010500035484003c403007200081c0d040c1c0f031b2001d5103000045078030345000c0c466aa01500c098442068010740a907405004004050030b6590b19120540c2040f11078103585010314407a64182247c409000c00a07403400201958920850b02c80034040da45074501070103000c074421490442c00054140e840007060030003100a0500c0400c2e1028405003289600c00032000f0b0768082040c010004e09900c000030501100705080d000c0d907400304421203c03041d441910b0308514540390800c010341d04421025522222000b440104030a0419882c405440c1d20f45c54110001c802160360a10080c504210f4154040d42c066081d1009200090030b0002254200348244510188141c60350309085c407690341c1d500b003000206c0005e003046094654921600c41c0d51401c503c03074040885c1c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 867398687 1250 867397437 867397441
    0x4140906041e0c06051606020c03121317030c040e270a02090114041413031806020a0618020409050d031a300307061407030e120d061707030605 63
    0x80300c2d216410003074607005a044500985020000c1d40c056101034170044102e00550070303050019100748040e200d0400500e0083d03455005030703011111801030140501c000e6035500020b13540020f121492040c00381c6036245245440303403155009941030b401180c202c0c00a06022504100c0202001c8007501c44c0407400c01c02c5800a840d044403100c0c2c131a025400065000540907006000e0300a089001a9040c03d001e0000140314100c1840c21110702030a49040d0f86032045581c0200600d54007400030070801e800c08a661494074030340103001e5039400300c4403002008152a94500c0700040e060300c0d080ca2846802070030920034134001d490202d032034034000244003022030b18010395503070401481a004c04020300080d00009855900103042d00707030048481d1a204151034401c2e40340c4516a800e10152a81a00c111008105580940381c0b20606c0040107120004052a00e000301419200c000b443c0c081c1c881d0740700c2d5010340c0c0d131101d01c1065000e001c0d5500f20405271f0300d50315032042c12244001000e00450340508000c1102e5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 867399937 1250 867398687 867398723
    0xe0d050d0c02131e02160f0803010806071106070315180903021006060e121603150506060306010804030f09120c090c0c0210050a0905092502010b0d110414090604 71
    0x4d07044044402041541d0955003860342c50075a00801c002603441c072000e503054034159140c00c000c292000d411078482c44007000401864908102c11030b0401882c1c2042040d0020065405036a400010258001c068950100c41180c144861480020f441d01c2440c4904001c81802c030346010700b04018085006210300c8413458010139041c80b400040d02d6481d0707250355910304003008205040010f00008151409454020001007a0140706040118401c0b50300e0003008050b003281c5811503000506540c0600000c108225041c0c0c0c0c005a19940294141410600000c244604407020340300340d000952481d81401045007407081c8100881f0880f41e14100900c548170b681c04040300e0780882c506e0001d4100b070108006010707450145000d4070825074589002c4000f20b139501c000400a4009581e040c00000c00c404030050500e020181784900301c4c001d030009001085447c0c011583c1c600701a2000742000d03440082800d89903459801040d07402d42d0440d6451b6403400c1c02d21200351107200545084441c5640768808035030b2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 867401187 1250 867399937 867399941
    0x3060402133c090207050f0610030b090c1305090f030f040f080a03021c1211030105090f22021503010303090f150f030903020109021e01120207080a0e0d050d0c0213 72
    0x1c1200880302e40450315000ba41c802a40002008545c00d0007a504090381a000801010f445103650302c8400211501d5400c0c209605040502040800c0c1c01160039422170381c0b200107000c07010100c81c5100095955441c0f01365820000d000680151a010000b40b0b090a800014003420a49550040c030800160b88c41222550321102030100402681181813480904000f424003065070400c6410001c0740050b04840030b804942e99440420f1800802200501203400c2c5042455403000451141c1c04450828081c03040081000c904952400038411241400b1522401014400341040030304140e12541c4130310b4050400c0c0080d00070310918030b24060b40001c41038943e100400d4a0301403500c4a0344a42c40c050303c00c41c0a026844001d50a640d203443c20b6200585891032a50740500140011950003071001c0d00040c01c501110080b0780420380140001004601128101d6600b54002c3c1440500031081a000c00d00000d6004cd001c1c1c81802002030446481703030000d94151007284201d502d007801502050b40039003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 867402437 1250 867401187 867401279
    0x150c0501141006023708030103060c1b11130f0501030804030311150a050c04050d1214040f09090311030c060a050f01120210050c0d020319030e10020306040213 70
    0x64880c28581410b03405c500c041c640340f01d04131200510f03045042d01a00d84c080c0319030003a44100da0a595400f25030141c03540c048918980c5c0703100304c40c000031200d8280e1252109803c448018602c0fa1400f0000d11455810652003141020b00d0403909001c19a0f59090000b0707242c20500c416000320304100b100b070388a0203003c80d01074044204c0540015054640807000d81c000c041c0281010380602c0c040001081e135540350000051858418880081c00e000c2c410380c020028580c5180310718002c402484144660034030802c4800c20b64628200018055110f03080c2151440190944050940000500460780c00400f01da2540303e200d0002d0180301e6030703c480d50b442006000900c034416901c92900e40c280c006140043c0c007001c8c0d0700c81c1e81c030b404c0b0b040c1203c20b034186080c903c03020003450250780006911140c198642001040d03048660034200300c1e05400403c010f13121401c0d4444100c003194000002840e55903030b54169100384040132004219251070b0110112084070110f03580c1340000090818040001000c04110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 867403687 1250 867402437 867402463
    0x1060b0409020306060412051c020708030a032a0f1d090f0915010f030308010e0c031b07050304180506040e0d0509060405120303061003060b0301150c050114100602 72
    0x600d00303490300340000000d42014181c580c0c0714208000c0020642e641c0c50840b15078030300410103080340b00c00d501c0d8200d0011150700100c00a40d040140c00b00000c00d00070050ba811551282804282c51080e0400c4610b40c2d00c1d0f400b6030f0403298190f24186001d031680841320784c1540e59540c0307601098002d40f4072000c000150f40e8981e00d6011200000040007041ca15001d02d0300710301c83c4c60449180c0b44e901e05081c03200681c241c00584508251030340401c00d00d0360140c1c030540108614001242c0c5410500401c92281c40300410601c0240c5040503e1480660458111131440e9041800da0352540d440b442ca074241d107810719848504181c00c280204819181922031400310008100040c100070140481c1600c0c0b94000020181c1c0c000340910001502da1074802c2c4541c1e88451400240d6500d14040041150a00801d1084c4041500e803800c14415180000b080f40c0c15075020b40944607003502502c400300c4208a081c80300a1142d4200540120b41c140e40e040c0d0a401021381c00c088141c059200c041c120b940d441c10700381003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 867404937 1250 867403687 867403709
    0x80303060a23120d02070506161217010617090d020d0806010c02030109080304170a140f1b0a050d18180209030f06060405100617090102040f12020f01020106 69
    0x820030001030509560300c889510514040242802d400103000b00e0624a440c00550411001c4504856041c003007400600710031650642040105155070503207a41c0800020500341440d03181c8005a070140e8150301080140d104995180e40c0c44a0009000030000c0c10054094402880441c024480101c2c1c29440c42001d64014810103c01050440d20618090401414001050041c2003d61001c0c000c06c0d01c07242c05219650390781e042a140c0804540400402c514490398103122041c003582d0b0003020118910022a00503407120358100440d0018400c4441c070921000c0600c404560704036002c211005402d00a03010b840858072050010ba68148007170743c0041140c1d4880f03901340b203031521801c07034604280c01d0383c0401401d0010b4000401e18003d01aa007441080e4008001c11000d4509402081c1e0304c101c2903600c00e6402c52419801910903860020300680346c5c840c0400251040740b095054400500900340c00062890f80c0f030700070b020855544203090307005113100500308042d540140140c20848401281c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 867406187 1250 867404937 867404939
    0xf11030d0c0506150f0301240b0f04030f02041401060f0e011806200a0803040c0504020703050702010507051614040608010507020a0212100f06090509010605280b1b07080303060a 78
    0x12001d1000c4088100c140d0010b00c5c2000300d10540c409206010b00031502d0b11540840102281c03101c030b0450f0850f8030800040d2801c02c0700d41d060701b65070f00a4a046a40c00721405107000c8603440041c01a0087c4900c1d240c800d24583c00005e2010742c00900c08003000c016440b200c00c3e005245004403070b1030310280c1c6148000900c04da0108000703841040003042c0c14620000c000f02d008008004241090084102651450070200c14002844178072003070000281012503045140c0b8903180d90203403031070040300006414084041440418000c05002c10803034011040c0001c00703401d85a102110099107400000d034020fa181a0001c1030303c200503c0744a008404540050914400c141d003005031030401c08042403203074001c0b441e4030014906240240e404110007244041401800c4c11070700c10403580010110521a814000204681d84920402000b07010064280303000b107580320081000c211443e40d10110010100082c0c4944041114010200480d101d000f46c1d0340895548074001e5a078001560017543c4411040c0c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 867407437 1250 867406187 867406201
    0xf0c09050d050343121b0c0303110d0e03070e09030715091e0f0204111314010221090d140105130209070302040f090b0d0f11030d0c0506 60
    0x101c04403201d1040084a2810b441c1110440c0e9050010140b00a0805029003440556520301107041d280d00a4010440d1540c806488140110002d01300c80b5040c040014409041d803d410900b808845801141004549580341340081c1400f20110709050f450045851400c001032151090b401c0f10070001b8010030b0f040782046003c030061400a02090464070041041d80e00240d1400d90b4010944000f5800095281c02410030a6507040f405070803c005003881c0780300070000b4510f00c009884460f01900c00194050080c01310140f58410f07450f1510f82c82e11451000522a0a46050548411401e83c2502c00110039086107100510044032001c8082c1010300240c00c46080880c070014595004459110b150400c2450160850b4416140601c030340c056180f5070420340c2002c8070000c2d0400f400345011072400b40781000c101c4500100d802a070b80140e0300d601800815954a1007039100c0180c026065503959411481c0ca200d80c01080c000040c007902035031203100c0907035026030540380b40c3e641c00c038025044a0751154 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 867408687 1250 867407437 867407449
    0x5060604030819021f141b0a0807030e0a0602091203090105070803041e0506180d0203041703251502190c030201061e08060919033c030f0c0905 63
    0xe0102c0f0442c07186183c00540740c8003140205008050072580001e2040301000c6094803071100402e0718120100d521b00003201d44000000301d4030920201d10b0300c40110384404004030054844800b45440034820540c0807818413015a00070002140c045902003402c01d103c800b03080d02c130302a419585012401c21f11024010642c003400440d80680320781070032001d00e503522240000903800848140c545a016404000102c550000c144e04038455250003000c0401382000000e690348200d01030f28207013803618502c071003044c0c03000c0080d2840c0c19402ca07408116a0504120600e8400b02d802c0d06403085c10010100300900c402c2c1e4421104240301c0d0814200201c16520415519101d401404070300719960351100140340269461103544810090200e408840c0c23625000611b407420180a2003410b030005031800c45d00882c403c03c040303c05a458200b80e000041d103410102009142c1d002d890b4a0340488020102c0c0c501c01c07820b0038151300d060a440403c5400c002030001c000f107030050748003d80810419002408689028 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 867409937 1250 867408687 867408727
    0x90a0602370e0904030e06030c03010513052205010603080f1c02040807050423160e040e06010504112809120f080f070f0b060109440d1101050606040308 67
    0x103406c10004d040b80c00404a001c1e0b80c0b0848000d50000c2010005009600d000900a01d020b5081041409141056460043c07218044184000490042010f66040060a4000000958000f403115440324003c441c1c200341a400010903040c0c0140b040c4803103801d2081842942e083c0e07003218000304605410407083c800141020702e500134205058004104422111400b098810485040b4203035808104c001c002d815070000c04171940c0304030305015031446082c00010329103044810448010410440c02e148030b4141c1d00c200102c050740440d6414405501e44c2c9119001c4220203115502c602d21180e580d81d00540e1180841d000900b41d18060710120f010456403c003921000e103020424510700003c03a51420311a60140c07030210784400e0684200246076800c0380440b401000c12442d464000503820340482c640059012031b541c186880030192480d1818400542103540810720111803200750100c8001c1d0100042904c40384842d806c01000803140d04201c010f4900300da51024a40381024804464107601c041c603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 867411187 1250 867409937 867409943
    0x40b071209020613030c0f030807150b120a0219080307020f01050d06090501090c02010504050303040b10050a0306021803070503031209031210060210110d05090a0602370e0904 77
    0x100e14516000d6682c0b00f0080401010f1601903c00e05465450521041000c5600014444050f000200080346056044440059002008180f0001805180c100070440c8003202500180503242e1000780c940700007440140b09000b2070b52140d0f0742c00c00c24400c1f400681107001b00b0174070360000d0200d540142032052a14080e06414102103007000a0511050100c80040d440321003103540b924010450980c00d80315051207040940b00030703c0549030075205c09940b44005400280200d00031800201000c06400030302000c1d15004140380019a640c0c24080041e41180500d002d2180d84018061fa0914000468030304846002c1c028500701603d0715042000080002c0c0611941c3c0003c005150414090006440c401c003111444d1000b1141030500080c030784550301c48400041442c05100000030401c500a60761500840e5502085995840141340c1c20314002d40c200030003490000c100d850303080194050311084801d640180950070121304404224411000c603280d00402c0c00380e1018072040c1081c06100758800c1c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 867412437 1250 867411187 867411191
    0xc1e090d060c03020a120506030c130b1f0806030a051207030207080706050a020d02032a031902010605010e090c0a05090a08030720040b0307050907120504110f09040b0712 75
    0x60191101000e07038030110b5100000a81c005901004150043c0180501d2485410100301a00c2c110000c43d50345e000b001404c03441080c0d000300181001c190f030b80246100c0d16019000440c41c940c68076282c2d450240c0c2d011880041401d4200003800d074100003030241d0645402c80000c00111005408410351513000d80c00c158218005e00d013000c9240c440400601e001800159107030b5a8403182002c2c020700b480e030203d020034219041080410203100581c4642c079044001c1e4000e00701700d014901c805601e10b100b80603843d2200355170b031584c40d43e02540650007107003240ca00380c90701144c0441070700401942c000111603801000005102e0303c0119403141002c0d00e40c2540c05010303580343c180c40703080e19451500401c00444840c410411132401805c004190345101550a683c2803040c0b03880c08002a880382c41500429018002d020001281c0f2031003220900801411204100321604080c01c18800340000180064011030121200c0c41450030402d41187c8200c0d000346600c00700d0f80382c407a41268400c0548071800a9a5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 867413687 1250 867412437 867412459
    0x5071e0f08150d05030403060617060c1c1a04050c0a0203071e0212010213170c0d0c0f0308130e0c04090903020c061c1508100902061209150c1e09 64
    0x3d140c074040701948034000e5000b10380b507603d18500391081c0d80c000d8010003060032000c4011180070100050366500841450005078480054107050400500451130440c28641010355592407251055500100c0120689080c4045c4c5d0702d040c003d042d2807060f2000600140e0041141700007203001c4e4103090110503c107011b048029540707600024911035203060514416503000550311007900c01c03441290001c2041c000000817500c002c04040c1c3d1580d0596054900605818644004004100b01010041c01020303170047c074500d8680c1001d03861908003a98030058800e82c540c021481491443c012481041c0c03101c100c0d80307014240290034014016140080b41503105200d11082e15980d45006040b0b12440c61030500b208454481c6000c040d25110620800b151445603001c2c0a2000045284806041e85040c00b1034201d03e580302003180e602c030303151010040504103020310005480104a0369240840403801c51010788510210358510712880c2000516403801c002c502c02c513540003002a040490004011034220 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 867414937 1250 867413687 867413689
    0x61e0504021c0c1106060d0201080402060703120608010903090509040f1407081f2d020c0c0406030309050102060c040f0e0c070605272103090f01090605071e0f0815 72
    0x80c46010f0380c1c81010403100650524181000c016031a072202048071071a1003003207a07400182401e0400b600180c0140e90018585044c54081c0e1340c0400012804030f4200010381d07840c00018000c10082d03004400046240c5000140b500e4510f400c1d602583c2c01c9845034045060503942c41c081c40038089a4508030380070701c0c8030028424805101c100f907425940c2c1c078082c040c400f03820800c408441d540e0303141d10407501c00d000416141180c8605243c92a03d210040141e8881e00c0100103803900d501c60040c15802400c0034404420598403520354000c4600c282c0072503299403a408400003041c0a107000780107821001142c1084a08100c3d031903203420604030704605203012003607104c0e0300a0b01c00498903006060617000c0c080c455019004599446290040042d008024400500c016100440f40f2085141000807000c039180040074810a00600c800d08000c2156500601d0540003409080f2140c8010803074040700031015005d40b048081005099640700f80c078503849035105542100f0060107038200c1c130300c5c204104c03403032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 867416187 1250 867414937 867414941
    0x3090c09091529010e03010e06091c020601030f03260a05060a0602030c1b0f09040c05090105040e03190e0d050a20030d0f051e0904061e0504021c 64
    0x10550203452804401041154050b00362245481c0810208102035014440c1e06000366801503801c1d001d02e840464441c41e440040d01400042c50b1110060041c0740902c003040d88005804020380d0022408407000c2142d8980c20380e00d6000c03d10019020940c18040c01000a2180c0400f00c0c003040080d4951940c41c45c040c001218102c0c0840d4440c02487d0348005104403864000c0c145d40042c5410b100445c90000c01102480c0c0722441c020101134860200106440039982e85490480031100140c150092440d01c4c0c14080600401c0d442010702031000c000000c521402c01d40101d1030b0742c181e00c000851a103444182050102003110030420308102550b0783c0c2d130085582d0b0881c400482e6009070000c003410182070410710f203515080090403140040d01c0034035003815100801d91a00d85962410842039003550030b1002d45481c4603200c0003a80e034500000d07042e14000b400d00054801d040050740d080188940350028600e2103400301d60070040200d40a142003081d07103000c3d001040741c000e40c210759162420141c01d500c81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 867417437 1250 867416187 867416201
    0x9061a0a031d0c030c0f0d060509030405060a02150f040c0b03150307060e0a0b04050306010303050a171315060303080a1a0a0e1801090201090504020708191214150103090c09 76
    0x10a58000d0a500f42d07803403404004441c129801145e0340020640c9032800500c02c030b5070940c40103184607260000241c41c0903043c015280201005000555901c40078031000352107001d010320202c503a15200e4085011810354600300c9100799031010070401e0b8a0304190301d40101d82c200416a8030600c907214000351680d24180480001045a92a4840110400c208111140115420010041509200801141da0000362490459805092040c1d0f2600c407884201c1c3c0340f40f00c00d102803d08032085800d102500340307070030005600140276000c800f03a00c4081039040f80a54041e0b210240c0003c8a0741d0115410002c2c075030200c0c074040600300100d4011080d03800424103552450f40035030480035a19040207030f4485000885e108440e03280008114061690780082c01015550040030b00440e80801c09804005000c01112084005000361b071100c151304007030040011082410500c020341c10300500c2501c5904020300780b801101c41d000101359900c0300f030f00110001c0c8071074a401d0380c0c2d0a040d68800640b5040a106401c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 867418687 1250 867417437 867417491
    0x2090f0604201b19020607030221070605060306060d06050c160b3103030c110a0c080118210c0b07050a030c0801140121020c010506040609061a0a03 65
    0x603201c0500303500f040c800034003440d400400c0d03401665100444d40006511203c01640c1150b40b140c8901d840e080491511211a086001c0c041d040b1a070012403009100181c04541d01c900c40a1210750340320001d0588525040d03c0309604240302d800c03580002211504101d90104240102900701400c0f40651290304544140685009a03400203100040141010503018880000d041200100b0700400c6d600700b00240740d801071304056886240403803070351081e94218041d0901000b100c10004250508281d0051140300d0641c440d8030302410310881014402180420a401c0003005d2036a451507021150b004541007903900030000e498400744009020001d50074005d000e10340c2d40750b0722606200d10203000c0307554058482060011382e00040205884043c03404005140038640001c1a08101052048a065802c0c060301c00f2400842d03601c500510542c0400e2140300300320750500c282c9546400c0c0303808580b118003402c01d030000e04400c280d031943d04480040c001c84096150006d081081c010710014041d035201405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 867419937 1250 867418687 867418751
    0x5040503160b04140c060a030b04020f040e06090f150d060b0613140105040f05100309150c0305010b040b0304080c07150504050918060a0f090b0a050405071202090f0604 74
    0x84018405000c000c503c2c1240440e0084c140400080005078441c082e141f5610105900c541440190384c40d41d03010b44004924a0104c55103440d00d41801c0309485a080710594000d9003043c001640103480f220b221402840c1201d0300c281586000d100744003060011150540d00640c4589940280d07884860080c0034285018422600c80390a000d401000100114199410408240014411500980300d1101190021540640007018184003503016083c0820040d101c3c040803a5110081943e07904403600c400d55035a0100400c1e078070b0340401c800714000d90041c040b0001040c00000c002481070402400000d0140c4103c5049a6035564003142040c81001c0300700c002000803d003000b4904091102c25040f1440b1b0722606800c0101028060343d0340001091a4040342e212141301f00591450303484100d045402ca4143d0700700e464203183c084044d10302030724129040e215200000800c0494044c50b25541d6038014600313a51519840c1480a1550002d000760307034005e130350b40c000c0c00000e03001070a0903c0c0380b4005401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 867421187 1250 867419937 867419941
    0x141031602010e100c021011030702070906080a06020a050f070305180603040f020105090a08060a1b080705030609060f060a02061014030c0405041b03050a2f0405040503160b 76
    0x82031403000c56600d514001c1d681030034100f9084210206442100c0c295940c4002102c0c10070a504030b161a400080202e40140f070007000301000401c40c00150310501c140d03000c990420744e03501200c10486aa51081010340d4100d5600c140001e04180c0040601c01002e182c100e04000074100304040d194070001084011900c001607070964400c00b901c0d102d0762100c00719000c5080d45401c2d207481c05000742c003100c02030421a0025201600c5e43d02c0c4144400504140743c100d800505d001c0080100801c081040841c0c05106005c04c401d502c2e1040350350324825510307662000e045480c0c1800b07100c519000540071581c0060b0b548044030154862401400000d501c2e0360041c607c41c20440c8008a43c80925007101351414409941804251000a42070607850000c2c3d40000302640c0c0d41c00e2080c000303002c1c0326100310990741c90040001484800602425500d0051100341450124205a0304078180c40c0110003176951411348011a00c1e203055400150710174090803d0742e10380003607820201c100e00c4400004480b00185401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 867422437 1250 867421187 867421201
    0x309120c011b210f150f03050f031c0203090c130504031e020d08040f02030601030f0c090203100311030c04020d060905010b0f030c0705150f090d030506014103 70
    0xc28100490755040101c503500003c10080e4074483c10b80c1c144801c4941359450000c401c6801d5016200326255a4401a00c2584a40141480c2c410500c82502c0601c00c60031340c84082000401100c114841428a0540d0240b118501e40040d400003406202c080c050010a00305988440c7d825031401d5010160010b4280351620b8090b209142c030308898840300b0f6512901011881e00003c8a03a81c00c0128289507406940c0c52408842c036040e4140003c0d018091b46000108000e80307090b401001c1407149030401c421326180d135089800c038001112181881c1d0a24401000820115038001e0003580024040ea20040580804141a0381c407048804440540d15101041040c03118403030b0601602c01031412600c0c3c048000c0340e03440540801381841264603000180d4000300007040190020070001c99101c0b501600e800c580d42d03206214125078038583c9025081d041181d945c481d2140c544207510584848040c058440c0502e180b926090380400000f0701d0311402103c00761500d4048018031440001929524a0021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 867423687 1250 867422437 867422471
    0x50601060306172e0b06040b0a0807051801120212100f060e0a060302131d040308090118141e03090f010804080f1c0203040f05060106140f0309120c01 66
    0x4069854540c01c01c2104600e81601031402c440c07000030a6507a2451410b403150f01c0c44c01448030302d00c100d500140c00900042c040c014040981450300711901d4108440d41d8403c0d0072f84080c8036101c0062078a840f5903062043c00d40c010145441c000008510060400382074412425080300c0596880807800c001ca001003000010350443c1b100038141524010304034420300d00100d00342d5030231405801d0505801040c0429480a5099008000c0040480550510f0044004451f00c41410740f81900052071800c005600642c1c14065451514500c18441c0040d9109481c0d2600080c100000e0031a0390150100504a00d002d480f107403400c0380c071118080d540c1c907061310b810428040610070180d410b1000c0c0c40d00308000300b08104141d58403100b04483d1660340b21761098401c2d03144446e0300d0030550341038800b1003840309001c2030025490445100303600301d0f60680d0301e8440903102001c502c00c0048a01c02c0c10041840005c81d0702d0065a0081c40e01c10840d6080031176580d010405800c80d001e00f4070607a6480402812000400b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 867424937 1250 867423687 867423719
    0x705101b020111030c0306191503060504060302030a1101030204080703050f060a18030f0306030605010314060a020f0d1808040305030a03061203141614010209040e010b2803050601060306 82
    0xc0e000801400288000e410b038540001007540e00410408400038410380c0fa0100a01c082e122080c6805d6451070f100c1c0381440c4000400d6400400081c035007000032400b41400e00c80c45042c0c81c1c0040090050311030b0352303407466050004001040c1c1015001d000002e201c450800558010b58400e80203401001d40c080d210074904240200007040070b03410283d00c15500400c10041c21030054040c982180c04200b0301005401415003070b8030060009117400300000a025192106019064170790041d01d115898851170001070f806010640c1030300480801c6410a0317513815502030101b0304001c03040c400610000d92030b03c01030f54000f44d20035526a08002207010610703606100d0840500003101c48880c85010a880c000c0070851240503080800c071000078504503040e0240301d00c641c0c20781d0152284000080500307400340070b90000807226000383c0c14a400184200810300413140e1180d8054880120406c0f003182100003440410105e10984080307110100226900b80400c5018207580d0701c0100b140362800d0251160091030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 867426187 1250 867424937 867424991
    0x2100f110c0907050307021203180d1106010909020a0806070c2d03030e0c041a04060b070f02220905070303081f150318051b09100e0c070510 62
    0x20507440e629601e07040040c0c1c00048514240d40c60383e60320b040980c60031000b0030000400d02d00101c2084408441041404120f908107001d40f42200c800c0d603000d4610511801141006400c418014849050254058507220340010301104d0081c0e543c40c1018104601642d0510026648251200900000c4140034444c4103c0c00e100012051103000d154109a2400368000c0405446a040e2492604100504100e00b0b600030400c006269400907200e020045201c54140a241445000100c1207540380c25900345c581c01c90904034a50f0455030812902e0b0b07a0072102c0c4144a52440c104180c1940c96100b00e60001748690024040d0608500f4040d100440040c844c002c00c400815201072005e4610041c0c0d411268100707210490000298003d4000e40a2002005008040d442e803090600000090f04020b075250a441c00315901405418404000d00860381c00c02c01e0444004200103841d070b6000360b00e601c4814165880d040072103941e80e04c4c0c1400c0e0410503020500392515085856207801103207010840724 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 867427437 1250 867426187 867426193
    0x5030d0203031605090306070206070f020c13020f070c0e0a1802060a110f030d1a10051803073803150909030403050111040f080304050d02100c02100f11 67
    0x10145402941c9200041040954181c01400100841e00a4040c0c074100b1400506945446c0342200c0c00940c1c4420440b400d00004101c0384140c0301d05800820205245107010f040002e200c2d060150110180d800301c42d00c0010b4040030400310740440c802d400c0c04406020340100000c214100200203100784c0c0e50b41100c16801035096a00200161340e540c044035402d0400e8207142d12402e940040d02030401e0f098000c048198000000c415039a14103da20280074002103144400844803804180b2004500340a644404180c08006151401d210b6a04107072844c82d00038101d4001da52140264078a14440ea03520403242017088a0441c08103207841d8203242c490b06507080da9800e6103072850030220f904c1c2481c4c50040c003036444000810a2102c0a00843d800345801c0402403050914044100803075501621030349034508043e00006c18440c901004480840e84d004101500d9084241c08011003007450b074208030140f254401010006841c0c142e0050355980b1280c4074421029250200a0b20740034040d244290150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 867428687 1250 867427437 867427453
    0x91409070b1c0905070f0b0c010e2107060b2106240415031e021f081605090d050318040212040602030402030a060f0507090b0705122109010c08010503 66
    0x905008540c0242a842e28081824411800e02a0501a03030707420100400080141c0490400c20b5940100f07036040340300b07000308803810780c100700b01c0d40383c00c80f0207040100c40c1c00c0310f03001e070050f032010a000d01041070040f000000d4076040180080c01c4801200c0c0744204050b07500c4001c580904043c0310b8142d0002e184000501402c185004180c1c510030000e000c00d200f613903180e4800c1b40144038251000046c40c0d02040041d070042c0b10103038800b952070120354224450440340c14103a8100c1030320b400b208901c0707500d40c031040030a1311031a20380c139484020800c3e06001c2000a0001e0b0882c0d9450205580c1031900400203955500c24001013000d98807804c0150901541c01001030308551844015190341c4103420280040e1a92514400a4100308045c500030b840380381400406503441940364001340c000d540540307601600981c0c98126421038003490308090030a40040d030380705110090141c003c0010000341802135100c82031103000900c2072501655141d140c1ea5407040702c0b40c18950440300107400340a04030300030303d540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 867429937 1250 867428687 867428707
    0x246152d1d091b040306061202030c01050406080f040303091a0f0703091113060b070b010807050111190305160b0a06050609031908190c0501050606041a090604091409070b 75
    0xd00400742443c81912003111200c0301100c00c8800380c03405103502c024103028280c2d6490740206052207c0740b05a104e40038440e445401980524121400c40d007154031149229039540c1e07000b1826001c0104103905042e00c902504000402c0042d03505590000e0251825881c100605440300c040c800500c0301c02494640f10b000d40100c2c0780e40107401a221022104030312504070000e600d00107082194007004c4208008100c031400c000143d04d0f400d040c1c0703440d402202e040d00d07510001100c43e180009000307030294000d481000740121403d024160f0329802401d100d4940205042c2c0c00c0610f0b21306c402c0074ae4003006150b0130b1022907415030013040b000745000c40b0700030304000d0a000069154500c2c543d009040d80450440103081260300c8041c3d400c03981004840c0303109120b840c0000b900d09407021108071201d5103004001021840d0090039581920180c8070b1481080500c0c0e090b92145500c47c0454941c0708005100c00511941140141542c01070504281c1d4510300340284043e00c1d16001d504880b1220505100040d45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 867431187 1250 867429937 867429949
    0x150b210c160515010b190201020304021804061113030615270b04060e091603111c05060406061e060f1202070246152d1d 53
    0x28510a68000c420074a024900381d07140c5045007101c40c00040b40e040000512035207100c083d018a44011580000440346558124201d101c103c400030b40c4036412641940d10072044450030703540720f44174040024400d1444091800ba607080541700700800c0b50141003d00420000380070741c007240e2060310f4a503201141030488030060030f84100d204e0780301001401101b1980d0755054102c007420410280040121f56260f00038890300c00300c01c549095041c800c1c003014201c04202c81d1400300480740c00143c14034140102c1010418044150700100a10711046450f240200d8400d0010b140168880d0000060941c64142010700c007401e0b00a00c01d24009102d501045456080141d00244c104140342160f214800500c0000090140702c9010f9080003194860300e49864110800c8440b0240c05801090039034810050800707100e44c1c41020194140c1030007810040c84044080750480e801d040e061280130724003a0b03007500030928564091501c2c20480c0c01c113641c9899401c0302c420720342010a8142003400319210008250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 867432437 1250 867431187 867431197
    0x1305060306060a0c03201c0c0f02010806010207090e07050918030409050c120403020d08010f060e090c0c0a050703110d03021b150c030d0b010e0102070612150b210c 72
    0x14420708000e0300082601c55400400750b601e1002140b405030820320150f03961000d403044928541c2c242580c0d07c0d000f0f90301503d09400800c2c0c0c84600000d0014507580112555407002d01906d0540c40340450103e003804007070168500001e141002070580600c0c210401c040201c0280524265894002c00420b180c000032080741c003034030169034002c581e42c0c543c500380202d01d21030305100d00d14258041c0c0500040550100c1c0681212415950700d41d000e0742c0300d11800708c618000d44188c0010401007068200030341000c0c80a1036100004071040c60406682c1c6180509010a24400f200c164001d541c05004100f49821405000e20090720480c101500c6590043c3d070302c11031031b094040404954405650103030750340c2d40d000c002c1c0380440d80c2d501c0c0c0354240d59a0407580c940082d46038540060030075480b141c86500c03d01350080c40110583c02050410b00d004800d44100012281d070f40a826165100c0d25a4682581160001000103100180d07561048a034035081c0d51160061028888403000280600e40911070241c031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 867433687 1250 867432437 867432457
    0x200c101b05220506030a0b01020705191413020a05041a04052b050f070806061002070608040c03050303100e06040c0233010b090111070e0a090311010908130506030606 73
    0x141000d4240450380d0b84062540b040d0b9000c0c1001080190b045c08170b0f000b4030b0300343d64203800b05d68034903840300308000c128000500c84404035580c020040001707892001076a1503110b000391194008681e007505034001d80e07018064020114400140411061b10644068907281500705c0090b0305207420140020700325803c8001c68030820400104086241180e00342d4a1901e47c0d000003210721258900401a450351498441c400c00d83c00707034400143c0780e0b0400203840e42c0c203050741d54003030460b9070700b005810380b01e0304000383c010b83d901c101d00d02000c80021800c100860162106c9404403d11500d0319110070100361005040c0c90103642441c12205640d90000f03581030384411b202113007003088028511140c03500070044400020001d4440c000241c4440a040200740880c0e00b83d0b0b0b005800c08000040c540d5408081c4140c0d22044030b07010005e1400b01c116803041e1015071091030650314134a4030a5825003581c07150f0006132203207600007680d101c452054103150f100420b0184e80301d40c01c6181460001b1514052000c00c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 867434937 1250 867433687 867433717
    0x21080108101514031f1b0311091927050106110606100302070c0902180a030302071806170d020d0c0809121e0607080117060a200c101b05 60
    0x41169135000d1001c20300b003110a00c201c401c6001d170700860341e01616070400102460800026a0700e581882802550a9424800700b490b16089611041c0700008055102044a1002c014004122001800c40000140880d1148034007202c51b400c3c0000200d44040e070080042c001a060726108850000c00c1d0341d940090120740313401c1c03960301c5c941c1c0035000780c49501d400808240000c900402c01000640c09000c48041c100c0148003030388407000900c2008885800042c016a1140c6810005905035014140107003007404004201555220000c03c030b0590500a00030803a0030401d0b4107410300c0e174108004c2d0a14075262404200c040a04e03250851503100f46124079020341041d1483c074040c0407081004045125410041d00e2801c5420b408440d22070b0b01c1a01e10000007600c0783e0000601459460b450b0b9801c4614102824482c0c82d8203070301030004c1004000341000b05c2a00d42c6c00c02c1c01d01c00403d010b0b203041030b5054090800121143c1021044a807030084040412032405034441c4000d0b4800c003500c00c030000d40511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 867436187 1250 867434937 867434969
    0x1e0906030f061c03121a120601092f0f070f03030c020f0102030705040632031506070b0613060f060c0512041203110a0b010306091b08100207210801081015 68
    0x30801406c80a20101ca82001130441841090f04000656078102c507030f18501040207a4a0801c8515030f4192100b003542c5c02001031210035002c00301c030001000400944000c1b01e14042240c0c0e200c54807000713126800d0300031030f81e200990200719030144030401c94254403100842c51351515090150250103a40920300030070841202d01c3c00c8500e400c007250341c150321405040c40300b4041c207a0104541548222250016142c0201205605092200645110560007400c02c0134603a541c40510921503d015201360344c1c01e440da403002900c03400c0346031444007602c01a511480301640500f06280790010104000312402400c000c100404090082202c03030142d414588501c0d80d020070030b00f540c078101c02c020000d0903c00809000008111165000e081a18401c649089070a52042420aa0305038684a900042c0c1c01c51a15030300c1c000f56960050120610070394004c81d52000d24814040c000e55030092440c041445480144404c0b0800c003c4040303d408002000c2c1302c0c1c50048081c4050308001d500c40e1103003004010756 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 867437437 1250 867436187 867436211
    0xd030903140f030907091406040902040209040f051501050403050a0212030c0d03090c080c0904030516140105090f1603020607080c0303040c14151e0906030f061c0312 73
    0x82420749401d4040c0b502c0d0030140000000c2d540c01502e008015100782040055100c240e4050801c040403c40701c4003c803999113805010240105850480c1c0c446e500300072000d890341e0360b8840c8680c8124200b0001541c1d01e00a191003110f402801c11160500c01c0070b0008100141c00040c03840c20482e0b051b03905059800300c00300b409181d8000c00c40345040303900800c4d08800c0d07150341c10740c484428180034081d02c8180a640da00c07003039240d0040d400f40980100d0b10000280c08039000c3d83c0106004808410b45400d440100e84404d1418082030581c0e1800341d45410500804210402a800420701094007800b2411990a801d00c51f41d0304510001303000e01c0c07000c42ca40d024004100c0507501c00b0600c050035260340e45054900068004030500a1085800c402500c4690710305040c0328510b5000108203103503140904036100d841546004068645243c4410080d4040c00c1d15443c0c0614040d40300c0c80c02440c420f00f03002e01002400241124035500a03100c41421801180e4440341c503128401c004c150024100141c07403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 867438687 1250 867437437 867437447
    0x1090b0a1812020f13020906030a091b030506060d15020a0302130b04050a060f030b18040204050702010c051c0e03040b04090b0603060f04201308100b0607150612320d030903 76
    0x44e0303510348c072100200812400071560742018000501c82ca4441d01841c0390b000e29002c040c4401d0102514a40c40700e0002026402c0c4a010494500d020f40c0030b88070a0000c0000040607a4846104440020f8000c14422127248081c601040039044401d01d00d0b00b41410400460440c50051142e6000c0048410740300c81d055029500c05011808007603c81e95005200c2e03c01030381d511206a5080b8081c1d03192200181c00244103209800c0c00028546d01c6515001c0c1c000b5840078031211501017481c0050351110130102030382d4200000d00081200c07024858a4520f0310000d87c0c00c07100c46c1c898081c0a44820803c1101d00c2d0764540782c01c000b51604550001e015500b4042d203074400c03030000034500400400003070a17203034007002851800e003220742d0344c42181c00e80f90303c40c014501035a000000c0c1980010040c04000000f8004030f0700e2544000038000b0000d00e10340e9803450410082c000c0501610541c02c20704855281d05084101540314101d4a0080e504082223154503980c1d4001888911080554076200310040510503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 867439937 1250 867438687 867438697
    0xa031109040812010b07120206160e03120c0a03090801050610030f090222180f0f051c09060813030905090a06330c2001090b0a1812020f1302 62
    0xd50000c0f882903841d00c04c8282c2da54401c40302520090100c0c03424a030b001d480000d250b0b10032040400b800740c3c40c04000d03009968082850380c0c05c031303414040c0e84000400180d25202804604094600502d004100c904000d0034466403034000c00408c1e41000104442e54403944480e546503440351500050001e08086030704000c1141040007036004001410000c08540b03c00d0448a10201e601020070524802c910000c110a9803524002d0154154907040004900540300780c00c40700c0d004405030340c021f5903000310300003045c41034130303c0c0c0c4010501080091240b81e6119118a902100c602c0d606050b1044e07a46018222001521806121340b483e000010010050b0340c001d403000b0f003140f6000d10b00d23036540c0100c890100802c070b02807510000d0684075440d8207144254503846109400041d80c1c00b00010703030030b054101e07207000c00d070036505000c406000000c2c03031490440241902040c0d0303038464440804425181404403510341c442809094040c84050250303a80788401c861f4040d04503503003820050742417282c80181c016 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 867441187 1250 867439937 867439957
    0x506040b030c3a0506060a2321070305010902031312140d020705010f05060603150f09011701111c0209190e09060109110a0c030918020a08060a0311090408 68
    0x40982403d400181d010b80806803c0c204103401d10959850030203000e02d501802030f8a000041450f02c0440720460b8140101001d13154604415140c100307100741c4a500010200406000040c8500c10468000e615104550241044110651a500345001d4161110b903890001030a50380001c00306602450060290701240f0920360040c50b200c04003c803c01d8001e40060304182c455509200e000c401c800100d1045034420308000b131266007103031141500c060303001d0713025001e150308004000038410260303444e2003d041c003c050800d2802102160010303100d00f50b40d012241060b00c000d060240700025a6001500703200e2211031a40181c545041c2800114006509070701c1090b0780781035420103c0c2034101e60f030466204150500446006990344e40717980d800c548a10003d8141c8240a00c10751080314032078400089014001e142c840c0040c0c1e101c0c4000010f550720050f50405c003d50024000820b10307000180d065012808503241e00d0114515115101690074150002c4d2107443d1004c0060700b0441150207490058403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 867442437 1250 867441187 867441247
    0x1806081f0905150f0306010501020a14010e0613110108100b0a020102040b042d050d0f0302010b090a0f0b011701151110061a070203281a100506040b030c 67
    0xa00c43d15aa41c599082041c040c02421031315508141030400103400f5048030300680c000e0404103a40e03140d5008200716480c584040d55241c48100c54800301c2040500d00900c40c019006c11198a80d00d40508140b90803080d950500842c00108070444508440c0c00007150315600c03d1954403100504200e009100d65080001030300c00119000c14481001b802000740c1c0d400b0800203040741c40fa18250300b04140c41a1141d16482607072400201c000810741030048030700c2442030001150800ba40b4000807000c400485451104a0751200071001100050040d0b003650402800c0021010400352400d94070454140242c842d0045000300c503a01c99803041d002c6a01c6030540d102a1444a04e4481e21007018025a1080d40b03c031103150300580d00d078500d00c030b4112043c0c0d6030b0080080040b991710329000ca1034003550703da00040d0482d20380c031160013140382561b601591041401c8009035070702d841d14101802482c90303000203009400910062001c29030241c00c03a40c0150308030002981b2082604150300784501c2d0304c0382002c41d40c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 867443687 1250 867442437 867442441
    0x10309020a030b06030609160603200d09110111060a1805030a0206010306050c09010c0f050309060708070204050c03040c03060b0607060c1716050a0c060f0e0d1806081f0905 76
    0x11180c00444d028860450503100c0545845800b10307030b991011400a00514614501000b034580298403002200410003016205500c0703035006040300e90001280e0703610040d120f038408000c0001c1740311031000f14003007401e040980c14031038400310b6030f662001808842e010755180f5903c0184840c40c0c0d10200400c0d880320031030350740f04808180251198007e1204494460400c4007050035099808180d410015041c0d41d1014980d07a0342e04d03000c152000d507c90982c1c0a02003000301200716107400000341040c9015480160303170769a461043c00101c503c0200310b14603000080c024000010031303810b4000100e0740c20600108800380795200203840f511900000514403032400d01504404c41d00503403441a401a41100302030300d41d84080040c0c8982900f6507400c0002201001404403103409004607203120b84c00744c02e000600b035441054110456251404250f5035500100d84000c1c4258400000a07100e10803140d00e616840c81e000024007141d2025160038500d80014000d141c51a03144103001d8024171100c0c2080c0094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 867444937 1250 867443687 867443693
    0x15050405071805040506011707110f0114012115021207030606021507052a01020c060405060a0207051002210a0614030f060703090f050f0c0f0d030801060806010309020a03 75
    0x1c0d0b8079015005660031a0320000501840d261060030311075401a103c80e078504140a02451130b4503001031444040c0b00340314907656018141000f022910200000001480c0f64030500f1101ea1403070160702c00507080364156030803280c2ca0a070564010403da07002d00621580c40d194980c2c507010313015890001d20180070704002c201d05298903807c1002180c0c3d903502610340010b4110000500740c1c8003250501c020680801c01c1c00039080382c1c00381e611b003401103400e1348a01d00f03080b11542070700760382c809081d0032903e43c07210742807000b40304041c004650055070340f20b41180340c004036a940c0f80d00c40b100140c104203455404034070911118501c50b07008544601513081d0a140b03251034460500241401e00940e11280301d207050448850900003540ca5022000304014075607aa2840d40c201c0c05000e903030008441c107010722800d4900040040101a4004c0c032100081e052060741c0e90144400b0800c1000c0842c40766180c1c2c5800c1c0f011a4001c070f05141510140c2c940f50340316648107401a0040c10321803400075044070764490b0000034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 867446043 1106 867444937 867444947
    0xb091e1f0803030f0708010e01081b0109030204020705011a1009050d02030f1506131404150e0a0f05010b0130150801051006090f05041505040507 64
    0x4803511000c0741c1d41107400990300b220003400b400b024440002e801a1003075026000000e0700c81e0803585418005642e5071001504051000b02112409002d40d204480c244095500a0401d66541d40103107040c500030450286821120503c0b180b000b410307131900d140d010480500c141c1e41c0084060034841041410900c441049a042c81407480300380e440041071196075222071045c13019220360310306041880220246070540441c8240380a010014500c22440111340040e04a11440c1001c140e40311103200911004062015034820140c2190400040003580e4501506c18402072007900c0d0344100544c0c03c400c8401c4049a440e03401a002480c10511041c0c1d4240c80003150f0001c9525510466881002440c50700030b084680d44510402c01d6a005070900840100210f1a044036030918003000031000303103560b001d2540314581b946441a1144d00310790310103001d0702000740300f0483c0d07040402c40501 = true := by decide +kernel

theorem cover : BRFrame.Cov 867266187 867446043 := by
  have h0 := BRFrame.cov_init 867266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 867266187 ≤ n) (h2 : n < 867446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
