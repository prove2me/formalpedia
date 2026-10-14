-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1544
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:29:57.044995+00:00
-- url     : https://prove2.me/submissions/72ca8363-f845-4ce7-96e9-6073388d0215

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 277517985 ≤ n < 277697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 277519235 1250 277517985 277517993
    0x17060f100f030f0c02030f07060f05040c0603051f090b0a05030d0e011704031e1808070501020c0a030b06040c180311010e01051804050705070507080105010e091c08100909 75
    0x14510316804075a90400244900074000b00680c0c000b0f695403001640180440030f82c0e441c00f04000c1030100d108560019074401c900c0703003401c1130b03400846003903d64000c600b600300038594060196681c040348201b2000c2c4d120741c10858110080740580034062103595244600743c010f444071110389028010050483d0307200c011828008080d038400c1ea08a82c000391903446401c04481c4c280300f440f800f569241e11244846c2c030030b00c00c1e03100d80c4141956000b001c1198500403803503d24101d140b0800030346200e40c043d203405401e02d000686403105030071f1000c0c001c5091f4481080410714000d10a40c21000c11280030035558102c040448444016a60715040c54070341c040d00104102034402c107681e48400c00e8071030484404d074a20042d103080c01103104030000380b10303001030700c2070740f032070700740e02075648035000d03040141c20b103055901e40c90301d00132207038205807010380d901c000500c9060103d05109501c2041400141103640101d5241245080b148440d4800d120b8060003050b03030000c410749154040c0c96044c10800010780d240c03c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 277520485 1250 277519235 277519247
    0x190b01170a05090d050c030d0c0e22060807050d021e060c070f12050618070b0f0d05100602070e04150e0c090603010b0d0f02120106061112040617060f10 67
    0x203041c9159101c4d07000b40f41d25a90150094501d580e000c0805103003000c200301c9071080a403003210714041c1001400c1c45000c4d02d640d144003042407020411145021040c0312080e5580071142c16030044482980404400c1116a86203240300060b954107944000e038481407403502203203802520100c40d0340211b020039032000070794000601d0001c07240c60301c0049003029035135541d4080800d505a0050504d4001100240d4001c05048050030f21314201c90855440d60b0f41d40007a01e0454001180c0840d1103940000d40b040450710318022650005c0b160a9942d00061074520060740e0340500d48a4552841300050015050152038a6102081d20900c007052185502e140c5100f501c41006e001000d1103000707103601182d000c3c10705200e044c154110181234000b00380b0a544074400441c0d10741d5002c030381c02000000340d541e84403000e02030701e0010407507501da44580300080e020395424414174603a81811814140310030480c466002c440c90304028401c851001c15a01e9030000b00300741040c00385415400541c108006110140e00031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 277521735 1250 277520485 277520491
    0x1b030d1e0506060702060f03040c180b03160b0304170708191b08030c070f0c030516060302030f070e01020a0f03200303010f05101106040506060108090303190b01170a05 74
    0x49007000159150410414180948140690403000510600c540c0000d4440213540041c007910114410564444022003d861030710b14000e840c6840d41c0502c0b0a0b810104109040c1003580401c0c0742e01c1d5814150b8841c0ba90200074806002c41e130140c0c604c119950f1643c4111145960441d1940742d642a12207100051040c0360340e0010001001c00d09180800007510f60200003d960003807a99203540c42c2e00300a420141c20980d000d03074190303441480e510000744028042c80004d5200701d000d045109034035650310f80d0810190b44403105140c010402c1000104500d50301c6588000142011400c0d6107002d80102c0c5080d5482500620101c1c0c0801400140b40c2c1180340c24200720388080c02c04040d40c485003c80c80e1217000a10807107565020100e410b0200f8074100c0c504c0300055003075241c95041d014a0703071502460800182c5081c0c0e52070f002041813200c10b50f0310000407940204640002e5286051400384140d400319541c0810301c4a641d20701618015a1040e541452180d5102c202034a5906040703910030020300e415 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 277522985 1250 277521735 277521791
    0x10204030c050906030a110f0d11030708030f0304060c12020d06140d02010203040e1f29070b04021212180a0906050904080903070b0d0902090601030e031b030d 70
    0x10341c00042d551906403102403044d00c1c050013404803100f95a40d62000781c85500907855200300e114141120b15203e41440200d02c60081c15203800b0468082d091500301800d94101e8400d0750010020480c620303150100b20303078200354051400200750040803421220010700c1c0002c00345407400000c90721441c1c1d195810500603920000110000452100d04001c170305400d441c0000c0c00b5070030a020070000f03c4400800c0c59449020000800010301c0e03124040e5000d0390345500164040c1c10b48150604230400303070050101541161440303451800003551a842d88098000300028442d14680c480c000408000340000b105544511002984402d0703022a80003100c0c0a045a55008091054000852085d10700079242103402c068030f60711903900c850302c44035a0391380071003055905032040d484c4c0001c80400420062002e420139820000c1c100e641441000701d00900a811241014141400c180314140d001c022107030300000d8860000c03a900c4418004a007103004805080c1d003260310704911007200803400300d008041d2010b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 277524235 1250 277522985 277523003
    0x6050301140307030f0609120504050a0e060a05150307020d08040c05040504151803080a2c0f0a0c141f050a0908070e01080601060305070f0e03100507031d0a020f0f012001020403 78
    0xf003023170813a040d00440c42030540c80381940104005002c0d46000c903a4000c3e101030b101c071005075211404030b0400c0780001c8442d4140e010000400802d20381c140004088808149081c946504140e07c42004007651800707100d108641e81e001107010803114840c5078030394050f60001401020381c00e00000b451900c41001c2a00414402400180d28202c0b6115a040317041d074803d00c071500c00410301d5810800002584c0300d51001e1003400a4042d20170400c103c1003400c107125500710b200c114140707004462644072484415004410740240325004007402c994075509044240b41c482c0d1611640403044504981c030340c6c03268050b8080c0072408142c1c1e80021a07040d0503074040340200d62803070b6a80c0748203c040398411200400040c00d5684d102511521a981c0b401c4911030040880350030007035031901c41c400c881060701d400e40440d0b921000c3c192070392862171000d0741e04005a400350260030141e8000c50ba4004005420512810214a520105030f0080706030f49030700d02908089450700c098210400c1c0c000c0d40280000e9841c07001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 277525485 1250 277524235 277524263
    0x203010602010b09090d1103040f0b0d0c0e0d0303020d060e040f030311120708070908060a06050a08070b1b0a0b1305012012090309040f061703030106050301140307030f0609 76
    0x50204c0114050080e441c01000d0355184044122154181407000e1092400101b0000450000403291000a8078480c04d915948800c4203c0c8130045910212041043c08400d4400000c965030715000c1110031501800d025079035031000c030080d6008040039001080040d00120512050007110001124154840c3e1010402e2604403494900f10380580303541c000100a8007000208454403075103071213400070250b007065009540c03503c0c0e100741460000c43c1c201c1c6d51680c0da4074042149181c000e81103c001c1c989440902111030030002c00d0b0006200d001001c001c01c484880c0000e4800ca0100100c030b03d00364211440c05014100a9102d2020310031001c015a0150b00300020407080550030307920004036040d045a01807509055046144400310020941ca42030f010502c400855a1101d01030590380055040002802e42d083c00690410041c0300c000d07207030140d2300500051140507048000c50781550054045041d8140e04100043c0c905001b54000501a4458984950402c0550f030000b107a080e20039411214422 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 277526735 1250 277525485 277525489
    0x71205220e0a0e030403121202030a09030f0f091403030903150a06050301110304020f0141030c040303051c0f060302031c0e0d03020114070512090a1524090203010602010b 75
    0x83c101540e624100d03001000100700103840040d141400c0071250030451a03c1103140103013000c980040300c4180030319848424450030103a014200c4004000c240c20b007000402c803240340c01800c0c4c14440c000e01038070100c118a1030700255020010740e8a0f0f014001e0854404100d8000c04090035442502c0100195040090200b0b541ca0180101c581c00c18810f0300c0c0e1030942ea1103400700040d8071045001e10b1b0510040d000c00305003041c000140c0c1e0102c00843d24080000c0c0700480f1000440000e15003c0440c802424420b10481c4c1c210502241c0c1207940600d01941c641740d1301030b0540f00116400c1c1c2401c600b58a0b0142d41c0c00502c2c07890300904102c1e8002c8054030180c220b0b00150021002d0310905180001d9901c0b142d11210f881c044000314543d602a10001030134101380004c1c035464860581e0181d0220b103001c40e006007400f40501709954081e9284000c1c02c400c107507940d030700501084800b003c3d011b410703210415468820b24400380c2c00c1381086003445a1180c25034a41460b00203510a0044000550a00e0001d118034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 277527985 1250 277526735 277526741
    0xc06080709030503070201050702130912120e060402150d060810060e1e1f030b0609011505070303020a1b1209080c0f0d0c1a0a0f08060303071205220e0a 67
    0x120f81107000785241004681c01185c00b03900c0140100d902500310a8031854102c01c62003030440e03092282000040004d072961010380941021312852854a090042c061000000460810780299043c3c800c0c0c1c804205041481c03a15006045411043d81c0c0f034280001202c0000007242800240c08003420070443e40c80388031030340c1c00c008201c8030b505a590480104113030382c8180100d84c46d440003401c159203050000c1b90702c0c1d41030389000316402640c80c1e25002c4180815071808040c81801000d0000d0520700d81030400c86c0c0034016000d0b907800502410350100f84020b885000301d921b0200d000000d003004a0b126018a403010441d921070f04440b0014015600215460400062250903d50010701c40c0d00f0b444501c20070080309600400085032b5140309005c000803a008040c101034102440c11220b561222882c4500a102122810b0000200941f28003400040e40300031048441c4030750400c00c82e0003c4c032104d1006072050711400d088800109400300c2c4180b81c4024000038803058802c851040d403000d80f164007202c0c1c11303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 277529235 1250 277527985 277527989
    0x203221d0106080f0a020d060902041403010c080f04021903030c051005060307090213050612091204030305030415060f080706090f08030f0319110903010c0f1b03020f0a0c06080709 79
    0x2080507180804c036900302540c5040d9000800171405840e001401c0c0f503880c01e40c0c0f00c0d90720403910260046001e1040b000040340307058020500f6030080002070303844070340240481009031000381806425404a019500e41407021020206074540302d4554503583d05d801000401151030503210340c000d503014074041040318003d440c000c5134018000c00381e05003171444800095001c44144203651101c07000c00202c80c0c945101900000c410b000904a9070325100041e103007400208019944480020030040c80040c4d00003042c0e03500182c010320724070340341c101c0501075600621298111010302100041c0018612000081400c1910390780e0740c55404840d0b4944001054444134015280361740c0043c05400c1107409020003641d40031000390000440984031000e24401c8440070286842c9241c000280301855003424001c00903825510300d400c042004490100810031401007200c9a0007140001c40c0e0000d0610070003030b03020050340c50383c01d64800711807604d4000202900c1d44604030126024900040301c41d80140d1115003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 277530485 1250 277529235 277529237
    0x4150605010e010e01121406032506050c0f01091118010e070522030c0e060108040c1512020d09031b080a030c4104140906010203221d0106 61
    0x1803401d040c28010b40e20200324140341c0e410040459001c880400c1b19008050f140c0c002c200d07446031107080c00d4090504080d44802c07540411122840280c01089a4581180c1140e03114a42161540b244290072810000d010104d6081507080c1201c000c10b02c00903651880a050084030700d040100d11010381c03140f01103024403a43d54140708100c0054803090240b40202000f80b008002c0c650f9400c540d102d228014103860304142e13200501c80707105002d4041c03404001c580010090030005014135103a514821a20b4a501841010f0030f110146088454081c440c06080080440401d6440da20841e0f11103000b081b042c0c4055000031300240c2c14035101c0e0000310922502c20703040713100c1900d04941e811040d0085c00034041d60030100800c401910000a5110002601e0035810107100500c44c80c0103401c02c81c2d000d00088030080205400c11007044800480031a86602c504261003011090307540c1c2d070041c2c6c1540500c003100e11205420311081910003c074000340d4015211050500201c2c4024030400e900212001d00400e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 277531735 1250 277530485 277530497
    0xc0f210a0917130317090102013606060b04170106050405011805060f090a020c150105101101020d060e01030b130f031b1b0e0a14010515070501140415060501 69
    0x10391160850010302a4409401203d08151380d2a0340311560440541c1d031301e43c1c0e01c80001c1081b00d0b05607428000d6481068141d24440c1d481021142180141014034004144140c000d45041c0c08210785900050001c1000c0301465850300c1d620101c440c08074103c0559460030354a45600413500d45407a1003980d0581e00b000310111012501c024203140181805020990300512140410385655501d024003841138442c1100540c43c0c01103c01d109150001d51704c00e0860340e10701100140156150303000d201c9000c80e01d5103802c401d020706100640740248100004484554240784011400c1800040348138100c0303128101c041f0040d525440305403003802039110014100d00c01d141502000c244a00103141c403466041072844604d48442ea00e4100106801c1a1040f41a030300c0130b000c019110350702d9003e0742d00c0000e03414113000e949041c44501c65043d0050080b244140c8003080d1100201d200030058818060b4014003c0000c940d08004846458108407012208194501c0e80d4600c640c681c1c3c0900b0382250740c180c55070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 277532985 1250 277531735 277531763
    0xc030e0a0c05090c0c0102040603020d050603010b01050a030c090807140325050603250206090c01090503030409051b040308030a0606030e0c1c0605041218030b0105090c0f210a09 78
    0x210f003e141c080d0240140342000d0143e0002c1050070302c0180000c00903030314010781e5034040700c4041003a00c0008100c0d40c03081c0d00d0308a0719440303070741c120b0304070380c82400e55190004040100d0350003640d01022a42003030000f4420884081007000f030a20408202c001c045044400858400d100c0400052070850381e4040c030210b95008100a0914002640c0c005003c40b94400220038603060400d00820b40041140c0164081014030558000034440b0074219007007860700c03840441c00c2c50b01295592285101e5407c44a0b50350001a1080c1d40c40f61050041301070441c17103160360b141d580c1400d01807900b044d078064403400c0c607001c800680f903030283c0308201d0715005400160044c00b1b20301d0b04002c4030500343c20440d46009070dc4ad40b0f01000558070b200f2213110300d10440350440c0e4403030f85800007090740070444c107039000050200d802071004c201e08218481c1110002c85154529580da00000816801220030a41c08440c02180036064000e03030247d11000425074003809021a52000c24120684074000c4c0c0107000003080703201e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 277534235 1250 277532985 277532989
    0x15030c040308090a09020a180602010903170a09080c011a09090d0c080d060b0d050105040c0917030f18151303030c020d0c0b1206010c20130f0c030e0a0c05 68
    0x5440d4200f0024401881965510600c009031f900660845c2e00141c240482c02c11900f40001e4032402400d4984004c004800507030307501800b0040c1c03145050390204003460002d802140300390846007078698031103090b5403902c0701a24080d028081c0c01461641d160411100e4402504043e5245441101c2d600004d1810303c1030803d00707a602001190040d542002c081120f100a401a80a40e0005203100c0a880b5034440201000c0b1046481c1a0099440390741007005180300c00d82c1c8644c6d01c6083e91000001611811800c0041c2450b42c030a40003c0b03582e590340400d65803041e278800380c290940c150303056803140c02440b6081c00300300c8588500309810904504958042c40480d21038a00c81501c24800340100345550b886840341c0b003e1424075445040010310000d51000e4260380f103240d9507082a400c0c20b0000c0700001c555660300302420020321002c400d00d034a88007041246e460101942c444100d8600800c5101d45241c0c2130b001812031b48402c08003090500d0724800040d1400903005c410150801d00140d401410141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 277535485 1250 277534235 277534237
    0xc060601020d120c1e050405090c030f280c17160914040f06030506090706050705070b03040f0c06020d140c07150c05060108060106030b04090b06010e03070911070215030c040308 78
    0x84101000004082081c145c10690080619444a40c99032500c40c1c0c030782010001c0c203407002014141c07081001d000780b03e9111107042c0da1030b4012090490b080102844103d002c0c009010291052204a040a07115440550821546452195032410300c0010b82c1d2011190140708002d07040d810300140901c0002c10128440c0c100c1e00c9500c100050010912007004c000d11002d03501d0381d402c1520150003032010701000784020410305004020314180305042c00041e465071a00c600c985e2044032071501001000404100340c1d03050071505143e205034820940d5803100303070096554204038604804981000c01c281c60030355198060f070303100164580007810850309080c42c10000741410900364003404100809c240c0000c4041c0040c034017070007228004010b5036241c02401416550040125409a03261240309004a0103201c0b200e030b4410000c1c00c0201212400780082450640c2c168064910304d4600300140c1c01404056006003080c90007101c00700003040744180d514203a8072050b60f09100c40102000f00b000006c41c184 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 277536735 1250 277535485 277535501
    0x3060b0409051005090c030703060507020c01081b0304081b070f080a0209011a0417030306010306060f020606012010061a040501170a0f02040e060a0f0503070306050a02041a0c060601020d12 83
    0x8811b0711120355508000c00c0c076000c41740e001140d010381c841c82003001e410350401c02e0001d00381c2e0900c1c1c403007054140264202070000151000800c20000080050b06201007002100c092101c1070507216503555185400a4442a4a0003905403036040c0c40c10001d2890800103031805180e40003040d1443c0c070791034500c2043c1540e03261042d04c0060442880005504ca90301008000080c0c40080916603a1910000042c00c0383e066400c40d07814000d907000c510b00c800d40d001038450361005003801c0c041c0c50b81121580c0840120038948030046107100e010034498900e2036940285084510700c1c0c100302c422440703d500b6201180640d001d00f6002880401c06880381501c5d882007250000060f81000400569240c103813002d9034801c1c0c106196445c41c043c00e01640b030800050040c0240741d4440321403403a6003040006925840148009023940c1d4071500851100401a8115002002c2d2400450940340748450342040503044107184a5031801010f0005002e9400442c1c0b043d103c000c540c0d03071800000c00d240e0000005040345 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 277537985 1250 277536735 277536751
    0x30f0e0f09150603040807030f0f120b030a02102a0f0f060908120610090305030306040209130f06030b100b030f0a2c21070f24020403060b0409051005 66
    0x442c1071141c1d02e8552100031409140540206a81d400450901134040f96002078124104842c04500256403076203d40c0e8802d0120303a400340414001410000207107020f0105401a40c030603056906c10040c190003850702418681901d002d0902c2411440e04c0021074410380c40054000f840c240d2100c0f00080d4044180b10040b8800c41002030b40f1310482d154042c45070483c64000480f43d580c541444498039110902c0c4a24040d2403030000030042c00e41d65440c0e140d00014000a000e2034000c10303a01919601d44400340d54008900d501006490000301c4580041c00c058841900c4001081f40401d9102e10f0380f440c10010f40740a2501580b6585440da1580a0a01c00030402024507076035070f411402030100859286499508203107000c840d1305001c0105800c0c544101c0c090340301c01030001c110b51211403000094540c0242c200550825000e40d609103255452103400341e032002079404482c0e4031485030b500d0b8040c00076280224400c10810349c0340c605100850b903480502a142e90300c48007080180500542085511201d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 277539235 1250 277537985 277538011
    0x1503110714030720120f0a020f030304081005160f0207050d0204060b070b06011404052107031703090106060908030306151902031c05071209060209060313030f0e0f09 73
    0x803644669401c80c0f8001944101180d05141340d40f084e141110710040350202010241241c0c140344181c0070f56a0101941c02170103002c0042d400c0940e03541c01d2003910010003010050342c08003246c040304600104012508115034000100950395414441c0c50b5800240d40c003900140880c83c1090204541c040074440200ea0140e01c915000c900d1305160300140c80b4942c820701c4808441d062980c00075101c200e0003080c8141500c814001003045540e041c40e021170f165a03851040c00b0a1740708610060030729440760806030075040002c401e1762001c0048001184035006400080281a49450b402c44422015116081d03a561090000c81c201349400256001000441c0ca00140ba081e002d800a06042078404150400341c0c001052202403640300400c00c0c02c025500c12010001c6103402d4001900720389c22000e4105a080d1342d00040000c0280719412907011040c010700c0103440389441e00c84082d19000c00a421000101005111003285000352954980060000c11580000c2c4070001403115012004101380c200007a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 277540485 1250 277539235 277539247
    0xc0c1b1f020a030305060d120c0c061b0b180604050610061706010e010c021302070303052a03090a06110301030311010606050306100912080903060c070b06060d0b090a06150311071403 80
    0x610b07041594a00c04403500e45000c00c054500b0000a10444bd50000080c400d40110f881d0740c01e03407400c0000c8003440e4065442000d64440030b41c0c4506186503c041803029200390b0080c0814080c0000d07450388038000d1400313503c1c880d40e21071400f180c0b001c4420003d080c00c01d00700030101d101076029000044d480c40062510b07188001058001400c101c2c4580403100c0300c82c0e40002c0d4202410340c140903103607119031042030001ea8000502c3c000f40301c0711100140d04600800101c04075610714814000c0090254106000b031101d004c0031042c03035660f54002e100840201705103800340e07040c601d01805001d0444000d625010308598a40d0b0904c42403a0206a26600304980080080358503a20341a50520340381c040c252440d21a0301c07a0080c1490a84080d240503102c0b2001d10400f400200c5600d60707107510440540c0d481e0340758038a142c1d41c42d0203808110540c0c0c0d07010b8900801c0003400080c3c0d500039000c0b00c038402c014030460300d000a01502225a940c010541e0039804102100100b24000c4600115413501800c59151039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 277541735 1250 277540485 277540493
    0x2b0807031d01050c1803030408060403030504230105010e0a1b050c150c2214150403021002010e060a20070305040e1305210d050c0c1b1f020a030305060d 67
    0x4500701c841c130030100390119004441030707030719800e11240d00c400342d00035031a042c140401c032640d0b480700500040c100340c0c8550001d820440076020401c0c0038290400c0d09110158841c40282c0603010900503080d42c001c94400041d0351a106004003501a8284101e034200ea60868908031021b500488011003644108200403c1d024501c43c1d6a030720403442908169100c10340e82d02c40180303581040702190382055005100340072005240c6201c01c0c4e0103e003100c0b044201d40304540c014400340210b6002a40c04000c12074807425058040d0400c03602c01e4000425510a540c40d90304940031181c00b41089860554002d40c0c02c00b0180f24240100700d140d000c0e041c020304250391040005d142d2541111055484c410180c1080100001040343c00303c0c8080c00a90400710031108018030019020780010700e842d55446070302159040105e18100e84003c010402510054000c0345200e403441040550b01074010700304e05440100e1440d088100010004042c0d01503c4402d201d91030440140c03201401840d40460005602c5e0005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 277542985 1250 277541735 277541741
    0xb0f0a080105060a050d3314060a090507140d0905011d01110a1b0c08060106170a0902010806010c0c0b04060c1a0702031606060306020304052b0807031d01 68
    0x2868034400200315458050280b107481c8007954091070113640003102e80000500384444d820480c7d0111800d0022580060004030340c0480b1020341d12048a01d001044405086480d1461b8480c2805072051800d2540e15151241116012152907000490716092000408154401061502200d11010500ca20903441d02421910396440075039001d0400c18070001350180038002c3c40c0104818040d85820b280145d640507114200b81484a862000d035408030a080000603a100805424034104440140d0384518000e05400c2c0340003018a401401400080d4414081e4003031300c40c0465040c0d484e0b500a4540d43c0042d1040c0d20300d110126509030070000003041803060440900001d00c140c1da0356081204103811700142a1024090f801a40e0200794200100d440d00001101c2000c0183c8800c5810080709041200060003242c2005105c0b0b800001884107000001640e10b84454220003a00c52403100f400b003100da051071030314180b80441d00d44400507a445010f13078003007400081001d500c5804040415006421 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 277544235 1250 277542985 277542989
    0xf1208090901080f0d02150610030f0c03020405010306050d0807020f0319030f111506060d0b0a1502070b03010f0e040f1e03030b030d0207090b01020a02030a050a15060b0901030b0f0a 80
    0x210f44c080142c071000080100300130481d140e05400a09081c0001103012500c1d031500401c021701403462907170040103940c46588004080ba0201000f04000c948107c40100030354070500c90540002e090550110309450705407816401d842d41b0a100302e203448250b60074440c00c804944030707999250042e1000c854104c04074984100c0114400c0d035034681c90302c50b840d50103041240341440c0c5c2d01c1a6400300360011420569a03064680103d02207480300c2d00c505900c8180d1004e08003035025a50403503014800091106400c60580c4104000c58094a0080c2d8941070030108a0100340718840c14070b507200404109011070224180c0d0080d010343c0c000714401d40c0c1501d82c11440008000c40c801c02910120502080c10f900d403148200d0008110f001d80262520404002d65400b00750040c04140380d510a50b44009030f008002c2c000303400d03902038103885c00541c1e64200f41c0d8541401500c00d540b0340b0680804079035072219a1050700141d41e8188491405c000c113074401100140420408144c000c908200c0780106682c900e40d8000c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 277545485 1250 277544235 277544249
    0x1506070302031e0c0312041514010f091e02070309120b1611030702010e0d0c080a060e01060612050702010609021303110f09130f0b100608060102070f1208090901 71
    0x143e600368008503003602400c103d640c1d0140303000911201e00c03022000310441e0401030400e10f540c0120340f554140301425580c0121803101441c600b07400e44e20300d042226a464129481032590780000740e602d88064094414042c0401c8032040300341110102000260f001d0001280249401d09000744c03100308850400c0044002035608110002c1000800000c0c0506c0d0750940f0810700e061501e800e864140390342e80303000b55080241441081502c0301166281c40d540f09190380d0b0404400c80059555201c0c15842d09030408055582c4c1e0700707104d81070344a690305002d000200d800ba80c1c0c1c0d0325401141081c598006180152855003155203071400010500690b00203440c5590304101118521491450001e503009220281580070728120b00443d003070340d0707140055658883c1210b5500340c03113015070b0328042030382171600100100001092002d000c2190b002c00181d00079038203580c4510359142c44410042e039641c00030f441220700300c440003e0180910860900349204151007502024108800d11001422140003604819 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 277546735 1250 277545485 277545487
    0x305130b03090d03090b01091a060f0a09060c02030c01140c0609010b030706090b3004060204050a060c05060c0c0a0f06140c0301030528020405090c09070215010e150607030203 77
    0x124890800f4808400010018142000081641d603144003403558144141c100981da9034484241c00c1600ca01640c44d0b0380f000a280c2d554448030041780d078446810500314400010110780300855064010302914502540040043c0050103000c0011103000c0d003c42e20b01d405c1d8502c140400c1991410030401c0034002c441900020502a80240905141c450541c0c000d40400040c1c0401300900c2c031807101101d1780e40103071381c0700c0c0d00c0748145041d462000140883e03200d0001c07044810810042c4601a8081c005a850444e2580741440d41e650741104d00350354420300a001a0050004501100303013900062110142100c1990400c3d940760701d640036000e140c00707030507252551a56900c0081002c0c200c5ea459005612010041c01d55040d070725015038030500107000c80c00c2c000b46640c0d96003a0303049860424038001c2d40103000b03001c540f40c01e901894461085042c501d0040303040d280810790007400401d5001070310a4401000000381c1c40c0c200805c07070700076025065400d8400340342c107400760640343c1500401486000750021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 277547985 1250 277546735 277546741
    0xf0304152a090608130203032106030d0807020c0d0611040e0a050601030513030c0302010b09041203060e190b0d05010912020c03030403080307030f1b020c03100c08010608040305130b03 81
    0x90004045440400d60800021141c2848015006984c050b00030400e202800910006131021a245108102d00b051a04a14a81c0e000c0c04a1034282e0540c03084505030151001c1c81c142410988401c83c042d203416025800224480d0b10a00b8210741782203449001d010040b5500e49403004007880342e8000d401a50040c8030350400c0000003511401201d402000030301c0e04125501d0545000c8030b403d94054401030070005980310400515200350401c40c081e010003800b15980382000e00d0820250042c4000803c0804c0c1030040c0000c03000f440400070b911560403001108401454440072000400e0000701301d9500c80b650003d1400440c40901c07a051080b489640c3c443c2c042a00020040d00c0c00c1c079034100c107034030030351080200b4800114940c2c26240c01c6500c80c240803444110503410700c405050b1044010859101c07100070b00100b15800a040300c0000303070a6050b0382c1c0c072440310800203081c0d59000c051400803a068500400c0440d102d41d5150741c1c4680a441d045003000c402c3c500081d050781b02644011003a02c404028 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 277549235 1250 277547985 277548041
    0xa0302071e030e13110f0a030f0c21060e07020c090f131106160b063c011101050f0f070513050111070b0c0109031403010b0f030415 58
    0x1c501c0344507900a000c003819501c80d07500801000d00b088005000701d1005803010b52421080d00081440d440e5840800d07100c1d804001c007090250450004c0f000080e04140c62494080b21520800c1c194008a40da40200c51001f14404a00c1420075000c42c90701313a41d203000c0040c0e00000c0700242402146137a02404c1d0141c21107080262101c0086d1400e21102d540c02c00b84404102220602c00125a11a501070034402c11080000c40500a04021500141c41c0001400c100a8500d09480c0b26030030031a010707a112041001c2d402c0740502e10a00c0c01c0468041d1403080c19907860110756031a0039080524188040107803807041a420343e80150f5040038441d91040c1802a09110f0103242984203500b403501ea42010700c41110608a08141e02c92107040c8244c04881c5404510148080806058254000d503603550b05244403d00078030300040c050300041d404029004a0031003200c03c49040fa80e008002d5801c142d00401c1d00030103688042d100320740b00c0034803912601141c566030045144580c92000310882804030b50701 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 277550485 1250 277549235 277549253
    0xa0605100501090617151305040b1005060d0b0409080706140105060c031b031b07080d02010e06241005030f0a0507090b0708041d0702070e060603010e0a060b0a030207 73
    0x480e0621144120502c400c55021045004242c0404040012504d075040750503242680d44900716006521f00555000340c0810b6008940030750310640c500da285c0e81e02e02440d4161041c45005003a03120004000c540b1080405401011a50000410020754102c03103654a500da941305000803642503849011801d001c161054002d4010942515568500b6001c2c4500c541c8912410070200e0716000141841101c00c50104141d9500310320035103110381401307a46014180c0d1940d541c0b0446410340b107980f010140c10303403043c000c40d40078070a50001800c0507107900b00c11070303c1c0c0d05446195906c0486c10625001d0540d41d00715a1201d00d07130140e15615903030708100305007010300b84000b40303849045400d00e8107110707a03241d00900c0d181c2143c900040321600e921261130108900c3c890f40d40154007030080b0170700b4410070000e90902c050054015808441681d56514190604a8070403118150b0010b818401008140200c00c1000c0c1d00241900000510946412a021407908190f545100203540464800200711141e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 277551735 1250 277550485 277550489
    0xf072003070e040204020304060e1209040605030c09180a020d06060302040c0c0c090c020a0501060303080105121204090e10050f1503060907060c081306020607032304030f0509030a060510 82
    0xd4080d060003030a241d200066480302803c0280921390001c00a414004194000c1940c280c0f40305c19542508804070718000300350082c2000c00c1c844c03031420b0b90004040c68002001c00d403081000d001801d06580d080300000c00004940b400441e01d000311008000103a4031000641d8030300c1d02c1402c001400500714018801100c2034400740c9428001c2c0041c101d00426040d015603011a0084407011130f003094441e2081b41400d9003810000c1c050343c00e00501000309504581c445068400942d903410b40900c1003000507a40d20301c040b4850254000c100414014511103802c10904003050804aa80c440305500b46002103517001c44060354600500401d004112010b0a5038402d1045e040f00180214100f01900075240c0702030340310380018003010b003440b842041045016110844480074080c0c40c207075034a41010392a684100e649200091416032140d601c040981c02e002600c101d2400c80d40c0d9150341e595000d039040403c2940000602500f4403009880d96030401c00c16a8080c0301d00c9000c5074034106240b441c3d040405035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 277552985 1250 277551735 277551739
    0x8030903030711061311130509010f0c0203070f110f1002060105041802131d0303040507030b0610020a02010e041d0703060c0201020906030a020711060f07050d141605030f0720 77
    0xc00d0900442d029030505d40644143c201031100c03602102c1c00001425548110000c207039141c101410402c1d111011340c0704112840b01c3d04014001a41c80c200201c0e01c92044820081203440c680e4080e0f0041121902407550309603003d0070a000b14150500011003104020592500517884000184414141401140c910383d100201a101e03140055000552101c41581034104150765111001c1d914210442d407000c03d890004244e90b41e030700300341c1800c80c3c07505010702090340e0801c040000329a940c200b20081c42c1c010840c50b030152030201603503401150191105c1101c0d9a102e91210b00881800c00100c003000e00d0004960000e182c7d041c40c41c9032250564002405030020b5901c1030000c01901c1d1120003c52340d10003008280140e90324042e1800401003200c03241840e030010004501a82960100401851060f000d02e0407600710f400065011195401a58400a4030003010b00c03024010900c42c2e54009042071007401580d04041022510040980001409540010045030b941c040304045540120041e901 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 277554235 1250 277552985 277552993
    0x307020c0a150503060f1f0206011a0a050711041a210304180f050a021c060308040b1b0a0503070b01170a0210030b151908160f0c08030903030711 64
    0x20b000c4045140740300b0382a150301802000000a0300716650071015003480c80c03004240b00c035801c903011101c040e4048080c40107009440703100000b00300040350241100071500106a541c0c901040084122007036007010100311003612404255011a03900c80c0284445021504804250300c07959804025a540d900d18100c0721640c9044401e05e0712840c048105c9060700c0c02000d50b900e01d048102d45000c010a510104a00700c0c81c50a814413503428000d07001821407094001b050700390000c40155060407a1418031004001d40e00802c01000b442004601030801c8640c110300b83c0d54a10102605c460501100100480e4150000604c0c1c1080000d5040c1850142c2a649035440340b0620164600769104a4114003034031651020800105840c4070350404050043d010302074200700c5840c00321402e00394100e00700000030722821880607500c441c0300346122885941d40011b07480c00303000300c8041590b1261030310503514108000c00b00f8240100c0d44100096000f0050b0381e00540d501d2400181c014501240d800c900540c80e08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 277555485 1250 277554235 277554239
    0x10c0c080120031e07110102030705040e09030c0a0b0c0702060d0204051503010f141203130501020c0303070201050301051306030803040b10090c020a02090907080f0102071403070c0e040501020d0906020307020c0a 93
    0x20101004c2d2442c103400650841c040d071a28407056889283c201180032241d80000200182c082e40600030300101c2d410030801505a440b180d03c015164054001a0015540031200d0f9002240d0b201c168980c100c01243c00303141c90041540c000c9041580008100751280c0e400280170022410480402404440100b11030307810355051080d00240d0350758130310030040f07040141842d603402d50b034807040c1c2c140c1d030b0001c034008481e03a90690300c1350b0500c40f0907944075141c09801059001141810040704440760030b90305075113407891603003032108108001003010350b2001241d42e039035004400905e1040046014500600008159180583e8070710000c40d02e68010120003411310b4002550300d40c000646802d0164119641c00040d42c80e0707808149410003540c03000d101c912903107982141001c0190300030314005008081d00319104642e039034140d0350703131083c0f9a00a100900c041c0003088006410000c003034001e0b1003440050701e000700001000c026038030800f03c10f90715181e00201340f0500540411a011101c2c2d4182d4081c42c03624 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 277556735 1250 277555485 277555501
    0x9110a05120a03030e0102130303080718080c0607111c11030a02060f07020d060c211116050a060903171003020f04020702030f0304030b01062318010c0c08012003 71
    0x241c100071000f8241601c44100041020b000c1d01070390502c3c080c0c020002c1c401d80d42c0f82402440564165441004038440781461400e103090820003005580205008113904201c0700140044c540c090b0500b5240100701011070078407039940401405419222201c000048040d0741041c4507024084a24140b003540a0172111006032513403420345450080c0c800c02207480301c1c1a400400e250f0000b060000307050600c0d1a488a4419030071203c8034414001042c1c034600300302c02ca0900c1c81c0031100c840da1424820300003801020ac0e030001006510740311510030019030b59034111300c0c1d42d81825500458000c501003000388001340882c0001d507001541c410000b01e001c0b0441865a0003180d49042e00140850049400040b07c0043d51800c1002c6007a003084042100d82e00d80da030341842e00b90007000380105000159130800d41401c0e00e00d031180940325007054803040d5280c03000746084403000705401d4103250706201d4060421030105d40c0f002c0f0040c6c01048070302c0010641152849803010940626a030f81d408205060040c40388034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 277557985 1250 277556735 277556743
    0xf17040506012607060302090409020909030c16050d021018062a0c05060f1e07060b0114040b0715020c0f0606150304020906010504032316080a03080c040909110a0512 73
    0x720414100140ea403030002300403502031310f0003180c040c3d0048540000e20030007840000c002c2240081c40303c10b071122464125050344083d00144286540030601c0d031072032005031030f11008900c519103003410020000e260200500701400c203103a01c003002244841e00c0d011b0003c02641007013045491781142c40324565469540384c40e2064201e000d103074080c103c042181a00304018900304d405540190f07484e442d40104260000303ca5610204080b80c86074180310008400354011140440b80d0060f203a00503040504102510f140c03908583d009903a0620801070740d0300003141c42d00c01402001d0714100904004441034907000d20702030300074024500521001c0c081407084201141502d070030940c12a2100007545615004884901a5401c0545583c03082229140c1c3e500f80400b8601b480c6849109440b141004400b141903505039620030402503401640d0228000b03881802c005a0001c03100c007016007015224104042100c8200c282180d5000682141950520703215105100a15041300d00005091407240c02d03940f6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 277559235 1250 277557985 277557989
    0x6091c0c050118060518010e030304080129090a0b010e0d11040e1c030b120105070c060e03030105090f04020a030813061202090a0506031302041416140a0f17040506012607 75
    0x7121000c6d040c030403c0780c0c0c441d080e4152103000040403281c55907140d900300d90007000c3c0e540441c40410900600085010114083c0140c0484c000301400c5256450300e000c00003800e03034010041d0401c401048100501d40e200291122030710300843c08044404072000c01c0c041280e00f55136900105601803d4841480080380b801d020340d01007107190103e0000c0300b00c0e01180e065001c8100d050040d5080108105610391701c43c0d4842500c1d40900303c11f002e884843d2001e10380360b200038050f042d04080740c04009040160101c00039900070f4070103400119800c1d80c94440040d82d400401c5403008500d1030240401c1030950040e01080010601c030b004519014042d030015011a004d4402da900401020000501083d554504d540600341c02501c2800754842002c40544100740c1192000c48200b80030900b20b82c091f02c59490070315644628203c0504c3d00110400549a03900705d04054820802c4c907148006882148041081c000c030b01c100002c041b03d506040e86680d011042055100b10f1001d0000507001074074000410b201 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 277560485 1250 277559235 277559257
    0x3030e0118171e01020c15040b010501110a05060405010506120c030604030f021002030702010b040f020310090203060409170a110a0332130608150f06091c0c0501180605 74
    0x280d154400d03041503080955035004981c40f80e034110b200200c820810340017400b913840044280c5400800c81f05120b00d48180585010304107400b18401400954080c00000051218020441e547d000b1a50740e610310703000c001c5908880c00c2c0d4541d01402024200026800000401c07980038054001e40507001ca0b40c1c80000038405010845c0c400d80203000d8900071b010092846018941c00d66482c84d000034068060000c0c286900d000703030315244500c1038034509407003a0b900442410414681c050b1038694030b40c020307410103001a64401d0342c13010340b400000c040080d1061130380d19403d10302c1d407100b9040c0c001070501c2e5100400b12001d5004806104006a8805010381550104641020440015441440030034130000c048038000c5000180011406c6840140b00c000c5035180e80e01c000880ea2420090601000d050320b03240d4120340800203082407890001c01901001d003000c0c3c680e05260040c00780e402c1144c20310f0002030b01c0794010b12409000e0b03940d02c403126000030120302e202c2c00005403610b040201544602c44181e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 277561735 1250 277560485 277560509
    0xf060506011e050712050940050108071d0406020703020a1203020d1506020a02040e1510170604080301030b040c0504110405030610060906080703020d050f0103030e0118 74
    0x4040d03a0141d10200c85501400d0605200265803280107002544507410954203404030312280b902c5503205004a810300940034286500349031070b24810444000403807203c1e40d86090031100c1c282200b2031305514081c44401840f00840e2030751404c2c411504100c0e0307a421483c005440b0007000300d1103140000c920364005a10a4005940c2c14180c1400c0341030094000008040c000007855610307016505802405070016190000c00c41101d844101c91482c0c241407181c417015800c58440312026140c544c0c4004046400941038550012240c050205001801c4503038207003904240d0000e014444d020320051001140e410001c2440d8105512204064001484014802c49680e00040d04000c0144503a81c01000050400d0025860b0b4820a6500d07070084e01440d40281710700b000050450b07218039010300488585803a81042a801c048089448850084c01c03002810307001c100440f04101e5901c02c1d00e10601000000e99025411341c9402004c80c5c0d4040d100c10b0402041e221881000d04400801104980c1249601 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 277562985 1250 277561735 277561741
    0x702060c1006090c030b010e01140d020418060e0a06030b0402120a0609050d020c01090f091508070305161d0a020a031e0506030c030f0706030548070f0605 68
    0x24604840c840c884036a0034104800041d680c603e41d0010002c6803290788007480341b513902c000119140180340d01980d002a002051f044200700a1000400d002c0940003000b40c541074a4551000c103058501c0c1404c500ca030703542c1e5020031061b9400581c071600502402c006010691075521040381d254009400a0300c148148070303d0824403e42042882c440d070794000c00a0000425500706075488101c84503401016005a0130117105035845407040360251000c45418154a50906007200c0c001c081d50f201d0040d55a9083e0340208540c1c0c010042400118400c10041010444004c51441d41c02420f40c4100046150003070040304800c3d21036001940000c2099005031650341614048000e8401d8001c6a001c0040744030b0000c9a6002c2034200a00c10001901101c0d103d0000350103041d5120091100c9644036003108034184138161094000c1500f0084d0f890340400704c0103446d1901442e03c0800c20210b10481da1407182600b01c0c400658010f8070001c0740103e11800c2003000d840e014907480c2c1c0e505000380140d660f1000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 277564235 1250 277562985 277563007
    0xb12010b130315051005150711120307060207050106060e0105090f03250e010b1201030b060a0518180309010c0204050408070506100801110901270801020c030703110f03070206 77
    0x514019a080540400740d032650b1080d03c8000d110580e252144a000218080340034142406071408001c0c148a1301031404809490308080902c5034051a6406520315140780b201c40030400140440a01581006944d500c5916205084420691002051150030496400c00740e80000c00d50300170b0f00b425038075901c10706021380010b82018025002e4141d030034140444071002e0b0904170820001c3d03520140d90303a4200d0741c0302c0c81c0c0c81140c0e0290740c4080c13808800150043c0001801a1881c42c0c1015014080c0b001050b00c5000098800310400081800210114104040d000400062410307103000e030b4001c0c5180c012300b035000800c01c10801e04064040ea03150004241000300030403c441c1c15940080036124513040084036a80c20ac4102c0c801c13800d25600b440d6801c00808641011140c6241050710707840c00c1d0750080c10711409c00210618501e00044510040041c06010a000070800352011602442d641e034000d1501404058007810444496441a419010070250010440700340c6a0101c0f4129202d5900c006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 277565485 1250 277564235 277564267
    0x30209040303140c04030204050c0301051c03030e06070f080f010806070e060706020d02030702160b07021e03100e121908090a05070e01090b09040f0b10050901030f0c0b12010b 77
    0xb02502240c02c0f5404000700c031114400500140e84c8221b8051106881d55000c07070295020038003a0541c84403055212620206101e03400154a81c8242804100390298801c01c90800c02c00b00c0720789003c00e2190031500380141e448160303603901614090401c0015410904219a42c40004040500b03000080b00d6070b800380e603280403c0d2050150b001d0b50070340d83c0c0d5100102c20f00c060f40056561101504c6600a418488080a00742a007075403e410111070908110341c00300241c0711034803c9070080e00743c100b507140380b11524140614101401e480c42c010505002d43d0301740c949461644010789070007410610075510501040902d00c8681000c3c0c0c80c251215840b64403601d030604a407540010202d00c02c3c0d000c00a11011a0340844c0d040703031041002002800f03045002c2c0705001001f1280240a41404111000010001c448054024241d0b00b4141c0c030307040c0c03200041511200283c03c1500e800390241110420040010507505c0940b06044500d401c0411400f086583d100040c0626000c3c8900800c1d480400040703d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 277566735 1250 277565485 277565501
    0x20c01051308061e09070b09040b0103020f1201030209060d03092c010e090105060d0201230d0207030c0212161205030d0203071224091a0306161215030209040303 71
    0x5441c481d080c10848080c3e010341d800313401448002138200003003a152000c80d01c10115621034903410310f405c4003101040b0082c0f212590090615a0901c032448440c0c004d1000703010300d001d80c12707021201d0794118010010f1400004100e10702c01c100000702c0500080d0300c00d002000322066191078a50206406002c0086401c5401010a0f0a035a42c00009140c00b09000c0c0103000c0e41550008204a898000c2800b19145041c180680800c9001c5040b180f601c682d1009145a880020324282c2803010700e0f080307d0280c0e404441d080d03000840c445040e078190300c5c1c04055162540c1c0301c0384c020110309500c8503140b52805040d2280c0c65203202d402c8402800d10030140100c4284030010a0119924070741100040c0840030240c002251841c605040882c16100d0300341c00000300c0d07900e600702400703140ca420034241c05802604c07100c20384400e504044004603102000414001c0340309180041b0a5101c07110001c01803091110250305141c2400080c560902026454206480d0141ca8400305c940c0d0b141001d0780604078030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 277567985 1250 277566735 277566749
    0xc0302060f0a030c0c0818150c07080c180c03070e10110c010c0312150305010203010902041d0f04031b020d03051c02090616031106010308090a08030703020c010513 72
    0x340210303001c0c0141d00034502d044260f01c0801c00e00c2003840703048035054940c2c440103100490810600844050b41a055104100020600b4480c0c0100c242060000c1d0802c110403c001e91000340240b0040c5020f006e1401000f07010b84149000c0d00c01c0c50b01c1a5502c800c0078010700c3e840d180c000080341c18940700310f00c03002e00c00c1400350420321803420b04500181034102082640101d40507410101d03407551300c0398010f440d456030550340c2e400d0080d402540e00c0b0020000c2104d00a110b034903445000001941c02e00103180200030350180140c90f01e00d00380c09501c99404480c100c2c1c142c001c80b24204900141d926401c2508160503260004000305846a40b0300c682a00da170010758071004030f58806080643c050001d000d0300050580c04d81d00c0c0c4540d0480d14090340154036080e544050103115100d40001681e2220000c14024905036600345811000d003414803100781c000b83c0700d0b6140001c064007503080141d41c800c010f1001e50001c528007080c0e0746000303450740d406c40421070400c07400143c2e010940103044010000f8080c6c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 277569235 1250 277567985 277567987
    0xd180b0702210606040e010c0c061107021806030f0d051207110f01060510020307110f04140708041109150108040206040b0c030315152209060303050714010203060d0204090c030206 79
    0x1582e00b280e4891045800d244680e00b03041c000003070848180150103031034003107444480150300c007540d404014003601d0400081c05017081c403480c0e0150780c46030030701d0001011001b80302c40c00d400c0c000706050400441500c0c3e2452135006c0340c0c220195a9102d41200d8a5100000141c0d01540f103404d41222018501c07203c6007094800c1a4080170100410352002c0c0843d48101d03680707080c0116985050340c4900510070064101710446001d681c0909290806c1d0b800c0798001000090080e290003c40000c174130050b54940006180c41c2b040004001901509112009044642e5a6640341c4107603d000b00b251000702d0179042003442400b240440d220501039802411120506c0f64880c420744501701c1da41d402c200c40605140610440e0441242004030360145180100e0004528044602c02007100b0610310410703400c0740d1611400b0014051019104082c06140729503160f6583d00c1044c200400c0e2602403007030b960401d034410000e000301707656013000c1c0343c903032990596002c80d220001d8204858141c5035a407000c0c0d00690 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 277570485 1250 277569235 277569289
    0x13020403050d0e0406180e010e01050403020f06010b03040b070c020103090818010e0a0302010206180709060b0c0f010b010207060f0c1502090a0f08030d050405010e0d110d180b0702 79
    0x100104440104100326620b103c10050302c41e04000a84001e4414050f0104c10021600e0907224542c103c0016a040707100080b417141c0e5000a00d9003141c004540950043e000a0b01842c6014400e1016500505144d50440c5c154101511650303100b400207800c0005201c0401450740459010342c00903146241c0100b200ca441d0240c0352804015a4071485c5e400c0e000a0891000655915041d0100400da0fa0180d005100b80c1c0c1d00c0104042d203140d0010321041a511a0517130000300c1c49102d011b10344c082c0105040c0320740c4504061400900e8021024096580d40e410025044010399000603260200e4850340780192401c240d00030140c0b1454802c0340c02500d100248544510301c4030064000300030041080e52030401003070383c1c2c10b40d11008a000380035911940c0c208001d07185040c0101d0b00300b6900a80100f000007104a5240e000d545480c182402c0344000c21010102142504001d02881111405505064012803840c03103a561a0040d98052060721140208504040d5107a01c003010034018503140d6182c922034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 277571735 1250 277570485 277570493
    0xf01140d061505010e06070804030f0f060c120509010b0904110103111306020f0a1a19140f0612060a0c02010b130e01060b0a0c0b070e0d0b0901050106050c030f0913020403 75
    0x20340705006042c0491704051101c140c0b4100002104c41d9660000c00f01ca0615040d541c40090700454030205440343c2e2441e00318200411210310844640341c2240c2c840300e540c1d4814480020980e20020160715041c0d06d0901c191701d55807601c0c5842d40d44aa0321048440e403416080e0010307001001888100300041e00c001c502640c0c8080d0040c081c8081da1015001c031a4103034181400f583d61890b41e40002009140c01e030000681052000440c160050940c080c00038900c2c201e00341040482d124012208030702c961000070700c0700c1d5407204020b80350449001c1d01e2603242c518844004039558480940460a81035a81a184800c20710030740c011580c90b000104000c44411403d40c3c0f0740c0107071075051040c00e080d500c0d0160010701010803108440d0b00314400d840703038141d80300349803200115598028883c100380b00302c40640c1901075650300d442c40341d900d2041400603005e0070325000c21400c40300305030042400d11800300080384140d032001017554184803082152603554041d0f8404103582d102c003002541281e03400820040200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 277572985 1250 277571735 277571771
    0x507021603051e0105091b0a0e0708060a08030306010c0201080a0605190e070203032502010f02030a0204140603070c0209150a09050108300c011d07050a0605030f01140d06 75
    0x2e0207840c1003140b94074404443d0309003200d034261106d000a5000c010b546280d00c0c0651440c00c900d1000501d11040d2a6441484003070a03002180c0c4c2100280c4218100141464144003400c042d02c19a401542546007100010340070204c0c40c48082e040c0b0024900242c60082c50380c0005002e0320005d0500c40001c035a414561a00fa1941d0003410111420003002440e00d601c00800e03a44038102c015041d040460b88013080480c0c1b24901036a03c0c0c01c41d52140100d0300a12407600045000ea4030040d00180d07900d2810b03840d980d101d101d000d152845044104103004400c0d03031005020500e40e40440da44030580d1151294945141e809030011600f0107035007140000d580a241d44140d0403030342000141c80b400b1048100c010000c0c9008031080540e1046001031700b4980003001e0103810042e0f050800099040c041d00f4031000500d003030303c08074540c0d41d003d0081071006090860b81e220050849003481419410810b00c100c40340e000c1401f40c3d11000250340c01002455071580c0e03e0200302c5400000c01c20ac40b4061000c44448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 277574235 1250 277572985 277573003
    0xd03020a110a030e09181b031519020c032b05010e04050d0809120f090f0a06050d020a03060510020f01050105010e060415050f0a05072f04050702160305 67
    0x2107607480344100c8240314041070a180080e81503641454014100e81048121240a0003d00c192074920700e107441c0b0698100159404060042c901c5aa2680078208140c9008204d81d009a01c000c0c583e0103001d038224405000d42403c100700c00f00581c5075500324007030501d1400303440d028151004d403407645032000813209402da00c021032907018103200c10707a01c0c3c030484000d48000f911b004002d94040e448040d480c901c41c40c015074001190303400b51101e52200d41d903403055940000d0711020201600050f203003494a130090462071800c10071f0352040521032030000090301c41e01404086e68051900081d4400d0582d10940c020740252800400c1d401000c01070000096407000d078003445403003943c40c21002146c25801723003804100c1c480740140910f140c541410358440381c2ca02003010220a0240611008000c0c59480c4042c0021041940e1017544070f441a04280c11854041c815a900352101c8817403281e103290440320102d10402c415180480c8076101c1080403841c107100203c81c038420881d46c4174044100200441d503111 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 277575485 1250 277574235 277574237
    0x50c070f0501080a1a01030c091a03090f06132d061401050a15200613150903090909110a0b071703100510020a0b04060c030e0f0c1905030d03020a 64
    0x2a06607984c0c11107400f11401040580741d800d8603644500c1c082d61003a0800746881c01c00f80307899481c0319079440110741d099010089550700c0740320110401035010700800c20b005080820720010090380c108080303952190044401e01405540d1003260705844001c44888880b00260f411844480341d408504040006100200039013100c40c3c240c400001c0e1300d2400240c0c1d00c0540766802ca1a14607144449415030b4003010f501d00c881c0b203403004400e415180383c6007402028881e42ca0345280248220040c03809130344e41007440750806035140c5094807a0000c00ea222501406603480c005000504030f00c6410400c4058180b0b000c01c0d9270201c40103d0108812035a00080c0011034410800103009850041c1d40c002e03640821a03c011184504150030000d46c68801d2403000c043c001801903945a90943d2101858814111016181c0e5501d84103c0078011798980310344900c80f0070300300207098980c00040c683c0c2d4071000c03201c900c0c41c0304c0c201c402e14500b100c100c400760510080c20f0080803110b40c0000f82001a02941000c03000d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 277576735 1250 277575485 277575497
    0x1206061d04050c03010e1f09020a090b0907020f0a0f0311070303020d0f020a0b0406020313060504110f01050901020a030e0f0301020d0902030c090912031306050708010e01080a030806040903050c070f0501 89
    0x14070fa8101400789030074828003140079248808018000f5400f16500b104642d000648400c10203000d6105c08000030043e04c03e500001c240261268140300306c42c10080d0121003158820100458024004510f44c0c100340d40c440503085402425040443e6403000d02e66040c80c04d0b0146400010400d90001184409d41c0c0c4648c680c48110007a010050707840fa040d02001a14600004d800100040e005034000c50303009403401c0f450200c8007126110359003218012502103a101100c0030141c051454100b51010803400c00746401840c129820f030000b5140d0014000003003d04c0403038a003c110740e80e1083d4101c42c0319440500210744410220b03034140050101ba82080e4001d00818042d5000e0b800e0188103d44180f01d444001c011088886103010502d900c0145040000c20561441c440003843d68052513008841c00c0d51424003550502169401541040e4011100c1c0c1c2d02c901d4030800041c1e0826003440d8041001c540003c0c03610080e0130150341901ca039102e20941809003000202e5105d08412081e420341c2c1080e0307114 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 277577985 1250 277576735 277576753
    0x5010e060601140f091c0c140306160e041d0f0102031501050a0504060513030c120b01091814070e090607110c06090d03200a05120406091206061d0405 66
    0x11072094810b1000311140f4900030041800a418401c049210b007004040e00720300c011a0b55124240603c0d60f82e0040041500716220244231880c08000094000c0c540184200c800c0300c510700d0140603e2030200c4c080e400b4171349800401c000c200381800c1d0908807138050002d030f0700075140c540c001703e000398030450342002c1d59110030001d62004d5102e1426908511019220949010b042480a50b0726400c07108040340504092403011002800f00c01031a8000d2261808580b0300c02c1c0540f802c03041c0f45070141c0140c060036103004400320410340031810000c191604103400580e61030b00100501d00b00b800b00d40006050002171000c4c403001d0340c4000343c0b07544034a40aa0f140d140d03200c500102c140c1c07601c14400020741d02c540c0a1104c4c044602d030448120b01d489201e4240540e662155266047c0c600c07014456000c8107410002c0007a051000c2800900040440c6401c4180391500b00000580700615a01440a0314054400810100145031380f121002d0154035012412001004008070503c41d012242110f0600580c00d503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 277579235 1250 277577985 277578017
    0x30b060d02031903172707081002120f041e02060d110301050909030a08011a09100305010614211801060f14100e060c07030c09090204050c070308010306150305010e060601 75
    0x45180210702d642d220035130355046c0104550031409141c9200d509401742c1078000a020b08100245070111507010340160701c460340c0700c582120b0103034000c180070f1214040e00208000141c500004071003400980104820300c5605002003506c1e40078406a0302c04461411881028040001d0701560484400300c0305840c690395182c0c0d86c01e4980c040c103644840032803c0d403001032000003220990402130f0306030038801a090204410008440006120400c000b1940d07c0c4010b0240c10b0740583c032145024840a04a0310742540c80c1c0c3d120130100645a1054064611071000c04c1d51040c507480202d030b60050000091007150380f11841d01030314801d02d2103078403086542c042d150052410603d00fa00801030094071803d082c03440400610120740c0c8030b5205074155005541c0c0110000b0700c1c0c1c0e03064034040c0101010000780c00400744140700c01c0340e01c064009112003d080c00b40800280c2c1c0007106c2d0f410760750700400225501c00d650700b0680e5550f1a03a0001802d950078007080c40815100000c140e8482c0e602640d4000d9094a0991 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 277580485 1250 277579235 277579277
    0x17011d061804030e040b101205150d120306030f11010f26090c120f010605040b0310020d0609230f01061704080408070609170c0109030b060d02031903 66
    0xc40c03040c100c41070000240400c1c0200c490a85401010300049000450f07240042c0a00400071205e4000c03644076050101103c03004d2103281da000f854880030a9003d8111000685524444040149500510700441003024882d4214030011a846401c44c1480c803c6440c01d4100986212807960018042904000c02e081c8245000514440b8150440100040500602c4103440d0018800300b02c82c030071548500010746540d01e564500c0c64404000d460b1140d10280034500b5640c071035104a00c40e50500158111507078001c6010020540622030050741c69640c26100303030103865140e100e078a81e0380c5000d030161030036004603100901661441e0910181d6035922840320030100c0b800c1c010f050001e440c0c103000c00d02d041608902d00360000d0040d28040e06296588001500e028199086640003510000d007c10681c0040380c581c20317640350407601421001c014180028812425840302402007010321000c0f83c4035403500aa18200181c0180070340b81c101d001222030824210a41008400150441c0c1d6071a1207002d0490f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 277581735 1250 277580485 277580509
    0x5010b040b0d060507021e0d1403010602030a08091207060209030c0a03080d0f11180310060b120a09020a0b03010f0b0309060c2a0601031709100f17011d06 68
    0x140b864040903416100c2c1c40c0100030040c00380056101e43d04c0c402840024004003080401c64510050120103000b4000402d001100da5070000700d254188010f2006030740200944200b00307003519000040ea99015890741c0b40c020100b0144100c810300050300018044541c0003041a80390540c11502d0034041340c010302840424510000c4d05041040c080140e1100c815048080003251012000c03944d8051400c80c211a54003ca0700c81140103815440300301c5500381444111241c89007000c0410500380b415900150501c1481496580c104000300081e05040117603018030340d02030f00a442c0d048556250030b800e6450380d0080c007501e502405a140c001419070300e50411288601e0105025110640301e0300040d0303500d9000300100b45111a440c0b03c80d400c060b40c024503002c00c0444d15500900300c6524600b00200d104102c05010600b40c02c040014203481e031907220b0703583c0815126150215040a850314200c42c00c0844a03400d02160000000028610140f80c03082840014044294030540d1100303000c000d2000100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 277582985 1250 277581735 277581739
    0xf1e020a0303050901020c13060905060312220914180102040b070215040305100204050405070c021c3201060603060518091501030b1503010605010e150408030f0705010b040b 76
    0x9000600000f44641c000d003100c1c44060045400c00e82c10800001c030702900701d1620b4018190364032400c012003452405407582250054000c1c025941e0300190301041741c810340c1e10181b10b03081c0800d40001e002180908040080010001c00c0100350491200f90000d0901682e9642e03840e1500403c030221900184201c3d01181e161002d80c528096595080c0616a214540404240c210521000000c2003052125000305458650010382d5a4280410802156005030494040018400300400140c651b00b0f40b9241c0c4170388040710001c6032045450420304200074900502c1403031030890082c500500308481d0500480710307810000d104c80c40c0c0f150740442c00c5445e01d02c205548440c1504080c600c00b540100d04079044145c56040d0390641e1614420351800352805e071b0048039101404d104104140c00c000e0020400944110002e0100c503240c100001c0040c04019000d6106150f142c1901710044080400c075401400420196034071240c00c940b5030f074425001840b007601c2c29404d000c4d481c58240307424810b0050003400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 277584235 1250 277582985 277582999
    0x2030a021210080304380c12030f01050103094202190f030204120309050103051605040b090a03020d030f02070b2a010b030610090b01030e1c02070b070f1e02 69
    0x1500780440ea185c1c0701c20711034940000000c000c0e5519006c04201980303050030090003031540c8408001c4224070b01000b030b51ba25122507506005100255058004140c119102480c002c142d0503451f040020341d040925501c0c80c00c80c1c1c1c2d071811464600d0359807800410300203040c1004800900c03928240780103a11035400d0340103031036003280c90070300c0194083d280329031202040346001400c0c00e4450b00e41c4900322407688025800318100150421040d80c1c1805413580c04204a0080f1082e220f42c5003020b45036005034010003900e0b5202007140700051f01c800203a4002190000d1000c10f02c0c00213030502230004c031700704240c6900500505d800400e0481c4204115108030500f04450060318809032440360781c424041501000da0354a920741c0880599040200d540500f100122031684180303440425002c07161000d018506150801019041c025404901c0383c91400001d2001d4001144244041f420108550040c4401d1800400c4803402c2c0320040c06d040d080c4c14421f810042003100c07140701c218120101000b0080d40204 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 277585485 1250 277584235 277584239
    0xc131d01061401032c120d02121f06080a0e100b0405070801060e0613090e0d0e01020a030c0f08040f0e040510060b270303070f060b0108060607060203040302070902030a021210080304 80
    0x1a000c100d40904000050f030b14074600e8000c46e00d101d80e2107074015007001a0086071700a2a50901001160041c4980d52101c03200c40260822010700049031140c20180310b050f000042c51038481e60440b4081c0240760044d82c1e901152898040010525800c07020f0250f07103820001142c46000d22141c50503580c0036100c2207034100c032103400c21100303500014450215132440c02002502c440c5078000e080c0c0f43d1088002400b180d902c02c9a00506d051901c0c1400790456001d200004081303070300141100c1c0920b03009425180b20100c0c40c146a1114071450f40010440007285000266030a07910407001d01841c0320b0003d44501114071741004d01030b10080d006606d21000c040000d20030b0721490300e5026100c000c001c01807030101000200081c2c1550400d035000c1e1170301200340080004010203445184110b0009003084074003403c0c1000804d440380a100001404107034000046000c0c1130003000908028003d440f41076542e49400a6034001940000341c40b19012423241010640c02011684840d040d20401c000440c1058 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 277586735 1250 277585485 277585541
    0xb130e060a0b09010318030c030f081612090203070b04030b01082109040e010c0c05071a0702060a0c170c1903021b04060308040609060809030703020c131d0106140103 73
    0x90b010f40710b03443c1499920302040b4240d44039503541c107900d1b5000382c69803000940d0740d06016205641c14007214007013003107c4d03003000b80a0084181c030402498591820f0030320300c65450600c070024108044065032502c6481800035110348e0010050054a01c204c40007441642c0e10315903203685400051918812049509100f6601d542000c050010020000c00c045115101c1114050846206102000024844808000610008100c101c00400b402010f204805a200c0d000305454081c0c0c02c1d00034402c0300d00140e1420310b1403007105000341c7c142e04000041281301600013001c140b030780511403450381401295020b007200200041224032079a05034000d4083e00ca40400c0043c0c004544040c91036003d0f41e03c100c0400031995150180c0b019204580f104454036042080c0909141c0004201c4241c591007001800f0020f940401c2e4000703001000c0c0c40704c24400c000511000d02070414041d04a64a0510101c03411038400305400410864940e480e25100001c0e00307900440c1a00c6480c04080c0c14041413050404010b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 277587985 1250 277586735 277586737
    0x102030a0305191a21060103022709030414013609110c16030f02040903050c03030a0603020a05010201230405030c0616030b121b12070b130e060a0b 65
    0x40300848103484040502581d4400c00c40c1c413140e115400108803400d07640002d00701110f005406103148820303403802460034400e40b9030340c14050000034007600d8a0104800011a8004d00c03001c0d0118090601b516443d0425005607250003a1003603040f204581494208154081d0b0700070480d0121440d407405100381440d411001e005003c0211080080c032051000419000c03601c41c002144640081c95560740c1202403006143c0741040c800e5040160b8a55001c01c000343d151101403010ba5810758003c60b554880b0b0030240c816001e006141c0321030b03000000401036400304c0d90b070ac0041660701c00c45d003c010454a58004a00b251400ba28440f604503141070040c00c4084c28991b2103038000c0c82041120725212009001750308000c0261000d403044080341c0001c080326500340c09101d0942c1342c1a0791542104a20b01216507070303403000c0b2680c8840e1011943e551103558071510080c0308090414030440304c0e802d42d241c0d000007465000c2d40240046030001c00340030800c400118491809124028011807606040c5078200040d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 277589235 1250 277587985 277587991
    0x140d0506060c010c0302070c050301060501050d0b0a0510320417030405041103010e07030b06220302091303120501030512030703090f0b040303180b07200102070b01050312090102030a0305 82
    0x311600502c40d0501030a0309005400d1031001c0c5070b42c00368441c089807902c071140045a80055110ba4148507007801143d9100040c1c4058401100b008515451440e010036a0845160000c541042c5200641d40409410841201a5254480da16406090200f55021004006d40303541c43c003100003000100b00104c0000440b42d1406c0319142900d04d400c1e0b8400000c1c0443c5e000d11003200d15004084010403110b62600700c80f0b54030101c24141480400d4640780003403900d106250050002220540c0910740c9811401c0e42a4040e50303003e80141c1c0341d800c00b009a8010680042d408400003195030030702c040b03150094002d01e412243d001000b40321705e0301c02aa6000301c0e42c10042810313080690342e8103440042020001c0030001c2c640540d182419501300b90034000c2c142c41c082c3c488460008840c130200030000d02d411078040c0c1d201681d480e05101450549034242c00e03900f45103030040d65030342c0089012403d000d10454501d04841e011001c440d02c006d42c40341d40c2041c5014500b01c1c0d6001d40c0040c042045194003d03000503074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 277590485 1250 277589235 277589239
    0x4030e0105070c2d080127050102091005031f030c0302040905030c0a0c0608010801050714030c16060f0c1806031e09030c060b1516080909070f02060601140d0506 71
    0xd1244c4480104400f010450160559094074000032400d80849000340005000f03004001e0125000303c420061141044080d40316050780501c10030800d008080d41505d800301c1004080c0c05074454071174401419600260340c030280c4011708010002644500207048400c4070352001100b01480d1858003044002c2556001c00c0e41d180c0420011400d640d01c0a0101f0034566208050703d0000b1400c1c03410051010340d0503000700882c0da1405040c030114a40001d008450031581280040d41c9070f07039180403807000f03010704481001040185050a402c012041d0000c0c0c10a0041440810400600c000304039a800041d0b01a410011102c0d003013800024880c0d005a02130300043c0b54410580010b030409103007102c2e8510341c140e00051810035000b040100c01e000b04407030381d8812519210240b425800c1d4104500c070f0049200241e460f0b200e00f14080051100031b44443e0040100441903501e000c81019100840300f03002d5038018050800051030540c005c400c40c2a03c0d4102811146c140400303c4010340092070050305007a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 277591735 1250 277590485 277590503
    0x71101120b010210240e0a050a0506060702040c090b070602030f061c08220e0403020d03020408190c05060712030e0318010e03071802091e030604080304030e0a0f150804030e010507 79
    0x8101e04954200d40280402c01e055005487c000d5001d07000c40318054441c000d880c2c2010f0a0081594504007a5400207030103c4001900c034180d1401964850400d03803000c4000000420958184015a4003444c45490b4001c00002544c3e55142000740f401c054820200603e400d940d00354011461610140c141c10211841340c0310f51030700b812644005505150f1006424004c1c000030002010360501200400c0031710303810158145030600f000c164585021107600c0101803040050303003007400030b582c440794010080034044a58500080c14022a12403000d005a400709081c030903800c035090400001c46025410b0f8009040848618000448105006440250b4181304000f800304804071803007403800890304c45a40050f0b44514200600c50081300010407802000740d649100383da9510007160310341d031003540806070981c3ca50719842c06a46a840c0c04a00726080704000401042032418080e1000c00e40e840300d0720140c00400c000b0021104001c04890043c0007915096880010303500400140403500c3c0f0544c892 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 277592985 1250 277591735 277591781
    0x1a0705070b070f0201030e010c020c060f0409020d0207140606130b010c1a1b0c150c07050d0504090522140c03010504120e0102060106020c06160503071101120b010210 73
    0x4104140c10000c802e541140301c3e01051802c642c2c051098801d4508030400a000035000c011019456221030410715000302c0d00080c4c1700301c004041c0402c48024000c603c90840d110500e4543c45e4009402400741183e0303414505c0407120001d080091010310501004041a07050ba0321240d010b0040d25803459542c0c1445103171000c0c00c00049101c03155001e61b111069000105140001c01c040f030100c01700e04a290144001c0000264104000c204c01040f40c0658060f401e003515001d10402040c407980c207002e440c0f8003849021241d0658060002c104540620b41c1c24010f9843e040c81512940240d5130705000c2000700d1845440000c1d4400c0c00d002c0c0c0090180701900d5030340c03403d40702090945804a0f0111a4070700c804c1103a80040341c100c0d401740040d040038802030046605140f0081c0d034a000300c1c510301344507406c0811402521608039503001c40103a4083c040d00c2e1282558681800d58285100503140841d559083d81790300c0301d040344034511300704c0c0c41680108a20700140300d000e8001e00b900501c585507460440d801c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 277594235 1250 277592985 277592999
    0x50a030b0d060506030c04020a05091c020607030309050c0109050105070f170c01020405091501080a05061c1101120c0c031211040b030403030f1b0e010207080706050403060f05011a070507 82
    0x7420704250103441e01203014a00401058180300f0008007092080744140107526610354841c2c1603a08060f002d0722041c0c0d02c91404040e10a50b11610ba000030760000c4009002d40070158140c100f00441d030300c2030701111b00410a10005503140d01c2d82d0f025003800158140400c001080c001600c41180d039000d444803841ca1a03040c24243e03001e9020b408840d086a4000400308501d0400900c0203500100303110042000400110009000400c00b4201c0368005854101081d038030f83d01d0040100c60031301500b09400847c43d45c0e19101d0075a00c000c0044d903000c030312568004c80444016000700d5920030322555540f5907000507681c042e11070803010882c410b40203641b1810303a14200448001840500070001d02e580c3c03246131600d402816107a030915806c0da04c07414000c40408035541600707041c0f0110040e052040820140d400100d103001040c6e40441d0740c034880c2c003100140b4150840000d10590b030243d6030620a0420211100d07040d10806e20401c04c0031071300b0040790703c25012440083c3c01028403070f030700b44e034800c1c0d96450b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 277595485 1250 277594235 277594249
    0xb0a051510030b011202041a030406111206011815030c0504050a0e01030b3303011b0306060e04020331060f052e030201080a09140a03020f030f0406050a030b 69
    0x1c800082995400048941d40c2c205c640b4071403000f040038042d49010f09000810b01003035100041011a100044080f50805c0113641100c209500010140342e02c61001113000c03282c0c2d8005665050108440000212040ca507405042055855517160000c1c00d45040304100c2c01400803501d0f003000c001007170002240c26501c1214140007801c0c284030a088550440c02c01e00700111025005503001c800341040f141c107005c400003c00000d00142c0e12502501810000800d02405003041414505c550048201d00034a415038014829079420b9581d11011100742c4040c00f08922050300c1000ea4444040a192102184003502d010303c0e00564003001c0e440141a919441510201d15104d49042d895004106003012050510709168040c41e1000a80100004066402001900019040100000000d0903101d6150010918035900001c1030301055250352900c1d032508900c01c0c08a0050140303039aa6903500b81e0002c15518040f51034200b2078941803402506a88540c08490884281610790042d000036030744101c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 277596735 1250 277595485 277595509
    0x8091c02070f23010903050c19050402030a09050606220c090308040602060f060f06180103020c0d03020712050406080c030403030f05090102030907060912020f181602070509040b0a0515 81
    0x4103845030040340c0d440340c2494030f6800d00a0b440c100070807580c00304041100096040e48860303080d9100c01103001c0341d49040030446c12503088190014000000c2c09081005039010a0405000310299081c9448200030002d542500c1d50170703521407410109246810004a51000701108001e00300303070300110342d00c2d581c1044a400c03a078000005038100c1401c0080260b40030229540c090f00458a81050103c5440001e00c240070300b043c040024150310004000c00e034040e504841c2d5001c2c49030201c0e0003060551000601941c019141140c10220b1209000302c2c0d68018825102076130781e241c440d40c209668071400100c03580c00c0104107030109501c4418040400c1c0280c8507841c098800c2ca0005a074901e01000034620b400311681c422000c0040303011041001203001000340c000c913036042310018103801c00d80c40003584201114070400d61400c490380c01d200c441e19059490340040344803502540c03180c40d1f642d003c00c1800e5500721400f5203410741d8440024102c45203a0b00540d4441c0008c008a082004444003059810040c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 277597985 1250 277596735 277596749
    0x302060d140c0a090b0a050f03060a0f0f081510031511120414070303090603020a020c090f0601110c0f0d050115140315160e0303041d040b0708091c02070f 68
    0x75881d248581c0000644050048145e1040c0f0f007404490000300b0b68403d0416103000d52001001041955507800e480c45c0040100000c00030090341c99040d0301c0f54034003503481082010702c2900c55500545140ba505079100d13049a00300d0442c064950740702d56594400c2e060f411131030903030380e00001038400018101403e010040340f003201200e441d0a00c0c064002203028142c54a4a90040c6410000030354003803015403e8030280d00c3c016072914440c0406a1624414040c5981e00c001e00307004000801382d58800880c45000c1c240e860f9400406580c9006842e00480c08007941c018414401d03181ca61b0510324512a030040c4100e00000d60000803220f10012411160040c04082d039010442c4120707454100240501800703c2e0160050604001e45549008050080720030103004d03103025003c3d101d039000d10070340f0010501c21403443e20709001e01c00044244c0748100c808a441e8007a540100d00f14038403801803107116205c00401014000d0000b03a00740088010f5070161411413080c80000309079840c1c1c8040d2200103000d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 277599235 1250 277597985 277597987
    0x70507031a0a0b030102070c1e030c030b10150503011a04080307030206010509160806100309080301080a120302070201020a020d0809180406050109090203033004050a03091a040302060d140c 83
    0xc00c51402c01602c141401441c82a8010f01100380443c00200202c0d04440500e80f50007030994550a501075062290392004e41550700e007aa0000c28090b0101219104402030440c6000302a12215a8030401900040c50360015000b4001407007c0c40840c0e03c0709211081000341d803403d080d620180030f407031540407800c1100181c1081c2c0c01081181005d070052a00407000150120b503105081030300602c141002064148100b034462908035840e4003a07030003800300a0304454602c0d52580c40703030140d950702c4401d01022254a030902d0303031400d0f11a01c68400d480055905901a04882101c0c5e000c00c0382a045207282038030042e804010030f284598851a5000035204a0341c000d86080c5094288002140c0f01603116100301d908040782000182da000c03007201c61100c9030001b4031920205010744890091002d480c500300c114800f5040c001070000c00200205007a1183d511000f0701601c8801c050390302e04041d000030f00d0341c4401f48014001803a20f0000740c000d0b1401000f0000b214100702000024242d415101c88401d284 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 277600485 1250 277599235 277599241
    0x1d010905010b0a211104090b01060e090f0f091203100609080102040602030306060d0603050d05030916060807140c0303010b041e0b0d0c0c0f05010f0e0a0c0b070507031a 74
    0x8402e0145925481084554004413442c1c014150451380082802d15040020b0130b01050401070350042140e07440c80050420000d80085113031000442c4001e00886011401001e4844014502510981c0c17080c002951402d400382c442e035a4180c46008003501055490084100d481e140707610003005584075044840600200c5c0d46007000140842c80650400b4900d41d00400003130084580000031640c02042c26650155100c0a000708400144502e4100410034018400904000c603070000146020f9840344065a55400400180c103030500d80c5442000f021130401000107401c40e01482c0e0041d0821300112a1503c1d101111030701c01d0035a07100760814220690042407c0c404031500c020000042183c20120781c0316142400b0300c49401e4007c042810368816100c0c00b14011540c480c1c400940a242d105005200c1c008540c5840c501038141b101e22a0b2807145019030340305008000081d4a01c600b604138401c00041418180c407040d6560080b0800da580d07124980d00080000e090940003031089405100d010903c4c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 277601735 1250 277600485 277600493
    0x5070302091318030806011b030509011d0a0b212508090c09041a0a0c0f021b060304080f041d01121e211d060a0c03030b01031d0109 58
    0x1c80d00100c507801500e0200f11039607844100c0788064160743c05081c103401c20303502c042c0100c4049015071503031909010200008404c154100b0080d0032040400d80781c006804c000d002c030203621b01840d194201c0e440242c02c0010041d20070120002e210072902d000f01420085a0180585c00c030520a0700e03060f17488030207460360000f041d42c25030240790400b815151521490070010300741c9a450890007005442040349101280401c250b00070ba20b00c91556500e848034440c0b5001c001480207101c000e10700000b08030787c030070348c100900c0c07021480304840085004400107161103101848551b400080040f1407440c01040481544880385002c0c000404007031b509108000389860b041180020180d0003044041880003100c400500c210000101000c0500310410710403a840c142241c1003440682a049407690000d60b25201560214031225501e1000441d40b01c044851400d200070b0f031281d0400040014540103010000a1094101980c0201c05260110b180303040801040c1070b9080501d0220f1041e036454020700104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 277602985 1250 277601735 277601749
    0x402040e010f080703030504181b120e0f120708090901030f05010e150705071b0b04031403070206121e130303050a05040305190302040f1d1609120212010507030209 72
    0x5045140060800c56107503036000340ca5800345002e40381d20b88081e00305080c01c28500c0e0344100c41c1010b801c4ae00c0803007001c0001010f89414880e0920900140c100040c40340e8603407000a80034110f6600600420001100a066032000c4d0082c1c00c00b1900c00404110b201c1d515610104068040e5000b1000c0c40d034001b40900d009800c440c40010b240002c1c1d001a07000c0c03105260750150300c607406081802c14039a5004c6c5440c0007440280b1019a0300002c15001c1804038141184001031300503a486016005105001400780c1070303890003a2103000307500500403c529920901c2c4200450b8000507505682d80c030000000b0103c0300d555900301c440400343c0c00140282d1040c10b916005140c0c0020f03001c0410840c03418142c90090051184112003245a01c1d13a4170b40e0f50803244640e040710020300d18040c0031030f111034480003021100b14000318400192400307100800c20701d040643c48034805440ca0744607600d8151400c2c0c0000d0180480308003c0c0c1c1d0011034208090690301e000e00840784504669900142e0b0340030224208092 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 277604235 1250 277602985 277602989
    0xe040507091e05100806011101110406030b040216020402130306050405060f06041a12120c07080c03070b031609080a111c020306041103030c1e0d0c05030a030b01020c0402040e010f 79
    0x846020720010401c581300c100c004a11056030f440c2104103a90b407800107881031940c140441003e50b103401011146100705101820540c7d2040d9030500c504e102030401c0000f64011502c3e5901c1a02c46045e034440103240c154010a0188011101e80501d15540d442d10021104200c030b0941d000e401580c204282e0380f03c0034450a610140882c1d0800c0f003044c0d44855929000401e1211600900500d088030200b160b0030002d00d0303149090741101ca641c503a070401030075488003541d210302000b910034201188010304d40429014141e0b5400b000ca00d0540d620a00944110b2800b0781646080c800c0002002c50003480900101006900070001050201c9040b03052060601c0140100013621203c00801001a41c02282144e041500650541845605040001d09500c00c8640c10902c3d4401e42c01c3d4210a0203c160a040c00c0f510b00c00c05450720304101c3d25090707030b0707011022000402c6504100500214180030b40e01290356806e061040fa8006801c56011408a911036040350b007649152600407c040d0403c4046440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 277605485 1250 277604235 277604279
    0xc07090501050d1208180a030c0c0e092a2706040506180a14040302070311010c03050403030f030b0604090608070b070c151e08160c0b1302010e04050709 67
    0x900040f545450403070803410400c070001c0110410200d0551400001c034003550401080588828800303601e40546500361004d400c480001104900049880002d04d00610030101344024004111410320003058402e08009000040c00300282c50000341d840360390401581d0002d0712402040945810f642d010f00850042c00c05104504203000c02a00362544030500c200c0001d1a1004503035a110700c041032001c0c294448500d580f01c201c1c0401c000508d030740003800e8001c607070241c0c443c80c5003074100c24011512002c0980014010800401081000902c155840b0100c01e80380d10300000c44c1c59403d000144550f1103036000010154444105110032641400450020080041034515000040d1b5441c0038281d581e126261340583c4801c0b0b1aa68035018070440404401e0031081c010840c01d0b0600042d010300825144811010452a82c02e1422344c01054581c002c243c0180400025546030610b250701c40c450200d04038100326541c401c100060300d903800b420340a42c4081e100c1c451240c0c20304080d07940f00c40d01001030003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 277606735 1250 277605485 277605499
    0x2040f0b1c0c0b030703050718080604020d060b09190b040911090712050c03041101021f02030703020409290108150402030c1225050723010e030c0709050105 69
    0x280095803100350304246400e0803070304103078030250038200b00e525150030b43d10149288a0000c01c1100042d07040e030149210f080d85440e4001d800e520207142e1003501e649401405041d9011602041c05880c1500102440f18402e035804546401c44c8000320307484850990710102404500208400c6400071070244103a0790b481a507042080103181d485400065500d00d400c0b40c018820300c8003140400748100c540c090308034501203060109080186240b07006900860b000d1340e41103074202c540340d099840425035420390b001c050707002d02c00c0820350710300d99009510180011050650030000041e4074480d80c000c4000c4150342c0041c85c041c1241001000000e90765840200b810403200f0740030410354540c3d0182e00c001d4034605880041e20ba0791201021a00d91242045040b4600c13066400c2000ea804041c0b205000c4000086401241b4540b1200544e8180501c03040100a0448401451074100d006c02c444400c02c03500000103c1c0303c4460064990071540b28180c1005641c001807000d102200c22070081c14010801036682c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 277607985 1250 277606735 277606751
    0x1e061403100c0e0607080325120c021603050303010f0806010f1502031e03070e060c0c041e06060f0206100b071b0f0b09030c0406030b06060a02030c010f050402040f 72
    0x3988803801d0414100c0301654902910207950b2007048000310038040034025982d980003908080703003a908102d8050101d80d000301c5920651001681e0f418000c200039450311301d504404100460050700038458075408500c21a41484078840d1400003041c000e501a5014607a03139410b1a290502c41c1409401960aa51124004029070344000510030111781c400390002001000f61007040707045110341c031704502e144030f00742c5003039100c5841031130095006491507195042000c022405001ea2801000706402c0250080b0000708024101a0800703451506448040c6046803440600e0000700c2d500f5400c03000000388155500c2005603010000d958100b0a0ba48902c82201e1070804080344c24030034030301d00601120100015040c4040c0a014810141c00d6441c040e4080544440c20302e01d4941001d0320b0507100e482242921240c50034036200301d03010b894104804003059a5410203100840d0710214100046110400c10902c4640d02803182040c001181100400d190600d13004010944e030304c014117000c40a01e800300f5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 277609235 1250 277607985 277607989
    0x705030703030c05010e0106170f0d0e0f03070302040c05031b070506040305090613080c0315091507020319020105010e0f0708010905060f0d06150b07030f0309020f03011e0614 77
    0x3103442181e80c907141400c1c64100c18a8918054544081700e44240e608110010501c0710144030f407000a0a03906048440d03101582c2c228960301c40791803101601085410031042860700300305c2000314000700c010701140e201e10b80d203034007040c00c44030004010300018a000c000c2c0f00303806000031405000022005c468500b004129141c040d00c030400030b040241800f01c00200440b05844110640b0b00400b4035480e40d4490030340d12a055919120300c1c0d0325540c07007070141000100c0d89036103a8028501801d807603070040c41048085141c000c0a500003070080000d502c000d10000601c11201c3c3c403030386a804c01e03070303400811103514001181c040744402074140b0010756094000c200060780c2c41801641107454003072001c0ba840d100c002c0801c1021902861450304a100d03041d14000b03008031608500118031000c3e4103c40103964484540030710b03004070038008000401001c0c4184885100350402100d083c002800011650034000020b42128091984001c817040c5079101c24659241e17602c00d2500806080c0240640c000007000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 277610485 1250 277609235 277609243
    0xe041113051c110d03210f15080c040203100e09010c170408121b180909010605030601140a09050702011b050a09050111150907090c0e060904020c010e0712060b03070503 74
    0x196550191204110350b1003858828a0061400254002050f41da46d140905940c090701502520b03a0a07981081000300c4000045014501100c807010081d2154030080010080039501c040c240030920810342c500030032605c2c10081e80d0b40c0211054000000d0180d140b0320042e0642005000c0403a180405d03408000124601310202e9100703082002d2000c005665041e00560700d00724400165840740d001007007080e501480d4031441001c401381200e03220707029500e14519a00340d422074010b681e0160000300040041032840068101e0700140100078201054a83e6000d0048132012588640180e4440806201955016455400c005c0d0f651524a10f40103901270080c2503240d040c8125410440c0d9035805d45c6944c02d05200030004038000d1a00c1018500f0120080340d95000c1c203008411b50f1500d0402403150050045060103c0c002000d0300b407508200c8000100f0009411450100750203540381d000710050440705224050160000d4550410140e10500340035049a0340310b803541e0701942c4a003000b84a1035074001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 277611735 1250 277610485 277610513
    0x403021009080316030908060702120f0c0a06381c05030a0905030f010e1005060303160b0a1a0d06022104030207030210050909070e041113051c 63
    0x189801080c209812030840721080190311840c0c00c0d0002246011000c4a042407240300180250754401b005a00c8598886c0c039007406585d40c0c001f50703008040401010881001a100c2c0302a1079080310700307103d8482c241c00d041401003003084684540c3c82d01002c0c09500b42c0c0c40c0c004400580000001850344180c034818241510100d141da119400e104409010181d20b006240c0f800703031740902502c0e00c400c03410340064541050b030700801d4480d0003035501c03401c00d420b8144109042032080000400306020105001401440c0103407a43d40c150008000b100e450b141c20005820000340f141d4050402450031030303080402c40c0e0b001300055010030701c800500b0102e0b0b80c07418201200190003183c010307a52801e1007074188294501e005800c01c19400d22040005250300403c041d82100c1c0203850007001d8045100044842d44a410303000e561050441000c2014a1300c0f81c1e081d4581110301a000082e16501c50700c1c8410280c0007a8034903407841c0319188040c1301c04d0070031200302d50104c15800004424246035603a003c403068101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 277612985 1250 277611735 277611739
    0x325110a0201050f041a07060c0503040c03030f050706021b0c030c0a030b0601110a030306050102010f020c0d18080316050706090803161b081606020d210f050705190302030c040302 79
    0x41507260080540130112170091090001c50080310b03c0d946540d2007650021201a40d000d441c040300c1c1d00000c0d0003003080340e00c070b01c0e0700c501c0b804141d90850307406561a00d410300b00d5070100300048c00301500003059880103105001203049048602c1b07a545810300d140010124040d03010750072611f1845c640d80c0701c0300d511609881e401070141e0070660700c1d00b0040b20348444034911134055100d1a100d8500b41a059030088080d68001c0c1c0c001e000703142201c80c0c80d82c21ba00c50a510860035900c058403445945200341400c084482e01070781500310700f980c1e800e0131030702e50307003000358032524503d4074030229000c10100300511001400302c1d042000441d07140442b2035403680141040e40c007003d2081206d801c1000444458040400c1e1001507020701c65480f03510b900e95811000310310050200085801081e003a00010300c40d902c0b00a16610003010b000d01188100c00c030503103043d000254688641e02c05a140079540113440c86401c480e50340c0c5071a24070301580e84d0b959503940182c4209040c4104103003c540810a0202c400346c80d01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 277614235 1250 277612985 277612987
    0x3032109032a070e06090109020a030e0607030b190b031f030f0c0611010b06031503010b1c0c140105040b1b16080c09060907081b0325110a020105 64
    0x58048520308622414a042d603a005444911a000030304200c0c8042c4107110440484038141c2c0c803141ca040e588541030b07402540c0250b1030001000b0110302d076001858400140d140201d85904803400c1d0500c0e0440a0b2840004291501ca0203001801e0071004115030702545907000b0801c3d85000010440c1d40300141012184030040014400034020445114000310f23800300642c1c0c03021034203003465070406000340140c0b80015450059454554014002e00b014030400610052841d1204a0010140001c0d0000c2039055500c41e0242c00840d912403940400c0c2d080c6003089581c1d020114070f4032143d40c800c0340e00680036081d11000e1801c0566401420303075007030754140b903403040d50340485000034450f42d020b01c0f000c1d01151099014a04103071204540500c111000c9904807950341202001700528007404960b840e0700111200d0005950900c607212443d00300f00d15a1401c00c0304600c1c1c000c1d040a940c42103429106a10941d0100030050b41d100e92004c040c000c0d14034042d0100c10a288040340ca03480c0400000e410404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 277615485 1250 277614235 277614241
    0x4020a050904031b030306060e0301020a02070501030506040f0f05070e0a0303082a130302042708180307060804260a0c0c05030d09030605070206040305040b03040f020924030321 78
    0x405883c4e0003c003200181034204902c0b4072450018040d04940c00b0311b00008200340c0118000c1e042c140240d8586540340e0f00070b4030381d082c1020011402420020f1405902540711210903400740c101e403040c40560011520003103114a4410000b1702540c03848096140103140c0c030780f01003010981c0441180e03000000703204200200840ca00f01815012480c3c44010400000062440204407000f52014200e034402d4505005101010502d14000c40c031122500307100c4040c0500503030020716020000e050615014038002202c12589010038a07000c055080300c00071910300003d02c405e004c0710101070391456003403841d00402c0116a000d50603140c0100d510250a0000321a0303e00c040080200a901c090400502140c510441100c0000d04401031031000780e07442c61500d4040f5850b0b40c40401d400d0710030b07501616100c0c5442d150000ca41e4007540000c00541d50340300e00c0700d504c0005a0b039880d81280039110042c501011515403403000783d04c05d4440c140c898072a500400c40031503010f5200c03030741088104040040e0003040d0303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 277616735 1250 277615485 277615487
    0x809070e0411060c0c0f0109080d0315080a1a0606072d050d050403200609011110020a030608010b0a080c010c060e030f0705070603110403140124150804020a05090403 73
    0x24001d8000e442d0f200704042040500e0340c50000b140300109a045505038007104003c3e00540b0022041c2c061880c55070010440e80382214000d400405c00400403c0702c4070700e010b44d6001d04504050034800c04a407042201c042c0404400d14044400380c00200c102c400344c0c540130305903450042428002d680c0054a208044003072202c81c60146030f604540d030700203003030303640301c20b5009002000341d48036020880d10903114070701290341488611601081d500300030b40000d207003c402c00c0042d0303a45980180048403c0c81084850001a40c0c580080c20b0b42400d0754030086000b074186105a402d44481d000f940c4e025541c1d581040000000c0001c0400e400c00c02821300c200c124510707003020310141070200700c50422441300240b07101d000c1d01c403540105441c0d0701445c00d86000c0b5803503100841c152000103818002c0c85009100c03d10209000844058a001940740001685541e0b040700c441541456440088030f241600000c000300c59920440c1c484000251500444902e0964006100501180105030103280e110b40014105 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 277617985 1250 277616735 277616753
    0xc02040f0606021c020f0706050f07080a0f1205070206011719050c040b091003031404080d0e01080a150e04140f03030a0b0f013c030b040b010809070e04 67
    0x100840300014014a034840381c020b95145102211060070000348200d801103c1d101050300c0c0210b88101e009407044038601401200da84d0004d4000b071040103400c00030080090301900007411004d40917224081c509005070740c05085040310642250800342400100b198466000c210740d4150703506881c4403000d054861040901c1c124080c0d4852412454140610040c1f260000f00152060001c88d018001140100e0a1151443d803d0790201a0b61807900d4041c00001d000d94403c00c61071925840780c60800360380c1e840c421f1805c400f0440410202d0140404036405580c002307800d50b40000c40e040e040c0241000c200c41051821301c0c0b0710070500390b681d814003c90100071b43c06414840003601c0d4012200c115001303226481e141d0740141c40700726030280fa09a00a9071800d0a031400c2d014000140c4401c203006c0b800388144440303050002e40c401c5850381c003410885110911200340008a0210740da0000304445a0010b0204031203103541e916040c4a01e0000300014080c001a003807080c3d50b184c00c18810a604c8510740781c1c0103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 277619235 1250 277617985 277618001
    0x8010b0a1b11100903060e0c09130302030706050112020405011403030414030102192a0312050402040e07080a1b03080f0703050f072409050303130305040f030809191202010c0204 78
    0x801034a0003a5503c0440d070052152050702c0c000d2408100701c02440384119500e58001041540103c04031001841241800389982c1409000f401601e14200b155512101120702c00d81100b00a219012007013410742c2028820326002d88603008a04510030230390000250741c1e019a104540000210300189002a1170070f4040c0e852024001c03d804003002120a4050704101a0341d02d0765038427403081c113a10715000403184004d11406400d0b40303480380c0844505850b0000b1f007200610a82e0415254580362080100800c9406c00411021024107000b00c20303441e200e19403501c0c603680b252001190050a2000c00d8501c000c0b100840d081580541e075810161800707480f2401403c0020004400104624050000b6903027600c03083c52801c1001407210800681e0141100e2100401a105600610005240c1c0c540c0d001c00d043c0c814040d061003824103070b035074040e0070840c0d4440e001194401c60201d202c2203d801d06108140c0382c0014049000e84840c1043d007920039a6203500006410040d9212111055490b55400920 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 277620485 1250 277619235 277619239
    0xc0f0f060d0213031401020702012c0a0b0c0d08010305060a020a11030705070501092106150305010f02040f17031207031b020f070f030b0112110d1208010b0a1b11 71
    0x5103d00100c103840c0c1c2ca424052205a8840129003219000c0b5841031088850f010350585411101c09008040e0b580340303141c2044207490040b92000340e20015540d09000b00028080709044a81c0e64a00c004841d06010b041e02380d203828400742c000103000250300070075090307400117a1070390040c1ca0300c450001c110b5030041c070301c0c081c1c1426000000e650307401c0c4140480c0c41001d5940c00c0e03c1d8644c1c069a520100c0c2200c1003060b10450a46800084c58000102d03075400c512a50780d040601d90103a40c0d04d03038480c0c60841e40607002205031241e00040812100e800c0100e4030004100d2001c00303842010b103403131100b500d03031251080d640c1201d0400c0740083c0b2494042d5100c440c03071885113400e0950421a501c40a50b0360441c5040c480d1440c8120310000499542100748a8192540008014000c0e460311803c480c10f59443c0c1811160083d41440d000c525444101c40c501e116030181a81c91601c1c00840000341107030b80180c01401d4500010005080d2464004810252001d00400413005000340c609050b0003600c50541c00c50b07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 277621735 1250 277620485 277620487
    0x611090901080c10050c0d140904060b0301090c140d020d1104031202070f050a03110f150403060b0d110108060d200307170606010c0c03050102030c0712020c0f0f060d02 74
    0x428814030020300c07034035103c9090f113914043e00d403504820340d0036000d1072007401480e6019112002c2d02620400c59008003e999900c2079007007000d44000101520a660007520040340c020004001c150f126028000b105480303410700b8040340551910014192066040e4851003a400042080561445502c000d6140225221031a1100d4880c42c2c9031003048e591b0400c250062007140c0004c220415101c40f0352082322001440110107518550750301e928400c0001c2415800159803440c15403c0d25000600d1164105100704240e4450451414904590288400e00d00584e00c803c0701400045a62210701059002420400f149940e088001032898270300d03480c001e1000c1c2000307031604c404203040184902d51444c118140c03407640d44c03503e200440011400c1d42241d0240c0c815004507181e940240c1c03440041600800400060686030b44a103401d9030b105440282c1010390004480b41404611054120880b28a10140180d10b6500700081e450014101442e482081807803800d840d2540c2d860102d555040060b8429 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 277622985 1250 277621735 277621739
    0x130c051011060f0609011502010605060703090303080c09180a0e0109080310080a0c170708190c0b0c100209010203090a030b07020f03040b0d0f1e0c18120611090901 72
    0x200071420544420703400703100c1c07003000c0741509000c00041c9124620103850503080d61301e4680185401e6152160310300c255582c3d210701040c2c0391905001049814000d0725000421469413034000d28141d001018200300042c244010a0f10303940e00c04000300d0260400303040c40c8a6440b45018040100084195603410f0343c603011014003085131401c00345100d4624440302006a070350381e1001c00d4841e415000020000d84c40c1400a1100b561002c100303803450504001140d5600d500c8946052400450511300142500c0e030080310070420400846440103044540500703410008a151841da444c4030517071031403c2442d00800c0d0141c4a92003001070780d222503001009144407943c5c03130400351100c4100303490070001805030a00307051b0348a100004580c125601c00540510f04400041c80da030003041e0000200740c4482d00c90410310014a074410740454041c1460500140a40c4032a90182c6402d24855040000e62074000d01003044460131900d80a903190850760209240c2c2401030f00070598420701d00003540c494508000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 277624235 1250 277622985 277622987
    0xa0b0a0305091c02060a020304110603010902030411060918073605010c02130c02030f0f03180106050d020d0807020301021209011103010f060c0510020f0a09170303130c0510 76
    0x108034042e00304502078520440d0410b401c1400304000e204000c003d0791040000c10546c00c0719600460303005004842d48549a0f44c440c0c0011840e0b402a0320001107c2d801000340018812601480c0340340c0384044a01030318100180002c030b082c0c0201c01c0d421140100403c40050344590150700c0786c0c40080ae00303410f81ca5804000d0261400100c0143d010305964415030030000c6401c0d401003004401d25a0010582820000a1b0b044030000c0c08440b4201011400280902a1089070043c0500425541411455103918100d00203204a11070480c000075940e060a0081111f40c0b03581c0c0581c403c0540603110340ca800510780c20086028440c0040c02501907100040b02c9142081840015000d402280001d1104484070013458485000030300076010025403202082014500903805504180d02c5032041e94021000d00007003004a80105117020520f560010f5441d209950040341070010704400e10700804044800e00340d00d903590200604850910750085904020b120881c4c07007210040c80f00501c181c80c00307070400b14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 277625485 1250 277624235 277624241
    0x61003030c06270b0c070308010e0403020307150e010b01090e2a21070903080a080a0f0501061d0a03050d140c03030103050703060609020319231e0717040206090a0b0a03 74
    0x3c0139248150598080b50801c03074024121001d1035015a14070400386d0900e01504400c030f80180046081d03100400040340001d01401125101030680600011400e414a00e001c0c02d45810405550402038482400c1c014001c0c0c601c075464100c03110b442d0310844514220001c00103022507203140b00761600c0106903181a101d14000b411185941340c18000515294118142e40c0380c2414080100086414010282840e00c91a07910b40e210260042c0440e03a85500a042c40444000f80c100c0bc000a407410403d510402c0390004507000001c054420382051859500c0d55508e51021003000000c0107924600240116428800da84200600300c00740d0740c4d0795039179140c81c580c0c0304800d100460b00340e0300f02540011203950520a4074441c23000040042c1c904009461000003d1405070000182c8103210020203216106907032500b40f04440000c1904000d800e4008c07500340030300c0000d02580030000d11726401070750306002d03403403041d0402e6041e205e0507140c2c0807800003d2038410050300990303180782c3d005c03802c084010343c950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 277626735 1250 277625485 277625561
    0x20c06070e03010621050c1909050a1409010f0c05160f0302070314010e0c06122e09020d0b0415140a0e0702010b010e0a050d0201050c0109020d03050a030e061003030c06 74
    0x5800c47e050700c0d1089090240300101c03c40c000308206090f00c020000c2e10810781110754800700031079002910314034800110340d803140b042d17070f0300c412aa560720141c1189603918442d5801100c1d481c10818280741840c10034500c0d0b22402c5030001c1c400c40c2c040c4816003c25008010300b202440d4441049011104c58102480c020300b2040070581081c0700702c100c0d81d1142e00303201044846072403006404a1407030ba83c55410510400c0004a040103c203540248050120030341045000580b581101c0580d03129150354080303080c2c40d11a0451485985060445004e45030343c00c44000c01c0301c2c04540c0100346000000300141c1882d01c01c0e40424209501e681c2001a61a410760100744e441f6826207940030300c00510800c0c041e0350103090003125001002c000103031000d58011006000315180340030000c0390203141c0c1d07404101c134000c400340220007182e00814411105c0d4ac00d4000ca4040080010007887c0794a008004410055581d12010342440f5000c900714040c0019508041d950f204905a84085019445940c0f0f0b641410340c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 277627985 1250 277626735 277626743
    0x30705040c11160b18010c020301110904050f0f040f210f020d14030a1a0d0305030601120b0d080a120603110a1e140d0606060302031009020c06070e03010621 69
    0x3c5220102c00f030590015260545050500140c28040a08940040204006011411b11010b1218180103039424010682000110030b2040e8888807440c0a0109546000e4850b030002200b40b004c019000c100c4508003640181c01041d0385068614500300000c81d5000341010307140c600704980c110345849402c2100342100c51016030803250784080c008070448000031500300c861180c110801c08a040b131411900403141390009011000c05103000b00c2d001500c4001e540c0012804207901000304030907581c0013100440c0b1507003a1602400f0f01c01503040042c0b90200c002c0c0d0020000100800c8802c100c038450006450000c2c0c400d081040001d0305c900f800c00520a070f1202252203524030301c1d80032896444208803210b5444e4030440c04c0c81c12701d0521020101d190a0311044a030069409030401c004138000307000e41c1e0020505510010780c1c0c1d05081111a50f01441c507004061200d00410084071045000240d1586c081c4441c507040030320100c540006409828a9071051440581c489130421403828040910503400b442 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 277629235 1250 277627985 277627993
    0xb0c030103151a0f010905040204090b040507020d080a18061409160305060c1e120103060b0d081206130606030b030609010b13020307020309090403020f0d090f050f030705040c11 78
    0x1803048100540700c40f81200c0ca4a040d4402480b0740c82d081c241101c0b000554141403c2ca0103136110404241241c005038800b030b0103c0e848403240700141c1040c3c81440c1d04400181701415243c03091402c007801125000e01345000d44d40c0ea41e640d2004007a1442038070110b0580c000024003260040e10b030442d8403d0020784407180c640c00781e0104010035110706000407007140e40c001c02515a03a41c466400041580182007000c0c0e01000380c0740e480b1b84081e104401003100e0f540c074401c440081d50444c1003c1d811a030300c5454040c0a01820b20f402400308482000380d07010130003021981407140d940c010114130000f4400c041c0c0c040450502c1c4001c00e03003a8040d040300f1103881d001d6044802603034800b80d90901766085d100100d5041f03c40ca1403581c00000144c0c000b145e0010a0740112443c0c8005540032540c1600121419030058110410b405888142482081000000c174a800d400c0b0505010b1a480c414140b0310469100c3c0c0800582c140b0f042d1010321492008000040c0308000c14041d4400141180c2041204204640a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 277630485 1250 277629235 277629263
    0xf021c0203011422291509060a020a02150a11060705270901030c05031b0102120d060503070902120c03040f060518120a03110c0c06070f0b0c030103 65
    0x2040c82540d0403101203010f90001140d94909101d0710b030509220b90040c00690140004556415000c3c5c81e081004040c00e41c6445030041d280c14040402030060a0704c2083d45e669505440a03850341610282d107001c03140e80d9550210680c0982c03070450300d0703003000f5007040c010507441048507480d03005096880342d607840c0d0a2030f0009000c01c8503120700d02160203001241c001c3c8207110a01c84004004802d11f1411242c1600304050f84000400c0301109a01c1192800351501040c8101d0800740314242e070410011400118050701080042c1d191030b54107159400089000c0390700c02d44603050382c018400501e405000c4c0e445058680c00b26030302a500141040e0070070100980411036503552541200e2040b5001b41d400c7c0001440740d038400c0c9c040d1102a14000e0300100b00c0003103e021110602100e030f000b121100505a8036856144050181c800d080b424810103042806008003580001c10502103d0508540c00e5546145e945405220344130424000390140c40c8000170044500c0342e0000641c1640c2c012690b50003088 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 277631735 1250 277630485 277630537
    0x10021b0111060a02030c0f07050601090c020d1d0103090602041e05090f010302150f0d050405010606020109020619110601080d0e040c1e03021c0510060804030207030809060702040f02 80
    0x28581e495144100d0707004600058141c0c00316800756822105541e80e05281090301c114801c12034200d101c041c0c41c140c00c17500040101e40a030f8441e864504000e400500b13140120340d80042c007141c2c3c0c1182c000d045100e480b000e00700380e87c0c861750121070110741c000750464842c0e07200c00c40d0110b56450a0349024004c11920000b0034503203051600f5a01ca0040041003904580c01c6a0900003081e404552542200c3d00a2003d03803c810404006440e040e192280005240e250a0601d02c0c29190701d43d200c0025645421241d001503282d68003200c1001c40d20004509548460740c404507003180c2003030901c08640c06100004182d030100803400a6403007002da83c1d00d540d100700400c1000120744a84800c43d020401c0c28014a04890340000c015901e0900e80c2801404c9c200f003244c0c00041d850150b40a51042e0781d486040110711f0303000446440c0a4012440c02036014509580e01a40da44400c1c00080c084200101d10071500d42d5440302254641e0780d01a2082c04258894011000030f900090107000d40340d0b4040351030400030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 277632985 1250 277631735 277631747
    0x90708071511010908030a0504030905060f040620010e031201090c200a050601060903020310020c0d0c0c050607030809060610091e0905090f07080d0806120c10021b01 73
    0x41d5081c690150880700480c40709a841028400204a965490304900c3c0c01007a00344000c0c42c450010244007092a103407074607000346400e550350000c91040c0d809001840e00c0001400039034007070315241e00300313003d101f140300c103800d41410100310b000c10b60b66082164a581d070400101c09414058030590340401316036210595032080d54610352601d0002000844a0812010000c00f2107080101c0d0300182c0d030100e01b054075801e0800200340c00200209100180c01c20440c2400c004001c00c080c002d107001c50510f62076010300394032a0700c0c91000c1410440c02c00100802e02c8010390f0148020000244466038400071454090b02402c0704840c607100360302a0178000b0f1001e0401111005001015075a60000c050030f0203a00d802c0d40c000c2d54507040400d0342081d800716460100d485954041d0103a0310041c0f201d40c4207030007100d14280c1c0a42007030340c403600401c1c1c0403019150000300b0550440f02c02c640001e01e202610408074505242d000340603500c030100080300060a034001c200c40e10b111440180300000701032207000540b02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 277634235 1250 277632985 277632989
    0xa14010605010806010c152a1b0f08043b04050d05030a0e01050405301e0f070309031e05070306020d060b07061a0f0f01030b01020f03040602010509070807 68
    0x104035000005807442d071003000204461b0340720706e0100301f00c4810444040120340d60b07404004500750b0700e812107030140210400009003001162821801840c07038894200300400d00030500034600c402c4400c2d01d000b000704039002e440260801d8681400004c400340d11004000c0c2c04410140c5030424442034003100e200e85094007902c20303a00800242201070b103616046920360b000801101d8101c0d602d0000d03056268081c003496000364040d000510140954240c2c00c8541030041840081000100300802401466032040d03d60100704170780e250b1281e1952820155141c401c502c1010356000700011a00205030b0041181400e403030144018100006812031030340c2e0301111640c000303406035100c24010400100f171070700100415040400f01103002640d500c0e54116a401034201250102d1721500c60100000a010402d4070780700d021039a506080851601140e55007900760b454604154481d0303c80c0403640d000300b02c0d14513000040e50072240d886645a5009000b8601600d60003010b000d0b0380702c0080c0078480040c5000c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 277635485 1250 277634235 277634237
    0x304081c0801170303060d0c27053301030b0405071205012903040c0503060405030c06060604030f020f150309010f0f0b0303040e07110618011506081501031401080a1401060501 77
    0x855030300c442c0d0070403040400c03500d0100d40c1c01d042c400c4c010440c0024005c401404400004082d0100c0c03000c3c4280e9000c1d0780b801412f80d071100080c1c0750340c0c1d4065072a4445040c602003018180340c0040074907200403805426041076494100381050f062021950748498844409c1d141c200341003000d641c070b13450b2880a1460361603549a40603003108111820780d01c11001150828445c0c52000340140d500c00c0030a013420000c80b010f0b00d140d0000704041c0c91a085c28401c3da0391008040380d500d89407505650f60802d41c0580181e01038090200041a00b040743c035010f52024540700741d0020710b43c5a1410101041c00b03845044090f448041c20302044c114024400e029081c420040140994105420303c22a20000f03d0000c2c40301041020003180c1088028062121030700842c520103d21420402e0079030603a0039680701d080300e401c8101c046281000350640c800b8103960001440c81a03503080710080740c0120040c051400105081e9051200000380e4000005140c603865032150402018101221010380d003281c0c003d1013440c3c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 277636735 1250 277635485 277635487
    0x501080309060c03040515030f150a152c030f070b091009030f0b0f06060a0c08090f03100605030d08011208030604090f03021501090221090304081c08011703 69
    0x4041c80d01c00b0140c00d460141a086a0400780c0e118002000c080f141f4215407000c800010a021612020307801c4294802060450f40345070780d04050101e00c645202c0d10480307100030b9242400b680c0d8140701e03904240c10101d0704804038052a121111004905820a0b0341b00e11a108a500800440001007820402c8800000905003083c104000344403040a034203a144c0204407601c1c802100044507074035000941d44c040c807074169881c0b51900340d646655074060b2001e4401c0805100d4200d50782d80c406000c19106511035291a103450305a00030591022042901301c1d458041c80041600070941d6911030011544110120342000c149a030064031440c400b8000c0280d40105204800701040c07025001b19044039018000044186580d201c82d600440c011500720016044140796408080d0300c950298050700c2e5104e0111b2034039151518483c00c0005103040c0441c020910b50004864400500903030b001400d6407400d866402d50700d504118000da401e44403041c04506043d0000c208054030780f0440c0d0588000c44019 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 277637985 1250 277636735 277636747
    0x10819020d030306081203010315020301120f05010b0604080a06060e070207210b040b070f112505031c0306080106051507020d0210021e0109020102060c070303022a1005010803 77
    0x44100ca9560070016800c0c59101c0600040c1d1560030024001c1e103030810075181c1d4a0f541145444000c2e81703103890222020310300500050040c122403140d940a0715030b011500a0705105686081405007680008666000602081c0001e5641000c80c030020154810001003003c03d4444403641c0414030151a8000140e00c600800d01c220a500c031140d20503412050290100040b043d600e4002a401c200d40031a0321445030410f0022039504180c0c5400c01902c00d04000a030010a41d41305980e0381c4044480c0f41ca07407101e0101c401c86641c8140e0050300030305070140641d041c84031045201e4002103405100c0b04002454100300140066042c490760065840042064000401c000e1404a80303070041d41059902001d5403450708010780e114803210034400780c4c60b0090580c0d0b011103000d51081d52400d2030400e200d80d040403407681c0140e9002c1505944596a41c01640d101c5450f420110700a0064500313469100e0000c0380140c0400000c0c2c14103000c107042c0d01c4c0460b01c1d061403405843d005e4450a1040c600540d1080c004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 277639235 1250 277637985 277637989
    0xf0703050a03230708071203050c0d020f0903030a0e18040206030420030703120909020313032f010902270613020904020708040920040603050a020d0e06090601081902 73
    0x225400103c814140308082801c0c3c0035845500240c422079002c200011084100701600300100010b060606080116240c480f48141c082d100b500d00d091440c550000314030003014810340603a210800c024045a0b01c80b007840700c000d000c24101c240390500c26081c040f0792444801c5a014003c0c4910f5000d004581552595a1458035440c607250041c03032440070301848900942c40c01c0040f180118040d00100c0400c242424001d4582242904030038842401003041120400d5207603190440240e0604d09180c240e000d800c8074009801e48840481030090b010a0513072030202c015004000441d00888180010710140c080c04a041c0000d4602e540c5041485000a2441d10b0145c0e420f0400401c00d2001526086245000030103d9106010440706901c012906100700021807140580c0c9040d0941421544040322503d0085e500a51152104260300d030000100c0300305050b0103645c000c8011800c1403001b0064940c000340c80d402c00700c4103c200751189130000030728410000707003800d44845000c2d8619925812502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 277640485 1250 277639235 277639247
    0x30b10051f120b0904030804060c020102072a05120102130b0a080601030507020c040f1d19111c03111002041203050702030708071503110906040b0d0603061d0f0703050a03 75
    0x2c8458160b544804000f8503481d0100c0081c40f591095446510030311307040c5016000c44200442c0c0b501168814021600001d6100c42e02c002e5003400c0b01d10304d0120200c010042c40e80a4078a400040d0001c4445244060245e0b05401400500a0b8680d485003155140c801503002d030700407060b0b08000a15032102042095000742d00058020340c0a01c1a25000003080011400703072604104802d104a54a11000c1c03c20050b203422544c10b810300c2c0740030b01710000c11103110083e213081d0075074050003413519121420071650f914043d85146c2000c482c0d40c2e003160041c40c2000742411049181c041c86c0c0340241c0d4214000e06a15100700c40070340d0003139074941c50307403031800d0701c1c22261034100c844100d07050f00c036a00e0080307090340e02000000000c000b02c1c4800c0e282c141c10a40c006041da010705044000200013030240110360703940d010544d0141c40b0070440003a19200ca00c14030300080c5c802644090032043c0307440c0922200c890b03060429420600f40d501282d88003036003500ca00d80d03103212134440940710350403040d001c00000b4403640c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 277641735 1250 277640485 277640507
    0xc0e0405010f02030709211a070302070203010f02040311010c02032a060309160b03090607080a0f0c02030301140f090a05040c030c06020a0605090d2307050601030b10051f 75
    0xc000080310410900315108980c01510110003003101d80e0010801e14000074030201e40941a49041d55010a8a55814480c04800d00071a1040440b00c3c0000308454030070b0381694811034006009002c510510030000c0001d500900040c1e500a0a0301d4200d000b40d40200400c01400d5400f030010900f0b040601800480720158051807410001e10b4903078020700b50b4400002d0360003103820101428441403156001c921040807544a5040b504041c800c2046000000c0742d813607400511420a87c415540307200400000700203800400c0e40c1d0908d40610070401c60703030010145060f42c40d1084081c01b410b0614003040480c00640240c0c0e680038040b1000542d200586400094006214400d420040c80e265500e40d14400082c0d040280181e00c46852003050000601039140c006002c1c80c06010020280200100b0503102196911003c1c2d00100d00c17104190602403c035107030030f900002500d0705541c491034031102050055039400011501070700302051614200900c0310449030004486c80c0910069001512010200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 277642985 1250 277641735 277641743
    0xa1d030307020402040b130510020c0118090212060a090e0c040f1803081e060d02010c03140c0304150e0109060e03100e0303370f0b06040b07140303040c0e04 69
    0x107204a00041c1c960340043c1c80504406e0200035120300700e0003442a003182c61648034610865021100c0f205480c0c000c0b44280302c103d0286000c80d101a5010080b8041003800d52180c0312080c400108081620410480503000d1001200d5003c8103540d1303004034000381c800e446108620350b00940381200051905031301c0a02400701411010400e21003400d032070000448007100903400306e41160204842c0c45006201e0703411403001429120400d04240d00402c0b0803c08441c4002d0500008075400000d00d400780e8070f0342c00a28020700303005688045000d0095207940162007000700f05450b003201003618a000e0300f0003407941c8030306030344a42c4043e140c00002c84030198440040f075010f0244991f0319600202d02d005003902c4080d8800110754a082102e00d120348540f4a03103c3d041c00c28940e05240d00c00d4503243c41c0f00320f1002c3c24000003042a00c029000c0c2001401c84544240d480480010001145601400034003182400ba01c10521503104d41782c4080e0302ca100466001b0309900c40a08180080000b03881c2c2d4580041c02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 277644235 1250 277642985 277642987
    0x1b0a08030408071a0f07060506370b042411010906050402090f012102031006060e01090905010f030f1e030305011502030705280c1215020a1d0303 64
    0x14810005003554003940001e00b050300004070902c0f404204800740e10000403030034505440e114022000d9a0309008004000702150b80320004a00159030759494050f04e0b034103c003107a584403c1c1c1d26146410b400d4070340d0044081d010510100080c0c0300720744410b640444200c00e40441680d904400188403e407502c101040a0100f0b24100c224040024810089030341d02c181320000e40c60520b4010440041c000425240001641c030780180180c1c1e021210f16142c4d069a8480e0300c1ca5031034580300003410400742208401c0d020780351480010740c5581c0f03c008800558401c3e00c03504035454a030b500c0c1000762942402003003281d1000d02c0d130410001d4400011041e5081c082c1c1880c010401c1ea581e10b0003588074400d20305a002a40f02c000500c40c010101c0d041e000300c030100d40011403402c560b0391342d12a21001036034040c117609616259004103401a69040d4900964005a80d01d1103d0311204210341412103400256040044055861650401807085986080580c0c4400422600180ba550a0001075011160705408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 277645485 1250 277644235 277644239
    0x312070209061c0b01061d0f01080a090506090606040b0105180d0c030b090a060f0b0f040e12030901020a1205130f15151d010302180601030b0619020f07081b0a 70
    0x3c074034081940051151418645951510f00c004008116100c01030404056201c5289600e658045003103e0800003820b1185150351119000750040564100140260080c00e081000108e13001c40c2d0756103c3d000498007007100ca00c824004507100e0058941401239488244600c4040f40b524a4007030035550701c038468051456450380d80d0306850300b00c103803003480c050341c0301004007420400c1b10300a9078440c0c0b0000004000c60145203000490010044003024003032035843d40280d98490090004aa4000107011900d66a04000d020079001354050350441e00050b0b140302c0d54850348036040c0682c600a5a90f0b400c0b80c0480c150640b6020b81080201904a0724941030f20a6429501b1040c042c48001f845444442030f40140f406990709140344500060148040c0064014401641d4442d281c09482e495054101d180b42c0e20f03a00140c00509070a4240d607801040860060f5401c000d0003980310050707c040d4203803030b00c0b050f80c03894081c4d0380c519500421025401c1003c0542c0e041c090440c005070785d80300041044a0b216 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 277646735 1250 277645485 277645519
    0x9041b09022d0c120f13030302210a0f050d090f08121006050304030e0a1a1b010b0a06210609020702131118150f0309190f020f040b04110a030605031207020906 70
    0x85a247c0c421009a00810b41c140480307a007031403024804c44c0c00042c85030724010841000404035990041420203019001c12201c02081040c2e01c090b60190b440b00000c80e40268600b401c42107500a46022100501c04000007600b070a4544880012115182c03212425a100da039401d40305102c081c1d0102e40c01101152000035a012204007600b1f905032201e80d201e90f04d90011000c502c040010310315002c8941e040c00c01440d06903e6040601045900c0b5140520440d030000c04480810303440d1850110006040100210701e15081d0b40c01805524421600040d02c4e44010707100209940c040c0c010200c0c1c507102406860b80c40c00c803c2c000000400f4000b4805481c01042d0701076105283c0250000d107070361801c08030402c060f403241008440407901c844001c0c0c2c1a18041540c603075550003c441402400307182e140821442c1e64840c1d400582c1480002401403081c01c2c0070021125071a041404034800090070032400003407070304010410078222050801c0c11481e0130199000d209480da4094480e03a000740410100752859 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 277647985 1250 277646735 277646767
    0x7050f09220602180613030b060a03081207030605010804110f0a0902030c030f01171911030f0c03010b01050a090e06010e100c0b0f010509041b09022d0c120f 69
    0x240b4410b0900607115214080e10650740480d11059a0041c601007007081c4c0801c0c00c03641c203141202c0d440360007200700340e444402141034107100f40d000803c02c40001c910080841204030070240308113020798003040f426030344400442e0000c1040c7d40191005801900940d02400c001120400d1020702a1100341800c3d075616056089034411602e500601402106000d90345c0400c03640700b030041400d40c014002485918500980f60842000c5041e03148a1900d2040208008030340e12520042004003521001d1a010030499110b90818202501c81c0d40780100c15082980140107030b468111499807013503c05418402c14035490398015000c11b0620041a40729152640c6031102c5000500703ca5580c510010014a416400002c1c05051580040c6000d00141f00e10385407854016405900304070415a903288004511401c1e0342e880d000009101d000180144441c04d04540e030803803c0d80c01e9409241d1141d25440030955501440107041c100743c114200e0728001ca100000506004a52210701c1442c20204490032014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 277649235 1250 277647985 277648051
    0xa1812060f06080a050303160c020a17100606021905151008060112080f03040309030b0a060e010911091207050406091e09080910090b071a0907050f09 66
    0x403511880241441c01c05401110020300703c6400038040310700e2036a251030b1a404004c19071152109000c0c8806001c520645071a030341150050b001e0100746866813582d09002003260301c03000061003400e8281044600f0352250404440c0d85601510003816008004000c812140c2e130299814480e1412040b940d803080355500f40505041880140400d241c002500d003010b8050740b207142c40031510441540400c0d0f14004541000b030b002d00c22195650398074a0b045c0c41000742c9800141039801564100b20b401183c4c1d83c458000d40742c1103030007104603030303a51b001000588000001a0113001d209121042886c240000c1400c101d0300c0c1841680c0354a034454000c6011a0306941c0100310164031000301c403481f0034080c042c84030300c404400c01c1030280350055251809540f180c0b200c901e001d0008100c04d001450702c10035510340070b40380c580080369030b610440c11720340d1030a0080c0240e81005045400810300c101e01c006210300071a4406440b1180004c4003004015241400903c00802c0b01c08100c0c0703410b1218482e40300914 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 277650485 1250 277649235 277649243
    0x90507061808010c0807030203091006030b06040f06030c050603040519060b040c0215220f050106170703030807080a11130e07090e010e070203070f0c05090703110a1812 74
    0x1503030001ca400840350488640c041c1c0c1050b490075040505041c0c0c40380c105544044241005a43c0f031703c803420f485141203d000340b941d070658035100b800b004101c00700c12910b000721011101407120580b104c4010080f00c0ba80e01c030007804500009010011030800300c001e59800b0340940151020442c104210002102c0d0000085907215510f50403d403680c6840d20403441c4081c1c59100500e504020507409007102178020742841518140c0c03000d121a6109a030f20f08030681c5900c01c2ca01e44a0640d42d16206001c3c02c1d090140100b9070840050403096040001000c1045035090350310010341d40c42c0c40c42c00342c030104000f81c0750700c69840d00c3d20074140309102c0c039a00426000803119040c8540b0751030b2440b5000c84403c0540180204280f86034200f04051382072038518191007181d82c0d511040d03255010164918070402000074a28a200e03500d0380113000e6015001d0049071000c3c0c4224449550b000000c8007202c03030650b881d4004031024001e00400714400c4d030f045090042c86410700c0030075985072070a1125203175000ba0216 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 277651735 1250 277650485 277650497
    0x17070312090509070305060616060f020a090302090108030a02030711010309080424030c020a06020d0204030b18101b0e12031b070510020a120509040c05030105010324060e0409050706 80
    0x8003d00f001c1c1d0907107600100381e10b0100301300c0c03c1c000b00140c0c00f403140b0001c121403840e041d03248100780007496000040d00101070700f085654484c0500060300942051106a11035035483e40002050035010044843c08070f0260f01840c41e000041da18012010a0380c082c00b4101680d03059080b00240c481d0001300080c014030080804540740794410300b80101015483c00003010304003007240b000541c00094215140347c0c810400350b00e81da0655803041c0240070705d50005d443c1043c001305000307610f141d030801071054040d9001643c2080a551490307609541003612ba0700d50807548000682c0351280b140119114041e0000c0280c5c0b6940e0801050341d16541044482004a40135039840a100740804c100880081c0800d0366200003892403100040d4440036074000c003070f2900588210f1421058807600444609600c020010044890303861401049134109024480c0842d16280c0403410410703914108170361002090743c101200504044048441101060a0540041e2a250300030b001440c2441000b0140c4079030381d40c134 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 277652985 1250 277651735 277651739
    0x1c0203031b0615010e060a02151f090501030b04120309020d05030316141e0417330a0209040b03010603050d0f170604020f0d0e0601060e120303011707031209 69
    0x81da0612401811656101e594081001ca690343c0090703005c64035413011a81079403a1149203005a0814600c2c1d0481000e103400c141c10400b50b03030410041054140f8004205246103611100c14074222002800003401d00d9545200050006030f04546040321000741c5e10303020840d81130b83d45c0800d0903540002000c88003504007004006210510040003081c1c50040e00d828902c10500c0c0c400c5136602d10031504080c02607401840115010800c4100702c034010119101c0c0281d41c24407110100d900c442c0c10f91420308041c141003203488100800240b03421210f40e00c407c070751003054407143d040380d0007540f04c40111a00a622940141c1d120390f404e10032403000758000c1018202865810100400d58400d68107404284400a0a0030b911000300d0030007654012019500142e4480c4054503140d054094003441d12441ca003041c0b000e600ea01d10100f5498100c0b08151112043e0b5614072080040c801c0c54940084c4103580280010015030a80c0c5029045c40d00000f02a540c00070740340d03102c0e1092001102c140c1004100d1003001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 277654235 1250 277652985 277653037
    0x3010f05090f15060906030a02100c0c090603031d2206030b0603010903050d05040507030204021803061501120f2712020606010c0206030709231302090604051c020303 73
    0x140414260980003808101e0f003005440c442541d0080c0080340a024a840024115203041011303103e00760300200400201c07200c41c84000c00032500080c040301c0a03008000d0002d8011414022003040e01e9040d02c1c2d9428846400c50341007126100001081d50000d07030802c10a081c1d50b00c204407020318018000000c07444a0075400d01c0150300b4005001c1a019070301d00000310007c40c1d84401501c4884003c02c8010450707407901e09040b0314114a540000c1d5002d440000c90745035404501c0694181441d040e4203450990b500d20f40041d1004001c0c54105001c01c0031f4446c14151030046500c4805c101205040001740b07602c000000540c4800c0d950f81c000e50103084c8103604014024940292050034100d072006101d58640000001c014420301d0200034061200440450307801e6010301040d0020341915010400341125000c01c2c1144404401180c40c0500c80d42c000d608907203540b60084441c4280d000d01b0b6180303058500303000d014070a0400c4003102c4425045c545e40d00d00503038050000b03000a5000322441e4080c4095158 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 277655485 1250 277654235 277654243
    0x170301060906020c0d02091602010e1b190305060109020a05070804060509090f010506040b0c030909070f0e04050c04050d020307180606031a031002030a0b04110309060903040807210203010f0509 85
    0x5013540c4501c0f2114500c00040c0e40f00b12840e9448008a03407044c400c014401d000b07034050000c81c0c45100d00c5000b1403c242c0c400c80b41601e85041c00407803c0300d44038038203443c20741102c0f1916214040544503230060001408154a503030020069a0f0789481e10500e802d0864481c0d65941d0881c1e00501c0005800103104080e038034107101701035001a650082c2d42c03055490300b070001b0f4441c8194031a8221852012414030507030b113002d0007940c201040140081d2054500408000c0013400a100301c08049140b0001c2c5000d5410213101d41e61050200d403081034903140c03c200401050300440f01c5d04076410f00c07400e04041008500b4002050010440600108845041c1807000c3c0076552032280c12901111440e00c0c64285a07000154000705003032074000160b40340c666040d0540982a1081c1890708903060103079040304610804000d5102c1d445150a598090301c0711081740740c580c45103201c2d011455014031010310044032a4110355400e4004019001c0e030b59840d50f4046425100203800030024181e81c2d40c200005101c3c180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 277656735 1250 277655485 277655503
    0x120506010806010e150f04060e0a05011a0c28020303070b0603100903050304020f06090301020a09080c090106020d111005090c01030b04021608030a06120f030909060f03030c17030106090602 83
    0x2c620006505e4800441c5000c02010810b079403140e1469130030004603032110fa01c00d1002d000901d040341890b107002d41c0c800010384030a21500c2c40708643c00012525000003141503901440d036020140910b01058907500c2040310b2a0119140c004440302c5508005940400040055a104070642c110f9031415504040c00e00344940b83c0c1c0729445040400740c1d03000a074000102c0e030303201394121030300c9400b803180c8000b08850b8040c525619425600c00a140038425400074000c808480e404d40c02c840948104c030040c000e90071428441e5901580c041040301d000e103030003000c546406c81d400ca411605180d1314501d1082c02d8400c25034040000d5086071107441010751b03248c0103203405200700740d409600d00031444e9004400344d5070080c0054030b10000800413503220600d5810200080201d0010801c540045040240307401c0700c81c3e0811004108050400a040801c6008420403205208c8110b58101c1c610344056412107805813040700d0f04403081c3e8080c18802c000d01c0182d8041c010300e03901c2d099024105000a49015420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 277657985 1250 277656735 277656749
    0x50d0503070c060f0905030a030603171201030308041b06030b030d1d01030c0c060c05030618010f06080408090a060801180e0714010512071e0c0b180712050601080601 73
    0x400400845580141c2c408082c20782c0003400042484c00680c0003002041c143c00000c100c1e002c00102c1e90000342d4180c004101392406002030803229042c40301d00c2c9442c0c0c841e858110081c0860b5078010400300380500e03a2940e115014000d2800003012012141c0210100c642103800840d660304071694044c10100a034503400c902e079080c032a9100d4004011004000e4800c441d031030401d500c418803030303070001e01c2511001400d9038813540074030100f12030060140090b00100e5005001304000380c10001c00e05800803015040b940c0c03040f40100514100007084480701d90061065031021020000d004550326400da9441c01421142d27a5414254102100d61b103a0280d061060502e1905201c5648101a8040340c0f020071075285003251003210081c0c100607a00790050104414440e03105000308280c10303400c2020341c1e44e9988804150b92642c0c1400a09483b00c00000e10050104e41c09400000c04401c400e50070020356003001002c60717207141e5440d003044c001012030b084100e03115007101c80100444401000000e014000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 277659235 1250 277657985 277657987
    0xf010b0306010e1c0b010b0d0b010c0b04060b0d0f0b010303020f0304050913021203280f0203030714091c121b1203060906090903140913020c0309100c050d05 69
    0x40700e00000c1c40b0b030b141105035610511450b0b42c8442018440014054015403091041d0340d0b030740e900c0d45e1300e6416400c180194025542840c00b544ea05620604107241e8503136001004450744c2c0c40715256031004280d41109a50800c4051031200f01080e80f51500c80d01c194030034a4544510b42c198900203040582d006003000055100b4042400346681e2000c40542c40050340b05010f1500c2054000544034030380800b20403805000000d4584080802101c1841883c80d03040360030320001d103000004a80543c0d03030140c4440140c00900c081043d1070b11500c01420640a000030285c14814003c00141188503d1080311980c2c28000704d010f010820000f401030920065400c00480c8007078000c200d0010542c00d00c1e0006c00035422841c0112130103000b64440005056032500c20804c0585a4400d440108051340007500858450102554091110f404417032220002038201301c880303807200490501a411141c45a20580418028200d454450341001300c4210515900d440e4510746905007607081034900d400c48010400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 277660485 1250 277659235 277659241
    0x18071a1804110d05130b04140d080106140901020a050d030204090e07050d021201060e0c09190810150305010504060504021e090c07030215010308041d040f0b040f060e060f010b03 78
    0xca2400c3e10511030a40e80003140c82c1c2d40b269035900703502941c440c00a010303801940901040c00740b44458107540d081040c00b25130b0981c04200059854950901c0b6500008018140800310181c42c0c0000c0c2003a0601030045404283c90303941d84600305201e07900b032400002d40c00f090400c03884c015800780140804107080940100350502d004650480d42c240e1020f4000c4a03211500b68072001d00354080c42c000c1401141508107804c06000c1009181d0001c0101486580c0d80000901c01d0003021440100301c0302e8540041010080d4441410082c1000001040c13001c1c49a90000000c98028000d10b40b00e01c1c440c4030001403a18051040055031a500403000d181e82180c0f810038511515440b03002074001c842c101e0060f440d00340501d0304a140102d04003c114001c91381034000001c0241300b901030020b42e03110100e103055401e590100e04031602c0b0220340107050100068511008581c40340e62858109000e03010864200c04241c039a442520030b00380340040c80d540310b6000c100c808000a4402d5001d4040075900701d2840c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 277661735 1250 277660485 277660511
    0x60e0609040519051303030c0e090106081b04090507090f120201030207060612060905010605010c050705091807060c030201230a0b03100e0606030106050102031218071a1804 76
    0x405119503260189035100041064003880c00031034903281805500c01d1040e86420810f1119600c40e414080f00801c0c140544400c2c50790041d40120603154010784400a56031819804503500b9001503e0006a4840d07a403114000e84a180020405402d0050010840382040c402c000c1c034102c0300b41d02650340c50005c004144982c0c1075000c004190283c0910303015854050703c2c2081c000420141c0e01607c0305030b00107102042048034540081051500500c000c0050301d81c1d902c010340b402041c800d4000c02c160812031080c00f080c6000c24031560802c0e0000a040d0700c448848000a1400c00b00e40c00c80d10108a021110104260342401680b6445142c0000500710004010040c04a41c0780540000129500c0e0341c1c1c51040d54904000c4440c211034641d03400c0c0302c80c04d500d082407501c440080e1036403400b03542481030108081d400001107480c07840041021140307950303456401351039600054100c01118081d4160008003112014180b0301c81020318a94965141020541e10601354011440c0501550401d40c00c25484 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 277662985 1250 277661735 277661737
    0x3021c03170c120103050c150307052205030d08250801060c0201030b1909060b030c1207140d020a120e0714030106050d0b0615130614131509060e06 65
    0x240041c05100300890b01c0d194030302c9046000f201201c0c0c0d00e0502c0b002c000402c0c0540061858a000420340d2804400707030040c0d134441072034401140c800e80403c200b0001002c03480703136626480100310b101e00c003002106522000080e00303141c0e4480803400060480c2c82405241c038040758040c040514400341d106007140d001e007000f6000400501c40d140a100650f8041015039000b07800008000c01c00804004250303030000386180085540c0d0081010311860f0000204102801c5011280071300d50b010501410405140000c80101e0001406003007041003c01c800d003884100740c0b014102c1c90082c10400b68480710012001400103214020000080d41080b00981d080c040115a0500396200344500103070012406001c00d001d010b09a111541001d542206002840b9410a856004508c2100c00c030440d143c3c1310140345120301640d602d4021610340c0e846c04001550268000300040074030f0000c1c507401d1484410032903001d259107920034551601a4050495143c1d4020845400350030f007801c0850040001d40c01195107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 277664235 1250 277662985 277663007
    0x10b03161401142208151014060c0102040803070210030510180608061e011a0f070f0b040f0b0615030103060b0406080709020405030115030b0f0711011503021c03 71
    0x502038840a10f1589001500c2103ca1513000c124080654040c200003a0751110740700d10400e40716001c2d200c0c60094184d4070001e01402100900f410590f943e0078a0101040705508503040c940c401810801801828000c1c0054002885500c0103581ca42c0c41600521040f80a40c50190342010314100800c20000d807200d07400800d4458085404001d1440c1c086500b0003410a034000101600c203240c108100002031412264040704082c0500c02181d82c0c0710107801c1d0480c40279800e910415814002c000c6032031108006044054081c0942e5106240b49450f0a00038203070584090ba0f01481c030380200c10a124481100301c1c0c00c4181901e586407011044240704410f4041804014011030b00ea07650059240d41d1038004030050302c0003c003030f42c1d101790b600c2d81c04d08020345c05485424025400e00d403c140d1807002420041044a8100e03014296640c0e07510768040302124024004418480002c07813200000320240701d014a6042c1000740301006034110300401882c6c0c4201c441c070b428804100665403000136406207a07415 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 277665485 1250 277664235 277664237
    0x4030804111c08092e050f0f0a030218120a0620030f01060e09070c110a030606080a1103030f1209100504032d050a050d0b0909010b03161401 62
    0x1c03015081500007049001010081080da665001c8402d0500040b10000c3c13000301d0044a007074202d0380585603840611041640f450001d10300e1203102e1101d20b0700a100616410a24001e0180781c5104440e0303046040c1c209040b6540002d034041034692100e0703c4001c04410882c002c46010f104650000f0420b03541e864508070041c4180d89503104000400005541c606011a04510440e164501140000010f01d8244030f44d40c005030281c803801e89075080000071240034500503900c0392140d404a44514101c8614007021075004440010b0010125540d07116050151403258080c01500145007405400d280301a440244290401c000800300c100011045034405041401c24072200d540303201003682455440400f00e241d0f07d0400c02000b04055200200707920b9130011b8060200040481c0c504e01141d10400038013400814410020540c0e20f500501c050075080030480000301e00b0303451240224425140c2515650103980d10390022011500d014007440e00d0200840c0c00c50711015180110310058a089080114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 277666735 1250 277665485 277665503
    0xf042907050c031204050309030d0e030c010f050c01060b0a1713120504170703030f3603150e0606240d1d07050f01033b07060e0f0904030804 62
    0x60b4580406106a03a10240f500000800900c1c043c1046034580c1d002c00c5c001d5200b406000a140038231400356040326440e0340e0207001010048003000064442c04c201c49140d0082c45010f00c4424017083c801d0103000041c20a850400d51507400410003d001040e11200c0640c3c014440020090410051640d210555170006040003644417610009e413079910441d0000305441c12250a00095884006503100890303120380c3e10a0340781040d02c0d40841d4001382e01c1200717003480c54140c4400c589502d46608050140080150341c0b402070783c0e0342d545000112003003d2801590315100c18103280c018405000c0650720080542d2001a200f000070740140c4071580d1640103035001440400c025582600907030100d02c1190419a0820314442d40728101540c404680c4541c5204024075983d40002c0e52003401040e080c020848114128a0710001e01c00c602c403440d20b6084801500000f6420303d40003c00c001076030042c011a2210003801603a41c1c24402404001040707940603580080074000000c0c3e011030115070054000000d2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 277667985 1250 277666735 277666747
    0x90e07061e050915090d0308100f05030309040c11030a080f1003050319050403330b01120b131d0609030405090402010f0c050105011503050a090f0b100902030f04290705 74
    0x804480c000c550382180c0241481c56458100340c0c0103002d16006401c800902038609daa15000e50001e00014000c20790180c10900c0b1015450900341c0240d9602541400e0104030080e000d221680b541e005240b8010000720f03246c013403092004800c5000b50700304201e000e01c40f0301141107440341a500d124648881110480400c3c108c45803c0c4200c0940d4091079001500411550944100a003895201581409282503414207407162074040d208000382c01d034040c0c6038242c2030b4807007907022002172004c2c00d44c080c3c2246090302411503c00c420b104403451b10b05091210405004d06454141c64210020091401d0754400c000501c155900c6422160f4826030901c2c0071a4290785140381220b040c41e1003400242151300300f8001081c40c12364801560400303c0c0e5540c04000035540d04265100341d0b40320360740207001d02120782c1d5500040b64526180b194811041012040c245a075446020304a9100700c0d461400011003000348002c201042001c240211804c114540305a00b048403060f080340000b0b810341341404400604 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 277669235 1250 277667985 277668019
    0x30f03050f0a0306050111060f010b0f04030203120c070f03081c0b13050703240e0702030705060a050105090c0a0f050c0a02120c040b0a030312050c04090e07061e0509 73
    0x122005007100c200010b0b150800c0c01006400350205005080c0884c031144a4410408000208030380300d031010512416030b5919040241045501034120f41c00301d84810000400075807020004140302d24a40071003143d07600918810309060070b5898000c0c61198000300310410226030100150382805008178520007a05c0846c440041c000c00300a28119040f9420b800c1c21105940668003142c4120480c1d00e01307206c04898072401d0385042003558462108150040780c180408600d068925074844100d00449103015050344400d0300d8584122040e0381c1494448005120303e040801d0341580000d428600281000042e0b0380151000c040014104104000804c5181040c2820020781c48001c0d001b510341484a81504040350325070103011000303801282041c0e0322207098180300c2d041400700c0e070309941d1707002c0301e4110b5003400b602411015009040501c0d0070301c801b1a00500318440c60034605e0107035006050343c6d03240c920f02500f0f01855461090052124046180316140c011080b507417080001c81d80d0b41a82e581c8102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 277670485 1250 277669235 277669237
    0x12130e0c0919120507090f110d0c1701150e040c1707020313032109050d061a040507030e06070809070e04020406151805090103110103050406090209091f0510030f0305 73
    0x406a00c00d003943d41e00c4401405000b081c0740c0c2c2a01c40e4150240400c2d5500200c04045e5409070300c281c51240350802440400042c15070025070038a85a2800000101d624a0a83c040d80340030307009109558001c00c540401180c004541a01c0c219050318140008030302c18501601200c0f50301c5110980000050002c1e41c01442071044403003901c0c0a00480380516201d040c5182e1500d440018102c1d00740d44440f003006080d005141e440203d5100400011009a0b03a550b4400036010036409408280302d075207000035076a078840c024107100c2e0b04a941c1c000f40320503040904a140034400380c105014000590300340000800042002000d03200904035142203500c072840418003c0c0020703070282155205102c00c1201c9190b1220b202c240040c1d140c8901d0f4045601e49042103000c02c02880010722181d41249420900d5010382c2019901c2070040340700090b0f214098011501c41c510880e000d607003c7e00720a502003410f40c00150481341608444400704085d1508001032251080785000c06490418004241d804040c8520 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 277671735 1250 277670485 277670489
    0x60703110d0207060311031b0f04150807030b1801170307081909060f08010e06130504031214160503180d020304090509030901090312090812130e0c0919 67
    0x20046504480814400030f450f908680600c00c0001e0a081c64044529646000e584c02040c0c0d100c0648080e0180728800307131895000d810007004401040c0800205500206042441e140141e02c030500c540c5000000101200c14040140b071250341004103c49680454048403415913009040d1b002855815041303541c554010b00030020100c0314000307207120343c0c40e01010002d41d0160080d142c001c001601c2d41410f550403176040503410b0000300d0a00041003110b480900564010b003010300f003414122072079584a42558012101540440c44001c0e103e400d410692003266003111000c03441c42c000303090105010768450240b46d28401044000300200d24801282411401c882c8580c20446140000d400b07070182d117a030820b10030f88401c540b50500140d9482008001c4840c4210b05940700100607003142e554080100740580305104011071a1804900340d0000c010348118107041202c2d1607140c11051824500200890700450096840c020501142107110b200b03488185100301c0ba408007540c0d6148810b01c8480041e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 277672985 1250 277671735 277671767
    0xc0703080d02040311091905060604051f2c060d0e0d1205060409050c090903040b0a020a140a0c030803061314072705040218100203040801060503010c080105060703 72
    0x14080e0100720507600500860780f00300c000034000c44120003000840803040f00c01999080d4030100d50240070502c0c2c8d21640e40124020a20741c24651100081101182c1e0400b00c045400c1d24000d01c00d1042c0e0b00042e107002d908000204806059120100c2c0003ca1080c0c602d44501075840810b0382d400c0101c0c1500101c0c000309110088502d20703015424014030500000384020099440e01c80031032050f003414041c1c441b070301d60803500030003000703558809015410300020001c0041d404248004110400301c0c01c01001e116021b58010303d0019541e091100d2100c0070b0544641301540080c090340009540c0700c46400840c0d803c07008003600ca82e18100401c182000900a980745c40c0d10b003c005040480c0050035a5000f084140e032094200d60003d802034600349080200440e26460740e8204200f81d280903001041c01508401c41111481210804501c080b001c89888101581002c81c06202c12002481204018a070840c02805070311600200a0f03e0a00113016503030141c04001100402d05000328564160381d41c103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 277674235 1250 277672985 277672987
    0xa0803120a1802150702040f1b020c0301060f05010c1109040807031d010219020a0302040e0307140d0804060b041518060501140910091802030a0c021609020c070308 72
    0x41040030521488121604000d1500c0d29203003150542d2050048000d46501070520fa85210201002c010150400d01049910a4072440807410360440c501a10865508003074044846444514010381041e8818600b00e0003a80b41000030003003068911180000c48200b0b08007500c0364481824041400c005520341c5682001142040c001080102001002c50f503000785c0d6030103c9590a5213215842041d4a0405030040c4d015003030b21070078a1048203d44556a20003809500c1c0c00341d80c4c0e400b003420341d000480c000324640c0002c1140000d000300c00c1404c0700480e030280098440b0159102d0050301c030090141010300805d0f81e40d10340c180c4a4480b44d002c12640080d2011300d2104c56a9031211410710086480a078180c01d00744032002410354050b00406407000d40c0040c0c41400d201200c802e0212010003250340004105000c10001142c507880300301507034260745000001d170f56450482c031403005503200c22041004562206014082d1510040592026507040c2e41e40076a80d001d54501c19464911503810207841e5542c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 277675485 1250 277674235 277674247
    0xb010c0602040e060111190b07050d0e01020d0c0c0f0803130b0a090203010b060703080406180b01090504020913050a12090504020406020106080c010509090c09010302041502061f08030a0e0a0803 85
    0x300c144480c800e104c266034426104d454407401c2c0ba25001030340420801c8410f00041000081c0c0701e03010b020f074011464900305040c4000124120305a806009804025940c0050600d4030001c4030301a05040f5640703410200b101981e9175a130340e504c900b140c1700003411030100400840c40c03010703441e14800d041d140c00445442150409882400003459407c204074031940c84c001903500c2d5810a0800c0c0c0e100350780c01d9207894060b5682c2e40c031100c0203094540300190940013201c034410009007016010320f010340443d14000601d450244148460005d0182c280807007661a00c540740b001410001c2c40520701e6a000714440c00d040d2402e0819199101907801c030942c403c2c0081800300f907160b415405141100c08807400c5800d001d401100641d1680700382d00d1004e80280d0340034005071050403440d004000d00c7c00103150061410356100b05608020b20710b040b5010050b0482c201f0f10186030803d070081e0860f001c005110b07a2000c1c1c0703400145035413031290201e00310a0042c0d0340c150018a942c0c0502c00c04c001d08580c000e4a95800f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 277676735 1250 277675485 277675499
    0x9020402070803040b180111090f150304050a140105011a0c0c0307171b09040f08130303030207060e060c16061814160f0902070609020d08030a11130302040b010c060204 74
    0x20408980007003895620a46e298101070050041d1211412080281450800d4000c00c3c0280c2c40c01e40031409411000042c0361001c1ea403000001188241d005d80c002c0d080410040c6000d002014810312400e9050381800700512a49841400d15002440502c003035599172000c02c9510381c1482c00248005601d806103400006904900c510b40c008212403c10984090303051801c61001c0054011004ea50017540c0e4800180000c1d541104413070146024540260804d4280b08904550701c1850b00308600280c0c000c40c100040022500901002132035110203030035180f80500c4204520700500380804840300b14446440d040c40040e0340048100c0e01902054a200c1d1070900301032024201009808101b13100e0a24140d400115210000040e548003000c5032070858a000307190380103504946016641c0c035549454400050351030640000da241d126001c103039200e2400012600031903061781284502c0303004c100400a0201041098401034a41c11600051b50082040040310b000b420814020402c600c00038011a0380 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 277677985 1250 277676735 277676753
    0x30b0d0c0806190516050703090801020a230702090408030613050c090a060c0b0601081503030a0f08060a030f060c0201092f060705060a0b060903120409060905040b07030902040207080304 82
    0x4410588204084a0f0300682c0201221812034080000002c50107a89039010b00c03075401800c040b0701a00e4003080c65a100c10a0a0880e1310114a807008501d5228080c811941604d800d54104809450040e09102c466004200c1ca06c0004000402244c0c0001c0041e40c180c1c0c5070030003489050b14842c0c04108500d4046000b201c145c4c08440004d1182001107000981c032441050000d5109510070450220b40e01c0c1c14005440c080030142018410701c00c61042e041e0183c804001602d003288981d92144128802e555018100e0710f4003408003070203403042000503c0841e00d40140c0c0c02480b90720640001d00403045920803401840c01010041c004000707195410301340780d0700c1e1011444000441c0b801c8585401d190303017003045900c10f03090000e03d15040840000c124204560202507510001341c441490801600c0001e420030a0360700e10300801c80300c00b14050207012407130b1044501510124404000904283e2a0801803030300080064042585030880c200454607181c0544001d145d02500c0c85490342060b2400d1206 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 277679235 1250 277677985 277677991
    0x18010204030c0f050303090d1103030403120f08010e070912020303130308031801020a0e01051809090109150903020a082104080306130908041712121006090f06030b0d0c0806 76
    0xc0b07143c80072800b081c07901d00402100c40184001b454110603d4a035501c86403501c00206089506000c184400004544440c0400c004030f0701a55a0f09100400010041c00424041e0401d15000c07030110100406603812130180d009484013030042d100f00c1a107078800a8954030034000c1d0340b00c00c0300e019800041000010305c06580201e0010745050b5550185034083c600f01d0286800100010344500c51b560705a5016100614000e180c00031610741320604280440c030f003070500f541e07108056076450300c1d44814400403c0b00d03d240070400c0031090103501000d8600a66550031035001a0001d000024642c01030045060b45c031910302159103011425141508001c1b100c1d8004540c21809040c081c188001743c1d102601c500b001c1c1a038424080b42c1080d00740500407020b407280c14035109031403080300d421135141400d10340500140220702058007614940343d421410200401d07030154051220080d02030156901d0001c110096070124a80003038082c2c1c071900000c1c50031500c1c003030103843c00e4035050300403409020110760340384 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 277680485 1250 277679235 277679249
    0x609050115080d0201050903120c0c011a040c0206010b09060c07090608030d0e0627030705030c0105070314240a050d0b150f0a03020907050f040807063518010204030c 73
    0xa01c0015603507040c5d003aa1401c9603542c0709904100000060101041d48841d0020700140f100b50414041d00740550031900301201e52800c840e0a09002546441d250148450806c503d2020300480e516100b02e81c5414001c200805104030004111401d0500c01046540d00030f000117602801050358030000c10b52258081c0c110ba200c480d00303081121040b00000100d2500503041240003181d4a403c80030f910805a50400a07482d4602040014170040b80c0104098500124144000201400c2c039010203002c850ac0b40300e0080da80e40d0140e082100d54030000141e40c1c079048810f000a00c01c3e501500000f40140196040b041d80403000c0e0001c142400580c010342e601c24042c2e0030707911650318605000c10018500964030554041d500d110180b00600b07110300240d030403000c1c5080c01424880d40b030201c40100d8003c2d80005145a01c003040c10802c0c1c640c0300c41450070b403805c3c040c81c015040e02c40d10303a810311000000c0000103000040c8808903402148021856030b41c2d160a0f0021034940f41c503450158115049841540c2d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 277681735 1250 277680485 277680493
    0xf010806010630021c140121030806031501060c0c0602010b060d02071b0e04060f140f070c0b01060f02010509010b060a12090605011410110c010c060905011508 70
    0x40b4807280a01c81000101c942201d10b00e501c04104030380181d8200748000f881c21081e40a04c804446414000341a42610000d407202113006010108400c501640580c005416050780540b100035030f2641800f80d000e601d805281001030381d9213141c0400c1c5806540340c3c54070b401100c5000000b80f4140e0203000001c802e4820028510115a1400c00b02c3c01c1e6036159000a038425010000100c0c410910360040402e40c2c4556210301116600025000d002d040683c00400800c41410400c01006014425003608a900003420004462003d250544a0760002c20f4410b0145010300402c0002e809200902d1045601054130b9003a0f68480c80020a080714040034230001d50b00b41408600c3e0500e041c01508801d14010308003d0801d01003050481d07905603007402d00c2c00700556904508000c13a41600840c0d018011603841890910b801c44240407161440442070000c004400440b500301c410089401c01c0340c05000d1902070386d030701c0060504c10003d04100f0401011507181c89001e54240d011a50035404440d121820f176 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 277682985 1250 277681735 277681739
    0x18031e010b010e01120e1c2102120c0702010201020c1c14072120061905040f080903100603060902150703020706030c170a050f01050312030a0203070203070b0f01080601 74
    0x43d100e005040b031081c0c0c0401e4444180440c001c815501a04094801404456074040e180c8105540107042c01c82c820002481d50b040740e68614550816980a4801c4030400c40c070703119100c5140400c0c50805043c80e6070745040011400d00307682c400d40555190013140f00a03039032081d98084107406440400080500403406075000c103a001c00b03150003502d01c0507400204682240c1016516a4540d0b01215111400d0013000e00c8008100c25544252141c41107100009040c0c071304010110b2111440384800d529510750074101003000160102001404496100f4000303a04c54441c140003900713090524800c00c0c01c1600d008000000d06c40942c01c050b03040d03170090312220143c071088401b003600c0d84580080540541e100013000c04c119442544224145d03140c610f050710f007110b50f14191070041c600503640b08081544590521110300c0d4800c1010b401484118018001c900400c5c114617054040100601d0001c0d40c0440001e0400b4002c0c400c550450317030304c4a08207400d03160108161620000a010745040740c0302e81800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 277684235 1250 277682985 277682987
    0x90b0f302703030a02070201030e060109020705070b0a051c061205010609060b09100e0102340b13030803180601060207060201180b04020907030f110a030b03060103020d020618031e010b01 82
    0x24200d00a0901c002075032440d903c4402d154040d40c020380d4103d0405070703a10340050300707101c045c001180a0445400c3c0981d9400302410000e05d090102d802210f03410360b04012090500303410600300d480001c400c0f502c2004072850698004000d01441d444921704014559409003040410743c00041583c04002c020440035880e40c00214042c003500940d81e070030014901b151403045008144111100805104440340d910020802c1c0170b2980b40d0062080060000700c00c0408060a20801c0c54003070010015114102403040c1c01102e00c401813440044c03d4400000003250855001404083c01034000008558865a4501c00290382d404caa1003500015460300d2041c40c2c9246e00c000884030901c1c1c0041c0d00c00b400752113540800a1662010b0900001c0c10790f554201003918000e40550300b82d8602c83c0c42c8860702c9840c0c40c0f2000d0240c900c1c00c2d4840307100f034024600620060b030748d606020802c41c0d010b0341c5280d240c1019184500c526120409c080c2e900d84114526a095811602006140a102c140091044540640c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 277685485 1250 277684235 277684291
    0x40807090b01050909090c06070602040e070f0207090c1407030207061202040503060610120c030b030c03070305190c091407030608010c2102070c24090b0f30 69
    0xa6800a00c1c100404940380c500301000c0c50300501c03c4401d1f03889081d04400000da540c2c1c440383c003ca500e25000b0504200703c03d0200030742c0b9400511414402000b0300f000b0380080d1a0802406a1503c456803440c285080a114442208020f440d401d0300300c1d590000c60402941d29800c91080c600040d07401a130101c004c00e00c5000341c4044480150041100751144001c1024266003103850700e080240c00b0b00c400440b0f042d00e005001a580300d40c1c03000600484240705045c00c01440c2e06c013050280d44070b960100009000024040c0042403100001055101c05203006482c0c1d4010b41e1042400c0e40c2006140c83c0c0d4808140b0100c0e025410b0f07914100842071f40c0d0542c0c1ca00307988207a40d2080109600d41084500090309600e03c0c54000700780040146444515640c1414007829034000405150b01610206c040d0b8918203840800100c0b00c1c00c0400030145040c0800307600388a140d141d002e1104c1d01207110410256000b401d1b603084614800b4028039003c180003001c54a51084445c10140031100d200b0a0554038100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 277686735 1250 277685485 277685501
    0x506042a1d010f032001052104020102071d0a1a090117060a09080306090408090a0806010302030d09210c150206070e01080106051b03070c030f0308100e0117150a0204080709 76
    0xa00f00f2469600035045d90003d40140014907042c014100411207907a05e590345402d40c0d5106c642c5181714203007001d0000910781100b42d0010b40c00260030252030944030796060b210650002e007058020030964400341240d08440710317508901e9007101070304001244101300c800300001c440076808121101e559a505d82b51058801004c806054070f60b0800115016041c0009501c1e400f40c00713605800e01c0c21409601148008290703511019468000c0700040c41140740511841032446040e1030040c5030142072266076508000a5001c0f1450080c0a03c00c11701003000342549840148554403e08003100c03e440300194a804040b900480001d04c0400a5a810340c01002c560b410b0391100c2d561642000c201a03802c160b01c04080480c12103601c001d112203000101c40022502c0950321a82800c030503540b841c98041c016401c0540459600e002030320003413002904044859044960300030280c01c1c407081300a4600d080c9141c002803c5080b040030b408001c80b52006400410480340c0f980c2c121001c16a4520781070084500c11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 277687985 1250 277686735 277686743
    0xd0f0314160b0604150b04092307050a030b130e060f090709090212030f040e0108010b06030f0705070c0f08070e06030d05071a040b060411070506042a1d010f03 70
    0x4044580041442d01452992000029000003185151039010207640041540401e0a1100000c2d0912861195009200442c015002e408001451030501108240e02c01000d200402101141d8480759a21a801440702144007902c21608000441c1410300503041c000c286010074826680405d200d03107001c1808030320541d1802c003c0d04070103003042c60740f0010b00b64402003079901102c1102d64250744007040c4010312440a140404640e51032034009020207040c1d0507030091956903d00300303800c56a91508021241c0c4149100e0003c0683e542d80481503540f4021820040c001c05849040810f4034078880d000e0209484100381264030f02d50381c6121255641c5011288590103401a8800a0000740203030701a200a5100d042d40a100780150800e001c1c200e401107900351034415848003801101d0606101e480b0300ca0300c5001650303180030740d542c4500d90b5031103010380020413100c44044030b03202070051550340c0281a0741900102a000c5c1e03480006c89904000c1a820307110f8030301074a000081031038144000707000300d0f944 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 277689235 1250 277687985 277688017
    0x40c020d0e240f130501020708030307080415020c062203200106031709010f03050702030306091b0408030d050106020f0a0b07030b040216050f01020310180603020d0f0314 75
    0xa00c4007406164a620350b4000c600202180d8202c034155014009440c922929040c51600c0300c2540c596000000c0159200314103640003402c0a02c51454080101c941c1f00d103890810f0380786070b20355260200403103010342c400e11040e51011031007140500b0f005c60000d001b21180d408072400c00024074403042c0d00e44104000200400e00300201070742000010f0300d20042089100c0000280c640e074a4448094002074440c0d283d40030040040c0e80c0b1002e68003c20300750000d00261404110602d0308800181d600d100180000e031040b04c1c840300007100d24040d44950002404003541c043e84555803014965603030340182021780320f05401c000c0040380f010310010b800745400d0b805000400f18038209840e5001c10000180c035540805441ea01d01c501c03e0b8455000810100b92440100319481d0a24140135003407e0048884803800d9004105014120400d130507480d00743d458140b018841403541054001c01004150b00c001c1d0003d8000070100c05000310b002c80000c081b4001e44400c0c0c813102080c0069400381c810302d0300b40c490b4214 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 277690485 1250 277689235 277689257
    0x271005090d032001060f0602070801020703050405040b03070b0d0f0e0a050d0c14070308070614010f0501180302030d090e010609030807030309020d020a180b0105030c07021c0818040c020d 82
    0x11140f041e8034040680c14031949008440e01c1206403c0d203070030741c00024086039903c00070031400d941000310400a19051008604152050350001c12600c04c51091510940e02c550309040c16036824000036000703041c0c002a40e60303101840011b41000d061001d1450341002d2800381d10b8512548040341c08041d003940701c00a0820000e1202e400c5d100380d07016000a558a441e4000c0108104404001000c0903500035200d2a84480d030a240c48421742e02400c4184c00016142001080720748150b9890714182d131005d0a01540c3c000f407821080840c945140c1c006949441015005040745400076236510075140100e00d0440303241e88569056501003424030009100290030030442011a12a81c0190070240c030040000d51030368619000180d80440c40e40000d602414800e04520002c03440c0c0c460407004002c2030034042d003980b50440080415001d410b5000e4000d01d404d0003100b1317558510b001714040345540000f06546030025141130041c0b04200c0c0d00003174002ca2401014a104500004043c20f0148450b0340700ea90070320f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 277691735 1250 277690485 277690487
    0x40218040510030f0b040b150306152b030f1106060f1225080706080f0c0c0d030b0117040f1103030d0c0507021908071a271005090d03 59
    0x1c10000c101c1003010007040800300c0000e006040c8050054020750342000c580c1032906004032800703030142680f0080e01d2000c0440e0810b45000c00c0c0b0b036500241d00a8039400380c1c0c58500100d0040740c0c0c254040d0300c2030070100101a0040e014010b00c40c107000e010796140f0740c580440c90b00c00d440b00c0d07451811141d175642c4041e000424078a4081d00c071194140b00580b03504140e0400310400e41c6404189001c1c44006414080c0070350600004071140f030000e0803001d0003462402e290410151082e40c010301143c2c00c8080d91030006805544100c126100c00c04200c040f2001d810302440020000e00754611094005000306c5070301d007a01c0d400d0400550045801281d001c82d8100300c0d6a07000300c40c4035600c031240e4050106201010761519144100079070582d00391101d41d9541900e204006c20140200312404801083c0941413102c48000a0650260382e0225509208a03503d40450301d03482c02a070714141c103018201c2c81c030400815180140221441420354080e0b10041640d07106481c9401440702c101d4010030455144000300e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 277692985 1250 277691735 277691741
    0x10305070b030a090803151f050d15030b09062a160204060302040204140307050a060509060d14010f09051014221d07230405150907081504021804 64
    0x200f00c804000007460740b030395915088290070888a081481404292401a504100d043d103040754560071001c0c0d954002c0c0c0d8102416034002c00d0042202c140d542e400c41074540c1d8400341d8080146400404680709494014070303183d900c050842d01101d25140c0c0804001005169000101303c1d058010310050501002640003411152440010f90740542c60322800805a01c80d407009101070001c440e0038a03118418041454640038890380140c2c001c42ea0007c003080045e501c0026220141012900103503928880e00020b400707000a28420220300291100000d0210750400c100800c452820750180b2682e6612894000b161a070361250190084040d400364280e80b0b0700100600f180790010000120003d821400700049440c4481c0740001c031301ca41822080840020080b0030003c01c0c00b601209540c00c00a000518034640300c585190081d42c4400114810722150b034007201c0882c4016191600c14945200001e03c0034006852410b24090041d111079083c0c107080c001c440e80c4040c2038007507561184a0509200003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 277694235 1250 277692985 277692991
    0x7050d030509031f0506040b0d020a0504050c0715140112150213090f0603050f0a0f11040207020301051005040605062a010e0d020307020411040e0601030504140709140609010305070b03 81
    0x40f60280d10030076204c0b83d020301880c10121001480020f45441d0000a100c11181c0301203042e031041414100c2200184e4440804109940c410748020035544c80f03024030390340302d03016116000b00800c00306c00c80003a5010140d4071040c00415940c003100910717640c4d4920304030a80c580ca0405000e0b44403d45800e400900b464000340340c8035000c000c0480d03a442d43c40e80d90b541242c8075001c0003000f80c2e440e10010001d200041200c030040d018044090108102c0c6030765840c400300c4483c480184104201d01d003a0039540e840b64184e511181e0082d0081c001c615000103015689042c601615209515025000c02e160a048080e2841022580c000d9598140c107101403007000c6003515940d0600e503498005442c0080700500c40c02114004540045440e07250510401064542a0500c034403101c106010401414500304241d6802a00a0078002000d89503402c0035a14820442d41c42d031906c1c80b5201000505075056032011294aa01450200700da803654810000d0844d0280310107403903039104040074000313580142c00850b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 277695485 1250 277694235 277694239
    0x12050402010e0f1f0809010e010c02190309030c06080f070807021f090c0308040f050103020715090317010b0a020609011109011409031501150314070516080403061d07050d030509 78
    0x13880000c4103090390201034040c2d0008001035142410b0082e42c8100340194400460803070000d010f03040462600940c1c4107080030520640c404109204024540285070f5040070316005500400c40903200d9901800c00700c1c00b600c001e29000000c00001d84e03090711510446018150035030107491026444825038461300c02281c001c210440e902d80407400090810140c22008500c50100951114905449a4480c4820360701941c141401003003d03400007683e003d20041580a440000111486503050444810301610401011001180000304064000402903c0341540903800c55040707548052003282a141040c00403c2c0381c501c18800c0690642c0510584080310788200b1041c5c1c2401007005c00246060310711032a074008114a0300042c0102032032201130905203032050070184185c041c03030b101142c60500000e010508000b800301d081d011080a8044603544982c0001d4480d07243d940f00e00300310004010300b0104501d00e981c3c02c2c607281000c1d01c01040c1d81c6d00f1244002c04c0420301420070349007501e865110704025a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 277696735 1250 277695485 277695499
    0xc03050f0f2512030c0e010804060f09030504051002070b0417032101140306070212090f0a03060e240106030c110303090d230906130b0703080712050402010e0f 70
    0x800d8080d0740700d490100445403402c060080e9418505914003042c1404010541080c4510f050b042d0403c540205800d000e00e00003c1c244c2c1c031410010020800d0002c03583c1c0c942d062282d000e00380740d4084017403c2615022030b1149040100d0480070380c0e5032266440345900c0c0a0701070004000407240409000360348100001924509581405400d08a1003c001e000c03440f0b01c3d0250040c051800340c0703401044411001e0f0000c1c100c41c2056030000c1c1d502c440860130000d81410003e0918540d03107402c0010071a040c0040c1495403601c0d16032400300080c01304089054210711031880250a40741c003401040742802d031014180d080d070ba424604102c01a00e810b0072441d00744a520540d01c10600c1c0108001c0d031080c2110030241030f0006d09001c000b40501c001410b40e0302000710483c0d0200389820900e0803a0728130310f422a00c10b41d40341054880c503030f080c0b922584215581907010a51a05164000b0300d080e100d91515070714051000c894141e404115030041d20080e00042c1011075074032180c18004400c203882040200700d9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 277697841 1106 277696735 277696747
    0xd1a09040b0403030615020a140607090e0c130914070509030c2707050a08100612050a09051207050114041220010c0c02030c010c03050f0f 61
    0x1600780c181000200301014002d0380316800904080b0803145031101c102c100a511460401001d0700c00700450300c4006c400c01408100d680c4074101984616600302e040c0001207060a0009242041e600000c1183c0243e0141c40e00005000344291032000c520110380301d130f004800c002c01030301d50405d01c4020b000c40c02441c1d50100f086e91040c801a207003d1100118442001c40340c45446607040309040c9a8028805101c0c0d0240c0201903283d072548640600d070311600b50070fa024103403600c078010005401103881c804101d1160051038000d45006d90114800c0c009499640c2010107000010760058400640041044420b01450b4022220b2001c080c5081c9403a4558011450074480c0070720411101c090b01e203003500401d0081c0c070b42c280360320402000f46881082015003110707095203041e8864401c40c0c5100320103610821196800940c1607840c1d6041603c2400b0404060300500d2a0812002040c800 = true := by decide +kernel

theorem cover : BRFrame.Cov 277517985 277697841 := by
  have h0 := BRFrame.cov_init 277517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 277517985 ≤ n) (h2 : n < 277697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
