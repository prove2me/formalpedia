-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:27:28.662524+00:00
-- url     : https://prove2.me/submissions/518c1ae2-ddb4-40dd-a693-958149fd9c92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 544784172 ≤ n < 544964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 544785422 1250 544784172 544784183
    0xc0f0c03030a060f29131703031b03040c140a050d0506060307140306010909031115090106050a060e040b01030e190b09030406271706090c040203060105090904020607 73
    0x1c1070098060032078004405440c1c100e03482100040c3d40d002c5105002c05082d52400203560f80399400d2003100725110080a030360030125880d8503416910202c600309008062440b01c0316030000b10030701645280804111000000803e4124114203007620380c809040d80d9032196010706c200c12070046604d07440d4250b50350000d20303009000c40e020758400c3c20b01940340c107411903210348680203c1c81c021540c0c3c029480e54000c03100020b001040141e0a01000c0401040040303015824803410b6500d0303280c040c0c800c000d00300c044684100c4c00320031414205080d0b03003921040d4120074414a03d00b88207200346d42c0e00404290b24100c0407600071070305102082c010b900401e01502545014001d00440300100321394042654510b0707200d0003000c0c281d40e990741e10741501d0b402513000f01c40000300d10b104540f0700f211010010345c020142c00c4c442010001e0352a10941c0318504285842d0401d80c01030030030051418000c0c0310071500c0c20400e4800f9490b510b00303540001d01c5031148141261007506d4100126065444270403c0e2806168400e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 544786672 1250 544785422 544785427
    0xc06030203070e1507050c19031403040321030c14180d0212030a0e191206020f031003030201051317161b050a0f12060203060d0c0902190311030c0f0c03 67
    0xc0c803d41071360b0b01ca2403040da070030f02c06c81c600760803281480c1c40c0580c034103414120a41200c40c21551403100008101c680c1c0c0703046100c280408400700d803882d01c034862442000c0b8004502204c0703060000d01070f40c00145081d03052207444000c0f071031565141c10485d10340281400000f03120015200010702c54810703240c0060b4100e0034001c0f040b212480008020701d50a40070342c9841040700c1c036500c00c021004150160301c0050744280307a02001000f906c0103003801c50318840d400260522001411038600d41e041140d10303443d070a110800070420f058080c89802e4104980e0b800c841e00710b000b04d8489240f40c01511260045482001822581680f10900c1014603507601900d202c1d0500c0e550b5030382503100c03409402413512030720303140000107880d2558000880860b02080264901800c030b6440c2d6100a400040c859074002d0740d43c03c1103000041d0686803a00107841484070050310f8140e10264600003004604408081c986403603000c2c55000011415a584003101d0016207030f544102104000300c43c00b54140301012031202 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 544787922 1250 544786672 544786699
    0x9060509010905010e34020d12060b040302010c0c15080103031d1e03030409021809060901180c14030414010f020c1f06050d0f0210030b28080307140c0d0c06030203070e 74
    0x4940032040c0d1500f559811100380301540441e0848240e403103140b001d138bc010001000154010190312240d01d0244118244075030307890751500c3c0700c0c80c0c40d0042c0c0070024a48900510415410242181241300307202c05c5682c1410062011480904401d1b0600045442540c00c0c1092541c0030001c0303074050441110b055480f01125820b50104852080311248030306403990004034182041101e05048500d03200d99100141c108940080090040044c1c0c8010051003d141c0c81d50061910001c5000d140b0074002684e108090107030060859041440404000c0d00422401c14038540000701408500c244030361000d111020880054001d0107d54012500080710315901c40500070703e5100c074003c503802926110b1070018046822400c40d43c1c103007c140d500c1a92109260901200128501e42200040542505980d255000d00f440c40d040310b03004582141407040c080c13050505c184100d07140e005066440200754805590b840c102145940186020140d001c070024512512441500083c49405031103035240c01c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 544789172 1250 544787922 544787927
    0x3904060b0406180b03040302030d020702060d021b01050a0608150a0b04050103081c020906040905070309020405180f1606050d0207080703050a1704080a11010b04050109060509010905010e34 83
    0x84186407410043c0d6008009100b0009004582c031035a0b156010f9494a03442050071002900000703400d81c1c00c10024015641410b41074070003051090614210340c042010400788003400c3d514001d01d41c0c1242e50409408100e4420001184030040c1e0f10006e0007450b81d03940200d088010b0641d00041544141003000010a2120120042643e2010004803950510704c10302060207a00c1803d50154010508202c03c10040b000b0703034040c58000c0325910f0040342e40030041d0002804c1d500140d8000c543c2243c800a17612040804001c000d9041c92408081c000105144003010707589900d61040e6800e01c140010003041c160b0203681140d90301c42c0c1c0080966211121414028595041407400c0008a8103140300c0217070303150007140194440c5500c9500640b4121210204a8046850034500307a4190340300c00c52403d4a98403402040e0191078800e40010780d0b01e1504080003416101071780301c243c00d01e03d0440180905203030390214035804031803401c00c881d00907440180185640c001a50054075080b070128004405079 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 544790422 1250 544789172 544789187
    0x31c0c140d050a020f0303010501020613031e0905270606030601110f03040608070804050a082506020309060711072304021323090a050601180f083904060b0406 70
    0x600544c01c89080d1665160329907981c0c0300038001d982c0581d01c007100082c1045021401e04d03480c240b081c54040d0283c42d03800301d034408040c503c100b02804a000d100c8240050308040d07106081c18148618800d200001c2044003900b4603002070041801400000000750304c6901a44644041c00114000c46e1070141304180c1d810b860750014010304001803204004121182d22600d995030045400c4009410151411b540f401d080341d0003400d13140c02c034809000100c0c2c40c0c140390b5501824054000d250141e03a0385440c141c03080c10540000c0c003507414000c480c26840c40c100000074400050f144e10f01382000003059015100d40390701b003100c4900f5610600014044c020b4025030092402241e0f00c50030100050300005041550349e180d280c0c14290040300ea0790000e090700100e50441900444181001d0b411182904c50400c1001c100b40c000c1c080407048042e08002440cc104581c040800342c1101d80c0c032040c00d00c0b02840440d40181c1141c5020003c01e0903060140759110392001d80100009070003a03a5075980c1e218080c080a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 544791672 1250 544790422 544790437
    0xf0f0c07030209091605090105131e0608030711100804060e0c21010c1b080f0702030307031e1404030b06120d0309050f03070302030406050c03040e04060218031c0c140d05 75
    0x400400c00112820441c034400e05a49c0014a08040e00e07540505a400030b02c1d650071080a218401580e01c450044107108090107000c000300a141d840031607003018454140e0b4100300d1030165118100102c03011307900c684000c0e001540b203d4049182021187e02d945885801d10711145d02c12500302c0980c0401c140d0200310750f5100b02660083c0901c0401d032000303503210327801202c1c40c1d49040c07145244240040c524078000c0001d120f0394800d45003015403d4000c01c0c41e54100c018100c0202d88401c5400c084507044c011203003004009441c0a260141040005250034010340c40000c12020b0003c010850b6943d50480c0b51140f280e2a00844039001541d2000038082c020407401a00c0f28050310030300d4020303220088111110b080c0c15070000e61820b0b180500c2101e17036502c0f8204400301da010901c000300e1420a420a814041c5010700780158487c840c46a1841e505c020034883c1c1c0d4482c0d8480790b800c402d1442c50f00100c41c510720a0303040082d6180840c0c2011181041d002050340308034000c1c0c0900d10501c139000000341c0a0b6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 544792922 1250 544791672 544791703
    0x1e120c040e1504081c05100312020d08060d030903151509060812090402160b0a0e160608190507031b05090d02060318030c01020d0c0c0b061507050f1b03030f0f0c0703020909 76
    0x2080711400041cbd8442c2d41c0600307007000151940c0006101400d10708070120580d40729281c0200690b039285c80d081503a410306010303543c034140c41c1c10100c0300a2155070007100240100c0d40041040500c1c001e00c1503900e04100c3c210200c4586c0c041110841a903d50341035802010300526408800c1900d85000c00400030220703950125103141c020501e1801c400000c04a030480a03884882e400681880d00c19540719900a06c107421403105c40301d910000d018507000c2e4502403030203a1808101522407250384030003040510015400c000083c00a8886a600c940b040110150103032801d542d80e0700c0d42c02c0c9128400300c441c1003034240c5110000382c06140e40d0317055000b00340225820b08200100c048001c401c961007511a07101400301102100412414a030603c40001c510070300707000d0725291203034640d200303414404142d6445207150012104c1e5001204160700628460070210051490702400d440f40e44e09500071008403205142d4045028028600100080c5c1c2c090340d001015003580d8a0902c500d07660b03650104691081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 544794172 1250 544792922 544792943
    0x1151e031e0605150702150c0703030215281523040213061b0618031710170a0f0c0612090c051e120c040e1504081c051003 54
    0x11421164800c680c107841000340b41d40c4c4500140c401e96501c42e0801007040c0da1001d04540481200040b9000030107078510041c015002c22443c0d1706010b410181c031440204c118115400070483c0c1544110000c040039045c8812a402904040c46120020043e1010284102c20801404904004007003114905045144003038500c5001100034031050b4041d13100c043d183c40c400e504060120500070828005c0c02d0020303400c1c0c2d0074001da04c0d40340c0005441009039010400b000120300181410740c00340e00c0f0717440303108032030f01168843c00e01800c0c04803004480c0c1f08080300d440312140000d80c0c100082c40020002504403020194031881420003004450007441184041000314007104405d49050099031075160700100c800107168070f8201072009031480000c2007860891064004140d95403030707107250003552008a00a1100c4400c00c0c0512046451103844e441295102c9140340c08010450750040f0390003a40014080e44910002599101107840d01001404c000c0c01e060400c410b0507026010601100c0c0100ca80c0e00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 544795422 1250 544794172 544794221
    0x506130605060d0201020309010507151104210305031501020c150c1603050d0f1106150f01080f0103110307030b0108210306090a02090a050307030b04022701151e03 72
    0xf102d4400c0009026800a020048082d8026800b60032070364051140d101504c01c1d2016000304980501900c81d20340314001c94180015001640e0090008080c2c0d0b84520203c40d03503450260a07030000815460740b03111745980203002c90744207200c00c88100070b0142c400180c14042c002040d0041e040140b0410403482a002c081140d45084400403045a80001c083c14a00c6002481105d138192039080e52030038044848807080310300104001441c401ca009442811461508008200a8880c0303030407103a04002540050004a0360803221250450b64014480012240d0380300210381047e0750366102420703801a071000020951400303d80b80001100304040c205910b900c0a10f450070a01003515026001454040040e00703041c0702d680113010011004086201e190ba4680004e441c0070071642046a1b4200c2c07000900046081c08101c00c0301d64001c0031400d00f10008108482c203c00581440ba01550001d00038480784490b0180e600640440c22886c6440301400403650041e0180c010000b50350502c102407100e08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 544796672 1250 544795422 544795429
    0x9020d09020409150b03070e0f0c04080d0309020306010603230402120601060809060604060608060f06040816051504030506070e13110a09090509070b071103160306150506030a0e0a050613060506 85
    0x203501340c80623100b0061450711400100301c0b07003035001014113921440401000c900c80a040061160141090b64045040300d01031041c1400e101042e404141410f00700410100005002412140300d0186000360000c1c83d070740c41c00000c45a5003410281e10700350251000100d441c035802005540306540340000c450440d1030b40c0c0c0c1488101c402c548140400100e06001007800751030710901440c40303004014411810326886490300707400c0c492101e40440b81d401c41d1180401860800402ca002c401d20710115032403c1c186192511911440003c044004000e01114130b003650350303142100d0700e40701d0040c21410400000c0204104041da8012403c0700b011620780840051042d2890049038032441d240700142260fa468140d111031580c0000c10110307000010404c201c0015102001848002c1e10a50003442c21070345182041030880e020540100070015078224244040c0e02c4c0c4100b140e400c000c0062000072051801d10b096802c001143d200100f46000750410300c844011401d00801290b03001d9482048603884a9042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 544797922 1250 544796672 544796683
    0xf0f0e060f0d02030a0203031305030705030d0e091e04080c011a01090b070201051903020915090a180f09082a1207140a0507090c050901080109020d09020409150b03 72
    0x300c1e5210300e403486042110304120201c401000d20160844111000716400a82144c014118000a80c5440103081100e8a0104010401441c0540c00381403014201c0c54000c0c21007007012881806003d461003c55002d07141d000d00b44d10040d4403421a1910390030070b45400c031001d5100c143c0400841d13003031038600100c600c02c00c400d031220070300140c407017801c102d00e4400c0c0079281b03070000c12041c0d0503c0400e01035070003e2400c3c02c048076148582568010b80e02c0070300004001c0140b201c044011020742e81849110400e8032144442015200c4500c1b0b62501800e50b0441c0c00084c004044800c0c2407541450700060422400b0405001240c06a00e1074600c039084848004109003a0700d000704101c0d501c890304040312540524024950507004400d007801858031046200c0ca030440c0c0040446142e80030360030401004c4140d04c0f035251010302e10300d0824030b401e8450780002c0c0140418014204d24a5001549140402040e80325140c0c090b4040c00c203010908180c1800500e4bc0031000759050060f003404000700702460f0218a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 544799172 1250 544797922 544797931
    0x7060c200606090c12150306010b19080c0702030a0b010e090d020c060703230c0111040806180715050c010c020f03070303021608031f05010327020612010f0f0e 70
    0x10081a5142c90800816a001a2401011044c01c018402294070b4914280d8401c48104c14400f114808600c1403500d841030503442a2040c1c2400d211180d034242e07036003242490b808284c0c0307401c2a450b00c0fa0361a030740305841030440083d8588105020402040306d13003688513048a0964104102e03658a151400ea240d2900c815104016041a4441c80041c6800301c080d0442501903d082c0c89560303840d1204a542075184200c1c55214500450b20110b81442400340c030020701e051060441c1050302d042c0e6155035800e005024000c6440180346050842d1504000c40c0c001023180401400121003001d401030603a40c004030b480d01103542000c0036000d0580c00002c0340719507001d6241c008c52400f402510300700c009400c0b038001a0564140c0c4104000460040700107140203948103120b56420207900c038060340740002030342d0040d810f03d424000350743c907000c08081c0c60307160011814091002c10701c00307480011014800d801904145030407200001c942c24100010326070959440d10b20344000c1a4440c4c0e00d05440010454 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 544800422 1250 544799172 544799237
    0xc12230a0b0d060f0b0603010806160e0f1c0503030c0c0f0c0117130b0106080610031406010c050111070c0f08070b1b010b040c080601030c09081c09090207060c 70
    0x7003140c0012000d502181680141306800600460f0b52800160254804e901400080d817129081c08115190500c003404a010203041010a0300801c01c00f06020304611007810b446140750080e040450107582802c0740c4800d5215040e60742d03034940400f1203042904100c0c1e1200042c41101040050803600059200324004161100b540c0c1c503d0801418641910040000c8030310382621508000290940c54458082c240c9610746504070310705501403200040003c2c0c4030380109030500c0329003000d0048400704c55030013030020f203041c04d425045828810302503c1b03c0d26811086520018680d004c1c060445641d0307050b88c4101019100315036868424523a1424680500e0409400030082d5080d102200c071070410040b0b0100002060740900c00000a089520024050f4045191041002510740c1d040c82144135025a42c00c0441000782407240c0a0ba8910f000300380785408203131001407010042d000b0b2540384000c08039440207550f940c60500d000d001400280e642c04c004610203041d10030000c04000c107151080002c2c00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 544801672 1250 544800422 544800439
    0x20307031410061d07020a05030a03060501030b030606450103060e060118020d0f18050118050c0906011103070303021c0203061804030504170601031202030703120c12230a0b 76
    0x41002c2072044c010b00074105601c1820080c000051045c006481e10000549002846514010002d03040d202c0b540b0303c80d0710030342041c030030003225030b555000009440c440c0a0074581c00e20080c0782c524180c02020611030300729a240c20070740c0c9a00202c070210300d41078900c12501170002c01c9c40c5011a030ba0702c510a0144e40c0600301405c550788100100c603400791a000c0020361020030540e840002010459056000443c4900e007454218401d0000901a4210030815200b803c158580d06440c0c45841b400c0f08280c0754403410f00c00010030200da1060405030103140d16402600d80d00c852528010b002076000b049a054a49204240d00d09840171a20903644100c0002c0d006a569118404814401040060044090107010b200124203501c00c0f0224ac43c601003941c0090080f9411400d14000d421064100402194810006500041e61050b2180003560001c1000704890701b0045003900c0c030380344014510002e103180a00d280d1a000c001148005810a00b0307541001e603460340c2014000f99004002100e8124855 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 544802922 1250 544801672 544801709
    0x31003080d060f080d0314060102030f07050a050d1706010e0d02040903090b040f06090801020322060905030d050f07090501051801140f19110c0405060d02030703141006 74
    0x80c800410000c105480c00084403611100100082c0407a500b00c158a58840a8440a2a07405104007001c611030140040308a10340940000d540e4071400d590b01035101d0300800c8450420108100c24541d45031b009003600c0d2003540f5600000c00b000312842d01f1015028029000c14110350040b210030b40304c0803010f03000c60004002e640074440a040c031944100c0402c0040c00300080c8182007030300580064000c10305206015407400100400c00300540d0001540d03039204000b404100381ca01d0800c108504103203411401c5401f55030070814001c0600d02c1c2d02900c00d000c00212280000380710352120b48500f0710108a85400e0b104c104007154a4040b5004290101e8020800180091110301d5220500501407604014800d541d0080f4041a00140d2184400c01404603d60700204501945088101c58515013203442c0c0e07802d0715860341c0c2d841e0f0700b41c2940d008590301d0002c10f00a0729800d030301d0000c1c00e2300501242c2c0599901e191880154410a09042241c0209900300303070f0b21005401407804942d20900041c041404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 544804172 1250 544802922 544802933
    0xa1e210204020906090306101701060503070909051c09181a060313140d0e1c020402130509190b041802101b030207080105011a03042301020c0109050d05031003 70
    0x480c3c000c03030360300c50401c2c02040c0d9a59420850b281c4181c0a282440041d80d2601686410700016501c116103d6410f218062101e52070014501040303501d80380010494117103d081150420000505500c5001c5906010b400e0072a08070444070112585c01104008908502104c0802c44202c00b50030b00440480c00c119179081d01c0c0038030165800032007243c0311072803460701a50340561880c1083c0b5100d5081c0c000e40403001c02190800c1c2d1808080704180c90113100d0b07054201102d400da21920b01c00078429a80410380307c0c0c0d00d6203241c0369040642030141201800d8200b20309460159402040180303109400e090f90016070742014018841d001c0044100380308102e98903402c20034080c0b2070382100303410010402c06810b980003007050115803484c000d0b005011850700f030110090135a070b41604a9480207940080301031200109400300c0b0383c42500078140d120f03a60b0006115039005082524408515800426034529441d4103600030101903210f9170032079070031041c50442903072280001c0742c4207100c070b0f50741900800c0800d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 544805422 1250 544804172 544804177
    0x4080c0906131109271807030311011103090a17130b0f0d021b060709050607060b03120408010204050306061f0c030507020918060a050c0a120b0a1e21020402 69
    0x86003aa007450071302c03100001060340f10040046a400c000c031030f0b140c03140448540d48101074010015100c01a0f281420458442d0f892900344001410010b690b500200700c11800c0d07000895904540c00f8a239600d00340824030b6542d4800f00c110070f4070b085c428a25070300d4000c0d00d15070817105c40003003044081c1c28051070404c0301044d64110460a08031018200141d184d2498148024000072110101e12645c29205009851400c14028000d00900c21641810301c04d035a1100f081c1c940480e8481c0c030107d6411200300100c0d0400160f0080d040c5094804034002c104141c040d005071040da6420f500701c03074165580004000c0d5441d101458000d104071000e44901c01c41d8850003d901010b4002e080a600d04041c660201d0400f882c00c841d8110144000c9040414800e01031001c42d80200d5104824811418110014040c0340700d99440c01c030070b00124601d691000443d40d00045141d0000070840502280d03036040403401c00c035000d10707400d810216195005c60080c2c0c2301c505042499015110b81c41b12610f59509100c02035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 544806672 1250 544805422 544805441
    0x7051f02060a0b1c06060b030c03040b10030b0c03071701060503150901140607030c0f11040609020c060601030c1b0b0709120305370207090f090b060d06021e04080c090613 75
    0x45d5207901c40415030ba03c400006501480901081c1d031355a25141c14091038030070300a1300805ca010f4080504002146840c1d42e81c41e08440c40c101e05540d252501c14095444030002950803501d140400e000140c1d960700100594402d0901c2a081803c000058040280c1d80009000f01c15420722203400c00206814004094403441b4424140250310407020f4884e44075a40505908540070249109622018205400740000800b2006001e5003010b44130b4901940303130300d002007410741012360380d10580c1072181c86980d4803c4131040340f00c1080d805101030700300385005003421520f40f00801e00c099400110440584901603400b901aaa50381c01d0071150b44c07280f024010b40313a48481c00c205d9100c1141984841000340280750b02d040d90010400703540303404024400c1d0385041c0041c034102c9261140d518045082e540601e50311900454003500301c10f5184c0f80c0400203020302c06031503d41526460301d103d0551010301c02803050b42d8002007296011041c0c0420803180501c102d40003500700c3c4000340e441241c0e03544c070341040108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 544807922 1250 544806672 544806683
    0x190201051c15080307060b01170a1a100203040302120c06040311060d0204080c0f041a13090b0709080c0a1d060d062d02041508070207051f02060a0b1c 66
    0x94020b500801c0344100c0058020890315000002d041013004428401c00010610030f0030002842e1000c8481041407901c000c000c01201038441307280306440c400000d4801203040c801000002c1001102c0c4000750f59030002d0104034021b5104c040380e4810442d0002d0400300340c0700d000300b5841c903060941d80d90915200214100503085841400854200034060011704041c000550040208103058010014900c0e41800301c140154502100407494051032270000000f13080550301a0201d82841d0102d2000f401d6540c409040c070000407050003640e90b13220b01c0401c116007140702211080c9081c001002218481c0340301d40e0201c03031100c9980a0781c400403400303001d40c0710708001c0c50700c01d485003140c0342c0c10252140008085950242c1c040d10041e46164150f084110340c200d031004605050608011210b4402e2495950040c0700b0340e02c0004039598401c2124001a10f406000100050340300075581c43e819889030b0780d100142c02980001010004030344200c174a41035005050507040c00a14654901442418806494 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 544809172 1250 544807922 544807931
    0x30303060d060b06030a05161404060f050f070c060801150f0f1106090c01032003061c0c0b030402100318081c02130303170403020606010e1c1202190201051c 69
    0x180c079135800000c0c3d0b1084102c0c01011450b460a403034041c1c0740b0503040440078240010525128816465103013601c0586045080201406000b8002130300c541c00740300719010f840b40340014050104603002e80030000700d8660391624000340e40c0311079091045c01801d60b04040022501b2403c401d007148203e00450842c80c482c03d00e5a07005403136020b2581016012074001c801a40401c0c0d02c00d046580c0361040320401055942414009440f514a0340880d06c00580264410b05070004100008100d40c8494210b299100c0d000c81c440a0b40d03402205801c0d001180e05a20031f0a0006041810901038002e1000e1404c6a01d013280900c1d8040d96440031903001760000309c0c1200b140760700000907a4502e01c000c1400300020b030102c000b101e1940c60000d081c0c000030803400480c81040307010b1000094001a5050b008082401e0059007522003601240100a600c850760220b114002907010030320803040340b00142c0345c1540d401d4509850b80301003002ea42d0350340000001d0014008201d1034829100300c0f219030b01c014600321400305 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 544810422 1250 544809172 544809191
    0xc0d0f050d1505040c080601090f081b040b180613061202240403030216060201060305280204020f03180606100e1c08030f0907060801060309020310020a0c150b030303060d06 76
    0x4044071170031020400070580140c03d2054640e001002c483c01020155040c2d4003140c20702031065100e02451500c1d00c6400901028850b0580e0360f5082181140300141103c6001940e08a0700598010261025800380c911400007040c44404c3e402000103840508010f01d41708581a821300c41a41a214800701d0754150b001000000340821038014030041d8082e60003400c1260401510680015041c0c4c0410103580c580882040024404108010007201d007003501c1300040d001c00003913207a50141d04002523010788001030900507040c4800155000740c84ca012418060002060000e03510350b01590f4141e071284025954220702403280c07000000041c4c1c0074140390ba42c0584280115560003120700200c840314004001c0204040c60074440940c041034400040003400c2c54028060004501030041e00304154641c1006c0095440070007000300105d01d80300c01156070305a81c010040c8a00c0c41544d0031519021074040e4580003030400e00880e4086c0300014061407441e1a040208504002c2c2e000d0201c8006880e1140700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 544811672 1250 544810422 544810429
    0x10b04030f020127090e070b031303110c060406030f0e0f0613080d060f0302012705010c022409040c02010e030921010e0d0e010f140f0408060c0c0d0f050d1505 70
    0x704d000304844100810900f42c40044a801c00310303990490000004288100324140d0311560100e81d2050300340c200200c0e1002041900303030401e2040c2104a8004a0015001900c1a4141c0c010b460402003507600b00300d128021040c2a03196015040c2101c585c0d80704202082a20710703640c10b1800518030a41810745404420401042079032103540c050f54000150800400030b65800c041558009441e1243e40a000500100c0500d1070000a004a41c104509403101c2021920f0701003040c80031400041072510840045841c0c0d00c0150301c03032442d4500450030407003c1344003580140140344040d080000514180b81c01602031101c000e02c2085100c0380e030540d10000410307a640030310034812a0326840001c0e0801a000c004083c06103100c01da290b604101003440400491903215400c02070403485044851380e2441030100d804a6401903070400080c0d80176030000c0c003651164400040c8003004540b0162401c10280d800142e4030000c01d06007803c041601044038041400141e480011f0107501e484000c8172058441c0c010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 544812922 1250 544811672 544811747
    0x303091f0c170c070608040f06050c07050307050115092a09050a030303020a0e0a0501050a181d101e140d0c140f0901080d0c02180906040b010b04030f0201 68
    0x752401c900d0000380c2c4806451084c00200080d0642d400c0076142070405a40e05081c40910200181115942d14081085c01c081402118070b9250064112500c2d4503641c10024000d2026002c0c4614040854000152156590203180501340c0c0c00c540310207903407854907403200511910a845400700003910750049401ea4590344544003642c02031b64010784541e080c22016115580011000384a42c40e901d40c10401e682c0e0120403603040038a40c0c07511140c04400d00141d208854801d411900500c41d1210190140c11014525203104800d04842034602650703030301400d4065911765050b1034540940c40e00902c0181003800072101c1ea0340d0003a0400a0402450721050b0341e8054581000c1c6030f0703d44507103201d101480c00d00503d0003001411181c000311035150682c000c1d59036294000010134800306123851015550750407907100b50340700516038525030340ca801003040b40c80307840840d4100c0e03090b61486c00108829000780213440659a003c03d4010b1442c84540054400c201044002442c80c0c0c1444042412401017184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 544814172 1250 544812922 544812953
    0x20d0e0a06031505031f05130206091c0503040602100f090309170715030c02010e0601050306060f0f030118052407050721050d0b0303030411102c0f0303091f0c 70
    0x2ca514409801d0403440c1c20b4403009842c440e05103900081d220098ad4038401126894001101c4002c0340d038611100b5003078030700d0b030001010f00103006c0818009141900812031412180e1441c0b001c001200c04441180201d6101c803401600181481c041844040b6031030b4415240039030781c202101ca40d1540c403410010903086d00d14290b00001d8039201100e40d001c0d02401203000715581c06d0060b042c1c0758142008265101c900400c85446220304400c400c7c05601c420102042e408070180003070108001c13021508017124a03844003154240b050300034820b04209040b1844020040349100341155484290080300c09801054050b502030070a03a01c0c0e03d412165101d41000c0103021505c410f41c072945244286001c81b0180b002ca180030307030020420040014014003540800c0103080368090300301a00342c2d4013100c0035103003170640c148840d56800d812400c1c048140005210302100f1248004c007031b180d940500d502c1e800356040d4103801c560062040c0010380301c2207660319000941c0d171070030801d286039948038500c90040491 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 544815422 1250 544814172 544814203
    0xa020126090a0c05090412120b0402030108010c14030c07170c1519110d0c05040302030607121d06040609020f0a0608010806090a0215030901200a020d0e0a0603150503 73
    0x2c0000c100e444102040202070031a102c40e80340c034040d100e0075401405040d400b010022101d030540791021196018195404015008546940e1a0500140208082c1075005c010420f071101052408401c0d00c1140c0c802c1c0c400400c003504025480d41e82a180c50580446c2d200103260038400c05218950420007400180b0051816040d075003010140c80b4074000c5a00a9100c110f4100350203507020113160400c403240d011101400182e140100d95085070103001d5500002d43c14081e900510140c6680a2041911a501400e042222042c0303499980d8100e110141c0c6010a80c0040c0000340115205a004036085400035140b2402c010880380060700a440a0300140042000c520041c40300b5101040f0309a0701038503160080181406517000a001d1120842441560074400800990030100a411600000c8040d4407110342d29560341954984517004000078200504c26502200c603128810104140c88103000340c1404100c3c0e0904030101c01809081c55121818a29400c0024090b28204a001448203525 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 544816672 1250 544815422 544815433
    0xc0812160e01020c030d0e0a1d0a061d04020d0c08030a020d0917070e18010213031b0f090b0607021305041a0405060c0a210501050a09020c0a02012609 66
    0x400140c00c050545800c1c50442d8040c0071501280c3e10b00180140e503004660510100210344000000e11140c500e401c01d0902030403014a4070108140441114042e000048040c0685510b544141c030303a1500816071001c00180c5030010038050700703080c500420700500411010107030f1a00c45240e5413459024000c40300050388424400d02c05103600c00841c05c040d08100c81c601c074400900c0c0420707660301d01c894050003980d0810b800c003240f81080c1d0200c46181184c2a18020f54480900b5010a09001c41900c815201c0142c805108400c0c08104541e0000342c1d10135003113181180c0e017040c94a40061a15034045500000d0400c080005a900c040c041c0440c941480c001050f14a49803410490482d00d403030784003050381c1c11035003840700103640070032044e52141c2001d00700e5807100444107084942844105900300915170300c0e407507001c40303900c50742040c0d040e00e41c15542a002c060396506420300f28411200341c08680e401c04840d1034015842803c4104003d10180414030302419411305200c9c5898060316261800d0b40033 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 544817922 1250 544816672 544816711
    0x51b070803221b0f0f180c1b05060f010b03060a03060b011704060209040c091208071106070f031409030a06021e0d0209030106060806011b0311160807080c100c0812 72
    0x8040020300303040511444e01c5483c29030350002d0390260b802c0c2c1c04403c03034541c04841f402074440c2103082404800e08581804251441c142030b515130700251003503212050310000204440b101d41d411613008441c09848554114910784801f4020080c0e040c0042c108108a444584100394040c865070040c0e02072580107039130740c1c81c0c40c0c00c0100b102d051201c220f00b40102e06504024040060842180080d040f0010f15910107807494a10407800381080d030319602c00d80115000d0180192113511813000c0d44241c40b2aa00c1d0201d00542d000b80d8001c84c1071844d031503070150450f20005451500684800b02c10150603000315040ba03044c01071031390032000d1201e5034240d022481c14618902405000000c02c00703828010424149100024030503c0c010500c00c100302c2000b86924100340c0708107180300170070003540c0545000044106000d0740c030054034864000180704400340821001e50100b90041758901c010005542d84011000555100c40c000000342c070b0851051021a80d291261414248519070800e000124601d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 544819172 1250 544817922 544817939
    0x2040f0513090f150f09050f0645060711121e0a2106090b0604080601061b02030a21030e07060c050a120201051b070803221b 55
    0x2100781564001e10b040030b201c500032818006600c9036054210408803490910491450042e001c0382c103030705c041c00c4d00d41510300051001c0440c80c61069000001598015222102403502c0202482481900074140d06015012900c100c94001800c031131210361550035010310f56456090030b0301120071f180890300d402d1171030f1000d40e0141700000e01f00400762129400c0caa4840103490300c003205802110007074030380061188000e60083d000d4a0101050600e4941c4011018402101800300c6100e216400d90600b081e50f0706600d0064207031815a8070240090003141e1070202c0894000c520324051180141380005032101689080c042d02d512a80950221045c410b14018009080780d00c40001c401058600100d008540780041480d204583c1c151401b01e80107131160521a04054400034010419109200041740d815011341015114568002d03560680d0b03085403072004960b114422005001d00401c0001464030310800040d9501101482d040b00e03008206541d500c2280c20740c480303048145d2005900308000b06203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 544820422 1250 544819172 544819189
    0x3140303101a090d020111010510140103020c060c0702190602030711030c031506011205090601090501050603160c17070c09050601031404231006060e100e0f03030d02040f05 76
    0x2c20204190408142c06032064a405a5804140f18a514601c00c009580c8907500c201201390300301000308440d04189164825030b6140d44030f41a4002200b014504a0790700038803d8503242d41c2c9020180065645203003100e41640e00c01142281d0010300081c140c1540481d0716014400303010a50019a0707518404d00340080794103601d03403c03a8800da2001422149070b44000c03c017101e110b600040c0c0c51007191035040060700c1080003111104940303031070720080020040000415904aa202a03010007960b40c0b640c00348841d0348000c4074040e1f000c0c0e4425014130100e5200300001d100c098004c07203a01024006804c030102c00b0b86d029071001e498003010380a042c041c100061140320340141c001d0800304220001c43d001d103440050002d00103130030140030b0554580c0114014138018030701000701050764500400c052040c2c004189034040c03000064000c0100107000d00301200c002506d00c0642d1503003502d03681001c0400420f42030480210390140028007036480404d83e0b0380041c1c4007801e40d0140c0f400c813050618040c05401c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 544821672 1250 544820422 544820429
    0x4030c080c040b0406060e04050a06090222120c030b040c26151915150203040e010b0f090904030c050102030117101103011a07020a0311120c0916090314030310 70
    0xa0f417400108000007a0421845d450101095074003007000d43e60042c0150003410716900003441c940c0006508441202880c9000084081000d400c15055880d121040c80320051000300a10f50b115140051001ca00c4548210b42d01ca80300380b8000000c1030b100c3e6602c144a003810810300010384410b11400c4a02502805404e03800f08440c1d030110301a1404e0012040100c008604481d1810f9841360703111003480402d00140e0140442d40300908882d901c0f070344029500d510074896079140c021120008540e51081340202c5103986518403800c1c1c18020000c0412444100250045003400001240500011400c2c0007860007000070080548010b00200c0d00303207082103228100700250600d807940a102003413002c4142e0341036a03904113a04110407502072044c00c0601c0f41e504080e5115409040c00410026008070103240e40500f40c6a880650340d14503841d964582003503070303016801903e0000284d103000508201c1d07500ca0342c091401c140f01070340d1ba80303d101042018081d100c9142e00700104000c0c2c2054184c421100a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 544822922 1250 544821672 544821679
    0x306090c23090109120f031205060604090509100e011517060a0b031204090c032f0306040f0911030d0801060e0904030c050f0c10020a030509120304030c080c040b 71
    0x4984581d809088002405820700c4606803002c030b103001c09644125401c00203061130303000c1d10388100303501d00f0402c418500200048000540480d440c1049038020300900340103c0300582514145070911019030090302c0c004014081c3c0b07224100c120b8030714030600d000e5018542d0340c14000007840b80b59a02e003040d81e071050343c00c00401c400b2071820101610b80002403440c0d03c100714280c0055811207641c002800c008118a0140e040309001c54049006940d651000c2c1d0241d0b8140c8080041d0710140c0041118041c224103000a201241007402080a0b0705a00556001200500c00965190000d03444400c5030b10020702131f10003015010220900d810100714002181c1041d0070000202e61421000070400c08803c1e20081c042c000d81000314007010b00645044503129403000c10f684c401303840034210960b80c541582d440c038480e08440f41480c40b400c2c0082000c0c058070303070981d0710903281814a006104034140c0400c0c00c40c516120812000000c10204481c0030080c008440107400800b103114100030989035544400c510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 544824172 1250 544822922 544822937
    0x110105041212020702010818030912030406090509011212050d02071b090509060a020a0507120f0f11100b0d02030f030a0905040612060513020a060f0801082116120306090c 75
    0x16030303000462158230041d41c140340329035045c800003e141980603050708541c004c00c84018100c003014020016205443d0540c1c2d1b1000281c1d600d0040000c40f460038403514200a10b07000460002c11000c00c00380051030081c2c104240b030007c03200201300072640030300425070318442c1d007501800e4459610034200c0e004109a05050041c1e04000c8030b41d075110f520151013000010b50000ba1200b02c5030040d804d403080350f13030028031b0b0001c20b00031468041c000a031180c0d402c000181c1005481010b082c021445007085a44080003807814200c00004400109544507401d0742c401d80132009400142c2d420004035941c82d21407000b131903c601c041a800751a000c1c898110360f10039410942d081c0442030800c140000c000d0b42120000c5000d86a00c55586000340784000007a40007500004042101500a20f082078800059a02d54045a0380d4010707140d01d560000c140198420f5010500207001d0400c1c101811031000410864000706245944038850603840c200060003007526050100640e0240f4404c2c0d02607203120b42071000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 544825422 1250 544824172 544824187
    0x51c17040602030a1d060313110d150e2a0a080c0603040206091207060201050105032401030809060409061509060e010e01050d06080f0606031c12020a11010504121202 73
    0xd44030701130110200d0800c050808104180c81010032401c040e000094552640c9080c0248680c0c80030710f1810058130b064036800c0401641d4200007043d0080c50380c0001c0d0f290300608050940d20003801009803034403000d10410040352608001c0300d40c10100314400002484600c6805000d2000c101c0b91680300100c2c1d6040110300801a40724001101e80c030560498000e665414418001111991006d001380c00360b10600c4004138500350154040c034141c0b01d08400b16076401c180380001c04034104900300d600e4000b880c078000400004502e500500410440106440c2c00c0c1038071450031404945a07a8001040700c241c0078a421003040c0c202038100042d00141c90a4142500c1620000c0e11034041c1c0110079040010000d4400003803040c560281e800b40040d4070554100e45145130304c09030b13554820768070103200380149542c03d501204e502252039000c0f6555140c803da4081d4404007503000717420224045052000356200d140c3d01010038410103104074410a24924549880e44000300101e1a102d0345048040c410480c05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 544826672 1250 544825422 544825427
    0x30506100b03150103110d0c021209060f09040b090a05011a040b1b07090f060e06060309280b04050d0306081b0f0d06090308182b09051c170406 63
    0xc95004012150f000c0100740b40d240101c1c01011030b40d01d90841c1d000081081c4500892a80141c18241080d508030b4070548000300c181c80700352084c2000c5550000b41049600c601030340d46005000d01000003400000d80400d6100407d50100b0101c039403d052961f150010701c0038030080b03d07a040c18880b6158800e403c00c0e00f080c80038070703c42c8201c0500b40010101c0607101d000e40318040007408060005110305000f03100245403110094100e0b4002c980c01880311400180352070034108207803441600304034020902070340d46042030721b042007a90680110142210403038001049001034400e01a038131030300050105107051b100050442e51150040c407901d07000700807904241c2d50201c80003a80244100c2ea0002c400080c42c1c001220401c83c450024092410821001c040c90f400401c07152007044404c3c4103840c040180d0000c40e8031071001c201c2c181121511030007000b103035210f100e04280b03046429041400010340c40b08002000025416402da8104074031540c07031070800210101c0c43c1200d000301407950b802c0c9428690003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 544827922 1250 544826672 544826677
    0x60e2713140c0604270c050901030b030127030e030a08120f16050f0705100501210b0403112b02010c0309051507050f0f041d130204052806030506100b 66
    0x191000e04a03c0e04406517942e0302d2041041203546000070400c161200b1607409003190b08500e800c680130901c0c0c41a01d011605060054410b6108224071740c1c40181f101d40b0303024a01000b80306042c0d0811882c0b100c46030709a24104642c805950081d080c45da1602c01c03013420f10081d52001008014000c4204060001400c04e00c2401203010081c1c1c02c103251264454a0400514000d07520040d140d072041d001c00071000401030340b1040c1610b000220710342000706400e0038503503030013032b8500700500d59080040041d001c240319400e641c00d00b09a4000355210703000d070465103112520851900b2181580300c007400034181c0d40c0910a0074564400303810117001c00c92003a122903480740300342c1800d84000700707241e000203200310b20600c21103007400041a8620f49401d106084800241c002d8092040110442c82c0091800381c041c00846101c0c80c070802000d0040c00780b5a0a10004d0135000d0704401c4c68001c1109411581c4441c1c0c8403091206511060024840e8a1420401d18100002d000c040c08056544810302180c0341d03d804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 544829172 1250 544827922 544827929
    0x160204020c030c07090912020607121517012f0403110607050601030b0609180618032b0b0103020712080907030b0717010b0301060e2713140c0604 64
    0x1001600c519407048428154828a01d88103030703138000c546001c1146441c640c44403a803907000b01d43c0104e544142100c1a656841c058603503602280340b50030310031240807240d044604800d182a50051035690759454184003012842c105e10b003580d446103082000e840a5000103885041440101020400d084018030244d00c200d02015144011071010340020380c60f03600c116a0040d5001080355aa0b6950b0309158280d54425600c9a1054000070042078032403019554240c2074442000107422181c07240014401c440307070902c5040601d40401d0000c990890081e00c8561440b42d0080c40582a41c0f030a406d01c001212810f041c500d0501d44140031440c080348c0602d010342a01000d6060100c0c0c2e030744440030ba081c5028420790009054510690401c071065910015910805607100c4d85003c3ca039881d10241c041600090152f880000c1561445e1807070780c90901c105010809a8518075620392003110300d404010f480403100412020ba143c0d013000c2c200300040c09141c00c280504805441c400400724000703002d600c40d912 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 544830422 1250 544829172 544829179
    0x90d09120b040204090209040309032913052d0c04050f0c16050102031305060a0c050d021315020102120114010e0409020f03010c03060816260f010c0c171602 69
    0x1c001402c6403551392150141580003403044006241034980104a2010f60008071200162443d038104041d0010019080000008080b0301c4180c1d20611100b401403240d00701611980301e10080c1000c0c68000041d440441195294580741c0f00104107805440c2030041c94545004d44d10300000c00240129084025400c503040c400487c2d40e500210741d1007400206490b0000d0107135403001051111803d4810540a40b251040080c0c4907940c1c2d0702c2044404842503054008081841004000f0f9810070030b500600c10002020b107108020364560100b05019001304002001507940001c40c2d0080c80501840e8038010421421807640c50400080000d041c40c11111f84076000e01d07102c548510440d51411080300c507180015000b00148a440c1c400200a460203224001190103082e14058000982c80118800d5a054120740f0400700000528807041618018484205020b0000494401d160038040c24190740d450780e48502d004141c9061a1039545211042d221520300c04212101116804071082a140d54045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 544831672 1250 544830422 544830443
    0x21080306120f1b090c030405060c09040e0712020102071505091507020907080a0606110a0803060a05120601030b01090c0f030b010509060d06140108310602070506090d0912 75
    0x6141d4518003004402070b05000d000704502c04400d00450b0000b988006822500b80362144c480100084017807105803401303010b94205400040d10200590000c1c05a040301400000707610020007a0681007808a4211621440b0011455001d40d030b030400041014000180a010242d0910342c40078120f8490003088034010485240043d0940c0c1403402030380c0c00e598020742440500e141c2140024240e0400b00c401040483c41c2500205007244a04003d1180c2c1d44110024080405940c8519840e80c10050117107a01c400407140110711034451184c030340174001c074903801820a54114034104100f01c90580020301082d16009404509a6101c0d584503020140ca080c00900c020703030800100ea6500c03481c24215001000024000d00c04c5c0a80d501060480d0707801d007030070380002e1000001168440b60594050103040694031821600b81042885a2140306914000c911421540d0707884500780e80280170b09031259044401049003c840510035200c54042e6480c01d040a13900700000a900f126000d81d0140849050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 544832922 1250 544831672 544831699
    0x180601050409110901171003080309031e0a1209030905040911120d030e190213090609030c030f0f020d110a06020c03091905031b010302070f030921080306 68
    0x14021a0007804014400780301600c0c000b84900880d50022040324001000c15600008052086a06d20701031032002650315041c0b440c540311100d0b2600301800030070003070004101c10368103511062160071106c2090419079850f1000c9580c003038800c540054032668258203210301d46000030b9024428400f0b4450071500040d050103203040c84440b030265801e2080e00420001c800e41c00c515000200003484a46540d4144022030030001100e845a06090000007458484800e400043c41c1c208650401c0582c46003001071074103066101c070400c1d540d414200398003003400300d6601418507510030302002013410242080d1052600e241d4000756910400c43c1d018003000701e1046d5000280c001032140340345141e0000c506540f40c0002940a075101d50110103664403030030072118410001901420a80100c0b4030060180400ba1482c21941540184400760039040650821840e00020020314100c1d010318041d030f580031102070914003050188003494031034103908000506410006150b620840382c2c8144160b9801005454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 544834172 1250 544832922 544832927
    0x315020a0801210b180106140307050607050f06010f03020a090c080a0507180f0602150709030f06061e0612020f0d1a0303030103050607081e040609030e0406030302031206030c180601 80
    0x2660f040040030358440005004040400010200021000c40d00030401c09030707200240f0443e90001032145402d40c000349000c00c05450003501810900e40284182e80020820b40002803d00009812180c1c1c1540c0d0341c0020700035828034080c140702811001c50300308052000c464020708401002401003880b00d031294006078480d07225500341c0a18240c18802d580200341c0b518022074900800d130040c540144a000c40300300304488000d03d1603000b0340d1136890b094aa1030542d00ca030101c1c14070240e42902d5040d10f800f00024107038034804080c4034130000c0a60452507281000001402c44105040f0340064034010300c0b030a982c42c10036204803400040d1031003000a040718141803019050901785040b40e0301d404007000001c28448003150142c421080c680d1601c01d55942d50544e410742c05c1200071440d0f1106000030000b00061002c0e44092441030180c10b20f100201301820000d0162075140c3c10490050304080350740a41c2d00505a42d0795041881140a088080074100200c1c01440300e68898010005401000c552683d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 544835422 1250 544834172 544834229
    0x3090d0203100c050d050f06010512040615080d03150b0f0313050307031d030616050c070503071805180d0c03032711090106020303191103010e010315020a0801 70
    0x2402c1980500c508003071141d01900540150343d800c0300d6a800e2400244250701e0700301c0d20704d102d148145c403080d00f0504c6c9d50085580260004008498107991a081032104e90340d0001510010060b280003011458648040201035541080c80081b074000102001e2180304000019110b5441d60380c0c0b550342c0c407a034070480c040800c841c680034081c007903000014604003030550140c000d0002021012031031400c04003010606030346aa01b01c074413503c00020209075400c0706200e200200320040360b65049900841d22080001d0504480d580b0150000042c000c6240040019029040c1d2001e0540040c07201c0074040c2c02c0880c5c403001040003034401c200b048020582014002c0d48105888035444091480c141034415121002007541a8203035035081c20406402c1540c940b10444a049e2611507015500715100c00b030f00708911000003150b0241c881d4850381c0c080240100c40025500030068402c0206095245051040c2550700b011911602c4a00400025900d50340188000781100c0c090761880c4203007404804050307001c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 544836672 1250 544835422 544835443
    0x30809180108191115130f050907051602130c0905041b18120f02010e030a0c17070504110d0e0d050a0e01030e010f0b010e0103090309170f030a0908010c0302070503090d0203 76
    0xb088213403284040c10064004c1c101c946d0200000346e00c0c0c07946901501900e1003062041c184c0c095000400918281d01c1100980b0075032024840042016050364000f4440c1d008075a5640d0b4159030b111020250a61311100f4400101404e443c01c100d6540c0c1c0008610702400700c06180004d001e10440b503d00300e0030b8234401e400d00800501c0089400010103203807108540c1c11901082c4d0020f042c0580e03201c224034000c0313007a40b0003a500c4440080030518001c0210315070b400140260403280142240001c454440c0c0c003400101161044c0d0b482d50f51101440007204642c000021201c1e00d5000094030000181c100b0304888000b102c80c02d003e01d0208000c00100c1c0901a02c0341046500c0d402d2002c00c420345a800e42054003021001d0301c8514040707884000440c1141c60403407026000400c4401c08001140748800c14180035107084003a00c8030036070000c0d600c2e46140d00c103042c5000016050141049461001e108440340301880340b9040d41f80a03200c0d1101c03666402802d044512034405065a034003150350400620340721 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 544837922 1250 544836672 544836679
    0x10f0b240904151a0d05060405070c02040b01031b0806030d0203070c0b0d0b1e03010b0f0310091b06020609070e0f010b090a09060909020108090f070e0703060e010308091801081911 79
    0x4d04190702c102c030f001a001401071000c001c0c00c1a0200d07159103494014a803054020f942ca10f19140784540801000e1300c004502d05040c580d60b1103001c042044030300780000002003541c450f82c4007400d20000b03140c505903044520b181150406d0115100107003c9515407007c81d40f40607002c0b40c0312030000684100900c00070501580c807004444003002501c03402c9000c0444040110f000f080640d05c0d00051003c07080200503419410707041620b10304400300c10382d48a1454903000f0303100c9440c0130010183c10100d0030b51a400000c0903074016810461120003c21201002e00390104051000e420110b504c824030390410700800341c50040101e1480c1c402d03140c0e007a205e40100010710b01400001e99031400c3d80e0040030810016800a1600c50000d04540e500159607940c0040d110020040d40f40742c840307043c181c1000644010b04241d00c8940011784080c10403000c501031070046041560741d04010003001400c0c00c0020440f0640c4511500400080c070000c1408000402d42c0d0b0103803011200c0f2860004030320513110600c0c0b40d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 544839172 1250 544837922 544837949
    0x60c08070c0b040f0e0f100627030b1602011a01081306060311120a020d022202040603020a11060402011709031b0d020d02031608090f03010f0b24090415 67
    0x1d130121450000300441d00540f0215842c0d8039480c80b100100c0b401282c0c007407600e00c1d03c45810405c513403240006039800d4146201c0c3c010460781c1d00040a0180c582c0c2d901c242c03005001d40702800300745441c00d850ba07000d050250008000241a03807400005082c10381e1011814000c03c030000540000c1c05540c204e030b07030a038007400c00c1000c035032649002420714030a00d204d50300480e25503038401caa26000003031030311446070028503124a1f0f610716800c12043c105068070341c05603042d4861028003000004e0000c5c1001d0303e42503d0141c0c80b03040f030b104000c00c000e140c10055551079002c070b0300780000341c2d81013265054080b10443c40140036a54140300700307240d481914000c0050712041c00102c01c1000340400c1900c1c41031000c0e803d07107105103040401241d030703802102411000c1583d5590f000c800203100100505031b0840c003030440d49100440e00006800c480001030010342c665269428042207103820f28040e41461489486170501000d205070300000c5000f21914540101d980b0f0411800c2100d100200500a02c1101d16941 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 544840422 1250 544839172 544839179
    0xa05010509061f0e07020a02030307050a030210020306060d091b060306210b0a0b0d0f050d030f050108030702132408210904150e0109060f0f060c08070c0b04 69
    0x14000c0c501100c080707825004600100c2d0440f1418030210240e01243c0444054240c11310540054400020f40424194421108803500503203061018041c040c2c026006803181106905010b800c00003070b41c8400a10520400801810741e4911050307803030202d040f100000b20140c6a10706000f1155103251007440d1101d00f240000b803000d625802050648031441c50440701035121a24402d800c0800c3c103001000740800500060914105900c80d076800c40c3c00900550f00c07826181c540300410245002d003900c0903040100038100743c40d003500400509020050080201d0740c5445451a22401174040c020312540002c1d03442000403500d50440040c2c0b030000340640030845800c01c1c0da20300341c0c145031180d40316a001c0c1107581c0c0003c0c1704044410f040b40310910310580c40c0c48004001c001c01000114241c1140048600e40440c40484011005018060f20f2000140060a2290a1002d81003a0b03001c62181c04001505025060303101c06260740f00c541c0000200d44488a610380b0f40040d0b09c4581142d800741b10b0114000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 544841672 1250 544840422 544840433
    0x12120309211202030402010c030c051005010b0d0b01210b0111060c0a080a020c0d140c1204080f0613081303080a0e01030c020114011523040501030b06180405060f030a 73
    0x103036158852901e6648101815149010030f90000300c3e00039001c10002621040464003d2500707200d001e20441c141d488004a4080f003d040303c030203800000302201d010030f80c08590350341482911507810090800c0420a0411a049071034401c1b082e00603100c0989641980985c0d0b401210507801080b891010b03940645010100b90703200741c00c108480000188500c0c0031407148041c0703100311019407200340080c1c0a241255181030f940d6462880040655450810071414407002c01c1c050300d81000b610700f601d1035941d480e1400003440c110445689803003a4000340244507031102e0014407400300c0c60b408025252500c0b8218070940762043c1c17591000d002841c1c000360142d8180e5104180c4000004242c8080028051822080703088035042e2299200201300100140007080050071703048104c520714a0006100c81c40311007004641450400701403d0400701040c01d109960b09401503003440203060310340500f00496500c0c0c44100d0b00811807102d006640c2d9002096a50721043c0d4403c1844e44090120f07500e0303e2442c60403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 544842922 1250 544841672 544841723
    0x1090b0c0312100f0306020315090702010b0f10120c141207090b0c0c01110106050409210e0a030818100503040516060f11010603120c03030b01050412120309 69
    0x81e0304801e102d1000210741103070760300d142d81c00c0e00c207080e032070007007035130450391400c0096001510950b0445500d0030704520700c0d92586089071280c40302e07500116591a2000c14010203004003085240b1405d040c810200b0354036406208402e00e1184802e0100d2071f081c200005444056900c3d6068014100004a20300d41d5010070031114090400d0b6a0343c44c1d11b00d036590003102c240d0f004241c84034915400c80d41180a40b503201c1c014600200c0f4141000084c03d941c0c03500094200c1c0e0810300c04840a4140d8107840d50400e040c094168109120b50034103e400e6801140083c0d0007141c18040103101c540d010603034042490344898072400c03d02c005851060800e1100001510507002228100d44900c5214440c19076140b170300604004a0790180c4176000070083d110801d43c1e58030080e00940002e996120800404100c0303c00240a000300e00f502c907854080007504000301034448100006040c0202004200403a400c000c5112141075040385c034407840024a680114090b10103e034020388201c1a41e035030f900070038405602c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 544844172 1250 544842922 544842937
    0x1818060106080f0606160b06120303090a020f0901150c08120a0515031c0311072010020105010f05040c02030c0106090e0d02070b031b07080a0302040311240901090b0c03 74
    0x1d0909642ea1190100031132481255286d2104c0e50840201c400003d1171441215003010380203000382c001195040304180f0b0340e042104c040d40f0a6220007085401e6090280022f40424000e5420094541c1851011141401150903030010407000782403842c1031081c0082941c01500c15401d442c840340c241282c0e200c001d0a0b041d50007049c1038409801050080c40c0001d02079100600c50703802802c928603140000d90040c51207201d000c83b04e8404100404c0015041e60300324102d00e070502400310064410100344165948407440f42c1c01560715220040c403100700d82c81d0888084650440c0e0104000c0380c4071104038110302800c1020380096003010000316610030140c02c201803030b260b550101c6843c5050180120703911031040c82405000041003000c82c00c001011404c03c8000a0800d120618100b103a954000c07040e44005140c1000aa01090620800030a100d281c081c030f80c0b0441c0c0010b042601c2800340c1840880d2a0200c0c010b03890f0009840025901074140030004000d502c0c401e0352946c5105040f551030380e00801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 544845422 1250 544844172 544844191
    0x20a050615130c0807180302040e010504030305100b030411040b120601150f120906110d150e0f150f03100f06050316060f02161202011d181806010608 66
    0x402d440b02d510260310a16140b01e00326965100f06131520780e01610350902e810704108410000b2040840941c41c0c9008802c516521100006414540b03418000c044a9024003510b079100802c01e410010b0f05400340a4a070842d4104106001000a9400040080c01c40b136400340c2d0001c085220441541d280441e440f4100e9120b4107165681415402045541140c9024800d0100382c0c52408560b9411550340300005d640c0c4540b800180d41c09400b81380c0d100c0d9810409140100c20f841da11f4440c2403040d01841e500082c4901e91140e2990705049410964481d0003c1218814122440d0b9101541da940401c20b5441840901541e11100c2c9801102e809046818510280103040440009071030500185c1c99103022120f25413a40c0b401d0602c00c0403200c002003044044218030030b8008070b003901c102c03c4c2d000c2c20080c121400380c8482c65200d48005400c811110b181c42255030350a845c4021180c8403003490280b6007004800c8444559981c18221120310720301850f500d0544280300004c074100b070300940002c0c003072079841 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 544846672 1250 544845422 544845439
    0x403030504021504081203061206011e050109030b060402090409140a05250314070b0d020901020d03050417070c08030f12130305040e0c0702041e110c060610020a050615 74
    0x401c04000f20707100c1c0340b10300d4a5541c0b0403c0900409003081002e140c11010007400e010703d181c04000080e150030002e800416041405080d000707103480c940c041003001040c0c00c2c200459018039645174100f02c040000c160764010b640008038480700e0743da2a17106091840e4402c80c1c0a43c8154400500356030340070b140804841502c1242003060403c00e50116041c1254080c4e0340600080d400c69451030211043c0300901301c03080c850400c0c04101580e03103101030070300f00a4003100103848144d080c000a1801c20110410800d0518290500010490040c16258000c0c06201461768425083c80d00103224041136001400c903020104240120242d190010300f8112081030403549140c1b0f03007181c034400c907494040d8000c022071401c201c1006080e601140580d84113114076060fa080500540125041d55a040207040718147c2e0710101406450451003083d0b10401062440c504108031841d2030795075007001510300c602c9516560360041481c3c1c8200064000d250707120040d6440c500300a83c0e01b41e5001c10400c0a039104280c1d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 544847922 1250 544846672 544846699
    0x1b0a0b16030f1506030b0d060c0e100503060d0210020304080a060212010608012102180f010303350a02130f0612050c12040305090a0e09010b010306180f14040303050402 74
    0x2e9001e4002809462108194010310b00441640108846e003500307500b003010b44241301d0118260388101200c840c110b07115854410418001c102d100900c8080c8081400320a00030f001c525142c214400d00800c1e0305441030607070038040c040180d20351302442c0d000c9803d03440745e02d141c02d0402c611034000d801105410402030440342d0301c540090720300c0e401c01d01400460b100d1a0101180000c980c11043c0c0215002404444851a9034003440c0240e66040b25142e2030000c040004000b0140c0c40200d0f40581490700700515800c4040c0d10605a501c07015555140301e900180c0c0119140b04590f5044a08600c0c1d02c69020fa1038959440a0940807440ca01c9900c0c040b900110342e031103200c5001d005992081510300205071522510408088103044090429000c100060100001c1510741e40079050240c12050b00001403032501c010130318251140070b5a500d04060030800100005a0280324043c41010810780201c0c0b4042c02010b1035004141d00d1148c50506404001440107068140d440b40380200e000380c880c0e400103040b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 544849172 1250 544847922 544847951
    0x723090307080a050d030911040c0203030f0601020f0c13060e270d1b061e0e0c061201061119030507021801030b060d0501090209040c060906090b1b0a0b1603 69
    0x50462003c0d051740c001e80c003040d944500c03a60001a01d00e200d44446883c035211400881c0440d1142c20300b102c05a400041441009408880c005a10010034401003903940c001c12405504d440c0904c4256001e180621140c01981400e5003041d0090320390084004c409240011801100c040410b15810040d0a400030000c1070350341c0400e00200364141900d0b13401072180d030500c01b111a1400220165042540d450308540f52a815100c2c06221440b203800200d2744078034191a590800d41c10010442c0701e00b0003041907503041c1ba000c0074028115036040c20a07900c40b81218206500b060b0500c80114070b4960345245410806405c42d000d00b923024000d4841101c40c601144803c040000c080c0809800720503180d00103515454a450346002c4030b0310810001c1140309c0384d980030812001003a40c04840c207146881c41030004da6406442c40e03000740301c946021441d0616010520605100c0c42d070b41c08240700014225040340c081c08001c1941c0d802d5000c890b03144103150400d8002c031400c0a80c40c082e40040d0500847c802c4018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 544850422 1250 544849172 544849183
    0x14030417152206090c050a05060405130e15040b01030b010e1b031e011403010b1008130206070f05010c0306060509011d0409020a0b030a0f0e15072309030708 69
    0x62110184035150b44034484005108642e004190403152140320206000928070301411042c688692031810784917041c0810410a00001c1d000203025800a001c204030300c1e43d03200e0010782c400030020000a48001002404c0342006010782317903144000c140ba000d1004021441c10340320704807400350500d070368aa41ca824200b26502c0095445000e446c001e0343d45500706801d14401580c001c4220a485805d80e035a4901d000118031090303110481c581d40200e43c000141c1404e000b0111400d1040b601d1088003941e6a0b005042d040d00607103803259000980c094075046489100844142c150000c3c92a410001585446400b0300403420301ea90009042030350002d41c0c540900c041d10205030781611000ca0301150920710001d005001c1884690254035032101501580720100c100000c0c02c030b1174180a940349403042c07000040e24035400034030703110380d00c2e00071028000321020603441036448075450308041d2070301d03800300c11602e441c10f18840b8011075a00c511450484041e01c00102107421003074094075a200e5035002d40903110f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 544851672 1250 544850422 544850443
    0x305010f0e0703150f060c0b0105010305190e070b12070f0206010b0d0b0a24020c0603040b010302060307031e060e0109060b0f0a140406030c120606050f0f0714030417 73
    0x240110800302d030805010f508406441c06040a414214666880500c0035100d41030f40540082411140c0c80018440d200f11041c1c05403100782030034000350429200c100c080014101602c0841680d4018402035402c06014000050600c0c27070302592105075a54003900d5462080e1024404074001c0c04c644190a800482c0460403610080356642c2000381000041c0d0207401c040781ea81744e014100c0072020840c40311450b40c00c241b001c2d040198048007a080d00e006440d00302c400e040e8612a40041c000c00001a121440c21415268180c031999101e44030314400341d01030100e510000309201c1c81c1d911a14212034441c0c1c0304004030380301d4045140382039a03110008000c032a154090124806420000080c044264000403c00300440385001e4400112007d42c0a1094200390000d40020f034031007042030b4017130350300480d404d200841c0c510040081030300e0080c001d4100e100310401c00000785000b00c0c00d01d1050b00c0420a0703035089a042411907015080d40040c00d6200c1d070150003400d1852040300c6865408640c00103560440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 544852922 1250 544851672 544851689
    0x603080d050a0b1f0c08030103260405030709020d150806060102100e0c0405060105121504050c0a08010302041808040e1e0f04030c141c02070b09030a0f050109050607020d0305010f 79
    0x1c60b08100e00c4d404042210200010a12814840c4000016100c000440c001c502038205080081d44082004048003e8103114000c0030754180024426a13901007200c60455010180051780c6150031003c030030140082034044a070300e04110383c001a030354602281084c80703400241e0940380607841144105d0202c2d0440000c04c0c0c8154007518210f4158100380c0d00141d04070005042480c2019141e000c80740d0000f000329915461807440b0f000c2c17641e00e81400e000301c0f9000340102c6049400c0140ba80c60090120905110203845251a09901c081081c051420010415000000107031340342d0302e0340b0100e02c800e48160384050102081d1000c0b0325103010744682132401401070350344000d000d0300c403902c2c12900d160320300c901a10564507402c03266140c0d510802c0f4410b0304800032144032070144c44100010342402500e030301c03040c820b407410003112010f5035000c02c10061050f4041081500405242005401042469002401e41c0304000600c0034964000480304600c4c103643e038007800542e8a403c3c0c1d4202c40781281c400c40303c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 544854172 1250 544852922 544852939
    0xb0f06040e0c07050a050d0c0605100b1e0f072001030b060318160e070f020106060e1c06060e0406050a0c0c0308070e03011109010201050f0705190306090603080d050a0b 74
    0x111550b8200c020300f101400f6030100d4071034168030388455040c41000d420b803002051a181d40001001070700e014240c3c1c0894a403103040702c258034040c0b0b000740c907205004500312600d849008400c0c8c0708410105483c1020400c012040c0caa44d407620780140c031003080d0213000e1505c103401074103c1125032190188510514000d40041d05684594802010304003624080d0982802014404100490482168001040e403401c0d2782203039040601001c2c040d86048030b440421a41480703001d0103826013018914040c12820784108040040e018009005569085d10042800741807003070026a010200100f28003071070251030304006c1510740f540404c0c115001c3c00c0c040780216030000b01d5100800d010f1440f00c0c3d8000014106105040c0e056000282100c0110a41e0302c07241c01c01180400d1603507030900c2619070001d4400b0344e09a140c200311358060105d002d25401480052054400030385c0d9144260441c02c0204158541403000036280c1c40c15401d1604080000b01d450f900d004c2c002035161039940244240d0041c050140d11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 544855422 1250 544854172 544854181
    0x8250c060e0616140421020420190917010b1c030c110d020316080d0306080703020f01050d060f0302040c021606050313150c0206010e0c03071805040c030b0f06040e 72
    0x4d800780c5003401907562440043c480040c4e03610081c0d810010060040425442841c210f1040008603024440356640301070800d5100c407020f29142c011900d284161a602d10a6a00358242c211004c0711329802003410000c0b18507080f006c01d01c05400060365613804640070007030541c401100902c0d4100e051000380006480c13519140111f01800c2c000310185001410540c3c4240c0140c010901c0c3c41c0031210074008219070400c003000484824003800040c08080d14092001c9444c15000ca0b940308100c1c00040d1240a04210a14030750380905c003182c1070101c2e41d4109000d0141d07a005001d00c01e008070311060703008034107107203001c902d4500c0420404400700a000380218520300388082111a0b42004044440090140030a040440c02241081c039150380c402e94082101420008028107011040c0d010746101160401442030f118500c0056079481032561030281320001c04d100c4002083d050646c031140d0003501d030501740ca60f8540d01d50003914103420146c0310149035204000c05d100c9103200358460b08040301c1c42039001c80c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 544856672 1250 544855422 544855427
    0xf0c011e090608100503010212040308010603091113090b0106113a020f07080604020a1a030403050d0b090115090806060f04090512031018060501080708250c060e0616 73
    0xf0358103c189142c4148030b40340c480002c40d00720381c84240840341d0a4600010041095406070081c0d0250201c3d19003400001415aa600640880b101103544a00c0c1c400c0018109940341c0c0c1d006030261034020101c030200307596405000c0c08a01d031120000000e40140181703030b10044a200724942800306011818101c0442203403d0120100b4038114071001c41c0034290000c5180b52007040164090001980600114145071040041c080d40b207900a4a080d1030584080110783e4905c4c0c1580d502a8250800f18fd5074031200345250014030104034011382c0000740c9000450f0b004011440d146101c01a47c0b1a07922544c0ca0750056a42c5600407101c4a03408904000111308a007400c4e0817000f2000d11a9088648a0001180e241d40c01d800444140039406400041000700452407541c0d5100d030307d1400802c00420f414000024400c0c0001441902882244e1000c11b594100241020300c0800c043c006c490100791480c00c0081010261080644119003040c501d56543c010108100340103540e8518004180011403d06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 544857922 1250 544856672 544856687
    0x180510050f010e0405100c02070821030c0f070c03060f0e210d140f09100209010f030b061b0d0207051c020120071e27050a06080f0c011e0906 62
    0x1101c4071b006005044001c41024040c18604412a4010b060700c00e042c4100780d46080496010000e25031712103003904003021544800c90f5005440d0b4075403a9500c0b20814840070f014415803500809090019100100b84150f5620907409989200170a0104025100c030003030751402c07460300100c144076a0305c080081d44901c0000030000754640e42c102003407031844400b0b4106070354011514016500945020000188004d0245443c00c1981d01e0045090025010009054640941c030960605a4540b0b807a006951001c0c02c0d1a8050307035682406940050184109850320400c0b100c690152144080214041c908052042594103200d400003050603074940044a4104445000940c00340800800d00541c1000b0701c41140604242505022000480e41504001ea02150b0182c580001200c500310001c456460314504184805200440e840d00c03007000c0500100007591044103103110f07041000150060205015902c9202600c8001100d000340100c0041d005200800c080040c7c1035400030710086009411 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 544859172 1250 544857922 544857931
    0x140d1a0a0f0f05040219031205030402040209060a02070e0105240d180b010501020616050306120705060a1707020307020d03180509071101060b0c2e180510050f010e 72
    0x80420100c54401c64102103403002100702c05515128001c20041d410118424076007102040915003040d032468554000041001c220941004800008a015540e5076010354060800c003c0800359500b41d0b42d10082d5850105105501288030004000611460030f41001410910406110b0002e0b20000c1c00c02c08699008100d008084c2e83d0780c00541410b035400480f051011807065000d001c45505100019241072001011071003004c415007661400640d0040540ba000344040c2c42045010000500745418002c013a000250418404220032094a81c04403075003a800302c100c2c02210035a2503a2504a0300c070310440c5170183d0460241354620300007038071600141c511200c400c01c0f00466152500c000844082c415100703040040e844141c0112003000038400d110003888070030f01e05850300e0f00348883c0d240c60b84c0c030100d01030141c11450140740a1900a180101c4030f0103c1c2c1c1d041c100191000840d4144081c040040180e80b117114040000440102e188a5139025594601d42441240e01c6d02d42c4610b42a0b00040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 544860422 1250 544859172 544859191
    0x1509011206030b04030807032412020d201c020d0f1703010312170f1b0d091b0602010209210f0a0c05040e061603180c060207140d1a 58
    0xc0000104001c2003109010b517201c3e581300080340c20303c07d000809488510741c100c002c0c40ca030030500d8200c00401e050304400f2035804425030344003201c0300e00008011045603c8081d00c0b1071800c01d207514911110401a0390606405c45034140d100344154021480035042c90700094004040e451003d001c2100c1c501c2e08a040380c03095121401403050032003025841c2e0002c0e44210746610303000135240006504000079540c00010403a4002083c6071155240e90050b2002e88140240413200c441c170441000608103d0701c5004041c403044c84600114076207500742000003140e0a45111003038902080852060084420a20004140091001c0840d07181c12500541c40c001151522403000c02105011050248a003041c1c040c50f040c4050030328007403c0c841071b01c0b0305200804054005800f000600d8528640c5000d10707881c54500091407142140d080001c4000e2010051f02c55402008001000780d40022850f080d0303402e0400c9200107810140a11003031001c1500c00501c40d0b155000c2c1005024005152140e1004050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 544861672 1250 544860422 544860431
    0xc020f0d0c1a28020901030522060f060305070f05010215071e05091e040b030a0f1b0e09030c1009030203120601030f0f090209250c0201182315090112 66
    0x40343c910314841080180c0c201d0362a00800e1345441507826114982d801030103103018010700541e40c05003400c40030b000500203083d20b68904629913102255403002000c2c650040440701c11a4440c840407000700c0f80c0c0e200e081c1c01441540c4d0794115401141010a0140c9215114510304a0b03520340742a001d180100340b44810403a09102d1340c0419500c40c0402408401e04042c5c2003051440042440b0540d401e00540c2c50003680702d000c0d4203002407001c04c0030345c40617a080707082010080c100c00b950310058401540800b8a01440348107100120b040031000700b241100241c1140e4842080030824400e807208404080e000d60800e02400900341a40201203602410500d000920400101403400481c0c1c91680c8003040d031903445500c1c2085061030214079410099403003081c40f00d008503010303030b0380b155500bd1003400030003400071150021640034022030241d0b8004084414242d90b100e5400e00704040d400c0e54800ca1110100b40003801e241041506203010001040101340b90041840040d249900d07800d101c0700680d9510b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 544862922 1250 544861672 544861711
    0x103020f03070302030a06050f030a060e10021903050a1a04090302011409030d061d0115050f03070305091c0212090310020a03050403180b1803100c020f0d0c1a 70
    0xc8004601c00d141c00d450050701c0c1d0601201c280200c441c80d4001500a0a03200da005a80c1d80c0e0029a4200c0c043e8044030108401078012112030410b00700e4014011801e00105001070031810840d240078080405541c10007440d80c420744a041a91507030100b079030303003061300704150001c2c0d0030290044040075001e4000840c1400d207419080d055050111041d0b0103540011500c505070b800c16002e00c10080c101081d41600d4030403074090942003101c042c414540700c520744100400c074444c01442502d14840c0100c42c0180c80f40f600c02c00c0607024060490303018446002e198519801d03a00f003080c556000030f13081c0d0300400202c0d03000340c1d1400749641702070500c0f44d040c861b00511030425015070000381401d03540c4e56800300745820245405400e01c1901c1d004174040e680c01d102c0512071468090f0540f0762082c8021f4414803008401d0010070b00780403c002454669505010303003a000160005801c1c4411000001120b002c1603c40b28101c03031008115400401c14183c801c03a000c0742003403000000380c101c20141207103681c1001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 544864172 1250 544862922 544862947
    0x5010809150711160b040603090f05100618051e0612070810060608041505070903080313020f0f060301120c0806010f08060709140d1502070609140a0b15010302 70
    0x404a07030110003c0c0140342c0307040c484001400705245414840c20350800803070a0107180100303401280100c9082540d5040007406000611001509598210080e00d400390010702d10140542841c1c040d030041554613440300c4591440702c0c03282900c03031080c202da40040000d0360701545580820140180764017148003644804080804c7c00b0103002050980006c020003519510101e040e81d013158000c0c41400340b02420030010071038140e000e40922068031400185c40c1d132010410707a0041d00036007014240d00700100801602850031000300714241d000f1a20910807540a104120b440c030003a504064010034140010025a81103003c100703581d5110302e80c0c0800158444070000c0c40c00000342d2209002da9940c0c001044007520602c9082c0d0854a2490038400090800e420303e20200702044003580151000080c28092180d140341040d4400310740001075540c7c09981c18020b0240ca01d082090300e02c0d404c207540501100a0004e0034003012a0700842c8443c807030b0f0700d08002400b007030f102d4007074581815001c1004054046 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 544865422 1250 544864172 544864213
    0x1e0406021c050a1505010207060c0305160807050f062208040b0f030a0506100c030815030715021e120d09060516080a09030e0402090406080601091409061005010809 72
    0x71400d1800051900d00034021009499681c07007001d03041c88411106000c1643d000c2303048c0c001e0310000e0a00c2102e25046240c225854030a0508545c0b0a00390703840c0b4001044400002020464050340c1141e40e1031b00454215608e982d019602d556140e540a00043c80540e210b101048189018102160400c0d6640707c0c40110348d440001c4421030745400004225084c071581c45200d03000713a016501d07050140303079000b40581152103840307000d0240094040002c0f81801c020795500d03110140074040d0b500042c2cbc0c84034288041011000c0c0b004c0580518442c00307100d1018003000181c07941541c030061900110540240300300e80d100c00b45240a003074540ca040c4001c941940280e5000c2c00c0408411202039040d002e004007107841c05881341100b182860540c0020907486422100c1e2080c0031100142c0d1000108002002000e02c0c1d442298103004034400000c482e0990350003000849c1040c000ea40c82651180c00c900d450300402c442103009200400d00034480c80d4480c0814a601550040c00c481301d203000c0480700340c1c011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 544866672 1250 544865422 544865467
    0x240111070e040b16022118121c0c0f020f0105040909080307090602030c060414210d050c0c030a0e0604081606022401050d0c1505030a11031e040602 65
    0x1103003aa4140040003110002c1130a442c68a440609070f00d8021403c100240415103038041d11603007001c10001001c02d03c01c034202a044100401541c05d964803010000d403500140c08515020141d07403611515054080c6c000c4130106a4428400314413030000b6800c101d1070086040c0307160304021040c0030118000c05684150712850340250b15894403403401c008003d00c007a01d190031500840d0011310400d019400009500d03500a0303800403008490404901c25503141080c00d105100c500340040240b4140c0c5151b0000900368442c46400610596860001d08105442007041070311079030b0b1040109038100ca00c102d0803038500c6000180101d00e010741d01c10400745810b2640c0c142e0800c1c08590701c41041000d0301040944025600c500c0c070441c8610200705003101c00c043c1485003078050786489404008111074240c40501510002c0803c0c500e840c0c000e8001001900100c0d4084080c40c50b020050717140d03003c80c030240ca1258007110704413011559106484540007801500c01c607495a003c3c01001140384a00701c0c5207204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 544867922 1250 544866672 544866683
    0x24140103050a050706030b0d0f02010509030109080d0513020102030406050d0204030c140301060e061509030c0909150109050c0f090103110309011505090c0906031003020307031a240111070e04 84
    0x401590070801d040001c1580002c091528020b05030f082516410a501c3c8c400d0780216201510816500061b6480c4c0716000c20203504d035107851401c04c10000c015000d829506019901000135079101030f00480c0c098910704000e0b003d42c4c401d200801201d031250000b00388100000c0c4c07015042c00d5880c0d882c68040c1c4429005140841c402003d03c2d540c0303007000d101d40b90003004032500403541030618801003000785619210181e10801c000610715180d442c10840001c0c403e1001c0d10035000c44c41c10440d040c2d211140410910510026640009640705031809944d00400d06008020300e8080406210800c5500c4802c8a905160300c803400300ca118119240918401d00740000081a42c0048003811031500076a50021441a190136050040c01f131040d001303447c0d100d54292109a43c0752201d010f0801d4040702c40e8002517040c0318445d0048100528410290745c107044030341c81a809500d59078035080424250003407407032400c40c140202e204103610481041d19001c0c0d40c0c10a8038407060304c529590307100c49011541500e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 544869172 1250 544867922 544867933
    0x3060d12111005251b0305040e010803070201090803030603060f04030c0f03020f250504050414031908180d0e0105040806180c0109060509090a29030c0301092414010305 74
    0x20b84c0c0f0040c2002401000800103890b042c0d03050301c2000d401000b0304003c4807403400c0041e2142c0304144c091012100070f00458035035800d8560392420001d9403584501000c0f17001680d0180300041070400002a24041c160080281030180e481e02030850214500420650400c04401100c60104042100080d0824040d41c06040e04401c14800305103020f0810081c8210340285000c0032407074170902c000c50030070f503001141d011850752560704192801c984045090107050100244003000c1c0051180b041081050546a20729580c1d00c1c3c1750043c130604a80b000040c15a0840b2007038095161284004280100c014100a41025280d500381c40c5070403000c840300c00c0c076000d40780c02c48030044000b00211041007009213000240c41d81013030300c010704501070001d03854090350420780421a00a010b4001e55413100058000c030034010b040c400103140c030346503d102143c0039008030050035220b402c06008140c4c4498000083d035841102e9440351042d8141c1b60036803400d00300e58400c00b01c20110710080c0481d0003107008030010300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 544870422 1250 544869172 544869181
    0x140103030f0c0308041502041d0601090e0114040b150a08100b07050d0f0519080f1014120f0d020f010608011e1a0901170f0303060d12111005 62
    0xe0030403411201120910802c4101c540010343c0c0003030216031069000041d915025140d0f030080029015075040b154945a101410724000c05e441d4010f03074494030099a5a1020550b607140f00c0311440f20038080d8001020308901c2c03150440c06c05802002d40c00c400548046c3c8503200030f448008003904445825000103180c8410700c204540e0307560f200005002c00d110304030f180c00019508c141c0d407400c4200c0350354144600f0300b849030901800740c810360f17543c5901540361061400343c8450040000b01e0131241001124407000200b54401c80c18011030096961140350641c0c1c1c055a80b041014bc0f00f80341000d5251446410700c0051502c005000e80b01c0003140d41e80040c81f0351400240c05d1825584c49401040950b8900541d040710811100903000c4202080f58000038211034110540802140d2341e020260080b500318000104018040500d103a9450250143d844030b00c49031001a80300e1100395030103035001c0d200e1180080031900c500f548132103480c00c0d41400ea20020400400310708104c3c0c021448403ca40c0e446c2d0411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 544871672 1250 544870422 544870427
    0xa060f0f0b061315020a0c0303050c06091b0607170d0504120e093d05180103051e0a0b090114010501081902030c040801150501020c09100b07030504050414010303 71
    0x404400400c44001d41041c4206020041c200010b20424000121000341c242e01d0302d009020550700306d03800c50044054103480b4103000e00550b2201c0c0b00c841c494400c0c14001070301c422020443d0328901080c40038210184c01440100507503070300b00c0d901c2600c80c10350f400c02c02250034010f03900404000c3d03a01040402c1900d02824030900c0d00e441c189160051052240e561104e607500d4050243e0b0110a441c50345030060a060085401404000329584520302b0b502048041c106a0903410303c2203910454207515400b03000402e002176500207100c0140160b10082904845891044134445220468011501d9003074258440d00810401034800746520703551007062414000e145c803100d074007510007800d0a05140c00d0a850305241000480303c3c18000507400300c0801d0035681a81e044070020040d80000344140c202010f41480854100d21070240540b00b2000724081c03d081c10020a4414244403c03500c07415031520207000460761240c034085041280400c004562552940710700c00c80d10085182820b925811480c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 544872922 1250 544871672 544871681
    0x80105120c010f050d021308250504020309030c150601030b1002060703050601110a031808010b0d08070201020a06110304050c0402160f0c1a0a0806010503010f0302120a060f0f 77
    0x103009a0122803120522903000900c584940ca007840c011811041d0300c28111158060200c00d505094000244550080f014040e1403060703515210a5400d03403806441e019203400350b500c0d900f0756541860768041002c5d207015406554465801410360b89800a00b422180c01d0210344048040e104083c01c050240a50303152081200144c42641e00f2141d0f00c00740b1038003940d03c81d00100b00c9400c054503200090480e9214105c0040e074240304000700c400c013a0b8945800f83c0314005400c510074140c107012900144000f4140a481c8100744081c0c483d48043c3d055071241e00240d0311030401a4154030807000080c00080c428880d29800007030703a02c0200c1d201d00b0300e49007172424a070206010034441d0b401882400c070314420004c20317400b0407948081c01e0115000b161900c0044030b80541c0c81401185040c100505c0f40c01d1611000b00f07018011540c8940440c0d82d02c03030066680c1c5c0400e00446001e01e40d400018401820000180303014800040d0071103629406030341c1d070181910380940c16212156150302c0c0400040500707000307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 544874172 1250 544872922 544872929
    0x150405091006090c05040b0d0b1903020411070308070c06061e0501120c08011e0305010f0e1e06040b0c160c08240a0c050c100209010905030d0207090b0103180b04030801 74
    0x50520100d84080801009806140034241803600d000488060034400390713104050350003000c0d108041703030ad02c011081141e50b5003a100a0340210b0030f141e51803c9030300ca4001240e0240c1c0d0305880c1c0600c562a286c0301200c0101501c0e00c101c075009c0c1e80d0305010400b080044003401c1d44012400c6402452801c000006004246c03100c24080c01504060800c80003a4100924a05480d200720003000c0007140b92107119200d04142d840600f0551030065a1010320103da080100d01050100880761074402d100c80c0d50210401201c082d4600f60010302c0820005103a5807803254205140d26016400c3c0074030710703030710140c25408880f08940141da010020010320201303121301c5100400a0005d8501a2144214804413280c01480c001045950b04c815011081c0100141d0351608000c104440d81294001e81c070000940c451401c240c003013010680f002860f8a0700240d4181800200d60250003034901d04000600070388415140c1c1c5041c103889102000c07845404c01e090524060141680d03d0207402c140c04c020b408000180c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 544875422 1250 544874172 544874189
    0x50a030e06130506030606130e0403110f0307020402030a1b020a020a08193903170304020619030b0d050105010e0711070b0706060902040902070605160e09150405091006 74
    0xc4a841d412407060b4104503039050310240c1e940e40d59400020041e00c01ca40980c00305046c1d045010030301085510205100e184030303440340b88140394007109281c1d503440c40345028100c5a2003007040400605103034000c1c41d007040c840e10012416003188400c500d40c000344404544010707400540783e5425843d0192464008040040181c001d040c0100390b030044407040c2c5600541090b40e001c100080d41e1201181804000b007400200e20b00c0e0041249035601c906100b8803007600c40c03248205014102d1b6925004881c01694000c28242ca403650303104503000821403000310078040c07541d50b05c50b003207072521001c204460344c2c0d1064000049560500f44d0402c010900542501d08100e952024416140d40c001680f1007640d0b45501c02948401044c980320000c1c00c0c1c2c6400a1800d40d0020600052007600c41e0007500626210b9501841145e440c0300642298250074400c84000620b01c02018540b41400c510603900001c0d1808590386014100000c2026a0402d40e41c004003544204140705d090225485034070007401000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 544876672 1250 544875422 544875427
    0x11040308030112030230070516121205121f030203190204141e1b070f2001080606091309050304030302210315030c030d030204090c05130e090f0a050a030e06 69
    0x141b920040404001d65604031040c00107020700c00d1002c00c200c3c0130201310182000e6a600d54441c442c1004d410356802c0100d030034010b16501603000c58081c0d802c0d00c0b40340d01070389525a615a1420200c3c83d0b445650307080c0c491034404c201ca0110140e2014001030340b8001c1d5020003820421420300c1030200325803155981055020000007401490802c40e40b000340f0f40c51018000307a0b107540390180344e8020f8000740c0111503031407100021100304100c41c5103501984c02d4000c000b5540740e903244030000013482c00c070544001c0c00282110300180562400a01400000780080c1c42401c0114004a00f00111030140754191004e9001140400070140e0403c081a8040b0184000000c0c4550079007c00a480c000a41254038052020320705481c9510100a181200c0d54020121001c003105c440d0041c0080d0300a0080808442c00d03d404c402c034250240080f00c403054203282d248007004d4a4a58002d007002d5015140101ca40030b891904070b885c0707508012481540740218085c014101c4240790141004180a085d1402042c09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 544877922 1250 544876672 544876723
    0x19030b0606031e16030617070b0a050906041d070f0e012a0c0e13050a06091a011508010e190e0c040c02101a13110403080301120302 58
    0x160441240c02010030399015072a0340726207159411040c44241c0310300141c5207407020406000d00442c0c40740c103411000d460400c000c64a4481c4101c0001041520100c1940603910401c14190240c00030030000a80d464510b04264180300041d086500a60107a0005035201c025901c1c8460f44070502604035a031401c05040009c410721019104d0200b240b111414000b8240b090303136018036035500c045540281e0450990b8600042e1420302e40c6500075000300c10701c1640010004c0e103858810954580301a401600900440d400b551f00d80e0042d00d10f0200885014059115103256030141d501c049020380007668001c5094400c5e0300c0b00078070008050380204200e424240900060103031151006038840c1700424046881071140102e11300e0001c0111909070090304e84125008000d80c08201e10107000503111050110040c0c08081c0c02203060130408041e0300c4070b0b00343c0c0070b2000060140d1010080c04440c20400e03041503925120b49445030401d901410768082d41d800c80208065040c4810104c140c40044c0d0300321036100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 544879172 1250 544877922 544877933
    0xa080106031e11041e0b041109190b0a0207080105060102011e1508190b0603060f0711011503080d0c090b0d0f0f0608072903060d11030604030302091903 67
    0x824503441060103407042d940d002840f0305240c1090103480c02400a01860789054454003440c0c0c2c505242c142054030b8500600051314041c02004001c00e131924003542000e40310020030a0380111128a02465401da1030300040c41d00000001e031000d502d46801402440e407030802d2460039907000600290459140c8030b008a0303001c503201850002100f0034080003995101250b108006500700743c003e40f000d44070385419084421803d494003864640b06400d000340584400e021302da910350007952f000400c1c40c0b00500141602e44035000481c950b011705030004c030f0714403517062011010004503003081e1390811000444001c803d0190041c41c2d00681680b4015501c90310300b84e042400c0740100e00907180740c140c540c0b891400136081c5402c20004442800410440156540d21095591101c1c4c483d1490303802c0088042e00005060011201100c3e01004909266070303200d808101202405100c1103c0050303a034121901c180d1000c00030148102d109450040e5110f21150802804101e800c003030088101c2000b105000040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 544880422 1250 544879172 544879193
    0xc030609010e100903020309041a0406060201022502011b06150e0603070b0918101502030307020304090903050f0c0d0305100602150406091401050105010e0406050f010e04020c01021303020a08010603 87
    0xc1d6080000030313122541d480d040303080d80702d640f6040340d106003045080102140900152100c0b5041100d04011032036030360605909038090380c51078074914255840c2000b2045034008007120b56610502d030000503110140c0180c8410400801d05440c05c2d56034002201c0a500000400c0000e003888c1c05030f58000c3c4ca0200300290380d402c041d00406008000220f00900c0a48501056403248440500c101502c0d1a101c801d07420030700014800c1e261050300b40003045189078004011039000340400d40c0039515150410340810003801c201c000031010840104218040141100040c210b41d402c510301404100c03c24500080645c0c10140400d110482e10050810495800040e6080700b01c01a015a00f003a0b034482c1841c900030300d88050060324009414018000b500019030056050f541d00340c0300d441030b280800e42440304603603880c0181030b00141031040e828029801259002c00c40c2900400152801d00039a021a082ea089420f46c40080030f6101c1e0203008618120040300081c021030b5008020003032031a142c043c0c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 544881672 1250 544880422 544880443
    0x91a161b022101060914460203040609030f02031908100b070309030303150b07020103020c0f0f010b0906190b18090c0a030e0a0309050f01030204050904050c030609010e 74
    0x10140725500240d12107980200da0510b9281c4002001141e03514403844016042615080c04000804000a185a02c00c2440680c80e201d1008200070072500c0c1000f0081e07409512459030300244000c10012000e00340703500007180705511030742d000b00710107441d460007801022442d10035405640050084240707425090881c00381d8282945000c02c480c1c1c071011810305199425070030000020600044c00c4040c5604440c0a80407280700766000c0006039214080c0d50700c0300c0d815000c1c0c402034000c00c200e07010240d8880d801400443c82c41130195001c940c14076005518003c6c0340d80e002a0541d4590403d42c50030324000d0000341d40420290f84840da8144403082d80c203a009030358040c1c0919a000840c43d038030b0f85d4030541c0654401400140402d14613040030740c0241020b4005c8003060700003070f04000107a000c9000100f030001d007071580f6407240000c1c03a080100700301003903002031070ba2410190700b803100041550360491100d0085010b500a030000c403441805160034008010514000ea81c1884600c00f200d020010300038480 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 544882922 1250 544881672 544881679
    0x160503070c0c0503030f120901110703030c170a052211090405120a0503101202011e05070503040308311401031b0e030c0a050d080904091a161b02 64
    0x40d16002d1924003001d040981019825200108000c004040340100410941d114008030800d2a80d030f02d00201c0c00c0c1e46035130a140c100c209060088100003406038101d010022081c0c140f880c20714084142603654844100c48190319691500140816010b0b0884103801c20300c80c0c0356050b1008135040d00d5401d03240e02d00f504410b00603542a07000500380002800000c8911491060702940d17004541801030031a001511085a99802e121000580141c811200c460080e81a1542c40c820410010610206046038a1400034000100017000000b0320a0008002070b522601c0b5644d01c0c1c100300044092108908210f4000c5094110112034620880221490480d909890400c414010b8000128040c12031004940250740ca503101540e24190403c00c00c06420a007034046a112407816010040d000c00288502d5401c9030a8034240c0c40825500001400c00080c0034001088400f170a5895440301a2002054130355511484144048200f0030031005540d50710502d004d40180d5404080881440c0414100921 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 544884172 1250 544882922 544882937
    0xd030506011d09070519030912171512010e030c070f0803030a0c0c0b0403170903031501050c0f06010f0f0515040b0307030b091f150e010c0602070c090f0516050307 72
    0x101c0d1840385c411520a00708101402c2400802c0e01d8014024187c0c001040310105102c60f00201003074400c00d140e0680783c039802011101c030b4031140807003406903006007045504004076184424412300c0900078501c9060f01100150396510f003440d042030900d052034105841400380d03070008001081c07000050700c0d0400c3c0c03c1e010000f1b40b04035800080c0c0e00300c845a90000c10002010081100b032680103450b003034698800c038441c4409540c03a481c1468482c0300483d901200c41030b41c606030010951041014105201102c001c4600301d000c01681c140c034041c400d034400c40300020408001d2112a1a4200400c014101510005811418a0002003c074003c038083d5503041c19000c000103281c14071941100d010808050009c1916003040040503808000031000311020740d0760329100044030081885044040d200070760700d6000c80c4900500466044605100649046400703200c00000f04440320490402082c5a2000042c81c55030041d0f0142980c00042c400c0c03407031850b0085805401a0400e0840354018160700c1e1108 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 544885422 1250 544884172 544884181
    0xd0b04200a02030702041508010e0115140d02030a061d010905070320040906050108150f07050a0c050f03030a06140d020112090b150103050108070303140a110105090d030506011d09 79
    0x83c903502500101a500604121180d4401170404448000740e4040100030312010750803058007400c0c5e40c0f042c060507000144c1c0e0079081000a020b8105e005544200070400b07101341c0d1681d0002442c00e000d8507004e0b90300a58501e400700741019241514a010000d250090000070f0f800d0f220306441d07125500c00a0f0130349185202e034161201c0c21045080281c0e5000b4000c020b5200300e4101b0364000c01003405941500d02c90030101300910032581d801e05120351134100e0741c55025520b01d0011503158000c2c104400c103100e8800343c9040041c3c0c0c107000103981c100c240c000640d16441e100c035030030056400c181e11090700c42801444900301c41d02d03a061140186602800e06010421204000070000c10015901401d900030045c144681018040e0040c0c40000f401d0f40c0610859803983c06c0162074000b270303200040100e0080100b00d0b01300140000a484170541c10300308085080b540b68140d0b400e56008949102c8143c2004541210302c1c0e404d441100c3e0025021b10703000d070411012100200c0b400d007030100304500c6013070040f0005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 544886672 1250 544885422 544885427
    0x20307050f070309030605100e040611070c0824040b0a0905101802241b21070203010c0e0102070b0d060801060e2203051c0608120d0b04200a 62
    0x280c401d0701107200d0060ba508500c0c100105005000c1c00100d850340d0410700420f4000c19101c400000340c9180302443c1803070307480d981d640800502106901d00c40c031403001d07c05280807a140e40140801080b4176006403440841c6009a0f01c403020120040c03400102600b401d1201103510300c9210350b4040b0103072200041d8040e075810900e18040745101d894600509128010740c40000404646400324420f50705458210b010304002c00010300074520400203440300340720801c03d01c4032081e11414941002006c0e1440150800b0f40442c0c820001c00840340100c0f40041c01d00d0450500740309029004070039181410075010203000007500c0b802e04d84943c041c0c552010030103400340c140341d40c04100200180c4008000b440c1d905c001580c496942100c0c0840528681c0c4082184114004030041045a15036191440c11030700f5019100400912031702c03245402e03036420b000b1480d0102003240101c0d03126000141c0b91560032005440081d200c65140142c056810040c80d0030310521407030002c0c020f980245860f00c0d01c03480a800d08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 544887922 1250 544886672 544886677
    0x5090d110301020d06091505031903140304030c150911120312161404051507051f0b0a05031506010320070809090106020d171801020309100c18030602030705 69
    0x207506510000318040250079031342c000801c440d00044240300444c01203941c010b0000c842d11951341c05402c000000300519036154015500c1074440d0401c11701c52240084080c055400803201103001ca1003400e12071b001d10038083d686150202d0f003178509001342410741d40c0310140442200c0340180640ea64010342c5c1100007090082c3e07099140002c0f0111040c0c035000e4541c00980c003070240b08201241e00345030080402001b00c0308480a4031005032100542c120218086c02113a80200780a941078050b080382c2c44002402140d212039080d6000c1c50101c0c0f0040e40600f004000200c551040740310350710200300c42c4003012002c0030180c0e02001c00d0800190303145500d8020103954081d114002e0440b00005628030070000084080e0408010035198140c0d80c0c1e8071180140ea4074404050120003140803171807019070300c00010b022141c3c81603000c0f05030719050003000d2840e4203a0700b058800e9001ca40091118451012207071182003452980c03840c0c6811080e20900441e103141c8a14080540f100341c00000041c1c8a42c000e504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 544889172 1250 544887922 544887953
    0x240f07050102031f050a03050714010909090b06040f0c02060c0a0c0c060c05120301080a0f02121203060f04090312020d0b09180601083405041b0906080705090d 70
    0x35566480c080c003003142c807807030b02030407014013000c00f00300114941c01c0444550058981c08401894400d040c08000c90240c208060200e0422148900105101029006010181d07200344407043c8203041020402003a18602e10100358042e11704003000000300d40c0021034580080440058940d01c0c042d09408035034014500e20080c19410305d01b2000505141c0c080c60010001c0d000e5419220b00352415043d03038215100030b1040915591000c0c0381e04011620042d80d01020600c010000da000b03251030f10005013402003101d62244040740c0401042010b090200170b0440380803007110204201c1c180b0781e4010f449000890201c20745990702149182c02030000394000482c11200074541c1c00d40d40340c1b017a500315200702c1010140d40d01d0301a1200000390160001005080640b031003130300030091805511480001074640c003500c0c564080b032070310003d865180e038802c0c18224103081c00000d45e03501400501400e00710007a03118000b0070584004000c861030b03010f010741d82c1400d41100d424241c650b00c0d081241049105c4103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 544890422 1250 544889172 544889183
    0x312030a140c040e0c180603060d0b010f090e061b2d0334050c03040f060e030d08040c0909111e04061202090406150f03060501060e240f07 61
    0x5102c56021290040c100701c9042d0188100705954015826070a03008004040c001014040e070f007820b080c9490009107501910160180e1100300703450312071445450003a4402c1c600c1103c090800d00507460a03003d0b0b5880d940d100001442c09081007003000785403103c0100d41945c0a100400c451640d11a00c001c07000251b51206030036001ca11607001e540035158805c1c0ca05803410b480790714500c8101c41d43c105207031a0a11190b0345020f800708404034243d516900141c542121030100f0000410300001c40c200000180c566641d0340d000a4001106043c9003c2e81d00c030204c0f080c001a481004001140310070148151944610007290750381291074005007490310380d11501d600900205c154808400300400c0860326190844007071000342c2e03940b10345803c4d01e030b0186d4000c1c1d0000d1441b00020b0208442d42c10200b0b0003180c40c242808840e9503844013090f000b07040d030412100e558844c001000100d91000c0444480c1070201c903c0c0501c100080d40306503491502050b651106da2010600c40844010181611020394002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 544891672 1250 544890422 544890461
    0x32916140c010f0605091e07030e03070b0c1b07140112060e152412091905010e070f29040b040905010806090c030304030b060f042a0e0312030a 63
    0x80c000e1202030000742c040c46010f8000d0100043c040c50005003003816884024007e0f907299210004120302400d001c20802c0c0340d0740320802030340e00041c000c000703001d119012220707030541c07240c1284c0071500404c00c40503000748440e88070304014001005626011a510303002403c046100110b01c600250142c04180d100e82801c400d400100268260814030890303444c10f0403149903100c085450f200c07603900c000d04c0e0b11449507085c1c144001c01e648204805580d0304142d501d0202d44040c11030360800700200180d00404c0350311782d440c0e0b801c14181039003c01c515005481c3c1c1040b201c00c040e0901020107440da44000c24074101c0102e02d6003540816200720102c0e8081c00e42c403058076030344030b45071118100034040078402c03240c1030b200d0f02c8005400c00380d002c81c050b80c49680080c0654609841d60301d0307541007800040e0030300364094000784846a860ba00d502c11010225581d9400310000c2d01404c2020030f188000d02c00c0a024001c0d0880c031282990b03004102c91102d0303159a14019180d488041c50319005002000c584510820781 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 544892922 1250 544891672 544891691
    0x4081b1e03090a06121d0d0e1c0303050a0902091306060e010303050a030c1112040602070b0f1b0c10110d092409080118120c08040e040f0507032916140c01 68
    0x700c1e2503503076901f1a884109043c000300c0c2c107005400014030f044103101c418604401b00003034800d80003160803900c4844041612511900050000c010541c1c80301d03a10403a015a42c02000f009006aa0061409001203c01c80d891a10054014420003207914201580c0d050781c14140c42c001c42080180d05181000c46515050203a80019294064066000944201c400c00600c404c0c8040c101c0b074001e41c1950940d406c200d8520402e0514900d805140c0c1128016081400280d03150000314403202011540e40300c0790665404061424005c02c403c0000c2000b80b1140107001444501c5242d00c5504c5203101c2901c07a40765040000c071a11b00d10703500508029400c206103402000c448100b14611603000d2a0801002010100f00392683e4016120081c85240300317000401c0003503d081007455103d401402c000c0c0d03020341d2039555541011950f8004540c0c690041c9044a03906401c0c08902010a600c000c00100342d04000b501440c8a003000101c0f10100324580004580b0b8002a100b6100f020351801c001f0711182c0070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 544894172 1250 544892922 544892981
    0x309100903050a11061b1b060c0301030c061106060f15071b080a030c0b040c03140115080a0c03120513030308060102060a1e0504081b1e03090a0612 65
    0x14a08040001c40303141841c0141040418094044c18003030440b8200e42c105031505130103a030420608000d41f9104107412038020035040c003c00348141e4540d14050780d25030540c81c10031b0001031541c01c1001000442c0c0c0d41a50030074800985207400c1802110181501410000015042c03c1035200000100c1000704651003003000501291142c0a64039034103030417482e11002104d81d28850030300c01600240314641081d01040140407219006409113480002580d100c0d01c80e00410103944c2c01400c443c0c1c1d52500380c1c1e640320303c00c0c040c0c0b94090b25002000d08603111043c1c131030441c0c41c08180405071500008020743d0130094001c9088404a600f02601107890342d41e03a0502401180c001c60703000d0302501500000030f070200740c42d01c00c4c1d04041c0012915000303a11038031004c1300300420f002002244c0c864020014010702c0d00c254403082c290001c091000382150700c81407060a07003038078881500f400c0e103078010b00180410baa02c002c40c3c1002d036090380c50500c0c00c3d0050342400501070091007070b142418007040c201d483c0550b10b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 544895422 1250 544894172 544894177
    0x910050a0b070c06030902030a06020c12160218150f0406031211060105180118380f0f090912040f0303020c090c0a0c020f060c1e030703050d02030910090305 69
    0x5003d841c0503105690340d0b09017a4160390030300000035419009030b03205500041150b80134084c40b01843d0119002400051440c5425503c65228080881c0383c0000210440c6000c0d80d603111222a05544405039040405143c520710003e152242c1c4146004000c00d00e0f83d03110f5a000500654000d07111300d480058418001d0100c03208100c40f03403014015080007251074140340106521003407407150841951ba01c0c1004c2841240072400c0c160300c14544074221405440703401c0c540303586003074001c05087c1200e120b641c1c2e400080c206c00100c0c00d130003000e204028079110358514035200c1034030b101030700c0e4088540e83c0e811040f4100315002e40b00f810742030000700300840d00b200b40c00000030130340b84a6000c9981c4402104100220038004a401e120310800030024085400d106610028400e480600301d54945240e41c1d001564076003051a201e181540000305141e4000100d03298a0764104910000d1443d000064400800711310881d040c0291650300040841c841700c000b0400150b2400b821102006080c03007900c0c1c000c0c03041c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 544896672 1250 544895422 544895437
    0x60906210919020607060c0c1403030702100b060d0203420402090a030212070b04091416020a0f11040207030e010f020d0e0d0f05060f012603090910050a0b 68
    0x5100780c1e40c002690b0225040b40382900d907001025142402c02559901025081c007001000c08c000710151510300081c00900414120b11860002d1500e0346401c0030001e190900d40d4141100440c20003c4400d600d80b106011211005035403080940c0d641e60b803608561054104070b55803c0400c2110449070a00078203140d100c0200501040103904801c0142c040006038040c80004c17a03880002e1071800c2005250801c40e51500c1c0341c5140940d070902d47d884441c1021600b065200300070f065103800f45c3d0013580b101031400c00d0340107407441c018000c41489040700035610511460002d041c188a150300700144520001e0300d40e40d040f0010415980c0f603a140ca4000d14003d01141c26070302080c0ca1010401d047c9001041814404c4079a03518044080c1000d800c001442c504140c041c0e64480680e0b008001041050003818810350030000000b540d5454a140c00c45220840407a06a140103c82c4c0b0050310004040110b804d40202151081c0044c5c507030a400035805a082c0c0d00ca580d000d510300724002108900c6001500340c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 544897922 1250 544896672 544896691
    0x307050c01080a09151509021b0601050303040320030c1509010e09062407020306041b0504020f04060c15020a0903020414041e03090e040804090c0201150506090621 72
    0x141e0b2140c0c02c100f0300b695004d48008000d90038818404000d03610a0b840100c1c1c1c02c04003c0780402095072020f103241203078098020048488009100c50301c107030508220550041130160019032816107151950314000004103409540c0c1000c100f501c0410795030402c05038003158401410382d03113079086048100d00298807612080c0d0204444010f0071415280078200c240c890a005090790002d4030850426001c151804544c0c044202170610028000d07841c00c0012500c00c1c1d2181c490a40400d012503d0300380c0702d9800c0d6102034811401003011b00c13916141380054a08136542400c011120141524200000d5000007004400742c505c00310f04400e42d50740c017048900c11070703000b130f42c040085412400900380400401c49000e020340381c001d90807050019004070a0100c00d0702a01d84401c0e2141c8614000d08101400c0e24243c5036841d001c0f6040c080c610031882640c40c100203a000820942c1e240001c0c4101c00380c094400e140c0719510100d900b51035621040200ca01c1049100c58402801d04000b118511a04c415160000f5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 544899172 1250 544897922 544897937
    0x3090c0f0303030c0f02031b011d060117031602120a050a05030d0606181a0708040f030b0c12040308090a080d06060e0a0b0306040b130f09050f010b010c0f11030307050c01 75
    0x1e404d8001c107500c202c2c080b0554051b43c03400054140e00d458803040c450b40482e0941d40d506803800c200f05404c40d0f0222986204000e02944c0d4501301c0040541880300c4004200ba4008010020700b4540d881c1c41e41603a40d40c1a110303212a406082c4c03030b40c0c0c1044808000a8142e004da240c0c088208407001c401042413600681d400c100c00780d101d0070b0407a40d1003180c80c0348400c0c0c410064400e01c00750020081e0b00003194111465985801080d94583d90700d40c200b0351040d1800b9030500c00502c00c20600160080e405001c0100f1682819040e054201c41c215001e00040c00303001d00000400d001260500802d07007000d4109030700543c0d41340ea10345203a00405861107101d001658a000c11503040c030306440101d0440700110b1869045440b5041000002c1240d4594560300c00001100b1150100c914020071001980754400042d4450250a140e41000320580260b1000d924084409955a0300881c1d030401c103d4010700755a1503101180781034100030700b40100c002e43c0341c40045101001c2100004100800010aa84980 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 544900422 1250 544899172 544899191
    0x306150504140a110c0601230d1101030f02070809010809121b060112080d050a1b0203130b031e04081e1b0c0a060c031e050c01050907030803040b040303090c0f030303 73
    0x9154001e1031402c0d1740c15000700b0010810f109882c40606588109034a41340045881035000a0490b1748440f07007211800c401d811950841d40c2c040c440e0105010440a0652500d0700c42d0396170b8509489800d02240c1441044030104814400800001d62051705043e60f8a80e555402858080c0254140440354840d102d2040041a003151900d0201d80540d4410b0086081c110380403402c030003900c401019810203960b00d00015180a0321000480a4911147c0195a90300c6000910248030041c0d500aa4590301c0c0420500264901084841c00f0841806840f15040d8407940390810080c400c00b2540c00b401220b410710400d1b40c8580c0c2004221f800e0400c00c2032882513100109107a1074951514440f0380c4040c20003000c2008070b0044082084080c407900d8800030f29894074401801000e40b0620000015102103000d00e0641424415640c01031400720092403110b1a55551160a200c000c0000307200705800d41c049000c1602981100f1000ea03880018801d04030707221982110902e0032840b003640001e080000c42d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 544901672 1250 544900422 544900451
    0x804150c230c100b03211303030905011b0c12110405040305030117060103121121040602010e031306030b0303120702010b01170402101d0a150201110a090306150504140a 74
    0xb60138010b0b000d4007134200a01d0a40d40c01000300c40c080080201b02c802005442c403d00b4001000c01c0165210f52585c140039414440010312030380000c1921417400246e405401d020a1080c6a1007007111600300e0141400045840d01840d910b0203a0040c0b0781140c10b01c0207210400d81c001c000b45068500b0405042500e103416084981d95010a10000d4070100c03249005888551148034070300a030403010421070f41404421241800640d1a050b450514100040303424405aa420300406d8610200c1d40300031420010b90070008655a2002d104640901da902c000d071038080c2d1401d00a440b0482c80100c12a2428989000083d0181c28134004850004040110356114031910401d0280155005400b034000075450301c100340d40b07030300052140e02d402e0286008802c002c0e40d50b140c10403002d0990000d070b0210b030032f041c44800703429501455203624022109102c0360510543c00311007202202d42000012580c3c1c42810754407070314944981c02c03480d009800c01d104085101c042d402c8550103200d6410040001f40d00c0e00003003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 544902922 1250 544901672 544901681
    0x201050601080f01050904022209050c0409030e061303051b011206030b04030f020304050301090f1a010501141c14090f06070e0405041a04120f0804150c230c10 70
    0x2d00f46850a070014003040c1071000f902d55009101800705035110580003462100c440d02840c0040c0c00640f142d000c1c00411000740901c0880e61001c2e5014000000140e030b0180c0000e0143c07030b0560060f8000f04801058814604104004507009020380301104d800340000420b8240c80c1d081507010030708503900364000344018030480d8116908580c980f07a03540c030740da98200c820030300c95a5036500314401070001090503542842070b002150b1240d15030304c003485c13020301d000d54901415448502001d1500001000240d0f00010010b6002c84c1038003425584001c91001301144031a001e0031201709c180ba00c82c040c2c01861207590a01d016001d00381c01c49255004048500d65184400c44034240014400320318940142020340100790494421002d60712100408034020701646c504031400d45007511801c07000e5140c107410040f80201100e541c079102d515440e06032599003d0b10039103409a6101d0b07584a117000755091040c6888181200c1101058201002800f0407000036009540700c884039005043e0000103c140074800c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 544904172 1250 544902922 544902931
    0x10219020103051e070e090a14010b0c1006090204181e0e01020d0c051b0604050303010506032214120304020d08070510020f03160804020904200d050d020105060108 72
    0x6440604180540c01103001e0500604a0602890300320039080a0b101c200c034941d0311840c2c2581e100d2004102c400c00f0048282d401404041c1400d103802d07044480303000000030311381c1590184e0700d10f180d440351421159440e184400024404c46840c00e0310100b003401440e00107200701c0d0003030100c810710625680c4100040315805e0321000c0d413800c1c00040032414454950403079221409442d00060030419080c0686060304c2140c00309500040e00042e441500200e003401c0809400b05000040c0440d2502c0c0d61070715520301c01806124450307031002c0b0000e09010743e4848940301d40d219003078410624911078544030003426000b070900c40719405580c2d502c0350301c0c07201c1030180c0e407086400800400b840003840e01c403600f41e5803004a0640319403b62800c5007620440034002880200030110100d6928508580c00c1840c01c1c00a802c2e6200f0086400244805130396002441600540c22000400c2c1d80c0c0b0700200404801891040c00c00c1d00101d04041e184180300d0045140540b161042d00244016035a000045507118022907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 544905422 1250 544904172 544904203
    0xa0201052e050f01111b0103110301120b04111c02010306170303060f0a051905030d0302160b061f0302030a0c090f030b0402010201290a090b0f010c1b0b13050102 71
    0x70801c000d18a000c9041030644181810300c8103500309064281c41c01c00e044010240e0780d08441c40e42d40201540e05105170580d10703400341c40036419541841c80c0482c000062403000340003102d00d20007003014450a1031000608c407070300508c49032220300303151040c4629900d00c1000f0ba01180c9884000203102090031000109004c0c244040c51550361034900b0407054030061414950080480c44010031182c031000c4610701c81c546000c00c2a540907103800100740c9003484090f101d00c10540140031440c1d03180d0492551030b107040d51104140d10640c0d14900400c681b40f101c8066641c05001d410107190699030150f0003107000352900d070403d0103010303181c4405907003a01c6641300351803960703003030540400114a0082806402c984144004200c03860303000c012401120184150100880e111003001070145010400d0100801d100d541c02d01901719084001040003400f0f000039818401401c8526040212040000d042c451864260800035511003802e2403564100e840d000d03100c074a41440c04146503000061141035070081d02c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 544906672 1250 544905422 544905511
    0x901141305011a13090501081b010507030e061b100905010b09040809010f050c01020304030504140a0e130c030b0903030106141303170c1f1a1c0302120a020105 70
    0x240f140203c164410101c3d003841c0e80451002103202003490041030700a000c3c038402005c100301008040440028441c02c1d05042c0a001c00217500000c0d000311040042c10003c41d040360b162a0481079140903807510b51942c1340c0c140280014600c2c403c0895001c0b4100600480003003003814903030700901124040607240a002c0034020320a02241c0e610400407004004528640703d130819070811101d5007a40c105490440101c0e401080902c808202c0044031300504108a50392520070340b0b420740100322541c0182134418003d03100d8800b00e00741b024505183d070003107038040c00200b0750b440c0043e0a15140c0d0028010000025034040c2d101d8840ca60b850140d59010754200c0000364600c0c51569250060215042e84144014050200300c0c0920024000484c40031b126150390341c59401003030b507400f0403201807412042c0c030401d00c500d051007252180071565001e1010540f034024400c8060500381e02c1c5c0700c1403a44400700203000040340c03444175906411980c000c60f004403d03807030310399a01f19052031192420413001d001c0c1ea050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 544907922 1250 544906672 544906709
    0x409050325021c08070c081c0305131e0219030b0907030b13062a1101060b09042c07180c0c030c021906051e0c060103030c06020405090114130501 64
    0x240449a40c9103403081344c0c3c1c0e500d00b10303e07a82c49900c45407255000c4005600b144569008040480c00712004458035881c00704541d180112005070b092488000103840c42651842408038900d103070700ca1650064004128402900b134940300841c5509041c04111180d010000c08643c21000009001050365807183d0300c004103070b071002c415014441c02035a0903500c498480c2c1a403400b07503100c0b880300014000c0c56a045200314030b0360000581840042454140c0c9030b03140403020400203404105888215504039004642d0391462800c06902c01c02c401e07441d2920411110081d590300b01c0000d5204e044a05038101ca40e03c281a07441014101c0d44184070711004140d01c03c01c4140000d01c00d20304140c5961004210070000070241c1d0340030307403080036a4000301c01090300014011200c41002d00c5400d07040b00c0480c1d5852600c80d50f40306040c2c450b48184001010b0184003545441001410340584014240240c050415503a44d01543c0c80d03203034007413400980503c14903c40303a800640b40380135090581c1da0201311130202080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 544909172 1250 544907922 544907959
    0xe07061110051509070201020c010e0f10020d0219050d0501050102010b0105030a0b1203030703060e0115050a083301030f0621051603060504020102120415030218040905032502 77
    0x8020701451820041c3c003203031185641c60007003680c0100c00f40d50005071146000a8081d00b117401c554180c0029510905040c4110030340081d559440d0702c540c0c031300561643e10101c0c064004c1c0c0520482c4c0380801c14a49015550303181d00201a002e6041124024003559070703208016401c0703c2800c4c21040c000f840810006500c503400740c00004070340e000034040304561800b0715119411034009130b0b0404002500d41c81c0801c2051030700d20300075001d00341400260307280340c2220f600038007144600794010041c0000640000e204408244c1302102d810030b8401c0480e03030080d010408542e12441c10f08800c2c00302e0b2420004414105891280c64291381d001141c504420482201e0200c40c000d2580c0304079004e00c0b8030a880c081400001410600462182c80c000c40c01342018400a070030b03d0180040d80c4a410003e020400c85041280a0182188640d0030016510014034411900b6a030524040c103420900b041c0609040000010080800380055440181451488449964003981c1003902942c00003408140500c0350302c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 544910422 1250 544909172 544909181
    0x703050c2d120c0a03080c0d05040b0a1b050304030f0c09050603100b0f040e100b2e05070501021210050109060e060a05040315061a0726040b04090e07061110 69
    0x2a64081243c61018005000900080c440c0c0c108840103217021400788040301c1c00300221460364800e81403442c201400c150189000f401120f80e918104a020070311150170b50f000000c5034400c99004800d40c0d40d210f8890411201c2503090b84412603144160100010740e00d10310744600c0b401079000070040d1a00d1040258400050048900e0440d17000ca9000c1c1588015503451090590180800d0051301104450f05000411903840d201058002c003000c44d124103c109100304e4091803026900d031000c0c80350681c0003048030340e4094460003d042c0d6100203843c00306481000c1c00c0500c03070089102d01040b841d4a4030011540c101d070b640300d4040442c5118682d030b00640380c4040030700941340340382c40d00a040a41c0ca03250141401000400030003455681c1034140000c1c4840413008429108071134610386000d08a564408550401205d50491140c09120f02c011100d1132408807401801141e14007030f252602c4415500040c442c09601c0c0c441441840c0000414500a2810200121580d0013170302500603001c14110150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 544911672 1250 544910422 544910449
    0xa0c02010b0301020706090c050d03080406020d06180b0a0f080307031b0512030a050f040f060e01091b14030d051b030f030f041a04020307060e120703050c2d 69
    0x1035480c1c8005814a450910203404454043c050114074030300f040c20910762174070484d04220301130f20300d0700d030560040f80d080b06044d500668000f80042c0da4191480350790004000f150005040420b070030945481f2150a50000b4030094400c0f42c0e100742682c0e4400e0804140b9000e4862031440b904148072031800300e4050141444100580561080c1500466407910300700f00521185a4810754080706014150b0000e106041e4001001412680e044c240741e00d40085441084c80d0003040c40340c44110310840c440082d08000c06d150752141c0c815907540900744e020031650001d03004501e4115040058031045140c0041c03080340d9543c0c1c1e600c07245d103071684d920010141c40e00409000aa2484104500601c0c1c0424200540c4250030001c0c0c071084038207003464007078a00e155000440d030828941c00c007880056a804200c0c842120140d040c40c00c0b81c030b400d06010070340c2500070000d5130183e40100140082402000b046601071000e0850784004401180d058001d00c42c1c1c0c4016661030307464920031350b800d09070501c0d01004448 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 544912922 1250 544911672 544911677
    0x1a03100c14030108060403020601090b0607020d1a0c0319020708040303080705160c0e010501020f100507090e091b0108150913080310080d1d0f0a0b0d090c1403060a0c 73
    0x4204201c0507890540c1e00c2a03101c2d030915408601000241a17050100a000d0801e058050151b1440040003451500030850040d10a6440000d8282003203210851601c29080b809100e003c6882c1203610501c207604122100c030500600440b913422111168406c880921f64040012420641140c80407031700c0090003000c070310600030304220010500c0100c1c000750800f00e21407404c40042c503051112103142e540e0103a0007181507520203440c2008081001c2100b450f400000d04000545035981c0300c04580c41031941d8000b548004010301801507207240803a5140c0154040681603102084000046459403030403688118010b0701d0040381544d0b80b901b5842d81d50800c2000c15400e200c807c890b2511a41c0c1d50044d40d00303154040b40200302300007444050108503070015041c00d0900a41a2030350340d034594005401680c9114001c03031080a58156109a41c290182008401654a4911552180b001441e40040503075011060000c00290640103c43c1c48900030300140151071207071038800401c409800091841003d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 544914172 1250 544912922 544912937
    0x4020103060b070629031015120804091a18060411040e10090c0909090f05010c1211030403140c2b08010b0a1b03050705010207060902041a03100c 64
    0x11000e0ba4003003d400f08070302030400054074051000010905080030301920568007040c040c0311016a5000c034190f5250f4102d072101055241403460303981d11811040e080007107010a504c0c91202401900380c0504251216a0030402c98a03400c108200c41140b4021400c5910423030724500b10510094242c102a00f1020240010840e085688400c1c040c2d070b0010b8110088110f90601002203130b80d02c0315070480080010f60010810b1002c07000005054050034000c600e091511000060b080111359650381d40c15940000c000c114501c180c030001003942240c41c2c074901c115400c015421040e0342c0c50204581c0200d605448802e031803a0704e14039600c0e080c0c200368540c94860184480d0032183c0c450181c0e0f00780c0c001c0e000c58140450a1006c540c080c1240c0700682000b8040070003030044c031550070713084103007481141e0700008480c20041071403030101c44a04c00e103c4000d02075400031a000080105940203501042c2c422901446502c01c0f02040c0000e2480f417655140e07050b03001e440341c20114081136100801c3c0389240e2030800c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 544915422 1250 544914172 544914179
    0x31b0c0603040803040b150f0120010c0513090c0c020d030e0d0b06190311010e0303070507061e080603070545060d03090302060a030204090f240506030109050402010306 74
    0x30201c1c0c0046030b06450b01c603000010003040185000c62036501007112000c5170618000f00c800306654802e041c0c1007034181315081d00d00120800300d1680c010151b5001000a0007000b494110061654104c0041080d4003640540003107a884942d001e040c0d40c0d46095901c80d80001416020004050102e0303d060f030501070030080f662015250140e0200109008010b55801410110305021868514210546540c0390341c81050002550160f0b25000840003445c0c452449003003900041d0a51007003450051052180d041d00240b490340103e000c0050460060b5080341c01da101c20700581310680110380e469416002681c0c1801207181c080c001d84051010a880e400c0e03d41c512050b00316120001548407401540192241426940e20034000c3e603220409442581d80b5000c181d80141c00308003e8040248601000b20b26009075070711aa06a40041c903041c1e03014820300030000605402408100820070f65034036030b014411050444031021008841c00600010700d1a8a040c8c0c4401c002c140c080c0080b8101511b480002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 544916672 1250 544915422 544915429
    0x10f05030403050a0e062d04080717160e04050706170a1a220608160b0a020a0204061d0c030c0706091121010b04050c160f080406090603110408031b0c 66
    0x107140c1d0761601000303048900140030700030030b900c50740143c035010041f01084280182c91000c41c109048860780070454808040d80c1c00902c1c107001d07030300d544452008a03072800018070105c142c4089010324012410368005a071030390000c071515003491402d254140f502c40c020800b070344040c2d4000000500d40206804015001200280100981625400c41906117072141d06000581c2d11641d4000c05c0081e00070015440f00110001880704d140c030614402e6240418130707203030240c024803030281c0071640200100540f6031507601010f440040e01541e5080703880da900001c2c0300840c0d00c0c0d0459000d1001a10242e00300a4540d58000262880040072078095a85c0804805552125a50703041000c41600c581001003111503000c500b1600d00065584c400c6003010f0500c0031007182401150247d5640300c0c2898115115030404400c10300d00740000520007440024001640381e80000b401096541c01d0360244050380344081c440343d080c007071030080d03031400c0e0010405c200e0704440e165540c0424030228000d4031443c03403201e40007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 544917922 1250 544916672 544916677
    0x406180e0907050a1707030318120f0b070f08150102120d20030103020f01050d090c030605060102010605010809060c31030c09090c0b0a02010609020f0a030506010f05030403050a0e06 80
    0x402001d03801410244040d01d03006521201424685c81c6028840d806a409241c1d10b1166120280910540126401e61450140c0701007000c1c12010b8401203404800d4500344030304000703903482561504a0760001c2401c5d1840388104841d428000d5907503000e140c54184030003200d80a52840c250540c8074a1030345030920560700003c1d065205019100007140060041c280a420b0b20700041108070780c400300010300040c0d407101d0b42d05004500a02e44183c69000c01044807000b4201e800c4040c00100c66010004100585500414030845013a8002e01089070380344015110302c82c080d64604d80540000000920f0400c001c000b070b1085480004d031a40129110486880030010580733009200e0442400d8140207106203000c800713006081c580005c200e840f038561102400c22055005080500600050340c60b1a14401d421150140190810031566440450700c1107003d0707400300c0e40d0b10022a040034006101d80d802904c074800b45201a448092456443c0e950440781a8006000304003880b456901901d10f03a20350001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 544919172 1250 544917922 544917931
    0x1140304021005160501060906140901060233092b0e100203090a082505010e01230a08012402030a110a0f030206180d020309090615070c0303120b060406180e 69
    0xc1d1850618660042061501140c2b90140c40704000400c0310341d40c0001c801c3c02d090340c50b40c0000d611003c0039040c03162000300550080007a85440f0140040448040392051040c20341c5d10240b451000c903500d20018010985e84041d01007508144805518180511074040006051046e246411071800004503c00e005d5006000300b075100660714504d0207104880d2102c500031490711003031054601030000309012031000c1030718100301d01c4225944030603140450000010039070b100c1c0c107503c071404901d004000e41024850030000c8040c0010070207010780300245100503188160302842c5048045041624901008060700700c40c2c2c892301007450081262110b03204000e41c400d6001e400142450507424014000580303200085070890001080c0654002088030f2200708255401d18a6a55401c00902e1804415003040504600080d07040200054080e207141541d21175290301c526100d55070f8000c030440328070320355203600413408200c203119003030180c0e045083d2041d40c050182c0c0656191032051220010544 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 544920422 1250 544919172 544919189
    0xf040303020c03150712140a09030e060711060c07050901060c23031608040b0708190201020405060301051507050a0309140111060a020f040b04080c0114030402100516050106 76
    0x505104059060000c40307070a00d01107008180329042e0800081d800c01c0302074102014001001032181c0060410340141d050400482070301d500c64900030107800080e200c5060300300d000a2501c07040c10301d84d141ca1313000e542c85907030000742d81510500341d0000c0c44003941c000c1041d40382d503200300b0200040b02c0e60394400c0140a01290b6407000e40d40516407429000400000903001c21442040030503941c40c00c0000241e4100c015003030307811552081c050410309000d00c9560080344000f4000900e04c814020600c2c0100443d00d0898110400c05502c2c1200701e00301d0040d0300075a9841242040100040d280c004180080100d511030309a10348070b4550b6070b4130302d019500801280864843e000420010300c0300c240c060b164907000c2c200040c8040c0100001603c810000341811991039000c02c60942290410050320084c004c0d05862a60300c58441a139950340380701000307400e80020490480f012a1124110940340641e90180c0101e4100542c0101504d40341c204030207581e0480f50340f40c076074030109030700f409000001c16041c3c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 544921672 1250 544920422 544920427
    0x120f0602031021020d1539020f0a03120e0d080f010902090105120702120403050f011515120b0411090a141305040c0902030115030c020c061e0403080f 66
    0x20341c0c580362400280c061840308500c03e00000700503856601d07104555a6120300c811141090702c0e0b07001e1008180203100c1452903400e919041040e0305403007013622a80354110f0f1190240140c5648201d90703d04484d000605140c0040f0600c00000b8000c02c4441403003031078040c0104000402400091030100c04d608003034005000389040c00f04130f4500ca4242409000810400d40ca80f03001c1d580043d18522400c1140340441041500041c01d07644284003400c00c1e205803201140e96107070b40342065a562910200140410351904007404020440714040200325104000c100203507903103240e010345510148021000c09140c070f9184001d0340ba600d80c85090b50904483c0e910315120304514050041110440d00315043c102c07480710300703241240c0d07074009010b2a03607000c1400802c15a407903290069000c6002c1d8082401c0078004030000c101004070b51003070b042c090102e40d000c010a02c0800000c076580c0d440d04d03e1003070f009542004080c80c1810064880380414594910f003602c2d0030790703945d510b03225644907840b20007138803102 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 544922922 1250 544921672 544921679
    0x1a090604170a060b0102010e1207080705010207080705010b0d02132307021506100c0f030507170304050f060c1e07020307080f1e030406050313060c08091213120f06020310 75
    0x920030003413600428402005034141e0808030716643e0290194404110030007003200703001c002d4590700310f52560303600c40029500c2e1030b02d81c41c01c50b00c20f03009148200c8040d406c007001c03480b02d0f081c0300310840c1f0704c00d40080120501088a900ea07000402c016100c8040606030520b460250811001e0710034000c1c1c0031540142020880031002100191002d019148221401c0f40d50001c0076070710503413506405803ca206100410020729090b41d0b24403c03400700070500e0b0024000b50480c018120040c5100764041c1d420398480c640860010390300c3c4c0e04101c40340460701c44144504550409106205c00d40348032003a0f001031820000341c00013460180194000c1d001c5038408042007412041c00d020040102ca203064500380900414241c0c29100d024500a05040120210006038000c0350302c04241109900031104110755011000000c0c050f2030110351070003240c4240c182010f5520000d104642032542c0800007101c0c02420701e5084080444184401d072040402d142815010410314401140038200042010016030319 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 544924172 1250 544922922 544922933
    0x4110a14040506090126010308090901060f120f14040c060e01090b04060c030c021807090b121303020c180f010f15120e0f07090509071a090604170a 65
    0xc454103450441030003880104071a80743c4806482d01690242000c2080040748090200b03e400202c101068668804000005000c88031000b440c010b001910070512581e00d401064400c4500c0b542c035000014041c201c2d4080c10507060341b008150152202c0b001c1488000300250407401c000a071410762300800d9031041000516004085800d2508003801c01d20030141c506031284d05540924443d5905020100544004042c840d8a50074040c590052004040d10025240c0d089421022034010700032803000c91001c90b881c2100010b0340c0303800010141c012819034980840b504190034951040301584564007900c4403a40d41e280642c040c0c510040900703011440e010090300b180040680c005a540b01e100c403824000c540c0b00b04500380303011002d41420900708a000c1103004c014004024050712034002c5441c420706040f03000c6a1072084407000b04040c0f0803600d84c000010b480300c040b03104440302c7c0820040768031031541c4800b000d4110404014101da0800b035039031841800307001401401c030000341c2000591034100300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 544925422 1250 544924172 544924187
    0xc08011109040b0f0108190b090c07030305070912060b0d140321100306021810090e01090203100302100e030d081611030a21090b0709120206030109180204110a 70
    0x52040b90190900131150001034950f180240c01000100400d01c14860403081940001c002078001030004206803914000d40f13411130300301000c01c800280c141000300384021f100e134040000340d40c61140c55000128043d642e6000034807210080c50b40210013480614081240030541007034000b0808082e56882d02140d00c59107600c40010002e19019152074184000c1d202c152070f040c0152a402200160703201d600d180308165082140740c07115070145040720240c00c040d0b0700c41c25a100f01c3c3c10911a03540c55036201d000c801c003a070104903000d1310a002250020005840c20b150101c803148600c0c00c0c02c0d240f100c0740f01d0110341400d85441003800402d000c0030500c441420681c504061003085445c1c03041000e002c144c0203d85034415800404100114030030807030109140c0c1019011050402a0300b00003c26040c6480c804500c1c08840002c0410030183c00000c8944040f04c24101c1e2039802808245107a0034200038200622318005505041102c686000c0f005860f548160018070004d46122030315031448a41c01803110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 544926672 1250 544925422 544925441
    0x1505120109020f18030a050703060615230a1724120c0906010207080a0507050109150801210f0302010b0411070f0807210801090f02040b090d0c0801110904 68
    0x107510401c1491030b03601c41c0c8030039035034502c0180d005210b0060700c100020b03103401013005016040d80180c490010800085c1c0e8407800441c0d407145180045141001750560b03808600c4051105a8000000c0c0505100103010040c81503040c54103184001c0d00c41303041c1420200c0411910101d07907102c4116000c41c6a1070340340c15000d40440c211400800241e04000f85c54aa12641c1031082c0240b0100707010964903030003841048054403804040360000c1c00681496030f43d500c1240f08050100e01d00070404200203004208200d408886503c1d05a681c1c4d1905034854a0303414012413941004540740070707000000302c0030240906400e000c0d5001049110090301007100f10b0310310042019040c07a040000000041041c0b0003506c54640084000341c03038110b01d0815103840d02c1c00b00ca44848030300c000034030410026003008026058503c0b28004100c100e0074000000301328442c40c004d001504200b13200b94805882c0039402104024802c0b010106505d5071a2a40b509540300000300340303090f060103d820f078124203241c85103a001c07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 544927922 1250 544926672 544926689
    0xf210203091c030c02041505030109210908061801181218050d06421a09040c090306060909210503040210030204030b0705040302030d0305090606010507020a15051201 73
    0x82c103410755800b400e41c007500800240500c0d1070f03042c7c940c800c501e4030360303220014000540280030440712498040f15000f0240400c0380301c104811112018907100342856010f80300204014071558540c181c074000400d11646c051800e5640340e40d4000510140c0310686c81c8400d00c103c180001003840001c0180c00c040080013440201c444402d02082103944600154140c9600440001030071940c0c450b008945140490344405881000c810981e100440340818030940103c0f001903580c002d4589101d88024030000da0041440002800503128601d03043e4003400804125040c1070b4840d035607070350b80ea200b80d076015403182543c580e0b1150007078144540fa1030f5500c4601030400c021030032004400400b0307103a404043c20107405040658070500e4040d000380e04640241d0380000842200b4074040100420365800740c00200c0c0a4080c401511410078041e004890086c04074170060121503a40302c004440c244c0000c40c0580e800031100c1c070300052140c01e090080440800d00d54a00d035a410300e042050006503010390240a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 544929172 1250 544927922 544927969
    0xb09060f040c0b090303040302041506080c03060109050111030d0c110d03020903030301060503180106080c10110604080f0f0c010e0715090e0402060702040e06060306010602070e01030f21020309 85
    0x82e4040c0080025192507a070b09a45032020400407070b2642c0125080250414581040f50900c0c2092924440450307409a640040719130750542c1071401c80c00192605408200810000e000c41e60050601c000045105402c60f81030500400c403030403d0b240b0b507203c2003003c100c104131400401d840034064181c05042500b415850303c1081c80200c0ea503480148140000c100002c404a40004c0c4082c00f07010090800800a000103078880484544a00c1d5007070709140b1480215000500701070181c03800015aa400b03202402850780d694a030001c0c0e43c0e00000c3c6400c5030160400824410540040140c6a5000c48100004644514040d414504030907034001c4075101600d4402d00701c1c030a23881425402a9401c200038405a40c42d5031011507594003540000a5001d0304100585d842380800241c406d10a031070803000c40e02c10b80d9846c0c6050361034281901484160903075200050000c20a01c00100540d07038454100c0e1884085950039501084900f0f00c080d01c0141c0000461403e0b91a082c0b21030b621086613440d0582 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 544930422 1250 544929172 544929181
    0x702090406180507093603120e1902030d080f160e060f030411060c0a02040509160303090e1e0a0b01022d12030f070c05190b09060f 58
    0x2510440000c2004000e00c0d140d12100b180c1080040301c0c420016031000132a5003040e150852200602081d04060302c44092150300c001d2800c2d42440345082c0d4125200c01e000c4289002d40702154010040d4007500030302d50715810001081c01c8100001901e41c05030301c0c4200f4140c040c510406041615031240c2da030400c0f8101d414890800c04004200f9001410406640c0a526100b0701c10b031b40100d1030010141d4406c5000c074000c0350060b03540d002144102d100d100d02c8c9102c0e101160400c50300d80503440880718654041d440c1d0400504159008640100b07003c0125260a2040c19007071464402c3c5030021030009050160812940904400d0782e03400049403001004428400010102007010061082070b445881d820400d900b64000e00004941c1d4100003d00b0b0701fa0540002d101c452105081c0c041c44044c800d541005d4890843e2800b40c03402a26044500f40d0305840b0507a00329038040c4c5400701500c16000318413400001c200407003488458188204100385a030f01d0281c0c1e1017414008000c0116840d94558070801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 544931672 1250 544930422 544930429
    0x3120f0402030c10020c18070f030c05220305060703240522020c010c052d0f03061804150605040e0a03051e0408030c010509070b07060b040f0507030506150702 70
    0x120250b01c0309444c400c11105200788124900071074a0380694000041030b4045611024030b00c1d0703030351040420303071503451020106210071001c44170b1049107440080d00610105d0022002c07003d2914461643c0341100c0d0b903541d00c0b61507050800109680480103e0b0f641d5015070b480f500340040c4144030030904400040e42e20715200200d00307282960465142450340040220761124a6036064400803202c0c0030007007040780800f200c0a0102e80c4980c6481803024003607680301d00301c1140e92020b02d04010b04100c2050821441980e01400c64102400d41e03030380600c5c50144041001c9014100d035216038065689140b080e1405403c1e0301c100c0300250803c40c02181088001c0e0b5000c10009803400010380e240c40d00c595204015260880b00101c88000c02c40700c3c0c040000d0001d00004000090040380d141c00008100c5900c0c2e400925a8034055449104903211041c0002404030b80310b54866414164058070120b5030740040c000c40c0c0c08580c1c00f03d40b100301190b81c0b0700a11000b030600918100110507840d0441d480c22030140c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 544932922 1250 544931672 544931683
    0x102130306060b07320307060e07050415050405071b050c01141602090a020d060b070b0702070f06030b1801060c0c0e241504060c15050106091404150803120f040203 72
    0x90703a11403070b590851541c5c4610182d0084102c0c2c60383c242625140ca0b03861400c1c001800008180c0340282c0314882010031213151070300c07555840720041141c21613031a103800148805400c00404000600481d4596403401c121070562444615100d040942421045c460000d08190840780070704034100703004d100401c0000b01e07090329882902c0d0101c8451000d03a03038580d4000301902c14007181c03070f400c1b5040217000100050500050240c0c9032180341d502035160743d250012aa1040b9500c91096070008050040240380c3c080d903c21820080040c01741d050a00756580346e210302800070b07400640040c060f000420140302034090b03000050106070f1a880c0c818284a00790054022000f0307042c44054190520903009962800d25008852000d900762a484035515440030305440c07030440050320b200c04080f582c80881100d078420181612041d8980c2020b550602200201000b101c043d0960440c0d920480b10700101e00b404c24060003040c00c54000e41d6201c50210030041c0801002e440d441007414101c02f8800165800701e203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 544934172 1250 544932922 544932953
    0x90624060301030b04170c0109030e031606050a090b18031c1d041812082809060b0310150506130306050603030d1803030c1b030503180102130306060b07 67
    0x989480e903888a040c4543d4004504409441020001980c60140303041900482708c058025216081c6c8240000185a102d14443c0c010200c1101e03000400c4c0b1409008002510400d40a0314150141a80300c0708003581e07d51117441c107100130b00b818591504d2b10b840c042111841c5500c0182000c151081c012002422009003811200344110303803031001440301d44032944000d03030104503540340944079619820203516600845000f803002071003500000f903211401d00c0e42c02032250318894010005880c80c4842078024603c1e44405c81e00141c0f1111026011394042100c210701c44d000c46000034404130280c0e2044000c819a40c40b050240d641440011420f403940caa58a00726038104001141391350311038001038214800c0d0104106c1c079624040810a0002c681810384411510030b031000c1200598102090f074241d0032000c19200b0094064111000291161001c3c4d500002c0000c00180c8010144081e54207903001140004150110034100704280a01c60240350014440ba100103481c104c000c0d04c801d20740d200c0401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 544935422 1250 544934172 544934183
    0x3080610030b03030708090420040b07030e040c0807030e0d020604080a1403010f15080c03060d052e050f011a160c08010b040b04020a02250305030309062406030103 72
    0x1440c0045010350011019584010300b81c03680d40201e031a020606400c01d1038002c0c000c52500c00c8a61407841c400d422030724001c4a007070032281003515026a80c881d40c1d0142404904004aa5a00f20516142d902443c0b012500e59210f0206a281080b001001c13242201041c40c00d99201d610f01d429401d4000c10001e80013600300f03030b540e640c40d440004181d5441030503a10b00070468a0000000079402110500b040c240c07100c1007103003d401c3d030185404981d403071425201e841600404101007030355860030484038840e0510134415500b8840310801c2c003d55621140d040c0c5030304807414091325258200c8c0c0b0702c00c540e400303003010103005410b50403d041e995110030481c10b12030000c0e000082c2c22081c0700000c6005940940d0010306001601d444906d02d5019001428442e801182400a428690f180c640241c1c0e0020b01142e0080c0080100c1020030175400c5064810001c1d04106d080c004804078000303000442c4503003034490061040f414007800840c1c01000c6410401039258103068424101d076925012641100e0304030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 544936672 1250 544935422 544935439
    0x180c020c09360609070f0902070c05130e1209190b0a050a02030904050a020c010e010902010e0f220e06101d0901180c1d060901062d0206160c030806 65
    0x892102011072414040c07940d20f1060004104180c00c002405200b59072401c41d10125556a0380b42050990061090003007910030780c26000d122909000c00380c3d00342007041a90124444194611440c1000c030750058401e04810009440001c50a041e1005400c0482810f5003903102494000b040c80c0034069903141000304000090903258aa100f0401c1d6100203500030010803150404c0d188940c025030100300105425420300c00030b0183d0740740c107104030110302d41c060b1110303117419500c101044201d1484149040d4003000c1c5d170a170b45c0c0c0c02083c400c800e000c000090030f01c00074a030b2445a20043c640b581c010314400c0c862000d56803d105080c2ca06081050351004118210350b1313615808041f501402e4003601a0342c404810b82c0c450400d0118651078039007100c04100c0321f13404020a0b90250700b2200400c4039280d4000c541d11004004040c442c0303c0040c41c0f41c2201030902400005080d60a25040c1441a54001a40100c05000c000c40c0f484c01c00384210000b50820404400403503a0103481080d000b80080e2255000c1e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 544937922 1250 544936672 544936741
    0x309060406110f0f030d05070302030720071a070b011703090607030306080a0c060e01050901020a0f030212040f03030e01030203040b041202030913061e050a03120306180c020c09 78
    0x403c500300c8030464000a07500e60318802c142032943d039004904164041420140451800c5d4080c2c0708890013540d040e42e904001000c9501210161040c61124611a22440c6000070b850000440543c60b4a45405e042c01c0d41c9480c00d04018801d520103070000003030240d01354014540f80398004200d907150103042d1003085c3c4944036802c0c01c1d4018400c82d4081900c6000300301c90101004103420010041c3c50194035206008030814004440314010305a046006d0707800704c5e4203480881c0c01c2030401c10340c4ea8031a1048036012042c1c2da64103102c540150307100300c0c001d011044042c0201038012240c903010100a01e4114103500d03140d02d44156400d030180018001c0307404240500c0e0781034400c1c4111006550050220781d8040300455070500180490301c01c1e141144003144032091804680c0714404100c0c1e0300184200703a51030443c2c5800510300680400c034070031325549040005030343d504249000b20190918000003001c1e8000d20020381010300d001450b0f413140c512541001b80c035007035200005018504078041034030403401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 544939172 1250 544937922 544937957
    0x10090806010603050603011407031b03050903121506130602120a05031602280c0b0901050708030c13060e310e0109060203040b10060c2003011d06010f080309060406 72
    0x6023000b030121002560802c1107120780d01a000403032820102c1d280e0b40c4100050000803400c0740e5054480c00c801d50003c0000c1c0c041d4007016040d02c1c0e001103c003840d10100828140004049500488006180341c00001d4100f01c143e80500c4405044907109246500c1c10003028001002d91100409600007034591004104003e4801c1101102c03002d4860114940482690552040c20b0110700003101d905280b9440420032240500035641000c00607166a400c08200f40d6400300c01c0d4100418560149105000b02c0481340b01c0c00c601c43d0010b00706600c98050716903408050040420041c201c1d01a00400749480003210f201440403001c6246820724001156443e03154642d026080781440901b10317034004410302043c8892900b07458040c040b1201c02040c05580e450040d1403052802c040a001c55080321181080803503001390800d80554010000101207039620201204600b8814a81a0b158008001070112109001c510710242c0143d10085041040581c00180e076885180220020072007501c030b001c44c8402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 544940422 1250 544939172 544939181
    0x507080a030221060a080c0319020d050607030f0605040912030b060403060f051e040b070e0f04050412030b0406030f20060c10110a3f09021009080601060305060301 72
    0xf9000c000040045680300010100603500755240380c03203000b41400010f2210000100000d60305000f6015120388030704030602d1514800c4183c01a604507400b01c2e02100060000c0c4003ca109075810340340010303c40741c00383c01107044642c1600064002c40c0f8140b4050003007a010001030750b81d0101c1c3d10300401d40720984c80200f880d6014903031000308140e040c005020400050364124603c10000d42c00305444001000c0215041e0f96010303140a0200c141c00c10109982c3c40c07298210f00d07903940e000342080040f01c00f0207000c20304941044a054941c6c61451461701071507a40341c0524045031204481c00c1c010704c2e0171038444005640e11140014904400c10703080e17591440c0603510440490b000180203949030000414007a0300e61000407141180c007840c1000241020740c2c101d06072a40314205940344600810040d540d00c03910389806e255990451401c44180300600035440180d0740000a50002107503911042c41403041d006c6807801008240012140c00340030244002803a18110307050b034070700442d19894010102c0e0050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 544941672 1250 544940422 544940437
    0xb040c0b0f04091b0c08090a03080d0e1507090608190c08070906090f03140f010f09020111060c0307121b080103020f040e0d0e040b030604030806120d0507080a0302 72
    0x100c0300890329494002400002d802143c00480007805941111210388058100125020300400d1050820b803010421074000342c00000c0019140040e1180c5a48403200359810241c0012500341d11250b504031a081c040c03190704151100c0b0071024a00341080900a000100a030103400c040211103000600160000443c903202d00c14405410001419907085c020403411003112200302043d144600020314510601c602003c0300c501c207100c101c0a030f0840d0b0f1307110640307040a50302445502c904200004121401e110351b03110040943c2c0c2c0020424034601c0090154102c00111103d550410070030800020418000c89500920302e1030100040a0202c1482008020100b410401c01541d498584812a00002030f14140c0340211041c201107140d003801c01c010748102e20210f2445401042d000355910303001d0f03109003000000051004c501c0300c1c00c80000c20300c1d00d041154190b001403a80020311140f0300744840c0d4250450800c001030260b60244000c050103d10442c18000d00303da400044949206202e0303419904403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 544942922 1250 544941672 544941689
    0xb030a1205090d1713170a080901030f14090d031505210102030f010e0c070c210501140a150f050f0105040e07020c03100606020709151d160804030c0b040c 68
    0x1038841105082500f6084070017002e0303099805e80808a001c503407080c0240708490442e4003c00500b480c990741e0640c6500050802d6041c10f07105c80101070104002e00030141b0991036031101910300d10b003140c400e0f032824051101c014140f40c98649900444c561080300001034034016101a4800c43c0c08404030001c002e00e503807081409502c0401400425131038505250704850006107125640e807501c81070203000d44903200300144802c403864010050150074200461803010b001c0050038071422075864041c01d6641c218880380c15500718104002d00c0d0811031248041d00d25804042000c0141400383d120442c5c170a0307001da180300307081e00c0c41050400e0b03200314126005000041d401c1c5503607040a08000c0d54912606c50610705c240a04c107640c0b031040c03016110740c500711540ca034000c0c09030350300d0b10342088020400701440051a00b0340311404220110941c803507107200140c1902e5006540740070b04001034410500d42d640d500f04078015051002003940b21100154040c2c014841414a8540b403034942c00118960f40211ba6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 544944172 1250 544942922 544942943
    0x80c07020612190b060301060f030f060b18090114100c150f09051005270c0307061d0d11010503070e031902090a140714070b0a0608010b030a1205090d 66
    0x2c02240c250f640d04004030703030b150080c008410003004128581c00240103810000d229540441c1c4414425040403c0e4003607658800143c064a40c285101c0e9903000e50540741c021039020304403c089040c100011401407000c2d41d0b1040345580a0800907101c4040301d20340b01c0401c2104e25049060150341c01440c011070121010070021711501d0388080d4040c28480d001540c96000d83c90a240c0840740742d0040328840c0c2d04007440d20911148100314902c12020200700d01005e44600002c5088035201046048068005502d807100c0008016051000b1400303d03041d51401081d00700c0c0c255000410700108001850003d080640d02ca544880d021100d941c501107007558103200b400d401a990420003541c6010140c000d48101005603202c0900d1800c0c2c0300746992081000d9051000103d003140f041240c1c1e51801074060361130b46485090303212041d2072001552041c2016590745410440085e0034451065405404c0e030150185003c41d4540605803402d15504901344100050103070690350390f440b160741066502c48448107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 544945422 1250 544944172 544944181
    0x12020735040e150f012f0105010306140106030b030d030c1206060908010e01022703100c050a121506030f0e120702030f060c0f0a1403090d1e080c07020612 68
    0x851200065405102548140040c0120350130034040041c0d1520061319018600315a0300c0305c0f000c440b01c4030003008081c0c0e003486038644034503d400e000d101d00a6024040200b00d0f4084420203a22641c0180c0c042c0c0705240c0350010b84a4980c8022a007180152130900b000500c400910100baa402c551100302103802c41c0c9810008030700305400642e48015185088000c00086051044503400c03031060b00030004503458407503195045854203519980c104030024045c2c641e40302c400a64002a15064206800400d001003060451140d000c2c090075000c40016405202e4401160304030b650011641c0074801c00c1640300e00700310b2442c2155400440e12000780c541284e800ca020960801c2e1280c2000c08220b101c1d02a000030408051000100c8a00a00c0c101e82d2052901e003048007000070030b030701122440e02030124041c00c19542002c01c1d0043d51040d01e9501c058103a06010820090041507003440501001c0c40d1007405184845d84569800d6225400302ca4807640e031921400092150f000d5842042c20a58821f020031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 544946672 1250 544945422 544945439
    0xe0f09150a1b080f01050d05030d0f1d0c09060904120c0602160b0a0b1212160c03141002030c07030e310c0c0b04320d1202073504 57
    0xf40d00c030395090840c041d483d0340c0300c40801501c0c0880e40800307846a401400b00c0580d00040da403215a00844001c40000e1004030b01080b0518034021340c042c0480c0d0b8000c03d605907428142a44450b40c810300480310b460207450a9941c42d006020f01911010410039506d1900c010014a58126400800a803d50750081c110a203451042e540048900715034807810f00e000145941090b181d21442070181070050311080800c0400c580540e00301480d840403111070b03043c41c0f0010500703030003400c070141d400b48480050b0702c4518110180341c5440f040b40c0ba1045c80c410000c00c60040605416201104d5140c03901d0031450030a140011012213001c13213407030001003081011404410080d0250444c044d0700000911540140f080150344800f48168081c1101c04000b00040c0040d401012030907030303d1852890312800144054886a0451101c07042c0144c030341c0540b04003000260056218203140d9850f00c1d0552400396542c0c0c450152001403601c045030610400038100c142c11400104a24142410040e162510781e1140d60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 544947922 1250 544946672 544946687
    0xf04170f0f01060f0909020a05011b06020703050a0e030604110d02060d0f020301050a210821010902130806370e0a0b33060d090b010e0f09150a1b 64
    0x108045003a00b40030004400040b4094446c43d40c1e001401103100324a824010744542407410b803422007025075800503800142081c800742400d02d00070ba503020703202c0000c0c80f0058a00303e5000055031007035004008200000e0717165660300c19072203800c0e1a0100500c00c144042110b80c058981c17156951400c01000540d907200c90b034080c0d03040302c408603500b0388600d0380d88201d00802100e007421515103042d40041080894107910041c0011a40700001c88480b44801e218205603901c00c2c0c0010741a10b0f00010b01345403841843c10b1600180030400702500c50350a0a204a060400302c2104904640190a9840503860803911100d041001e010f0018840e041a4185440d1100d940840840f041d240c0d00000c1075203040354044550000500f112001030072106410b018511410700d0000e254400340c02c10207803060b4540740c014241c4d054410406000503504081e010384010340010400814400486c0c100103007002d00140601c90250300700d51528032515414120b802610300c02c101c14001140018030a05040e82c070506 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 544949172 1250 544947922 544947929
    0x3041209050a080d08070e030a0507090501090b03100b030102090d08030103031e0807210f060f091803030c0201180506090d1814030705090903070501110f04170f0f0106 74
    0x2a410358a9072514100142000640144440d42e442900c409800b907014000f010707000400d90419440c40d5810303400007460244400022525504044d0080107a012180940c902520060b801402144a11800300f6915a0740c0c00c02442140d465510044c1d40d900c0070340c1241c90f403400240038901e666410b428058ad076a4028401100003403204160300780b46420208036002c800d180b0741d072001031a0711015801c5030310200c00d05003c03e8102500b58444820a0544512129050850303004101c5038501111030300900805e5101e00c84241c09d29440309803070092544078604a907810b040000e0f403002c0c1200f040b401002881d0311017001540c021401824088000f071054031999101c0102ea030705115418046401188421201d1696030f0b0440c0b042c8005000300024000c101d5000c1c0854030340654900000320300c00d0094071007a41c80e400016100e014060203008062048910003182442d2440140140301c1078031503803003044e00300c0803280d44100c065034060050403c030000a5048580d4083c103007403554001c0c4410701c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 544950422 1250 544949172 544949177
    0x60213050315180c0a0e0430030e150f180703301b15020d0902090a020a08040f030203160302030a0f02150c0c12190905040b030703020402090d0602030412 68
    0x201c107040f034800d0008400c00d0059014144240240c6441c0c2c202501c0600075008a038030b49204080310030301000c0d0180588400490340c400010800070705101800300d0340c1002c0c900f245030704a07c084d18a4240c843c14015080000c1e0a01d0f1501c1d951009088000300e038190345641000d000b811800014003034010210a20341000094441500c04516100d4444000f0b004018000c2215120040d070f03c4041c11400d00c20860103a40e8000d048104802c0003000c0b81d1041c80c1940707940e80c0d84c221074819414200c4840380e2003081e0300740843c60003070b40ea980507204000003440148402443c2001400b018402c2c001d56400c0d10542602e1026103141d490003940302c0c1c001f035011900044051852a880510000c6e10462507204080401e1041d294440b0b000700a9101c15007682c030324440c6407461040d001c000c8008040e510041c240700d208207039403614010a000f0507a4001c074400c03401c0c08080b00b40780c0d90110300c0034100e0754125001030342c8580d2075001c202c103900c514402030040d510110402c400c0c8490100c84645205090703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 544951672 1250 544950422 544950451
    0x30303090b0c0901020d1d090f04060c1b02101b0605040512160210020c061308060709030201120e011104080a171315020a0204020a050d110c0307060213050315 70
    0x30306940480c1c0928846140160700c10594000c5140c010585143e000708001c011f801410b030083e0104070381c0c200544022414118a50402040c8001c52040307034190a0b803881c1400303c101403400340003c040c0e4068400303032045c3d0324450813072861800f500200c040304100403c088208585810844010300003180c050340c1d240984a0310030480d004480490b5182c80c134136103410034500ca054080c0804c1e0318490b401e01c0c0a5210ba503509101c0744d500e0b9009025080390700c41c44c1d040c08034100014141030120103007404052000300c0005200503a0031000700c200c581c4c106500012a208094100381c0501615507080c0c078011800540440c0302c4401150300c503082c0d4060703101203081c0144030806002c0d900c00c1d4900d80b02e24048610090040c0c0d81a5500c0f094143c0385803040702c81e00d20503500000e080760300000c5403601240b000944500c0d40000b40c000d403a4140c58030000b40f8245451640c11681f603100d540d40042c0151360015a54400000d031840300700150101038100c403035843c0c4400030040d00ca4030545e1110700b0940f04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 544952922 1250 544951672 544951681
    0x21030901060e090714041515171915050603191406090408030c07061b030b150a030b01022803140931141006080903040b13080106030303090b 62
    0x4024000d402164404004c141542c6001e00c00d04da4190680d0314154040c0d254100000c10b0043c0080c0f00001d441d1231f04000000c41c10304c0002401c1485541c1920041c840c0241c10840d1219044035010054444501e011444081c00c0711201d8102c01e0f181c0009a0001010040c84103141d40400300340c615400f8040d00f044141c7c02d800d00407241010071506958003180703280015000132400c4003c1c50f00021821203180c14014140d803800705442030030808000300040f9605007807000fa4180903201e0401c034184e402c451040e003503601c10700551007a440a441410341320041c0c0e8205034404c00218405030035004000d60802c0c0d00400038441d44241013000d60000f41c183e030140c42e0740b0301c00303200325a1481070081500d0040b01c44450358000c40c079000403e0014210340c6111710b00342200b40380105011031000c0c0240c03150614002c8000e0064200c3c41d000b010401c06910100b10350301c00000111402c0c0c80b20307548480d494101503803881064800c0398003d00684d50810000108064040d008508824410f003c0120207a48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 544954172 1250 544952922 544952939
    0xc060306081c030209130c0806100806030d031802131a10020a1b03060203100f1703030f1f09062606190b0a060909050702070608182103090106 63
    0x20310b0403000400c21507020320308141e5029034001c01039110081c0c064864800080606000ca0b403038a9101070105001e4010040d0b5894a03408009160745103040200882c03c011380841d55910818a80e4801c1c180d407851740300d40141c102210116040c0d8010654415101030904030005051420340c0f200b0002e250310018140b40ca0155584048103159900800c2c0342221038071040c008450184d82c41028111201e000b201290b00ca000461240440b005240c000924000316086034040f2644620328041c1201d41c000c1c8203a00101c220381e00401032000001c2151640307801e405400303046c80111200f40c00040400203104c04a40c10400480d510147e0070607070030700008450103001000714800000c1b90031020006440f900108048000800f03281c000186000074500866500040c540240001c42d400328010404883c2034010b540d8407400030300c060401d86141c44001341004c0d10203011081040e16002c1600103803036080200c00c528a8803180c24100c40e450305140e080090f030043d03818103115420181d01180e03944 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 544955422 1250 544954172 544954183
    0x5130503030f071704120207060503060a031401020c0d08070f02060c07031b150b0f0d05030703080405010b0603010906170a0c270501081e06060f06071e0c06030608 72
    0x15000006146103984610b01003010910040c20301c0140300340b49456100c4100b900303082c00e100e9841170240c07031203141d140c100283c03400c0015070023070b0100300d001c1042092544896070000c0440e540309401b43c2c907851001c9802d50190103000c803003104134810303031480f19000f07035214407600c0c02000346846e440741d0741d8800802280c0b00e610485416956060410800d000213204110702e030a103480441000c0c2d10800155241218a503050354281d41054488180703203407600c0c000840100182c0304413140c0d150740300165601522809402809820b00100b0400034050060a4115040300d110060550f9500d40c2c644071001c008103954054106601c43c12041562701100000707158a150b6080a071540540c0d1400001420f241a03858007181d01d03c08212141d10f40400c980105400f80c10a94040d00400440f200350310080002074000d0121903001a003403003100c0e1107a121030b0031007607000d0b10115941c401904004c4403c140c80d0050090400c442c007081024400110018810b40700d9994050144039504c200540d600c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 544956672 1250 544955422 544955461
    0x1501240f05030a1806050a0f06050d0204020a050708030405010507110f101104080a140c0a0e0f0406020702030a0606150215060d02150a020115061d120102090d0f0605 73
    0x540010180380205004501840e844014600081110b140c0c3d03020400c0b1812100310111040c45c0c451042c01810400b42c001e00c64400e140c804200201c1e49424001808002000e002900a0303034000f80ca8010684140300b100d5040e600050125074a007400c0c82e041d4001c010031503c00700026034070340d03d002a4480106850080c0c5c4d245074001d01000c85401080340007005a030201c481c0a0700d00f0800003c000000340003004003a0b00910060101078410081c9034200700c0d41d48095071144200380c009020180c045420540c11a040243c00d2107150303158034001000f440f510300c0203545407180034005400c00500303070080401d0300c000d12400307c10402c1e42e103c01d0340e440c07041071404044008180d00060050030159240c0d07071850300041200311004619010907809500a00c45440141d45400c00c6401041c02c11417244010040d614003a0394103c4d00700e184044080c00100514416107481c00d040c0038006003501640c3d0304407801050054200c21341d14207101501803040084410500308000035a05003126803295002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 544957922 1250 544956672 544956677
    0x408011a180a18050601080c010903050a080c1e0a030f03020c0a02040f0b04020c210a0e061b01020a05120f0f0f090312100504140c1603050903150124 66
    0x40c0400055030184402802a1226503585070f1140228200c0800e480380a40940d0240149504003080c01c1d00b4055101015418450592003c000003040021310440d466089a00503071190f511188030350a0900840b10402180156512100310010201d11030068074405d80300c02425544012040d401d9003d480c1180840317400800201002d810103410240540c0500100003c003044090000f0307080740c22a0203010f07100d03846984906505c1c0200d0442034001c0d14104203003030034103c440d50018142d4240c0440d4a00801d00404c040207010b40140000030b100c02004000c6d900d49403a050024810f410001421030062032800108540c5003210640d0b6000c3c410408448516980c0c3c1102c400b0703000c4010b0030700703200ba00c400c2010390520701a05a0460043d105000010009840c000800068a02c01c1c0b14507188650301d9424001d00032040c07c01c41b0b980c1484c01d1801c2c0940f0506040544d81401b50000c1c043c6c050080f100352007085d0204042e041d05071040611283c0d009031009005204034100150940c02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 544959172 1250 544957922 544957939
    0xf03050609190e0705040e0304030507062d050904091425060c021c0302070518090703030e0d1e020117040c091e0e0f0c010e0a03020d1106030103080408011a 69
    0x7035030a4030f90007442060742e031002103c10540c2c0c3c0340003150032681c2107000d007500313a04041024800c2150600c0040014000c03841c0ca0503031004180307060910180c03031000c0c01c0c448200e109403482e403450040c010b82da03a05400410402041c0b15500700425a030042c009480c1d40b502800521410a18544658102288940f1010042281001c8040e02c503a5000d05003640e012005869007403026060f4210070740f005201c0c1d405050614606402c0c4448003500401602c000341045080108940340050345c08c0c21250107190008003540d950000c00c0e81080c501ca0003400e458030158000010308016048002218030030303a03400301d00509111494070020001da84c000d099900908042101070513a404c0520a200b09280d11041c409101218104a4040010381c206a401c1901c00004100c1c0503ca4440742100030700b014407410340c1c8600090400845400000d05c00c0d1000d5000d03000307104000741030040501c0d01418040e6030f96124181006141c21a100d048919800e01c04001840b22080451264004018001e40b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 544960422 1250 544959172 544959211
    0x3091b0f27111605030a0f03020c0d0807180602010b0a080105190504020a0b0403030c02010e0a06051b0703052e14220204021809060301061220100f03050609 69
    0x3018000c408600c501c0c054040c00f408400104840a040c43d0a224400440d60350608036005843c85625064074424940f0502800081501c00f00da1417500403100d01c0d200c0002d40d83c411068500d00c2c4c00025108581824900109015405500500030f0950848542c032985179101c0300642a42d0003205c0d40000c01b00d0b0032040c120052041d4201d0382d00548001c06811095465810070481604668410780004039180000820340d60000794500ca032000a40340815594200003000e4524860206038030030a091700004148610001d02015024650104c103a070300908522401e0304074040a0440e07110a0000e114500c084404503214809203100341e421008890354601c440100d14000a41c8541c064000000c1c000005039180d1000388076116014001800401d168402c2c40040b0800506444c0a03038503000f0240b042e403c941c10300d815410340c018002012070200030100c2c1e0b8940a00ba121507044958850200105a041f5030a1801c2070420380c2c04012681c0ca840070010705032070640300f07480501d81010245 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 544961672 1250 544960422 544960499
    0xf0901030b0603042112052404061a07080c071706070306150e060d0c030204080c01020303090a0b04051606030b1e01080106180b130e06010c0c090504020103091b0f 72
    0x45c60b6032001d40c02c0209420042100120941d94220340544924520103a800340400f1407508100301030100751010001c5034241010000001d01080ea280d50011012460000304a680710445844100ca0800d030750180359101003201d49640c115900001c02e004180018078881d11074819441202c00c0340441c8110f0b5800306009030b4000a50b24140c40d000b05d002c221a03540c0700603500403a01c0c1219240e0700103950b9454016403a05211044d0402070454000700705100401a000414000301030b00100b1000c503d4030360b49050b42c5495480c070380a860319031021200080c240e40640c0007240c0b140d820750b0388214155040085240300b410324a40540440d20300e5005010705440307444007008414501c46d1512046488003903208040e085401c05084070840d00348107001807122050486d03000071081c00e001a02024650310055400f606015408405a440300040d04ad60300c640c0022886c0c0b41c001c2c0b1907902c039a881103c1e01404000d0740c000c00b200110381c2000092455241c2c5181c1040c2d004001034a080c60101042c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 544962922 1250 544961672 544961723
    0x80c03070c1109090f0d0216210209040602030f01090e1e030c0a3002060103060b0a0b0301120b061f030902030109120810140d02010f12020f0901030b060304 69
    0x79510103075842d060712059203424070041d000b10058401804440c054a4449180101d0540c5000440d0084450b001d10404411204015600d00300061b04240784060803c0c0840c00b030200002c0d501060000030302c024409250f0045010f10305042903590142e0721000a9015601100c100b12602c1d8011b2100180001e00440448034000c004c5055901e81003400c0f41c0c2602d03040c50204207455009144080c5c50a000403074003c0900e240f0041e0901d4005100080b020351111814800540b007541c66a80500c155900c107480c80000d0940c07400d0450312561684090101248000c1d8101c4458030700c0d00100311303985418000c106d809003040784804440e2a100000301c0280804c0c960498042d9213400426000403000b007288100c80c0002d948208003490200c442000c042d02c1c9a0101c007174243c414410311030a0f202c84042e00180d64080c20306020221425400722408904100745550492003c0f40240b04489040f0040025600c00d070303402d010b0410309800f049110b1009640c0101440707a010f915500c00703412000c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 544964028 1106 544962922 544962947
    0x90604090f1401022701180302090c070c080f03071e030503040b190608010b04060614120709080a1101030c0509031b1504080303060a06080c0307 64
    0x100c4181c94508940c01801007814200220300440c001d404481054401e44170318048980b000b0b201c03c0305030707095605044c00540b41044c61401119182007420540b074005102400c3d80e141c2e00440703d10b6a10003d0222403800614400045034030082c403001d1404851800030703544d01c02c0c0d07601d0450061502100d44815030160040d0704c201103944641a664841e500000b02c2045440f035515034400402d0004000074801d0903c01c002c2038078001900468880340095509000301c0303841d040b00340c0c1c61041100e2200039050050141b10314070380079079070b02c40e03005411820480310840e1190005807c2a02205003034840e00c411550031071041d41e041c801c8100390005454040d0400c0401d0002a03140d0300201202c0398103405103800d01000307a4610b101c05200c8030800201c00d81d1555284000780d101d8104440d0648a04041c030360002c3c445004920407440790b15855006447d581e41d200b0248c07035410140c41d = true := by decide +kernel

theorem cover : BRFrame.Cov 544784172 544964028 := by
  have h0 := BRFrame.cov_init 544784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 544784172 ≤ n) (h2 : n < 544964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
