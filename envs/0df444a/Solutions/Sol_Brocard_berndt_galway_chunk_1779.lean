-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1779
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:38:52.237923+00:00
-- url     : https://prove2.me/submissions/15d3d502-ff86-466c-998e-3e41e68e8d73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 319784172 ≤ n < 319964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 319785422 1250 319784172 319784183
    0x370b071403250908030408010b0a0518070c05011e0509060601141c020f0d060302012a0602030c0702030a050c010f1701060e190602010c0e010309020a051e13140c0304 73
    0x110022550201c4121030340344010b9400c1111070142c0307500f100d902e581c000354411841da03034651040034000c0c00c03c0d8442c000036001c15102070301c50220f0f82001c026941e6015105104000c200006031050080a60014490b141d0003d0020801c800016800020344400c0d501c02c2854084c3e0008030b00f00358061255240c402c4545c40500f41040c20a407814202d40c03803240c04426642e9000c10415510b10180001002c888000910004031b843c154000140501c00801c414203c0d024000d40d03000040034804000107031558404000350b42c83da00e0b0401d1240d039006643c0003c1d0180f0888814101b0041301042001220800781d8842aa4103600384040707981542c00700408904500c4180140710b41c62003503540d100300200150610f0000c00481001c840c181d2000d81c002c00060f50342d1014061071036070000e01052914001d1906201180d80c030b0300000c07a00c1d03a40f80300d603a2041200741910b0b0350004c0c0280141c6003000e401442c1c04100b2012100a40140880a400c84000944000050314003403441b41964051a00709 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 319786672 1250 319785422 319785451
    0x60212060f0d0209011e031406010e161e090b0d05011401090b0706050405010615050c011406010f0c020102011107150501090e032205220e030408370b071403 69
    0x1401800f461b104030415684600c05021010034200d9501e0801640c0f032000038045503240c50003080507480c024020781540040714a030504100d9112804001070303148450f03002c181c0700900c03905940d0f5442c2c1c0d41c44200d822902054100e881046603100c58100c51230600e01003c0711481400440308800180204c880300d0300107104040101e19144d21683d80070344103000014000c2d03140d5081239200c5603444180d0313000440028820850680030b0088400c00740e02c0c0803048111b4105600042d00080300c0c010018100541c8a500e002968400d404c07540300c41e031a519149580e45650b04024a0003000c4440c6650f22034180000014840d0403846128603840c00d0001950a0500c2c151840d1034034030080c4a41543c1c511001404511035503410120540e0320005482102550134140540d4143c0f18001d8901810380c1042c80f04010700c80c004106280403219440f00300d84007001800420f02c202000c0801019504110100c0004026484004c0c1d40200815100c00408107030340c2413901d01504c402c45240007004401d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 319787922 1250 319786672 319786679
    0x20a09090f090218180a030e042301150e06040e0610270e090c13020901031b020303060a1e03110d0b09011b02121213060212060f0d020901 61
    0x2a62080e19241d408600208001ca100d8000544012448040c400c943c0003207020b03c907a08a0703c226401d00345264402415400c1c20b251000ba001c180141205030142d5103440700c0718030b12007a0f00100000e1085038040c0800950311607403c5030700c003079080420101090340038031320700309500c1d081c010b0300e08881040ea1456500ea568009214948100d00e4545c0c0500075074900c2e00d13a03a42c00510755900003c4200c090b0a140501e481080484902c020701590201e400c0f44500d6043c94458a00701440166291000f685c2c808403040100c005208220030401d000f420005002c045170b074003000443c0195402c13030300140307660b0f1141e02040849040001c03c05c80b40c3c15250b02080003c0c0310142c58285031034002c021032101c00054481d144205011200715042d41d6507889400e50b81e080401e13550324460860320050941c229400c0441c2d003103114622042c0c41c50800c13140083e002468055000000c1940000190b407100b2000e0f44580c80c54009030380162050071103001e4600c0604207103e41061050700200b406040d13902c2e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 319789172 1250 319787922 319787939
    0x1d0c04090309121a15150310170102030103060c020d05070201300c110a0b011e0810022508030601030f0b03070b090f010513061101060f080115050301020a09 69
    0x4514000c07824440101e00000d401202214900ca40394042c03401c070803042401151002002d00700816504006221030202c907031035241c2e000011400481d0302201580c2e130700c1c3e0610741e01140e18690320182c019040560328040c0b201064004d14100c0388220070521484040d28026600d48290010481c00190107001d0302025620400e454041da15044105030560400d8518881820b004c6012442107070fa1a00c26810601d0b034400704160302002080043d214404003940c41801d035083c1031181d903101264802d0060101441c1a8074003000344080c3c070864000c070380c0074112100a504513000000d0111280c005060f0900420385580e03841541c4100418599544c0000550050a0751321181d0b020701e0703992000d60700e107480030400c82c0090218480b1094440c0b49902c20030280c0010404031904001c014000100d105042c0c00045050b0749013400c0501070807038811030381e90041489a00103007062080003800240102c065010420000c05210041d073380c41c0d22681811b09034802c15400780b000607043c00e0304202c00c84 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 319790422 1250 319789172 319789181
    0x1020c1c0c0b04060201020705070503010c0e061e220e100312020a06180620040302060d2309061f14010309050604111305070503040816020909060a1d0c04 68
    0x91107841400107860b216081448a90055041180540c0d4001168018440200450002008200d0083c0710f0b9031180c0348002c1c200c001031a9004c5c010034000c01e030201d501d0703441030024503c40303182c2e5400d40e00c0301600105121081c110118504581d40d10000c04030790320303082c0d92032148100000d41c1080c0009155039241019114400b00000450007034403151030004607940520040840621503104c0d0360007441c02c01c1b40848400c1404e13032620003455003007003a04003a000300381e0381129011100c030360700c0d288184503400240c180c0b518862124000d002500c3d2044900c045901d00a00207070088500d16501c01280d0200254041250585070650003c00c0029464002003041c1020703041c50040382c40c518550700d031842c00130145c030101c0303035084083c54400b46410720f5003d40c1000880c0c02d0f418000d504102d0f8000d001da200140010304202c0000600b10000000b00d843c82c10004e90140010020b4a00901e0650315040d041e50141441c03820903c1040003041070b070102c1d8008804c280d000e084181e418008010090 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 319791672 1250 319790422 319790479
    0x90e0a06084c061403070b130e010e07090e0720030906070506061504060c020108041e050c040b04060302010915020a1b03030e0108150d05190305120601020c 69
    0x2070038400c100482d22840e2a40000804142400851014840c1c0c2c4055054501c2500f002407424000c00d2281c00c50360f0f0000c1e40340101d5294100240c2d49103800040400400466001403a800741d409000081c2043c4560300207200b1805551000945c507164910055030100603100e500c0000d1104060012007c00c130402c401d01e450305e12007101d103000c003101d01003801600681d00a54040d00203404200060420080c10028141140c0f103151a00d410b2050250a803044000080e04010401c07000404101d2104603420716506803150414551410b494881e80da4009001907900581c14010907642c00e0501d4011071095990584510805c2401e26900c1843d5000803800c1d41d085106290143c4042240b9081c03003100da0b04a11110b2624034294103002d092202040301c26070401c507051003004105e80f01c03003c0d00b581180d400c8507000008071250a046140c08030034814200140321507110001010740000c000c081c0c09207440c0e00c00105135110030040e6210300180b00c6041d000104211031211625602035440b404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 319792922 1250 319791672 319791733
    0x50f15040b1f050415081b01090e0a0b040204030506061504140603150a1d09060c0307050705070e09070f0504020309330c0703020609010b030c010c0203120703090e0a0608 75
    0xb1140c0d1800081d0944a0011065a10f14401d040910008006010000043c0a0010000018030005000a03d0384c0480c0c0301e01d41c42d40002c6070204840320820380000302d1000700184155165500d9080840d21640203441c1300d44580d214020400803031b013024003038800701d0700e0444d4005482c01d00101400f40a45c0010030004046407800e40e813030306596581d801100074200003006203544c10450443d0345c400800107010310403298420402c00021040440890703620100c030340b80c17044e03e5060901d0580e02c0c2015036000f50b082e581c007030300401607094000100d90b000c46110103c81a049a625410702040340f0040d101c2080310740142c00102140d01c1404016440710140e1003010443c0c07540100710064201e000d503184049403000140360018142c0c1040341d00c0c0c2000c00071001308081c58011300046c0c0e98100c46220a03040c0044298010207640c1c05100f1306170054828076000f0703a6010145802031600c082c1d4024180d00f100c2a0000c1000700547e8130540080d41e60381d01c020704040300610700000b06160072081c003550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 319794172 1250 319792922 319792981
    0x807020309040e210712050f16021801060503160509060f090105160302031902010510031101090305300301030302031806040801140a061a0f1305090103050f15040b 72
    0x144d864140014003402050004100d40355441c038038102038000140040c800c1048400c2c050b19450b00c010500311501e603241051420890000c5101140008210244020b0100d104034000a80160410015403040a102c0450303103004a004000b81c0e070a000c0e200741e050304160705000c003000000540d4001e056801050500d582010704100f4651840160300d90b0450040e0000314000f0751000c080c030f54445030850180003d102e24a8061520340131038016110213802e90070422102e1170f80ba401407201c1c001540d000000d96407120303580c1116901a041140d0021070404030401c100d4031f11440c0b44141c3e4140c945c150301039454040100c1c413001d04480400c1485610000c00c102c000b4544009220b80302c1315000c9840303000e40d2031600104200495910f50310601d5212011002000504454000c035400001c031034001a032118140303504503c1a001c0e54000d07640104100d8004400d020001400f4205607a03074100301c03003e913003080d54113103e264030503035001f007110740c0c588081200e1540600b981308001c0340084c07a420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 319795422 1250 319794172 319794193
    0x801171507031d030903010b01080f0403141605071a3105271006020706030f0b0901171605090703020702010c06021b01050903070206071b0807090614010807020309040e 74
    0x42e000c03180c0078056280d501c0055080c1c85c034102802100c00d00403090030f061203c0d1800344454580c4400081c801420800c0e0110034104d00300ca00c001b40c0d214140c1e50000b0042c01c031800c0c54241e03035502940c054a51110380505405221450401c00c454900410104040884003510422008548a0705040c00c070406c256001183d1502c403e4648021125898600350b0110030020b07126480d0403000d481d4111800c0b00b05020701080740c00042c0c0c00708643e50740c64006460b200c43c0200400801d01e4a8103241e10410300750000984024100c0e241c44040010825165060001949420030100b144561a004041c20000442c198001da0150038068010704103031141d2800340d540c5d881281c0c060032414283c2c8030800ba0021102c0c0d82446032580c001ca0080003103103840c500d50000b62080c0641e08000b85001820100c0040d21480ea02890780200000c000301d58040b5124549103003e0300060040d00303176450600401050743d43c45480c4242c0645103503009103241100c240300340805032055040001003442a0034011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 319796672 1250 319795422 319795451
    0x60a1d0303031501032003010513060801060b0304021003051b220602160501030920030a050106121208060a05041d100c140a050409051305060f0403080117150703 71
    0x21440340e03070101c40c150b1000403940f00140c2240c48600c14010003000d11b030081c030524001101141d0542da000c54080c0100c1e4482d403103440103480c080d0013400e00703075081400029003545c2400c05140568402c40d1a00050a268142101252000c4510008101c0b82c0e03010301d403404049500070400803a001e540b212501040200d02d154410b41648a60b0041e80304076800d85245109500c00c0b0050002468240545482600c800761038100d00c00303c550103003807800400486950200581c01c3c80310b621400131b1200c2030381c1d1418401c990f03422000070f84a403214454180b59541c85444400d12a102c0103000c0c00e10745003400c0070f02004100307000c0717421100f4610130040002603038100304904e00e04074041d4022884490160000b8210305011005e1414800107012012280da004010354058518802000078940c0e10210303000104000610007074894045c4000f400710881d20414003501c1a0f00a8440200d540d903242c03041d80e40040810001c01e03440c0c100c0c000128088441500d02c0790442d02d249008075065038180c508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 319797922 1250 319796672 319796677
    0x60c03030e0f0f06010b1c0b0609031606030b090720240109060602010b03060a1104090204091d06160c020301200403050705091005040b0a03080c030418020702060a1d0303 75
    0x4002c03855011101608102c02d0402413035014098203000356042114080d0015200e0400d00000243c035030311214800000e445460566119600003002c64003200c40e0780405240540704c9026020019051406ca01550700b00444481d0103100c0b0b50f074400500c101c0011890400041603142d80b5214002c40584440210f0403000d51880c1c0341041c9103030500c651501c109070f400c4900a43c00f00d025641480c00a040c1c5a40101d0501d600c800010008503c0c520900c01c07052451007290050000300d1b101050100c0d4904156206120801e400306a5003064038042c940a41d07075940485803190390064002d00d0981c44c03403081761207421007440075002085080b0f08091400d46451402d5800e102d40b131000c1002c10511908000c214010310056034540040d05240103c686820028007406000c0d5450340c500c410f050321048100c20007140c1003102c00391102d01102d03070b4644a900611803c0c0180d9102c01001c10360700385500c00c031210b107a4010038a03440d1030303aa80d0040e58164090a0f00c200002400c44521a450300e05000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 319799172 1250 319797922 319797943
    0x403030f200c10091e0501110f0705010b010305060a06030209032b120c02070510051207030606090b03010506070209040302100c0807031d1e0a08120604051b04060c03030e 75
    0x341c00d521540000819032614250f0604010f40c5030501c0c842c403000c118102c440180a00d0140a4801501c0560800601410703502229009103400013503012020200715010f40081c030300c504000d0040e800300d10300440036514242c0741994800055003041203920300030307801441e2a40d03018007602c030181380b544641194143c20420032000803440ca514102d859a00107107054040c0e0b0f07140e400f0040c40c518084004d60b40d22180c040d050203900c0d420035800d115801402503d01189003012a0b04092814940c02030250100e44101e6010609961001c00c9417109071055074103940019144500b845c115408001c810180a0b00c15410b40c01403102400c02000c9030b01948012841c03e49502001d07040c4903100500f11407964048802c214489030000c5045c55010401103c02c0703601074007100e001c00c80004058102003000000502404000405444641c0114807051154204031000c11003583c540564941c110310304400d9010154007044140103c5000c1e400c00c56a4901034503000400061038105075281040005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 319800422 1250 319799172 319799231
    0xe0a0906031a010f06050702010c020406080604141e060615090a0b0910050a021e0c0a1d0f13060c0905150d0c02011107020d0809090c03150a0e0403030f 67
    0x3002e050007211076000076004000e20704030801e82619140e001403107406540710003810444086d100b00c2c01c1d0b40c1c0f541c20041c0a42045000d5900a04180c544400d00350079100e00014540600400202c2641940000005014183c03014129913502c400411141c1d500350b00801e85c00b0601404004600d1702c407240407002130301c443c4101c590398902c403d0030031661014089072030b4100402005a024180d60100c1e190b41e8026030100d44001e200d000d00099400c0c104101c01d1140c201069000c0083c46c0994001130004110380031303009206d9610748030300703c18031744000700c40002e84074260512a00018427160b024100100301440d05004413611800003440c0301504680039200b8032804070f400c0c5003800761032040c0c04442041d4000ac000c50040412043c82c0c84c0103000c0060f01ca40c6e000300e140800c0c814044125030324140010722a6000d0f01e04403074501a01d800a541e142d04905d040300d404401401c03c0d581e2442a500d004042942c00c2e074442c2e4089000d0805500f032884010749814418002c4609651b41d17820842c6a103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 319801672 1250 319800422 319800443
    0x6110c0106091e0203281509110301030f05031e041404060e01090209031009080301030506160203040e07111501080d0c1106030417070b0f01060c050d0e0a090603 71
    0x4202903003034503aa6042080700501e41280e070303074000c0c90b0001142e0300400481400b507281c0e42c0e50904095070f90400c00d044213030658180844454031079198001503995158178481214170391140220800c881c102c1c2100c0907034440403c014000b15080c11449002144990100c0c2d1800c00344404c00619907201003414044000082414008854802010b103040c1c0700030380d020072205d4a05001040200e03818450003120301d500140c080d480e91018490307600002000c4005022414580c540101380e54000d200c20344850040c0800b0503100d035804045901a141603900071410141403400508a01d0009449074013071000b0041e21414491080c8180c010308030b03074050410b8213585130415903810521000250810004c1041c40b00e0000760316204007001c3c00d0350030340b440c645a0b9150f01e00100da086258480c07011a0001207025020400e103001c80302e10800900065000e03d983e81c181c10b49007420701c5c0b0030083c00d40d040441d810b11914450001448001130040440b15241d98404c1c501c0f040303d156800039940c1c003ca2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 319802922 1250 319801672 319801687
    0x5010c050f070f030c0e060a06120b04090b0609100e060108130b130c080c0d080d060e150109060509090402040911041a03010b0a0501020a0602072d050c1207051201090611 75
    0x30005c403c0109201030718481546031900c001a4030706045c0c0a071200340b24145d11310104500095000880301310001c1e20810a42d207250422a42080b801c6515a20407402d08000403040a000342e035000c01c481c030742040d07615035880b00001522880001050030310000801907501000c01d1281c1c03000c0b40a010202d180410500d002e00f03007105100d0843d00034403916130041c00c0c250015140d60034141003886d00003c0c034649600095068801800199001c0381907080391405103c05581c5481001d0b55103202602c81240655a8000c04d0f1114040c1c0c960301603201c2046000240942000c0d044500700700d200f00003920800031360100103001c980c0082d0361700c40d8602c0609821061401d091055042c1040105c4101c20614078200000f903841e014400700900c1203802040c0b980c1001096003007862001e01d0107181ca03405813081d0014019076418001c050707030184104203151616041100c0c00c0c1686526400183c0710321030918082c00044400242c0c4030115640c1c414a01c0b0100e85144035408004150321034442c0d840b00c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 319804172 1250 319802922 319802933
    0x602030703092001020a20030706020708010606030b0d020d1113020912060402030a2607060e15060a06052107020c0306090f1011070c0e0703060801050f0105010c050f070f03 76
    0x1602c0b00d50884216429030f003003d80c0c0002d074000c81541d1100c2c2400010610004400004546101664040c403850a02080440d00424104240c0392180f0082101c40d0345c80307500b2001c0c0d0302030b0801075810580c5840a880581029240304038418004d02461400d04002c5004c1001224a030301c444040950100c1c41303004a2410000700d001546882d40103002ca420907400207520303000042700060604200e8411800c80c4051756045034001404c003840380303440705500c0c10108003a000c034424088190180b0244034140d5200294110701541010302115142c5062500a4600d60b0002c00144482e159011102420409480c64280706040130340c06441e03c1c49990701854a0301c1400303040c0802c10b07085084c05c00100c2c4070008081c42d995040c6500460a0841c603059041c41c0e12807140040c0c880c8581c203001188240c03444881c107000e150320b640c081081554451f921801c0390750540d4030008600386880104060340c400d40c0709801942c081c80981b00b140c52140c0724640342c00c540d54460400784900000c00c005020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 319805422 1250 319804172 319804193
    0xc0706030e0f03041a03040201020a080301061821022202070c0611030c0d2d0e011101020702010c170f072f030618100c020c0a09140109020d0207060203070309 70
    0x2181d0000544c01d040c240018410b507000f20103220600403101100040a581c0300b0016144a103030001039080e6a0350310b07000000c01c58000ea90950184104d8214001801c40c40e41c00d00c0351111442d200724000f10012982003100060625002c01e014011014811100442d40e100401132948904808543c8514103003000d420021014040800b941041c001a26215004907072020210034501c3c0403184034180c031800c00d5150600c00d002c09402d00d800c5101081d81900b02c0f2000c0c46001007620383d4403007034140303051107802c0c0c0c81030701d40c000d0006580341a40d00004503030141e4407108056018501e07003082c403060107007031140d00f220a055401c1c440d0b10343e180390381e55080454071b81d0488011030540122841940803d580341c01c0904a2a208804000400a90341c0240301984035400b1490302400030010400000f555032021904080c4107451600c000030f111941071144c000010b550140e10a00c5038a081c507440b0094101c40c42c94034600f6001c00c03029000910b00d1000314490b0320b45450000c0e07101c00310f080004100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 319806672 1250 319805422 319805443
    0x21c0207091a10050703080c0c1c030510081c120207022d01080c0a121413020102100204210503160f0308060906090112060e011103011701050712110c0706030e 70
    0x20130700b086900042584080e10507800f0380c0d80e000c52981c4411000d0741510303104c00b5100d1080e81011460703a0042443d80754100c24007070225070014407095900c4101994981526004071392007605090481700d40c15014006800c2c0c045c008450040c01e04d4050b4011840103906980c208500141c8003400d040350541c6000625580542803800800d146800c00b550a5244242080981030055040e0030103001c0c503554020444490404a51b10070906000040204800714608203d0141c000c1000100c0301520b244295011500151180402c3c0800003620400004500501795500e0108201c1e15040c3c074184203803007a00c10b00c1744044022855217401e0080002601130031091041542c84107100103550344000341415100d505012910098491420500034050a005405a9402c0034620007188011a01941c100c070b03801c075401c0c1030400051100c0c1d401c031081110200081003415000d186401202d9100c5026003040000341482c00c000051190300e0180d040d400a00001e480e21a1009602c20600141c42d1380f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 319807922 1250 319806672 319806677
    0x80d02040f060306150806030109021201050114091306150b03040c09050106020a0203061501090e090f19033f0c0201060603150b0f0405091503060601080601021c0207091a10 76
    0x1445c148015800318800418010041190f4800882c410f65403c0d44181c201540c01040d0a0705013114614460180800f4401c0c9000000c1f0041004000d05105113900d2188036130030016405500c1c10340c0d4038001070441404c09400c82000c1b82c00800c10354134990040d4041c81c048c2131406922442c0055844c2a204160404c00071500042201f40041e200000c0b0b0302e40214445940f101c84110708030040391441110f50200101c50001402e00130300850208548400000b14801d84805a0a80c0b00d044000018028020b00090801c1d40c1d0501c0826504855686c000b43c102101c8600b80801c11184040011001108909075a40700c42c0710b202078091041500410003400c0910501d40d6070007408a5115003845418031a2000040c007500b00c201c0c0038212001f910380204255500e0070301c205100c45520509801c8c034064410071012619640c06641098490381c4168010a01a00025182400742000f900c1c00d809512a413540840c004d0300754000d1500765000301c840d03000c1c0708082d80704000624000c15054801d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 319809172 1250 319807922 319807931
    0x150705090f0d051b0f030a06060f0e0405070317090604090b01350c090303130e0c180d030905041805061e010b0717030f060f0a0b0d0e0a080d02040f0603 67
    0x10b40100d2041000710002211422030341e041804256034001d07801c17649505001320030500302002580e0303029100b9103000d8940c80500c41d80302d5483d0b00000d1400d550140144c0e104040070400100c44c4c44c1c2007502480c004161508004400d03020803240d0700309802c1a444103440f03000400e006c1d40d016844081c10581103000902000311b46925548882c02100c2042d01c00001100285901d10240119151400c0c044c1c2141d6964129409840c440352050060048002411011072850340e40301050b64044d081c080108400581044101705042003101412028400320a5000486690f030388920455031508055081011110340703403990070320400501c0002040c140086051540050b802c255041d00c00c65103449a850900341000300200d401c45180328001d410000c02c000381107809e00d19460050805a07201c6aa1819440800061607864000e0445001d41030003074100c1c1c00c030590040c42458041500392100f545064460701c0240e4082c03800d4031001500003030304020103640f8010340d000400503441c0800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 319810422 1250 319809172 319809199
    0x3070e150901140403080c01150602010c050a0f111204080d050313031107090c0c02040b0303030f0606090d060603051615020a03031a060a09050102010506010f0c0b0702150705090f 79
    0x40c0c040c090000254100700c906504041c804040004503000741d81c1104189403541740d24250b030303400303005049075a45602c03003070f040300285031401401206898503254852904040101034106c0b11f45180881d202c04110141c0da400510950900c50b64038001d500c0c107401690b0303500300417185103004ca00030400402c1240400810021510602c1c0c050116907043c0b90046031a030200d480a80790003955044404201c1c505201c03110b4007038105440d00c818901c00c0c0c5e418401d420744817040503160301080712414030507001c000c001440c40c603007200140354955004100e410391814940341d00c02101d61581007107400c0e0340090540c0e40c0d1050001e4807000240440303070304a00d0020f00110000d4070740c000144000d0074161074410807403281e82c40030400400404043e00140c1c41d00c00800008121100902c50103000d9440d050114165500c550001403c03050b01e5100c1d040d20300819518a00d90501c0204100114001e100c160f0801c14a00704e4018040c0c012940c40d10384a6594800b0804d0100740d0030761941c41014280c0c0e005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 319811672 1250 319810422 319810459
    0xc1c0c08011202060f0a2a150603150509010e0709021c05010501020a030e031e0c01091a180a090606120b0301092004092f06071e1a040803070e 63
    0x640442c0207174148151500740750b601c1541e20703084070a1840444903129032101c0000001c02c1c041d840c014060103013101a403408600f008101c070355038003002d81501c1510b2482148610540c1080d80c100118400000343c1008800c0301c41e0901e926a0815640650006044000c95a180c42c00c16840b007030081c000c0286500d031000103591fa00b8202002020b004c902403a001c00741da414826410840002030b07083c401c070048200d02c40d0700d0340040103045001c1341d0300701004245400e00d00c1d00310b080c009044a20ba860310801c42030030a2010100225147d00140e541e1010613a071400f400b070300d401844681c5400007850249018002030b540c00d0041c89004e60b14004003840824880b4003090b440d031100c0794460000218140c00305016040140d0060860352440703100004403c00340c2280c840300c084c42450a03041d507003403000b004610b220b29080030341102042d01070344151480360b0801c203001a01c28400107118134140000105803030001c4406990340b41c03000c800c200e2240d4101e990b4020350f8504441400c0425481600e5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 319812922 1250 319811672 319811677
    0x30f0e21070b09010207180605040606031b0306051509030f480d050a05060114180c03040303050702030d06090614182202190303030b0a0602060406050c1c0c0801120206 74
    0xc0300d0087e0920460406c411856500c01c1010704409030040c0f09060300c0d034030064083d0452180c0c1324103080ba0b60301d124680c03902c24410f81080c0d07407000f8901054035400c90140070403500030301d504913490b008620581038901d40801c0f00318990170324409020070014143d010b0210080034a003400c01c42105010f1021200c0c0d541c0504038a1460007128409407100603400c04601d01542030000030614400c0400101703148846540b016100882213644d070483c40009220103100c0c0609490a43c005201400442c00080c000e400c9282c2c4440c203841100d00700703424000502c06951103548102c05aa41d41e0106015212019000a46038031055036a000c80c1d29400c0f001c03005003100107203c02011418030040c01540c240d0040001030840c0c00420f41d09009602c4503c0740c5000b00305100c11008a80382040f2880c1c14103183c40880300f1103100f500a44140c2da0f80703407240c801400d0300400101d43c0080030441c01a8160912141c568000c000c00e20001e8201c2c90a00040d200e4403043c0c1000c60a0b0750404116001039603000304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 319814172 1250 319812922 319812929
    0x717010608132306100b0702030c041122031505091902030f1e010b03070806070305060307030b0408031f1206020f070209041a1b0304030f0e21070b09010207 69
    0x14040184580750600c00600c2d03c041050264140009049514110002804502680b5401030400a490303540e51031008611800500a4054100d200e40032568601139119140d0118100f03189450140600703225454041c8c000000180c008008500744203000f8010182b40c2d040c02c0d09503040109041c2410000d40e00d9030f80100381c1548140035258402191030511024408008503000c4881c003051000c080c00c030300c442e5061070980720341c80c00742c0d4002140341c001034182c101e6135110040c1981d504c6001c0120041c00c0010881a0144141080040044e85221140348541e000f502142d40b642844d10f80c4425000d09a0502d034401c400c0c016007441b1000c00c442841a180b80e0180e030041c0d40310341c22000b08aa5000e00341002e5840031035042000302348801364403411070b4046807440b40040303603840521100c03d52070740c0052448800c03000e0000074006400fa1840001310f110710309002004d024200c000070b940c001030480300416004007100d17020200008021020213031600300401410801c81d680001e65803407980c070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 319815422 1250 319814172 319814191
    0x90604020f0607150c020c010e030705010819110a0806010f030e0706050c070b0706060e0703020304080f0a051210090c2d0c14010515010c0203060c300717010608 71
    0x1d030402004000c143c2c41040700c4c031050050040c40f4003183c01940fa0200202c2e02400b09056a00700311041c40c021440e4401e40f04161075480c090b449010034003045514400b0000d500c0d550399802c3d4000f00e81135070080c201d0032019564245480ca8401c00062203801c42c0e41702c0600385414000102403400022581e042035908501d086034840d100d40800030301d04403843d44844c1411000056401c244807264200100751032000d2140d50302c0b6210321f9011403c910048502a100fa4002d204c04485614090020a1400d585251450070040210701d14a1100015510010390703003654041086504d0b800d01900c0b11408107800c2002d1240301d050440751520f09880d0f00c08404003044020400524040ea1102020790380201c1d14403041000e0344001c80c0208801d45007442e0121940413400242d40c030510001c00040e502070091b0100303407030310000c500e440d402c410302d03420700c007002403000c041c02c03000d0581031078803c0030420000384c4c40c0c1c104040050318110440300b50700d1848031034100612025400000081d00f06d000007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 319816672 1250 319815422 319815427
    0xf141c030c0504030c12170a0503070c020d051510060309080f03180a03080f0f01080a060506060904020f13140a1403030d09060f0c1d01050f04030b011508090604020f06 74
    0x900003140c0703074852078200801600c05c1e240045081c00c90a411051041d120724018500c0c080100d035480840e001e02e0380c1c40400960208001180d0b50f1042c801001c0d0300c1c1c4050200c211210095440c1410003154480d901c003001c45000800c00c1c2c0d1019080341c8002072030f103810100030804940c1c4515800f4030840901d4080050000046181c1c5076a4900010011040e0026a0748400951900a20381e150966280907074002d80b0000c911006640b11000d4100c420801c024201c24615541d544080d080040c240e41d0b0088050103140030039210350005112941e207208070655500700704041d4005003443e07500f01c101404d4801c40001c100d0740390260250180c41e00001e401150000b4032001038650b1103000d5080d4841d908040c032610030000c0940210001c40c043d508240100071040908803107144140f59994260300d514900c00388c0650060000f84103c07000c00c282c00d45030907241d403074880304004203031b000e2032a2204040c2da04000551209100743c1118000300075101909040e00011000342820b400700703100d040e00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 319817922 1250 319816672 319816691
    0xa020a20033403080a0e01031a0d03110f0c01090902030601200102040503120a080630071508010305100e0703030f0318061b0810060e0d0804030f141c03 67
    0x10300b1036444010009854116403a2249880036458011695100c082210300c0c4c80740c0450740c001d020795400c120035402185400800d881c01c2000c1c80700110f20507414420300c0f8060003801d2109218000d04200120020302881420304001425294181d001ea155a40b043c010700046070b80c080010480310384802043c20300842c8070316200d402885150301141e45841030007820000c00541002034402c2c0d01742038031107003082e40e00c0d0b030b0a01c03049550444030701c5211914122120392007000388001d5065450080102d07160309417909403a04181d082e0300d008001103094000100300f00002004103880c0e07130203144001d00c040742c440c0301c10f02d035035030120702008046c400045148050103100e540503c0e401404c00700050018952410800c0c020090f4800d0030485e566041f880250090203a078605015005402d500e5000e00c0c6010401c40308070048429440e0b0106800d0a0340780821020405000958040d9000c03540e01213a610302803503e40d0000309940c145030002142d401c181c1b00014543c00030b8030000c1c1000f142400c3d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 319819172 1250 319817922 319817983
    0x5010819032a0614041205250c0806010501020712020f0d081303030f0e090f06010c0209010f080616120507030219030b190f06230a020a2003 62
    0xc2c5400482910074030700504110440c060226540060f000b400100b2490720b4401c21008829012a4094420584800c0c0e0740d12603071245c0c1c000c0c03030580181201c641c2c122407074504040f1817260a00c801d451080c001c02c020320118205000050040509000a010b5140382c40300c4000182103a41d00688034901503a880c003002e4035007885a480780c41d400ba0715580d0f1290080b506424507090741c001540055903900344849014040c88584d00558001440b00c2c2d500e50351464000c8006600424482c10040520150b20041c0c8441d41001c0c041c03c200e440a202e40c1c1d0501d240ca6240400041604000d003413049401e4440c250001400310a844a054002c20160b031003007000d501905c1005903c00c00c400020f462404c5465066101e404640f80c11204240140c508891013001211a80180380303d0650450007007141c1400b65032064080c225929000b46152186e1407036031003035040b0032407500c0540c1040866608001c000b4103181040311115000228081404003c00d83d541069240c294803018100b0f1880c41000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 319820422 1250 319819172 319819187
    0x111c0201020d09140c040203061503040c050d030207150e090109050901090c1e0e0402030c090a0f0609050708060d120c030203070c090c1101020702090a0c0c022806030501081903 78
    0x600304103019001d03240c50044c031041078400c6402ca85000341005e80c26246807900880f80074020003072007815103404008650031a5031010f40100d48070003845100007002e444112011115900076005406131500e0416107169007042a4910001c00240d0110402c00359618043c507815501040c40c001b6403a40c40d0251680100b81c0c004c0043c0c04c590600500003407601d510804034040c0074044004001d815611387d40700800e682b041e14000d503d0b07001340d42412030b94103006000d181d005040c60b030081aa02c4200e50810101c0c1c00903000180907035128010001400c0c0c21000c0070360400c0c0c080e24080f011240d1619504248090201e40c5c0d03081003283c801c0c400605108000f500c0300d090300106000c0c40550b8900c003210062891a14120202d40111032100380340c08180b00b541d40c40c9030007421041d2151364440d056001400342132070441c140907101d0b03805405a2a550740d40b1754400c07880448941c4010440b511040980300662140d0201401c1200502003554042031040c14800380d604810131094040c601640c0c8070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 319821672 1250 319820422 319820437
    0x1503050c0f0921010e0f16050d020a09110414030c0907031814061503071512020f033d050d0303110a0507060f09030e010e0303040b0c01050402040c111c020102 70
    0xf00d500c0700c8440210041988404030300513018045440c0d82401451050700e5031000c0b2125215114242c80402140c142003455449107440244050301a41d141c2010b04103c0c1c0c603000790f03c0d110301404102031240f03a40180915040351411002001404909070000e0b1a0303010081001041580301ca50310f43c92241c2c2e45c6031801c551a4068540c200c281c148400080e0b135a10201c81d2510b00d400115450042400d02003482c409441040c000d9802003582d040701035800d1241442d9060003141d081103054450b41b26203018500405901c1c0a141220440704c240c85052100045064084400040c1c11219000800c03c50002c40e5402e030340307440c880550303800c0641c01005c0c0481c0d442c84a03040054a800401e900c240100350701031144100700000c1045030f40c2c803001c4880c0d981e80100491000d000c141400e60195411000e45a00101140d01e40380c2c603003403074420a0300610510f8030603079190305c02c1c04214a000e0103141c202807030515250052580e128442a940c800076414052154103521505012038070039012185e07007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 319822922 1250 319821672 319821709
    0x5011a1c1803030203090c0904080406030c052701120e0a030e03030f070b0f100311012d09050f1005030c160b180d03061a0d02070b07091503050c0f09 66
    0x4000310703400c000e8003961048414031801c5c0204d06600305107143c400091070149030081c4406050030309001c01540200802c000380703030510900b40040d00c00540c280d4400c8110b81c0f91071000c0d01100003414005000011030445040090b410054414520400042e00b146c8113501840c201229107402d85c0802d0075449010510460306074000f40c50018820319121141c000d0340b00080090340380e510040701468521a6000013444a107003145000800d621540d443c9030055000452090080711440b4a002030f145201804000300e849000100010314101d00269481101030701e44038900c0150074001041c03132000800008030b0702030100e0481c203401c600f4200403003100d174403401e81b031114249001003000031844203106c000c141c42400c8014000d580f00b40580c01c05c55443c1000000021603410b04044ca54106c8031103088030513824000a400b040c0d02c00709050013000641c5a20100d2410a02c0c001c00000d0441c1c611002d0500301400d00c5070700755664044072074080c0185840f94507a00303460005860344c0c43c804610b000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 319824172 1250 319822922 319822961
    0x1210209130b0a06020303040c142e0311040806040f1a040507091a030601030803090a081803010c020708071418070e0406120201020606040c0203191205011a1c 70
    0x1103400e0a0ba01000c4142d004560400b48565160004c0340d4038481100c0042000107400c10800c40d001100340390f850b0300d03100100ba07000914200c000c0300c603198005a810010035440080581142505440b0b220308900d80420001c0c949824040c0c00c40c0d40701e00c0500b0050056040c401d11200780034100030100c04c030508043d882d0301141401c0c1800f90740d5503203c1c021200c403c0d00e0642c00701000501c3c10b21081303038000b0140181c0440d030310b188c40b000202d401c01444001036010315a80000001c0589006040040d0402e0619186004004c1814215420003089205550001006000c080350001d030040c2182d41000c5031120410048000c9040441c840040b041c84e100124140302c0b056402803500d030480b0300d042d50b040045c15640c80386251705900040c1d0207405078011401154560420707401000001500e0b0049920b080c591420141004009101042c0012007182081102100702d01806004201d0b03040095058400180441924482e00a4140d01c40d00440b02510715a403451b0400085071520754600305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 319825422 1250 319824172 319824199
    0x315060f0c2a0e0f07080105030a030804020112060303020a14070602030d020904021c020a230904090c05030d09030501200a030209030a0209011215021912090c091a0f01210209 77
    0x1c186400959000f180c002d044400510341d588941b40c0681280c42c0240104420101a20261095080a070041e8100000b0040782c4c100701d100c0d1300500c40114481e41c000d01e0901034a003050a0080d8a80b001c2170015040084100300940d4000292a0b25450203840103a40d003a60800241c020f106030040500d00b114010001d02c503840480c0d01a00000100d1303128013500302d04200410302c4c540c2804c040f6a181507014000030781c3c581413a0703103c2c1c0d41c03043c492201d0382101500c807c0020702d03100c0f940400000281d2158402c0c01000020700072503040b154101c85104c10740b185100030030f126000303102c0321600b015804509500da50341d0030441c004c03003d41c0150012a8950311035012580c5402810800d44521120f842a1038a200702803088400355854102400b0842c0c6250404660301400007100c6003509448505010101e0540c4030000010003181000269284040300c0401100c0e07003091501d84140c800c0024200b080e6081408805a03850082e4041e41d0101034411507402401100e9000340c2205082c400314 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 319826672 1250 319825422 319825439
    0x312010b0c210705070611060901092a080118030f05130b07022403011706010503030306061c0203070e010e0d0f03270b070506090703150504020109030501020a0315060f0c2a 76
    0x7c8540c0042060f00d45d10303a2000784040c2a01d113803050041901d90422810300c0361405000b54030360805400c600ea8450325680c0c0d0402c509490401d03000700300901e54941c04404164108006015145041c10040d06003440348820995010301031180f05280b1100241160840d82d90440034003101d6241010032400d1032031150710042c141c20900035001020310b843c0380060550000128a8100d81000b402589503a40e52800c2c000307182c10181450031402a010404112048140080c0d4802c2c0001d84d6541d540c464407030001449040c504141074050a4203d01440125403960102d51405426051034014044054100c0c2d1104000c0d03003086000d03200420380800c0403000c000c020002c0c00d0142c42181c82c1612160055500c0c2c05840c03100600c0e86113102c0c43c4c41a032200036000141c1c03250050400d110a2a81d035204e95081e81d20200b00342001036581c0440070016040300c80510054012490b05005420080c480a4452032152801601c01c03190304604808007680558280514000a074580c023485941f420070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 319827922 1250 319826672 319826687
    0x12020d060c09030b09010e03090d0201020c0916030f09050d03110c07031109010608010f03030c08040f0905040213051306020904150e150301110901050c120c0312010b0c2107050706 79
    0x320798082d000d01c0811400c817014051800d0301110701d0003842c03414582004020180f034440740c0890550081c2c00c4030b030390f26039500c1c2da900c0d2081705a00d009500007a901c00c8002c0845110810030414203142103a4000481c030005404609480182400503110301d491030811803d000d00440b14400b40b04070300c00801004402c90584440346000e0302e0381e00460b621000c1c20344407040c0900401580d46c0c0c40c9070040003c03074450707613100b000e0600035600d4a14007603e80c0e587c0c0e4040403060708641d45140d101d4040c4011800c29002480001c40320010070880d90811421407091aa030f503080140c101e9401149183c0155915400024840551581d0903031043d550782072404941070403944001120a540c880040c03e05040c015800000c0d401c5002c140b900c0c2c041c50054a09400641c503815691244c11800d0912108240c000c00003550520000d6071540c140c60b11914072005e05800074080585d003800050082400040e501121002c40312403c402c3c441000401401c030b01990308050118890060002440d60300541c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 319829172 1250 319827922 319827929
    0x15010e041d010b0f030606010f17010608180a050705011d030118030207060f02072601060314010608031201090509030d1802010e0d030c060513020303121f030c12020d060c09 76
    0x380f020f442c070035007002401d00d103000404e501364100d00c0c0000e480f5807240200449a129070705140751a45514008090400c1c0e003600a14042003101d8184031010000107400b40440301c200d070050940014581d10b05868020921550b41841051500301090191825210a0b94807018008220794941901e050f071004064900503000b40c0a448000b050241c81600c01d80d100055540040c16124940498202418440c40f2421100346c410190f1140b6140c0c00e018101c02113009002e81c003400944080403500b110496800802c9691013004400140c600c91458030341192300e503000001e83c95403000001401c0d44a92060748401c1c81c1343c010100728102e0755642c0700c2c80460003070780c405a500c084081404070303518803401d010b130108a003890100006051034104a03440103100000390303c024140d50200c1d1443d08107a00c0080c0e8070b8000010043e0501c0070400d4032180c40481d540f5070480c6460340d1201c0843c0707034940c050318600c0c2600036046415912020f61400c1425808001001205c525600088c620f034902e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 319830422 1250 319829172 319829231
    0x705090714031f080f0601211b180606080112030201091b03060b01050c030d0c091223030702010c060203041e0506071d0a05091003060528060e15010e04 67
    0x107401308512a00040044c070808007500240010f074204580d540c1c148a000c402000b00305c00c0040440000b40440d5658140e500c01c4000c2072030300364144400c400c0003141c0d8010811503140f60150400c0303442d034409030342e504449140c01c4202c1c2c514101c0c02d0032400b4040b8248044d01a10803003c0ca98803515000940c601140c1c001c100802100d031141d0011a000e20504805200503801070000841424241c0d104078405042410004c059a507a070b0689c7c6110105400141e4041401c61094201c1040301411030f00a02201e0000d94645141540043c105940940c070290103650301000103420000800051440302250b0008d40c1006449891b002d941c0d004101d0304000001d50700c80c42c044a0620540ea81c004a00c001040015070506280a200341c0903c01428074201c0184040000701242ca07900c00c080c01090032040c095170054510106e907a845041001c10300c0c500d403034900c1c2040101c016100c4203410503050168640a04421401210030100c000c40d1181c0c040d142444815295808082c0e20141e0100326 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 319831672 1250 319830422 319830481
    0x312010315060302090c0c01060e0901090302011a0604120c08060c04050f0301060b09040b0103110f041a0a1409120d020f010605010c0f0201050a02030c03070f02150c070509071403 79
    0x19804000703031240c2c0c0c44000c5d04041c58501196110805602628200004200001d03000380d03184c07900f0a010310280c2c2c0141c00c9035582c4051000340765082c056069510110f070b190b1129240d05001003041c6125610801c2c42007414005035000f0400164246001050000c003100c2642c28020b80b03840c80b5074801d1107994421203140c0c5113040c3c10304060094200f01ca95040c0514101232015041c4005000150307491070401d540d42d0500c0701031003807074805095031941d4040c3ea07903129418000f040380b04070364400181604070014041441040c0d40640c00c01c003140312042080e61904031000219514092054400c0d641d801014500c0d518203600195140c0c3d00b60300c0900910941d41e4850066585e001010005001c10405181e2040554001c4008107034100c03161040302c0c50904686401030964010140484d2004004001034095103400d000d6203034101030002c0998a000f1001440582d00d440318031500c0d026250031400201c07003c3c007624030800d4000720341c02025030700e10340075264034001c0c8400700d442120144603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 319832922 1250 319831672 319831703
    0x50c0a0305030708070f02060105040c0c0606140307120b0402040902120a12030c09051c050705090903030f0732090301060602010e070906030b0c030c0d0204031103100b2202070503120103 82
    0x100d800c6d651600c0c1c5a000b41c00180d00748400d00002d030802d90104d50511948010203070000c1d6503489444020600c01d400454070307031503507020181003644503807080b41c190140a48150104010340c41c001c4e0000d40c11980020300c8216440031800542c0e0340000fa80c224080d011000f0240040c00005480441159130100185260380d501510f81d035106000307190300001071550442b5084e500c0c0300000d9020340540c0032124103603511400a030546108440d0202150004030506c910704503c030b80855004011820704052111100c00c100855510900c030024846540c4114850f00340d44940841c0c482040c050024005191110f102a010b4070001182c5002e6200388907000030404024440c0c8001c4e0f90344084d04e801903888220903002c0f80c0c0c00103030034800c214100b000a04107000861008000541c0706181200b25204654100f604000360000000c0d8002e003402213908080d590051441c0b00c8040c001082d10000c00302031201c1e002405070600040282c4070000e8610300f19003600d40b40350b0403070748166195409030f43c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 319834172 1250 319832922 319832927
    0x302090f042309010e011536050a110f0705060c130e2214011503110d03050c06010e0f090708030a0804050309090106080a0b06121501050c0a030503070807 68
    0x410600303840c00d002c0100b1200d940c5800c0c200590390010a000004524164000c03a45406c48907029a900318003404200304103d0742c180112224071103144010340242d00c0400c00c2c2e500c3c0080302c40c0c05020038460354410016500010783e41c840f4901c400e10307418068840458840c0300259a03c4014262040d22540000402c800310800c11947c000b94840000c81c00c861502ca820820180b01510050107140301e58070090411041c2000003107100e0041c0d51078030f4402d034031544582c00c460003000454071a44082c0810700102e03c889205c3e260003001902e50700b01150241c2421600c50250411001641c01f0b0307100005041503d2404281c00f8ae100345881508079106c46a209541d0825803007003410b182c0042c0440d04610b030141d0b0500b5405402081564a05090b00c00021200c403000d8000c1004200c0010612000d0501e2f8440c03140303041810795400f41740140780035884083d40001000001c2c1400030380e0021a590b48540c0c240c2e203640e038408044618030146441c1c064036503007049448030001403004000500603407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 319835422 1250 319834172 319834181
    0x109060504060b0702040c11060915060f01021c0c060204090507020d020610121509060f05150f06030a02040302060d0b01032304030c05070f091b0c030512090c0406060302090f04 78
    0x40d20045007130300d0701c0f5003542800040e0001540c0b002c00d120740c0c003155902d54441402504e20880d880300203009014a403195082d07004801401d0705008070004103903525242d8000031001210720418143c0c03000503120007422101c449500000901ca28000314001803101071540103c0d001314429026100c0d00250700904a0395040121030f481d405424602e0100041c022089040070194040d00150f290216a0315448080e00c000302d00c210345040d60b42480c20382c031001c1c512072103820076004032004007240214400a00d8605550141508c42c01e80000400c0d6007400e0b0390304541c01941e014014503200c4007007000c4000145124010603020ae414582e041815038160104015112040302e070b40b241a4807261030440e00b81842150498084c400c41d0408030714403882940540041c4070112001c204038080012065a00c8110301d16034060000c2c40994070000707034000c015103a0103c0303403180c04041580d17034000c00c030701e005240c0b0a80f40d003140ca01030740840c8495242d00101100003003a80c14882100b130520610040301c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 319836672 1250 319835422 319835429
    0x100906270c08012c090a0209010f060f1110090302030c010b06090603010905070c3203030103030503060121110702040e0c010219020103020d05070234050d0f0b040b010906050406 78
    0xc0889006010b00c0703043d40040f1004c48007821501003191110120700d6400501600c00c52040d500c024000811442c100b4032160252100c0641094420329210010302a256560510703c00d0105244220100550030015039a2400310410180080151401e029441e94403000e1003144550a20481c441ea44c20f042c8100c541108024005502d16864007000d040100805043d1608200c0543c0007440451174400e03c0c0c41c4006003010502e84052103031030090104224404400b800c0e500180010004a5040019258070540a00745520000549607014441c0308440c83c2400b034040c5050f0200b00400310141c090b210031442610200007030b440c842041582e48950307014080c0142d0010500880c00303440c00c81c02000c0c0d288181030150a010008030300b68140c44080f681400180c1c80940036244100cdd0000440c0e1440f03400e1a2510902030400c1400404c0b911030340212130040890340c03050010007a108410030040381d002840104141007030714080211243c281320b100d5200781825000300e0140350511a12048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 319837922 1250 319836672 319836677
    0x200306030d03090312050c0c07080a0804030605040309090207260903070303030f0e060f040302120703230403081306030b03120d0b0f1002010507021c020312100906270c 74
    0x180511040704901509440c04128200450ba9808405070b41503801280e000703c1c00c4112440e1a0f4400c01d0503a4500365499128440310f031b2103c0392103404900c5c004103c4065913000b500c0443e0300ea4503803e061703821442551000550714400980342050024817540c04611008244408074015008041c4203402d00803075111759815007043c141000068041c0d40300c031005480c0c452001c190041c5d4856800d040c92000c80d500000c041c40347c403c000405505101a1a210010600c2c0e00c2c05e00e98161401003a0340000c1031618142e082e89121610402c1e442400e607401580cfc02040a0760f10381e02c80c040e0b55103101da04d00c14040480d0510340e440225243c0841c20280768203088070240d05080712184d032800507003c01320515420684d45070b10380344580c07189003d07001d60301d42640004c07850382442c42c0001d1500b188044114407144041c00c500e9400b541c04801c480804c54101444812a2189206590514175952202c200c107071600300005108901d41a41080a040d03450180d10204131b05030381c0e2019a01071040c000700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 319839172 1250 319837922 319837933
    0x2070515030f09070902180a06050304050a080f0d020c0a020a0905012912010e240604030b060a080d020f0f060903030105060a0302091e040c0f14160503070620030603 73
    0x2540c030b510042e803018000b81290a11690744003040e049074490300e5100744103802c84140340c105040200c1034100a28403450b10b80e1441c40c003602c0d141e4581d18500e40c018481c00000494007000020507007940c2c95000c0000c0c1c210350701c0d14a101e0391562100d0104040380240220040050090000d101d0141201c491303804406081d02180c40d035803c03840458411544456040c828020541c40343c05e042406404807a000c0340c0c0508020007002c40002c01c00040c0c0d10380100801040070241c44130340c10b48046aa105003a820a40c4030384000400000c80c5400c402d01a21424480c400600e50001e450050030b034400040c2c0342c10381c0c1c681c44e451307407551800c03500c010055208000411450521030010200c800051034014180301c180d2300000c914541e07a07014a014164a2495a249880d044c81003070030b0a502030170001400006443c1c060200755400310003050b14800400c00c040c806603004920a038150348074090b01ea039000c192600c180100141c0900d402681040117074003184001003011a0700480c4d0081c010030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 319840422 1250 319839172 319839181
    0x60819170423090a150504090f200108010b0403021509010302280e040b0f06031e0705180105090a06080a0b030a050102031806150d110303180f01170613020417010504030207051503 79
    0x10190042000071a01002756001403004201c401210940c40f034141d030441031380c0308042e0000401c140c0c0c06030007403015541c04000c10401603982c08104002d0140000450342c032501e02d82d0050703000340209150503112407038081c0c01800041c10003c0005844036680c450441609800341808203c5540704c9000c2d410090480310358a140c0350803406180e00503411820402424240b2a0f0440204000c1e075800020071804a00c00c035000c4131030204003802c0d200a10f0b002d81051401400505a21164410501841140380215042c4426a0400c0c40111070180071506551110300d0518002d52044a17411444015081c04442c1c0002c041802d500a000200c40d04500011840400c450348950f0481211502c0c403078201048651820f00152443c04a01e441100d07072007203003d090101c1d024405610504014948002a414540d034104071600003000765526012001d501e040c500081c4190303000180054604400c2d41c1d212401508030074801c0d48281d09890180340c1d5101408004804180310a100390402e00008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 319841672 1250 319840422 319840429
    0x11b0f050408061b09060711031203040308060d02031221060406030c0b0f040e0708040606080705131a0307030f050f03030609070807030605101101060819170423090a1505 75
    0x1101200c10902000d245c440380c00001800b56221038021210405018201200f038a024045201c240a01d00a103500d18a090355001300070b03030340003003030684107028118075402591020891401d0b41e1241f030f002d03560b6078000041010509090b51030302d4603410801d07200180e4141418041d1800b160f42c07042d0b81c00e00300c40c10030300307020342c0c0ba0002003104002d41e170700703101c0000c0302c00c01c103644c0034015940c41e100c9400720309003414000103441c2c0380c0d04400e5003513010841c00c00881e12403c0040c40089607011000a9040e0b211048440441400e0445039044c440c070380010080c04030510703480c1e003020320413421038655125120409859020032901594007000c15400500c0b89800381642c0f6a103c68640340c000b0303400b0303111000141c6903400c0500200000b82011419020b1490074484c220103848146c008141d8090401400302d40e190510800808071603140c100e500340c4284040a85014043d80090401c102d9440c0c0003105400645004e2644581819400b01c2e10007003861141d094003204031400300e1400c60074142230 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 319842922 1250 319841672 319841701
    0x1a03010b03150a09020403050114070f0516051c0f0903080a12020c011e0e060108060c0a11010e03070c05063c030f040c05063405011b0f05040806 64
    0x302e000d8402c1d000c00c90360380f6100d042d000b41507a9500140c4650450601e242101c0091022501000713032041444070345d9401c685610040c2c845890555a40e61050b000c00c400041d81354001030480c442c01b05400c0c0c1c0345490000d04804052a6505c044441d070304d42600712100300311448007410b044020041c0b104414814840c100c5e04001c0e1400c05440c0ca8142c1242a00311031300030440c80d201c0e06170301101210b50411030051030008500c0500070003c950404480c0758550601414010381007100040e90301c13000d40105103002044180c800204007880791825a1034484d40403100403150620031440109040c540300040d1a080005894203a121a1500344c99211408200c0b000c001002611035840c90704111010041d4070406044004203150b040a2078026264215600098410302c0140701028150110810300c2c200900192210410781e24010541031080da04050081c00701c0d401c000004169582c0a05001141d9201c1c0c0c2c0c9001080c0340b249800c417040d000340e014402c89900440c004c01d001001c443e50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 319844172 1250 319842922 319842931
    0x31b0409020d12020106060e0402070c05040e01061e0f24120e01111b06010518042621010f05040b1302040e01180c050a08090a020603010b090306011a03010b03 70
    0x507401d4040c009464603a6111000e40f10640140e4540d0000e03c041c1b640410b1252000304142ca080d404c00104c0d41e41c24070b0004903809154000c0c3d130b43c6c2d03400c070035480c0094102000403c104ea00e041c440211110180c040c103c00303409681ea00c4400200005040c207008143c07446583e00ca41c42c005031103d0114401c5640080c45003a41d080c00d6101c000500b0110428072070222030039101c0724400e6031108844a42c0140c0c0e010820f581415030043c0c001000740ba1500303c004400300b00f480360b0b4400b045e0381d0f51a0001550103c85104698845d030040c000c401003002200501b41000c80b0202c203100818403806032103040340d090290650407180c001c1c0800a0f400c264111568480c00145200000320b80151000102c0e00940e10448002c0103280042085c4100b005113010103002090080c0140c3c08208400344c00740c843d0340c0f480c408020010001502042c018051118240c0d80100752a80c0c0f543e482168120581003402400e10034050f80c030000440840c2c40c1e51791075125800c41c103d83e04580c0381c0503400009820007030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 319845422 1250 319844172 319844179
    0xa06080402030a0c0f08070f210804181d011e02070302190f02011209020a05060a050c0f030a02120c0a03050f220f1d01141306140906031b040902 64
    0x491100040b074181301200a004901c548020982c90004241d1a1905075072001c0c4801c0b400400900c46d90040059501141b07085009295950001346000d100030710440e448102813448182c80c00c070707001042d904800c084400a6007040c540c011100d44150890704203400405442c0f00b04a0307442c00e500c2c3c4640140c45818064010b440340e008640d0302c0340d01c501d03903403000031140410140e0b9203504640e0403003070104603008599000c000d4460241c0c0030590394541d9000307880c400c00d0b000c11a49100303032080c0b00315680540d0840a0710396201141e9070680d5241c00c40b00d102c030b015028a0048101103400711003620825101e07000205001010f54070305482590110080203041e6508000304c0c20150841e170b145030310340c00d401281803000500e0501a0101020340b48c000c100c1007401035a0205a610203214424103580d0944186030590000d40300040c0005020200502c03003509080c000107078500c0d26420107030100c1c001e0f22a41115641c0108040d281d403100c6050390f00c1c480383d50350100d1207410960b104038074040c80074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 319846672 1250 319845422 319845433
    0x92b0c020904050f01110a0e04110405043902100c030603050a050601060e011b0b07090519051008060102070909020607060e06070f020106060e092d0f090a020a0608040203 75
    0x6801003101d00030215015103070360b4411440004102401d104070081d410842d80f040782000c4801200900a00c06a03541c0b5110b207445003182c00c5880918000c0740c000700310042003004201c0462030310404c142009a29004600b03003075079403e1307160340d08034032071060000d00c590181c500d111071055a007008106245117601016035038100400000d10400c0070311002c1d4004e500030242589400d00c020903100c0e200c507a0504220200000060b080c0d80c42050041c0b2a9121520542a81c3c6030501118010820f40c025548418407010f815003001d48214850181d501c00d1758801444890f000080d00c0c0c0d090140d0700fa40c0181e11040c0100080e4141d5440302061a01c000c0029250a0041e100c0c5029150070302c40c2e802d070a401020500041d00d0b0000c290400406d40360000348083c52400e41d028119140c11070b1954000c020340030001d5000c40c102840303800d602448681004149500c807460b84150201200c0340c00c190030380000440d0030410001078080495030b000304074a001504056044440f04005442203070948541d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 319847922 1250 319846672 319846697
    0x20705100207051b010c030504030303092d030e040603020f12011107060c030b0d08030712021317070f0302090403110313080f0c0a08030405090606040b0705060f092b 73
    0x60000b0a40b240c019030003003900c2c0d100b151900d84140c0049515506102e41c1043c8580003a80000990b07040300d41500300040c3c002100c0c284912501140c0c1c0600715800c2e402c0c0843c07164031514010101c1218020f0385c90b15400350f01241404100c84141c00040e40c4a00300101c0c919461415424141490755880300200e2690711050a4000c1c503013100034120359490321030185100e0f1036410b100703160004000310741c2c2413012030054841d0035030341c80060f010b10204411455194103102d151740448042d090f07084018484035035621a500d0107090fa104d01c166060017440b50004d02407074170031040001d5035001006603036940c855030f400b03407041c070010301141c1c4131030109200080745c0d0850192000020070411000d010b0701e401c0d0204441c1400d91021100740b2801003098140012103000003500d007564010307601003407207441d0100010050b01550f03001c807100382c4000072003100b0080e01154150049110403a24003d03910790102154803451030502c1500070a8129a618034660300882c040f041100440c180400311240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 319849172 1250 319847922 319847953
    0x1204110102070806040303050f130b0601050912030309070321050f0a0c02120c010201061d3d1a04030203151504060306021e2107050d0507030902011101050118020705 73
    0x5c0718281c011a85e680b080040010a0285080d4030400c0780c0342c003c010f40798a40da140402c01c80940032504100c03010480d18642d48500040c6891400702e0003c6940ba4035001800315500d602e80d000480300c001e40218100b0b410701c5103074860b15090940d52079090500b00030340e9003c040c17500316010340c0d820003401e24080000f5803602030451800105500140400034001b00001e401d40d2920390200368a01500821801440d00e081d00c00c542084041c44088051041c00c0b60f803900d0020031005088017041c00e141040d501011640a030030850301c5c1c0c031540b400300500d00911001c1d203005512020b505a0849034140c03017104042a131240d0301050302220940311361450030100c2c08036080e0341c0046408503130008101100544146030070342091031030f000080c43c0c40e641400300c4219500f140242c6001c4071402e030101d01c50314050340c251600c440c038030301e02041a45443c42c4000c0140c1030f0803106a010030507580340f0135203200e0107009940c16a8642801d03408101d82d6484400000e50045d601902c25005900341000c1d149d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 319850422 1250 319849172 319849183
    0x10e010308251a0702120f130806090604061103010b07060b1f0e03070509010f26060f070f0f05090f04060902220905060f0103020d0902031c09080312041101020708 72
    0x40c0a01e81203107202c08800c00c80800343e200640307403030f05552000200c0d0305a846ca420450301c020b904050459150078800098010001340d0380c020b4070f51400b80e1000c10611080c0090761905c501c1c0203404c140100140910080e4a510082c003640151070010803d2074007203491900004003a040251240091650076004542ca41e1100341000300080d005502901c0241383c100001c50250030b0403500d070b128651500c01120b1a994841c4224243e80f4120701c2c0408403201904850601f01c00d40e01c0c152043c5180140002914030000c032520804185a504500380952281d04083c07061503058840c940740110300e50801c20480c90341e0740d20030707802a200c087c00f080101d45400900b902001c0a8222030003c0d9100010111041d0b854200020007031907c0d0402075196a001c0b0160340c510350030300300165034141e041f0780c00001d00070640340a034240c8036540c0240081701c2803801e000408a0703290b8800301d0300758845440688034440e42d012059001c8050012801190b441080e8080c0c40d9014011142100d0b80d4503812030401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 319851672 1250 319850422 319850497
    0xb13050607051308031606051f08060402010306120b1f0302120c100c05190206040509070801090f06060e120708070e06031903020318060906040e150108010e010308 72
    0x5100490030316030f41030660402e20040c050344409141048188a2070110001c16140040c00c9171b40c4a801060129040c0d95041101d600c0c51008071220a8442190668801c425070301240040d181010014900c4e42250b4010780d0a07a002e03031400b80b00c0d2140410903004c80354030314003201100c0e030148000005944018110a4001504000c0d1100100c034204210346a000888840d00b4020644034040c0002d40c0841e408121911140390541d182d403080c0046081805030380c01464024090509000002d904600038a040320920392040c030210569000703070307400c0c0d586038031030540891304200f054a003518200400d82da289034840211522256034001d12854100954802c40d5a48159800e01416050501c030b011000c1188552482c0031040c1d581c0c00039600d201c1c103045141000b00202d100030181e501c142c12101100c1c1300400a90307c8035100c03900d50902c0d19081c0c0300b19452100307140030401e5550280c0e4006040b118040b1865000d42e180d51550740b00b03613104a58200310300e405a080070800118074038841010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 319852922 1250 319851672 319851677
    0x90201050910110705120d03270b0415060b090402032e0f1a0d0e150108010b04063008040306140402031006050319080405040501060e0a0f120b13050607 67
    0x581e98a0381c0c2c4681451303850b4001c580140d0700103440766202440000d40c4144400076140000d0040d0601068000f42d003101102c50118400b1103000303806100300041241d01807030140740c10368107200f08488544d044480314400e02c0040c030b03400d200004540c43c00d0b601955101c004d505217600d1607030f203110186100340d5000020300440c1c40d000c1e10900c0b800900000d00400740112101c514501010300c680d03003409009500044121030384403000047ca80303905222001050440b2859841c0d15616005850f000c3d00464041c0c40c020340c50f0501c006240204c4042c00320000c49444030035030b031203d0740e035640400c0f000c40e281d802e860f10201004000000b464500c2044680290301015a601341880e00c1003508041074002c1c8040c0960400358140242c1e40c020942e19420141c00c4102881c00400b4501040d0f5070003194403841e800341c500800010029009241e44214034800c6422100c802c0e11010031100d031100f00e00800c9580b04015580300300040d40d85101682101c500402d1440780580360717452524040c8102c4582e0700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 319854172 1250 319852922 319852937
    0x10030605040e01150902030601050322021003021e070c05190b030c1b010203040b0c13080114010807060203030403020705012613050709061a0a0e0901080c1e090604090201050910 78
    0x16240c4c41200b1a4000c0c02c0074150661941c2441c2c0002420750101a08409404440c0407081c0c000c00a110b5a07141d20a03030240c0b4050790560044000350082d041007803c80707001002d450b4070403c00d070302041c211054580d0000c440c005650a02061000350000342180300003030b20b4580d801282001c0103101a40c442c11040340040c0d9202c220405002c8007a18030030f410070840e0300600910000070012280b0b0344d80018010721150f15810000703c03003070380c1000b41e5000034000d52a2214a0314504040303085c09041c0c841c400100c403111a62100209e07900d00c400c950260040c0c204400070300c525881019522003d132554104c004000620341c0800040801c2035621b8134441000d1400841080001d0020318001c007440340b001c00045242100403520142c9000e00c00400100018500215901881041d102044081c02c8420f180d80c4810000d42d41e480310301c40d040d1040049a407140300220301130002e10b0007030314050f100c0409601c0300d50501002d0004268224103103d0f0a001e030700c0d0303180c4a9020791088865140d072000ca = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 319855422 1250 319854172 319854191
    0xe07050a170a061802090f010e0f010305040615060914100f0e0102030409020406170c0c03090d08070507060207080f0c061b010b04020a0e1507230a050a0c06110a02030c10030605040e01 81
    0x3400d00d89a140c101c8c10f0045840c40e2060325030743d003e1110710180302801e01194541d1603151400040c110540450100003010300c020030701c0f0398003c0d58001501c12400708610302120780c00811007c0d811000424000540940320310840f280700725201e8000141c103004aa044c1a02c50082405a0300b064011100048010300d200b6405c403a119203040d0042003090000e440d0800304000740380c49114803000d8501801840c4908810071404c0d40071690f0060300042940c81d410303114400251140100d100f0103030203100b100030000788220701086417803032441d0040c12545042408213000c4101c0020b04003208581d5600c813000c0d6070036290303030009040303450b0950b44a00d070825040d400c21207102d05090358000c3c6507406000010016010102050708041d00301007a035a024079100080380340012000d070062a07401048181c4c0c0401c280400124250b8020b0f4803960709021010148695405019a01030340c5580b00d242000c2c405c3c00c0c001c0300349035030070018503000c208243c4030404203060b90100100410140c2d980c0d20b048 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 319856672 1250 319855422 319855429
    0x62521031a030c04230a1409010614012033060f0108281505030606090c030a0204050604080d02060c0f040504051801150e07050a170a06180209 63
    0x6001041454a0000c8031400800da40d0b56181c44001d0196903034080740c0d940700800e07030311440100007a004054610701c2d0500e01d0002905400740007041c04042d04008c00c20b08a418000c0c03000b1f9a100f00d401c404440420401195400c002866184071240c8094125505920a0000c4606c5940e22181000580e030020615900c1c0000d20056890070700d01c2405200290f914800c00c030885420910341811140c481418014034403009031688400160550650300814686400034036591071411880e0808541d140c2c10b060300e0303200880c2c07810f40c404550b07070010b684403c200d009560800c0c2c10141c01800d0030385850204000303602c2034209400c0c0f035100c6001c002d29948c0c108580ca03442595800e00b10b052404402103405035010f04d000f018070540c0c0303920009043c640c209549500c200c100100910a00140c8203410700b80705260f01401189101c98030003d0302040c065401c98200b5080c0341c0e12003582d50303084000054040e0000c1c0030380300005d4481d4400641241424250542c43c0c1240400503034402c1c0300e0081 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 319857922 1250 319856672 319856681
    0x12010f0b03071203090e0c190c1a0103020603040f1506140901060e100c030e041404020a211b050607140f0c011e02010f020c2a06252103 60
    0x1842c164451042070f1001950280c0d1034412542e080701c61031210b40303405a106085000c0d030303003d5411014004603d0107030168000c009044aa009480e02c001c120500c0441d4500e265007404065013100041020030300048500d103c08401c5801140d81d1500051020001010340311a6404110080556070643c201c03850030258050050110b4200130346458042004621000c0c4070b0000e05041c0320050034054245409006d0751410450001c00800004050700f4000c01c9507401a46c0c241c0c010004070300302003001d46040188103030001552072410614001641d649200000a020f00c01403099032020020b201d8a40d040030b881600d1184040481402818a44510f0100000d000380c0c226408001e00d07482590700043c0110006489200c51503808481c10300076801741c1108240c1e00300040c0b002604010419010401c0d045141c140b2111100c480242190400410002c603140c50344600704011562486096006404c1c01100b00101000240030944034521032120501c103200310640c81464902440d41d06105 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 319859172 1250 319857922 319857929
    0x60e0406080a08030c13060807110f071a210624040504050711100f0b0306192a0201060603051e040311120c0102040302031204140f12010f0b0307 64
    0x101000541d2520300425580c202684018215010001c046269402d6034011078101c8222007903c00c42150b6034020041c00c01c901280c40200042c0446642c803e04d150100e6a07401100a440003003100380d05050341c114444840200c6140c1c4201e04026042041c4003281d11491029142c4024100c58035103a801e00c851640b9001e50003c60940e8074244108281c000f00540f8161941078900003641d03540c01800f9071b40b0882c4c0b02410030542c031455020748078081c036a810101444066407000d120420044080c107545080649815290100101c520300b108a0344d0b80c400001424142034000e0560308060b9100846005980444010307516140d080c0010358242c000d0503004130103031442075048000b44d03540d4410074070064001410401c00c3d0010480d40c4000300413071406176600c0c0e0480381d030311200c4848090003580582f1089000b03024450049003070380440303400e0f14100d4010880021100c0c4502c1c08010003040061100e07903010f14a000206d002103024400c2c11805e140344100010203010040800d0300d4840f0030390 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 319860422 1250 319859172 319859179
    0x18060f0a08030f03060409021e01120c120e03070206030a050108070f0e0402090a061e090c0201020415030b0d0c0305010b040e0c01050403170f1201140607020f060304140105010b04060e 81
    0x30420841090000304072004120040d002507100d80720280080c0160034074210203540030000c2c0000d280c0b1207031101c1c24041141000d803a040c40707095a242c1a80c042d16145a403030404281926554034180c072a980000482002c0b54050b64680000b580c0001c225800075039081c5492540d0b0b200502500c48100040406004000005011b16203801c05800c0c4100300240000c1c000c03107166010039241c14054100700701803d007600c4641c030020a0b038900e0b964440018400c401001d400d1902d0341d20014010f1080364290340c0e68111080c100c4001c0c0000394041c00804139000c1d040940090740c0c40101301c80d4020080550300c603d001103640d120300002c100680d501000ca0180030313040000485100c0c3c0e00142250f040302d6014207039213a0042d40314030607201d900440090a048142c0020b83c05c40400d2465500d5050f984200884200360301d101c0d0501c00f00b4025080001d4200803100400040e5144c49800365a2140c406c009145a2841c4a107006081d00d00a138002200140046400c1c008260080843d90b150301c1c094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 319861672 1250 319860422 319860439
    0x203040302090a0b120d050a1701030c060c170403290f01090c020f03030702010506030601080d05030411040f06060503101a090d03141303020a091b03020c010b18060f 73
    0x150001408014050002d070221560750802c5005905c071400a5010305a1080541d5201040b1907005040c0d41d0059911400141001c08941114140920028103890304500c060300001e00713202041d00d141e2402c1009503052070043c5001111200c0721b1000308051841580c6213130980780b5031411110445803c0d10190440301182c0104500ca1a0912007070381141c01454003c190f4929820b01070b400e009448a0041d118080003040203e03440e0150030103802508290100c0d60140e0303030341d03080549030700720802c0100000f9000c20114011411440001c5000000200001001c0c0d54071900782c011030b070f0164461710203d10007100308a100051104804014031407058890104c03505020036840030702c2800440342c481c1611051113010705114040c01402200280002c503510082245100100001407004901c02d912907030001c00e06800300c0c0030b01e03803100c421b82200307174000c0c00380c80b00035000385d040301d10800b005659540d40c11000d5942c01d452888290309840718844281886c1e000d2080924490040724062100d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 319862922 1250 319861672 319861679
    0x50406090c021b0f0a031a0c19050d0b06030a090b160e0405041106070606030b0c0703050703110f1e0d03180b22050c090a050105030703030c0c0f08030403060c020304 73
    0x82100d401c071450701146144103101d50800600c6804c0313188040764001e046010084100701e45008462403032110310090417002d5580c100912964414141030006c1c03098450071509005000f040074260011f2400341c0480c1020110010488030381044400e03031030494a036002d910500094001c1c258001c0201003107035005074214070014103240750740300c81d1a0103281d07110001414842c0c440d049502c011402880945d4405260815401403c00c0d4082912801d00803008284002000da0442d6400b56150701c5080c10030141d91000d6640b4464815036146501171281000c050b1801480b42654041c81e1b81841210b000e00802c0c0b05152015200e541000c0c1850103948805454005012201e0740f90300100b00c11840d62010820410009412911000041030f040344404020011900001220003640d9800d86580d031050030b00c0541f5002e10a5039003640100606201080c481c48000407003502a000490a441d96a40c640e40c8292841c4d00400c129040032409000300005c501a01c080d8911610046041a04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 319864172 1250 319862922 319862927
    0x60105060a1101110304030f08091f0207050a020333040c170115060302040e0f0c2703030d05040302070801140106030c0338040e0d081e10050406090c 66
    0x1060020814401e41190000342c0020941202140c0f00008480c240c50b8202898040c00310051004120041410440003480318800002d45100c060030b41940070b02c600850007036038070096004c01d000341d529004402200d00540c4003040044100400c1184001113420350b040182e402030404010f0306c501c202c8940501001c81c40115000c01035410030503e04ac031000b20813141c1401420103100e099001c1c010880c0000d0b845405601500844032a06030419840d50f840c403e4110240d4103d8103000340c01c405001120717502d81c0000c1c001d1400500c601107440508038050000c1c0c610340126142842040c4c0b50300c204010580d040c400c103802006030b00d0007409000500a2500d018400c1409540100340c1d0702d01060ad000c1d03100360041500da59201207a00b507002240e004c212204403080c04e468070000c600742c0c94500075040601c144900340341810080d10883c681d212080f1180710700079220040e001403540010704040180d849190040030800f1800541e07514040c2403000703940896122010f031030f02d01100c405010740c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 319865422 1250 319864172 319864177
    0x1e150313020111160f060305010b130b0a02031e07030207170c040903050d05190617060c030c130b040518071d0a1a030402120c0109090b06070f031e0206010506 70
    0x40d424203112518031444600c003032810441c8107205080d20450a1300043c4411900c1c0020161074595505010036038030f13490941024843d520341c58029810840c001c1240c000c1d14400b4018000451050302c1c0350201040c1c031500320305104200004030790f40c001918001c141d010010039000f01200c1030f411682800a148164903000440c0d00603025a48607e8941d040521400407a0020000c41004025070b0500b4180701240500a454031124185040030208090043c04503030300e1080d0400d00289056925144200050b400c00b0f4102000c0d07441c20b015001041014a480c0300241901c2000036499601c0c140400c9625101002c1441001c0319200a010742e90f07600804070080f4070307101e1900718012000400401c1c06d103210b41e8089001c42c2c3c034482d61000ba1280c4080158011402281d075a922900c2080c6415101d40e045860309000c580032240c2080300c0340090b0003031001284000c2520b401d01070036865154113041f0050301140001d01008040340346200e0034001c202494100d2004242a6040001080061 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 319866672 1250 319865422 319865461
    0x402120f0a0326060d2904291605090a081c0212031003030509011e0207050a050303191b080a05030613050610030b0a03060e0607080a050c160503091e1503 68
    0x100142c043c6c2e007884a030780380c5100464808039400b074034141c108404e000c50075050200449058402c0c0c800c210146400d1030b4040d0088600700001c4c6040114280c03165030040440d00d81000b020640003a080d00d05018150307800b200d45200c0449112400002424280044d100c03200a0809005100403550003164950940381e050408590356088040149c4401040c03400d20f0f80c05104030f1503600649030740815a03408649003a15010315032529801019140c1c0141d144010356040080350f03000c841031148a01d03030b0002302060790b811519001921401119403102c1c4140000c00c00010a0020758208407a4004d02018004c40803c40f6043c0440041d6145c0d2142421108242e280c0414849540e00d140080c0c00075039002c070007006084c91010003d502e5517000ca45450209983c0400960001001e00409106400354902c481c548155452003002c04000310304252007030f02c020b002809a903150605c801c01c02048202c0101c803809140780c00c20000300071644041d10b8a09046c01440311510b005c81b000c10f00c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 319867922 1250 319866672 319866683
    0xf12090f0f050d081b0304060e03010e0c010f110307030f0908190204020a031401030f060b06070c15170a050a06050d0506150301020708160510090b0402120f0a0326060d 74
    0xa0b003030f600b0256143c2c0a101081d507000c070b69541000c9a1540d00200800403603840340c44020b21600990b041500b02e0381251305e04009034212040c440c1c480e62041c20240c1c103101d241d04005012004000c0204d18540050204502140803148298942e642100d2503070300400788000148074003680c4000803601038181310002030243e5004566030951074000d4000b02c60701b0b001c02c0704901181d0395a0404da008080304a4041c0d07007031072903c0c10844007418020121060150410410803003a89041034900c4001090707980c0801b046905c039542e070760301480511601d006011041020480b0b0410b15502402c903412580203030320408190b03910b500050700111308203a00403910031740c2002244641001c83c0c00381c8030f541002407000b440098804000d65491076000f4000e400340b0110b5160f42020b4070010200d074480000540070601c1000041d0040c5030a14030003809582e48408c0e114070324484c4900e42e246c16078081c401ca01090240d1006d00000d01c2c100d9201e0301d044a40e65160420f410404003040007401181c201915 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 319869172 1250 319867922 319867939
    0x302181c032a050601090f0902060f0705010b0901170607031a0402090406080109030207170705060702060702040906060807031b060e10030b150c0607021b010e0d0f12090f0f05 77
    0x800c01540b40444003400c1c0d500010420149900c0e1140d1108824000c40306118500212500c10300301e00d119203030500c0c2c0e0207071120f0b107090760b100144c94598000703810460310b0f59203942070f07a00e0315162065a203000340000032a0b109007850410b10541040c500520040806141105512500c00c00e0a00300c0c11140003501e0041e03881c50200c000c600030f032800d038100c461a5805d1040d4401090350000b2070030204e1381c007805510f683c10182141c3c19162082c500c25694400300503c0390344050701e0081c0c010300c51207100500000e00c07044540d441d00255802588800c0d41c503000000300f0800e000a009843c0030b18282e4003110740700c4c42c2c280320014000f80c00c06440180591442e500c0c0c1400c05010303a2200e102500002c01202010302602218046540200c4c06840c8030300400010035036060000407103100488002c2c00301c034507842c00603004407441608804083d5000e004501c50034045007140c01030340ea03450b014429080c00c00888140c0035002d85803d51040f0700d20040ba410400100801c1055002900e104a40c0c1c0f55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 319870422 1250 319869172 319869197
    0x9070c030509030a030207061e02030a08060f09010608060f0111060408030603120d020304020f060304050c061e030412020705010815090a0e10060e2a0702060f0a0302181c03 76
    0x407054010509026010311909440106244d000101c040440d5144d80d83c1d2042900568072240a85074561542d070090b138414001d0000003402402d902c0d5110304050a48403030b5200260002d80d06c036a082c0d010b50040740c2440d00b4417507a0b041014294202100a007030000b1a100112003150b50340000900240c0ba005000c404111195001c4c00190300703c1c07003078030f500507116000d01c03803408000d42c0103903400ca00c111042e07843c40c00c05050600685e0700c290340141c00781c01c85001c80310510000d40d002e64102010314006000302c12550040202a500039070050100401c01891840007034070b000c0720707500310b241480002800c21070164003181403041208001e0f103441c05145c9440325600d01800b1281a80c6815029042e0300500005556000000b00d81c04010750031015240e810541c41090342801d40c0c070301d422440311035101721451204000e1407424406402030386012400c40d03140c0400e4020750f452a00194001880e1010101c882000034401441294000220b424603491031082d200b004a008040c0701d005141d4a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 319871672 1250 319870422 319870427
    0x9090403030b1806090117060f180d05071103070e011e051206090105240105070c03080403080301030b1b090f12100608100903170907030f0606081b09070c03 69
    0x1541e00b00c0740608400d4090325001c1070b02d4010b10040300c0090003840c0071400006e0030906207600c80075029040c00a0300950b1208203c1e80c44862005140ca1451881c546810800b900108482c880640340c0341c1c0c4080e11070145143c2801c5441450040d5442503105175801d03c04600600c80703441c1140c60285806644a030301d100c501003410801ea1040e40e000c03102c962481080c00c0e000c501e00344544071050003004695111034100364503a01200c02060283c901e848104007550107000100a0301e07010300c40040c01705903240d84034001a8000c1d002143e002c3c41c04001081001040c44c03030650017401c289100e9082c40340200302d04409000340d124040c070480041002190603205d1080c114414a040c4080d036a81c1c0e4030600c103050107080c03544202500c900c502070207020503100c01e1082ca100c0d40c1d8103550f046002c640170010002e0044019082c40e2450180c8a400000121025100d45140744201c41c0424081c3c6040c40c010304028203615070041c001070726462820681d940c0c2141c15032180440c14803a51452850908 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 319872922 1250 319871672 319871681
    0xd0305030610110a03050403020405090a03080105010e060d0c031b0f0c0303020708070b010b031f050a1a04090606170a0504020d02041a03010f06050a210828090807060509060909040303 81
    0x50403c0c40c0900c110780d41c02c0c15801070042003503038001d40d000e202a841c1e1080d551764601c3c3ca110003a00086800005020641c0310b1003491030b00c010014481c1c1c0c04c2c4100010003400b100e42c3e040790000400da40c2c041001a542c11103030412601140c904003c40a00e64032040508641d8100300d000b402c0550000e1003108202d08076090b41c040c250040f0740b440c83e03581c43d01c0d001c081c617520070303540c0311212100785207a00c06071010030722404260340b405080c80c42c003149030060802c656499103001220700c1380180408940c1c5c2c0074512442005082650b50240340c000084011140c1180143c45c00c2c0c1da640c148001c00c80541c070380c0340603100aaa0f0685000500000001040498065141000d64554280328030480020200c0e0003034001e0b031b0811920ba80501d5600c50450403c0c007901c0a400d10803401108490000c40c0c07242003d0400c42807440344c0080261030044000100f990f282001703401045403d03900340f28060080042d04040c0603030341002c503d0244141d000659501643d0070031403143e22006c0c000740426100e17400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 319874172 1250 319872922 319872947
    0x9270305040e130f0501060611030408030906131208070b0705040509191512050c0405040f08090d0c090e0c10020712020609090408250b0403030c020c0306090c01020c0d0305030610 79
    0x5800b103401e03102d2409a02811f214400c0400040900c5043c1c000401d01000300c0b0101ca021000071498803000301d0034064590032114560000080e803c10000709548000c58890106108207416507503640c1c1341c41c00400c0000007520860800505001c14801516401203103600036501c624001e010004104180340a804000c103001d0003a40002000031301145280001c04025200b1019a40c482034208140812500111000791651203448911000700d5000d00060505450190250702899800c0d1581d841001c5a54001c0310100c2c2e680f0790b8880104024000454142e400320780240215220f940300940c0d41c0f41c0c030302030003014038110740e540c804540c2c50904032401420050180300c41450a401c00344101d07000100e012013061040d88200030f4a40e503404980c0f000300e034401741d10391300354a844d181200103144031105d810540c031170139003c90b005540802031644950714107802007241c2c07480c500009040c850840a120300451360324415400103034001095913400760003510f00c945441e010311000c8071000078048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 319875422 1250 319874172 319874183
    0xb0a1506231c0e030306030606120f0607121803140f0d060303020a1401020f0f0307050d140a0b0a0518060112090b040b0f0402030c04110904050109270305040e13 71
    0x80c400110800d5401d201820b45009001004408142d850f52500ca12017100d005506802160000b001441d00c0d02c4840d000c0c81400f01120f10810381d00c02e4061520130b054503140d02007404c04d903904442440d5401800750403c061303c10341c00c22800716540a040c003075245040301f51040340420081030386003003c1c040d03c1c01c0d802601c40912a03a5540d04010b9100c040140050b541e2041e4011841d00408050007159449080d1018403450712002c51500f4415401c050411400c1050070005c40249400c0e6004000244000c5000c051040c01d01c66610411203001140090107400b80070b000b00007681e038600800210320030600307229480303641c1c0c580101e590708070b1311709401581481e0101503418880c9088006206e14420101c200c0b89841d02800c035001800201e07002541a40020100c8440d414241c0040000e09240c045581c01c10303211030001000d171032090f0003c10446640e106490305010003842030041105400a14203450b40b5152001890317403099001e0740d030300000d10780080f03041c5604030301500d00c1c60381e0046c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 319876672 1250 319875422 319875427
    0x40c21120c170318150a020d06030206180f010c0302030d020c1507020a0302060a0501030f0201030e011512110d0c0621020c0309090a0b011d1c0f0b0a150623 69
    0x202d854803a035800035a50008256140c520300d056483c0002403e00c1070001840d00250160344d50405c1d20702030350041000c0c281c00d6854500020050712804060240d0244800107008100a0341050022816540e481e060401c518402d14a000c230360003104403120342c003240c040980d8840c40030741ca162030000c130101100c048072019010841d03400e0740442c0070703502680709030701781c1d80e064452001c6e03001519020b020103450440d03030300424401980030780d1081c442c02e5020030010035682c40a1400040108481e800205c044820189110400070128500628680c085407a680048220380764040d202c83c0710700402041c05401048080c1020019680284440c003500d405e641d10b03050394003559100e8104c5510791340030f903010310080f0340e000801e4000c2000e40300044e51003510b80c1190360041442034002d00613182c1c000c1c5000340ca04143d1200102e00c0c1d82464007035044010707500c9070740c07503c0072408800a1441088620b0002800381c00307000c1070241d800b00c44091034401c10718000c0c0c1d4007080500160021407003942000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 319877922 1250 319876672 319876703
    0x110412050c210d080c1c0f1503020102010e0601030f080315030a0c050405090d02060c0a0c021804031409061b0c18071106010b16050709050c03040c21120c 68
    0x5036940b00d8500380d0307a241035402c000c000a90a031401030065403104450f010a000e038a03406400b03442d036114810302000003c6150000c0c01404821181100513840c80c1201c1c600041c002d65030240a02100244843c0003000c07550700d540c5801c0c1c00424101c2c3c00801801000000c100502085401c902c280c00000301a10a041075629041c0050380c1c0b1407065902070f42c240310002e210b031000418804144140c94014000d140e407151071a402c04c1d07010301d14840600881f03008480241e2907081aa40d1150a14814002c96003403606014004030799000d42d440c91114200900102500d6080540c0e07180745050381948000c4514110450510071034500380d41c0c01141800b105422800249440b601912068440540c0400000101c1c1d03110b4900340181140142c0c20000312000380f0544854000381030056003603914081c2c4800e04442514019540000c26000100500c000d00540052180003441d0076240b4910352800f403188240d2442c42c0245c05004440300d0b40034203080340d0103000c2202d019a403020001801840303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 319879172 1250 319877922 319877959
    0xb0112060b0103090f080a18030804260c0105130306050f0f01050409110906011b0b06030c10020d0f03020405180a18020108041e080d0203060f0301110412050c 70
    0x8014800d40d038481c140028845594028401e82800300d421203000000e0701001d4a5000340c551001e606101003121412a0511145542500c074000c4c3d4411603d40e5036461500344403014110395003020400c050f09010300e1010302140010007191000003820304075103419030f1045040c82c082c0183d0001e015a0704100402041440382228a40714541c00c4102e00d040340d03208c00a20040b91500c01008100f00e0610204403800d142001c011540f00d00141740c03698010901d0304464101031039030130045a4500b224024082103140a0100c00792090083c0c03000314524204681c001c2d61117031252940014003c1c0c00d400304035524425011079000c0c090140403002440d0b17540f04811107005c3c007250032503e00d9140589804405445082940229405968034481038603240c0f10020a4100c81e5480b0303490f0710f156046003002410380c00140a044001c81030058580c9419014846d10303048220031240301340d1400c94100300c051024029941544c03180342461113081c40030b10b801da1426038400845030344800b00c2c6401150051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 319880422 1250 319879172 319879199
    0x1e040602090a0b0a1b02040b0319061a0108191523040204030c0e0c0c010f1d070b0d09150906020a09080d0f05030c19050c0f150403110304030b01 64
    0x714180c80031600030381e481c40440ea203400748102c1d501c000750b21510b601040e003403043c03050700d8100e0000b0400070b0040245400640340c000d00302c2c0d040403851580f07070381d610a0100d58458040f070f0b0700f24071a4144640c80d00d540003e000410090105440c0600003199901080450744007940c00410700c1710301e44425899801c10003681d44449251880b094600e6034001803802d03d8002e4804595001b010309280c1030900000b04070307002c001402003110300c0d014440451034000901591045c80303200355001400c403902040501e10300c000c4902c42e1500343d00540007000150400d004660f42e40c03140703480c001409011440c10700c2441c914125a01c4d44182080c00c1031050115680c0140340125558458040143d5200c12440d120b8520304601401300b8240092210031364000d000540d408440f2000c1280381500300b9500b5654003a007044000f001510105410402104c100718541e800c0c2280d00040492400340030406440c58001440202001080080850028008c1068801565100508000310b684034180d100041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 319881672 1250 319880422 319880437
    0x90a021b0601081c180302040c0c0c09020409050105040c021507050f07080d061d0406180b0702071a0c07171c030e07050405040209240a03110310050702030d051e040602 74
    0x1c107105202078004c5801030800300c801101c02c404104c0360300d2a603000c200007000307240b08000600c05041d0b030050000b400210050058220440c0050b1101c3c2801103280032502c0582065000b2441c20b21039440040d000121001078400c2002200040e0b0780c0c1000886817401b0301242c205040402150120802038410043c1941841e040020884182c0c0c4964400c100e121103514424a1540d40020401244c42c503005600440740b5800c14445140a0f5980c2d507007104000c440210040c0c0200b030003800594014200c50304050f00c0400210309000c0c5803100310ba1503442c01d04c50070a0860011403d112012000d00200d81001e800c2208103056100040d00540036040100e480f034000c2c020f6080110f05072600c0c1c0324460040d034014001c0b816607512a0000d03030606800c103940c0307030340d4a40d03401038030328190340e64aa403201451007141c0034400c180300340d41450301e09046118500541400c0000300829964000309440515400020200d82c035114030102980c50804a00034100000300ba108010600c6140c1d0001d1001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 319882922 1250 319881672 319881703
    0x303050105030606010c0c140d080a020105040204050c0c1005060f040914160f140a0314010207260f181f0f020c030607031d0307111003050402090a021b060108 70
    0x11584d58500460309103c042c280100003080c4108140320070624006003642610703015202c0c2e032180d840c54440c246d81d0381110b01d4100c0107070b4481c000c2108609150042079048510f8180340d50806c065801100e48400082c1c40a0304010740c0c60001910b40e9852811040d140e4030094420403041c1101d0920503040c10241c83c0c1c0f801e5501c58041c000062201d101c1d0b1407005c403400c181000d0011810107841844086c0b154640030350100305204c0210101c0c00301c2001c013810282c8440010792711130381441c2a0120100c41c1c00d4042c1c4520200d0b80041812001400300d0380e0b00448007142a903242400020151a820116480da0b080468922905207428000d010780400400c203480300d5000c0070000904a9907488440c000d03507015080000811070403802500714070f4500c40d640c0801015100c410000b14555003120009588914000682810301c1c289178000550f08800d0b45002d01051400d038004c541c0810000d040b00c00120ba00142025a0f00c05820384d200d1040c4200c0c044da061544e41c3c41100b0381e1250b140030803405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 319884172 1250 319882922 319882933
    0x2070909060b0a060203030402010912020f0301050f06030d022404080d02070606031505040f020918030f090a0e010803030601140702030d030c031d0a0f11060c150a0b0603180712030305010503 84
    0x855170f0000058901c00c40d130596030f40c9111030810171480c00e041801401242c001c06e0011b0451460382d000c1c09814440d0300c81c15074101003454414201407418030059020340643d0489007080d48500d01038603e40210200c2c40041e07242c1c42d00d45242001040c892540e045072964030100e040300030425190003100849005030146070b214040e1603c00300449005480c020885640b242c0b1907801030400661082d88280c11000d5400e944100f8035419013180d00000b0740d81050000000ca4850503d0802903003c0508811080143c5560502081035641d1001414441c140680c144d00b0070121a1284210ba00f91035000d401d0303810f020150340014029140100c1a030f00401d052512624078605d1640188460283d904014007201003680c642d8003618000308020b407105560b40383c560000e9203c04e0300038000c4240342d10050040f00600c907111041c03030401030410103038903080c845603509981d900804d403504110f5001ca03010f4004c1048280c20301d4142d02e9801119040240020308042c1a05540b03da030403141c06809a96 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 319885422 1250 319884172 319884179
    0x5090a1b080724030e010b06040e040b0106140301090b03031905070b0903030603030901030905070512060702010501061b0305090103140c2107020d08070e130f0e2b02070909060b0a 79
    0x101c140c43c41c41480810034080071196075000c0d00c01d811041000781e0010000a40c00703542c00200e006580140c2001c03010303a80720000c1c8005c20000e111024010980d615015001003158030740c1d000c180c0301c1031103104203c40e07c0b502048166501842107601041195440210b031040801c6d0140c103c0c2c04c41882514000a0320700002e41840002c0b08592007050002c01440c500101701c0c0c01034005080d00c0d101a1614030810350b010800c2c1d1a4540d89142c0c00034400020000da01e01000c0c020300f5954160000410000c004c0d081000300101405043e0349a541030070b0032501c0d00c6010004034020309024240c1405419a0418010b40140940050500a000c6181c070183c907501c8030400c10007004c0035642000103038048881101a10321850f0265003007840f85c43c01d10086004000041d01900c2200d8030b410400c3c1d03030b44054900303646040c802c42088a00081c040c0105200311441181100602c44414569012401c02d41e80054800d00c14880648007440007000705010301d0501100800e2652200c0c2c0c080c061800010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 319886672 1250 319885422 319885439
    0x601020106052b0602120610030605090c07050f10150e04020906150c03070813060e0d14190f031412150d06020a02060403020c06070302060a05090a1b0807 68
    0x54800161a41840700440154000701d50040407010201459903e421800a800b03400100081410201c1c45002130804508001e0a02c1518040340c0c14103150034010841c0f520354a1451364010000b5400a88030852410b2550408991100008981c002c2e080180c035455004d40c08100301001114910391502c1d04e035100d45005080070303a0080d6009003c600098001c1c501680c0030042040d1440d416818036101000c403c0c60740c2c201d0b07c2d00716001c0f000402ca03d10304180e40343c02a0003c2c00c0ca4505017002c010403201082c544031800c100545440400030350301902410030050356034030500c00780c0304460441103400d03d9025000710b82c1c022000101c0600055000c024003e09850316955020312070307c0543c44401c410107001c0d134814140d6070809815030007880440c0c0d051010744100111a0040e00140c07030240740090a0010140300b0070b10810301032008002282d80010034a07400380d00214005110b03210b51401520b040b48528000f08804107902080c8004a41880c60300c00b02c6000108445c400f50711074108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 319887922 1250 319886672 319886681
    0x140901020a0e041104030506010f03031d0d0303110c0f0606120304060210020a1403010b030a0b0a140103021b190302010501080105040f020405070c0606080309150705030307081005062106010201 85
    0x124000039031000e10700b00e080c0c500356015424840c11a40342c14039041d642d40d40e050820409034085035281151140410525801079141d48480b50b01104185c82003030540c00181c00d1144044014080654459042c1c1c03654000303204555180341d020080f40c020700d64402c0003d42e580c0045070281c0c02108050980d034a246000026102501d0b0705402500140450344400c1000f508592000e5041001041002c000b00413540002c501810014844c146d0740d103481c00100d002e5400c0c07a500c0314010703208004100070071600c0c85145030041c00d00740b070050713620291610b100004840319141a04a0b000741100c020300200e0300307810038249521a0700203100580e690700300c860807620126000381201029507d00001031034564001c40d80003400b03042c14100081c1903100c0c6411149190403280c10395100241c01034081c645203d00680103100d05002c0c40c684001959416140c1c00081c00703050600c044040403403c402c03000c42c6048003810000c0c12050310303080201d45800d644140c0e8807032600c0d080740110119403d94418001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 319889172 1250 319887922 319887937
    0x1031e080d2c07060503040521030106170c31120b070e010c03201c0216030804090c05040911090109050d1703060604030c08010906050609011203030f0e0607020114090102 75
    0x500f0320300d4540042503403180d100070400c440078010b610556001c4607512200c20401d4000d2465591a903040810160100092007200c40d0700300140307400c000c50007100500312038840d02901d25281c4da0009a140180701103441030030070103880c0200c10010404110503d080390000c0e0042003100c40b1074a40010513100c4a0030014400d000506460021003c00d000382c00420415000c1c220400c0d09441c0441c54504220795241602100700d40503495031200d940c1000407900d400c68081084100d02d11355620701004d885030340700b0402e0407511400d4603202d95001c0c3d000c0c0d90040c412980140300c031140c0b0300c00203143ea41c131072401c030b80c089200c0038004034a90501c0303100d1280e8640c0c4105012540d41c1c2d40301092889810050210740c2c440c030100000300004910004000c000c3c9113560010a03201c9130740c50103030150b550044c9024010307100d200040001c00c40d00201c1c004426014140060411801c56564000d0151400c10380d400e1700c9000280411290305502c5408030010461108800d038960b41c101c0c0e4203034892041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 319890422 1250 319889172 319889261
    0xa050612060a020306060912060a0608150402100203190c1a070c030c0606050d050102040e150607140120120702010507020703110307050d03081f030b01031e080d 71
    0x1c00050300e04041d030b402107030410070061480341004903500007d00c8814021500d11815040b240500018500d140149000b40010001600c2d4a0384c90728580340b219400104007901c90000e810b5103650080c001d200301ca107510f200505000d84001c0b040742c0502018081c13082281c45240703000f132003a91502c0000c0598042c485a40d50012507000766101155032071842c0200782c2d0781907a80c11001401c0c0e40c807540001c03000c612860025848a15241d00320a107414010489802e100400c43d44800d00d94406c411196102e0340100882d401080b00503445004045104103030241c2030450b9070003030300c1a0b4080c001c0d09525100c410040c141e82c0ea048012803c5e0780040c0c407508056440003005000007001030103598069080036080701c0d14260b0313400c00103415004045082d4013045041081c460443c840c1011060074001c09001c4159003442c5603204012503105200c05003001c00e1807415104069480f003904134406810510341901e60540700bd0010007014104a0754681ca00da4840c0402c0c8045404a036110004181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 319891672 1250 319890422 319890433
    0xa11160f06030f1e14061002030406080a020c16231e041103070c05190320010f0e070602150115051608041d01081c030b0310060e0a050612 61
    0x400241c010780f440c034078124600c0d5100d02a0084512040c040c041c14a1451080414542160070300c003015403002400e001e020b072100c00c610aa0741a0000104c900b102c180b8601102c0c950794182c5030364000e010b610304400442c02008420840490106c00d884151120300e202040c040d02d01880c5002c1c0360701e01c111711680118902d41410300048807400c042081c401c018101180744164101d584076254022244140400c20b5120a03406001e0100461082c000450135240c59411594030040c3c08801d8681074901020040805800c0901007900a040c45400c191818009416040c2426440c0c0c501ca00a00005200c0e03078101400090f034849915040302c8000c4403207502d23484104022203241d8071110048020070007a00c900d4001544842c014001054812171884420906040e02c1005000c10703404008a0752041c10a160b40c0200211001b14074907690034002103244080740400d080c004580c0d402040c5c20318020000500740d0b41400078911600f070401082003680ea03443c00300406203000d609000c5055104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 319892922 1250 319891672 319891679
    0x70e040204111c0c052101080c0105030403082706090a0b090705060d0c020c0901080105010302041803081303020c030d0305250f0c030e04090302030a0807030209151c020a11160f 78
    0x200d6000101031640c0c0e02c2c1003840c219070101660031809400c81e01b2682c3c01e504100400040e2024004c050790b401003441d0040c81d60030142c03030040c8800800b910324071064842d03800c0b51078208611240d4003944448001a10042d1401b02c5107144c446e008200140e910500400005160a002141a0b02600c000901c403e0034405600d00c0c9030014050515141c0551003012508040c540c2e8003401a03008150340c000110303a071345c158818001a51074105d000b01260510b0809003000a0b0000d80180d400911242c2000c281e00407401c3c00c910303208822688507054081e2101c0305103031b40d505810440c4627004440d50700c5081c00c0d60051844950b511500c80000040140c1138544a0600c00d00398484890300915143c2c802e40b041c80001011600c504200b100580c1c40050900503140c0c002d140181d1224803410114100000071001c69a80140c90300c90054880c00000c640d91942d290100420140c04620001c540f2100c001754064241004154007510510841441140d2502096410825507009065802c2510316 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 319894172 1250 319892922 319892977
    0x30822080d272309090318010f1d150309010209030106050f0303041806030602040f05090a1a04090f14160b130605030703020c060a0510090203010e011412070e04020411 74
    0x203502842c1661000c3d0100940c3c807603950250990080ba00140516620701d404004001c0d180394100380d0394103208243c020314007034641112502c0c0440c1e540010b40040c0700100302c0090500c084801014416a0010080c8000401c0550151003586402c1c0d0007008544d8498040200742240c868001d03074180d0040000b405528a1031084d02410402600c0c0402c0150f16076407140280e8022360068966010640c80402c001e00d0105001600510100c00401c4080a103115402c42c03a05035020340d6019035242c4410341c080182030140c1184d070a40040b400b8003040c4074480310503115180030060b80301e40320003134402044612500c2d003142d0160402540c0440701911b4441c040d95150070040c40001410707401c1c041e10038003403810311200c0d1050380b06190002d40d515210b405c0c501c43e1880340c2c02205e203182c4140f006001c1408011132950640d010020601305030003007200060350030706600c81c282ca0540901980055261280085640560b20031a0284680410325000c1c203050301903542944c1444400d8401d8208018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 319895422 1250 319894172 319894199
    0x504140a0e1507170a02090a29040905060103060503190204093002010606110a08030a020c0d020307050d05090d020f060c030a09090b0307030c030822080d27 69
    0x500340c02a20307022441507442120041d8111109800300d080801d4144d114441c0d085040d5120311594411170401107010081002200c2900600c20142801300e0004d85030100d401c40040c00e24404c040072940c4640325050383c00a0202a40c00e2804641021008546460041104c10501e45142300c10307a85140d43e60200030240003503810035191940b1740f0201007040f484894505400301c5110150700c802d0302c1311000090844a00d50300a40030010390582c00b10119401080e11440b030b640000b540e80c0c59486103e1100001c0c1b14180950b0600e00c24008a00e13160b03600800a059500c0c014401d0390038140075050181d680b4803400400e55409110007c00800500d480e491070b911811015090f82d0405035110750132491036010707000950102d004c1c441c2c10807a203017883c0540c1907440001d5015000042c91980c401031341e13000034000144020000708003030500c1e00803007064911208042c1031440c0002d9480b030010340c039903041440c40f0380020114105080f10585000b80010718015031603a00f0031152900e2103841848 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 319896672 1250 319895422 319895441
    0x2907081602040e0c010206010f05220e030c0f011a1804050c0a060c02030f030403080a120b04021908090109050717010204050411040806010801052511010c05030604060504140a 77
    0x30424060120168440d03100b100c00b07811032003006100150414002915001059010320490040882c1c103210a031201c601c5040c0d08070707401800c80444524034001d400a0840900320f50380394400420b41d01c17020b010002d80d0301008003415000304418140e4051070003002840310082a000646201107414030310800603096845401001600d0701119100d0000e1070014047d448a00000d002c508000291b2805105004400c81c0c541c00440c074003855a5980c5506001c1c2049082c240806101803145160b002d4001031001d2100030421952064041d4000d501031214410000004a4450014103071420500c00c0160564100006000c2c16241c540c1d004007440c0b5a440d519200e54091000046a07162402800c4140941000b15034540c2d06001d813062501005a20000b030f681e05001c10301c4270140c5c000101100441d0301c204407013461103140d481030704d444010140c00001e540c60320220703003101070b03104014501900041310140a01c1e581c0b0410441500c21000c03810074480c0c03005c00401c200300b40c0d80c0c1c80300011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 319897922 1250 319896672 319896697
    0x90308070f020d0b060a06050c0d03050603031207021f0e120310050612070f1e0806120d110f120301090b0d0f050102030402031009050c040c03060b0d06290708 70
    0x44101c0e6000c2440030f20b8004045403280502d0003405040d00d0244000e00203001d02d454400c1c2081c07499481c4a0b519044201e5000505540e200460f10300d031401d104544c4d07001465131082c1c1c10b50802c00380080d5510143e0081070105034000c80303400322890040c00f40020344100000200b8480d40300c0c41c40300030b5542c4080d01900c04010090000515525184040d0418040016091415103002e24019140c0055030751200108001114440c80c0d5000b0140c12034100d0000d490110295560000452903d0210b003d01d041d0520070030380f00804466125403a8a40588100d046c0c8800003018054680e5035030010203640000f6809000500400205910084655030000c02030401d1100c0c3d40c4506a0f03035810100305440a1350000201310070350600708071201d45104451010010a141c9440340d0380c0764050030094034803994894503070b0030019120750810005072200c105896912040a074428006100b903215404840251110315080406c1c0c0d50440d244403001c01c980245440701942c0d03803510640c80804103054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 319899172 1250 319897922 319897943
    0x20040e060a0312030e010b0301110c190213020304020f0a080d0905012f01141e060319080901270914100b1c05040f0b180c0609150a03091406010609030807 68
    0xc01e40d40901558ad2824000c8011075940c0802d00e880a0070b0103003500600c000003003030000d403100580301e400b585e0039012407040300145c8a071540d04c0001c05060320410496845111300c20042403410001c81d080032080416103413003030516030f40c0005660f42d49001c0100802480300590359040e849403051800d1100b12035900000e4444203000d004c4440f85420341d8a1051020300b2540d10502c20b0301e070104d40350000c030128000c20258400d444100600900d820b4001c1524001040c3c590060b40155a1f8030030045280511500345195210179080755086849402e4842e81444581c06200c403100104a004924032a82c1305415410a40070201e50780c44154600240060396007031650032801c604c80c070b900481c49400c120702c071500e0f80d08040790814070140000307050700104800740900350000031702c6c0030381c4c40400e40e44c003070700c512940e4001014205032500039800c109002034400c1e00c059041c1c1c01f04205600c43e500399441d000340064610341d600b000f4080c2c030020650301e51301400072565400241c0480352085000f0385 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 319900422 1250 319899172 319899191
    0x406030902030a021201140709080601051e0405040b06011205010f1e0807080601031a100501030e0a0606170607021f0f0e03180f040b06070204020a0320040e060a0312030e01 76
    0x2e50740d907a0a03100c280c17943d548642c0e034030440c2031b4003c501d5040706003850007641303190a100040c1e803500307018840c55104921031f8452543e60701c101c144007000024014420404c80c5040d05200d180640300310f5515000806900d6020300e400814864241a03498900c01466454103018080d41409100c8010596801e8131840c00148260704206480c090100c13540904401d52540c41d10540c5541c1e4900c0d0b54007400c11100400150f80707102c003880000ca0b0002d10b404144c50206124240c117140c82c0c40c5003d4034903814001d000c5a840701e03600d003c550b000e0002c5d088031000d66803010201e0302c50000304000b2102006040a0000c0900c03542c00c01c402c20110060b0001c0c6048121030380602d1a0311000c19a03920b4040b08990070813518081c00e013820b640100380c170103000d0288403400040881c440c03400001c0c4200c1d8082000030625101e0f90202e101200c0c2604030362861030b40740b07480c032500760880c0c403410111900c4507000a01c5410030142440803a58050020181200070100550203004c1c902c21821141d9a28030f04803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 319901672 1250 319900422 319900429
    0xd0204020f0703020a030810140d0804050a06090e010b190c08120103030c050d081b0f121f08010614010f14030106050a08060d0302030418090c09050109200406030902030a02 76
    0x1d20b1010721039001000d03249401c0c60041c10100e001400d2040382e0038001d03400c01a015480306c08481c9010111403800380522541740c806060300882d0000ca811010008000c02c01c0c98103d10070b5402d50f122401e00c595560303a103000b160001d02c20319442080c40344511001442050103001c0359000144152401130820110a00d0000d0504090f80b055000413601c0070f800c2c3c14410203115000460405143c003c600e490000940f14a1a07400741050303507968000602c004801c08581c0540701c4441f00069045420700b89041c0960b0342c181030424181051608020000c1c039600c051144608440003200c01c0c4024120200054603540b205400c040140070f040f298080355138420030300445c080d101c40d845950b1a66940800100850801043c0f81c0c020581499414042034002054500300c5002030098080c1e007000f8951b6130042d00d04014010000e100d44078020840003c6500f0aa046e01c803130000030031950300000140500c00c0400b081d00320f490780c000c02c000e05c0740601c05d8204980060014040f0351400e5000da010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 319902922 1250 319901672 319901677
    0x6050a1d04050a06171513061b051e090307030602090f0909010e0c01090e01031202030c0f01061401082505040506030c0403050d022410081504020306060d0b060d0204020f 75
    0x1541e035590710300380305200d1791900c80110360180100616802e04c1504120f0034001001e001c4071044040f907002c1c08100070580c1c20014442031131541c52000c03c1029030b000342950308a0316244203451480800c03964105e5000d01511003420005008080c440d155032110304c001d5000ca54404d4200c81a440714603103d403544540079003e02281000000c000a60600d0142080040c046507810002c0c401410002c0713000160045040d00c0d0004100c00340b203841d110f816465441101031409041c00740c41040190440c0640c001340407100f00c600c1c141d120040690045a050104a035402d5009003031482d07403c801c1c08450945003da0308141042d501e4103841701c2c0050800d41040360b100303007049000074080c820040203210b0a0303220142ca00003440c0800d0303112081e20803c4082c41a000c4031080400003d201001080d03216001010f41c5400e64001400440c0c030391841c00c2e000c0f50242e00900c151000314003036007480c03520010850b4101c401c2c056151903d604004070030080079001c0c8c1c0c2c03007030b020b001c100001c6842000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 319904172 1250 319902922 319902931
    0x501030309050d152c0c040b0d030e191a09180705031512010f0213120812130b0106030207060605100f12021308070303090b070f11030703150b09060a06050a1d0405 72
    0x41186c1b107030000400098a581000c207500541d071814440001a400000030b2180d10b81c2121120184d80344040401e5441c0b0035a844000703803008030000e040c08048600001c01d004641139405001d4071100c82c800c052441030a503441400908100001014441207401c3d918594000400300c5080d821a414440d003540c24000e81074a5442e800500c14800840300c02884000b000315080200b01c10265032103280b100e0140c403620115100034140040c84503586807007000c10051380700041d0301c40c40d40c50b150014020340010342c0484449140250101d43c6181c0101c034084803841070b64504146480300c9004076220480a032400f00080d400744148084055420751040c060b00e030030001840034628500b0014112500c9602020050800b0400310010802003040021481e17004480f0f5412460741c00c0c04070740742070250b600142c141500100181d080075015002140040c0c0101c48903003080d00c40100b00021949030748190b10125a00304440c4023154001c0700c1142c85c010004403840800f0303090501003003da41c1c0484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 319905422 1250 319904172 319904261
    0xa0e060a081f1a01020d080a090c090915060323030c0d0e01090b040e01050f06090d0b010611121e070c030804090522141905010501030309050d15 64
    0x51942c02c1d078926511450100b030790810b801d0507801c031050001075150790100707a80d0380803c5401d0002a501d14440e40101e002c15031301076000000c035555050f03000020580d01004440c00c0c0a00c040c03e02190b001c1e800740c50152508403004518004502c007680000407007403d90301d001400144040001da10061140c504505090740750748a03031500c503400040c8601d290b0380005054007002d00c028480c01d041c100525054400076a000340742d03a011140004c505005410083d94003ca1802d003e208100c40c200245040b02c4107511440002c01c0c00b200da2944459016040d0b0308000750500c2142c0b44c00703d8030102400403016031150135140c0f110a13150420b1060082d00184d03000c91340001c0810200c0d041e0301c40e540c0c0c01450040900b001210406241d001c02d8184040900885840042d5060510f03007400010715501b043c0784c42401d000b20b140f2340786028010074403083e4081a4955400900780c2410521a91100e40c09101007400313182d005e0a0390001d002c14442e44030b464003907040c0305001c5920556490844000f44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 319906672 1250 319905422 319905463
    0xc1c1214060a1a04141503190b0315040b06040b060d05010303020705010915030507020316051c0e10110c0607030315090b0a0b071704030b01060206070503060a0e060a08 74
    0x108144089044143c0c400464403a0980b40c150403224003009840590349065020b00380e14082074000340751b104c0008607265402a000080c094a1100c03401c0c0c05500f009207120500a04105070100368590520700407040c42c1e005280006000070300e000e007403560300040040c000611641500c000c10140d0f0003042c007404405179104014018160104070880c01403000346410081c2904040c0c083c180b80100040700300c06e05031580b0200300c02d980248261401a010f25a040d0803260032401e00d15034560386640c4039020403130b000c21513081c0c0a12508003040c2c0a18003400104000c40c1c064030465441285c1c0c5840c0d2801d0180d800c1850030b554cd12401040200c0c0250b401140e4050490074142c11100710303600c6008082d02d851703030f42212512105501c02c225070146034065181d1a0901304038502008522001581540009000c000c00c494024030030305a681550072101030341d032030344c1007600c2c5c03840b00392080395101a00300780400003060381070302c0d80d03170302500240c4880309490340c8060710f074035105407401a0241c82000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 319907922 1250 319906672 319906681
    0x70f0506060907050406081503120909011203091205011103070306170a030816360b0c030711011205090d020c0306150913120f030b04020c1c1214 64
    0x2081810781000040b03680715003600f04004003070b00c0c51003144100f2045c441040001181460314400d0703460914000b81c203840100d81c0700c0c0040e01e1140c0c01020b81c68447c01c038401c000310b5804107014501c005140d1640300e84100798100240911400420241114151b4803182192044c2003400080c0d1300070102500d01140c01403d1600010f5060381350034005959502030240c541c0031a40c48510355030084900d00e6204403442102800702d400c43c203c42c00c080901a8070040848051840100c00721080400701c814074400c0d0340f03e1061f80d459201e0003081e1540b0354010320085000c07031f13100700541e5515207050410400318802101001e040e10000c55043d03056400c5045000043d54040c0300884e25404101c01414962901003000050903003072403512800780240c0e4000600c8041d2a00310742e0500c1e504041504010301d2444401814441050469800241070050100c15400c050098940e03001e6206e01612000c11051182c0848424001e07a0788204101c0084840e01d5420703a01c518848100b1a16100c1c280d40361 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 319909172 1250 319907922 319907933
    0x270222060e060d0f030302030615030c0a08330402160605060a0503010b1c0c0b070605060301230417091e03060c12070509180702010504150b130e03040803070f 70
    0x1000700003e00071903280003034400044e550016061143e60504005860351240c0c004204449030090641010308400024032280c603119401825007402e290350381c00903503564001e40c5080309001c010060803030341c0d9540c011100150005454030307807020064001401c20240c6010002c4850140a0541380e040d0307140309001d070900b0300302d01c4030300988000c3d4000d01ca1294a20003148010f014880c84100010500c0381280c10450b0300c0c802c010090101041840d1211200d080c40300040806903030891007586410300c060314250b00211284a164020300300301e1190760740c0380c85107042941e800e01000340001003041044015039402d803071004040c03201007401d052501202d0900d0b01d810030290031043d03c0c90052103141510010008095400001443c1c40c2d23440b00100c40c041081ca8a02200c9010480d001e0420041c20b1a41503010520035801441d544400100d0200a4011908241c0c9580d801c4a6060312515a00456070042c044542ca050202e03440d1954903c2c40f603003075412203c012104181d41c816843d0610a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 319910422 1250 319909172 319909199
    0x60c15020331030f300209061c0e06040210110f030d091b0807030f140307060b1903081b0a0501050903040302090f0717060d02120708010f27022206 65
    0x1c4c903090440d09445c11018041c258044040303500710f030350000302e00c4001400190f0196451400040c194070340301e1001110b601840c181072655a07034002e2a003103035524450000512103005980191107a51030841d900c0d401c58203030101c40e9107070035240320303107030348003078409002c000400c036078241390000094111480c58645200c10000008020b2191114001d219440c1c01280c0882102c1e4440c0e02c40b4103089203840c010035031603514000d61710766003c003060350300c140500b640100c03400030b008888a8003006516100d030080c0d000680000b601c034840c00e0008203100d175403800115400c16040c508680c8040819a503079400d44800301c2c1c0d4084140c10101c3c082007103003880341485820500c00d4507181050b252803800100201458030885029000400200d07802d40c80301c1c86604c4619401500c03902c0310039210740202d50f84504600c02e402c0150703c0c0c400001c240a20038860510301c6030750030b222260120350020700c2480014903071600340d0b4090b040d442c0300b14441d1100810072544440401d0003003006031a1890710300710760 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 319911672 1250 319910422 319910447
    0x406090603094407031e0e040507020f030c010213051f0305040c15030b01021c0e0f010215010e0601120204030f0b1b0408010207050106060c1502033103 67
    0x5414040e5100008908008080b001d40c450108021841410032150800300041407602440e4080744500210030588007005100e4039010f034a80d510451b600f1300c800d40184202c2884017000840401401c0014a0107801c4150040641d20480f42802100203800c1e045500403004608660741c005640c041c03400d180d1400318000c0c0802c4820307010a00400313201c60f05100c6e040301050101651500082d0801061810301d0b0054500d1592003e520041c0f0030003d4010148502000d02610590400798a0950551348940c0140241c0c1c0d0b030700780c40342851000e100c045404c0201607419401903c45a044000001c81a85d000704003040c040c200074100000090000100300d8607100d010340c0104014004110b0056468040551001c0e50060039030391112222444103000309400d0728840b00007400140b80d041500944200780c0a10002c00c4865521902518140a1048014030341c800d80f18286003217240b5a03001c4c5511a11104511074502d825400151003403c0f4044141e500400c940040782c2816031000007105c19 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 319912922 1250 319911672 319911677
    0xb0c27120d050703050903120a12050604110904020306121912022109130e0312060a030309060503040609051516020d0917070e0a020903060703140606280504060906 72
    0x70035010300010114450070b0000f40900800144c00c03000ea403401c020b0386078562000c0010070340b162624400140080c000314030895081d418072011806510307080c410030701342480401c011407904041740300303101c040d400007091254050380e0200b46020a010601c202c0e04013007502c0d07020f42d8002809203405c40c40154001c02140443d0301078100303950f91405480b402512000140e52281c0c590080c940021101c100340540300e040c05040104400284100001030305c00030281046007e0642c0d0b8540500100e0351062002800242c64601c0c1003240c0d6000380d0085401c140075400104440015440303940c03074004407a1b001510300c2003020811080c25004043c81c01c120381d16102600c05440300140003000c3c4030039405061020b00000d1141142e8060401004004100c410b0768130400d0728150958200a420070790502d4024090b03280004c105900c41d11407070300100303c1c601c2600035940742c94003030007210f4004518040708145104c0b500f01043e0301c51403140c412000c00380c0c2c9040c0c0e40e5040010040c4422030300c4d0301c210103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 319914172 1250 319912922 319912933
    0xf030b0907061d04110706060609090c030e0307020603040c03060e030306090a020a270806010b04090b060313060506061c0510060c0b04080c1c0c05011401120b0c2712 73
    0x10b0300100c61001880c1002114085174001038514208220710030500700801c3c9034508440000c415401c004020120317400400b0420844003000001c0d001c9d12081160110650800c0015200600c2d00e040035540050150000c0300110740c890f66540200c0b251052911107642c008410010b0502c1c115104036403000c000401541000f903812800b070040090074512500d1110070302c00f0342d1000c145a181240c001c000d882d04541655032b690402e400d00354403602805041034100304000e20306003040d0084038010800c11006100c00191a04d4440c000d11000d4610f40d8080020072482c04500380e1281d806d416400301030b00004240c141126103080002c16503000c1c605005900b40c02c800400d00d00740e004c1c0c0d809904401105d0b80e9200300c9001d40d04221070050030380038810700845030024484d80004000340903885080200031041510000039818042413044200c40c0c80e50400724400140540511a040001d99000905158802d8103501d9040e26141e01d00c0c07289683c400300280c2500d86a10840b03d260494000b230003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 319915422 1250 319914172 319914197
    0x2070b07030e1c1d03010e0304151e0f1e0f0302090609040501030b011a040b16030e03010f0f06090c02030901050a0c120c050c030606011b06060f030b090706 69
    0xa2488000c00d444289070ba600040e01e880381c801c3c8140312031005207580a903504188600040c210300c1c40b1100143d049051022143c456080502c00e50000401600003903082925003040e203079098454006060030856a41c0d83d203484192501080960780c40700e074072001c0c1002c0520710028091070007480c1c2c000d09000a0000018002e401080e86400b404441c90050707a1811081301003030f550300c607003a5403a0b0081d140100000511462282c514143c81c160380141407140319204610490380118020310103111000c01450b04108601007481c0c251900c43d08107003000005200000742120b480500f400219920f0303500951340c1c0302c0345e886030802410007610100b101d6906104001d40c0d03402488000c42c1808800201020514002c650401956030310817013403001c108d0900740c0148038007114001100e061040007a840064540400c4c11841000c060751040a2503900d419854148030f6101e505440c02130fa24000031900b4140108210b001e940100c0c19001182030034141941303403a86030380c4043d01f000b00d03100001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 319916672 1250 319915422 319915433
    0x14101a12010c080106050703090509100e090a0201020606211209010908120f070203070e01080a0623040b07051605010b09220204020f0f0c070806060a0803040e15100504050906040207 80
    0x1381034605515200ba00ea40c064a4290b0322407190743c100e40d5114400004000320000070041c1c0380300f0368824040f00c1e2505c1e102e0075801da54810611400a0168108c50001041e604100c40c60150314111004203100038110400e006061101a0901002055000540040c1075801100101c01407070354400034110480c4c0d6401c0d422007401007486043c0e102e5800107604080d503508105102c044c3c0848600c0c05065655a240300d5510800100b0031070324a400c6c8003015a543d0819210350313501c1c403a60501c018803580c0c3e941e04e01c900060000c0c400000d20809024490507030b140e4103190644180328100024491010034100700b42d0120090680ca0100240500500815400e0b0520f042140d070589007d80c45055000f078a04c4140601c0010a03601070010030050001900001c010303080b100350005588464980005100c81720450740203044ca181c1c0300300070030800100010105a84031440b90b007000c0c000003c00000030155604118007034002540841c0078402443c00b030300c0141d00164102ca046181000590305d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 319917922 1250 319916672 319916687
    0x30b030f071a09040902030607050a03060906031203151e0807080607120b0109030f061e0e120702030703080316020705091003110f040213080c03030f0714101a12010c 73
    0x10100500b00480c2e06003807615103030080e01038240d005043e03e5561809503001001c6401c5000c40100003400d2000009840c5514480c1400781d0781c00406002081d02130000c2900a0415014040c00a04032540005203104204480a140044941c80301e01528580181c540c0741000c03076042040305400c00342c01c0c4145240c104000601c5040c1c5d42e140440c0b09038441c0c006172081c4a07103a0000e01080780103400c140030085298000300c1003240010003d924003030035140b000202d6583d12010b07002c540c00400d1b9541c3c101402e83c060002075200800f1100c0e401d0b1a40c0d0b442c0e0f420340050b990003244032400a004040340340c051000c240a41030698883c0d50078070f00380d0100320682506103c06080d030725490020b046240c50710041610803540c00340055545418100c1c011715031082d1031003014007600072034800300f1039450f012040711034281c0d00044a60400c40151511510b00d40c11488240c0345d07100c1d2051991652016014110703001501000120f44d000306031040c02100e80724409445980e9240c03080ca21030980d00441c1c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 319919172 1250 319917922 319917959
    0x301140d05031306030f0c0908030d15030804030b190905060c2101030c050f1504091104030b07090323060c0f090a1725051012020a030b030f07 63
    0x18500c40d55003032810240e00b5481110090b880d40f101221000c24101d41542008400101d0070108010148a9220454403250603018458440e0000c0105155210007504103503640f1988001c180d0303040743d40b0350385c8242e5940680d10440ba10004002000410b00d01560088019190b003401801800c0e115a68103803039810040c45520341c000c0119601c1150b26940c0c03590401c900c0c0481c011070b00c0d07507124182420450303400d208580c8984130a11816980d07003042508503603c0070400c0c480500b45801d00b100300e009805281c40e05524100e0038080000800d480441c19801004503071140d000b00c2d401c60a040d00102d20000e010308000281c800741005c2080c0010b4020780c0660203068654440400031600180c0380b06840800e03500c4010034501240403855a420a00740780c40381c0f001c5881c2d459030000d803000c101814088400100502500400c040d090500c02c0c265040b0413450f141c0b20f2a9400d071807000c100d800c41e043c0400041c0e5079180e1720f0010306042202c25074071108003004180c480d143c04c1c0d100158041044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 319920422 1250 319919172 319919179
    0xc04030206030a0f09240621050309090406050a0b062502030c100513050102010b03100b0609060d09020a060e0a031e06050103150b06040f03020607140d020a060b0402030114 76
    0x42e00c408826400740d2010301e00c1103070520115201b4248880010f81c10300e01040c40c0807650140c0092100340c2d119503070403503800b11b440381040da8181c0b081d1030010b0500366059035540030420000d401d66540c00110f07841203214800009840c00c0580903a4202c0d82254521070040030200b1901c00071859011126541480125078284020303a0b170b10109040c0802100b0b9188c200e840307111421301d0541c000005d046100000f00c086500680d03035000482c03d032140300720490707010303009a8460b81e00d006040e088440110405040b680c60112040041660341e40310765184030440303a654013a10114074003142224010000d9260807000d0800d00f400082282103644001000c40118070040480c411b00c0750300c1c0c1c062054025604014540c5d603418003241d85840c04403d0b40c0201c0ca800c21980a502c1c1282c2981e0940c0c1e900510881403a041d60b003071058aa102d10016140f010344004101140c10007046034075200a01030b13014000140e02032038040c042da43c0c2c1440c1075109500520050010801c0301c20200307090b81d8120f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 319921672 1250 319920422 319920427
    0x5010f03020d060e01110a0813030e0d061e0c170f010b1602091e0903030106080a0b0319050c010e040b060703031e0c02070f090207032f0f0120030c04030206 69
    0x107252100040c0041281640d0b05c0d424042c20440644404018040c03010094484000655440001490210450303400402040020303015410500b0040c0c0b01c02c400511a04000401e21900180c0c88000c0c5524645902d1142d2601c82c030a120561014260103450191045088682001520028601414020401e5111000c61419918040c400440c0b40c140c1e00500103000908000c444015029070b08007588040c000000c002c0b803040c550000417a4102c0711582d45081141d01c0742d12014003d800d546054903450312840d045401003141c002c91202e1450700c10070050411513096400074005202d0303940e200d0300c03940c83d040780141c094a41100b200c00803030f49458001607007405c400041d0384c141010100a0b0700b1034a0300392441c929640000f03000d0103945484120740310f0103540d02d610106900c140c17000240001d02c20100c0905103413040c0c5500843d01c0001081030044010a10b042d450541c0ca80d0380c41401d80e44804403c800c9402d1803c0512118002c0f60b030042c91807420808402c9184034510000f40900e100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 319922922 1250 319921672 319921699
    0xf0f030423010c1218031407080d020312040c050907020604110f06180402041d0703110901050a080621011b0f050412030e040903020c030d090f0302060c15090601081005010f0302 78
    0x1100c017041c1180381d10380a0305102d42c07203050003040c0c406406004104c07031280a101041c220340005003e4440040d5900841c5030403000c030700d40074070307e180540101d92010051b80003091aa4404940500c201c0c040e90041901e490141442c440b501c00d181201401aa1440032444458903404201c880740c480088d07006285c0800d03003021600911541d800313061001494401e4400107441103d40a014042d42e603000d1228090f007040c1c004991080d104518041b2303404000b030322001401380f025280e20010041030b10903032240c0142100000208010105001c1c0d40d01c102d03100c80080c1c0075035900050070240c13603c4d866010403804023412500c264003410307a412005103220400c041c41840d82c484858000f40c420b000c0d186807403030041d640708040d07003155101c0c0c040c12440c80782c403500c100c0d0300804442e40c010000d10040c1ca0742d003e1110640c4610948170b0f541c010145048411250300e03030458001c0440200504942d071400c000035080c2400b003040680d2107828140108155480d03051a070050305d80440d00c0b545035055 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 319924172 1250 319922922 319922927
    0x30c01030905100c180b120f101e0326030408030c0c0a03030903020c0906031b03010f02040f17012315090f010f1d01030b0403020f0f030423010c12 65
    0x20f54002c00901d0501d20070380c00c030540c044aa21310100c1c80800e10110030b900d0305000d024501841050f0b07046c1d011110f000400c651005040b054004c010001d22a00180d00d441c0c031b41c4842c20100c041c0c168401c81485040040240c5940200740c42c80e4001110b41a56400615020151001030009015601d000c00402ca41c0c1040c0800c0340d9283c10088220b130070000751403901030702805a1540c03d4002d8011300200710300d14200151101d01c60f2000601421790401d1844907240428100c1d00c600b6019961200c5924565903240700032300240c024071281c41500ca261001c0f01801c3c142c4051001d4003641480300343d4425184402c03040400d002d150042c0d0f8040d41d00c0380501006000280003c6900c13003400002e001c8280003031a001070680c0c5440a00382c6a603501c0d000f0080c040d01c43c1ca40001d00090080004201140c2c101b0728451b001071281c4151541030f401101654501911400d1040300d540002404102c3e031081c20130320b4580f0b486aa00c085003c4403a85001030044070340003102400b8542c3c03d080307410542c0d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 319925422 1250 319924172 319924183
    0xd0602070519050d08090105060f09090109020a090f05090a03020a0f02010509060a030501051918021806030c18040b010c030c080d110403060c03020705120702180a0f0506010e030c01030905 83
    0x103542210780c41110050703062090744c2c0c4480354840c4c0701054144010940500060007058852040581400d4407030017000140032044d0300040c0210010f5681c0c419000c0140d40740c040c44030042490b5600440d02d020f000d603c2000b190005840040310368006280e003070000e0740125402c00941d0300300700c00715489001c500041e40c9038455012000d070b2284001030582e0301c458056000078140d03182502d03044040c0b0f110740341441d08441540a4060140130300c03030840d03013914090780003056900c40c0601389040341101d5001040301038105648103440702e9000301e03030490206180c0030140c420b08004c940500c140d000c040c0000e040616a040050308008807009000700f0b201207401100d01401304002d040281c950100f10300350f07068004e07000849040741020140e4902d640709000790307222260060080c090b000340b100f018000710342c02508221303040006014080b44144000101911805110310041108840c100c0c0c00011182d0040046052168001e0500ca003074a0024404180c400f080c01d0006440080d81407691034030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 319926672 1250 319925422 319925443
    0x1009090e0a030917240f010b16150207060e061b0712030e0a0b1029030606071703070806040e0f03041401020715020a02030723010f050c070b0301080c0f0d06020705 72
    0x50640b6201d40b058000a01c00320b40f0880c0280f2a00e025a40c0354908e07a0502d100d0203100d00c80c91900982250082451101401c1010b0b907122030061801c035499a800050301e01a00305404240c10100800c201ca42445e0306c420120003400c40c0491030502d041c2c4d00c0d044840030070303010f44042651752032009040980400100130151340103400340d81c46191044003c202036120b0700482029088083d0590050200310b180f1007003944400100c2e43c2150b55075824410b042d00844020344e0101d0000c071061050005041c0154094011603445481c145403138003d20058030040502209141d00001020794a440040281c0c1c003600e5008001e204c480d081c000040349026000d80100e607840300310031111403625800041080740c05209500781c80a03a075a03105012410490300022202020304002400f445600c40c0c0d42e2040e04034030b2810b20030f05020324a4011413401020b6004807000110000041c00301c400108065000b0400449000010702040e0000c200c1c04841c0e640300608080d000300b104000c009040c003114650 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 319927922 1250 319926672 319926703
    0x509030c150301150507020a03030c15020705031818070e01030b0301050c1b030c120a0c0b070f091202150d02070b0a0b10030504050d0f0e1009090e0a030917 69
    0x41c0300d10191002544203214503084409032a580b643c1544c042c8086c0c1e0601600140b1f140340795231840c0c50644281102000448056140180000700410f162018102c400d01607c011a1070303240866544800c4c0c189003a1040c4540580c00b43c0014043d000c000300f5602c20b03001c3c50502620900d400040e070103040e500045660550905080000c0c3c42a2500500030012004a08074100d02412140c542ca92107800b00803081c58001c0c0641c4802240c0020007800c140c03040d40341050b20489035888034081c0c00e209481d145c0024507200303003e4940c55840800700001c4d002c801040d0b00b0000495000540c10340710400d8652007100c02017141e1128441a80c1076917120f0fa08130802c030455141c80c01a4600818044007800e109a5041e41d885602ca403181c403500d48103e038840020156005007110036101072001c4002d0900b00b1022064800c111303100d0f00d032003c5865a4075100c0e20340031030031720204a050307030000c11140f4101d502c203225120101e41d0201411044801d402c0040b82410b4103c102d0604014810064401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 319929172 1250 319927922 319927939
    0x1c15020331030e1207032105040f0e0403020307080d1e02310e0405151b0304110f040e0a1a0601050301050d0c05030105040c030b09120910020f06040f12020d0f0509030c 74
    0x3071048054050324400d40c0091700200c00000340c0d47c03d4420b8029402403902400480c0818080503400400582d0000d0081c01240d0030701d0b0082d0344003107840d40561010110161101002c410311400c5680c3c80c1c43c5080c4941066050043c0d8040040e060076092075003038400d49082d121001d0703101307802940202074040d00c1e40085c03541c43e2030306103965100d9a10030030015a8012100052812f42146ea0039560072a00f4a491869500d0300c0c2c8820018891070752403150b00c82d400744400307240ea50700c0740300b00c80502324484081d00c0f11341c00034105110035210310041111751880780310410001c0d03a8884200ca065800440c2c1501145180e0706092113194000c2e0080c1c1c0c0c0542c40c140070f0100784084146914100c1c1c2c440d0801b1103440d5264180c00f501d07085800088404200c0620001c8030500d81a103d5042c400e540c2d10450341e4003d00340d00e40c0b904d841c4081c0ca058641900190340003050028425030b20081344680c0c00104443c05101000800b0300d03d0009140007040707070100d0024040e6030140640ba0b21320200420180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 319930422 1250 319929172 319929179
    0x31e05010f0608180c04020702040e0f060703151202190b0c0a02040c050a020706050c0a020301092a0e2a0c0706020105060307141c15020331030e1207 66
    0xc030078007203074000d80c0041003450b400982c41c0c8402000c9888502800c40207050001000014000030f50441c1c24202e07405600e034504011602410003411504404078401004a0300b4014005011210590410021500c0090f414400780700b04a20344402103134182c1d000e510100d03274840001c1c502607550304014200680080c0184c0045000941210400d000300c504210072030070340c0c0703059840c2d11a400e030060242c1c001c0502000002d0240c0c0c090403543c0f1300d110503120040025030009003101e8915000311443c100d100d40440842c00a054555a00400e146961408c5814041001400d0400504118852a4940d01c210795011004c01031103a01182115441d01d03080d07850a03541d1246228040d1100561070032000400d0307858001500012243c40b00c07850646c205941050100082002c601d00300f802d55003803800000035003641080800c0e825503440041c1c1301d0500503a00c00c490303910703030750f0400400d903500c0042d04001c010548900180b941c9420300c00c01000c0500007240040e80c480c2504d1489002d100c0000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 319931672 1250 319930422 319930439
    0x105070506063a02010f0c150c050c0d03051009020a3509060603100605060d0e211306020c013507030f060503010203040503120c07081809090c060901031e0501 70
    0x3c3c598034401d8031624440140040116800e1091031006001108200340c2e0303644044a44d4400e041200062914134a0140d100406a1404100700710b80800a0781d55020084400ca02c815203401600c080c007401e614108001e50003c1925920084480487d1040761051542408883e07450171380004c0d000100c41c0d14a8085019038482c0400c444840c0240074110740c0041c034054038130401c0e0644100802d104c0c20300f01e10500c0040146441c4a6481f0203202c1e034803001d8401c01685824880c03015400d1440d80e0b440b01322581140d100102ca80c440c03425544013040310119a80c11045810746000328540107842d0302d10841c0103221030205401ea40040e101c008042c010429031503001942040f40b04001809615030b11070506080b0301c402c440140c4107400c14080090146d500c04100d41d04101180812030030100c171601d854a40740e0000800d101a00e0303e000719046031f8105410202d900112000c0907007400280000400d1040c401d0990745810542d4800c80b02e0081d40d200001f0082d01422800100701547e12002074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 319932922 1250 319931672 319931779
    0x1903020306031b090c0d020d021206100302090307030b0a0207060c030c110a1109180f010b0906030a03173402011104060f030c0504051e090105010507050606 69
    0x7014003e000d00c9020520081907110940e12000c405064100ca603aa02400031801d0342090140300b04090b02005960121240c9002504a0302c481d5035521185052280130056409010301c80300703040c1401440007820a94000c41e00004594121006030350720380c0e420303550000902c2451001011a8a03040360721310384030741c540d2007410180b0040d251412185501e1819075521026010001c1c0116100c684e40000340c10001e0341241c01c12110741d10030000c480782d1400d145c2400148840750055a56031041c0b806e0700d01d0103c501a800a2080d806040340051035100100780700d0305410500030181580c40071440109190b4520340070b00100d000c2d58822109813070304084220805001500066086c0b105c0e03842074088040c211011642242c496002a4820800070b4003e4035101c810002440b0060000094503104c21002c0408600034800c01c20826042100b0400c4041045c0c1000303041203402c3c4010740c0014800100300380c0200c0c048500780c002c001c21f088554101203980108507200f190040014040714800c114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 319934172 1250 319932922 319932931
    0x50904060501170f07030f020103140921030f04020103200a03060305011a010c060507020a0c180c0201060f0e1003060e0f060a09020a290a09050a090204060504150519030203 76
    0xd200000d81e4403c0800b07503450348004003544640d0030100c0f04100203002d03443e5089819106040214940340b07400400701103200700311102a80c0350401c201082e180041c2c054118413614201980030f085080c881610f000400000304000c0c107065454000700411615421a200030003400008195a4030905034000c0190006101c11a802d600300052440c14224803082d1001d901c0b411381d501da04076140c0e5114640500b1002d86054190700603039a2038008106c403040c02102404ac031b03070941c52051004078051001c41d00c14a00003000c591404600b44022001c5141c000101d520031096418151110302410084000c07582c0000c114a280c104114011403002ca041d2000325081010b0718220390b03580c10000c0940d440c161000b540700c0110607041c0500c201d66591500583c0e00164040044880d002072080b89a1007403000c48007282d007481c0c00300982d19140b070001e009003880c05e4042d1f00b06880e049024010780036501030000c2580e1181c3d41d003200d1612560968103030128210f2150340702c10368801c000d402507000f681c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 319935422 1250 319934172 319934189
    0x20307091a09060304020d1b0e040b0f0f0604021e030112120c021c03200f011d060c0306120d030b0a09050907140415033225050904060501 61
    0x101e04100740910341042c1c42802001074030a0b440e660f165420407034024001a421681c0700003004600c00b003080d882600714042d204c60043c1582500341800d02c1c000c3d01800406c082507501400080004801d102e44c24960007140c03d6038056103400410800e0204d050000f4010303054030001000000b0003180e500c1c032210305a03001e821031038600755204030f0480b1070903803614029400411044510020041d5500c0d00c0300f0071800392801008112a072005003045020304ea95865203584440081540742c0c0d400e101d6a24000007040700d0b000e100e00c411001e076448044c014800929107602100040746c9882e04502c020001a003541503c042d2441c2a0000e0024184050320a0040002041c0442d081a452103114090815070004040c2985040c00c242c1c0b040e1610501d180d04291500c0c82480034102e0090414040c7d84662504230300d00001000428001d0001c401000c000c94000144204190380454001c0b020550891000e450150402c00090302d0308013035200c3c1b50003000010800c424001d955204a0590741c496 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 319936672 1250 319935422 319935449
    0x3041205060610020d0503010b1606140103051009030c0615031b030c060c1e02010504091a0301050f0708070e01020a020d1211070501210b03060907080c06122802030709 74
    0x281422031703450815a100d600030500420040c40761224020150124001040708288801c00c10b540e083c040e1092605000801d2031420018800c0101c00d1145414100b00c0500401190740c1c180c50080c1922211407000d0122580c2d194280f1011004205a002854201040610100c140c201031103c0b801c0301d100c02d5400030b00740344c00420080d01c2070580c0608a9004102d50000c1b50248518607412200404d080b1b061090400c400031701c011031801420004a0700d008000100380c08032040c5801d407180209070980d0f09001c0c004202c251a04072640c0d941161107444c0800d80304120100607890003441e150040c0d40002510409404c1046c500070001c070050090351440701d4040e402032002d95941490260304e020850099000005201d4040c0151031468000e2001c21041d8004011038144503094401001e0780e040760605001c01c100404c110541d50000761105403512540c612148100030700580341700c8052403051420b07181410313281c5418600010223082107549040c11040a0100031451164002802d02d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 319937922 1250 319936672 319936699
    0x41205031b0a03090503061302091005090a020702010801090b1c060204081b030c0a05090c0a0302090a0303050408250608060607060609061412060f130c09020403031101090507090b03030412050606 86
    0x411f00381d0055090880e02e00f00343c030b820741c02c11069001c0100100c800d014008400140c2e603548989003400f030303d1105001691800180001400301105800041d604c3d420005a208652602407001248220000108140d80c59031f00e4070740f0183c0308550040324107100c1c0e0344408034404201007440d110716504400b1030341588180010b2000e03902d1144a401c1d4000c3c1aa00000c000000e2600108100b52962800602c2d080d1080009510002250019400107501040910600c0e80400c05800381070b8600440a2145d01c6112001d07031050864050f00c1c04101200380481d4840d1180360a940000d50b0182d400e200303007a241c5081000a04030703840f0b8410003110a40c5501c03401c0c00e01c0b4940400d40c51042014080f2940d59480300300c481c2c0c501034400410b82c408500380384049892116800c0291100d044d01594481c80c509000b0000700e1012403640b190b9141125903800200b000990074122010040c0121f1030003010b02c0003c0c21405070354004503856098010382010000c003c10024130429003251801a12000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 319939172 1250 319937922 319937929
    0x41e0b0f0a1802130c022e06051c2603040f03140705061503160602030408210904050a06050607060b12030301052103070606170d14041205031b0a030905 67
    0x16070302e402a400245950302100001e08680090f04940c03998011100e2500022074520214222121b003114004040d00700d4010028050003114002d14080740c107003001c424001c0101082d8041c002004180b28002200a5070219031240c04414510f0704812090b16442c0c141041d88140314003c1040700020f455000390541000f60030191040190070600814860751016907004454452000c01a8148241180728098480345640c0901910300756021b10345031440d001007580f92030401181c5042030620f061104034a0394041060710031541d022100400d03662034510b4174030300400c60b039004076402c2000014800c051299a4003e110401d074143d07000108020307041c10741512070100b0301840354403d4698803000c80b6060351111500345001018150b03850000282d88620481b0403503840b1802c2c000d81c21100030841c00090141020344c0149040c0010302d0707c1c0100c40500d80381f00d107000717012800354070080450a0040800540301c0800c503000100c0c0b10907840710040d1703988000006040300060000c10300400d483c107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 319940422 1250 319939172 319939211
    0x305030c0d2604050a02040e03040f06090b1c090507060203070b06040501030b06131404030e03100c020607030f0f060b040509100302010509010f11060103150f060b03041e0b0f0a 78
    0x102e000c5a55420b850300180c0c403401c2c100980203132000e00c280d00484000d40d50340c1c40351078420101000115500c500e0280c042c9845035250344680c084c002e01c51170400c04a841c4070102c90513000300280c2c1c2082101404464002489100400791252181c03440124102e5000801441d4107405240c140500c1c0d60b80c0001c11041e6002400300400c1081040045075803800c02c105880700441000001060f0800070340d0802c194060205d03000d8002a00742c2c11a0709550400780508407418401c41824401d00e08101c202030b507150030292035202056590103d10051900a07400b0115030175000d030741884000e50b904058401504580100c038814141031000c1000d0001c400e00d58011280d060310303103e04060345280103440e1411624101414403580e040b11100c0c02805006440c0618407032a240c8442d1034940b18901c1c00c0f00c410110542ca0035280a105100040d264429240c0c055070181c940c2c1c04000282400015950306188000c186440240c207004004501aa07494420024460308000c0394482f0007103242e501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 319941672 1250 319940422 319940447
    0xb0c0c0c0f03030f030618040b0106030605010206040201022d16050306012304020706020d05040606060201051303020a0f0203030c0f06010302010e040504080318070512010b1804051507090f0305030c0d 88
    0x5600400603010904c0c10f0801031544a9002008030501b001120901c650160003210b04640c003007045001400202d4040c80b40d200038160a1005081a107059400130390b550410201c20b603000119443e40074030402c81c1d9040312002580406c02c2d80c68907560700268004124080c007c01c0d220b400ba03000080743c0317004030f4170300d0390f8080e00e8540c0c5004e055505141480000d41c4400c10035509103808104003580e406690180703a00451048800107a6545020310090840c1c41c068035148001100080300c00c00b00707600098156a040e041803240000e03415070f1000038558454949001c0450003441c10b819010030010480c281264003c0e00c03403180e501d40c6001044100d0340708513001004900140041440000c0840030301c0440b0b0385041c220380e03180b510344000407010410050241000d139128212056541001c2d00c0340c00384010701621170031a5003410340d19980c0382c6003000c964111041c46d034000101200d01c5030711110014105640c000185c0394882c1810b9840b58000c148886240c80394500314044188920000003c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 319942922 1250 319941672 319941679
    0x50114031002130b0a0e012309060313051e06010501210c09030503131406030403020c0d05010917070302160501050a030e010905010c08090f03040e06010f03090b0c0c0c0f 75
    0x5809281c281c840080d0051618603110051940c40460020310800040800081c0c68480c424462001000103002c249203541c10302189900b99403401016035200160340d01c0340021501c140d1256200702e113640006069001c050701030f219002288860718844004200c02c0521034042e00c0c00c40c0e0701c44c00190b60030000c4140da03402140f400b82224114461a60000e44205c0e030070300e1f0145d42c09036680c441910315040300e44282c0c4400b0b5080c004000c0c2205000d24181100019242c803801c5140c03503280a900d543d5081001409000c2c0002c0c3c02d41008000c0d8800c94081d68080c00d40c00522000e01400c855a070070050080f4098403a001c92900c00c2548c3e0101070048800580d1a507103441e0710740720110302a002c2000c100c05250749507a01700c030015000780507480080c05165036550242ca0310340348042c5800c84129002034640c104010500089105c1d4a03011b500c4103003801c2040700c0606900e000c50041c0090140503154031329400c1030059001d040e100400090032a0710440d00c0e00700c41402081130840844404962 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 319944172 1250 319942922 319942933
    0x6030908040509060d020405010303020d270e04170403030815041404231009020a1a070609083a0c0c0605090309060703020f010621020d11101205011403 67
    0x40c5290444600c4da1000c0041c06029510300c3ca131303011a00b036130007e070000c5000d40c004c0d0a2a65003d903001e010006030807844004070380380e441401302c440550b100310b000d02e03500c0760105800103050051016115032080802401c2c6c0341e90350707640d0070000c007408000c0d900003180c00c0658840c52603d28082c09101e061280580909121361203e5888100c102c21590107403020801c0d004401c603c00702c040c444030003580c54144010034110601c0c4100100e43c080742c0c00c09009200004241080040c42c9019100c42c07641c0803100050060f101c5c1032544030b078001c0c0507010801009001c0d070040440003008101c401d615000c9810000100d11904540035030310745c0d02d2a0400148401400b4000c03501e035400490b013004c011000d0b685060074400200b14180d0280300c0c02d0700503910202c21300404c0740342441004024940a00c1c00c1c0300d072034651702041042e4142040701911554050420b0f42c24440d0307400c0700d1012000003e018118500050b040585031b12590f114a203006803426000140040340c0310610013030140c2c003c02811 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 319945422 1250 319944172 319944179
    0x5040f09051b030c030f010608060903031608060a120320060712180210081902090d02010c05010b090a090215160227040c090f060312050901050708040308070201090603090804 77
    0x140500a0344059950501c41c50040c644c05460038001e1900c1c105c080800802c5160908042c5844c0080151074000301d5801041000007910100d89039403404100ea24184100d40c031044002240655a5008070007201401100c034000c16802840c103400d40b121440100e40c681e070111901d25200c40781121400b01050040d40303242820b0782c403a80407140d031000b0a00d2040c0a24450f4011072108164010514041034100d418882d40a40700c0d000c0c10a14800c02005618002c0c85201052600c425240020706121032000300604004c0c0070b410080c0308050251200f8444e15061112801924440c041680103c50300f552609002010004895000f0140340003d400355503981d0034440c202c0c151083c10100e062442541c2c00401548004250081b4041c2e1f0041c0e0849007409090400c440100400b248240d05d0814200300180d401c01c0032028a40e450301f0010341318414080141c85a1041a4000307200c031000082c04002c00511601820106000381c3e268100c003603c5000541c100d818101000d042d01c0c5081c041003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 319946672 1250 319945422 319945453
    0x601060516050706032009030703020603252601083a0206040b090c010c020405090c04060305010204090b01090e0115031d01050703051b030f060a03050d02060105040f0905 75
    0x404556800c2114102251490b40b215402c2406a0300a200002c2e240c5441840d580e4603221324050301058103090a140c080c440300041e540701c08612000b8002d4101000040c00e0704a51801c0e52441d03000d41c0c040c1d802d10380456200a1115040b000d40c200e01c544004002104011440c003114107890102004005203582007501c40c42140c0c090792202c0001e008004075801403500c0a1720000c00d8525500202058200307482c154080010051020030198030603800c0c043c040e07922000300c0c030145405413000580c64440707030405410b02d10004c1480d5046030408100004000056009008603048900f0811811500100448891110307114481c0c4c00c5800300c0042c045442e0400d4030400e410b40e5404e001800103d0031480c0189541a40c03200e0000b0395440301000505a050b0060302d45c040712030440c13441c4c8440f0442c803903640350001034005c04082400310002061900e5982c60100910340220031904501c204100013965610f00b4000c141c0103904000c0c42c414030041c1409032900c07140c0c0c0304001d80a41c2d414141071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 319947922 1250 319946672 319946677
    0xc05060c070302060a0206010501140c0c0405151504170f1e0c10030203100b040515130e040506010f090b0a030818190906231507061a040f0e06010605 66
    0x1004a03a004032140040141c1c0c404e40240701418194000c0e02c039541c9024005009c06031603c0d555541c0c143d04206c0401d40c214040795544a01000700c900091649801030100012492400e40c160003004039020b00090348000c10180007114070385041c0d0100a8074660401d40c0700c2c0d10710b955260722a4490709012055070314940c0384800100d000e0003103480b01c07680e140015018814600070780c0007195001081c044040c1e6440d40c440084d0040851365481c09141c100420028884078119281039400403524461145984228900070420f1501c4060541031506056444140a1103400194000c020b400a058181d50242848280340100300701201451900ea801c8240c0c043c1c04460100b5440914001c40380da11611180e10003415491060142410102d050b401c50340c40341c0010300c41070488e608407400041406081c4c0b08009065600b203d0103030b00c44c29000070070f0140580041000d400c0c412002005c4080801c0003c043c0c00490b018840c040b01644900112330f200100205990400f40c0148075082c0a0f000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 319949172 1250 319947922 319947937
    0xa030807080405030c0313051c0b07230f0a02150f191418010b010302090604050d0201050705102a0f0810120b07090605040e060108180a03031d03070c0506 68
    0x1e1345d280142d108192411640b04a41c4408000400c034018030050900c4040d05914034a01710b9100d141c6802611000d001400c001c04020400100809110140740545490794500b03441d03590540e100d01c00164180601d13080703841075000501c5040042e00d840800c40c2c1006c0e0007032580541e0103e0607101c1000c203180481c0d40031180a40c90b901c031040344030a86801c4070494400d5160385401448060b42e10b02305030945000005141c101070040c810040070303580d00411902168811103043d1041c0c1824401aa014021381c20043c0407405015400a006d1919402403104007404075010848220510344910800804800000005101540d0300600d103004004168010050454042d400ca6580400c2101d03452114021510291b154051121150b0032038100070140210341801401e05081000f03603121004001c02e0a41041181d4000c6418641c0110302a001d030000c0200f030700c50b88400c604000e40502014950000706100031080320380e80404c08000e80700300b203601144148016140001300a8650070028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 319950422 1250 319949172 319949183
    0x3030e010e0d0b0f0a0f0b061c090206070605100501090308070219080a080417030c100c03140f100501050306030c120304171510380a110f0a0308070804 67
    0x1041c00d008556040d01d024844d41803440900c0f504c0c03800401c40300030703940901c0707441c0e4110b030030300002000b913649400c1510800000d400300c8c0c4640b52070440c100c1000e0412454043c0d0080e0340000d17000240161034020521620f903040c3c200400d1540d440045451078964440a40001c1091180600614001d1b412444244100c403001ca015070311040c805050110700441102c11030130009041080c445c100100e44000a550005035040208150045844078189208091040e54034100079890038000e030301010340700400e141034a030f039441c0a158242d05d2003010343d488030780c150212400041e03a603c20012644a0100a005080070030426828040030341400345504100b80401d00c40400e110418804401d8080c000390028800e0f0391203600c0f00c03e000c4102800c20409048005414010300b0140103550b1440955880841c071050803d400d480c1050840190400039200001008100103501a408039242008034058585000240741d0141e07590812040c020042a00da4000400840c0074194680d4007a0041c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 319951672 1250 319950422 319950439
    0x30a021008060d05010e10050603010504030807110f0319030b1e1c1403030115050306030303010303050928090c030b09043206040c080109051c0e06161b03030e010e 72
    0x1307503641303400d503402c51000d00c85035484582c0d8080c803070b2110b018258002d0415002001681881d0310020103010001b02941d05020001181212400c01044500c20860342c103004c0e2a19008201d403156400c0310075422100001e410700036003032014504135a42c04c0d4142c040c401e002c420171080409000d445040c0c0c82141007407056134500c0c400429441122a41044610001703540d0ba98140346502d00c0c400d94588840c01044410310410500b92400030407a0306494060408540b40e4003002c000a205165050000004203002c7e09803211000001010b03e0a8880203501481090f4190100b01d00700c0b016070320300f40e074405510fa000c00c0100d00300d40c00c110701c0940f21005401407078010320000e45810081c070924075115804401000240030000c044000940031200080c02018055200c0507034890305101c544401a510322190407070b0500400d510a00f404000d0402501d81030f00c241f00c4c2c14035050041d0203940f62144000104010300e5040640400e482d81030729680448044400110307001d20317440c0e40d1940c004120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 319952922 1250 319951672 319951699
    0x50f13122709060e090c040f060503190606050d111302071b0f1703030a0c05040f0801061701020a080a05151302090f030d0c14160807080705030a02100806 68
    0x300910407109118040404041d94902554542269056444003003440c0141061007900240825a41e01108040b0341c0851043da00201d200c00030710b010703403200340d1601c17a00c0c20194048092800c0c00507424000e02c010804903980348140108088020801020780b00b0510200d072003441c01c622961100b9800d82c078010b0918106035100c11a0b98000e0843c426810a440010801c541c0e0310b268110180c4407801c040070302e0030220010946d0780d00010f85a0f4143e103848801c03025002d84510203130f0340180890710000490680d140000350081c80e86014841d43c21801c1441541c2401050080f5a00c514090b9030340c2c6c165590f9001e00380c00420000c5c00b500c0a41d03a440407000303191b90f1942201c0c030080c3c50031300c0d005a03540a2102013100c104001c250081c0030f42c00003100e00310856040848110f0060300842400b40c0291100c0c0a90b043c0000342e080200034455400d0041010007000480a09440c54503046800b155103550800d9560031551600950003540710042c0d40780070307108000d15508140b01403c802c064086 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 319954172 1250 319952922 319952957
    0x620030301061205160c020402090d0510150f15230d020a0206060108040b2206020408071802030411100507050f030306150306030d030c0215100306050f1312 69
    0x30030b0b4080740000d0781030414090004030314814150000e0b28082c01c440c4980202502424110702d1a20203846030354040303000b0f04a526481b2488020550041c01e440d41c407508004041d00034646211091030045e1402008a42c036800042d1700c009886441000354070801d480d0000300ca403403405004883d00c407441d2030400748150804401400103101d2900b005600c55030303604402860040014040d40c10898044140030108214403485504206a180c0c0c02590b02c5800810040070454014024622803000600043c10100801d100c01641d1038030110b6214000044103080c243c0c041035501034640402072041e5203036454089440350703400d22103041c801e042400b83d403506828035079840314101c443c1d08000b040040618100c00200d4a42070010322107801c40c1011800b003a600c0074854615014155185a0350f541c540c02003000f03000c8080c00840c0640b851401c803034200820140741c03008a50076800e2501041185607102079840c032a01c05104002d010002c1c940f285600800130300030340c00600c07941070b580404049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 319955422 1250 319954172 319954177
    0x1b04090201110319110a17030a020f040902031005060f0412021f0207090e0a05061501050403150b0906100c020f2701080c01020106050102101104090203090c012007062003 75
    0x208100301410542c41200c001400300501401e150382944c200048400004070b880c4129120502662440c944030781d60089c8410080c424401c07800c0410720045400600c001c915001035100782072050380350800a0390b84d0180710386801242104030100c8020b20052242026020513134901d0b40c0002c04a02200484600c152686003040d600300c0c0043e04204000c2c1312100c9140158100d540307800004000004041c0c594980345c40028010100c003c1c6807000144113a0b11400680d4059500031075615068200c2e11244002400b0015505000e2007052000036024a404034854846030001d032181c0f841854960f08000f05440c42c02c1484e0381c881e50304107407203208290350082da0a14111103aa61061541070240c003034a02023114600d541168140304051080d40da000c28403112009510b840803800410008103501d403806160446200c592001c01089007565000a00101e220804c1c0c8890312500115030003000f84505800307145039607a10150040014a04c076108035030302c0a4450079600c40d1034107103804090444c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 319956672 1250 319955422 319955437
    0x2131802070303060b0c0a06020d06080f03070611130504050402031e0c01092405070c080d0e010e090c040b0a021501120c080d0903060902030c030d201b040902011103 73
    0x140c0c0e02080800030540c141c454400584500c00b40c4034103014401100c03a55590617641c00a0005030017080031000c90015400c1342001d0091300c8141c2e00b00b4074440c0e00680d030b039820046083d80d585042c107040301840346602d0200c40802c05c41032102c15450f400c00003032201a0030f01900880c0c052240440da00701e00c8014104d1848620249400351441c4030045000402c440020b4200c0592890320b004500301107180c0c0c0313210004414490400c5a12100c03182801341c0c40711500d80c803020081c000c0c00004505142d02038400e031600744098807031001c003032680024400c5502c421140b1120702c180c200000e10100e480c4902600c2c40035180c1c4111446080d00601c1e07071b030b0f00369030a84c4103681c4000c0c2d19510800300304180c519407000c1d204400082030168040b500041c05040d19104c0544616075500d00d010075902c05001020420300054201c608001000c41d0090040f03885540101c0805040038030803650b0fa001045410348408000d80055108622104007c018100c40d9001c90603c0240700030741200c0d040910280004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 319957922 1250 319956672 319956719
    0x108010509070618120309090f0f051302030607030f09140c0315040b010e060a0b1207090f050315060d150c1b0201020d0807121107051002120a0213 65
    0x609100c1c6807a454040340e604400240030074850040070140c104441c201c03c54941001d076001103401d0b41401d5803000100d0b0000280c141c1844140d100504054004841448540d00c04204a5451165444143d00340751030080d8140c100c0030125003110f00c0382d08090301d040c0c0011800519892940da51542e8140c205403043c0c0117400c5116013010620b030900c0883c0ba0248040d02445682ca044c1e550312001078414051400c1c1c03a0940008640280c0702ca0017600051f21600e411941e841c0c02c00c0b041c66800900880d00d500c0010034002011590600710b00f400022620040c004003c0e211407070b00340c03180c6642c00030841034000318940c15a001142d0009020760500350b8139800000c0034078080304001c160b446421400c00c00d00d84041c04000042c0d90000c0e03090700c0c051803440d00c0c80554071044000c0318505c03038078495844014202080d4003040301c4000b00508905d0320600486100b4009070781c2001c164010700380003512402801c80091480d10319078005109003468801144000da4407040f550340d40340d4125028002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 319959172 1250 319957922 319957931
    0x40906050a050a1d0403020c0a090902310f0908040f170a0c050d0302160f1716051002031215031e060a0b0d0804150807050403030c08030c0d05010801 66
    0xd0400c181414041e210550f24802107905041106440c0b030b940740b40c0d0321091500d0100003070a140c8244011018070400500003548690340e049071401822401c9030591042c605000d00b04044402c07100c0c4440e480031842c0d00400c508080d2800170b401003801041400c503954032a202c0c280090001c40c000c1c0081c02910307900d0000d20341840d5036244070080c80340207500c00d60700041044001c100401c400e64210390084a89411040c4c00c3e15003281070002100c44000000e619800120706155051681001c1e80c290540d140d2194420b110080e95079255011030046400c0039050038080b40c14643d0000450034050700440e45814101c909481815004a8400c450011090f20b000150310741882400c22400429000146ea044c40d0030b0500c1d122071014000704102ca642e4284501d00d0313154078502600f5070703070007903085500c66645407900d0b04c00614010b0120001540c640001d25030a010703030300782d5054a4140d9154401c0ca0741581c1d600306150302c060803042c10308200b0301c0405004880e44c01942d010b000346100214 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 319960422 1250 319959172 319959179
    0x307090f030807080703030906110a110a0b01150504180c030606031a01030506030114160219080406140c0a0f0210051c0c110303040c050a0614070308070e06040906 72
    0x420006840e000600000040c010401c045881501626079158101644940e03403400c5180903401041401001031030141422100c40d0b0360000c500c09440c00102e80d4039010082030500c1d03d12910b420f0001e0b8000c1c1380c4a003000041c404c010b2214124201d00700903080107442c3c26250f000e2201200713a2070001099032078a032034540c15041e9060080800030700042c10b040c807200d83d0a2a4900c1c0b03044407103c8150404d0b941c0d10000d1200d0307400750801c00d5000301c0b1191115950424011007030701c402d81e82d0b12410140c403862200011220719001c203084269000785d003890a150801008440c0c40307030074940351075044d8010300020a4156042c0140b404452190402c1c880707011451040c081008031100b4542d0501505000048480064211129000c0e850307a2000a03c1888117200351184a021500758403e8131004c410442040048070111007643c400b229100e1000d035031100200c8900c5030a4421b41241e00701404010b00290087c050a030700074003182082800013032039001145554000c0d60040d614281c4444042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 319961672 1250 319960422 319960427
    0x1e0c0d0f050d030c2111040303021b030a0f11010c0c0e060a0b03090d05090a03060c050d0f020f0a0521070201090b0f09070b071a0c03040201020c0d05060a15080607050307 75
    0x8115000042c03c003800281c01d0190054110507068580034900ca104da10b009064004551010080e000507045484e1075603200e0400070341da405c102c81d100e50000700b9031403200c409260004a486244d50302484850410200e60ba400120154074403015060021201195000440000800003c1c00c0034028080e81468000100700402600d42c0c08441ca00408005001078590040f13103445e403141c80d6052031944d400140011580780301160744060015403030300c0e0142c00c100d68080000c10100d02c40341c00034407081c210341c0045000c03446980c02c0c03951003250070064050028002c0f005401100170501c070715600030183d18012400300904585420050355075601f0142080041c0082e81d0708030000c440c0d8108580b41c42406643d035640507000790303500e90f680030801d1ba080141c0e0b00409039051040ca03103043c6050501c1c180809c0a9002500c3c200e02500646081003c2828403402c2100840d4000c8001c20050f200d5800c500b0041001e0408680f20380c0e40031350089218202040034902a649a59520f03940b883c024000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 319962922 1250 319961672 319961683
    0x3c060b090603121e0301060f1404080312040204020d0c0e040e0a02030703032007030501060e09030a09030b19110409050f090a230f010b03100e1e0c0d0f05 68
    0x64800c031500018000c1079100016030740503c900d29404030f952504e105090713950512034150b40d004ca18000000100d0000d81c88010129020400d84503101c000c544500001130034000c601074000e456105010042d6144881c86034a90024005880180b410a6440d001d0041d80c0d06448002701041c0081024100c82c2420f11402d00c180d024800645004041603001a4a80030b0074032015041010141e08800030f00c10381212882c0207030340c1200312034001d0764030314010340648458400e000b12118204006042c40d58044222400450141d960b000024215650f00d8800c04014101c001044841254100e01002600c18110304145880700251154506012174066450080040c9209251035040c072850200004a198180350300005841c00300c05001c41c460b00d80c000e408808403e0303104000100300107107810f41c03040300c500c0d1080c0c054502d540510300e000c1056039050342203400c05500100b14400c2c142500008580303081f044005884202440000060310b00207a140169074404000348200c003000020001e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 319964028 1106 319962922 319962941
    0x901020405030a0308040302060705091c06150b030f010b09100509150a030c08070306080c010309080909040c0f080613060c0c02060406032c0a3c06 65
    0x4008001405c01e0b07070194050302440010403107003072144045034040000a05030400c0300002a00f14005546025010340f01d090342c4070300f0000000b030b10b40800c038020981c6416640c2c4904140500d600509410b03070181903140309c10000c0700e03041d0b114a501c00a0580660600a0715610900d010a280d8180303075084954401c40020b43d81e03409c0c1c0d0154000c114444440c3c0e150b030143d1f590410141c048030305034090501343d940480d95002056219070080c0907920304c03039610396041031194004134003580e500396412100840e840c40d081c40032455483c2800d00804c10f1100620060034108039450b000555403002030b080d00c2d110f00031070081501480160b114240d01130451580d179562000010010071400300c28400c0c800c0d04140089400040d54985803240b40c000019002c1e60342c05a81d5544000120181d814400c12001c0101c0c1c00140e00030b01208000075074217240c40340340c450361500800320780c81000c = true := by decide +kernel

theorem cover : BRFrame.Cov 319784172 319964028 := by
  have h0 := BRFrame.cov_init 319784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 319784172 ≤ n) (h2 : n < 319964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
