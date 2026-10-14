-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0930
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:02:15.095466+00:00
-- url     : https://prove2.me/submissions/09ea4227-df7e-49fc-a2a5-9fd1348667d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 167086330 ≤ n < 167266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 167087580 1250 167086330 167086351
    0x40311120a05060103060e06010b0d0518010609060302150f09010503190f0b01022b0e0303130b07020108090703030503010b031e01032910060c080d020a081009090203061f0e 76
    0x45c410710220340140b610000c640d2000300300c50b524040400d2882c0c420100054078a641e11004500f60200d01020803004000b0305001b442000d8803006040010801848100c0c0318170400e241c11500c0c00008019643c0d406a80044182481c60b024015a90350344020507281d22031040d02c200d48904542ea20442920380a04a00003071141401000a03140910488540c41c0d4011880107419164581041a220345001403904142e014100c00200b031450059a0320700280c000d600d0008140c501c2e01d40c01601c4618000d980d8460b0320745480001d0303030300c2d400c080c0000741c00248100014880c000842c2d00035900140d410808000510000f060714803039400c20303001102c901500c1610800700c200c4040e0030f45c001500f401042025030500ca100f40501c403025104001c24021480911001c0c00079010903a8260310b4605019076451a109a001388a03100c1186c0c00b8000c1c6101c81008a841510342c03050b0301c001da0b03014008003c140c0300d4140048070f0001010b180e5101d072441090200381943c1c0c03980814000d904158 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 167088830 1250 167087580 167087593
    0x120f02040609050f0d03140c061f06090e04110a081506120312010323100c02280308090f0a1407120308011703090d0f0303060e0606040311120a05 64
    0x140020650000c90b80201e00c2000c0380207041c0130a41d1074030044000b4641c5030a00001c03401e0f442c66900c019000da03519082d803c2c020042002414868409541c0e41440741400519a054494005640d00002801004500344144000a0024000104003c0c90780c1c0c00510400d001695402102c3c505000b0041c0030100d18525010302070103041911030920383c0314055000c3d605200c10000100100c1c4814400a00400082c01811003030b060245c0d190460240311100303807401d0131441e00c5608050a0081d00c44d80051141d4510942080321111200122007d802121a0038404944046030101405003c84031640203c08100092000800a510202e4842c035094190084007001c1c660401c4071940c02020b034199280d07107010000398400c00c82c6041d150001d8070300c0203508010301d10508d14000d4072a0310750011001c1180200380841590b0981682c6d2080c1e80c203004039629000b4419000b082a28420b4003c4414071081c0002071000c00c0c104c4003204040c2c40d201c9481c03214031065292096054041c0c0d859048074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 167090080 1250 167088830 167088839
    0x7021e090121080d0f0509160602060c0405090a060803161509050706050a020a060c09051905030c0d02030f03040b131a09010f0216060f0e0906030304090507120f0204 73
    0x40c20140d004151280b50074141030035046544004804649000f0300380c03400000ca030300035130030940e200c2c4010744800da108010601d020452207a850410011070242d14400100000d40c4a00c0000c21920074014150101c0c18103250034140114007102418006030303280c4030a40400c1d280803c002070000745940c0400401160b016040c04110091101050036420b810f000e00c110100b00001544400c4843d645000b654951007204108e04013250004020000d42c05c01e102010300b10382c001409000d0314411a0a104242d09000da1034030b00c55450300c50141c054214030101c10262034482c1c40c50a02ca8006001e613030f280300c0c5400d078060035039000e42c11840c103039200421044908585040c03600040c1c000c20602000c024540d0070313480c00d81e0003a04001c80c10020318400f0310b000c40c1d10a000b103011440d0200005c4040685660024100140c911140317000201c6440c501071861402440460040343c02034060352429041440c0040540801003d040070300110004000c504840d038401d0381007040359008016199820b2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 167091330 1250 167090080 167090089
    0x4050a050616110a020f0f010507060903080f071b08090d0b130512030408030c070807060c020c01110d0c0209072007030209060a0b120423010209090f040c0603020c010207021e 77
    0x2410300c3d444a60b0000b07601c1030050710740951032040310344115024142d20004400403280e520032a03400400700c504043c00c000400d17400c00609400352040350081c1000b0f42c0c0c0d41d1404c80d030059460709900d2082110240c070401044004005040410002d080451362803100d480d03a22020806994103441e2211807030080003409024000107281280c10290546542000d40380c4140c1400064800e5894000028150b400c200ca62400c9440090348180b0901c1450422a00a901c03009907008080c00b00300c0c03c080c20b0101d07040210b10004030342c0c1a600c62101011464080c8000500018034004c2401103141c84402c0c0315002c03d081c6041d40a0100003003c0c0340e03003584180040d682024200900400300481c091000607121010390b8900110503507403280325501c3e400c2c43e60320b20b91030804008524030400001621090107400920700500d0549894503503881d2600a806c2d02d031412103007d007110301c000c0c0d000d101c0306100750001c1c08000c4600001508142c0300b0340009800c50f00c814a448441003422203c0c0c001d0b41403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 167092580 1250 167091330 167091347
    0xa181104150806041a1e060102190501140c210903070b1315020901140a09030b1e01080604030f181802070506060103090203071206060e09030301051c0302070501030504050a050616 79
    0x10b034212251258206401044806c0202600040151074050000342071640708000200340307034030125001c0e243c142032402c00c20b0007401d4448000b030000700c40000084058081108590032060030446041090b1040344810411050140c0085400e000c00c0000402003690000010f004000304044082c0984807880c1c4160703001601d10001d4410f130700600907040c40360b030450411148070f05610134080e40c9403510f1070b08661102e00c1c2d400003003141220070203202e0f02000030504200c020008a40c500c940c0e90301c590703001c1d40d16007089800178001071254620711034030743c4111502c0207801c0c0300c030042000c07458607546203208202100246030100c07940494250284001000f1881d004a400e00301040100380e1900400d440320800d02451054241c0700c2c82c40020040a507000400508049004c1c8219081c4882080c5c3c480d4801e228151062010b0603040c2c80b4800f4841e85100344540c540c0042c03541500e031000650103800c0051007074440380100f020600126600784202032040100588400c0c004560010240c20b04c607 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 167093830 1250 167092580 167092613
    0x40c0f1809020403140d080f0c09011110060f080a080a2703030e090a090506040605150405090d0e010f050301050d03050c0303090f011d060a151a0703080a18110415080604 75
    0x6152003031005c51090b22a9003500070302e1400c1d0031032b5a0b03011000162079180c104252040740e0710801b54400b0407610070740d008800303507a05804403161144c5d03107201c3c032681c1c1c6052210240c0300890410441160314056113110700c034000355407008800e20311040180301c81641c07194019804954440901d03101c1e440c2c60203886500c02000423007046000169240c0f25501c8500038001040150b0714400700e0151174100082c04c020690061041c0513074600544810b0b2100d60950018000c600c2d200b51140c2958014080c2501c10300b140d03500d060a503881c1208011407000c130840c098091020400407244400d0301800207600c60907054000f480302011050400c0c2c04c44030401243c0f40803410034008443c0f050004107030b0540242c11a04c0100d982e00c03210b0044641c9800e2640080040314100e0149618803000c2c40182400350300944540122341d48109813a002d0720621803419800f04d26186810f070004252011107404105d0250000980c01803090003900c0c00c01103500101019480a4100000c1006401006800f00d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 167095080 1250 167093830 167093837
    0x80d03050606070b06040b040e01060314070f0e071202040306181103010507020a030c022b030e010203030402010c0f1106040b09030613050a02120f1e0c040c0f1809020403140d 77
    0x3e03140c0b100407840201501d030b43d220b0ba480309081112580e640d0481c608154900d0000c003c0982c0d2850503240b4507100d240d6131000c80c018100700003010300c2c5d400307021821103c440241804580d181e4600721000d02130f19495010f0242c3c00c0c4000300226400340300320014105400e12140c070a41641c14800c000c40c0e00940010f00c00e0b818501042406a40880c1440ca00340d03160403d60f98648103440040c0090710349001d9418205c2c0d00d503500c0035140500c1107402c4501030007031b19022900a45100120303100c1c8012203010780451984540c40c030000d5220945001801e00840701006854220070010300282d000780e114801c0e044012491309581d01e01485403e4204050b203440d01c0e03003c12540c0e40c2c1c6499415441e03020344218000044247c18200621128110100b68002d0350000460030000c90600007100300840000d00c20541c1c014480d0030144104a00f08946440e08620454411411140d25030030031030450365a4919000001c0c00b1202c1c0c0050f00c0618418100c18142c0e2001c032112a01c5e0071003010074202007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 167096330 1250 167095080 167095087
    0x130b040617010f0902183f0d0809100c02100b06070b0105060705030c0a050106061709060a0c053f0f070309033623060a0e030601080d03050606 63
    0x115802205440032111540000340c2c4642100000150301400504125040b880801c00d103040204004001d07220010210255052080b525240894002403462080f205034400402e07030416600070300800341d100710ae9004440c03018505038086010b032200c08c154140075a101003000d01c911140c0b4060b0310038160040d1032813820040d65480c0e9107003245040c07140a00a001c00100d4009001c010710403901c46078000d8049803d20500340c9030080c0207000070700c5004005000410050700c3d0310840c850700703802071003600000c01103038641d41040d000070b00081c4145418041e00308900c648851340000c00d00310001c04114809201400b0340080c2e48402041040311001258bd14108a07081007144d40494002c4924500054051618507083c0d03220701c10303403000f4800c003a801c11b171910004511b454081048146070440c1c144542da50611044080f0240700060b00d1822260501c008a0400001614440080780740902500d181080030a0074200c1c01c0c4c20010064100000c940c1260740c06000d03081e040b08040d90b50300d03e03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 167097580 1250 167096330 167096339
    0x30e3d0903171f03020f0312030103150f090201020307120e031002120c0f0a08070c0c1e0501020102030c04030b061c03020706030c050f0a050307030e030c03090f03010902031f02130b04061701 84
    0x120803804021b20560a0301c0c006085070b1410040960703a0741c91800784a40d2940c4130700704000490140280980308509110016005817000e010b011002070341030b0020b50801003169282180d00ca4442910340400041c640355254941e02081040c00c252000c00c001030380d61482004018034004010b00c12040d1020402c84015581090f004590549185182ca440c007500d6041c000c8410520040001e806221601004103221514008104180040f204040c01e65680d8000580c20707804100c4000c4500c84060004001140041840c81d9002c1001003501d10442035188600444220550064005a0150005002007901752207280c0040a160518605101e841c244051032842036803400c0c002c109001c00480c03c403e0090f0884840f11400c0000d40744c445070b820b0400b9540380c01002180340304841c030f1010325085080c107200c0c070154913802a000d0012000384108000020030701001070345075190300b042178002001d0340785000f00c050074085102075512490004010100c0d10709000f41034000341c0b000c00400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 167098830 1250 167097580 167097631
    0x306010503070b07170d1a0f0a090c1106070302030718270e1509070b03090c0d03050706140f063007090501030c0501030e3d090317 58
    0x1c0b10030060807251340c0d0f501da1406503040620b2901941407180041042454405075070131404c00d4800c210480011501204100449100305201440e0000c888001c00d120b5100103421204800000c2d041c20f19054200f034408600e0190120f8400001940c04400d102c40158080320350b42c46800406c00000031355041c98a40c811404030000c40c0444040b20007500f180001154209840300742c00442615800a101070321034181001c2254034010130301450704003164403c80c00d01a2400b6013610030060030f521040d84144070384010b44010650a00030284546000075085020f40312802d41d2050104007142404001c44c003021130003800c0e05210340142c01d60102044009164420405a5611810303428500c1032945820f0000390740004e4040c909100022003803000e28076101c01181c400381e03002c10010340d0545910351215009140712200c580c072623051650841c203940c11021109446d8032062044190040c00700121814140110007284030600c91606282100080c10391240040d40170004140306206400d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 167100080 1250 167098830 167098843
    0x3120708030c0315120615061309020901090b0316080105010e010206040318050607030201060806130b0a050a0b06030a0e010c02070f060804080c1906110901050301060516020a06030207110306010503 87
    0x5150402c0400081c448507940070304040c5449001e00760031195240422001c1e216102141c046442105640d00d2a015041c8101220480e038405280401424148158000030790f010014140c10040405004100400c0c100001c4d40107c80d20000d01109149010000e09444416030009040c010581008190f40e40c011450390340c4107a243c40d01d244410003451100700b084001d50007454215801145403c00c0580551000041d600f402c8221840f565400a14410307084240b0002445007a074400030483e5107c0c0c40d0026500101d5810740400c0031521394010411640007240c0004010b501c400840f5842c0c1820b00c5a4125410ae500c00340400900f040c6514150b6011071282108000c038207400a4140101c200584400c03608400640300413a1306484540d00d0352031010b00c00c0c1c400510f848e11100301c6c000100100e510154041e111582182e2038900240c90940000c010030705c41184104102006a44507011800940b156840050715803620f410240a54018441c041d030080d40421300520a555001618 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 167101330 1250 167100080 167100091
    0x5070c29040b0901060902030a021b0703020d140102040306020d0906290f01020a05030307030501050a090606021509102c0111030f0c070507030b0115030209010f0f09050a140312070803 81
    0x956125101c43d61494014116940600d070010310201c10301070b40079600d800070035400da5443c2c0c1900c043c03403d88480544500c41480001d500914a0b5040d00004292405105204010500060509681c0c0d00e903801a07a10410440340340e0359a5014120030400d1900c01c0060558a541402400c940015200e8652190071354019100e004c0e5524400c0c01030b88200303d505a02c540c044141da0702c3e401d0030b90340074028280a008031442101c06039004900d00c9458468501240c03400d5004188004015100d401c0f80d1002410541d1b041c02140750464081c420750190310816070360035105003051240800300940042e0500c04000b01641000e000c0a1401401030071340e5040703044078000642c5500d80f602110310620441ca4010b003030740903040c2c0010a0204842c160b60488940b0003011818008900089040380700c0d940c0e8060100b08810f0b1984141846000c040a1601c02810000300151711440080e000504030762000e020710000100b44a01c1e41014031003a8200c92a060006040800d01d40d601180307800010113 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 167102580 1250 167101330 167101343
    0x903120b030a020a0e15030a030e01181e140609030c0f040e071706060406031e02040204180b0a081504030c050c0d0b060907021606031e05070c2904 65
    0x10030a00d41d0303a05004409405070300814600c941da035101e0f42c428100d18200c40c9540044101d4018041e030741070114050000380e43c160b43c1c180c900111400151a03084200700200740458000c0c1d008544607049800700b40391045594007103100289080380200d000f85c0010303d0b5038000c1b8400d1040d94a40c0e02c0005801d03803041b004413044464010b02001250083c01440080300f240e2040c0100000c1c0c0120140c44500c035031103041b05a40f480d9481c0d1043c0404c0d10120700c0000e103c50001c502d9600c10185080c2d100294070f02c01040503180540d224078449022030000710580d2a550740d04c01c040d0a034134066080200403e030a0b0050000131001d0002126400300051029046c0103560000c203041003414010400e510b4402407038903440550500304811001412039a690190780100007042084d8000280300c00384a0300c541001c1750080c103085041b406480300701c4504090300802164000001c1c11030081a22503100d075500d140c803104039410050074103800b030040004a5110540305100030340e2001849580710790000f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 167103830 1250 167102580 167102591
    0x90307180f020a0503070e090c030412030902130b01080a110306120c061903150302060a0f02070509040b100e060604030206070f05010501230103021c150b0309070e0703090312 77
    0x5209102078150103815841e41c030310005103020b03180c2d0001d01450007440701759a51a4200910030512030078000580b11010204003d0000a000407000c405036101ca40081c43c0215a2708001e60201d4034407044d010010459032b484060102041d6803004405901012242c0f00b0300c1052501850041d440c48094110340c00ba190007a8154800e040420101446c4080030f800c0036591452003420b040f4031141802c0080010b070801280200380d000c0054041c043d260001d140340d151400d40c0c0c50a68800305050103207800d42c020303404002401d0b6071309022544120300486084104e45030811a061043c0c0d8660040c0724110541e07001d0100546070f4005940c2925415071b00c680d5520400d0402c0e200724000c40c40000c2296080c200003040c50740b41140780c018aa0f00300c0d690010307154210030054003a401703003440450412640b03002c440322108040e0002d41008102c080702851140d240c040d880202d030300032501084c03164000d5004111041d1086003565014081d0b14040110202d41e40d00104910b0b604d4021814481d00c5a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 167105080 1250 167103830 167103869
    0x12007152703020102090f03150609061c0b090613170a03020d02131a04030b19060302030307060213060e010e130b0616050f06040c030b070c060e0a0c0b090307 70
    0x30704162a07081090221010700e0341d402d1500a010394024030b4518003e004c0540d40e902e99007000500540901c1c181e41c1c03200d400c1c0e6191014440e140c5401820356a0065104802d11605201c404052079141e00840010760103160000e0b283d482c0c91009001030201100f00c500290204c1c40b400d00c0600b8000510b110141e4402e030190048001e805042184a03149200040c0e810032070420032204801c595030300c1c8030361034504d20812040d082e40c012032002500749180a400a91020313000003c2d0610301541c44400174030642c407334020034503580080100720f4000340c0c00268405203040b0050074200502030380c98000305079850503000030482d03644030000a010703d94039054903141c075156401c102c1c05984040d042640710b0351240d15502e107012501c0c0b020b40300390181c0301c689040444042000d92240e9001542c0d44815444d543d5900c0250200514501c10441d0100c0e0110004005000b110042c1c07000000420020103203040602d002d65041d44031503990300e001c01450700203480200e54181164004104403280a662 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 167106330 1250 167105080 167105111
    0x503130308280c020f011a0f041b09030b01050d02060703030b01030605040c020304171903110c150c100c0f050a03090510090b1b0904020c10050901200715 68
    0xc60000001d04400502502c804040d6507001070320b250016400c84142d0000c05a074913003242e14078000007001d80200003852106082112010b116000090000242080303440300780b83c0104d200030240d00005200003010414840a508200d000d4001240d502001120300d60003c0d202d4400c407440101407546658441001c0d0307000c0d07400340000307240c003501c24002c5e80200702c002502c90f4080d014800c61b00d448540104103e200003d651002021120018481c44141d601c0903920092000c2e56841d640c0702e0100140e00984940340781d002e815035104040c5444e40c021142443c103125000b40d4070b950706898034840c200440e030721600d0304035100c0150400c10366840c80080120301a0510810181aa1050044407101d8075203d0340070507940350055540000765141c89a01840790000309a40f491450400c2c800301d07000b451b25034010000e00009000300e0305803061220300c550607180203c4e0445c0060359502c10640d9008440d00310851040f60031640103240a0555032003001420705c12101480b00c950317a2000c0c8008001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 167107580 1250 167106330 167106361
    0x180f0609020a061211030f070c050f160f06020d20070906081b030706050703050a09090507020d11070b03040611090312091c02130b031002070602190503130308 70
    0x1c0290000303024940310714029018941c049803440c103a0303161101e200c540c0300a0005032402080542510302603901c03140d2045600040c81002034444e40240307000d00f001c140b410400c050b018004d41c100340c0001c9180c008941d0212036036500c10025034008044051003158002c898a00702401040010165041c51a9040c902011904400611494441e000c180d122000520041c00c005103102c810000329100c00b41034a80c1c140d403140e10007046051100d480041d000d040a0700f400e812514264881039035541d208001d4807004c4d1841c0000d030b0030051036001d810341e002c450000f407080c1c1b02c0b008020203850102d40c00b143d0b100040c0302500e100d0303441080200188400d41219034030040101214000750046888440c2c560003ca1054416210703c1c0400c100244080380c0000550b030000c04400c08158240c1c15070700a4810504000d40c1802081c050101115240c40036120440c0078101c010384034a182d07022090302070310440506040c00700510400ca50070202c402d107400b0980e410311707140301583c0b15446940481038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 167108830 1250 167107580 167107583
    0x90b1b0c03100603060b0d050714061303080c0601060201150506131208190903030804060209030c0a1710021905070f080403060b01170f011403160806070206010603180f0609 76
    0x1c0c16882d41c12250350b82d0455410b4030702941c81040046520000c01080e10120100203149410540781007000c81500608000211000f402c5689800d15520010f44140d05980045501c0c0130049a40409100c003040a0b42c0544451f000030081100c6400140c2c910242ca4460385200d5140022450500d80c00340c000b03200201115003911151440318948110b4580110380040c02c041c0d5811054136495100d50711100407039826856036a5162100c5e01c8000c08ad50110786a240c0522a1440f03000da0343d211018154000e20404070035031104240700c903040e401e0a00300e0404d00b10303980c0140200b01c400e10050b80741002c10080b0b400c040c0d6279070030381e440c211604001824002d070410b607010400006004182c3c01071801c84909980e06d0814074081c44603815000800d5a5441d100910180140036640d084440d1500c1f20100508036102400c070783c80c1c0f0380f81b00b0020b41c002c02c2d400d8110038248895550100a481e000d4691402d090100030943c858000b85101801070140542c4140103010052154641c0030b4150345 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 167110080 1250 167108830 167108833
    0x6070602030a1e050105060304030c24050603010b1206010e040311060124050a09030b09010e0610150206010614090d1a091603020a0302090714040f1401090b1b0c03 72
    0xc0c90420b40c014014500a041203814008000041103502d203144a041d06a0341e0052900341141c80d6610304513a4040801d0040b503c112045e88810b003512a0f03414107040d03208040d00042142e140c03080c113050a542c04540c505019411040841e00010004249141540d200c0c0b1000f000350364490400701c817902c0d0821400d070040d009450003c51491742d010700000740c1e0010440c1c1c0207541c0c2c1c0b8004040340d0601c5283c00c10302c0000c11148040c800940b0041010750007880840011502c4040e407172006081042c1a907000c0185401c00d10100700c5c05010a0090101140c140040c10583d803400502070849820706100d080390203000129181c03960381d4658030303501241c0c101650305555410042d0810800300c00f96802d424520540064030103440740340f00c019080e04d6011782001c40b26403440d42440568203010708524240a4140a0f0805030749820003d800105403082d25000814078000185071100d600a0065040091510007408510412801c4034400c0480308104030504005c500790310b00344480f40b108079034503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 167111330 1250 167110080 167110087
    0x70c0b090a06110a02031606020c0114090c04020f19090b04120506010506040b0f0c0102090d0503190201020a0905011d060307021608010204060801030b0c07020613060f030603110f06070602 83
    0x8030014015040621640040040212050041d101c5009070180030780103900c200a00300c080e0842d5018a408688035103c05401e00e040d0f0303a0910700303444200e43c1500200750349101300a40c01c0002c01c0498031000c81514118640303001c014091006102d0030080e000e04410409403103005c1ea100703103606401485100005500c4540303607000c4503400c0d40c880f10251154403e900c001b0034103181c620119011501101d4900746031095506502a003a0024028030071155401e01c1400206d8940c0703036540c000d4038458409541d490f801c5403044013451008010007411a841400f8600300e054201c2d9481d0107540c000d0a00c08011500c1c424806510001801000c0c0c110f6004000d100034150001a0607104518803200d5400c005d8030340d00f1183c200e0041e4800c1400250400004101281e0700091140d08a44560300041c5000e20b60380104101d60f0140140b040d4594140c0c2003000b500e9800300c0108181042e91a043c40f05a01d951070b402000d2860f0240720344584100408003a50740c0da14400c45501542c0a07105549 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 167112580 1250 167111330 167111341
    0xf03071101020f06070806190f03060c02101802040506030c040c0e030c0f0a030b10090204140108010e090703060f020c010501030c0e130302100203041403120709090c0203090603070c0b 81
    0x1146541011001d01501c14580060120f403000b0900038420b06180e516804d0994410081208820901c1002c1013a1245480c022801240c1c5105020155000300400300740c00c6041007000703103031008002c4403902c480d02e05001c46558054080354070034610340485003c82c4d6601d0b80d10000341008040c00704503034000c0c41c00ea0050443c68102c401107403c0d4104800390b5050034000014054100100d44001d648400c5c1d554081c030001d051414299000080b100c1d541058075121f81c1c0c03440403607120350028000c02c1c41c0f2904141d0740390b074040c18280c090708034214410b001d401c10003441c070307a142039a0000402d00c0d03031204140a10040540e064484041d000c500a10407542e40c3c0c24113910590ba240070b9160404070060018115020142c0700b04050703030389940140528020355465171300070742000d0b004607510411138500980156041001d0b10270414a040710382d404d410310410180051000d0f50000a08505003110303202c00c55004030075548400307000d84589660399a044001c0302c0c0c01c0729004000b0300d401c215a00303105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 167113830 1250 167112580 167112593
    0x30f0f0806010c08162d1e05070e1f05060903150714070b040b0603030a0c031103120711010605151804020d05010b030928140a060218010e0409020a06110f0307 70
    0x2585241c05480c1b4a80c0c80307512002d00d0f041007400d04d0140095140041c200c840d441d00ca504452803a010702d01f82c801941e2292840344050005a8200407905103501c903803080902081c1811005020484100d0714040c040c1010948910103441e00d0841a003505000400046c0904602e08610308604003861740c6005a281a401c000811346041d541c00b00303c80005152803c002044603c05160784c1c440c50001c0f030096070200d07103c8042d0a410780c5503001c28070401c9482d120460f440390064005d601c070311031107070320018556003154410750205210b840c6030409584e881003a14211051120041c00b040c02c20800c403800b08029100e065404400c952400000040c00f54402e80a0b5009030307141c5003034030388140c0b5002c446448100d9120b22203000e00388003481040016825240006104140d9091303031032111141c2c461500b260405035084848500c0d203204a0010341c3d00c81800040c056080341c0400c210140343e00801c0d844110341c01001c0c00e0001d0040c494110410030450110440030f0f4500300c0e607403441140b5148 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 167115080 1250 167113830 167113853
    0xe10020a12020405092805070806010206090705060d0b06130f030203100912120e07240504031a090307170702120109020916090f080604030f0f0806010c0816 69
    0x10300041e880c2612842500441c000c4804640d0005c00d0401c45444810007455a982014030010040b2071580f0510950703501e60184c03030b20070041a2907440c0c251130320304006800c10b0030041c010003d0f03802c0111700780240d503a99410f41d00003000c0194005600304a00c1c001c520540304144107018086501c140c0020001420241103040c1e1f0701c240c3c00e07560800025811041910740700070307005040d0000040c848240502c80d1a03296041070103039038040741009030f08803024140900ba422416070942c61811018100d820443ca1003000521854614507240c40c50b1070b44071807203009480c540f001c400408081070180c2c02c100700341c2d40840d41008208018000f00f80b0f150802b40d00c0500128000c1400d44003080e45110184140d1001c01d801400b081035544d40d00448201ca0074004070701c03130180b04c3c1045011401c1130b21042c8000281000b40c0003441e141c106410f001e0b00711a0013034914010002c01c0c035044800e40350b00c00c04180d081502801c04038881d0000c3e1410f0821270198011003240e604c0c01c0c2100409101d58480c0c403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 167116330 1250 167115080 167115097
    0x60f070c0812070201151a0d09080d0506010306080a0807060c05070209151e060304030c021f08150f01140306040f0507020d0908010e030a0e0303090918010f060612050702010e1002 79
    0x208540d8504003002c6146910f41d10500c45000d41006600c0c821401c041f0050080e60300750400081c410b030340c2d69118600c2d40c1166150140c0c06d941e4404005855130144900c4020b030a0400082820811039aa0700c1c0d00d510803564014580c981380d482000740705000300c06a070003075640107285070004d140032070b0070848403103a140403644200304d03034040d600e050943c0300080ba40c0300c50064001c91456441c0e85042c1c603d00300650040760032800c05200d150141c2e0000401030001e000a84e152000c0b400e00c3c1410304500c51420986c0b40c17081792a0803000c03e11b030307812020107072503c81c45115413922950740c080007800400070030106403412403e0008000d0300960108144541a04548800c4800ca840c3d121590881c3e10720392031201c55034000c01040c1d0400d0300400513400c0450001301200d25003c18200480d42c014810743d080280c40c40c4a82d41d0303108802d002c1c01910000b07032816004210203803070044000e120125100c2c0c44c021003582c0e00003207001e2900c00c2d0400001841803a003100d1940d1004501c040095000064 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 167117580 1250 167116330 167116333
    0x212030c06100f050109090e0a080c010605010305060a0b0406120f06060f08180723060a08100806090a1401090605040b1e01050f0103020f0c0a0b060a120302060f070c08120702 77
    0x40031a483c20014800310507504103039211b09030b03a4140100900148032080b4000e240b849030901d50400180060000d1070258107400010071050315040c00581550005130900b84110813aa20a010250301d0700c0c19107044030510301c0d02c1030550341810a010000d10100803420301039407c008000c00ca090b080b415400c144440c5640303503000755849036856440c281c1420340800350f0350000181004210340c51080014884039200c1c00f5611701000000140712075000d02c0c50000401c158900b0010110f1031145203070024041c0c0d001418031882c003482c86507141c100c15100140803440e5a40a8400201c0c258407444166510420802082c00e2034148201102e034100c85c03105080fa041441d601c03100d89400b441c68100c80f80600352410140160005602a40000080c00c2c0007500501002e079042d1810003a12000b80e000f002d40340c41a0404070140308411850341c1054a01d00c030020007e02c0004c2e400681075500224044ad501032035100c120040300d03c031a10120142040b500400d00c403140e44a04500300b03010380c04a40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 167118830 1250 167117580 167117611
    0x1807051c0b1302070c0306150906080f07060f05030402010c0317090c04051503060105240406050a090605030919050c04020a02150106080105310e0a0b0916120212030c06 74
    0x403103581030744203641009141d00945d0344104009a841c4c3c00004440714801c40c0c28000030348584d011021542c550f0301c104419400502580b00d840c0040c8400d901a01180c505001181e1140402408911026000074100040004010145842010f9000b04088044690046410700700c2d8401e645071032100c1654451450b00001c18038100b61182c41280480014028015581c84d0400300504001c20404841600d0b00c42c41c000000490318400a0028000c44c1c0ca03a03684404007510014030303880240d0448014400c00f0424005111000606800c0c2081142c60242c40b49206281003802d01141c090340ca42c1060010038110405a00401d900c070509140e140c803880961380c0e03210b0861343c8180a200e241c0c0c0080d451510500302030030142000440402d08019000d040b030040910b081111800c450507401c2d504104030520402440403e50360b007200c0c5c1c60005229070030038288841a440c03c24030074185c9640d0381c40308410446d01c500403c041005e41000603607889100760b960b403a483c0e0104840700c405840c41130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 167120080 1250 167118830 167118859
    0xa0509040624032316081f171e0309041b05030103120c0b01060c0b100f0612060504060b0c06010602010903020d030e150403030c0f030b1807051c0b 65
    0x814268882c103040441409002e50101055000b000e6080c0c803040d0450004a540c82400030340d110280c02550804062410309410b82c400a1000c500903001602e070754441e50f0102e0340c1d01c0651f90800c00781c03076189003014207071081076011520304010054040d032040310416072000100e0010024022056003070700c06010001c45212500c00d2801c42d043c01c80042a410300c010701c003107100c008080385411440d042440d5403142c95221550b40b180240e02280c00641d0486c1034004020b948102590000c8070200d5001c2441c1c00c18003108403407519801160100203408803011400031075070300040d00800300604100140798603074110560039807000007030781c0320b5200d040000145c45105114804041e40c050b400303000140311461003100684000410b00426200d030940c0e009910703044030007042c09184240c03000500d0541080e070280540c0760f500c10b51014585411400000f170340381c41c4101103e40941f1100040304d951614000c0d5818003480843c8030840c070944801c2c250440041d8071508848030202c2d051081c04103030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 167121330 1250 167120080 167120099
    0x71103070506010b160b0a05070e0618011202120c090321090105071505071715060f0309030c030703020a030305010b030c0d05090c030a0b010906050307061409010e060a05090406 78
    0x18404020700070341c04100104541c0340d16101411109881050002450f105a100c811002c1c00650b200a14540c0d91010b1012441d000340300000319880c180c91607402e0040311091080b0600840811506000281c18003551400c0168125850a80c00240e10b11007800c1c80c5103030f50100d802c41c03440c89001e0b225101d0040880108080611801a0f541036200d140c4240000111a140c01c00c107422640705100c45c0103860b10402901a2510401c0141d840100c203003542009180070020240096007107013400c4419600c1500d4a0b41101c0c1400101302c401c0b0b81d01c2c3c45072060ba51640c45030300c030021001e000200c0c0d401c04156011410445044c025902403060340d0b01c03100e92071450b03c0141d820426400040015940c00b5202e50001030707201e030fa010b060711015a224400300c0d0811024910031640d40c0002401808a0003840c41504060721054005250031414040050803003445407e495041c000c0110700d03c08281c0c814410607649007806444142c80c4e9054020281003038002a425500c5603080039400b1500004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 167122580 1250 167121330 167121337
    0x61706040503041205030d090506150406050604030f1b0b0c010501082805070306020412021e030a08030a18061a01021b0d03020a060504140d02060405210904050f071103 74
    0x1c018002c2c500c2d05160401c3c64568080704001150b550001340040d800d04181481550300c2940582d01070040c61800c0345611001c52401441c00744112f29011040c8900d86810080e94243c95100200c00300c544200c1c14003541000f0200f1101c006c09154003c0415071120100143c01c0701c03240c8000034005a42c075915450348602501c2045030940c120100f0001940b4929003c003040c040c011019150216140d450341400daa00a820111030902c20044c04030450030b03d58107480e8204500403d241800c0344c88000640c840f1803141001e0024a400b00100301c2e0000716a1100084180403007180580010525249018128109030112a14210346021202e5400407856142e450f000c1c0c004800309040d41d00c10403401001c45501a0118403c00b056000000d4003803040c14000c5006013207a07d907202d40e583c942403170201e00004840c21904114140800107500141c04010b82584a43c4040e50310285081490a405030107552903202d410801806414003003c1d40f49400303406107950f000780350710901c0000c965911 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 167123830 1250 167122580 167122583
    0x14090601060e010e04020c0106060801050f01020a05060402151201060c060f0b0906060a0e0301060801150803040b040b071a130506161403150d030806030607090302062a010f06170604 80
    0x8140d0b454051040d03210b0444003844072801031005040c92510142d0500b1600a40c0145021036005401800036143c0190341410b8240d0074401005d0000302c0c0d90740e942d21502d000c2c0c0000c0c0034064442c2900b0441580e94190740c00030201044854075503135500401400d403450410103a4001c0d01e00280050b006004d8000c1280c80d00026000320815211841405402d07030004403800d0800082400c80d404940d002c2c0102c50041042000220303600040e0020103948a00d1680111941d0303008100400c0121040b909603022207444401040d00c1c0e9003036082c0300007000e03510110780321150340320000c02840362000e107100b95a443c01081266910343d11080103d0000226450b1000400d5081e40c0c140190020399000f1540990300b4165480e00c02c000201090705284004c9088000c039544004000c0749003410408554840158a4113000803451500481c0440c40340c855540381c1403041c10490300d1442c0010a05000c0344400c0c10080105800400c1c03644003c01d20360080b07a08207510081401200c10001a50a0245 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 167125080 1250 167123830 167123837
    0x5060604030201080f04020105131410020303160e0d02091312030209130504051e06010311090408090409230102040f08010b0a120c050307060f02061602061609050901091409060106 79
    0xd85900b09845c59001c0700910890402c071080200c0340c200d052900ba110002c00b00709161244261000c4100100480c03503280b14000c44d407051082112810688142e051300340ca41d030030b180400340616400b040b480d074000d40000c0e402c100014180401000b039284c86041c01c1d80298140060205c0e19402101641300d048400c0b50301c600d229807507051140c2c60358031140c3c1088c840c5084a0700d03016031a007402a40c07500780d15080103c1d04014010424400000071040103854200d81c0550a8540369840a5607809500310035400755995910320b0003045869040c41a0049a500d084124132010300143c034080e50150082c5040201d6030100042e0030340f0f050255245546c0e004215028080c1800690031902688042c1503603400302c04040090a600c0030701c03010018222580d2892440391950310040d11301580504508207102c4070003020b484040d40801c07280d030088003d5030120420401104201c6558889801159100d0390440c00004d401007150f12036000b840000200e40c420f80d80d1010134903140c010034451100030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 167126330 1250 167125080 167125097
    0x120a0b040c02070614130608041a09070b0705010b12030414010c0b04080703021c02210304050a030509150c0303150a140f04020c0f060910020705031b01020f03070207060305060604030201 82
    0x803680640c0d1052021142041403d0500d081181c40e0b0458010587c84000071071f06007420b0006009107043e03240c1440300490520203150501e00a05680c48136103120380b000e0b240b004500c490400401b9007240c501c0701c00c0100840d00701300004002c00e460350310500c80d4001c1d80386081e5038003010b5406010a516070340d8100c600141560388549a80c001343d0310401c0d04400f18001c3c0e80d800910340040150642c2c645456500030001c02c0640100503985505007282c0400c80c0d00b0920820002880000392040429854a00343ea00c030013403500031480c0c1401c10b9420901000340031661039803904e0000061441a03403c0304600c40420f00c4c000500041045034042c2d0719900c01940714280e210b0810280f00c1c1070340000640014601510701402c94200100c00e85111543d42004081c032400c41d40800801038030700100b074402c501e442c00550311305a5a100c0e9101c040328031030b490b131045041d03039400f94180d842c0424804080c0e43d90b480e04220080d282c1c0c1290140801080c900340200d440d90a0110a66090303a5040e11480c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 167127580 1250 167126330 167126339
    0x809010b0d260f030603010501091e0b040e0304090203040b071e0503040218010e0a1a010f0806030304030c080607021c0801050105130314030a03180201021e030708120a0b040c0207 79
    0x100c42d010741840d2007480c1149028900e01c44800420303800789000512500c80c14500101420354030113a002c04202405c195040b09198508481600519450318000036105110004500540354019841d5003a000c007081c0010244507940007948101d00c0b4040b810a55a5906001d44081d40880910050040d072021224455070180c0c0045400070700041601c0700c01d894034140c0c5191403800760025130280448405010505901d030049010400e406114891041c900b040003c0503020070000510070400710b10003044c1c01e500d05204031005541c00003240c010705911081702a548041c107031898401440740030400b14044c1c0c0500e1081070001c00c0c640d02e20304544d280500444250b00b102c0c404003803100c030380030b4000000f410346030035600710780741c16400366860383c1a81001408903600c0d04401c820040d0355180b1040142e07804119243c10300c6038284031007401c501e0500c4461450280d04402403010390002007003010285080c514620444c0e811505029207040d507814007042d41c031680042005a400f4030310030300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 167128830 1250 167127580 167127593
    0x150801060c060b031b041821050403210908030903060408090102100e060106020c0402070b0a051918120c0b0c0307050d090807020f0a0608040314210105010809010b0d 73
    0x100903601540000c03d007901e102d40000d0400404105a440312400182000b80e141018024111f031407880360002d1814a2040e20783d4042c8c0c0380204d031185e4440d804100b555140a000d441a00c4c09950042a581600c04408a1b207114054482e00094042516410006200e40000081310043d5070041c0181540751500d5603410b1050b04038000c04c90540c055180a4038100e102849030700c880c007681d0002040c3d9075241500290a10556582c001d00460041106a020072a15541640c204136003d0340010a5500c036124464200a1000002d0000e81014121055040c204100a58583c0549519032889442c038100b507629284200000300fa425255000401c00c400c850f018503804841403d0681c542110080048212161003e0449901074081500303002c1d82410781c80c030145071400355041e2902c142800c0340600348040085c00242000f401070b004c0d181d010725076004d0318142c0500c0042e10402e0341d00045041e0400c0d0090140700d000849580000b203803d0414042c401403075a02902c01c003030302c1c401c03500e404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 167130080 1250 167128830 167128847
    0xb040c03060542063c120705120a09020906010305070c03080601050d06061d040e0312060402041508090f030301061d0d08030108160b04030b010905041103101515080106 74
    0x3007000420001650129100c0d41d005110b0390070054208646141954004405c002c0d51001c0030401011801c0010038440b000c0c0c007194100420f04180b05c0e615681c2400480322481070700c1c0300d140c1c1c112500062054022840d0049030761a8802c55000c201d0740d032003000441c00c03600c04854039400242d40e2400403020034061020036801c20018036100740340004002c1401c0c00e80b510340d40700c01c0c00516844001481000d01c08001c1c0310fa003504580c24408031004100240d87c0380100210203800c8100c110104480ea50759504550043c040c0004610340140452000382100380c0c111084042800740d900c200c4d07403498010044905803035031a203840300101112004642a54070030320000f5000740102e107444022895844c043e5009100500042a2000c14441c0e002c100700c1190b4411405101c05100a100140c60042a54151003160303c00041599460615200c0f00020301c68940c2c040c003452140f07151101040c0c0001c121205c1c41c40c50880c0050f030301c3e103e196400700d0824014000582c02401801110f106480340d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 167131330 1250 167130080 167130181
    0x201020c120a110d0201050a110115030b04020907030917070302100f0603050d080f010608150405070f1407020906100519020a02010306090c0210180b040c030605 71
    0x1199552401500810710344409144042150792114204800700038184035550075402d01562000400000796001030030380c2c05458009014040034a41900d174203c800d5121841d00324850203000459503490802042c80c4000b55400c1c1d0081c2003000004981e40d0081c019814a180c1c058412004c02c210041c41d402290481c4000f10118041c08000110f40c14850141901c3c0381d03640710000810920310300e08280f40440c3c5038008400e005209003008a55101c0240340ca0450300d0707504146010740d560040183e0b10340c2c1075941e8258000d152a062006490340302400c3c1510007400e8540c2409030350001e070080414011041c00a42c0810341c080014100d0401c0100c00f02c400e240340c189a410314400c2013040c8192940c2400c001d005070f0042452905640e4903000d00c10007410b040d6410001400301000007501c40404035580c160140e20b4141100307010917020354a00c08103411080400307550400c1c0ca0606c450440c1880203644170360600000c18640d4611032265601000f20010705d103040f41441460b1000a03110540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 167132580 1250 167131330 167131333
    0xf020403170a0207230418050d120501080a05060c0702011b0b04060b01080112240606270b0d0b060405060c1501060e0303040513020f070807050706020d1704020102 72
    0x1645018001401e0340386078085a0300c81e40c1801d002460300f005503020920a15a0310640d400043c3d504c2444407001c0b20980b03011416940141070400800e124140003002441801406280b00da88440c01a07001c400b005024445640e0702c07903500d60f880cdc03031565000c0c102c0d820410108044801000051904500c117040503440012000c01d114511641400300791303052b81c031010400040107860321461a2101090800082c00d5040252a8100507964080144250056180744049840d080005814004800410f100d9070351076040080106c072203003140f10946084001400f43c094a001c3d880b1040c0d178401c9143c80c0c14011008060b001402400c2c202a030020f008000205081d101c4500030510300d0302030030040c0403d600003510800c0c003c005a00400400500258200c029680801107804030b8400710ad00d600c43d42c03501c60401c1c000b4032030308003214640800050385804021100020f00120750081094031400c0d665210180c0e01e40d00785100803000100c0340681c5202c44104021800e070054018030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 167133830 1250 167132580 167132587
    0x1005090c0a0e0a11031311030a12200d0e0907090909030e0108100503120703020715091d0903090d0f0507060503060a09060b0910020a121206090c120f02 67
    0x4001c6841401c0d150000b600449030b40c0308100800790300e405280b0300040c0d0900d02031310713600d85170045800e42d54044000130040542116000e0f0540d03010060407400c6500505035071074600c01024040c00c504e815902d01014030801c004044141400454400400c8034191a1255525454003c103c40d84000918490034454101008580d20020744a8980c00a10036110100196243c10000d0403030300c0d008224400e195007250042c061380c2c40120f6418142442480c00316203400240c078040e4200040c0d6001101400035041c82142c410b03034040700003400c0314481d07254000c4c1c080300d403010010303da0740c1118005e4042c6d01c20010202c027030600508044015001c0d071501a218007031035031034500702400b40d031103000080c6003c03084c4510380c0341000c1100c0060022100800041d4500207580d0f11900a4840035485006040b90801c000c500034000c1040007580310501c440d100d00c40507805080b0140d51000c03040d1080c6481800328800c0e00c503110740401400c040e103540c1403090700d200360381c0060501000d030805115001d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 167135080 1250 167133830 167133853
    0xe07090905010605090103050108161a0412050106141009050607080c100606140c0705270c2101120f06021314271605040317070507080f100509 63
    0x900c00c55000c0d007004d640b039640d1440104001010b03250113802c00007254001e41c59065450004016000417113a00c0202807403030707008143c0c040d251030251b54040c1d58503806000804e020000b040d440700042d50440008215032140d10804d110501c0c044c00f40c0000400d00b05202480940342120250818501c5003d5803441d141003480c0c00ba04000405002e81e082507261034091250642180d007100e0a801d40096090400580e0342e500b560390000e51140600803214035011b90040702c00b1084441d45d0841501c2c00b0b6055090061500300158425032000060307030420340d00c51072103040f0002c0d014101d8503d10090118010786455a586045200208a4001358204110056184030300d182c40014116541100400813031882407104220000c614512107041b40301d000e006d401100350344140c00c445060342954030014408001c0d40c0c42c0c42030703800160180481c210743c40740b0410b511004100d880e00c1007040d0b07413249a03100141c60355050000c03034803080f5400540d000b070510102c03544803a922181a400310b0b035608445 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 167136330 1250 167135080 167135099
    0x50303040f150f0c11280c05060406080a0e010903050307030509070302100e0102060a051b0a1803080d0c0c02130c03090c0b04150e01020705040f0b150309010b0303070506010e0709 79
    0x3e01a6200a8a880300b0a1251694025a00160790410400500f0940200030102062800c0400c0c06201950141071882c043c091032a251901416000e480f155903291541c80162403c48221030a91485040c00c0381c0d101c40c0d26040c092048102d90540360641162a404001d4000d8803000705600c0f014443c1680000269179054841c03000740c2540e031030b03000c440b0500100081c10540014000400300b07040200b40700d0510b05142100c2c0e10070100311800b07507c1d03102c0311404032904404d15221440b2401c82407801b0040c0150381c0e0091801c21a444410008200c010000355000300c1601006540280ea891500c0e120030400c0d0800d03043c501d81480c001400140d5550340e03550320300c5d40343c00514000c076000c00d00b0b120a90010030448d0040581d800d020300c3d1310042d400001e50701d51050240714025a11100031080300151500680e10500b802444480a20000031303d04d5817940045a400c4820360904021140300e0601100b02c44000381c014000d02266800c1030b400a141200150290081241584000461006c1d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 167137580 1250 167136330 167136341
    0xf080c0d0903030e010b0409050c12030403050d02100c030507080f0a0f0501030b1503070e0a110d0e01090c060e150915030f0f01060f020d080a020409020403030905100c050303040f15 80
    0x100e6240051140b08001c40c04d821140d502c0c40d0980260701d040021404124009460f004401e404c95102c00d00300c004807125410341c0031b583d10040107481900000c00300303640c0225400d2028100050200111260043d040f81510303c00e80745400460030a001240e6403003840c2e4a0340313500254801011403c201d0700ca43c16030440341c099105a8a94155074144064100c40c08803404030080d0440c000d01750342e400c01c0316040c101034024183e01195039450140d4988241300034150341c02c0230a910000c1203055214210035020702a01c500132100862a094003150300707402180c02c80b0031a04c000d4140c1240600140e455461540a000e100f6400f85d00070400a41c0030070124001c61040d02801100c5041d4101400c5041580c241a009a414440601211080c00341c0c00a68541040b0301440d2001480e2600c2c040c0d0b0000340b150390003110b445400020040145600017200700101c034001c0d58203440101c2d030b11908844410500000401c990401c0020a01042c000b28907003400e02d00951f0304500c10744244506804841 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 167138830 1250 167137580 167137583
    0xc0a03050727050901050a0b0a031a0409080702090f0c18061201030309030611070f0f06060308031f0e090c131410080606011106060103230103081b01020a0f080c0d09 73
    0x740081c800f48000e003040003c1c5401810180c84904d903907030900d00307110024058a0300e1902010782c8c0c1d00807441c440740041c8110369482c501910400642000e41030500207a0f0007980284d004450480104e80c04c54061003403a4461040c2e072482a05180c2a0002d60042030071010409901c035105000941d42d40103140c1c01d132402103100340c0790f90990608d1840c1540c240d41c80c1c51025508808213100d810041007103100f440707030a40da01400900c414421450090024a1703281c0025003d000084208201da02c104960140c0b000440d010004005940d00300600c00102d08903030000c42d5802c503040d000c0841c20650003172800382207546408203004841c5220001d244030304039240400c100e0105400c02c50504140003054200900703181c00802401c003010010354a500152100d4100355a42c6801c5407140c0c14100c0a104c2c2031031103003000b007055070350341014503868100b0301081d420100c2c850b021002c410414404c44510841c80c3d1951218060400000d03209c0708001441c03114008003c01c50001840418420500180d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 167140080 1250 167138830 167138897
    0x6010612061805060a0f030b0708060d1401020315030604080706020f0d0203040c0f06020105041a07090b0c150906070804030e0d080c010f0506060c0709090317070c030f03050c0a030507 81
    0x249403000c00c12011205d168413014a00c252020140082000450002d511242a0400b00b80b0354031100c0220349c0d07018103428040c0c0b035601d0b04440c060319114103400850044001299100a401d00b08003090385a22003a54000c00c1c4013030030001480081d2240d00504205a10348024504041010b600c4905aa1048504644549030386100303001c600c504000d107401804452001b04601d103013642e030b0031080303113a604003500103d031b01c060004000d03520423400140980801981c054079801034940f4103541d09421400010400f40c1e19001807452500015058415026541c886981342c449840a803402c0d031040301d002c0d81142c001c10111012401010060940c0c070b40840001031700203250030340c1c001194030140c015849400d04100400b104840010080300792007400e031000402ca0300503e010364815072805009030344410f0410810050300d402004042d805400f82c2c0303d400d5509078116044003207030802ca03105ca150b03590900465155074480d078031040c2d01c2000c606142c003440c4008203d00e2241010030103103c509 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 167141330 1250 167140080 167140091
    0x103090b1816050616050c130509010b031207031812030c170901050d020c070909150c050702060a0806010c390b0906070c091109040b0111060106120618 67
    0x80c1031080010104103012296002e408504100002d942d510804450012400e00c02007504103200301404002d008190080c298111383c1c12140704c1070080d09048401c03a445510b04000c040b0030b42030115245070203a50140c0e24a180c0301c000d55047c3d84075800c1300c2200342500781d500b80215800101810360840180244c4501c1d00d44541072070600041541d0000d605091001070254203026600001503840c644082ca101580b02c002c070458013407a20003075a010391a000c4c00c11845405008a01c0c1d4801c000c3ca1031414148130205c52400306540c00d116a0500a4010000300554451180305000d0707146c004205161111401a4940b14051803454800105209681d1756003800588440b0019440025440310a843c47c00d0781740284104140c003a51203442e003e08000a036000800202911000181084031410451b010300340640c030f01c4a42116286902851030242c4107a195801a01d283c29100e002c10300410150703003000402c5a07000e51482102c1c1c1ca5a442e003030003140440da20560400e8031030b81d40c4000900d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 167142580 1250 167141330 167141371
    0xa11010b0102070b03011503111603170f0c03180f0106050f030613080f2512030b030c040c0c08030a09050c0d05070501080402010e03010f0501050a05220b0103090b 72
    0x21100c00d111254155440107600300300c80e0442c40140c034110345030300c1010002540300c001c0640107400460142c00b90843c4c00203200322039101d203d8034080d805020780c0d01c240c042421007102e02c5004605030f07071529a20700040006401c0340c44400066a2003403940b8040141e00e001d000200d4501001545205001d0b51034a2003407180d0704103140e40ca40401021401050503041407420980c2c2c0009041000d0805040003910304183d4085908079255040248405491306030095440c803014808035808440b0140004e5400c02e030300e44640900794148400401815030035614904100041c044401d00321f0034450b1050642c00407802c100061482410b4024001c1004d42d0145096401c100307822803564400c2d0040c00c40c4002184000402000b134036020309108085850314001a100b21002e0b04003da419801d2590b04409040e06d904640d049034000d03112041e496884000b009030242c204502180000a141c4220080c01a40c1d0003081214806040006015955488140c01581d00302d480390391000f00405200d0307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 167143830 1250 167142580 167142583
    0x3080715050c040e06040b120601030b09010c08040809010807090504140405060a0e0a0605041e080a020705011d04020f07021c050610030f120207080303010f031e0c050d14030a11 78
    0x590000d00d070b40256140604081d83c4041d0242c3c06410540621340d03d480541032911745900e0b403648014030b0012a421507a40349451804404200c0d02ca4016508003680d00d00018000c0d04018061350388014441d042501c010011220341d14000e201104203c26403038000359035240c134455121aa440a00c0341d501174501810000e1030a00013502200700289401c100c2c2180160100e00b5810055110a000c200303502c6604003030110400200c80c05051840030050401003000f138200411218005409546200e40e840f40192103a01e5030303051144006000081010546c40c0c1540109600d07416042c00301d00b000325030f40200c0c100d05a803002c4007021a107401c9402060001c100300301c582c44000070856500a0341107a8400d0255001d684005095075a6a40d60103401c40c000d220041c082c100280c02c40740c40c1d42c2c0d100380801d1201490301c0245c2e46243c507450300303082c03c03c4101c0c00b0f56101c2d0303008844d1005003880c18040c41b0384840c50301d00950303000700e16484030401d55400b030004100070f4469540c0d0400036a164140c80c5d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 167145080 1250 167143830 167143841
    0x418110c0f060f060a03080d1e02070201032d0b0d050a05030a2705060a050c010c09060f0c0b130206040b0f1206030f070e060a0801050115081008060a09030903080715 73
    0x1502044403408014180c0d4401840c1006c0d285d102e4807080d2621111385140000e0300071400401840b2148018000000b0800d502600c1454000d030b8040c41100100307000105041040e83c6820000d22521071075050303210322604200d0170351401904070440305070f080d00c46504000d10848111116040000c280700c04540c889070903100b50038002d01c0340ea903050750003402d182c200a4511649000f624007040740c403074160140307058a6608034454020300081001d10300044c9107413100d006000100d4120a09494003510550a01c0704080c2d00c503644e4031042d2209159038000d01c101ea04101e030300400400000c2000d0309000d020f8140390701c5405602d61946ca02c0b00c0c000700f0100c802440c00303001e64481d80a4014000c4001800720854150014a144540324007010070a20748407a0040b2070780d5070030000001204078030503a242c2d07010b00c1e281d0366443d8540c49209941300c3c0c9220707512480c1c40b40d911850200c1c4c0000701c2a070165000501c24203041c031859690b41e407441c04036000b0400c00d8400c080c044116900c80324050060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 167146330 1250 167145080 167145091
    0xd09030905010908030a0c11060d09030306060201140a0e07051206060102060a0e0a06110f0406050d05060303042727020a05030102031b0919030f0515010b0418110c0f06 74
    0x203e4403a030411000540c0d0780190800b16041080001804050200032146c0c003980380000b801c0107541c0c103045d021441c040c04400804400091500340001030f032a1041c481c66070003083d0780440360080d85400455002800243c09619007500825500182d60f42e04c4401505901031604058291481c3c1840064284903004104200460800e21001c3c0e001201180114816900c1080000da045618002030041d001d401500c2c4200b001c00a00460490f4000010b000f0b14100d691007405103640301c1c014551240128030030600960707040c421710841d200e1030551007200710700c141100080c0201e60862048800006943c10610500200584401c1d81003080301400644401e400039451802d040c80c1d01d215203081a03051084544000c80d254410350384919a504405403d0400e0050658807400e0000785441c010104560701e01c604074103803544141c000ca240381299a890400f505251400012030803e01446950321170301c40c1e40e40c210309c07160009240a490703e007910400a0802d40b00c1103113000d180034805842d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 167147580 1250 167146330 167146337
    0x15010e15040905071d0d0b01030b07030b1507060513020901030f060902030a0b01081006060914040f05040308060109080a02010c060209010c06061514030105211504030e18130311120d0903090501 85
    0x80020111f551840c2860440e031780b0010b4107046e40d84900f801c030020000c074021164000d441c900a21694201f1401520b520760080d44100705544507409840c0f030380031205c0c034025003140c0d0200c010408960b900c114a45814002c3c00003003001000c0c0e90020b0b0030032015900c100c520701c101c5070051004070020480c504144520301e4080108905007000036103140b0f983e114180c002511660031503100e484981041901105012040c440b40c14a450080d0000d030080f288140014070a4400142030400001e0b507450301c6070107131141c240d80982c6450745401b80d4000c0c0e04150610606100d9000003410340d114040c000e000740c0c4c140c0000054524001018442a00c4200c004000103200500003556406922843c040b41e00b040540300b003100e440c0036424514a544205007043d80d900c02c000c18540c0049020303098010442e6036512a030356142950074503030800d0340d1500d01141038015002c0003030b004000c48200c0a410000715560008000460003042e0f1101c080000c0d02d94171034a83e14201504650101c018040909 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 167148830 1250 167147580 167147599
    0x321030a0c111b010207081506040b0a030c06080a0e03030f06041b08010e09070816080d210504050304180e010b0301090812190606021515010e15040905071d 69
    0x1c481503840480c60f41c050100f000d514407120041e0700802c00305000341405010f403500a1047e888100140004071500b600031801d1404010403498203106c8101620342c00450041c3c0b4604180c0116070903500200b85009446e904c0e410448040009c0029500ca070a03030703e104501901d00780e018401a9400c8071142c1c42c28070300c00085c28451542000925040d03440d40c405d00c800681e60803540314a403c61991040c603550054610182125030709000500c25a8100030480706898600030040303071002e031258180003040240c84402d04102202e9003190390082d0240d002c40e81416200c680c2e03100c104000c203810b1244150744d0140482c0151083c0a260f0208a00301c0080280030455120b0240c6403061a044d5070740c0640240c0007074001c1c42c1401c0d0301c4070340700e450250030405280c54040183d07031603a48036810300c00000e040d0005145802d18801e015048035042c1d42d801040c02ca94000c4c045154501012288013a50610020540e42036510610f0301c680350396500c1000841c1c4251a404a00e403910011602908800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 167150080 1250 167148830 167148857
    0xf0818040216030e030c0909070618060f0518040e01090c081c0809030d05071101050901062601060902030a1e020412030503040f0b0f0108070e04021008060321030a0c 73
    0x9000e11601c0f0b805041c0540e11550340c00c00a41402c00306007509078840c2c1080240249043d000070988182c0348540c85440c6583e0400c1102c030303007807020303485401c001039402c3c00c2500e0f0b114402c1d4040c180200c4828284100210617500080582d10180d1a410240e90b4030100c040600203048080001001110b01401d00d1078a802034084074a4921069075050060400100d00d4004041003100e0020498500801ca0380c1800480202291a40c1e802c8160f15802c5c03401003450020184078000444103141c51000f140c110301480804404400a01002155601c0c140010700c44042e00040d4442d407812034000440d400e141c8820072080300d04000d6010200c1c8103101c03d000754940300d000010a1501410640e842c5c2d503c0d4a84001e415040c450000c0110f80340109004c0c2560b0b503501c141d4142c840100960b080c058171060f10503000d03102201c0195104619204021483e80210307031464005030054251803034000b070980340c100c002c0e0b01e0042d0031808503000010025031005038841e00700311003c1d61a014800300d080c0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 167151330 1250 167150080 167150107
    0xc040c1103090f22020405010e040b0325270c0906090b03040206040503010911010f02010905070e0405011b020a020405060103090f0210120f0b1806090106030203070302070f08180402 80
    0x120580b05001d0402c034002907a441e0741e406040c04800f904601032540c89070f000e5801d03101075007140c4140d50108070302e00b00540051502e40200c0c50140d2001d802405036516158041d801001c100071501c0f8002607010303000c10504161000303604907000041d140c3c60381c5488102c1d22130498051503040030810810f02010310513103034007000f0941124025540c0d25143e440d140005507107441640e215070384c558a0102803d0422400801a040c904401d0725183c0d40d581e01410240d082c0c4403203c00003003807030b00700b03081c00d004451885480303e401030300038400080c00d04100005091034120300003004001d80d02c582d01c0401107241c580901070340301364286028800500180d9031000c020350981c00c0244920140700c0ca1207403c6210f90148204918503600c01c0c0004d6002e40f0306000140756004007540600c81111010344407e1404100a000c0c2c0700c09440c0c100c4a0b8038002d0210001d4002401800425800704111004a400c40300e4405a460040d1081c540e074030003032241d2520f1020b114076414040c60040c041200035122 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 167152580 1250 167151330 167151337
    0x4030e18010503073318230901050102100906020c0a1a090d080604240909050f010605090403180302191d090705061c0f0b01020d080907140619020c040c1103 69
    0xc6840080b0618510b004043c0ca504403000b26110311109006e2000424003c060060741001001c180103a4440c2141c03028070400700024040c060249c0e00c4072701da41448034503e5004510315030061000600700f0340c00d411003d0400d00409026205040c0212040120810f00c0007104d8000c0c6c5000c00400a80150b1240a0420180201803a22450740e8045a92801c025440c00350f110030044c501d140c0845885070301d820010301c0d0340c1c0001e0f0703210700c1181803480180c001407040c3e000b41c504c014401e0960307a5480d9400c40f1001c4246000d0380300c0c0c45141d50700000503200d0201c1c01003c00724000d41c9444140c18401c084041c1d40c88428080702c070360107980600070822008a0b4805c19180c0c2543c08580c2e500c8450007600c43c080b4a05281d50303c552800303a071403031440c12903440044d625000b60f00342c039002400c49000b00d82a03203040d40c54000325000b45208020f45e0602e01030300803540350050308d12410030760400710012503140204190005a0481401d9480f10b00c0c09104400303c2d540c1500b400051a080c442d4075076501d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 167153830 1250 167152580 167152649
    0x10c090518012105160602061023090c040e0f0f0a0b10030c05040f080f0d02060c030114040e0f0109111c120207030507061d01111504030e1801050307 66
    0x31084803c10003444828094564054400c0981001c5107a65040c020b5884601302d4094601c0401500040746010450b03204014052000300401c904160342c0c4100042c07010302402c1c0001d00d02d400c020000c1c8130f000000304140b1a4a035114490442c0c9805000400c0d080e6000b8015150189000f404040550300c04072024400c2d450b502d0300148040c07280c2800e40340b034030a0f03401c4a81e052140705400540071a0015490201080c80d909a802c034a40307600c4240c0c0d0300c040039941c6005d18082440144040014040540000b2100400216560a140900a0400c09845e4840c2c1c12a510b640d075820900c541040001840c400c140c0e031603201c03c1d0b007900d182c41240c100d044d4000c100c07141502c5250a003e01c00c01c0450003668004043d80d2007640e803500080e041c13070400307240c8202480c003025402c2250341c01141180600686000900080022202482905800200110700707102420080c1d80c0d1540f28611030800141e00c2180a10035541031104052410103030b5441106908110100d036a044041d100a80c1484c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 167155080 1250 167153830 167153879
    0x512090712111003060b030406020a020726060f0105030d0302090307030b070207030501050c040605070213110f1209060c04052707031a010c0b1611010c09051801 71
    0x26111254854100045588600d802419084200c01405074880c01d0741051981181d01011500300404254185ca52034404c14035020307024000900880c0c2d190f0020b04030080144141c502080e200c6d1240801900720040c07402e0101c0210418400c0304804001181d0440102c0d000c50040758035100010341c0d51904100a81e0415401054460680e1410080344d80916031190101c0318518004000a50341d48062009946540c00d08004c07503e0441d40808444c140c90140c0d03a414503020140d0203100d04003100f2241e0380344003903071124041c00c0700750000c01805094040c60300b00359490251000003691810081d2034100c03503800c02c0c010f0018845e158022a41125000e841881c42a24a0201720b50301003100b841101e881c0008a00300180594154047d1344455141803010344540c4000d40111080024044010310030b04d25000440c0060000500103841410b551502144e1502c00c603801c1400c0d10f000100d2003004c180d030003500b070002c1d261400c0409070302c100500b20401381c0d6240040d062607510f00145100d000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 167156330 1250 167155080 167155117
    0xd0c09090f05010f12141506011704030801030311150a20030c1b03040b0c0102070201080906070c03050d0b04020408010f0506090c030411150a080106180303080f09030912010c180605 80
    0x1003020640c1186c407a0303480c0c0301c107541500701c01e5500d45c0701105003190001d0005410078440c81190030300c1c1a005004a415030b4a05d80070343e0843c0e034180d9413166014048a498418043c41c081412405201c2c54400e0f4070261780032884071003021035000342c0025404280056a424000c001071a10b920059a40550600c211240340002c080502811031050383c005840c8101c0020b000b20348480150010410507101f0fa072610010b1ba1904030b1183ca8803400d03901103000500308902e6031301291140300503007a06c4611010016068440350000780481e0311a922241a0741d44174004422a02070303070b22a440c2c4c07100701a00c13148040d203000d40400700980b0000b88006c0040014270980407041d02c445075052011041d8119155440f0020240988101402d200300030008500038901c0b040340c82c5640c001400c0b603505445005280e11411516100b1070ba00030409021844180030703607541036880031060903504100c0000018078940e0200010168010002d1452840a980d2020003400d91301804039101e18079107044890300b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 167157580 1250 167156330 167156333
    0x902040b031b0c03030f041203020918070e03070f03060b01080403020d030e0a0f0818030313060c140105010b04170705010509010e0406030803070207180504020d020d05030d0c09090f05010f12 84
    0x10b601035070036200400d22000c0300304040000700090340b07400780c1d008410b0199054a40b030011010381c40350003591500407070064120721880c004030040c550010a2410507110b101c00001c0441e24092f40d6500100f400503080c8030420a02080307102e041c0640e002803a101d1201c0c6860303100a235461031032005200c101a80c0e106c0c20b507110075003845100c90040e803150139646006c42c0d41c1802e09550b000b0901420243d40c0710301d04120145400003c0b6500840c200100020552030702d0001e40b1303210100720003a83e90740d80c0b02088503c9010280302c0d0754040c003038141c07456445609109600040c04107174225409583d02a2034207010f640c0e0000c0941d4000da00074601880480d0301000030030042e050301d82c4014081700b80070040c00302c2587c010580c1c0055422614281d4861000c1c01703800404d40d8010b45c1c001e50400141103c00f03000d41460355810b40c5180c040c008580c54107000280d058111180715880a000800200043c8152070650088000300b1020002c10f0109504000c0924110709181c441e1521940312840d030b0b41c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 167158830 1250 167157580 167157631
    0x2060307021501060f110a0c052e020304030b010b040b070b06010318050c0127030204090302030f03040f02100c0b0105010503061207092c030711041d1005010902040b03 74
    0x1214010340d51460400b65030b4403c001380c80401c101d040c2d94041407031207418080756800024140c00c800e80054180d600c10346050240910031071309015040c1007801040e5140300f0110114000707920118954000c5645074611b00b044505040185c0000c2007140b003c100400c0011510400c2c2c07103100384c07c10240c041e01d4541000503401002c2c0c51000001e0b81000f420182c05114000c945041d100d20280c07520201c04110302c804420f0714200301d10f07450300742180300c0d000d101509183c2d01007294140310740100c81c5401900c2c44031700f0094000711412a00c1c01c60310001e400031800c085035140a100c80c68103158020744910317907902c0041001401114104140400054030540d01c80d000003401282e00001d58084988072007481c0040e0020100a8400303280301d01c80c122100c010010485043c807071000140d07003459500d40e03440c0024203002c0d1410354031580703560241c888071300200f020205c2504140d00600c00c0041011604080d120305901100c080b0f803040c042001403620104c03c49505c110001c0d01008494100f61404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 167160080 1250 167158830 167158843
    0xd0503070e030d0c201c0c03150c09050906030303070e1306030602030114030a020a1413060602010c020d020f0c09040503070512071b0b1210150f03051e040206030702 73
    0x907814800e4a201407102900000000d0f071440c0590a4240342c030761031702201c0704100c031600481a041240d8203880030030040b14210310082144980b061011003030392502d0f203101c0002e006201d481074590f01c00c414517603150840c0b000d40013058280c1d9135080d9850898002912804002c24038010b001141205440c9a80c1e04641102d0941841404024058403070030010029002406503400300c599100d0001e03c603140c0012100c001641c02480d90340468248102c0c01c0d44810b031511020381041c80c140740c060082441d402400003420041c0e00001c1e135800c1001000f072800c01d06a0841e030664000005050141c8000b15a2070082103040d150218917407124900946580b1030190007030641c0c01440040021640d0342001005460302480b9000040c000604018900719841c0c46142c000e824200401d030f241d5801a0722095110b080051103031446981c91850f40242d45554030114001500381c038080000c250107200f0103408c5000441c040d030400030088074055800700d01074006441401c0100001e50300350702c00c0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 167161330 1250 167160080 167160107
    0x209061203031503120408210904020a030e0c0109050a090c02030d06140307230904022101020d181509050a0519060c050c1c0903020301140603061003050d050307 71
    0x441e5036a1411100e02045040104156482801400c00d0126202c0103802074409603100340c405800b54000b0f480c00691504994500305804140034402c80040b542c1c0c80c406807403640d06585001c1020340301c0000e0203040002000340981405041c12051000343c03120601a4184c41c200400091002189001030303156004a0030b1340c444003418004042345160160107102100e00054044881c60780d122404050070909030710000ca000d24191140180c2860940007283d0010b0001c1d188410000180c01d240102c490581050105607400081001e4511824899120f003031000c10040c666511066881055001c0c1110307d00c04022381300d6400c3c0c0184030741404a04040340e4002c04072105245249080780000c0007098003501c00c5440c003050b0080160045d0121244200340344090404804009031103041800a8000e005c00c0254060300800161001d10500c1c03142c81c0d201c62000140d00c0e10004051070800001c02c842808034a05208000140e000111980e03051117030704000740c0302d13501c140e422103807881c03810075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 167162580 1250 167161330 167161333
    0x80c010603061d070b07110411070f0317060105090607080f1204030807030b0105041410091502010504021002010603020303030a2a180603110901120b040203090f1006030201090302090612 82
    0x3001441549903e2007000f50050341c806035490290344038070000280c01903032000b40c1041c18031154111286059030000da081212401c12600300741c41c1e900d03050323600108a4022004102c20303440d82e442000c2080d0000b607100b0824a0624070b0101204c000c50018003801400800700750010519140c0600381d0b4065400da116224030708191403509003001002550140d400101103450101080c00c95440382d82298203075609012480d21400010040c0b1070440c05104280381002080c0d0b178040b41c05001e80c401228903103e25800429942007074010003040c0a0320407000400e40e071622504000588000c000d599000500210009042d100c2080008441d543c0c1c14442d00d064260188012445400031140980140c00134690000e040d2103a005070101c588011601da00c8200902406210750b01c0380324400601c0181311004605c0a80c0a00864103030b0708103551030a02ca801441c003040d99080108070040748010300e2542400103d26540000c3c060050750300010303009540c090002000398888242c5062038a10010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 167163830 1250 167162580 167162591
    0xb060405010c0b27100b09060901031212020c1e0d0f050f12010906180b03100b0103150b04060f18090f02090306010303030213060e0f0d0f0b0f010f08010513080c01060306 75
    0x1800383c588840a140e401c1c03043c134200c600c046c00c3c280440042e1040308054421681e603425a1602d0340c0030300710709440790100502c200d01207141500074005004003880fa200100172690002e254616041c49514540007541d02020100402d2607001300d4200040c0c140e0b0824558403401d00c002c1c0340b0303140328041e112401210030342e000243c04007460f13001d14200d0703110703211724002d0401c01c62158082c0c2d000c04100a900d50301c1042400d2900640340c3c02050440c805060006081c040385103400d46c011419405a90381c0c0b10089401c108464101403000701d450301c5d80c98880c002003490050f803c140e4a2901402c1d54484c0c0e2040c58814001059045400005000303088800d0396943e85002400b03944250710680361880201c200040c0313039000795031400c5540300082100030071140358014010038041c0300c0810303210b69010340d400c8001714009060203802428030b5440d030840356051080c03c4a20b0701d21a8084040c43e0724000410401d001c84030015a110340e44a500c0d180e0342c810102c1c3c8103002d08496000500103902c0c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 167165080 1250 167163830 167163901
    0x30106020717030c060103030f030b04050c03070e120601270518071406091302190e03190302030706050901020c03040f0e0a050708040f0f15020705010b060405010c0b 73
    0x1224411102d0315014002180b6075508035a031203024642c200d28199100e00014800607026190107440c0c8412441d00251030b0808400060a07941d05230b0301038019004c00030501160682c0181d484192000944000c1083c02100d00303400d50701c0505100e030788200c64004400924003200407070340c1c60580c1e43c144021b00c09410248182c00d92000a034078100002e00c15140c0000d05400b8400b010320000e607000780703001c2c02e140819041c044140001c031511655964200a24034074220300303c0310b42400d0395280d60380940582e418001e0501d0f14800103148240250342440c01e5000075400000c4a0106900580225182c2c0341c00035881e01900565850041c3c2e03000c00b113804251f0942200c4608115400d02086078916240c1e5001c100440740d003940c0c0980010200000a40840c0c140056080410b20818090103424840e8440320303240740020340c403412800d400241c544180142405000c0c00e900044940ea880e051030400040e01c403401c884002407100d409603000400f1601107024044000403040703a61030088150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 167166330 1250 167165080 167165083
    0x10f180e01140114090a05010b0f0717160b011215021b01110d050a05090a0f1e06022a0616090b03040302070f06230c0307060e06091216020108100b03010602 69
    0x20a07013028019260f04000070b2010300780d4011a4121100414024940444541840ca00b80e00400003914056140c0000782c6e0b0000c2c15100600700542c040d03d01522680040c0f61000c1d00800603484420300d0845040040046007680c210490072100340900140e540040700d001080040d014040302c02c0c07079440e2402d40c2c1c506003600c0c4010b051490b141c4004009503a107207844201156400c0e1f5031021b06a016601420020318030382204e01e0f0042c002c80048103401025111116807070b0800e1011156070780c01207140303029011017812003004003000b0515490030f0303100369005e182d5405001f801107600900707004264044d07a010f111408094205c1d90990f603900d00e000e09001c5d5941407148150100c02c40c5020000561034495402d19016440200d024554480404c985041c25040001e418410b40020032500c030025149201d03403c0350760f80e440054101460040c0b1018100f080216000829040400104401e007800606030b10b01603509080c00c01c0b9a48a01103191a0341d5982e400005150400000101d4010740 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 167167580 1250 167166330 167166359
    0xb011e0f0210150501080c0417030a03060605030405151506030123270c16030e01030506060a0c02092203030501030b07050a02101e0c0302070b010f180e011401 70
    0x1416000c03520040d81010b2044111841181000c4401e080f040c4103128562082d5a20394100c01070070641400c2c2510b510a603401188000e01540c5203034400110700c0765850b094040c407801006030b401d102c4c1c11341c50306450742c60f141c0205a5102d03c4824940c0c001903128482c4002c8550b22882c050300060712584c481901c0e8000710844940044907007404c910b11840303850f05281008040300c40d40c0d03d481c0c824401a0405600721000340241c078440800307025940c2048521041c001c0898026510040840039610000d800c903203002e06040e002e42020420070520320b0300103c0308a81d00782d0544441d40c1940d504584091203088103d8107001c0490648008802d155040d00814182ca0150800c0f1001d601c594000f610b051183d1070700e000140e040002030018640c142e5000c20651804045084080c84024561204407282c0c45088000b1980c041024024400d44c41811400343c0074004020051a00f070040380010319054085030502d05840c0c3d0714881c08170740c0a420504140c04c070004144042e50716601103484100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 167168830 1250 167167580 167167607
    0x10207050606180601140d090609150c030c140904090f080706050609010e0408070f0c0b0c0705031b090702070905011706070c030f030b0d0b01031a0108010b030d030b011e 75
    0x3c6581084962124540d00d14078091403050b100c80c1e5040007060701d01245034004443c0c3e840c070076a0b58009000841c415006604103e4443c40001d94498082e407044000c0311510305019003014904603007402210f41000850342c81d1034183c50700e141c84001c0000003402070100502d008042e8100300e5410010020410041d10100748280801d004550350304007406045a02403180d620b1409162003c41c0103d40804001c2030264040d022100704407507103444068010302c5a9100b0b100b00d090003d0040310728001408414040c0a089014200c000100c12040400c03409150150b485038a664000c2040c01d80204410300c02081c00071002e02c102d40e07607840c540784d0700f0500000340c00e907501030700d800648032a10400c81c0288655140e00c813030109002500b001c030001e080202000c2e130040880108200440d0004004600852142140c4071038800788104428540034103030b0244071507a0600c4d011343c00694001c00e00d580c001c04140350000300c41d2006c80040741c1b512401031417244140e00c008071040059600c03040742d000c0d02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 167170080 1250 167168830 167168839
    0xd0f0f05070f0f080d0c0210060504050c0703051c110703080603010213031106040801050c0d1401060207090b0f0636030703110d0c060801030c1502060604110408010207050606 77
    0x2020010151401d20070510300400d1080c2c1400c45030009181c510780c9203036040c007620030036051020b01c0742d0000c100c4103507001e0301000d6801062948403120940c00358001400040d45c081c4130a040050310060a0b000341d240080030b020021510503030306811041e0440d1000700d0701030140404e1000001c600d4440d0301100007940014070900c006005410140215000341c030001c81030803140740c69134a40703030501c0c60051401c542c494020880080c600100340a0700e401407180700c0701c1c80c0c4d90301d40403040310040301c80c042d024031503244150004002250300844c1940480d088404007058074144903002503044030514100030b030f01c20404140340d0042070407c241c00003034140c1742540c44c02d17216002c0f41130b802c1c414040c02c1072541540300d41c1086c0000f0b40070210700c0002650241c408240507802c0c1e6141c1e18110000c0d0456000a02200010014400c0f1885088000d041c800c8501c00d0203c0020750082d02e03180014a4a030084d51104c0040515081ca00304660041200744021501e40005140c8951100019903156104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 167171330 1250 167170080 167170097
    0x6200a140307050a0e011116090b030c030316060b0d030c0309050927010f0e0d0206071b030c020d02030f0d0206011409040b0c0c0601030807030314071407050304080d0f 74
    0x14810300000312402120342d503d4650500c4604013044407141c456091150410103020001000d40104204901210743e01d0401e0505681c20005a41c048910420540b84281d021a0413040d00361004001c81d07a4034102c2d00341c54a9442d146040c003001400c9614511504a200c0c69002d00a00d0390103124070030307614840e41e148003585503107508010b500241a1440c001d030f08540044981c5180506e0001d44016641100100b81c03400c80c500800304076001402d03210707002e800880c02e00171015414000c1a9100b21182001c0070f0040ca64849202280305000c401014002c2000d102c00030343d80c4034079210350f005074009c08a940008101e03094a455090396004280584140300021500f0300c00043c0180d0418400b400884443d50307186c98100d090030b400303040e40c681c83c00c040100901040042c06600c0c083c5028a031290764551741c0f440d0040c2120703120440050340741d0300003091040d01944241c1c00070380c5004081c1159110103042c02d0243c2940300300c1d840340100b071003250003c010b00ca40103154a007408540b910307050072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 167172580 1250 167171330 167171357
    0x60703050f0a1e0e101d1006120809042a03140906220f0605060f04020309070b09120312010f050604062c1009050a091404080706200a 59
    0x260352003c1e6084692107a110880e409080d4079500599507041c40d036040790450340420918404883c3d1586040b4100d00740c4064050400c0303c2004240299180d00004101452a10b40d180c0380c4061500c100829010000510a140d591950042d201c06424005d140e02c09081d000c0108030f42d08112107a47c0c021038208070260924030529841a44585c02400c00340c4669911101c03a4941e0060300e40d0501801c0902c00b01c6403011034060003068034424480e40c800070340ea0034150104055104a11200b41c0704074010020007040c40c402044003c2102c2147c40341c0c40d101d900c21400141602c0f94807100780741d140b03c04031b00b0144a450103102281203da03507444440f10030780c07204d007809554800d0b07015003404190501d00258154407900e0780008002604a8a040070110b80c500040c1c54040f40340e01c1c0000519525010b000c1d524006c1c013544001d0011030002c00c4481c8800350b100d000f100c0000c2c0060085034003ca105e41c20711000e50011a070301e9040510001c064400c90a0804041d04540301440c00607440e078000d4103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 167173830 1250 167172580 167172601
    0xd0501030c050a140f0a0e01090504050c0a140d0203120d05040c0e0402011d060904090b19060f030807081b06041202031201030b09150106020a0201020f1c081305060703050f 76
    0x184c0c0e0304130100d0810400d06a060001d100445510300d41c016031090b40c0003456540394454180130744100b1001150030308082c00d00d02d20b400d81410113035101d400c180e002001035980580d06200320000690300350f400e281e21800000d040000c400705901622000044559840d040d613400140b155218a101052160b01c5a101c0c08181d201258003e01064040a059007802c981e1101c01d00159401040580303404c5a40d80414140e881c40c1104542000044051010403c41009410106404c40d0130030028549008140c07007007c00548006401c03071000003003003014055944200e4904800c0c0011882c40160310010981e074810003214180c500340e032654035814105101000f00c500024110612400c0d40e4296100c469500c00c3c0903100b618184558005500c3c3e104010416030b0080c071054014004c0506280000381c103110034030007460b055030048a45d95034800710400c22000c0c400d09504d0308000594458024065038059400050b01c2403080404101c24250305030400c0f1b20810100807801e64a440b02d10f08031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 167175080 1250 167173830 167173849
    0x608030906160807020d0f060b0906010f050a02010207020a080601180b0306010303120e06040c050307170613051e07030309051002071703092806110606010f030906020d0501030c05 79
    0x680d0300080070455444982c038054100316256026951191038800564002083e281203001d08907800d185401d00e5038207010246c4108002800c0688800380036181c0880001d109990807400e0006020002c40c40d184858400d606171400b180c2d025118003c41602e81c080703d40e840034240301c2c0018801e1500700c1b845035030360350b1300503200040009070040c0341c42c0e421035400f524048200032104c008259102c2c0b80c161351400800c2020300650040c0002e0003068101028182000c1d0302e07400c0b40a0b184803e09218904000c000780f05a442441a00000aa00752a18019061640e02c824030b00801400b01410042c16002003005411a44640c0304d90041ca996241072050741c02c1864990000b68110b04c80030004040f03106220211900c0e45000d85c0d01d4000d803080010a203660031681a85c02100d01e103103460008540010100c068281c0c1d00b84800241400b806060750740070000c14240c10010b00b1000200c105000b500a015080d500840030340d140d400c181c4500b0000c1074240320581c1c0c4040c221200181504110164 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 167176330 1250 167175080 167175097
    0x150d0503040b0901050d1424010206130c0f0303030f0b010e1e010e030703111e1e01090e0106030b10140904020f070b010308220506040e09160f060201060803 69
    0x3540c2058904000307a64503801203c4410305024040210f1000b1003514880da00c1c01d0480c1031840303211420100d0098510150441002481c0540c0c1100828140c0c3c000a070725902508200361040e0407021850001074440050b40320120300e5554a00c040101601500b0402402c25099070402106044c14011100030840e0381030302c1d030801b0400291810b2040c1014040000d40740604107100c442d040500860328001095209440242412500700d65510340b00c42d101095107204424a03441481003000501100c041a8105507024410442d01080c1e034010040003000b0041f90722425030a40e9900f002401400ba02c1275458810758801410100150241d103172003c4040c0f070001c2d12400d04552600b403200a6004000401030303030400703100080000b807880d58524082c61007000010b0b00c80c1c0d1202103100700c0034041c850035011810008400d010a88640c0251411117a00048a01c07840d110103040e1401c107050614000d410480110010851448165411003111b40781e038001c00030b840c1d40c0c0c650f064a901601d0078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 167177580 1250 167176330 167176333
    0x1e030c0d0b01080d082503110d090501060504020c0d110c0414040b0609090601061101090210030204030b010b030f0402011b14030a200d0c14060a09021309030c060203090111070b150d05 81
    0x548104d0066800e00e1b11072469200c5c1400a130750241121a9680c40e0008140c1010482c3c45001d080200310003030040b04010003066078158248000c1c0440d0301d44501c40820090208810100803035030212003001000310030341c00500100000030700c014001c1101c20302203909440c030000001c0407900c0360a001440611908010003c0c1050345d0030a4be0841e00a24500f180290300c8d0740340c1800401603a9500400c44031490345840040c0c0d035600c1c5180880281c54160311102400703a091040081f41c404440314142c3c0254240707024602d881920780b8405011101100191840140f00e5100c5001c540000007450414115164528881781e2080745084068941c0210a0f4a03001b012202c0b2155005221000343c0358424452201e504041c9124035143c61001c40d5112040ca0301d800d00d1209605103d400b4111082842e1401c1c008030740703e034601802000031050f004107020341c0040040e103400c00070f50010000c2c4d0203420500d66141014100725000700d2098480001840e220450041a4030344040c000305003560290 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 167178830 1250 167177580 167177611
    0x5090f06090903091207051002030a0203030a0f090816021306050109031104091401020a1205060d0b0a021e181c061a04020a02030c07141e030c0d0b01080d08 69
    0x424000741040c00781039614984400e0144e980c0b190399608001c9082c4440900419820386050100803000c0c880424003410754108124600845502008a0ba48030702004c4010070340c2d01c030900110340203040d80308014000c0180812000380241d03900b9104c400c858000c442040c20300e640300c4280812212244100c82c0813980c0444200b000414416000302c0702d1000520001c1c3d03410030768503408580b02d4252f0100d0340303a03540026003050294129000da002da0a15034070802451a140c008291a81c2305034002038801c2c81e500000642205040d012070f075803809507410b038100da0030040d003020070b05400140b04403d402d00311080940050400228920115840c0111031b41450f0341c6440b83c1006007014801d044403200c00d026180481d40303031800100341ea040c4a5009540ea0084010f034103080128030b82150380805c4042c1070041e015a6040b4503603c1c0d8512440403640c1d103140200020b498410310780d683e2a089803000e40383c0400c0c0701080385041d04a4032800242c4001048101040b940c22400300c42c2c0d0100000c00d41c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 167180080 1250 167178830 167178841
    0x70302040e061f05031b06090a170f0d050301091805010c0c0309050f010e010f02010e01090827060a0323010608061306060c0b060d020307090c02010c031e0b01090e01091505090f 78
    0x10000d401b243c040240180740b91440b800d0105182569039004144a00c98075240b103151200e081000001310715200014002c07031011032000401510040c40303041075880d218508030169425080814042e564450001c20414102e55006815801603000650100d903c2c002c0005803410300350400c1d442206c050399982c0c07040c10508015101d81040d4403462045642c4c07020400c1c00c0c0e0b00b0074411800d8460003480c00e16100d964191309412214502903108180261011040704540c45410903103485000504000c1510980c0c4c0c18008003070103006032420140950040001040c80d04092202e02490302036595062005c1078241602c02c0c2c80092086400040c00240400c0c007044030f1807525500544010300100b2840101d40010307280001540151708180d03038541b14400c04035024440c0f41103442c403604050020001040841c42e11170805010401c0f37603078440e041d80415a00c68003040b806054800010304180d616004801c000b001c0a68130700240307068921300072602d842e01e0410f80380b08500315400b01d0400e6441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 167181330 1250 167180080 167180113
    0x40902030c041d06101d011101140a0204060f020609070302060f0909180f0f0703060e01180c06020106050a030b040f020301111b010501060804080409020c070302040e061f0503 77
    0x107181d016070000074003002c07401d8205a980c20003026101a4102e545080c208100000402c5030000752090000d50400036810b0b00c001042c400d101c08090a00c60109174450340380c90301401b042d4400c030343d64001036407c01404c0e40c010780c007520582e032066039224101e0384500d1041e6655682611045026488001e041005103000d800508140c0114516181000c007600e004c84c01d03400c4103540114040d90001407880c0da6440811203140314000d0340c130080000c00b80200380c0548036142d5000140c8516150000380c40400001d40000d41a04100815a01f008810f41010001d010050180100550030910b000806103000c2200385c0a59402250000032a110b59642c0541d015042500f03d030103540f2400c0c0349108200440140c450703c2c116012481030f0f00c8018a0207401c4500582285050001000511000c16240000e41c0d0030350740308040c01071341c0b180750441251034600310303a10003940b06040c107242161704500443c150707005854a000501030010000c1d4040c0c00c1c0302850151913090b40c0040f03541010b8804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 167182580 1250 167181330 167181337
    0x40b0d0506040207061a190501170c070c060c06050106091a0a11032a070b070f1103060a0f0e010603120f09090e07031a04051c020f161e050303040902 66
    0x4010b00040c0b8000455480b0710944803403546507081c22428509000702e900341244000e80307201c084644c1550240c141030000c1c1c0340803c10b201d804065000480003941c0040a502159180394010131180c0c282a681c85005100c4010964102c1d0014100000019868050410202a142002a081c0308000b040494281c140c205444500c10004000c000d00758100c0c0c00d2000384080308251520082c010803030f042d2006041c0c0901242c1c00c043c0e10a8004100d200003a10545881c1940b142d2007001302041c600740884c0c00541d030840f80d68140562414400346407071a0f488031600c001520800e10140032000181d500b214000d21010b070052043e4194100418810004502e9a6806003082c8409944035241e807002c54001541c510025405000b06009101d01072041603038410700c00c0c0b01c1c2c5a9901d016034801e610f64031061200c10407883c801566a01070780c020310030300341480640c6003200c45080d034083d00f40740c10b6160b81c460460410303203001e4036840d40910710072000103031807002e401985802d05c1d011000340290b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 167183830 1250 167182580 167182591
    0x81207051006060503090c061801051c020f030402010905030a0506070f030204180603140a030c021306171c050702060f0d020c0a050f1203040f0b0403030f02040617090102040b0d05 79
    0x641681180d620282d01c00c450142090b580e59a13100d00d0311103103443c6002c420314011482164284001c1d50b84066003072600c22004020300e041900c4000340307048081c2d40803c241c1269203003800030985009180845026511a0b8001da030f81a0140e9030354424035403581c81c0790101411070380100c3d00040026009a0003518218050f01d03005180664601e401d04002120602514001d510780200300140802d25840ca18204100740140c007040150759406466180d42140090007001208042c044806040d8000d0000307200200c0544c9401044401c0291240307140744402100010303240d41040b070b981c440c0059801035a03001c2e00c80c510340f001c0b01138821040e40041d4428070030641c00f00000031140005210031902c0381c3c801c100800240442901076030814409541d544020701d414010000231408211035240100c0c0c201d48419002d84603030070704401504070041c5080c04c0500002d40012590380c45207900910038041032808155031111501c003402e030302c1503110300c1c3c100c20014031030300000100c0c40d80301a8110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 167185080 1250 167183830 167183833
    0x10020a140c04180203031611150d0e030309060106030902030a080a11010e01051608060409080a0503190203100306020a2a0b01080c010e1c050a0606140d120c17040e04050f030408120705 81
    0x1001a0008800c0d5006d27488402c0503240c04103a0711203401c05400b840d01220712840145040d448c1a0040c40d96444051045404141e21a0300140654400b07000a900ca6070f0810640c1d40d0b55040303588003400c502d0500701c8040e225841c105000c000d1880600c5214041e6409262400e82c1004100f81200c1024015004e190301540d10304007000061640b00c01080d20b5006034403071548034a00b0300e182124085050028013100e5004004220080981c04540010b41e94001e80058650109041c11250503038619148800308860760380c0d4004007111240d2480d00d880c0304850b04d003142e0380c9600b20140c407040c013084e015003c00e6050031301100919040010100b044503240a8030f0b1145c5840e12514031b404000358040c1c0e10240d6800c0240314405d640107009000610aa41195a0442903135412120b0281401c4050800200c001d600c1c003000145498804061288006240c8894850034004030004c01610200c515101d01c04840c0070741070011042e030301215a03210140c64400d200313600c0000c1c00d621641e82143e00c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 167186330 1250 167185080 167185103
    0x215040f15170103020a180f0903020a0b010603060308070602030c09030f030d0605010215011505120c03150d12030b0613080102030106090f0f1512020307020a0b0a110910020a140c041802030316 85
    0x40e14051040c80b059034020343c01031481330020b06103140c02c018183c0065003058205481400403880040c201c0703155039445080141d40ba0b540481d03902e45801846581e036494080d143c14203408a100001602e003078810000100010356581c801a41e650300b0780045041d0420903880100023034812400381d00813510240c14403900c2d24906003407201d45080c0403103003046000c00c00b00c01e000343c200741541402640001641c00d11280c0300c1c0d986031780290001d00c0014008240d2036125130919a01c448081c0c8182c01c821034003200c03070039860381ea5090103074000f409100c2c00280c1c2e4140c0020161107031031221044802c5d000c002c0c40c1480c02c101034006000721180082080c008200b4501c0045009403004605c80c07000e81d4060900c6084030b15103400a00300c0540304041d034900780000020102c0b041000c44e03e0359041111b0840b2158602007090341441d440c07200142a956010010b02c460344004180002c5041c1c04603810080901100142c0004454180010350140d00600c4031400300c800b218500c1c04d89078000c00c0e0b80c001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 167187580 1250 167186330 167186351
    0x90b0c0c15120a090308060f0a120501050414030301060906030e030708030f0604050601031a042307020610060314060607110a08070e0c090d0215040f15170103020a18 73
    0x2080700d00c0c41880300d100e0000039090810203405050560401c10340c0d00240a160880d032001801403901500e4544105a8040c03612855039400c11054002c0804400342000307240d190600c54002d08003110300b9203c003690701c41800500480442200d041c3c42054607803600c3c0c2800c154044004044c16580a401c40c40208004c101084a0101071440741030f40441440840c0b510340140310507140003621513414541030070480120114030f8100040040010f0f40d00081420912803882c45a94041c0300075000c290799041441f89040d400f18405100c0d50340c00411509241d40c49404904841814051300840c8511802183d07040c81c2203401440298010780b002c54000417103400240d040000d5a10010b03807030f441040104040b07081220a1540310000c9084103090206140c0417074090440f12000034170810a1000c0801058486000c0d1405006034419032020561100310045880b09038000701404210048088031812052282c1141a00e5003c3c14014003a071a008249407180c13128241070311030075183d40b0b0506 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 167188830 1250 167187580 167187589
    0x405030714031e0703030f11190e060310030317060306010306051f0e070f030e03030604020a120f06050a090203070207050103050603100f090317040c0303080c070f12030f060501090b0c0c 82
    0x500d11004150f030340d9841c8020f00c0e001e0121582e41424050356410005200100d900d02c50a880d803503481510607000009656000700c0f00038445802c207643c0540080103200c80d011094522406891113511444501040020b441c2d06060040314800d50544c007440060002601a400c4240c0000740400e88007401d21051724080c210041942002e2a000d107490f0070881c6941d84864444030b18501403d04208114409074025101d110041c10380c3d025507000144403204d2032003201804d086c145c08010400c0884441201c1e680641494030a280c803035900c50a02084121362482264041c4496800070040c0e00e00e000010350241070000e00c2c00d5454021000d6242810a40740190309219034101c00c0010f00464518015028200203c0c0e8280d00c045141c040100041d080c10b903003410f8039010f00b05051a03590344601e0a482d8030032010000c02621080c00c41c0c01c20401c50340103280c0c20383c60684040c44022421740020040f00e96a1041a0000780c2d10300d410008004104003c000482001041c0c821003900b01004c42c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 167190080 1250 167188830 167188867
    0x3020303030a050a06170703081602130f0605010f020a061104051e1003020403051f09081c110a020d05090a0f0e01030311060c0702190e01060f02010b09040503071403 73
    0xc0b048503280c07020041038850a2184d00040c0c20b0321005045007107501e801c46540c030221408004c2c1991400207580700c1a4540880502004d607000b80f1075020781828528100180c2164081c041242e42003604c00700756503003d0030941c5042c03242039006045404040d15000040c20b0180418260038004100c00300e003a44070300380c40300120603980e010308030000c01c19401d001c00d84400c4406402094814482440080d001050b03404540511002030645072000420000003061010710050456800160b03101d002391240807156550300c5c042c0d50801c0500209014140c203440342112210047e004100e00030121809440680ba6194001d4900012140c80380418140a04c1e140c010220440c1c1d80e1004004142d88190b41011583c100400b801080c03c0c50204544c2601039070300000d1040c04030900d50350710300102c00700083c0202002d00490101d540d50700001b84c4401d4403040910015420910503111a06240f0701c0c040c000e0ba0301c0741c015890300e05191148040e400c035a03030700c1c1e92050000700004441104041600c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 167191330 1250 167190080 167190091
    0xb030d020a03081302090103080c0705040f06030b061801090207210e030d020102120105060702060d0f1d0106080c060318010525021c0e0303070501050f010f0501080903031f0302030303 81
    0xa00618806082c094920f1600800c510901c0d031290901000584442c1104d03411a03900415031900c68602406d03050501859401068000b40340a461020f035a01c0754100724103c07030040b0090f541c661606000d2080c4146000103d1000d861480010401da0085a00400149000710b4107081026070311110000010040b42851001a218501a96280c42c062220800c0c2141c0342c00214607140707c40600048810052003002d125500100e980010f40d2038101c01c403407088038242c2f000c202d290541a0040300400e5485980948942d072000c988400c560140704410903a40c07600e00401d01050600108501c07544010000f4803230940c00107002008080034060340703004030002850003220241884608440a80390716941045500c52070b01819803010314400020f003081e5528049969100400201e07155200b0410020540e62802d01080b2034066940e40d404d050f5450300940110a80d520001121001c4094072152003581080011605213210b0440b036200110900d00280e801c0f5030341ea00080d045801c2101c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 167192580 1250 167191330 167191333
    0x6020d09030318052524020601050402070f06020901030b0a0602010e06160f0f02070f060801081c081f030b010b1b07140d051e03040f05060a0804060504060b030d02 72
    0x504058040c000c00f00c1c0998185840c100c0369100740c442503601c40b216034100c036000403240e548034541443c2c40541d6010300f0315029000070750b103036298142c284517059005c120014092480049a2440c29008039243c03d600900342e42c00d0381b0782c1900c0d908000e5021088640c14950b540c00b400901ea16200704c00d00041c0b07001d4000084003c0200f014604000b402000360000f4200003c2a00203d034018084e0509107400c4c1c03400e60105031001c0b10070380c0741001d00c0d0410503c24000000010700c0030342c400252416504044203a40f014028030090002c034900415013540030400010010b00c0c1e0201c041000b070711610b8443c01d0546c2440c0d40c3c0d11103060400b000e80000d2403016001440040542840c0b1480306060001790040c00841d10b01264500b200b1180f0500a10640d1911680e805200342001070034075103d51015607180d040b80c0100b0641d82c0f80d0180c4a00b00da842414000040c651400200351200c2d01060346078107081c0e55036651400d0040000a108444050f40e503540e1070140c1c1c4003000740056603c000d80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 167193830 1250 167192580 167192591
    0x30f03090c1c0b0105040902090a0c031113170a0b0f1302040c0804020f03061005060d021b0718020c030a0309080c0a260304050a0f1a091605040203060307140103060306020d 76
    0x505241c3c640c0c05800450003107060407071b0600140c1300c50052680c00011200009400000000d0440c081e010308406178003030741c6000c9100050381c50000408011545c0200018104000f040241e0b40c4841c0708580c040c040064400000720f00f0703079000080c9a44a460040c400d01c280b20203500042c12100501105800a00f0020804c021414070881c3c80e9119001117001700300c14980800b40603402e10301805038a0207100c011541c5114904c19070180e40c0260381d107080c0e42880700400b06029998140501c00c1c80b06900e0429888a031200b024401c9501d2420314001071850900703a0b00058000d0890540c0403603941c90100110312078010244114607580d44144054080611445030300804007200d01040d20504900700180070001e140000d0000c0e18039400000042c0b6040503040007034245505280c1012800d2102e0104088075401046030070f000d0346903120951126440e01d0910089000854480d0b80680c02681d0510511840312180540800149400f00e0500c2d04d965940c3c041e80c1141a041501e0764586 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 167195080 1250 167193830 167193833
    0x909050d0801060c0b01050f0d06051905161d011e20030a021905030903070308090103140402010503042409050c100302091311040e041101020d020f030f03090c1c 71
    0x580018010452484e1100c80032845803144003c00206118441c400c0301550140d141d2034988032041e0042c550441c0c81044645080020100e800c0e81202d0340d002a14a00700010b644414208a542a0141d0310b030781d5103941110000e0008000c40c40711101c2c13810300c003900644181c00250f410b6241041015581d5900e0250900d82031105049445010550280c10074003000b5091035001a00700409030402c001c10303140601d103040880c09c41c4108002c180d010f0142520104c28001010001c01111500380c3c2c04010070441e0740003102c1d10000940d8002c0c00205c1c10004200400c0c03404202c0e803c41c4005400c642180520210070320100c9600100441c0c40340c1040413841742c80e24048001450390107460609510380098040002c4085040d003081d070a00715520142c0040d81c4404105450140c40071560300c2c400d60500e800d2010900720aa20341c50700500c03862400140b62440800d48a01a565840096040c0400a2401901c1d9080105881850310510001c1251070f43c500e0354440c031142c2d59600c900d0704400ea9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 167196330 1250 167195080 167195087
    0x160807020d02030d020d0605030f03030f09010203070c0303050907230301150b0301121401181401060501050313050c0d0f03140304031e031503080c0f0604050709150909050d 76
    0x28260019034100c8000240000d4010080b0f0b01d40001c4070310010390302c94941c0c14035401003045d508240d0700352003080f02c5a00303540e400100a500810bd540445590b0f5651200035600f80c0c0320460b8410b001a000609000c0024065084980c0000501d401e86001360303207510211400e41c1d2055084a418201c4c02110f664600f028801d944079012951101c2d40950304140f15207030548410f104010301c0181000040051203c8141c0d0746c1d050381c003a840240b00c2080c00040c1c00790004451740080d0382031000c100c0900c1c101c1105100d028110b640c181c40b060700310303650490320038805520500c055400d40201b03801d003262540c2e000c03000700d48180b1a015544400f8100e0034014400a4085c0c41c081e4080c03010000d0002098210307201d60300c130f100003114400c1c44800d240000c40c040c0802100554010260150200820140b60301501800341349104542001041002103030b80e840081c0e07005000e40c2c000c404180461034150f04508501e0820744044045190b690400400722580d9007400d4403a03070840c82925606560 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 167197580 1250 167196330 167196347
    0x30507031d0c0f0103061a16050d0201061a1606020d0e01050a0e010e0d08160909181110080105040b0409050d050301030201020c0f18180307080403050c040e030304030507020d0b16 79
    0xb0b1078100081407c103125080c004007012100303a400600400c0d03c01da2140d008480b01250340d80702050340c06021002001078081c04c1c550090100c4031100900720740d10070046a094510341000b200c13200040c3ca080c0d0f215440250701c40c2042412007500e44400107032054090042a00076120121300081035407402c40001d0840302000541d03030450f008030f2900c54030280c3c410982c83d041f600c040076642c051003100c44107444440440d403180b0202c50404400101c000600541e40b000e25014181c0501140e5428040001d21505201d01d100461440001440700b410158000004484054000505203201c0d03120181b4020104003600000b80b0f00000600c11964140404801d0004c103540c4d568a40080d07200081ca0407030a0005401718084201c0007495201000f5040ea03182d07070382d40007a0780e40c414040c106000154018082030701c452080030580090303400c240c4658031002210001135402c0d61201e40d8204c515030310584003a81d20032440139140d008031f80390a032040c8c003420126101c090000d0011602034030044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 167198830 1250 167197580 167197609
    0x60609060a2102090f060d030305070e12030a08010605031003081e040b0408010b090f0f040302160803070c080d1715090c04050f01030b1e030a0605090102120a060b0901030507031d0c 80
    0x4441801b804600c0c0c03510114541c00907458200070070595114881228000c0701c040803664010851610804140008002010794001c81c2c1d40740700d0b4a0381c0f200410341d2544016689289060f0301220100003085d0100c020b00b191000400070041c9668a01d41401d030f0304e8003d42c1200200f20782c009410088074400740b240c6646600240c441c00214501080c1c08030945800030031098070320190100260416100b480401d205030800908000c2c00d80d220a09503a0381c1d084807204490403150700001082c5842c0008844610f080e260380e542c4440c0d008114072421104018000264810ba408886c61aa592700844144260b0b00320b40540d886a191104110004083c04c1c440b5040c58a040d105032416111100e4842c100190711980f400489040008613140009030200641102c0c50f1400b4840c4151064005004025201421200f1920740d8408107080303640c90b03c160a0420010883d00820b5406070300203590004140c1400604100b51104c11906600f0300c1c0240d0065400c0303140ca0503032034a4124060b28800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 167200080 1250 167198830 167198851
    0x91e060c0e03120a1103040807061d01120216051c030f05040503041715010603090c050405040b06040b130212090609120a0315050409060e010f020903060c0f130e07140c060609060a210209 82
    0x685882000de0a21718091220001d1a40c00003080c00501100e044d80ca1a500d92020486440300c074208000d0141030078800c54000002d040001c5000c1d05072480c00f4803401030f80c109000d036181030f10380f0400300d02a2000b0008005240607080e00e03100c906c0740e8071221a00920382614040382141042c50041c1e0641207507008a44100d207028148004151041d49c1c1940c071100030f6400140c3d5001150014030400128102d0410040c00040c101c00f0422128040a008100ba07104030b820302c0d01c0310100c003034440c50b1181000400e407500307000304054640709401100030345084034800031300143c81d42c0205040d15516901a9641c940303c241040888100340700e241c0452000701021802d0000d44000a903e0303001c003802e8110303815008100c1e02056080c110480b2007481890703094180302903403207940c00c00b403040c01c43e0000041303049501e015064080c5003040b1403d244040d4040c09131980c42d04100909004082c0a15405c02e40102001c100002ea00d1485805040e403d07500c0c4820b050288104403403040c00800c5944030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 167201330 1250 167200080 167200127
    0x603020c0d031508030d1d070303050307030b0f100503042616050c060408060a1b08011205070b1b010b060c1906091e060c0e03120a110304080706 64
    0x800310040707050241c1c07a9082c0380103c3c40c0b1102d00d4441e080115503420503c1540400a406410b18440703034071405041c21000d20300010032010081c01a00c5412612010b80402d400b000010300d92482070b48084074a01f070040c06181130580309804511130708699a41c800100d400003090005101240c904031024451070161458045010b219003222401010810300552001c000303e0010054107010340784480c00040c11990311281d03200c81e240e955900540d2420780051800c1c04607515140740900002c920900c6442e4800306928081a950050b4401d040984260080302d202003241d100d00c03001414155400c104a4451211800805007154224a0110b00c10f07001003000d0840c1010100700e4641d00b00b20b401500f0847ca200d0301f0903001070721302100000d04002030032101000c0c1d503101417a5410454040c007020402021103807000e5500c6000796064652550080000c42d1142c0b0182c1d004180070701e003a1400000b5540d00888292031034203d9000b5004a03001060240f01460f40040c2421b4000e1458503102c06 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 167202580 1250 167201330 167201347
    0x309150b030d11070e0a060f0f03020105160602120c030109060b07020904061d030705060a2d0b04090204140601171b0906160501050601110d0203181c0305030f01060302 74
    0x380c840300c0b5002402481181032195142c0d4005002d04402003c90b80d5825850389001582c00008081e03d0140307100c41500308102146045502e1b044c0801d6a5040c0c41c1c09140400410080095902d0a241168a41d4007044460018801244510300032401c0e900c10701e0302c81d41087d01c840c05130350190300000d00c0360b00180701000c0582e40300c5c0d069541150300080b00140c240440807142240040f0481d200300644000140d080410400152040c4500311a181c00c2100c200c29801400840300d1303120a550300c0344582e0203a400c085440b98081213100100503c00076502d24254013260507203490034000303040b08850008001407960400040001d0f412a1000b035100d44c544841c6c044084070210141c1016a0004140f2100ba9200c01c401c8403000507941d00c0540e07903150740e8075149010304002c0350424000b680c048200028640005448040c80c0c0840d00618140322200d0030307110f0f240c004900141e60025203407056101c1d24003241c0c1c00d03040c3ca5000c0e5407042ea4a1030304118205a41d1f0042e40200101481080702c1360 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 167203830 1250 167202580 167202583
    0x4050d0e0303030a1d0a050304060207050a0b1e09040905010b13020313030c150f0c140c0703030c06020702040213090e0304150e0a091b020111030f010e130c060309150b03 75
    0x7a403121115a000800600c0c8105d10700300b6036a030b40d52800e01840f40d0307110081804000030183c01142c0c4076900300c0700016269418007000581c01d2040e4004c0b4042031003007141407429103e90800140e0110f15030390502c2907000000f010360b1001c0c603007510315075505d146482143c146094400c0e50282e8098081d4a10f04100e900b0f20400b00100300007500f00131010407800d04002e200c0315a55120a444030040c0100171041c001003008004618500f0082001100310140c00300c0d505040c0c410381d02806000e0407015185490503262001460000c41e0f800c2d0303003046040010b94852010303101c400c0341800c0022040d030406003034800b01c8001d10010341c81c980c000c0c40100000c0c2c041884210310b14025250148040850074042014802c0075000404a41d041950340707881803011303146904c4000c0881d8000d019106200c6140007051100381c481000c44a0a1001070006d04103959840360000340d10b10700b0041d80d10264940816101c05034000000183d01d0768030034000c3c401c454020841c5203030310400412540340c030240041d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 167205080 1250 167203830 167203837
    0xc1516080606030f0f090a0f03050a02010c210c090b0a020703030207060801050d0201030c170f06030c01030203090303060103090c12031709062701060317030609090706120207060b130504050d0e0303 87
    0x2100c55086000140c1d00781c0d041c070001847c10b6100ca41100500450328001c0c101b5041204008019843c2000c00c00126124000703030144007448030806d00d4005c03000c50785200900701020b041c0d01070201902000800d0001e0311700900401c0d80541c00b4210403811494002e04100841d84407104008100c4014800e607541c415086900703950908000a07240803190058649038582130890610804001c1041341482c0543c00381c51003560210151065403140100560407804140d40f4140103500c184001142c5500035401040c10a005218034a41c0d00d6079120003180c1510615030032000542c18804000704c00003080601908040c40e000904402d00d4030040a2559503829a082c98800f034510b0b01551500070294840c90242d134110070600e2040e0700340342c12940c01da403044e1402805040d4000c00643c540d2400700c3c03411f081d2003081d540c2c02c181c1c0702c08485400294000031400e40f603899032445118440e5480a90045203045a4040400d40b480c0500b40301b800d00c6000d07207840c818040340e00160038013680c002c000c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 167206330 1250 167205080 167205091
    0xf0c021c08060f060310030303050a090804030b0403051201090b010336080c1b0f10020a03081b0c010b04110a05040b0313020315090d0216030303020c1516080606030f 73
    0x3100300b542c8040000d035241c0b4011000341e402480000902440160b1071441c14107581c0252000c2c000d5848041c0d8007411284c1d405009090600188000d20008100071840c40c1c00a000e0b280150510341d184c01c00c3d00243c482a401001c140b944d8000382c00055800d80158022403048401280c50b201c07110811601450366605801c8004003c00710f080100701d099410789a00c7e14490b0120f403180344548181401038a000d41100f4420620381d0150a01031034000750301c2d40030700030a5000e0031501c2007a95017941d0350007014094400311131601345d1600704007411401401d01c003029200041080c403021420701003200c0118145113825482000000580c507001340c11030b003c8a40050401c3c0e034958a802c0440845062000001e600d40602c82d200150784003401c14440c00b449e0b21800750713909180d080d6016655052481802c1a505c0c044103401c001003402907000e021003201e20700070780e4003205000300d900202100485030f0203102680001e00c240e89a5212107840d9004000760f40b40c2c0d1031070030420540c024a00c002000e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 167207580 1250 167206330 167206337
    0x30f09060903040e0103081c0e0f15090718021917090708060c0a030204030605270102090f10021606020f240a0e1c0c02090604090b0c0d06080304090f0c021c 69
    0x60043c201022303c101c1070010100c20204004148491010544445003513041e00094400c0c3c0c1c09199002c50465a9240605a481c00610443c2e18264898600040c080c0c0c0c0600c000c3d500b4400d400d41c0c01c1401c2d4150251505568036030320514440700a50031030820242044045501c0369000740413503140020120f4200022a000540342c1e900030004401130311958100608050905061100c80f000903054a281c0000c855140c003884020400c901c0e08074060485e0b0141e001c3e58210001e1281c3c1400141014600c03840d1050340c010400301c103070510348910640e00000040e80501c1c0c3c80358031210207202a240a009a105a1000203034000407101401005800e104c080ca0303941c68210040c030820401e4100030703007002c4075034035603202e5088024184082c9814241c2c0500108800075582d468203208210314660711400d40031003511090001d00b01d540040310b151a03410f5889501164496040018100030048104003040381e416243c500806e40325541c14500542d840100000e054400240234900030217401d00d07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 167208830 1250 167207580 167207587
    0x2040e0108030315151e04060e01020d05071b0e0f01030203060c21060d120c0302150403080a0509010b1305160819050c1204290601050f13030206030f09060903040e010308 75
    0x241144e4461080c60189841b00c0c500030b0485c2e800e00e840d0070181040b140940c5607031203040c55500040e80c40780c1c0c0c0345010740005141000b600c0000b45100c14000910384141120b1035207240c80b000201410380040d603003c1d210108101c010021403400b040300381d50207030300e090f100c038142085410007054500740d8080003c0e1207130890300011b8482c0c442002c1e00d0310958001480f91500760801e080641800030f42c010540040c01221380343e901b2540c42d03007943c90080358913540e00a0980d8030500c0c440c00600c40900640c0c500e5485440c00072556540c40407002d0002003c48000034a403c025590418401c01c440200051140080402040030a40754119030300300714241c40498950380300d2003040c80d280b103111488031001c5008803c2c8014080494041c0d401e0308450342414003440c4501015518404003114078a0015078104494841d83d00118003500c1211131041458003815169800100240c00c100c03149081581e0075010007035035080400500d508160300001075403400b418a40580d1000303805000207400f414000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 167210080 1250 167208830 167208859
    0x20405060a0c1b1203110105221703090115090c08040b04050307061b030e070b09060a020118060b0a14030d0f02160602010629040e04030507140102040e0108030315 72
    0x1c02c880b03c1204038504040e40070b161203016a0204150300e0300284c00140610b02da44240610501ca0b207802141701003080f842d801c0c40ca04842440d8040700d10300720741003440380a0b400030360f01000d8090350181307100c2d1002040c8010190594846e0358220f501c916510fa0030007011440283d00305901c19086604600c1070101942c450034100d20f98410014003d0045140c0489900e024550150300208103000fa81c0521821030300811403030340c68105005070b00e08030500300b00b21113003072030441c0003407804070020300000c21580b08000c40f050360100000001d803000f0b034846110038038a143c5081c0803009400c6204800002e4440c910100c0e41d1007400c41254020700000140417080340b8001c025110030038000310f8a08240c0d6440e0300009000c2c0195108d0350319940075633601003035000074041c00142c0c503d80c06004541407030324000701c6403113071007000e801642404410000314021503006005220401101c0001503944c40c80d19103014a0288140d01030702c00381c3c02c00e0041c407110035052040b4941c1c00c42c0480d0100500440e5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 167211330 1250 167210080 167210093
    0x1021b1507020d0804060201020304140102030403021c0903080309030c010b0a06020303070311070609230a030c06020d1404050a1101080103030806120705031608010e06070906030c051905071104020405060a0c 91
    0x3624000b404584d40400d002820a074150000c510561092071340401e2801c248443c0d50030b13030006036001000b42c1c11441c4100c2801d0000c480a0040742038605d404840190307603032100e140682c0103480d01041a000040c410030320345030074080e1440c90f00003a10503135100c52078034100945070301000d000304e01010788a6484252a40c410425105072175003140c2d04121200b1140382c5403d8032a00c44048800ca840e401c03141c070000c540f01141c8950459010b48035a01c1c05d1b4003680d20900254031050040008566502a112031074120306061481544210b000f06410f049038182442d101418450907810001558014800264480041600160700351000c030400c01d0394120341410188035070000e50b010701c5900c03802d44040b4001d80980b004c440034a0000c00010140c0d41106d074442c5411200780011548241d410099a440ba61050498000900d0714509040400b25a00c07590012644036100140c4041140002e10034481526024400215821440c040c5490301091450041000ba0002d01402c04908030030300c4103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 167212580 1250 167211330 167211349
    0x13020a033e0d1116020108010b0a020312091501030506190501120206070507090c050d0b100806010f18120b06220e0703060203010801050108070e040309330e01021b150702 75
    0x5502c0c0e03090740c9500f0381d04d9000140f907200280690002d6200b400014a020840d030440c1c03041800c9601862801500070301900d0741480280100360b05104200308a010b1900d2105000e018502c224060f08007401d01171440c01c40d216482c54604409403500c2e004001c01d040ca0309500e51019415501c8503101e008500703165040c45013a61001804506140c1010000c0d94424000c2074a01200032080054142c407405009907442c4a07209a0301003a9224085a8150b001e42c012040904403450481c100b004400c0c40c03105a40c21940c0061504003854614004200c00c0c51311256002c402924904500141450030780312400b0741c000210074455444001c1500010140070307000242da08000300b5552942e4a828585c02041c0c01d100383d00803806078030703004161084000b041c240590b4040d03980403242420040340702500c00120051a030041800d00c0200c3e0520021000e140c0f00500315250304800d20b072804006030500601207100104094203a0301c064269a076040910b04043c80300003d141c540505101040c0040b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 167213830 1250 167212580 167212601
    0x19020f01020426030c1005060a080606060306150708041203030c110703030809070825061803120302070203060f070e030a03022a0a080303010306110414090613020a033e0d 75
    0x6c941c641d075512001d070b4000703034050001620348818035a51640b80c19180c0d1000c0d986568028410804034240303203080758100c41e6188040b103601d80b801280b551a402c080c0d10541c4036082304102c400f250b03018590140f14804400b0310320b00b00301d215407144403d00c42d01c81080380002414072084402198440e0b10810074100074240d10003c03030305001082c1c2003c4240030500380c1c4402d1100036907100451f203580f0403100c3c6000f10110740d120700c440134119660b02015010f10016002056424000100541d60421101d40038800e92060b4003001c1c02e0035000149041c0749030503003030b003c0c2d4400c030030000000307a000a0382054600810a60815403880c084e5043c09069545007095100c0c100a9010070303c036034048000c50489208800420140c69401d980098034004ca1080810940015050307880c44e09015504540c400300003482c4070041d0086a0114089812183c6180b0010ba80c41080401c8144075000654030300d540654a0020000c3c80c0030200041e11704c0c0f408880301c5803008074a80400d06040d80101c41c142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 167215080 1250 167213830 167213833
    0x1204030c06020c120903010f021e0702030c0d1505060604180510030f052a0f0d06060f140112020c0613051006031a07030b0303041505040b19020f01020426030c 70
    0x1240d80c1201c40130741e401480e1141e110394a880c0c407542c032818140c42180d011400440250005842051044946800020050340c240c0140c410101c00380e83c610024440f45881500c0b03258894039401000e0080751401003245011301000c02041c41407200180750706c00d01c42c052aa010880e0b541c3d1039100040f2081139403005209000080451040200c0415202491140480302941000120b004401c0a4440b80082d940182070341030090064188204002c1e4084e004103c0400c0b883e5844005240851946e0301c448102030002114803500e41c2e0004019054030710042d070035810150408603da85806c4045c00c43d00104000e00c090008000052103802c04180200e80d04018480e03032401e09130b2000316041040000d6004120004119a020788103030002084064002c604080c1400303040c50495654580c50400c0c014207020004803814204005c040920901d01c402c8403003410000040d1401901103000310362640140024400c2117504034042202d450000c0603011440159031410381188918030541030703d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 167216330 1250 167215080 167215093
    0x92104060f0f09050d061d1f0908070807050316120f020102040e01090c020f060c0406030506010809070623040f060801050a0e0c091c060902120d050f0f1603020709050109021204030c06020c 83
    0x113587c02141078841a0000180c1c1604681c51401e40e0003140e0042d80c004004200c203101c0000801c070100083d04d0f600c4c4c0f00f02d04480c0380240c9200c2c014112440e03400220790034110003119110443d03000c80e000d050382c1542d0000303505150410300e440701d0100050240018071556481c014403154030820a00e20304100401c1a107095061140101c14184d01501a490119003410003060903544505802486030142c200606100c40c02c00c0c404840003000c0c600744000440b28001c240b10400e2802000344014460347e13401c20401c603e00342c8060108c800590100b03208035000c05042000e2282080003680c0003108014160741d400e800400102c075601080301d280010b0200c0807810f8104030160b40030a070928000c80c1d00c7e03e05105031005130341ea110450301120000070024401d014410070054050002c1030a40d82200d818819a05031540d130440301300d0005e800591050000300003c00551040e40e014110814003545030400c0303800600c10700d0f070000d0001420040d12000d15070610176a03034141c0f880044141c0941d42c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 167217580 1250 167216330 167216381
    0xa020c060d020304050705060f0712031e02040e010e130303020c070321020c10021e0a02270c070f0219091506120b0d0308092104060f0f09050d06 64
    0x9403c100c0d81180c9600c90304001041620b800f40949811034000c84003140703010600d50714038450303140d8055180b042c10340700c207d040c1010080d19000714600318420401620f42c0d00c0c04c01201700004060303024007480056003080c001d2061409030f103042907540609000d40d4070300170844039900d40304042c3d1000d0940810054003190b0480c01810028100105074210b40f800100ba0b0304000c4150307004031242001d40c1c084010f001d40b10514502c0301403210400001e40d60b03c5001a00802d01c2c10908071500c8104501c2400c03000803020860350200c0d003012020010604209c02c0b903032080003140206202a20551500c6503032002c0c100c06042200140c42801400d00105441e02c011180444840c014000401c4940441c1c0800c003000f4403690306040e900070b141c14904030340c1c0c1d10280c0300746101034501301c400d01441d4040300c4080304001142c2c0c41040400340d1103540c0c45c541540100280c1c40050403008220303443e80c040300718550110044080d52000c0316940e2000380c2510f001e600501ca02d201d88001c003c1c1c0c0640045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 167218830 1250 167217580 167217607
    0x30f07031704031d090114120a050f030901180b0315120d120b040504050a0609021201021303030e012d020a0218040c050a0b030c03100314070f08010c140a020c06 71
    0x41d4460004807040e044d0400b503004201600109009002c500c040b052248020383c54500500b4425006000903201040380c40c0d103c0d503081040b08a905030440e070002030120b80701d5a01c480003020305a400e00085550390708011810045200c064000056107403c002c0c001010703078800d407031580380141250482d0480c40345590003800303240c102003103000c4041c80c141071000703682064040d0350310882d400000f6140f04d0748140d90303050003010301c85002d0b030300b201028034040c0b6003038800d2000380400e42c02d075001201c480345589002080586012f0240b07041055812036800109485603500040350100001410102c43c6044100d2803c003100c407000e5400381290b20300142000c00000043e001c0e034010f00d00450b1042d1603100740a0b1541e518424140c140408000080200e62003002a46d04000141061000669203444080314002964603004080d0441f000c2000320310100c10140c401003804200034040c0111002019007000b5001040000d40c01000030042c1505100340a030f151070000091046455009001901 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 167220080 1250 167218830 167218847
    0x60612051b010207080a020d050109081308011112040f0510060905010515070c0b0711180a05060405070e060702130507110709090c0302061303170a020717030f0703170403 75
    0x4689480715008401c00552004c40c0d2007042d590090000c0000d565a6400d20144081124054915550f9000c6540000d040c2e54000e00f481c82d08030100c08042414811f12500711000b51480385070b101010000004004480a00107610681050785550084003a0a005041407000700700c1c00360951424401103001c3c840303079100030705030303501074031030b103c6d001c0711486403446134031039402c024101203003c9004010403030a07003004003500d0344200c1c4009584450789000c5a0480c080f0041106005c004404000c1841a284100b5500420848061100d03040441010b00226201000d42d03008400000b050015526039030821749204440c00c90404c242c0c40d01c3e660007080d0510b0480400b60038081c2100014480f03441740a00f05059421168100e01640f440d0b00f040a06e600500c00c00640b00c1c0c05000010114155103803100e86011042510313507507462111402402c10303c854000d403610b4444410011401c090000079509040c074003010880d0341e15210708003504c030380740f06411032100b82c1c0e8080200720802d507122114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 167221330 1250 167220080 167220103
    0xe1201140a0f0516021c09031a0f0a050c03061203091f0906110705010c020f040c03061e0b0301030615080a030c02040f02091e1206010b03011409010b090d06061205 72
    0xb0015511400403500702444d4000c0c4400069009111007030b10841110030320034043c41d450a141c40c445a503560388094410000b1004c030076440002d002c124030101c160b00c015600100c40081003000e840d211045d05200d000103410030b40120140201c0c002018400c00444e0b81d0284007c1400780c0c08109031030f0aa100201c16100c040008051b05400540e03107024841c0d040e4001c0442d009000100c2c01c1c00e00441d003030713504c594042e6400b034a5010303401a00d0b1518404c00c1218074079541c0104050f4201429003003d1000380011403182c1000080030004000c4080c162070641c3d60003000401e04412a88070100345004540000e03501703008030501c000c101a00306201855052094405002107000160070701e049024500703c164001850b4500041000311529025100c0d031401002240e040615803a4585018403d80003050504400401404000c2480c02c0c19000c210007180c0c0040c0c5981011000030841c09000c1540d800782031440c0002013008829003201c4040d03c59200141711508080c1000f07a0380c0c0e04c03507503107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 167222580 1250 167221330 167221361
    0x20702011b0c050d0206120928030e0904020d051002030601030c0503060d02011101061502101103011a13090e030d0c030b030c01081009090302030a030e0304060e1201140a 75
    0x1082207014108642001c80c0d15000080078000c07a2420301800700c40140840100ea01c9241086025208141092600e024041c81c10041c080d50030312103252061500349040400300b96043c0c04078070300000d0341700c924001994401d84500095031034034404503c0c1c003000218020010b020300204010203c0303540d80130798454003099a00f400b428520f100281c1d035030722003550f51a401c00c031044540340155020703182e16120f00c64000e000103030b600d60b0381c081103442e0304505e40d5500040e0440000164184407a0080c184403500c40c4500c2841c652504540d4001c101030000104038080b004100341c0408000c071341d011f000801e4007202c14480b02954803140c5d0f4032544032854908d0311520b000140d00001c1d21074071035040c080601400a100e900c48000040d80c2160004100ba40d01821641c0c006c640b01c6500c0c0101c00d50288250001c548800c0001030180c21703070301d04a812070a41d0b07100340001c00000380d03c40150307800756806548580712130030300f2454540500b80d060440701d16282080c05105c5c061016a012a40340101540e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 167223830 1250 167222580 167222597
    0x90301020a111b0604090507171302030715020d0f1b0b04030809061005010c060603050a0b04020a0902030c030c0c1510180e03090415030f03050d1109010f081f0902070201 75
    0x2400440c1080c1c0304401150004c409010620009a040d40260b4018103d1304045024840b442d80d281084403040391040200150300d9100402c6013000c01c4403001030a0080d82d404086510b02c03030002e43e904c0740800c4010411141064205100f4050300f000071403800d2442c001002a035850400b03507030042c003d44049002942c4100060301c0108007154484c05003449084d0404203928100045501e20f0b6402c400303458250352520000b0002e9130410500d0619840f4a103030b16244e1034540108240c08210303500003000180100304015100418400302c981c0001d04094458892020041c25445e20381c5160011000020107028000c01440308541c030011a5619103c0750740c00903082c2283c106136900c000034442d0682c014803030248246003541180240c040e0024540f00d0540d625118035580c010440740c00e401280000070703410200c1601c0d000390114404240d100710b14002508000030200303201d44001904000140c00070801400007142104603424001c0002241e0a441d0403424000f5401072134200d01045c00c42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 167225080 1250 167223830 167223853
    0x6092101060311120c030c0f060f0d09060b01020d1e05071a090c041404060506030a081206040f05011202041e0c1d0102070b0d05040f12080f060121020f090301020a11 73
    0x2039400d40c0114060054409101c40c0b5084c8052302c80000d030381342d610680a111a0700f002c06c440000c0d05164012140104111005007424422981c10392003e6045410030200c00c00c0c40c2c0c4d0451001d01000c03580c42d0780c800940352507400c2155a13014202004001840d040881001a5543d15446000e01442c1c401c3e03d200380380201c2004201d038200f40402000c003100d400084c0204240d071748240d5000b20098103962501c249503446d110194010b041d00034092031810309103ca1400c140c0b00c0e61f0003070701c2d4000302000360f541810a0b8210020411000910560711a00389503000442078040c0402020a81c009001e0149500c0d0301070312a0340d00360200031400c00c8003207500c0301030744c40000c01d40308490400c50703004e1a040450141c1006010300600550302c1c00c540c421940009490b0350301d6218003204650f1514601c5c288020b10150a032000f520341d038100280071a4010030f6440e040d2045289088056005a440094150300e004601070803208170307495440442c52060298202042a00517400402541c0c000082c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 167226330 1250 167225080 167225083
    0x705030619142e030b0607080f030118090b01050603040c030203070602071e0f1e0b0a0305180c0303190306030c0e040b070504063501081606030207020609210106031112 74
    0xc43d02000703200120003803100c03080703001c0e50104004000c060401443c1641649030304001e648074003210000424004010800305100e43c9020b020050640c109000e041c1c1140c0b151043c0d8801806041d11554000020030108072361003913494000e642c09002c0e10501c0759203110180d15070380d0354425210401c0c07040820503501c10194110109890011000005d941c1c1015984802144031054a80540d20408408144c002c445030180800080315a4041110305d06001c214030050075400403126a640f16201c4540266000b0003591000380180d0641c040700700240a04401400e115030003c1c0c4002100100494040c0b540d00c181c61055005074801c000940741c45204454130311680c421030700010100c06000114180100d500e01008050301038400c0c1c40c1e0032035202d11a01c9c48003030740041d04540c0822502500000b481480000a00540c1000c6080490a80111351544603003034100303201d200d103041e01e200d0b14042458001507888070034008005403502da1910ba10810940102c462140b071a124110400800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 167227580 1250 167226330 167226379
    0x2d07170603120702030f01060b04050a05040504030c0204110d062c0708010e0727050102010b0604050105090405130f1a0c03010308270d111305060306070503061914 72
    0xd03000b07000740490100d046400d5008007034101d9250050b000a031030360a4013401084e0181020707507031065a171803500f001c210f0f041e1841e5209a00650810080102083d008540051242e405032000b14040810700442c2060b48110840c815006c0c0c0341c00e102150408100e0390704100380311100c45021000f600400052285901103034541c001401c0100140034820b0300300082a0001c0703040c14000040720404900c0b0701c1c0303480381140d4002e05601c031640800003136909015108690f41c00707032149031405080000003851440f0b0b0400b124001c40d124030102c1c484600050300022600c5e04125a0b030305403801417030410300790324500d1003e101204454003c030b500c540c5480e0032a8122540000140d00d0094094240340000101c0e6031001c060340003980f240790040d01d0381e41e240300250340700701e1080c00014080010040384c4541ca00440d0300c520310b040c0070807000c0d44002038105c1d0071101d1030030103c0d140d0341c5000004025107040081804442004440068040444040300a4804003210340b100d43c0c2c0c800d28a0a1400380d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 167228830 1250 167227580 167227591
    0xf0b0f0603070c0f0204051501030c031107020d0c1e0e0705040b031f0f0f080708010e0a020d0510020708090405070804020a123002100606021002032d0717 68
    0xd604002140b2040d015407a407403203907480b8580300c400516807031300000c00f140d0f0200c556030440c201614016241c1e6a16204010425095040401001d42e03820412046802036070f100901407a03211050780180304542c2d200c02c0040c102c0c00400c0300c0010000b00c0141c600c1e0028800d40ca00e52001d100450300c0d01c2d0090003620103403a01c04400d2400c594034136815103051406a24041b0b140703501032002003018a5810500006405014045400c05107400c84481c642080d82d800030f80c0e01d0b494002031041001d4007007001c010341c07034040303c004240b4002400c0160418001c00d54034403d40c1d00c0060018108502c0d030024003600c01d000c0301c04000542d64407000391041c2c10120707802907010300500414001c0484d006074030721040d8020300516100d42400d842c80745442007106840e58803140c804100701e4401d581040600081c0041e03040038004d00b450064081c0d41c85445c0114087d0098001c00000c130300440b00c00d4031902550a060004134844012010000f400e2001d644210020703171103103600c4c412440c40ca82c200e80501d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 167230080 1250 167228830 167228839
    0x70519050301050d03121401150908010e0304090c0207080d020106030308010e060918031e040305071203020718020702062803020403211b0311060708090616090b0d0f0b0f 75
    0x190b05540c041b030f840d00c0005400040f80d644c421150a510070b0824950f4082c0419042d01500010590300c05488544264022509a810202d140d050703807031301105880031a1411400410410607840c0c0030f90074040700b5000300440c1d02c40c1044c030103113480d815040003085070b00076100e4444590300c0d42e181c0c000300381c41154102d420400c48401b0814442a4480b00c126100100054a0510143e40c02c1381c040884501c3d441c01000d14041014418442d0911082000303001c0c440b9140b41c015216036020751151058400ca807031141201410144000964044812407980200025910284041a1140d21000c00c04003c40102410b80702c01000740648202c50a8903045907440040285020900f040400e011550b4401c20a03000300c8600304003060032034140344034426101c2e1041101c4000b40b280c0360190040c88102048440c00c2801b481c000c021642507004028000c41095029546206a0b020035095214581c4d24600285400380444503a00520941040160910010480c01e04000c0c04145044845600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 167231330 1250 167230080 167230099
    0x5011502030a0f0e2106091c03091703040609030f09050604140a12210e0d0b061f03060e09010b15031302040908040306050a090507050d081207051905030105 69
    0x181405014180c40808040c84c080b00b02440c44400300b0fa02e110840c00944e94031a200c032240d41c400f10f040c0001640302000800030900d10200464101c10b40e4103200412082c50b40d1142000300b03020355800001303071100101030700903502d0400c3d01d002c200a140030002500000c0b907000460071128451480c0710f0403a45c004000a0500d810540011006104201d4484c2d00208000000410408031034030006182d0007079249448421500000d48011303100c988591082165052030700a465999000c54000150030080001e42961510041440324005204041d40004140c8101440e207034903421145c21f03200c2845d040411500c65810075800e0360900d00d0507661103c2d4041300c1d41c840b00c1502001d541d00031501c1c54003010107911600414122a0340200a80d041e913000503003402404001e004580d0000d1100c04208001190703522296198501400741034416000c146603541801411002d0780c0c4244040f18001c0d259091204c0b01800d1a80100d50240c40c40442000d5100800d000ea03003928100c0c1c4015010418 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 167232580 1250 167231330 167231347
    0xc08010b0a0e090709080709020406050f0a02030705010e030a09050105120414030d140a0606081b340c05180703050408120708040b0109090203070320030d0e040501150203 75
    0x440d00044907820410102090451803962100382d00b038090740c83d545814010a091604140c103100c0e00303402210340d15004220030092a42c1c041c2c12201410300c1807552980700d40200c84128210311419502078903a40c2409285d0b0300081c0c3c040000c0c06004000c0d1502d003101551000151818003c41d10000100d000707143c001004940c50410b1820010144d1060302e00e0007490018a80894042c1c00e40b40743c0f40b08500c410082c851501e481001c018140d1420034650900e00781401004020801c1c801e41120780b004100f02030f400145200303501555400f1175581c05d48101ea180345201c0b500141009490483c060b107000500d900b0540403c1c10700342104070010072142c2e5010000e5020b8400900f040707610780c10800ca100750701d0072071800c2640100f000e651010040d082c00d080c105841041a08a100054a007050440060364000340700c40481c0c2d880041d1469540300811004203d6209051654240c080e443c0402000c680c40300c024203041c1e00c11581041030b030f6201c3c5034420945881c0d00d062000b5a004010003075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 167233830 1250 167232580 167232599
    0x1404060c020708070807140906030309040b04200711042306060d0203010605090a09060501020a06050c0c011508010f0203040c050906041b09081e060403051b010911130c0801 76
    0x254840380360040360061582c0b0b1680c1e5241c51200d5100305280e03000440706000c1e12800303c2121515800440d0302803414101000040e40382c0c8103008103180300e107640f5000340c00507840380c1c0c00c145020741001100700c0d550380d103900303c09400c0ea21840c01103e034130003c0342207000c6034649071003060030b58040301e020310041401895250030340c1a0040c144651001c01400188080c203841d00085019188540d502074803414034030103000d030800040e003003244c1407801e11006100b141d81c00103441d01040e4120f8004941c1c1d03101c80d1001802c900c24480d241d0344a5003041e01d09030300b084001010404685940008000281582400301d0490000341c6004082001c0440200282d1038110803150300100d00410008424040441c1000c040c072045041d840403a807040000c204000051000f10411f821b21100040c018000c800800d403610b0005200400303002c0045581001c00055086198500e2201030080081c00306a043c00001d03c000300c801940326030241402c200d141141d50081c0901e100b0980c540040da40d08050044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 167235080 1250 167233830 167233841
    0x5090105042d0b0a140907052b020a14030613020a09050601030b0d0b0702160312050f120108010f11120103140c0406030c030204110406080a18020613051201140406 72
    0x100455458059070020443d800711107070040d162804c00240031026820030344a22130307004281d511180c005100822003a10b07480800c0f51404030f08514041540011141604140c0c6042d03000303500000f0f96040800c242d40311401850b64040110101c5089944101c1c40003c110351988001f50400307011901000103952760780241c0d411850504004c0360485c1490041422000312040907500381001200784413640e50144400454070049104a441a81c03d645a4805c80e1104400074000c1160000c0c2404010340075070141c0700140d1126841015550351a1103a5005c0d240b060765a1351103602d07050032503c40307003001400c40e081d03219119444590b80e0301e180c40742c1500314521850500030b4000c00034450310302e6540f8400c00006d54880e8420900c202d00b50f005100807103126000c1041a04401c01050040079001082c10790311021120b070105404940c0360448594919544009402080102d0141e01c5140c01a4010b0280c4509655084841070410070281c242d8400040354500080c0340c5c00410045001358000303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 167236330 1250 167235080 167235143
    0x180807060c170c0c010306211b0f06050c0c101b0c0b04030b0103060b01030b090c0a05041d04060f0513020d06060e070f08070f08060d14060c0703030509010504 70
    0x1d402040100503100016521100050080e9008040d100c01d8941c4c041c41104050801d150b0f04810728116001401c0c100c55030004040c1140c540c13001a80e11100d0300100c410041c1028ad540040204e0703480d00003401c036030000070158040d8040e03588a107859081032000300d82006001d90364209490b100f4103a0015100000300c007a0380c143c0046c134012602c40900e4000b0801988a04040e1210358954100700c2c1c100e400166405041500b8124500c2c40c03a030725112800e4210700c00c86d01082d030724449941c003a1501e201c0c0d5400032010907803020006e10380440585c0c5451103a40200e03410301000f1a001b0443d000c4030011074150f0301c00034001c0318440250614003144190310344141c0c000101191503902c075035032300401146c64800045150003030034141c3d6444800e207a000720b42d609000b00d580c100140301a06080b8010460f42c081d06084015001348071507210138440c0701d0700b01806d8500c03600740860705490581c400c00007a40420f00f000c001c00c1000d10144a80c501c120380210164181c002e480110b0319400d92610f21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 167237580 1250 167236330 167236343
    0xc0c0309052d01020a1e03081f15022514031f1a06032a04080606060306060706050403050c150906010501110a0602030c0301180b030a0b060103060305060f0106180807060c 75
    0x5c030351001803e0304c48401d44002c071031141020400101c0c03400400380d041c01003258409220341a4005010440380d0301510980c1d401c0b0403005c0a0b100c0001040b89812078840ea802c02c00e0f41010344502d0a410308125200c240c803500c0281d022282d0b542001d1540d61200711501208040341404840d00c600403603030144000061001a44248a808400103441c5800980c1c0f03020300442d03901d44610b00c8205a041c0031307015510303a085281c2081d2401108549074040286200c0c06800000000340550313403880200c40340907a01490810450906040040964021404161491280a001e03011030301e0100c0269128441c036000401042e82031000440c4c03071110710301c04084240f1684c0d508800041590010707510614a1642040e26036141204ca42d01e68030700615450551071070104030150f152004202e140005420544c2d41001e40ca41200480041491b6031014003c0d005290503c2140540388401034126201c1c0e0382c800a00800e2031050803a10b5a082c461100254000182048124094010a40114002d04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 167238830 1250 167237580 167237593
    0x10207060815040906020309010e190615080a0c05090603032a030415030b03010c03020715091401140a0e0111190302040b030106030207020102070b090a0b0c0f010c0c0309052d0102 79
    0x103d03003036801c080c008640264000c01042003110007449021401d100700e00041110340747c00c94800246540600d4068070040e1501c4143c203092880441da00f000301849821243c01841904101301e060400c2c0c000c0f00d1103011080041902e6103400426142c056017640340301c0020a000ca141c0d521000307410121000c0340e01082c4000140303d2112441c03081401c51980700840d441d240c0304101821520304400c42000e26205000f808041aa6030b00c084625641904000440f200d02c0d040c085040300080034a00340d03560905140607100600801464010b480d81d4005000e0803030403d00d481e0980740461910454490280300c0f002190f80c510151034034107080380c10300510340780c0c481c005c0c950700e40d000340c20000210350002900350465a04000c0c03030006010050b022820140b4003000207955242034400d080507110041400300a0324000c0c40fa045244c03920034000c01c0b19400c0b020000e41480078400040c2e01298125400203601c0c00c2458618101e840d5284644107004010074002e80c0001408809604520450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 167240080 1250 167238830 167238871
    0x4062304051305010c080106020d02061b09030109080a030c110307030c0807080c06010b031806010e0c0a0512130b0702031206091806090715020313030303020a12051015020c0102070608 81
    0xa115001020a02c1e91b5580515814000060314180562651104645c880401c22541d0b40340205440f04c55030041c034020b5500d016610000b8054a0b5004002c0c200744000158118800c0e0503500c180308440b81070f00d070605219a8040c046849000b04400035001c03409802c0381d8070000b031189004200081c400c1c0021810082408600391604200743c1000e03c0c108000810701111125503a0800007400d8501d00608656062003441401440d000d82201c1c3c802c0350228010310814044c409507000646054000034562401c9407000f540039444074010703550320035000d006c61520b0b84040112031940b00f802025180c2510f03294140601c038840108401c174110002418042040d10a02c401c40c00b035190400240308850410340d80007681c4881c05030040075036008000034031300d2055036400308046a0f05400c0043c4c41d08403040090f1462418000249000d03031400b000c00440c03550b240107030f4003902c207000750b0741005010b86036003666165144d40e1201c3c0940e014040401c0000c0c49990810f0b40710035103400c0510415082d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 167241330 1250 167240080 167240083
    0x206010f170d0c0218010e040b060306062b050f010b152104020f0d03080a0c0c03090302121c0203040321080412030609020c01050402180609010308090402160f0204062304051305 78
    0x4e0304015130b900c0d81e00048c0800c0c0800e084019400210403400b070041c60600c0800900340f80c800b012864048621910850b040b01c0c44c40d0705141e217954101054881c004001c040315030007400e80c04d180e180300f888004003211000f5100001d591741202807012840f4600001d01030100d80c403c00030b00484e070090010002500c130391070f601203174070751503210b6100c051803410401820f10544150013040002c11850b40d160001195010316480212074041e58845c550041220740103050001418181c450341c43c0451900c031102da8000008c0048a00030215250201d0816000d400c01036802000c000c0050381d4180070601086102400c2e0454204034200020040d40c0c480114081e80c0143d903030b44c0c0c200e9564104001c1075080110f0210400300010b640400d00346000000680c01314411b001c0540208004245855142c585034110b503520040f20720f2a90404041e4581002e110104620480c000c45c10081e000809016451034844180901d22110b80a003400c40c09100042400809403074400007002400008541c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 167242580 1250 167241330 167241379
    0x3140705070f09050f090f070302010305040507051519030b2101090b15090604020306030d080a18061a0f030d0509030304030602030c030f0f04150b011701060206010f170d0c02 77
    0x2180314003c12a4500845103418900d4010300e01d000321f820120201d40c8245020032103400f074a03824200002d1548840c103050b807a005140c0c0000e80c00c80c070401220f0003004018405040300c02540750400b04048040001141a40d05108029802a54050006070416841d0a008681c00d041900000d1000301c2034580580f500c400395800041e41030800b4103445642080d40400e98011003d0754103600e1400c09402196036540110385241c1000443c03004500c0c0806150861a045031fa140d42d03c80c0c8a402909240c0010702c540300c0c100703402290001c03415116062411090543d131000401070408640004c1e8156010350041d07a806905000400010000841903c080c5001d4651030f200603449141400c00c000507003401903c1344201c21214020440012890318615082c08044440418859a00c400681c0c0d106040100900d50403100c4c000407070010b41c00a581d50403207240c2c0f06110038003990b481c11200b1010b03c1d580719880c1c0d42c00c000d024004650040d0305072648180702070251605402c100c0d81c0c1048040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 167243830 1250 167242580 167242589
    0x90501050a0b040c0e0d030509030709020a02010b090108011506050c0c0a0803070c0e04080403061a04090609122120070b06040c0e06033105060f090102030403140705070f 75
    0x941d110100042803c292140c0400009a82010b0808007212000078628400020b4000d0130050001042841c03500c00b1b0080d00010180002d040d9140c070b0b0079507400b0b4060200d6078040c0340101001c200010b841c14050144813001401104500e0781c0c9406c1c04c030700b190a984a803003201614464502894182c0d141e10080c00000e00201000d1034035807920307150101c5146441e84c404603040c0e42c0c201c00d01001c00c440c041180c00b100d60051700015074200b01c030b0581000440070b024ac59800b500e0100c12605100d40e541000d00d00d24818409041c1244407405c040d1500004544110b031550580144d40c00300800560000281c2e0011600b80c00302d05000001c42e5005038411481103030041400010b01007941007501402802c803005090007200c01c10746101140c40ea001c0140010480e918003015100c40301c48106ca0420f070107103902600fa10040227420400c0d0380d9001a6188141100b07000009684402e062003601d000320383c503a95503843c0d141140c1d0841502d422500c1c05030b48901460500080e0241a403184c0d80040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 167245080 1250 167243830 167243851
    0x3030c0d080406150812180a0308120f190921050c010609020f090118030b0c0a170603070e04080d051005040c0914190f0609051c0c06080403020109050105 68
    0x10b16003403400d4400c3e21004041400c039459081c20600000a010890310383c01201c4203e40e039100d20420050310302510030070007000e4011940c0c840110512580c0d90007098141c280d042140110388030b42004040260040300c41864000c05508410402e20f03841e00108000ca001d91004000c00c03100d002e11303401245035840340320081240041d51f000420000c0c09a80001c3c031220f01c0860070700711007402d851940d2040076400da04001002d4900032994403004100c40203107401c20101038142c0303070007010001150b011034001e00104800c0180503503112054690b944c031a1740d000d0b01030703c3c420703203800e45c85410b404000d007003280c0800b011700481c514011284620741c8550b4075040d020309910310301010305c4200e44440b40290200300048005010b011120f0030040714515040e40c10001c08210100d8203248858640c1040254802c003910010340164400501c2c0160b43c000c4842d0510100302c035440704511b02c940c44c00180000c0509008018190007210131a070710502238000800c0c1c00302c2c0f5540d05401c542088030b0741d2400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 167246330 1250 167245080 167245097
    0x303041e080d0f0c03051c060f080303130615030b0a021201140306011703130803040306050618040f020f090a0c0f030903230f03040f06050a020405060a080603030c0d 73
    0x540c05005060000c10510018050b50080d049000b0910803607454450306000d1610090002c240c440c0044525160221200d4070350111541406006803480e44244010402c0018000c600c0101c0401100e00a1031904031180714142542e890340d002d80f071242c004102d42c0c041603000001250b0b184002a200b00744020b0016540c440190718120002c40c1078202e4906e401d0300075100e111a4a00041c0c0c00c2c1034401c0308400000405640c1b201c1c034694800c01c401d40301d03a066151400240c404000014000352841490144010ba541e94203101010210700a0341020f101c40401060104003480611454140040c010000c200304000103c0e032000c2040c0c52440c0c03e10350760341a4034061076000307421880b6075249280520078840039440080004e031807402042807858000484a07030000031f010071a0240740c00016055140d1034075003421000e5071003500094a905061100040c2030003264801c50f000e40300c0c000d150908000044000729034050005058a8061000b0000c0b01940c0c0c01c100400c110805165803146075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 167247580 1250 167246330 167246369
    0x150114040b03041506140d0203010e030d05090d0305061e011202031509090d05071e0c08030a090801020a17040213060825030c0b0a030204030602040e070f0c080a0509030705030304 79
    0x5402003110f0b03070712145500d002d50600c41307040c20020ba1141b01c1001c40d4107040010a90002a00400c0810340885d8148000a4401c4c0c0704842500410300c65002041904d1540e41c0441e015000d5800490310380d54040401071501030b030b041079101c00314a00780040c0343c480d031505005c09040f81280c0c02590945a8a180c6c403c2c00c2406103000e003041e50340082a84003800c4501d42890000e4854002e2500040080100503210103421001c240da10451542020b00342c0002d542d03072004143c49070300c1002c0b10000154299000700e000001402103400c400380c036a0b034164a0b0314910000c3d441e000c1c40600105c1e07000c0c0c600c40e0a040f0400d2075019500c0a09903c03405044843c03c17004804408840700c402c880c6c43c3c100c00040800c08100014403440c111070108a10381c0c1d8414040700201d0081c825a000140319507c0800d01041040f81d09040340d103d50640d84400c000000c10710000d481d01904003500804040303003048402d000502c034602401c040c070740140444d49120749440000e8155001504411511114001d0854 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 167248830 1250 167247580 167247593
    0xa0306090b0d02010e1011011505031509060a18051209130b0d06020304020607060207030e010f03050f0a180c080c090c0a080105061305091003020306011508150114040b0304 76
    0x91001201d0003085042c25a0000e840c005281504070b01c21141048800070320b41c0120000b281c4021104000c1080c451f1184040300d1910060040902901c20f100300c15600b040d00078822405003500b407006150303c2d0b4440281030b0241010368182c02842d2400d20003880016000c2050202d4004140c0d08240c46100d07840030b101da110038449811455504010750320341c003a210164503581c1240c101e0307005aa2559030740080b640030705c0750f00710041807188002640000e065000d500c0e80e0b4201c2090344c40c0c03281503c1c5030030304400f519810368501c5460351687c0702142040d40568402e040c02899107c501045171000d40f03d40780201101d6119165580100051743c0f803501c2e10381c0c0fa090340308485444c01400c1041c02c660040103100c05024682c000c031400240c2e0454100c0d070810003001400d00504981b01840c0940010141e010940310803402442040e0001ca414000e4003e850088442a914200c45680d0102c103101ca000e0400111030510140d060f4400141e540d0a0050001d8150500100e0b03603400c0504c2c0c5070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 167250080 1250 167248830 167248841
    0xf15190312031112040305040509010e012909012f01020c1603050a060b040f05150103050a06140607080705061008120f07081b03031303110111030105060711060a030609 74
    0x107001c2500d021002c141e074155040907564a02520584410305654510f42a5190b12464014551003810701c000005c1d0320b008120018103a803a001c241900e07076440d40c10506120800174042c1c500b000024070501595502c10070b1301d100e2071031409894004136102e400c1403601d010302002c941b018503500081e110440100030821300300c482140e4440c2004161954031250b44544000d20024141512080c50f2605555580c0124501c8004907500300000d040980104c44144154403d41d07011901b014001803100c2c00e54401c138012214242e150200485804c070401c41c076a804550101c501d460207100d05000f0407010801d0904c44ca50080b00300d2000341c18030180f5071400e0304e0b81ca84008140f60130450002e24805030801d854007550f010700482c0e150703803448000c0350019500044e2480356100102c2044100a10b2503a0000c5550081c0c403000003444110460300e090b40c0566004c503a18403001c01c0100064217142008180241c0070703240d031080e070b0049040042c465030300482d1903030002500c8103000d0100c4010340c402ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 167251330 1250 167250080 167250113
    0xf10020c0108060d03091809150507080708010b09010c14100902150a1d060d09080306040f0603170c070806130210020d0207090b0d06020403150c08070203030f151903 73
    0x84c000122119a80148030782854000c4034040000b01884609503007440c5c01004101c0c0e0302031084a100111000a00b0044c00204d98001c00201d8040105640728003c215140c1038800c9100d44a1034800d040c7d00560702c0038400750088407412030b408494081100300f40030011007030309000750110b5000e02d20300402c032680c205011011030f070350700070032464002c80e8201050450400520f80c0064446041030002525800303070550045a40d17060030400c070100101440294410f0400f11001c014003c02842e81d90100c51a0340401842600009042414508003c01801540c5040f00840b40071a4540c0c6180d41001e03015684090580e03400100d2a08510304280c681c1c84098091000380214402118000d64070403030307441003451705940e07180d40012545460303031982d40ca00e8000d003081d540d5039505d01d0151549800780c1e1514000911700142c00c851144200c1010b806600c85074015825a1902c4044619841018040203124030402d005200f694860842d02d550504001310807840c00e51450900c00ca020801c1d404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 167252580 1250 167251330 167251339
    0x23010e03030c0406030b0f03030a080a1503020d020d0c0f08030d0507110a0b070225050f030705010801061103070c030312050f1303082a070302190215090f10020c010806 74
    0x40040006159040e40c044484605d0003041c109040c102241000244d210701c150180400500040fa04c1d03003040086028082458042161540101061080e107034a40402980710300c7e089403410140c0740051510881c64010758211095943d80c40c1d115004150550200c11079800200d400d002203d440d203c0c0e5980f01c1c210f4101084411072405507142c5a52682800a225090800104102c140b08000094601300700b040c0d804011004402e00b807500d4501403046602c9144200b00c2c08010b41008103813081280c0041c1c6864a2a90030034000780c41c00030803d02649850700c024402072002c0340c03900860f600258040c2d160070788a01c40ca0160082600c070002c045500c0070081106220b903004424030a01e03585a0503203041e021546a910f0598802c10750148000d908001c4c500c001e044481e00030001f070080c944240c00721b46410010030000080e49400040207584040d44007102c8450200b000001c013100c142c0100840101980140042c82800f405881100180d0000110803540d58000b030540e50041e50446 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 167253830 1250 167252580 167252587
    0x10050d0210050a030b0907090e010f1a03150a0f091407050f0a02030409050f0108060f090a020f01110d0905040b04020405130c0c08030103030201140705031303030e03040323010e03 79
    0x20086841a1465010389042150001d03009480f40d1003544040c0e11540010012611410801c50041c2040a14024680c1d10000c08000140142c0940035803c121940c00311800c002150780340b21070700f51360070044c1100708405581002c0c103110703640c40c010700016028600040042c54100060702045420780000c151000341c50b60240701000fa008030540300c05030360004d0282d0341c404401d10202d046010386e9006c000828100004c0c89030320380124281c0c905907003028003222100d0380c0d00034440520060644030070b4103c0c0c119000da03c0250511260708100014181442540310980b0740c04c5074985550441140c00007414100300348160f18242c001c8072a40b090454056042906083c0001d200c005d0760210b0005069440ca04856603502801840c1c5119800c0b02047e92250b03507a04010780a003d4206440c00c200f01141c0000b00894040c1c03050324003800d11135031003440a0104e81d8040e4000c001e84542440180b1013400000300003030001c20700c0c8052041c401301140f041014054100c0c20768400d100c00000507003062 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 167255080 1250 167253830 167253833
    0x60a05071821060207080a020105131a060619030b010905030d0e060912030406020a110a0e040201030911030102040803091009051806010c080c03090a0b0a09092406020610050d 77
    0x460a0261400b424022102482105915404882c41c100081c1800d0002c6420b200f4411a0b03805031000d000e107030700240035940d0346105846001030302040042c43c0300582c01030b0316480041c0740e4110394011806080c0b02d03e050001a4041810900c2441e40e50000c0e4032109003c041d0b50740440860700034603094005107420322040c1005412a02e02c400524005e400228500a441c1d40704e5051940b4201c420003038968a5031144002911042048400d07030b0922040f00c80321000313040800400c01100e2485140d8940b940701d5a0044010700a10001621441a80803907200306507000c0c07008100800c80d240c015599050320009100403003001d07a05503030501c003024004110130f403205c1e1007040205003c541411050380d03c100050b1a008941100a003030b100000c0351400c90307180700100508401504543c4017502c6513a4120100c494030070380802c100010991881088810b00c690048440352604914008030408460369401620203540d200c600140e2020b024420440c19000301140070f02400e81e8180341c000d41c00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 167256330 1250 167255080 167255117
    0x4050f070506031b0d1503050604170306090115030f150801050f060a031b1d06040531170a020105011805071409030c04090b01150c0c150c06090302060a0507 69
    0x20f404c2c5031400403100140e2000c54800030307402070402e51341c00081060302c55120304105584210446080700e000042018044185681c00180d920511000340400301e103a00b0446820200e100e4028400c09041e19069541c000c040380e4091044e010310203045103603019203080c06060035200060b00c0703c80b600100f0f42c280320180e01c40c00c08401c1030300d811101e035000394201303141c005403003a01943c890017440c01c09581415082c20711411250041400721020310107616a26058584c2800d0380c0c01d80c10595082181c081e1480320800c0075100041d0042d1404841c101580344070305402e611402010005075514401030040c010081020b5410f5440903c0c00c02c4640f4001c0c1010b400ba46048903680f15596011408070013650b010441821b0301f643c040d1092000550a02c2c00f28885003080c080c1e4405a0b0010180c500c29034421200341c1003d0b07400140081c10940b40040c2889802250941e100420100c5000d00700454910b0141c0030742c841c0300398002d10851070b0081c94441180da01501d010100264004480c4007a1361 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 167257580 1250 167256330 167256361
    0xc0f080103020d08071b260628061706040b16051e0405040213050405060f0901090f0209030f2103070503360304030213061508130204020304050f07050603 68
    0x9112002c542c0e45e80c6a41070000306001800c00601590105200c0820024880c03415548084401101381e000300362280c038266103030f480884004090001400000c8243c80c041d400d00035040054180006500b9180c03d4103000e0140c141041440310760152081c4000c1011510750140d02c0228103040828006c00303050010301c00d1088400005890928548013401003400380200c600615004004554419440d950344400c64468030420340700d68506800100c080c01c0035020300d0001c034401020340401c1c3c1c0c00c0c540f104004003016880709011300da0900201042e91010440407100d842694002e00078030100c6521198041c8041034007003808403040c001d100d01c00d80c2141c2a81d03080003425490031060314010243d15120783c007880d520040d0b00c501040f08028801d0100042068900a58400f21400000c60020054801c144188031043c00278034203000320b10b4440c0c150a6041074403481c000441807c90780004080c1d0300191010b0740c064001d18607046440b1820008480145016a03407641185014540001c440a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 167258830 1250 167257580 167257583
    0x30b0105190614041212030f02160201050c0102210f0603010b01050d0f150b0408060907080a020d030c02040501230f0901050415030506090309030706020102070816031709010c0f080103020d 83
    0x40c4a071083c2ca4403114803400da80c0908007030b045401c08200641448031002c0c10102c400c40129241200310000b80e900b40c021141002c4c01000c5500b155107941c4d004440e40c1c0d00c500404070455500b0700844510300e0b61088069040903d000300650203081c050900399105001418061103a85010340d40c80c044d98004003600c140441c040e078002107100141c0c4030341c000303042006100813802010b030b680800c0619040d80944240c40c011400c5803d140d80c0c40000e2030f42d844407806412116880301121500614049160151140c03081c0380181101e1000c3d40420705441003a01704000c4100307601d40080075001ca643c10840340d4201141e90308018207070840170411400d0180501401152a2010000052891002d443c0115400340448807540b0303240e001d0300c1e101d8002d440c0e00c0b4070900035000300044184c13050096940103600319078402e140c00c009001d001e50f0460b03010411014002d0503100132441d043d4240b0031900c111525000031401096000c1c0042001d14403002c40c000380301c0118014001360310f45524018040b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 167260080 1250 167258830 167258837
    0x3020c1b030109021210141b03090712030c0b06040902010903110a050303070602070302120c100f060909052112040605041a01090b1305240a0f080106030b01051906 72
    0x103001100209025003075809010350003141e00f20000000035000294200e4848400d01d00b0481c80f001000d04411150b4165a001c0400c941c40031440400742c01072000355000a501400c44003002e42d54074146500348403485090300880c40040f1004140a00400380c103520150450b01040540101d900282c200340326800040d20400404e221503030f0a0304da4581d580d014000080440392668410720302400a9400001c045005000701210041c44500c48020365030000445400742c40154990241c42009114041240002c507440341400a15902c55200d291040e500541c00340251011841000b101480c45143c402411001001140c15100d49550b581c0c0e0070a520100110700340e250790804814140c0c554030149007441c404d4000040c940410f41c410b8208031015110300441c0c44140280d40129041281c1e60100c03c2010b109001160221600324420480e00030844210251240c4400d0861800c075080341c400c2d17039540d450600038000f1914000c2d00529089441740700f03401800c114442c104529100d110b050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 167261330 1250 167260080 167260123
    0x305121b2a1207020312030108030d02090103090c091a0f0f0112020904020f0703020c031506010318051f0b040605010203300705071109070f1809020a080103030f03020c 74
    0x34140c071044100c0048072080c200c401141590b111000140d1120000f28071a2043d8070741c0c483c105080030f094034121920040614102006091071001950060800504040e0750350041800900c00304003500241203500c02c001080c4281c5001000a07004006d4407510485040c0d40d040b1045d9120305200407481070030b03e09840c1c06142d00700008007030300803800c420741c1c46400418003010740820040600310190007503088403106402213050584914603042c0410110001d200042c00c01d50080c0c010b0300fa5886903000c0b42d0f40051b80f81e2101ca00f8a0265408110340358503200c10003050300b0282c05582c2e0b425108a4040103081d141c00700207941c900c074202c0400400c031580400100f800414002d0041007404d0b58003481035524061200400c4c6501440f4101c40d0904440304920b064107122170030758400d0b070352a152a041400380ca2400e54416230521410034504a40d03180209070081c281c0050301d0484066103c52410307506502d400703002c018002c0200c04c1014410301011603a100001152101c17210401c009041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 167262580 1250 167261330 167261377
    0x609071d030d02010b0907030507090302060c030915041716030611130603020307030f1a1c140c032103011202130212040b0604060305060a180b01030305121b 69
    0x854151000558180204400700c2900b94040d00300d42c18048040300d605d5155510448194111070040e070701d02c0c0c00240380b00001c0c801418000b00428980400d001142d05000101c00021001c0c5110300003031540350008502004020381c440b01a5015031410707805825003d4003200240c0170400e0038071016007c00c2d00d803644909050450b8084804c9600055040c4454580340c000150180d4402d9410304000f0380b8005030b8100b034a110b482a1588808620800101c0032841d908105a0b026010326401425916001c500001001c0405241c080c40c1000042e0000f11310f602c0403d4144030901c2ca540300040b03115000742012803140c608407819030340d4030321090b01401c22034000301c2d94000c0c8010401034154400501071110b00600012180320324411404404155225824041507508030310005059a1004002c00d80c200706503000105065128103079111284442d84910b01e2409081e4001c0e000f00348002400951100007050213035001450061400d0b00011840b0580a60703c50b842e1100380d80c0340c00040d1601d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 167263830 1250 167262580 167262617
    0xc0b070e0603070305040c12080a0f02030906040305010b040b04050702070303180e010e060301060b0906070611130e09060a050622140a0e0712030206010e041505180f06060907 77
    0x341040c001d401c0795100e00e020301d8041c004040c180d8064994145480e000a9808903001440141d140d00c41c510700c1c140800103d05640b02c40c9101c140d80b066000a01c0500940d80f904006400110300440001c01c04090103401d1204441844400390300942c03c000400c0b1006800046810480b81e1510b4403185130b960042181d616810745030012080d441011000050200c003842e016030080c00218000c12403141c0c4c0341d030700c0d40e07603407162010703d641021080c403090010544660103200c088030040034003868050050f251400d41e076503541264403044403120508c2801d400801510307034801840c060800ca0f606000c0b00040c103200c125000c1c0c040b041c1042220800301044c1b5000302030a510b010000c17500780d00b000507204014089400e541105032158400000300d02810b400e91840f0150550043c0c00c4590074000181c448400c010826102c000514003402c0030300c0002d00c242442003c0340d180c4400c11a02005010342403040740c08103102e5542c0720b2400d100f1070766928101c0642004043c02c0200364410f4026480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 167265080 1250 167263830 167263847
    0x403020909030408010504231c05090a08031204050d09050a0e04020f030601030308010602160b0906030702070815071403070816020712110103060614031b2a0f0d0c0b07 74
    0x400139542080c0a11040200030481c0107203400102c00d4481d00c0c4035400c1c400303990765980305040c3c40d2882c000360b11074003003140a140103042e0030a01812071b86440b80c98108031880d561107418641d6041d6102420032007030140c1400350600c51903903840d1142d121403902c8002440c1c9031003070061a00d820342c00004102155540215040a004082d059450642e500d05001e45203640074820500940210015807000342c0420301504280c4506030001742c103140350041401280d800050100b400c4d4400d018010588110400908600340144c4400034568039022000502440c02c0003100c680070b12092041c0503a00e5007001410b80d000b1039140a602081440507412440c05510750721003295002e044135060b0074007607a46c00c40076151001b17807000e0101035580c120884031b110500b07400419107803003071010552505001c160311072014640112141086401005030040c600d00c102c90071070308001201c501d42c040e00c042c42101c1c00c101e1584060010780075040c43c040d10482ea0100300034099241c0c00c0020303404601820300c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 167266187 1107 167265080 167265089
    0x110d0807060c1103120105100512040605150a0303020c0411030f0c0f130e04050d0f050904050915010303050a0e0904030c02010c0303110a0201020405091b04030209090304 75
    0x181d00300402c03040c1c1c1c0810800c4030072043d45801e2203041025094044e01000f003000c280d40752200b0040c060030030358000c00c00d01c0b078203100403400345a042d907115a20540215000c42c60b551245a880310300d6500005081d403142c50207501205065000070004c0840f202541c00300522006007040c002e03a404200d4600e12000d841e0800148442e480304060003425031504010341c2030480c0c81446245101294100c1c500007401002080244502000030089000342401c001610744c84031500201280700341040c188c051503d8001113944101d0400500c04d101286415100b199612440c0042c02ca92003d200c0c0030000d588155a40460310b0b140d49800d00803070781512040341000407540107690503401c0c0c000580c00d16503141d0420a401e00210010304440115071700050307403a828041003107070020f4050070581c044800148480c14101381c800403101504d4045540c14582d6071080b2019245101c2c41c0c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 167086330 167266187 := by
  have h0 := BRFrame.cov_init 167086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 167086330 ≤ n) (h2 : n < 167266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
