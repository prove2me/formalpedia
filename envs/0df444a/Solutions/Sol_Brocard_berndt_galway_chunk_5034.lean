-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:31:53.270983+00:00
-- url     : https://prove2.me/submissions/1cc4018b-79f3-4065-9ec3-2ce3c230e241

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 905215827 ≤ n < 905395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 905217077 1250 905215827 905215859
    0x50f040b040c080706020a02150a121104090921110d0e13020d06151d0607050f030309060f0604020c0c0409081e0d0509060c220f030f120f0504 63
    0x2d10b802c40141d000412060500180b0702034802980030303000802160040145440018170811020442080720000840d08494120100e01c09440701103400c2095051800c050b003d554440c40d252810400e50304108002005001c2040415028603502d01142d030340202c2d0b108092a004000c5a8042c0465003c481d000e400200451100244120042c80389600c005040e60009144c0300c00c0d040d00ca6800b81300c58001e24a5007100742e5090302d4540d4400341c0100d0b040c070b00d00c0c03050081c540c01000e00245010032702405001e00d0300d0b41c2c2e08840842c0d9032410700058841d50383c2ca003140c0d494826610a80072416919090084030180940d2170f008210801e1003000304402071020407001c464640041200c9040068081000c50080d581c074000b03030b9185d62840c140314090741d20040c40f10629410107c10003c1c01e00d0420243c0e2111003a018030b0f06030207100c0e154140b4070708485030404c40321550002000001c01070350700c030b15110080c4140d10140003c960464107403298600e0700c6e1494041340f41800140b041c070403158000c0c3c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 905218327 1250 905217077 905217083
    0xa030309111f020601090216030509030c090112050c1c03300f1a0a1e0f032d021f0c0605152e0c1407090507090504050f040b04 56
    0x150721a0a90350001d946103145100480802c07003400c40221120b90113010071801805211400c0d442d2802032030000c0c900a1480c20300074240f080205101680b80c508001030501c0200c09404803000f541c503580d0000c0306104100040700d0a200d160759140c21418036103400b4040b10384520340303001400c200366002c0d01d04e4a081410002400c050308248a410401e030083c0720003d03014114000b03034400414050605903071454580703100b00e11f09072005a00170303280c131010581124154070140d15003800b0018016640711075a8000305a070191703024080b003030004a44019042c00180c2e1000c121025290100c1d01160110001c065407200c00f50912149503403524055602904041c03a2a219003c10b60303644100b00da50603509840c2500028a2060850600304110640b6410716005c070018044440303400a5440e02410800040124102000007048030540d40450031211040a44282c1619071000c00700501040303c0b16400600340b01030014442c1090b100b098022007094000c0c400903992900c4440001c04090402c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 905219577 1250 905218327 905218343
    0x509060102010912080603011401050a090513050703031d0d020306071d1c03090506030c0315150d0504260d0b240408150c030406111c02031603050402030a030309 71
    0x310300094002c03060184201d5003510b4170b012505101e424903003100d032801d002c0c190400b00e500040c803139640c911810078100d13286054003280c00d9a034606140c000a03e440c200919500c910807000c0101504561451060200140d05092000802040140c4030310f011074040c3d0590045008500c00c2d612581e001000c0039020540701003140e0001d00410a9540d90700d400c404c0c5440310421010805611440c10341c010f01c07003221854114105100319000c10320024040030582c003500d0240c031f941500d07001502240c282d041c09401c0d451b1500c1c00740d2140689801c4800301d620101c9420405564201e452a00301c050b481c0c050f6460030403200d00c07242001000501c0f03805500c003826480010050240030280715030001070b043d40c00e444034606400185000d0f58602002c01041460040007203c80e02282602e9115030065004120083c0c1a400c0681d64402c3d442c040c41c1741e40305403c6000070540e03150002d6010343da0f000c0805011884100044084440990b4020340c5508034185480100b4466002002568020665 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 905220827 1250 905219577 905219591
    0x4050a0209120a0b09120d0c0e0a03050c010f02011e1a060403030c052a190308040807031e0201021207110a090e2103180c28090213050906010201 64
    0x6101c0e0b06101c0e10402d06035000b80c01601c108959440203d800c01034040c000c01603d401d0310302121850043c5d410f160082662074102140c000d11800302081021400b406080c07640e916410000d4a0b010f2508034180840c0f1214542c5200c50f105210f02c101080850fa08400700ca408441100003034112028140c810f01031320505100c00741d5400004100945c0b003034844814980c0c0c54600b150a144030140d146400508170000d284843d9a00080d00700d1651003210780c20b256900d1107600008a00c1c582d000034202c00d41c045408244281c000684030b0560303011f6641313020900c9619441480840302101d000b801608001c2c1b0816411403248003500865214071011035880328284049880030070030f54002500310362194003466039110144110001c030304c91050710018020191124815910002d0000c03140310040b000402541e00061140c039000b0030f8002c15410120051000409480c0b5154110f90400418a0b40c0021144d01138822562510304180050b40e03503034944810040c0100008000e03034155522021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 905222077 1250 905220827 905220829
    0x603110c010f0b010815030307120315090c0e040225020126011a03280b041d0d1d101205190e0703031d010c020a0b18060304030e04050a0209 62
    0x2940b40c5800031440d000a8469908000400c02000907220391500303c42841064000e440c04421070303038404d800c40da00030000741e13030300c20100c005100d04031400d402111000c0000c206902e20b604603c02240c03440d9100701c039540307440c801c1004030b10a140301c240c0c0c006174006201002c80b4560000300101c03070050400c0000e005c0305001902048154041e1203804041f40b40052041c0001c0390f094040440041c0b035001e041d0319101902e5940c400340c1c00b40301e003050b858280010003218106e4100e880000030240c000e004200901c803110000b0100007881c42124041c0c0c0c80c101c1e8001d8407038102d40000f45c410348404100380b510300081c4403032411600004020003140000003518058503001d258050180b0030307036180401d00c04040c0081141e100c3d41d402403182d0071689042000c80d0380003848886c0e011100100d502941d0004005032240c00c41400025000718424030005407078680b403006402c445001008100d040d40100c81080810322084400a0101e8468441c481582c20290b100581c014a0b41c10011b140c00c840c0340c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 905223327 1250 905222077 905222081
    0x12020307150e0d050c0a111c0602070203010b0102030c1b0109030b09100f06050a090e100606050c0705030604080327070b04060e0d0201230f030a09030807021203010603110c01 77
    0x3079a4040c0594907407245522040c0c1c20440e08a4000551030501d0a010642144603215042410301070082c81005401c258960303984680d0b81d90840c580707035510b03011ba540d901d0180049d41181900b40d1295280002c42c2e0081d5001104035181a01080094114440d000c104034803008007506031181040341c082c4001c00041c501203081c41c000d0101d4401081a928070b000d14800703840710801c000c0840c0342402c40401c000e4440440e41000c0e40c0710a2008100c2e02090400140707480314940b013400201c2c1c00c04400040f0140c2102c024039144503980c0560b182c060306d82c018980d64000540d001004d4420410008411801c80c80b602c1060300c450f2101e01c00407a5901940515054070f035005410706540c0082d0070014150030202e00d0300c074540b007a118070106042e540c001a029002c10344241050302c0e0b0b8030720201c40c00314020381103801d90f4000040340c548a0500b044070000400b0104011004280003c0100f40000c0c000a20015041d84108840e80766a09103e01207016103031008101a14020a009291044100b8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 905224577 1250 905223327 905223353
    0x3150c0f030f041e12050f160303230c070f020303090a060f0f021504020103020f04030813090c0309120e0a08120c0705121c0e0618150906030412020307 67
    0x503084000d2509044c2070810107003155410310021507101c802c99900081410170003003940846410410380301d40d1068401d14182c81203050241003001d400310204105030700355021101120480c091403120404101c01d180510701c051300d221100c0d00341440408c0000304a102d4417224144041c00f41d80c00e065032203000c14180ba5241d0403613400709400000c0340718450790241140410702200d00c02085008041c810801c403030440608040c0c10582c001a000c55243d0010044400075035101520540e580001801e03100c806604d8029200ca0504103180004618070030302a81d03030f41036001401442a41c5480005450416061a550350004103030040015294030a0010801c039100810035165100000c908080c2881c1003034001910a00303c50010518210002610b283c80300c40c942041618003500c07041c182c411901801c20280d205e080042c1c941c40c8031003aa013524030100c00594100c1c140c130100010200f0745005074a0304e590850070600c0000d01003078000c0e0203100c400d080f50064910780030180d11003036102101c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 905225827 1250 905224577 905224591
    0x211f0f0605030d0e100509060a0c2a0e04020406030b07030c09060311091e1201150602070b0d0507021f0b0a06050a17040204241a0403020a170c031b040b06040503150c0f03 75
    0xac02464179081c0400c1103070001c42d0310320701915016480100e221082c0700d201d050241480d100b825400050854546074806e2000d16005050b80a8a14040400802030513002107048001000d4600010f070090190081c040300d06009080542042600320501c08001030000c041c16130440200105501d580384c002c81344041c0112080013184a0516034804408008183d000300c003190f008000400010101c0c070103031003e1500441e0082416203809404a01e402c550030100204546016020748241c00301ea400852010b6099a400c980c441d9500070a88180c00390f038002070301042034611790702c400e10f0a40c2405a80f21384000c000190b031714203803170f442d1208075401c840d505243d507030781c0c1c1c400d0000c1010400381c08061451494010306c0d0904681c00700b0140282c0d03120351880301000701301f44919907070700b03100d44d8000742d102400315040703c803054001191040140d503695000e58038180182c0300a042200c04c440c141c8201800825402c0340d40344003014801001003052403800020300c00003488001d181c00460140368 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 905227077 1250 905225827 905225837
    0x19031d180a1a0a050d02011b050d081f0e01171908030415060302130b1c0506180109050715050708040b0711030a02211f0f0605030d0e100509060a 64
    0xa051482c914041c01c00c0328103440350800440421043e13503580c20807480c0c20381c20711b00000440604407850f1500c400385000200305001d9802035420040d0301c4004c8600c03803129040c00010340e0400851b25150f0a81d00d00030f412008a0400040c040e1000c42820202c5016034441211402c41308540d614440b140d01e18401ca4410000100b40810f0200b2082c01540c08854008200803c07851580014480c1718024044c0d001c0075200c415451480d9506510010042061a040f0000210070b15000d5100c280440308110062542c49078406003040500c250380a00768464020f03d285d500b000002240782541594402c1081010440000001c089001410041c0114580c068a5911038500545c0d00e40240c076500b802940040080300150ba1441810318244031064414a00e42e001c07081d800d42840c4454845070030604441c0e030582c208480903484520310481c9000d0030040945c8400800d17880348901ca10303d400044943d440150107241003005061f03041c6060401926042160011401e5500030f09030b8040855 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 905228327 1250 905227077 905227091
    0xc010902040c090f09050a0f0f0e07080c06031f0b16060c03020a08040b090f19021e0618031e21090a09021606140919031d180a 56
    0xc1001c0c01100554000e504210f079031a41840d5012a0712007440c403640c814a0303240d5011039000d130465030040050382ea5010b0207000c0c00054809020240104600c0e80301c075842810f03000034001a0200710700c031050200805803442d540f1280d04070303080c2c941796024440c1703904c252640018182100310700408000c0e1508400407a640c81d6030514031308032140315039060281401000410380440d800080e0030b038001d1740400e12200b140c445045151034040d207600c00d42a11311903c1c525818031000c400d0454440c0c1e10803a030400418180d01200e508803800324880039008001448802e01c1c810030000c05407a4400e0140072a500e0071604403400c2c04003a0304145804607a008540410b2004400c03107900e40d54401980c02652411440602045465a041c0708440c6600e601089100718200c2800c2c0c0c128000b030700044248060501102d200c0c80c800300540e0b00e00318074816034112114003450340900b441095015120b00c485004caa41108030581c14042e2044e03403140d41c0c9200b5403420840c0350401c078041c11201c04001526 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 905229577 1250 905228327 905228329
    0x40e06070305070302040609030f05070513020c070b0405062a190b07031116050109021f021c050a0e030316050c040612050604062004150e060c0c060f0c030c010902 72
    0x20b0b14050565820103004000a000c1641c220385000c1c11692b0240b04246c160b001c034140300381071110f00d411455200e5000110591a07402c95009001000840d0043e01e18055841040112510403807181a03081441070054000c0743c0100301545c04452010b40ea60710100440f54141ca00b04100d05481c400301c110981b2007001031040d00100b80394000795a06040003c9125104045014007a16852008000c0c114011404000b401c3d0000300380c0980c0540008003003200030303081030742c40703040c007000100144910000b21030300001b001040c52850210b42ca426240c0030f4601000c032480702c030107902203030540b0003041708905c1c0344501220b5507205030060000d040e03903000c3d030320401058480e1607011603414010030448001188000c1000750300250710101c0002c40c5280381c80103171502281e0a4985107130600200c0c000070b0001c903103610074100d03a00503991400000110390401090b400740c01ca8807034691380000040c2c4030f2401c0c0070000384000021000c140e801e01010340c40062841d80000f1007452180d45880500f011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 905230827 1250 905229577 905229581
    0x90102031e040312050c0c01090507141801030209040201050f13091a1807090f0306020c060a050c031b0c010e011e02030910090303060b191101020c03091e040e060703 73
    0xc6150348a941c69039080c1034034020281015481d0341d402c0c080d42d0314041039456040000b00c880201c13604001b0b120825032410481d88582c1030303100c3c43c0c440340e8243d81e05501a18081c2001618200540441020b0307900350307000e016004200074822418440c0400c02014005a09030140446038064005e49080314107100403403080e5071811000292030300c1c0f0191001005d41e00c09640310b01c6488010f0545031a0303524400111014203a5a005502d0701212801c00700a004a030b07001018015144400c807461501d0b0038250034108c03032003201c03802413012050010400600e00c0c240007810b650344c0481050308248e00011040d007140d4104007a0800c582d5252018081c525a0046d0415040c49a01085003035150400c406501d0b09c5058007030201c8507985501c071004150107944828064071170700729459228500d02074102030201c01280314030f01082c0c40c6130700440864014001c551042413000c01031030800d08001c0c24441c81381c078003280da80248559840300340813580b583d00c0303518090852100107200364100040c010741 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 905232077 1250 905230827 905230861
    0x90f0a0b0d15050f040e01150308070b0f15010e040f02030a090204110702010e0108090a06061401120917071a07020a1208040308010501050723010f0b19031b030b09010203 75
    0x10b0040c403101d000f0000350b5201000044a9542624041000402020700c00d00620038201800a48010f80c2c90200c240009980984185446103210600f0b5840d002080340c05090100e0f1801d40003040d44168a116520a80e4100342244015101181c0030b442d11408209a0701f00f10b6600ca0480c0c1d507403490741c040d46018010740c0d06240291140515003001307500002c1c02091342d00f0b21039060100050102d0a0550b080088000c01d0750020420001e2903103d440b1000d1000d1401142c80c0001d211102e004260302c07491181d03c415907804805000c1880c5011081078154001007401e0b100781d0440c0f05251b00c181403410f00c40d403080907181d01802c0c0300308a900d402c504103141c00f040c90042198000420000a03008280b440c1521400d00301151140000e02e081c41118044c00c0c05003156151494440d00c4502e41500310001e0341124020501c8145103103424041d0040081c9070a030203040c5503074810808a0210055904504040c3c0088820103031a80c071803042403c426500c41009a5002003042002109032041d20b17 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 905233327 1250 905232077 905232101
    0x2106150905040908090d02130e15091606210609141f06030f0b0301150f08030f03011208090907180f0e1f0f06090503070602150408090f0a0b0d 63
    0x7001007a222041c4c10f0045c00c05850061100200b60019540c1e440720a0701d0608004030f040c405040009a40394449840b01c428684800c0710030f000c95040c40000c03c1610140403117100b507154603407034900102c9a003021750103038207680b2010440b003d4080401c3d005074000f07091600c80110300c000b480c41c140c03030b61044000c0013682c0c103612040e040305000400e84d440308112501407034049000c02001251700014003101104590541c41e2500070082a1881248e40c1c0c01c54101c0204640459907611440b034892164149104402a0400c01402244036243c1c402c0b007508d00800c0d030705007424040b00100b1800ea0b001d90f02440442c0c000440040c200c1240c00c0c8a101500d0040301c88024203280c800300300d0400302c01401d4104160080141c041c090411801140d005081d20740341c40316040e550f00704c003600c41c43c030b10700032680640504440401c0080c0001b460030006480c0c1561139489944a4440e01d0b03003900001314059102c00112000e80031560b41d011807601509843d40c4407961041030201c40b00031180005030382d07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 905234577 1250 905233327 905233331
    0x3110105090109031511070506090601050906130509030c1510090b060d0207020d200909070305060610090e161d01090909020d0503040b0307091e06210615090504 71
    0x103600141da100d0b085401300ca038012070b40b00384211841c120402401c940d082d540541207021840344203104001445500450a01c0d043d40c2881e622001807000400c0219241c40e04030a14140266042d5860382c401948284610162400c080d0b0854405040c00840c00d03051074548407400a12458000440f6244000c14031032108111084102c1c0c0801e51500030300440c03512055010803a130303055440d0f1001c1c0d11866903110401c1125880010f603c10740944250f2249805403058500103510014009101000d40c1c0c0c02c40700908607070b81c40d0360412500e400c40c42c80040800c4901200003441d42c0c103800c000c0d800350b0b40d1444540ca014100200041003480108007409044244006c08240c9903048003143d819a4000707040420018072a0001c15544910804002d026100c0000e0006d00c107010600078501841041d80c51410013a51400b0000f8103a40740d483c03080312180f02c03142c2007100340d00816803041d02510b0305003200003184e5440340741801c8030b81540c030040c00031000000141e0f4556201c00719401504041f101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 905235827 1250 905234577 905234587
    0x50d03030e120c06180c030a261e0913051014180f06010201090f1a010e100b030a0e0d110f0d0905040228050c010c0e03030a03050402150406020703110105 68
    0x41c3c40c0c0d0342801910000a0403004019015400c00c24081c400d6180000341c103d800703d03038091401c0f440300d60b01c40e03000d408000c41503174082c2d00d01d034410822200499004d40b0304012441034041c0c0e40b281c0b984040e5905034828000d501039001e01d4418001d143c440c00500d847e00642505d8104061014400b68100c00c0c400d16510209561104030864540c4c0c10070140c4068140c1665680c1c0140c1c01040d00401c0a030411141442035001c112101d44245880c0c89102860a41644c0c4c0b14980030702d22a081e81c0600003802c2e150010f0084000d0200034541c00b445d190004900c46401005660400304040f4003080010f5585509c000552000c2200020422350340005000e400045c6800508045207401224030881e00000c92405003c00400c4420710784161180ca4584058044400b90896006604441855003071150859071203004003001905c208014000d14074001c02c00400710000d00c80200102ea010400c01a4078407031205d0f107070140015208039001410319500318203142ea039210b80200700904100341004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 905237077 1250 905235827 905235847
    0x10f0f0b01080f04050c06070b10090212070e060702040e01093e030109060e1b100507151119080109150302060703020f030307090e07080601081501020304050d03030e12 74
    0x24554041003c511110054403035203800b9007000d03511015141d010501107000b0090160b5882d550303016401c803059400c052980e420b0140180c2c0501c0c42010080058000000c42c2140506401c00900da00206210701e41302c85603000404072141195a561140c1d0340320610400c002040e034410032100c0140c401882c2c1441c80304001015000482d468044940d0320301d07070040b420384007500250849039104805008014080140c5660b401d034404035090465001d00038003910b0f0a01080f070003100c0340b0b6595614030b070005648440b01c2ca510503141c81201c29a58802d040b071160311400241c0b9045184111041400c4e0005130014203a01301038021403940d178646403850008d402c02c040d1756411a503040e203040751682118141a4203000c1038080701a144c0c0000030410030b1682c1d10160060980e81c500103600082c3d02c464a04440709601281e11074007160362040401c89005008107002c1d0064814811640391580750004101101034004d000c034040380e01ca800ba0825800c05001103807914041405460130001911 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 905238327 1250 905237077 905237087
    0xb0906030d030209040b1e091023010539011a040903110d0503040b010617190908041404061a3f04142103060d14010f0f0b01 55
    0x40c18507000d0560008020743d554803560400041c0840003001451203118614844e510708030b5100c1c0c0380d441000d00000040c1c0c22507003c6c1c29607040d20f043d40300b200c0b103510280b0380d001a00b0500200140c10b0080500200c00001460080f2240c032040414244841c83c507c8600c0d0b0007044406461001186d0604201105401003594910103642c82201d01080c00da01c6410252851a0300782e032041818020b02010328185500300c00118042c0e03108030810300c4c03542c0e0f03202c3c4126900c00701c20300d03041184000e560109005a01a401103403800b0b0784190006016413140ea201c43c8a50f01903480044984900443c041d0b180c5071502c0790380c0081c03c2040d510440c0c3d605c110f0181c50700d4440d03403c2c00541c80c40c0e440b0211011204003000003c50300002d030707021b407901c1070f10484001555400b02c1c2c04849400f8040504078449101082c15904071604c410340340c04102800012034401d800c010007883d007016524142c00045200e00102c4d5041040101c000514114143c2007801139440003c02c41065608104400740725076408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 905239577 1250 905238327 905238343
    0x80f0c060f0307090e070806100c02180a020c03160501060f050136030819090614030405010b030a0f03120b01090902030a0e010c11010e0a0305040b0a090f06120b090603 74
    0x7090150b40e42e54241c01500c0311403440e04506002401c840400c80440d8200400600070803088a00000807070366100301b1a03001000000080d00b00091000d81b07418030080d82e130b02603003200142d0303400340c1010070f2160518616041640d01e80b002c1c0c06c01c01c00500506c0020310400004c1c01058040c06107441c20031002030070110081c96204031901000342a41c130081002d540b000d86d584a2610305001096490230071074407681000441040c03d0084041c02c01d043c0380030351302d48411900d0035101d540d90909503800c60015500010000e880035500c0d840c100c075440e80d0a20034114210302c218442e0096040c41d040040a4400c96560241e81d10301e00181d181c0642c1e0000d004504071252814090703074030b542e100c80039000341462114000440d800c20484040d2980c2200791036071082c031550000c2103601c0103015583e641719012040900854000c0200303000c07110000008041d009520300b0054011540d810038600314070040e40c0081c0004400d0101c50140d07250074040c2a0400c1022564140181440310011fa00d450b44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 905240827 1250 905239577 905239597
    0x807050d0602070f03030603020418050712080705010c0203030403110105010636030606090e060c03180a0515070f030b10080604110c0a020315040c0e072106080f0c06 73
    0x161410300c81004010340440f0b802c2584000b10700050043c925005c1d01819141c001284034030300300800050712900005801d00c1180d00310000300380d56031401444001881411800342c84081c0d0420001010338000d0142030301480c00356004651f2841e207810003c10444607000d90903e00d0b410900108a41caa00130f40c07021940811001c914210400d00e84001c1e40001980700c00120051030103400414880e45912650844540034801c2c1f000c00c0b1300c541515210007049418000c01d02050002c24043d49140070315410b02c2d40040110b0360300f5501500d54038a06600c01789040d01e001418010000309550044203030050324028202071007000c03000d400050b141144c840300b450820807000001440366485402649401c0661205203545061028145031900800300050b03000744034850320110202440c2000703903c2a034004e5448205a42090142044039001a11800c00c001d0540b401142c000a021a415217010311480000352062a100304c1500302110034020316420303007104021542d02e443c0c003400c850140134 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 905242077 1250 905240827 905240839
    0xe07080703111f080613020a02070b090612090a12031a0103150b04120506090c010804080715021b010c090b0d02090a080706020f100204140f01121a0a0906080705 71
    0xa40100810690046000d4407030f41600340d03911400b401034108613428000c150684580300030301c04101341c907000c4e88503c0d0401350040e4001c18040124800b05009045426401040d281c0380002080d001d60980350180d50340c10060b00b10100510030483d00c04041201828103080030f100b0039075000d40c45203241e640078007200c0c145525000301040c408008030b1284083c20300300c400c59444039150b4030980303e00100d950088403603115040105000c404000b520208802059640c4c0915503100c0c6d907080101e0300156021540c140c110002e00a0940460001d4020224488640d0004c0000c4080300b1342235a88a03143c00381405000d14050003040401d004458400c002c80794090303a107211180c0410291121030f8002c4c2074030b0050343c1c004601c2981c040f89591020110a08807411940034400340012440b07180310710003154001c3c0c0c941c0c82007402c000c2003a40116505042400f4002c090004440039102e4088032109a9000d14002c60003d1401c00081c502034010329404110060504440f545e90b101d0600803144070705 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 905243327 1250 905242077 905242103
    0x2060307030906140112031103120112030e0907030b24160317070c1b08030403030f0201140f06041a03060105121f020d051510080a0b03031605010e07080703 69
    0x403041d904240690520001041e0445d81d40c2c59140c40380074094542140040e6080384000304140c0000b0070b403040d86202d91400b50301646403080c03070040e01c0107a01044081c0540911403080a80d14501e60074416019518081905113501e02000b41c5482c00d03030f20001c20f030745031002d0980544e00e00b00c0590380390300c022001600700101181001c0c0c42d85400e4015018040c50740004004000d44d12900a0782c555125008411001809100311884101d6034000c0408a074024441000802e2090840307000c41d001c1d034000012034010f00310450419150407281030242c00010028003549090511824010b80400c820540042e03600c000000d44030030040c031a842c418414000a040b04002c140410449176040c0c0b120714859180010020020750008003070506c455107007100003009501482007503215058020440242041020015129104050f00c2540e485a440c0a860705581702080140340310214810800c8400215150185c01c0d107000e040b0301a00343e00500800c02618400041c0c81e0f0030f480d803100466041b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 905244577 1250 905243327 905243333
    0xe0f061203031f0617280e010f05070206152b050f12090919022106040b010c0b16051309150605040f060c02130c0c0c080106060e13020403020301050f190603020603070309 75
    0x20340994084c02441840c240f200c10a01d80158000480089075810a02c02b90742e400c1410b985619048804500d0f03040f034111200080d03e441c2d0f0000c0c007a0414005210800b0000c00310034204035295403802c5800b940aa220391604040800a090401a01c075202503d095001d0001c1440d010380900003c82e24103000144078004902c0c3e4041d1031210b482c0300c1c425200708a284410251402058480c00d0285140940c4c4007000c0d440358102255541d0450100c03041c90311601c000400e084c50001c049000c00105000c865094502c40d041580103005405004c55050b036262016084021540d20000c00e0080400042142d4502e4000b80740c11a402d504084034a16054004189111080c107403019500f4a01a11a20003540001c03c3e40d0007140507105460031b10fa110700e40780d0300326000c50103598040f034080e002c074201c5443d100c44200d90300c04c440c0f2070150416560394042801e4540550f10359540d40d40b0b600400030b000110224404940701891800e021051070b64021071440d21019040074105502c801c02c28080c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 905245827 1250 905244577 905244631
    0x30e150a1b05012d0c020a082703061810020a210b04020f030f0901090b1b070606060f081b0405010c02040b0909030c15010e0f061203031f0617 63
    0x4c01c00201e43d0807501c13014800203962400c2015108200802d2409031182e003102e20004d440001c203544100c3c1640380c10303203003028415001d0118440c890010803000c3d40c8241c0b0340b428044a4014010710740f990b00140700307908400e070814503100403107400c2900c144584138555601401a000740c1700108030700ca416154000d004070181242e1f0292680050000829040c4002c068000314070591522031010201c0c0c4030044501d0a8603185c070f8024005080d14000700320744900500000800303c2d10240d40303d141c5130141d6654820340d24154010004906000208040c06030804101c03540070405a039040c000b0849a02030381c48034090350040e58100059200c9490464469910000550f10006c012104915100d100e00340e44e0b07401440038801c94001c40358018407120300d820b00c250507104030855420315691441d490f454130001c002c14140e4001341500e640c00811000b44011070041500e0610003041170401880010990b002e42d1116082212000100000014011070700b030b04000f800c0a502d421042090346404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 905247077 1250 905245827 905245841
    0x30c0303041505120c0706060603180206090d050a05030901081b0d270b04020f04020918060402070819140a0e041d010c051e040602060a050603030d09030e150a1b0501 73
    0x4c0140501c0a20180c05800400780c4000e520030340c81803003019142d0700100e0545620010407804280d02a00b0317803005240c0000039200401020304040007884464480368904101442c00b99000d4000150325003a950f40b1040d2641d100c0c1c01c503000e100e9501d00f00480c014691240400e4050b089540300d000103003909458682c0c8002210200c0c4c90ba0500e191810911000308095808034411001d00303503003080e40c0c02c2038000c1d1541e03c040208100541403800b08070440001e4000c02899204d0740c200310f00000210361502514101c0f0035181050340e110840c85c1d01a200701402d0a00c5103015006125401d00b040d842028041c54980540d40070560441c804407250f000c80c1c410910380300a5003442891310201d40d03c00c0203008800d03007204814800d90b4101030f18002d0303480b541c001c0301b0042e0403e80c0019400c0440341c01880d00400060200d924005900041d28211596148201c00207416951b04040524002589120401c00f401c009440e01a003808058255160f0310201e004418032900c400003803240c20b41c0500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 905248327 1250 905247077 905247097
    0xd0e061908011809051f060302120f160503121303170a0206070c021c02010c0b071d040207050606090c0f040b0c0606092401030e07081e15040201030b040e011e0b030c0303041505 78
    0x185206112a580392f01e42c146021110140c1c07207800b011150000f01401c10404486000e40504600c0c03141c488203c0ca10392251074102d4001254000c008005291815280c3c0d010551541c015141c4016440003804c28078050001d00c20014140013034805a0b5840585a0742d40c6058504c8051410701880142c0700e1464201d40079240b213078503104101200d034005008070b001384101c81803010324030200b20800c8100d000b2004040d2482d407098000500d541486003243d134000008175401341c00c0c0201401003801d240e100c0e400400461501140d00800903200304002900407404880000040c0b0b0580404420503034890a20411410041c2c0707030721000c0e4040c1d44280c0c0d56a08150940714107a842d04100341d0780710071078050303500200744071100f0b1501102c001c1110900190a03102c4d04050fa2242e4004402511018110b81c0d400b6a031590303005103d0509114108021610580361071441d105802944100c40034081001e0007500000804aa2a40c0101c200c40c00d44014050484d151610180111543d002d400064 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 905249577 1250 905248327 905248339
    0x30403030f050f06150f0304120504031b0f27020313021e091f0b13180b0a08010902010903151b0c0b07030e0d0e061908011809051f060302 61
    0x403291a0f0086000d15100d95810b46008011100003108408a4899045040c0c0703141804e002182c00104101c0c03000c07240c00c0c80c9140c850b00b46502e9482d0f1a0711640030001c0e100240d07103442010000b551510950750020001803452825004c5560a00750302184005200c146013a80080044d042c0c0071040e801c9040c587e000340c000b8841c905038690f813005418203001054410050030b40092080751000c2e4102d13694403c15180da1a0b0a0300c1d0005440040e007105148203141b100d48907000c030f062616511040c6100480d0400070030060310220078450525000d0f003200c191641000380c8000544d807c0000342040b0399220000c610084540f80342c0e0001044520003040504608000e00032036940e2103807011894500a804044141e111031001ba0102d50030a02c03400d50640003501c140c1e4030716005076405003003044060101440e111503c1e16205400e801c0c014208082428000140680036001c1d1980680d0000840c0c2041524250340724660b0b100400054041580200e0300e0901707124035281c1000009550203411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 905250827 1250 905249577 905249581
    0x2100923010203190e10110f0a210b062a0a210503100303050901021606030617150117030c01061403011802100507030509130902090c09090a02030403030f05 69
    0x8034038042d60003034410500b9078501e0315010304545140e02c00c00071214126001800c120105005441c0a41140d00c1100861031050016110f001c845600a01840c101603681c254443e44002c0b40721704042d00b039440070745001d1070520300404e1900c2d240c0454160380d54072160710b0058520f00f20b50001d001c130781810303550060048003101c4080200119881074000e880213209952160000401c81e0507000442c1c550034910720059041012a00a00c01080e075070106106640880c1c603440c000429416a85c0c3c001070009030b980f00d04100703800014880410520302c01000e00b07050140c020319140420418028001074440454410340001c80410480390301401400091140f039940d5100490092300c54152103001c0d508000800c40403d8031500104d000c15401031908081c100c10600c03c03545034100c54070443c02c1c400100201174055503190003400c5030000900340860804094418414020070150501c044400c0a12041ea956a512400c084d80204032070740050300c81c0e03641d04045010f030115024803903500e440c1c881 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 905252077 1250 905250827 905250893
    0x7030b150f041805150103020304020118062f03040b0a1701061808010b01120506060c0f100c05040803090d110613032d0b06010309050f01060f06080106021009 70
    0x4040c2040310508009246904810b1041c0825544105d5113400403044402030f041c003942c00390f8061070b003060040c034141e03e443c1d140000141c81071440b5004500480d0b0203103401600c400c00e40c041c0081000c00058403c11403000700c0c010075603a0149005500c0f0080d40841c1c40d522143c4a0000e8100340601010b00e914556500da5024105a01c411509078103103031912000b00e01a0300c14050302c6400710041e900e085c80d0301c1c0c1038090340307000742006042c4a900540401c04001411000c001c0c040b203030302400c405803680d00b400030124800c40705801902c10a1000900c420080810040241e0343d64000c00d5814584d000c0700362908520300603900c000c580d0b0080b07000c250001030450140c03200d015a803244a48880504001100394031509460149240d0051498141400520007032103040d0840010704021801070940c0d0790b07150400d00c41d004c20f486940e56404040106002c0743c0b200d000100600d04040000b5410442d0003034079200680014406241c8035100d9101300b00c5c51072900b90105102c0300e40210346800780a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 905253327 1250 905252077 905252107
    0x4050702191515230402090301060902210708071103040f230411040501200706051207210911120c090603030a1e02070e0a09050d0903050607030b15 65
    0x1011294152800c001000c40c3c801000030f0b00c003950424074001c0e00301d00203084010114851500d120760415000d0280b085140c0b003d01800010b0a0641405071706d42201c01c04540284441c410300d000d400410728140032182e50401034003034116401d0715061b0f403000b284141042c51880f480d8800075800454480002c4c1c4400c100781407072000e500107013002d0852448041000190303004944c0b452000401040200050740c001c104801d82010720f024130011007000c1201040c248049548000003044000500d41690110402199808429420207a0801003007210780a4004168200402490340d80d4042c14148000040b003000e03440c500420b1303151600201410349480c0c54049807428021101100407c461740740101c10f84a0031001661016804104000c648000c0f007080410f810940c080d002c0c020822022503203c041c440c041701c807800308400c1010b00e801490840f51160b00c4003001100c1c0400d000040c0f0104445401994924021801000620014005a001030b80e00307048003800055034640480c0322 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 905254577 1250 905253327 905253353
    0x1022203030f17010b0705070302100203121e0109050903070b04081b01020f07030507020d0b04111314041425030501050702061009051e040c090e0f0304050405070219 73
    0x9940e4407114920302c4405a43c0b011000260352205420703940188902052503000c1c0201602440c00c0321001c50b641d03004100161280440500142c00c00290400071840d641d01a41e000040740454600000d400c010301c0140010600410704d80c43e494030045454880d00304244c4400c142c104414225508041c03501186550000d40c54141e00c510a00711101860b206200765400101007840c21740c6404190396003203c1940c080c4108903846001045004045802c0080c9584540d10800c1c80b01c1000c00342c902000200282c054443c10314900f071030802000070100b43e00f00d40c0c10071350007880b0340c3c000a03280e12005e0230b01600542c25030004180d000e40f411140d00100e2070801700c0b4000c00c000c2200d07440d0060708986401c2c08492200022409090421100e41182e004070343c070620070080030761405c003090506025100c0c103450598066415460074802400c10f07120302407100c2c0034070006104c0040a0b5000d1038070f81c0990b100707462042c2d66580008207040c0c006c1c44070070252600c0009440700d421080c5880d5001c0307050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 905255827 1250 905254577 905254583
    0x60c020703030e18060d06150608091b060a030b040617100e0601030c06180b03041208090601061b06020903120304030906050901270312020705090a05010b160501022203 74
    0x1030324410f003168104035031110301080b078844542820740d0351351003400800c0c4040402281c3c42d6594421001d41086502a2140902800e0781c4003042403c0000384580f60a1009008454080250391045940d03614841110551015401c012440c0c144402c0028014404c591014200ca11070100c12102d541d00880c2a00000200b040b04000100710003488a0317564009000c020002c4d0b0031482c041c080d03a401180e601041c000c0401e0443e00045c1c4a048481c1d040d00140c2d0100d13120b43e100b0100c001d01d140c01611403135110b402d1000904040d03142000050031041c010b8034516503840703a80e544d8000d014190301243c42c00c0c1d00160444120f1540303041038030920342c0101d400307a0000e001d01d400030607801e11880c11601242c03416912440585034041c4180b41d040f000d40c00052584401c2d007400400200010700101d5601c02c150007414401c1d2800d428061003090081034400700b1494200140305030f4252034203448048060981e210324800d298948140203106600d076403040b602244d0f042006140030380c08054150f900c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 905257077 1250 905255827 905255837
    0x6090705012f210d0e07290c1920010e01050f0906071a0109060506030708060415240203030405030f070c030b0c040317270f0909010203071107150305070507060c02070303 75
    0x80f15410b05170300d40d072060003160030081c0a10002d104410408100c85902c0313803114003040c83c1554405449103010360788620010b09140c10240101030028041024109015006102070b0ae5002200024102c030a01e0482c0b81c103000d004255130f081c0400403004e403080160064226656410b190401c0c54031b8659030160040034415040010580b001d99004030400c445020341240e085407686801134452050040c08103401c503a4440a1000c0800c0c0b4016400040006084440e4040600c1c4001119404c0507030700203040d58820414000010400001c44914184e0170104684556091403c144400d450b548003400c000302102c14840710000074401482200e00c0b5246003030091080d0310704000e440c040d00c1829039200b00d508441c9940b0490280340c02014110007000803241480c0b071800200b0140042d900d01190369400700c00c1009894102104650509041004114403840e004540d00c883c02007407031400400d034540340400c20480c00b0790152420103a00c00710a0000c0c0c0c01460000359980790724070083e40021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 905258327 1250 905257077 905257091
    0xe0606030f0a050a020105030c070506190510031e23100b0f22020c0a03050c010506010503091b010c1509050d030203100e09160806090705012f210d 65
    0x280000e4000d00b9a6100018043c40e0100e81c00640b000e8000914822030701ea8104918400518240040b81c03060705285452541051092100012680000c1c014440c20469240903c00718446030b04d000d004a40c0b0802c209400506890440620000c1c40728070401c0c0c003800d501200c40c8140100e05040741d03840da02c0c420071080100708104007120420528041d0088419103490f0385140d2604030102e025000104098500100040c0d410702d007140000c0140c00285000c90030300c80004080c09a29009030702443c0403821f40c14810040c0ba00c070007140c030b6040b2000d030b55502d401100340d00071024201655003283d801d03140c0c0d1a001030180081c1014810071035030781c060344290608141c000d10075a1b00805d0030741d5030301d0001c0d41028034000f0300c4c5401400c07040f070307074400c40c240c4241c0d03c03500000c0c59000d010490080d02d00750070441d0320580f4040e03442d080107040c800403051a2280010604416941c50424145108031480e611441d600309005000c4030b45508104003544080600500020507500017540c41c100b02a13 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 905259577 1250 905258327 905258353
    0x120a060e01080616050412080c0109150b0906120c0d060b0303070312200d02070318150f0503060105090121050a0b01090f0f05090402060c070f03060f090209280e060603 74
    0x35102e54000d21060715287c0202c50049059440076100074034601000058a1089407111140d044d885601c403481c543c1c403075480d48100d007440d40556820080950789050040c4030f00c5605a2a00314418178580900030358110281409141d41240b80c9080015090341c0c0e580c0424100181381c0003004003581c0c1c40d2420000416580014000e05000d5106c81a805070305156140e413050000c3d41c4810400d0301080b204034005080c4103404280c400042441035090104480e200c3ca014254095420903001442410300802505036006011142100030920b0f0181d4010085170013030b680e1a0b0410190f02d5618a05070801c505450140c2c403000e0160b00c241c80300002c89658040d141440e40c00760041c2541c1801000c401c00a90402240d066006480107204038146002500001e180140640c0a080340c0b201112080040c04080d104003400d0340c51122041c40303445003640225103c003001804202504250300c600c0d418812030742061000701c0c0154030081c88102914a0441c0d601ca00c01c1c0c540d06c1c442c0c083d1060900c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 905260827 1250 905259577 905259587
    0x3030403210801050d0c03031103040f24020601030819171f050d02031f0e0d080f01050a050f0d03031b09051002070303080a0506030c1f030f11120a060e01080616 71
    0x48180d0010092107207c0c2956000c64000c00340c40303104002e910040c000454080c0c995590100500408010143e2640805031201c003c58004910541590800300050022031706880840b550200c551000755980032000c041140e500368405920364030001d1802c00e205140d002981500b407002203604985070b0003601c50b0100001d100c48800300a50550025030071a050b8907190314540c0f610187ca403070002d0304c00054401942004518015040020709407000c00c0000b69162031720901500055075600c0d4811308100220311001c42c5403220030302c00c84103101d0f03120426109420040140c440320f01ea800b00409040c030041e240c0a807900450748a20b4030051141d111a10014200c0e0450b50149d44034182c9468140e40c40e0010807018203115018010028101c0c1c540d1074200000300544070042c5010441101c0a40c01422143c1c1c1d0b0410151313090a03d5051000322281c042610180040c2c0182941c0c80e8441142c1c0d60002c0289074048007010070814000aa12a40800c890b4441c460300301c019003195484e404210b41c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 905262077 1250 905260827 905260849
    0x6061e0e030d0309260a02010e07031e0606051302120a090308041b0801020a0f1d010203042c0405030405030d0c0203150a38010e090408090303040321080105 69
    0xd0168010002c04041c94841c0d08401c081c01d015021442c200340705070f04001408511155160b10440000071026440c60342441100c40c4034015001500038141981c4c1c42c800d0800b89028204451021510035900740a00e9130b00400050000410b02c030030741084c400301c0d40b02940004c100e98401040341000510000030710f0043c2816554159a65070182e640c07503946071070000e20346071410002014600c0209030000c0910080155004030303125071140e503c00c01c1c001488040c086150080d0485064120300b503598000007aa030a881c080000844441078041d41001c41c80000484081c4802c0e5110a0006200703012005009640045e02a10020400760800340c4d07a0f6215014003d401d5440782d40002c2281124403103a5030010005200866501e01101d10b90703031100d1100700f44225002240344101c2c01d8000348800c121450f442130030486407582c1d4480c006a1042401400500700041c00140c480042c2c0d0107108440146078004481c1c03c41a00d0404010800485044800d01080442740045034900d04010310300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 905263327 1250 905262077 905262079
    0x11401021506151312060f050106020f06010603020306060c011409070e090c01030b1c0308101d06040b03010e0703030e180f1503010b0d08031b03010e0a0c0e0406061e0e 74
    0x3282c0c55096407490000c0760704c0502c0042e0300740122803000c50702c106607140d0742d481c8034003851011410300d20751030362030341201c1041e030040c01954010711006c000c0030408110181110381d5824016103c0d9500d20111382248030303c60000146519058401d022102e00750003403401120b0390380440d1b082075100e80c60083d161105568680240e07014480d10716030303988641c0101807901000350001c000c1c036007008540511000007480c100c01164170700c0708000e08500140da601004002005071020300d0194013156120003032014001c240125107807030907203006440c250010103000d5024412107880e680e50b030400605500d0b030304071164400c01125000d000d880d880c045030980540001d9900c0003103500e80c1d5076000d01c60402800b500e9055500c6050464080c0d881c4080074103020702440c051541c1c2c0c0790814540420003414418014200000d200500c421800c5000300c5a0142126500145031000c855003a034011400d4140340381d002d400c043c40420895801101020801540d901300c2030080c485103002e82e80034105182503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 905264577 1250 905263327 905263339
    0x5060603010e1023090109120503100504051b0703091505040f050402090a08070605070b060907080403050d090611180337080d0e0d0c03020a061e05011401021506 71
    0x122110003c0e50042c64280c0700006900c0c104d40c0d2640e060040c03400d0440b0300110907551042e0140910401c802580400e50702c51400d5480c501d03046505250354095401418059680c41000410340b40c40f00b00d00143c90546040c0803a11b43d03041e0310740100034503100d0080d040c1a4001054411000b03004006542c2036507110840405580c4c00d0100380b200a403c0f2842180e032080380c103080011400703000e12020000c2c0c2900c0d82d4040e922951824807848106002d0842801045040708101c0d90b1030303203ca48250401d900d45851380c2da0f9411080da0740064021800f010f0401860200031280d06007900d0300070100d0005107000b400d600c2c410b4104040d10381e1491100740d400f040c40c20391810001000762030400c403250003542c0c41d02c403d0b0f0b0142c0c880140c1d41d00000003160000d591101a80d0340c1900c00c1140061203401c0e0328000507200780c295030081d02d54100c14801007040341c072a4940c9040b90501520162902001c01c8100040d682d141d8a821503481c90b111540e01602480c3ca0303540b0002c1e46e450b6550300c135800181078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 905265827 1250 905264577 905264593
    0x5180a020112021c0c08060f010512060d0f050f0606121b122503110d0c140609030d020d080a0b0d02131e06050a240309051606050705060603010e 64
    0xe0700c0007070340c4202c144460a01d8084c44030306a03103001e40300e041000c114550755075446103003250a00041941c540320342030603c0030501041c2d481c03041240007541c2c450000e5440d010640e01030314084940c44280140100940900d0b074039914a45400079245205000845103c00b10b128070f0b0220301e4981c9507004941d00e00302c8074200b00390020300f0036001442e00c4141810031210304103000e9100b00b088482c03a074079480c110219840c08200b0700840b10340240f003500b812240011080159a11900f40c1c00c00b40c840c815600703600d141204015641c0e0400c2d01c8861001406880782c458043d540292500303a84510b2a0110f1070850204190749290b11072008080c00180846601d208150208404601c10280e2420780d80d0305d580022401c45008a1603401182081c0404204581040d0030031140c144d00e0340011100c60361090015440e22031850484a28015038100001c405040d0304200d070800c14080e02542000e07051480019410b48c0c0711006203c081c0c01030080e50b5058035074100309801d0f541030000a154540c010b00c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 905267077 1250 905265827 905265857
    0xe071209020a05040c08090d030204060c030837050c16020909030c070e150114030105120106050303040621092f0411040e1006081501020c0303030a05180a0201 70
    0x11003440e059000a118514a903659800501039501c41c186000004500ca000e0185079901084a0b1045007440e080550601e400c0800080c000840e50001504005018010410080e07c3d841c00440025981e407006942448500d020317440e4042100241022903d0030340051203c001c0ca006880141450b0020b0110300c20f200e8007080f20912018003a1100e5000800902083c0c00d003c000c42001004010a241d08034500210380c10b603440301c0d0f030300344505200c0c82444003074945044404480c15100122040b10b440c40007079800a0050605800c216050304c000074000c030b03c0035040f0300b001500344540030101000c802c04c80d0100066542d801d0000b0034803001130794886001010304428034032240e8040100c2c154074031030030002010b48103012601c0f40103882c0000e090103c0349a80f601c4070380c0700080342d0400c40c106103000c8009064280003000c021912101d1242441246e10901840d040300300d004040303945034105041d02d10300620051740c2240c8201c582d079115000350f80c0b021501d10309198058445004185180c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 905268327 1250 905267077 905267081
    0x803131a09010c020f06011503090f02030d09050f0423061c030c03080f160509150f0c0622060b010c020306160305100b0f0c0a1401150e0712 62
    0x10404680c10301050620315110160000110311490416001280c10000050080d05080400019440170b41002c0d0050010101407906142029454540041c55000608000b0f07201012100f0003985801a80a01c41d002e907841009442650310855000c0300e0072120404000817120856141611400006451210207070f510200651021010340300450440f0000003c4240c1040d200e03003103001c5000400002c1c2410b902c08801070780a03907800d036407001b281031890780d03140080304000401c0c082200004801446842c0e00040d88a003e000c41d40031a1a60500c008407085a00b0021000b50144240400510041c038114032140d20601030b55220b0108080b0f5499000c0034102d81c041d0755060224603501c41c401610b0410003644190540b000340301c13054405800040941310081d0410342012010301c014044640308030201d03204030706414907140c0d840103144c0a560801e480f01c42e000d8142c207403e107035102492906402c0300c00380c62480c415000d107a03510343d4010b982100d416030f201800504040d0303c0c02110344031070b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 905269577 1250 905268327 905268361
    0x30506041820010c0807050a030210020301030f02360610090f09020d2904060801110f030406240611120d1509110a03050603060103020102032506090b01030209130803 73
    0x113142c040c0c0100320b15145c480c060360101100f181c072684940c1c0203005055042c03000e40c040c074040c90025840d551558031512030303070131107008082d10644400c1d0703644051960800380745003103421856454030b042c40014091041c2c0f1004841c851301136100300300c4005025119003207035000d0b40c1601c189100014100740d40c000007900022030403d800c903901c02110b07080c8e9001403001319200001810380c00d5101d03540c0c001c0c041a2201a40051403a0303042150310744101001c407081e00c0c8024110080941c4a0742d580c1040c1010b0100501c0036100d1003421015641c48400d022002401e41e055500c0707440d103c05401c11490350700d00c0f11006d215110034080c0314481681605802040740100c114041e86281525902c1c080308458000e01805031420000819694440d0103010b01075000030124040d080c907600d140c0001c1d440b80702d40d051031002031016103c01c41e09608a41e0f521611207420050402444040c0d250800c0207550a0005070b1244590000140e2658014041e4807040da510000480c1140c84003a807484020150b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 905270827 1250 905269577 905269579
    0x102120f0a2406030b1509060705070f0308030103050609150c090303091503060a090204051f11070603020304110418060203090a0f0b0a0525210c030506041820 70
    0xb80c06100c403403a04094040100c880300648074419603480c144001d011900900300517402030780c0d1030001ca140c00340c9030401e562040030b00352062560341a0903e40181450300c150020b040341c0155200203c04d0003450406541030300e120310100e819544030303a5041c950f145194011020305500e1403000030940207541010307140700316019044038241207040d00004c08582e4083d1110400c0c5c40c0102c05c0110a141c808040342c01000051404c40c50641800085850034907911441e0061002507907110400522a400745c45803404460141c402580d107940b00100030703500581d01601c1310390002c0350300d051358602407180403150000340324030700f045a0042e50f5500103500004e01190323840c091450711703101080c56500310426040c0b080640c11454035020101c0e108a5034098401d640d00c0b215134280d1096070515801005074801c0038103140f411001e0104c0c10010081c881121155014106800100b007582c15412580c060401224140960300c07064540d800160704030034000d09058000e00201d01d040a49602081600310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 905272077 1250 905270827 905270831
    0x601050c0d0c14010f0b040f0b0f09040f0804090f06050a06080f09010e10090b090303060a0e0901091a06010f0f050d050a150605070309051f0318020306091e0102120f0a 74
    0x103480868903086903460941c0884050b251b0607030600903e05841050a85ca4110000704521503c600104001d1324a071000940594807801c00f00303043c8030002400d0b21140d903000c41c841e95925291520403016080420078800d016082050110303861401c12085001c2d00d1442d59480826940c108043d4000d02c0082c10f0900c0a550f941030503080300005010780d0404041400010468582c1d03440c02c0301c0d050300010000303081504180f00f0701c0340300d64034507022204803090603010b0f80f41038582c12151030040196020051500e0305075800311490320381002c60940300720001d895892041c0c4400c00d090b2446105500003a00185042280600768156540080c1d041030803004001000e4020b02c121001005058000303001040303012402c0340805070b000090101810083c0e407907120300000c441c00c21024035943c148960516440d00b044450740301c8407074001251b194000341107414a0074022003041c1c6035520081401c80040c0d4102c080c1442d0344050007154120b0800180705603c030f55a0a000741c10102028001c403680b55 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 905273327 1250 905272077 905272103
    0x80a08070e030f030a0914030d120b0d1a0703090305033607031b0b04120807021e12010207080d050718140f0d0c1503061a030901050601050c0d0c 64
    0x6103003003144004403e0702d880215a14860040e02500b07080c0c0941c480c07000040140c0060805850200d145041c003030b410305011001610901580c005880305182da16002010201c5c40401d00000303060807411105a46840c0d48207072a8290304034165136900e0000340202d44100041107043c1070003090b58000114840070342409810341076003020b529050445209251740a00c1013030040c441004950300c0c000020b070055005480c605002d20b560307802684500100702111083d02c00620400c2822110307000d600800c0000d035032030f040e210b42c00d520444140681c0200340701b0b084030710401014802c407100d05402000ca01d0074029060b80304000340400400e00c1c0304001880c2c4488240d0880c10b0991000b90840b82c0345040242000d07024081c03114075101070944203000c00300340070010410310701c2100300703030b0751404042c2d8940d2008000540290540754880343c100c040b4031090404200198025600a20b0795034002c0c0800e484800044070a4000c40690b880b56402150005060034040c0c00c10100d81d5215800c40c110b46 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 905274577 1250 905273327 905273329
    0x302010e0d0c08150f01061e090b131539050610031707080304200d0b0603100b030304270c0e030606041506030504021302220e04080a08070e 62
    0x2c0056030344032007404da100d11a1910310344100d80445a01110b00b807002c074020b42c504a8001e121441c06c540196160040a2180d40310902c20301545c0e016248154500b036880f0002e240d04504640c96104043c00488440001100c061140082d00c0403a610364000000d40004040e4100f8207002c102a90000e490702c8441003030005a007881580d00c103000c2c0b05003000c0010b180d0302303240b800516415412032840300f0400c800e0300000c1250301640e070425000104240300401884600a080000c4a001030740071420013481070030400003403030b00c0e48600c4082d01501c5507880704903065000d070b81c5a800d00e154550800d00060200c0d000000b120064150182c0d9610904844451080100c64401e050140066418240f143d45420104a0203410002c25501044440070a035079801510f44140902c504143d220700c0803d06668a030568030f004071a844c40d0440da03800c201c40c400280900500308030303d000e510030b100000c1d0000f107000181d440342e50041d049524100b0171002c00c45400000510075014841c0b41c008103402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 905275827 1250 905274577 905274593
    0x1080c041e0606091712120a060e130519020d0b09010b041523031911090708071e0804020103090f120e1201050105030c06130b0309010501060f050705070302010e0d 72
    0x91143c1c0d1590f80000b41003500e840001c1c02a04111001c0d644510703064400d10540600300e9201c07068004501304503460340300900c0701802d600d038400c00c03028840d001845401e40c00c42c6c0b1045200d6109004860010840842000320008109000b0358481000890140031442c3d246225a010042c04000124208000005000c0f43c030002502003035401e4a0b50180203d12103501840454400e20003103201c00300f10b68001a690718900b0130501441d445501003042003000e880c608200c008001007000c4082c0c034001c1001021400120b80c0e280c0008c1c0b0070100c40160b4034600382c21080c803030455035801c015a99290019000703044050000c0342d0000c0040d0007038021511002010502d0f010741da8844560145070070400c504100a003c44042c0c503494007004104d113640009482c015204291001c0391146205c1240040e00c2007154002803043c0b600104001440506510160681c0c1407501c403944d1031030160350220b6203402840002000b662084038240007540c051159090f844000070102403000a95a41d10301c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 905277077 1250 905275827 905275829
    0x1051c050403030b0a14090105130908030f060a1e031b030816020901052b110319021906200f070e01090b0904020607060c09050a0b030709080601080c041e06 69
    0xb00181d070b00c0801044510f8180e40000090030000d005405840080b0f00003007500b2410300c00d00344211f840700003240c0601c140e908054070254110b07100030344a281c940da40007082441200c11a100e54100c0b1004500040108008071801403a4440202c05600b565151044001d001b01c0540004543c4200000040d01d0310b0014002000c1002ea8250305403080d01c1405808035040c0c00481c030035482009a0803241e03860354022204184040040f10078001070f0300304401c85407000740c0e429805026a42c0e46040c0007500304007082d4428420b0b194801003e8040400000e100500e0107060f001501031600c0b8129808845d010780703011401c080c1503851006c410f41070f141c504500c0d40c3c4040c03481e04140c40108203040c0148141100c05c441500c40c5442d9141c0b50740011143c1c0f180c0c070030040010f41d64141602840344605000409004050440700100b6142c10085040350001c84054001440e0183c3c0031550040c0814414100c1e00520000c00c0102d001c03204000160881031403c86198060400100200c619130041c0700c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 905278327 1250 905277077 905277083
    0x5100b0f1e1b0705060c0c010503040f02091305060903031015270f051f140903060106030204050f1f12020d0c051909030b010311031f020a0f1d01051c0504 68
    0xa280c96a20602c0581040c0c0641d1000d0302c03814050000e040f00800c0402d5907070303042c0b00910f00b41e42e6a669924148600c8802100f0280d003184002003000b200b610141c02d00c6a1303c501540c21a44150f5544065981e02d1008403810307000848414007c100c03401d00008034080c000333000d050110700039440080c0e05000c4000d0540e0a800300703406003010041c00b40307003000030b0000c1c01080d203599509546d403c010545a500040c1803104101010440e0b1a0091000042e22081c01d00241900d5042d40d488000601035007050091500c40c1440f41400d10a500e424030b0081c0001c45140804001e683e031420f0700361003d4039103a07000c41445808204103020f040360b9100b01d4043c4e018540f01c0c1610b92210b4003250190f1500e892408051000707649040c80420344090b43d0904483c0e025554001030034000d000b003030034808400a44044840c40e030450748a8044242c0140400c00002d5031100e0f0201d004010850348078400450342d03060a250800c210707035a540300303000812400880c00c01e000000c1c1c0e480508042100d008880075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 905279577 1250 905278327 905278357
    0xd09080316020303061f1110050717090705100c05012306060705031206010c0210031a041104092a0f0f050f0318070909080d05100b0f1e 60
    0x2840e81600741520040304491000314190300d004404610780303065200b00c0300c422410100300c0c1e5285034440c0050400c05c54410042d01d00d18a1080b40e0480901410754003d8041882d0307044480d6a0020140030314410a80304c0010440c0c949080c0a00c0320440100680c05c0800c5241c25019021450034054903042a006020707044540b448128000d400300d0b00a4a00340c03280d00104240c40100b80000180e910b8035000320301030080d5485d031100581d0030602ca01c200941000c0302d4030160000981691050702440d480350f03040300b0384450b40d50400c000c4544c45d50071000105020b000a0004140036440010700c1d00002200103c80861110304000c2c0c2c60854070181c0000e9449000a13420541c0201402c540011034100641841915550b40d01c1c80d000061540c803240342c074101c8a14003a081040282c004041030402089a80a107017454126941308800381e40e4168180804a1002d08011802008544075200700c942400600c1c071016004d039100214084010010708040041e44480c240148541c1e50507100f9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 905280827 1250 905279577 905279581
    0x80711042018010c020a06111603141c02032a030f030a0c0503040b010b2a1b06090303040e0406060e160315050907122012010f120b040501020d090803 66
    0x4000c2e000104191240c1000748090610700144c4911003882d083e691107040001c5071408481d2814a440b400700c0840080f500e4a42001042c44035004a5000520481c1c0c00d0b40c0c1307250300800c140d0024070010150a00183d1080110081031085002180c1c0552010402c80c3c003019140001146150042d0411500c0890f00006012030655544a43d107841003540c145030b030840c940798541c3cbe9001c220510400c1d80420000901030700305426011203000b20a50b01c542c1040c2c42e1140d501080c0d49800722008030340201703081c1c1da09256615000f000e41d4840e5100400451034039080c519050310304007001d07000300e03242900c541000c54443c00180c940c0b4403520301c01ca0481c138800040329005058503807130590454607416400d0280095202c103030f1110350000443c02d28403500e0703980c42150710060103a0822600480c1c58040255035070031101d0300414500700b425000400300d988a4181c2440c6450900c51028810421a0603500050720101c40303541c0640103000050400294509142c04d07601c0e0480c1c00c035044600041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 905282077 1250 905280827 905280847
    0x20d060302060d060f090e1506031005090f070b0408060610110109110a090b0d030e011101110310080318010c0c120c08060c040b18030c12060415090807110420 70
    0x6405c0d0000d044800051020110060b141520b502d80700d406001c90608400c00540140c42c204040701c00d10701110360401080c41e2400013180c640700310340381c0d81c2d105018032440080c410310100180c03816a83c142001d40300a4a43c281005803c004003215201030000c4a28900740000c028480e0650850040e0303410f00c684d010110410407d6255034200c80a11494007800d04140c0e11805102141030760726040110013a1411001681c0702c090707103694005151300f4942e00448000500014600503404180001d801035141c0c1c80040c3c6034010b25400400440312400c03440318561048038410907040c041d455441025442704045141c001904105840d10782c0d80da01c003041181c40070440307640d0105040010600700f904100390080103105004007500c40004030301c0c05074015607040c080b80e00781820040144144d010828012030312400121401d0b58080940803a00340e03c011a40501b10031180c0c04400545440b47c1c680d034540400d1410001d494019a4428041800e100800500810560700da6501741c0c031104003003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 905283327 1250 905282077 905282099
    0x6090604020a021f02040f12060b0603071d0103020d02030a020a1409060d0e12071410050105180703060e13050c061204081b0a0309170f060a020d060302060d06 70
    0x2a18460145104202a05034141d01041c02d81c804c2e00d0f4050454540e1800f0150f4401901aa8122800303803a00c3c0c000c0041e0003070500750210042445804140b246418010802205000480f41c08002c150101040c2801802480d0000749c6038505040050400ca81200c40310200e0b00308483da42009a400034a00c4411504403280d44800038201c80308514041c9007002181060142c25160766107152520740300003010805002802088a49078030254680c03040f4103094070b074038400c001a00341d107001d00389045084541c28013606041c0d4038041d11440540f000d05c60322150402000700301c2e0301010f65802c0003007074440300b400806001d403d1403800800d66003954140030b401c000c0300d030180c45d20038441008890006141004216845500200c006449404904141000b40c00d0030280365100d02030b2101795400c00d5001120041038840c03821024000382e24140c0703825541c80118a20203040c0d03000000051800c80603030000d2004844074040401c100e030356940801d03030780c0e0407840140f0016038580105100300703e188 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 905284577 1250 905283327 905283331
    0x70f08030103241b030b04021605010606080115090302060708070b010b09040c0905030c041d030d02340b07030605090103060e010e06040305040b03040303180f11010e0f19030803010305060609 84
    0x24604200003070b4407201148000088403800c0c13007410389034141e1440c0b5568a60540d8941050780b0074a90750b4030f00a152082c0240428041d44020881c20744c0042011a034a4031b0203164852113880300c00301c0c0c0b41550200b104a40080c0004c0304d00c1c000070042c0000040f0403042082c000e140302d40149840b4145041004243c600007503d41c0e00700080b50004011a0340d0009800d0361150013510009054065011500745030070440030185c0c5144000101303030321800c02d01d42c02000d004140714108540ba81d2100c00d071500c0840a4240c4bd011b10a0440c054004980301c070030250341144c40c80c14002800c96503080424810304090784107a512aaa0b9404036040300002c0c0580440d41030010040c100501d402d0790090003c0c01140101c4c14084000b00001c0c080500a80c00412a8003800c0101d1940c04c0c5646002c001c04d15120340704a800382942421004a54001d080c404c01c0c81c1d10003403008032100b640200b402415001c10282e03001d8040c03006400004550024002d45c0a580901c01502e01813030032a081c483c3c80400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 905285827 1250 905284577 905284643
    0x1427130b01030e0a0302070308090301021e1c050402030a0b06040b03010e0c030f0c0a06030222090b01141e1810050c07050303040e1f180c12020403020f06070f08030103 74
    0x401320700da800080e40451540306132070b800200652289a0440881e00a000303040c4103603405031424030020f800f81d1100f400b400e0180440800e85403030440c0d8848080640d001624001d41640c40080214000341030000c40c1503000001400005041501300d0020b820340301114144c100307035001a031429240d41001d20070111031600f0349000f013045a0090020400113150b51103203c04050340402c0d100c410341503c1d810b0550914000c1044800991203986800050829004190100d8507803014100e22810301c0f0180c5004400c0e6113160340040000300e1961416910501c030140d4041002c04182605940d0401958590005642d03040c1d1980c5a624295290406682210b807003640140401c200c040f01e0b4109035a0303c0400749121113030f03901420000d554406e526400c65250065441c0058043d115594001610b1025603640c03d03440b981202c00f030700704911540c00040c0d0130415520f40440681443d400038034407548140000c8080702e801c1d48030f101441d042030308112500b05d0144641e80c00c1041001602c403101300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 905287077 1250 905285827 905285833
    0xc060513050d240603020d030809010e0c032d01021206130207080a0e040e1c120501080705090c1b030a0e0103051005010e06130306060501020601061427130b01030e 72
    0x4030b25103031450b080200340c03440184090002e1084a014101381c010358000e50b03016200079125070309440c1c041d001d42d02c101d9071802c0325071824000c070b100c1c1000042c0514200402601901425046030b05030000184108200c8908511044000020354006d2006040c0b00088401c00c091504054082111250b0180b08000303203070b80140172810100350088222900060030741841d40c6050042c0f00854003420384c5c40d0781e00045005022403c0d20300d411042042c101d02d4004e40d5040000c10038407a00c541283c50a01a082955000460622860030900c54a6030040d41000701c076401c00d16114847d0b014a81d15440180700c982001c01c0b0985d0180d0441c6400c1d0241109080902261070300f5140040610001c0c442c042c10840090800d41c40c41d21030303104441040441c104401314994903400c014004e803095210300307401481282d00015450340b040d03102c4122000e03810040d03031821600c4a402e41c5150341b01480010b031440b12001c05a6543e449003060154040420404207145140c04005011030741402c8400c0d2240e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 905288327 1250 905287077 905287099
    0xa170304110108161b140c0301050702011a040e010608031902070603050106120b13020c0c0a0b0f1c150306150b040b04030201110f030c0a0510060b030a0203070c0c06051305 76
    0x1c0c0030601100d0291841c6402c05d921050407510740800624424090021022100040c1001501103a0300e00084c3c016002807105071901d60080307080b9006004141418810901d001c0c019103415082440e120020b07100128049032a000c58070706560101d0402031600403003c01000d90560140304032001010907007000c0001d0b624040016005440c0c284412027503a03600e52840e8003950710b00046d0b080703080364031078110744035010940826911031804c0e0b601d03446131031100f0001401c071641400301c2d115030a640c03001c0c82c109100300000381c040704800a5500650b40d160306024003490880d0010000940c0900310210380c000c1e021a200007540010303008100003010400050180c0202c0e10200d40442c0c4c2c6c2860a00d048034076210a05003049620410001c00707000000708080924400103952000074003440640304041d40c100d0045044941a108100d596901030002a4040c40617034059580044d0a090942d10418a5500c150680d6101c0e04281c002c02c0c0c000c00c0c0301d03212044001002c000b41000340c1d43c2ca8020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 905289577 1250 905288327 905288341
    0x206070206220204151d0f0c0708030915250c030203040b1c1803090b39070305010e070803091c0804080a030207050103050a0212180a170304110108 65
    0x54040034440b41000740c0800c0340d800464960350700c424240c4041c58038032010039807141da12881e003c41400c5c02030305012a00002c40e900c40c0c9210004d5002e4440440064540b2076503a031003202980004001c0c1e05280200c402c0c40d5417000707020011030302c1034003841d40401a4480d514076000c400e01411b50000d0410004442c00740000780c0010450781501c203d048202e40360300c484005801e001d00503c0e45040e5860902240003d00802c1e4040c5002d16886600e0b0407030320a8440b50b41c80d01c030f401803e034001511508112030b261444000e0049140300700303244420341c90041072517040c0c9180c40602d03403046030160b41d1100078607260042846041c0160007564040c515218200c80091100c0611640c1030803000384140c0210100122117048a006001741c00594580c4401030a020752601d43c680f06060101e401c12000410507030031403080b6002c1000b10840c015a41d110a1071880002c16001071001c0c80c0d01c501c400e038002003903500281c82060000e02c4c10307156980c038040c40c1042d69070a03035040003418002c01005003c11 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 905290827 1250 905289577 905289601
    0x20a0e0120121c02160507051e09040f051606201c020a020a0311090105012d021f061e15030b0102030405040c0f030b0a140409050102040819030206070206 68
    0x9140b8140041d80c554101480b00c0c0040500d40407000c00c82480081c900d001c020201300e08648050041c810b551402d42d079001070100720310f4000901c4c4591591002e400070103280c551446500580144801007194200ba0380f1540b8104501e0444000390048500030070900c1e034021842000d500b5004800e118540701e4a52269031950810022203600b0040782c0d80c801410b10070420320f800740d90001c220342c854503500e0410140420003070b85490f0185241c10004aa594020180d15441c0726000129420100c1030800168120114075210720440c0920f03000142c00c25012420000f03540d46055001614501e81046010024410100341d80500001c0c0c1c02080240c50710390a540701d1f0800c07410007085403100900100e04511541e08615031180c68224846240ca0b408007003610380c0d10360354a04000c0b00301c020040140c01182071184c0200700428140e0700703005050540041c641144200005802e160b01e8034501030400d05a0000401c49114802c0000d042c141d0411005402500034005404541032140d11810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 905292077 1250 905290827 905290843
    0x8130819020f0d0b010e0117012d0b04150501120e0607080711030a0905030c01020f0d0f0e0d111003052203170703021905090306070c0c09020a0e0120 66
    0x101c00c0c802d0601c00c1560307440d1201c640400e0350b403120081e1883d6850b005001c425035003c0c00303404024008045081c441d41e0052050346202140420501d0400000140d145949a42400e000101c03e49441d4005825111030242c2d806a0500b451b07105203180c107100004143c8039440007484078040c206080170401540100f00240c01080c40e281520481e51030050075202940c041c0c0340c9100c28803001a4400140f42d00c040b00c42c0564008a0507640485124401281e4519056941e00200d070401c0b0714012806000740501c034900074213800c0c4030084184800010f800c0181c010401c7c5c9d0b183c4401c0c600b10340540390000d01e0781c1da00032541c101005603081040d10340c02c940c0b0400481c000003429418114041c0b50240724140d8000c0612180c003005031500c020b008010350400400c401c4505000ca60980b0070710700401c140c43c0c244902038020403480c0c0c0d84050485890804171020b5403051036128010408007940d0000f0502e03090b040d184d660150b400f00000400007022101420102d298824942040300c40200d8251 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 905293327 1250 905292077 905292079
    0x40f06030c09090c03080f04030210170a050604090c080604050c01050708031306021c0b030c010f12020315100e0f0a03030807080903130618080304060507060e01180813081902 77
    0x5110403807131810b920754070860b4101400d0480080307050314403000d01000620941b442075500703900e060748c4001e09403410041e2842a01007030a02c40009203641183d07170301896000000a01c0428000e219071a40719401c00d807908250700c00e8120004100c1030200401c1881075214082c80c0c40c07850135466071540e4040b800090881c01064402c4e80c0b1b0107091145e113030140c400303480c0b41410603e0110680c410400081c001524203034000d01400110840642c050b440700f0365242010386900c07020070380301c954940003944010300d12800c410190082000507240c002c042c00b40300445440e80d07044240401c003005405500a2241c42c4240880c0e001440041c0c1d000030b40e10b8100f802802d000344140c64504816007180038645580d1000c0c80850720024110760302c0910360043c1034110141c1102241caa00c65583c69204a016000100d4410030407440010703019131000c403055041800009007032120780c070310885115032644d06440d042c0c400319490140c041c01800a000800040005010300d030a01e42c035003019a50010406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 905294577 1250 905293327 905293331
    0x70b160c030c031107031a0a0f0e0703111309080c1023040f21170103260705030310030311060103030f030209130f0e150606040515190905040f06030c09 67
    0x18060758001040868080e5502085440b8402c102c2c4110284513082145ca80c041c0c00e01313000e400780486103c0e1203601800c0d24ad04014250141c11625483c9420800070803450700500001c0e601c6659694038860500380c42e2051550079560200302019510700840c20714882200d40c9484c0894021004161070003018289500121001e552603080c020000c0c0c01507038001c0d0940345c6610b65000100c108111541100840d9107071000c0042000c0342000c41c0078000d002c02030190a4031854910241b0b40a00041c180c515400c40080c50416195283c50854100307a5070300005501480080c005c040d00039003100f0030200c00d03d0007400c40d5032441d00c0042c008040701c24113509240d030015021130320351202c0c050f490140c44426014041c100030701060100502010f01306102d035000f09840b0142036581c2d40c0125028140007400380c1d0401d41400d040004010720801c11480f200c2d020064520700c1c0c80e16852640385181e598903400701c8a031510041c8020f0f030f00c1c41920490360901e0051b013440010703d0400740344e0948400d0040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 905295827 1250 905294577 905294597
    0xc0612060105070c03030203090415030803010608281a0d110402090402040504090f06150f180f0c0f08180a060e030405090a06142704020301060b070b160c030c03 71
    0x58a440c0702d00000940134028500e404003e1540000040001030000e0360204a042038040c8040c0305010a800010464107041004100c80c034403869005030801c403013a100c012200c501800c0258054226072140c0c0c0282d442d4040401c0d0015841081455801c007503a82e90442d801545d00c02d10044206050907104541c0854558250744456044e0b8000d4000584100b0224060341045401005200b8003100e03882d0900075140e010000c0e09a114044912100e00e090b411420414810405100c400181c11042d5a5221019030308006000d101403820550707c54030000300c00894001d042940c014500604007142c04000d642ca108001001849550400d10000703080248400d154110321a55101c0390b0b1065100003400b44859496100740122100ea0b944410481100001d2020451681d0400422505030064840700741c0904401b0960051000300001400340c0c0341c109050705500f2801003900c0410a8104104170380c840008180010050380c180800e24417641c1d60002d080c9203880302c00400300818054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 905297077 1250 905295827 905295829
    0x80909070e041e05090a0c0b09010e04020706140702031615150f080c03011109040914010f1514240c030315030c220902130c020604140c061206 63
    0x101070001c0500080c014809a00e03020a00c1012454001092020f20f140001152910743d001a07034111240d44021629149840c3c45001070440d04809101d905001d44c0202600d295941c3c0d20040c80f003548184000a02e000e0a0a640f62640300024030210030740d44100f0041e0b9002c0c2501c100840040d9200c09450100d803040c0d481c0c0c0010740702c040324109204204810100f420207007001c0b4001900c001c1c0c811158410b050504240c02c3e2507041032107142d41101040152514202030b0001c41246000701c5040f070081c802d4203500c0b42120040c0110040c003999034410140f4803640745000c8030041c0000c3c83e450342215425000148074100381800d150705d42c0300d41c4880460304001a0140c541075880c080c140c07078403840c100340e245200d0000740f28420302c46e0081c00d104040501c3c00c0603482c62202c20005030304040c1005e054595004103500c07582a68044424034400d003d65209000e003081d0602561301512003428145041e040c0c11203599103400407500882c054a4050f1a040700381c1c1d1042522801c580041d8076208 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 905298327 1250 905297077 905297087
    0x10c080408091c0501090605011d070e060306010e09070305240303040e071b080307032904110906160c150e091506120403120902150703030212011502011808090907 72
    0x500130b0a650800c51164107010240c0d11050407905400b641d01190540707602031213000c030f10856009000c504005041040d90904c3d1014661055060501001910b00100010308050040f54981c0c0001d45802c200b004980440c2100e080d1480d8019105210b1005040065203038040d40c056564100c00c108006036075a4412080103008500c80003100310544c2c641e041c10812a801120000080f03401c00520302400c0d81000780c1341034880e1a012000c09010039440c00c20024014038842042c1500c0c041c081e00b100e65460707a0062100c401e1243da05180c0d142d0615203440c894400d85d001c49c03000110082c4100003035030060600c0a680d00111044100355486400030f10082000841040d00710074045070100480c499405407a0007a8060340325058450720005998099800714900213402003030498100d80300d01c2419002d080400c1c401e0801604114042811f550020401d9100c0c25181d071070b000b1800300454082c030444410000100c50440e02c0200c40e242c603e40b034424000741300d0059411400003411144a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 905299577 1250 905298327 905298379
    0x51e160b030a0b0a060203030114090103110108100f0603050105040c140a1b0b0f04030e0a060c080c1207030c060c05040f0e0702011e020430031202070c030311010c08040809 76
    0x41036013481ea61900380c000d58a40090003140c840382c0900401000031302c1e01704011412170381d02103040300059880380d004503401003018010440d5a10389100c082005618840000041c0c00709580003e030942c54082008292582000b00342c3c01c4c00078012800e14429250b4048406202150800c5410300c040b482d002d6004d0360040d08007426000b0076400f0311040e4410440c0541c095070103503079680b041d5801e5008001c11000b2038850346021940001400e80029131250150001d251078500780c032400c881c000d07220b03100340c0e1001c8003c80003d6103248040b4200a614030030510a03e1651038070a0900b42099031102080c18a070089804141540000906241c07013500084001d9a8a80d58202c0220f000e8440e417000e1740140c003888000a10f218069080d04450070210540300c0c04400f01614480403c0d1030640b8980c03a15802c41c68016000c01454010032112248a001035100307a030b8594801300701e860800d00f110074680300c035002c002410041c4000b0556200580f18803000407615100640703c2c02179060303a40c0b101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 905300827 1250 905299577 905299579
    0x1b0809060406051c0608030a0c050109060905030a020706050405030601170316060605041a0d0b040309240e040b1003150e0a0203010509060904030f0f050f07051e160b030a0b 76
    0x10001d40412542e5001025160302140314003010301c91190812400705a4555000b89403055100344941c0d0001407040003085038841c040c0c000010746071490f84901d01507403d007120544060380b00050401e0b90365070411500000300480d140250600d41400c0c0029151501841929074658160f5100304401d90180103d44400303041019107003810425241c044c028000034072800744514906405842e220b507a401d490a0305003001007180301040b140d0b5032a1040641c0282c425010002c040e007002c03a100c0740c2801c03603919aa6102c00c5130707014240c0341080200640080c45c600340c019070808242090ba078440c1c000c074640703c150030704012414581411284458096030380c003c11551900d0b40a101e001090341d80214143d40087c1e070000c003659240ea0500140c000142c400500040a900400481620407445900b9140d01c40c50b04900e0070000381082001a0003007542558150060403054407d90544c404540d01e0420440c040d03d11b40d01040c00414034030074603106000c440b46d80007001500307204180d8007052807120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 905302077 1250 905300827 905300839
    0x7021506222903030d020c0708061e1005010206040210020f070315051605030c09040902060a0e1932120312130803070c020414161e1b0809 61
    0x80c1c1c0c51400050055851034410248404036800390780c4000c0c541080360340310302030019850244411000d00c000e61006400400d140034904001c03521a8060010500a04416524405550041d00109258000a009c01ca030304074045008201c0f41e41c01080352a8400d40403280c20020540303491007a428010117070002c05d881c0c01030601c04410000003950200f540d220481040165603105807042c11002908011203010950500020304034184c50001085e006c130380903002240c045880d50105440b030300000d941d00085800203c44422a050940c0d621241800112052031028540180342c5440004040d100194841903208401e009071583c0020722610009001c0109425086100b05c1d02c0340c103d402459031581050011405104c80b1040114000c1e401c80c0e0024615103a0020a035002c2d044442d08030307000b80e16016000011501180c0343da00c2940c480c0002c00d108150100000c2140e4000140703c030014800510418200e50300c161492518400000700003516000ca040103003050007031800e916400f01e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 905303327 1250 905302077 905302129
    0x15050a12061508100503071a12330108160219030f021c0e0f0f041103061003050408040317040e1e06030d0e04020a112a01020607021506 60
    0xe080507810800b048196601c0201036156015034064002d0203100c1c01358103501c0440c00780000d00b290044004030607080c4429918117590a2803000415800300d03802408507505410404203403050701c01074410407044882105440c4d001c080081d1481c0030140424003400c0703c2c510102040c6001300614606020031900042e0010b01500d002041c40f116454403e005018103982d4602d0070440b10300d2300890840c140c5a280da6513807241c05020480c4080f2126075400b004010003841d598540d4420843c50080204215a4910b07040f400e11017000c005100c000304041c900420071001c1084840bd40f0103032688412000c009681210322107001b8000ca0b002041800500e4050140c24400a0b4800c20300d00000248408569280004c260311a8038412a440104086403000d00d5185030950083c1850b0741039042480c400311140b1011454a810440100c01060115565012051402312680912402480200b6051a041d030009448801d4401c071001200e0740c48021882d65600c00f41c1007260b19041900d690822 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 905304577 1250 905303327 905303339
    0xc090405030a030606020a0807030c11040509101506051c09051b01031401080d0e0102071a040e1506190e130902100503161206050301060e0411040615050a1206 70
    0x1c0d4402e051a1011900e0030100040300d44c00400d80349866900068410706201d11924243d4186100c1181142c848107400340302c0840b81e03600e00c10f15000d4144640240003a800288261084820500e0b05000101c0c0c5a001003000d9640801205d9004110340b04449030500380c80d0b50b100c041c040d20440103005003ea08002491060351528107c02200300341d07007d00c02c900c0f5182c04403a0f200405c1c014011580c20450070503031154090b00c05418007550610440d13000744d5a0754010340c19990b81c0b0b05a00170b4140c0000f410031101418114258007d0084001000d0142481d40018041c1c440c411041c60303500e8003101030f1104c0320b010f10074000000c0c401504a120107001c8134054802400c070003408901c518075102d0003c0e4130611a00a0307074440c007280040c2d0401c03c18040400e840000381509802d80301034481801050070b8800703006280003811070010540c002d091500d002e40b101d0f100c00c0d0350140a07600d401020070000300d101500c1076425400e803c00c150341c0c014101d0112990044c0b0015070b044281403920008038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 905305827 1250 905304577 905304583
    0x1060b0a11210c06010e0601050702040e0c0a06020304090501090c0c02090a060b1201090e0a0302061f030f0803060a06051201090507030e151504150b0c030c0d0507020f1c03110c090405 81
    0x24210204044c0e0b807040c1c1c0c8882d141924010180c400900040c403d00c81c29005080584c0402100d103400c4045513054040728002070000245504a28016040031504002c882c144c0d000701c0e8050180c1107820f009644004000030044104a1030280c031660070030000ca1030004095014202803d19600d14655603148625403031811182841890300c0c69103846040101c0f400c0110b503400e07005505501030925030312200250100306003200052540d00040210000c001140d000809448902c940b901c6034907458503508000d00e420b01c55000344103205081004040d0503040070280d41c10f442040c00d00154580721101e08030000c102e86054102948601075018100100400459109505010200614203040d00a0209803500c404404009d510442030500c03140c2084409003400030300c008126410321640710405883c0695080000c0c001c610002081ca0641c200964a07189520065880306480d485240c02c0100e1105110400b81c01c000d0000d080500d43c0c90203024800010a00a1915104c0e0410381041c50f1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 905307077 1250 905305827 905305837
    0x10203010609061403070e0909030c06090a0318060801091a0607031211070209010302060a0c050319230306090903130308030a05090d02070315020720090901060b0a1121 74
    0x8581204d42c0865100044411a44034001955484240c081d17203c041c46010f00020380401801d000501003844250701c108645482070114078001c0200c80350f07504018003002c840f1080030902003411030080c41030b2030300544540e0449204482c002691a00096170101004c0300800d0769600c01d000040e11001c3c0350380301c0b0308000d44180001d010040347c1c4840c80c1200c0c03988190100203400c01e401c02e004001502c0d140c0040c0c00f894440303042c20b200744030b0103617640c40c11507201c000104241c811400080320318903031011541440700040000e403240c0c80101c00e0340380e04500004280034801c244003c0041e000400620079a4a91021a035440c02956100d203404881f5800807a04001e00d02e2822002940800002170700d103c0784d030301c9a0003400181e41192109140c40002601c41c07840340f6000c0200d80300169105da0041540b00081c420f04203680020400c10000701d00282001440d681040300074045120a002291006c03203e5092402503609640c0300300b814180c00241800003e9941000074015110140040c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 905308327 1250 905307077 905307089
    0x32d0c06042001020d180512070303030e010b0d020d0f0209010f0608060d1109070309020907050405010e0d0b401406010602100518070305100e060408070303021b010203010609 77
    0x10403400ca0282d030169002d80b0741d2030b4483c0180d00280500c4590740c040c5440c10b003000351105001030416115004102d8002840340740c403000c0c0c0e00c070341010014540d15220b68004507003400000e1180c5940c00001038099070854801902c00d803071418550b8100404004900000c0354051301c40103e40d80e5440d2911b50348005842408041040b0f0300c00200c5620b415140c0c1a8030b1540b03e030b80341c02038900c000306100f090340b0700400c000181980d41610b04003680d6090080c1c2d215004958a95980e0b80c14800018003600483d84994080d100c00500721000800304c1c0082c6d0b600842e4040704071540103660a51340d00307159000c08181a00140e030100000100c4e40320010112076401480040d0542c040410700a1741d51501340314600041e084a9120280411103810203a00001c120748c220110b10344000308175003410440e030720072106036101799510034004d41503003d40b28015010a000d0301007450292200010740c40b446500600b05a400220401b242c5071002c0c03420340380942e2100846d2070b580c4408025041e102c25000701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 905309577 1250 905308327 905308343
    0x501060906110d1b14030a121b050d150807031b0605040e040f122d4a0a0f0503101d012a020a05032d0c0604 48
    0x1c550140075412030030800d40c03804000c06648081603022540100d5505988404c0d4504820800c08120003001900b115180c036401b0350b50710310f249003011702241c12204920074200c0c1054030000c1c4085101c510600f05d0300700c0e4144540d4480c16804070030028241e00721051b81c100104179001c1000400010b124054a214503071400b90150340b54909524482c05220300c81c009a42003109100440e150200301c2d803c46e1050b03100b03825110080d40c90b4010601240680000160281c4010300c0080f48250070883c92440b405290807400c056241c0244440025000e81149040c0151101e4005140c01e002c002c0100200d00400e00c41c05a48001034800c0f0079424455200d888601c3d0701080360f00c5540c80010840304e008009103211054038010202134503040b00d00343c8060900b1001c04800007c01e00800d1307100c1801e100c00c040d0011031024003a600104070711001c1e003150300032084140040d02c00400c5940d8444e110980c520f00f054a4401c5c02d14541c1540040d03180d41c078020038a0007500d1000603540c1d02030341c818aa6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 905310827 1250 905309577 905309579
    0xb07120e12161d0133050c0c0105090102102a0c061b0e0f010c0611131e0b030411040f020a080604151707231c0206040b09041b020105010609 62
    0x1031001003caa00d10344010581ca50300104200c0d580c4d03040c484000c0d00101c04c0c4589410b00c004200d091101501c0c0c86034003007000001c035001c42c107005000c2c81500795000d00b0410700344268500005d41d030f5104581032900c4156a031040644d8410f140d150440382c620440c2010800c0c0c05503010091412011140480340c61307080c0180500c00703a0800c01003203035180084c1c0c2d54007800207520301005509195109e042d4148000c0c0522000404c0c86805825410180b1240d01d9540d86090590188050407541c080079420040803050900d12442e080044101c81503040080c0d100e4440342042c1243e90b1100d03280550003890015010a4504503801800200381c080e210045140d4508041c0400d03240741085403c50820b01003c2440358011300440801c5100c069012640f041e500d403103070b00b84980c6a60003007480494400305000814580510884c01c0340410321341c0680c0011190340442e92500641c0107414240001107000e0702e0a403980c0c0c0c070400300085051260000062840c6019008000178020500001c5007110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 905312077 1250 905310827 905310839
    0x90a0902040b1c0209090115090f0308030c09060d06030605040606050d0c030219260f120403030f0c060207031e0c020d0b0703150303030e0105010e010b07120e1216 72
    0x1080d501100d24050750309183c8001c0b104841c501d140d521906181d2540c0c02e0200301c0030341d255412140c1c0a01310784c1d0f0b41e82103034610449014090500c2607205079800c0b640b484051000802600549410845420300541c0b200007440024a2a00a01d0b41028400e1316040c000024803c0c1c603000280142c0c016582040700e542c6550520144402840000e4204030841400700010f00b81034081c0441c40c05107507061144951980e840e2804079151900c0b1032801d440c0600c003c0c40380c0a090103411000000f000040803800410184403c46024070320014080c02802d880103200240180701841c00303140d100c241103568401c80d25000e401021814841501010030000341c0b80000c4c007800101480c01d070018040010700d40d0680d074145800da0020401001c15850f003884804400d404102800a0744c8203480104010f03459044450131500140c1c8040030001d1910010080c8034a01400c850910742c1104011500d038100781402d51f406122140700e560030016421440d80145c60100d0401d2100c0e20101504e110f1030f95502c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 905313327 1250 905312077 905312081
    0x140a060209041b050702240403060e0d0c051209031c1107140d020402070204020d1404050c090f06060d06170d0201060f0b1911060403030902010e0306102303070902090a09 75
    0xf02c0c1d01004682e00b00603070f4025160175109007540070a000e9500c0f824a483d000000c07402c0c0c015600c1201e0072620740c0da41d84030031442800107140104075440c01000001054484642d281c0100c0780c1d1415440e000034644038191000d000410452484042c5800d220140390710041000403c210144283d00400c04003286c030020420809640c090010405941c8264540801000b03510522089078003c1c0e0810501c0102895400b5840d4500304d202c4400c5403a05c2d10b0300740181045041c88c5154800c03c0a8400c001020251030413040c0c2080040d5840303034a0300040d0b00b00300005c1503103802c0030062031000520038000c913500203200c8810000c1e40e8020721800e41c1d10b1561081c3c81105004400441205011458040314022a524004660782c90039810070240211940e042c05003e81b03050b8000380e05e6500150655070482c07178203070220034154028200d6140000e004d241e031151030300802d0110740c104500b0411409034440d8040c42c12030010140d0312180da0f1400040029070002a9203402011461000a0803102078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 905314577 1250 905313327 905313371
    0x10806040509072c04110922081b070f0911041202010f14070605161106073609051b070f02061b0d020c19050904140a06020904 56
    0x14900800c0004e0902c2c48124902600d40705001e130071020318050390800340c0010091402140240030210b60340c0180410711001d25001481c10703180084281c07800c541800020039016a20340c103c00c030503440e107108090002c2c0d80711100c1d040180781d1007034000100c0d44030407050307407403040b12401c0c4000c1119074034048503107000d4041c0703118418603005c41901c100b000d5401045080101101303442d00c0c03440700000c030b0360304007a0380c114901c00c1c0c605a0751182082003860050600203002c41c07450800c900300d6804072000346e0755503200805800c100001c581050904501800f070385170640321003640c1d4071265441e004445403840080d116440e6164100408940142e03501c8414035100c90b010701c4117a2409030a84c455405a101c1500f00300c5c1c1027a8200804285403084810f880000c90a020203041c003c07840920080c40c100003000c51030701c6850840c103c00184c01c2c2c00d00820040b10030540d07804c6011350721030408800e110a0341640f0009030050241443c104182c950003072a0920049408014090301100d03568014890 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 905315827 1250 905314577 905314591
    0x6030f150c0d0225030201060603050405190c0504020c060901050a061a0a090905041a0a050c0912010b21010e030405010f030509070801020c0304180b090708090f0307110108060405 79
    0x2000000c1201d641002005240d03045041c50050315101c50141d91444202408000152802506011004050703080c02010b005203058901440f150920783c4409440d5040191041d8030240d100844500f00840005450700510004000310f468928040c1e940c1d48070841120314641c00e52a1500041c1212458441c020558101416014032502100484200c66110180c4502406001c000c0000c8030101c2c0d0080c039208510400f012550500302c0c616144864002810070b00c6d240d0304100c10805500c2c07280e4161481100d049030f82c80c40350202e580d2414010801200016080140f84400719420b2002c440c0d90508645110003c0000c0e92034242c9964032801103004580c000b48040414025140c42600f044d41c002010000359030352695524000c9003242e0000b4018140d43c2c0012400f0000200d0b40740c601442c01225280500c400740c0c1c1c4c03000086080310300510200070300c803a90000c00c4a2201c2040705074141e1400000b10381d039a0b400d500302041c070b502c200f05149000507511800030f00642041e000702801091 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 905317077 1250 905315827 905315863
    0x609020703080708072d0f021c0e040f0507050c070f080c010509181f05010e0607061e0501030c050901210b130c1508071106010506090406080102030f06030f 69
    0x1034030281218541c4005c0d02240030440856240300d040c00f032802c103032500d41d03075041d0303407903100c0103407a8070160071a8079406200c41550846ea829164400001c00381002510a920b4040200c02c9000c1c0001c000300091000c2c180d81519140400007090b4103c0b000b001100c0641c0c04690a0710740c2d6200c140c070031140704d000d03003180c6400c4100c0f01c11041d40a00042c004001d401071401c42091424107900814031000c56480c0c076040014266848003181c0c003140b19004e0502803038040800d4503650049441481a400c000340a150766030403598403011002c021090b2100302880510465039241400f25680c00d00d8000c95105422100000070a0060000c05241169074660150741c88400c64403080e54101c4004e2640c0812394401a0400025446400c664041d2011042040603d10403000080035508010200300034001da40346110002e610028400f41194811100c0c60b0f6203d01800c00300c2c02400465100c09655800841409800500084014030034941941150760b190100b00b029940c4402e009a900070083c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 905318327 1250 905317077 905317081
    0x60f080309040504061d1b010e010804200d1103010c0503071e0536030303060303190306150f1418010c1103062d010605030f040c1a0706060902070308 66
    0x10405401c0b03a58130500611000542c04041525503413040ca00a07a4909107400082060004041006c11210206004c1ca0182440315a200020309843c001030b10142c5000c05610034221030701c1c200b5252040c9120080c1c800d02c02e101c56454080c00c80f803064259180309509145510505910540c04c0da031080304103070b0f60240b10000d40411a0074010100d280a000c0003420808414800e4122071012203490b40161400da9809411f200120341c19001c071450342c400d400c00c100f0300010741d40010a50f0b240605e00f07050510188040c0b02c0507401800d042e40039502e001c1c1e0500e000f60039544c20040b42003400f8034541350180480300c041030180c030700d10070070070b0380d40c000c86090100054651040f8047c240c901d04c5113014114000c4440000b80c50901e00f1205001801d4441e03048a8243d9070f10502c1c06000200005280703425410304a0107000307404020500983c0b551800005003d100400810400070000501106002c111306803201d030441d880041b068510b070f404d00300700007000700240c800c445034243c06596144d519 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 905319577 1250 905318327 905318329
    0xe0616050a0c0501020a050909010e040305072307090501080d0e030d030c050909010e011d04033005360727050f010306180302150603030705030c070504060f080309 72
    0x95005003816104000c0842d049100040e000d00c0201170001d40c07a1a10358445500b8030801c804017a05030040c6a404100100307100010350003106071041b031607001c4400b004098030000001d40403400005c40900520448800003841c00c1d6030740c0002e068480b550f0a075110800310801c282d810140070b0444580503403240c0c01c08043d1707610a5210341c281035494a40315151070005070018415480a030845d0118408240041240307041c0311007510311454141c8040301007407509407005072520801c0340058a00c1402c081041e002004c0b030858bd0450018070038001c001604101d1440060400e404d0f800d0900031022410910300c50300c2418101d0300070241d1500401b40a07051051490356141181141101c800c04611036500a180ca801658403902c1d200c5140a415172540c14035409071400d144509040b0b00d1030441181c00b2076400300d025403203080c4840c2040b00584440002c03034614030507410083e24901000c1140313404894049222400ca9404490600c001621640300c580c40300a00e00c108061070340100007415103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 905320827 1250 905319577 905319587
    0x18020a080604020d06051008100e0f1b1c12030608010b12100b06090607051005071b03200a05150a060b030123060a02061e060303070813050a06120e0616 67
    0x3010081c458147c00241c0e80b034080901d810700b00f0b810414000c0d121148646480010440440340012304001800602a0202500003054000c5140350140c402894640c2451441041035844a6032101c01c0c0489000200c900a00425241c001c0c82c1c0103500b01000b24030320780b40500010080007403031000341c100d080c2d81040c024000c1046090083e00403006000340e180d103907036500140800038050380140002201201207442100d030000d00d500284443c0034080c01c2c14040c5e5131082c0382125454240040400d074110340400321040350350340c803964a109100080d0100500072444400750501601010001c0d281c0d02e10290540d0b9550103400f0300071800380010070906a00c1034284142401c03002252080071402404120154000608000036034842703428042001031244c0380d0381c1d42010389500800780c2d081c0040061789a203d00c100140c0100804106002c900b07015180c1d0200030640100300c0580e031586c441018203100d288040740c59850740703080b044441506021803191f01c19075482d4007140b00b001080000f03940f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 905322077 1250 905320827 905320831
    0x1e150604060312080406060b040b0a0e1306150314070f0c031707030516171b090402031312030e070b0c01020d110d151a071518020a080604020d0605 65
    0x2a00c55100c490001c00300c0e8502c080429224000d0b0742d40f002d98502030406100351781d0280d200300303d030700c2040104005140002060b02d02c851503615100000c0c402d0710b00050440c40d071030380841c101d2034076102001400c803180c0100d040c80f5004030788041c040718284019200304c502c41140c001c404504442e12140c14144a00b2041d014035200c0c1c24003140308201d11403e007841d22405c6401602284c3e49400788500c0705038424400501c05028a042d03289980d888008030702e50500540701d400441c0704051368035031440d041c1d0192401c01171b01504c210340324a0164140150003216040607918056104911074840d0310074012961080c0f000c2c802400c581c2d140007880c440c240d201e5010852255824001010a0308180c050700280003d40700400f0b4503500500800d000310780e000030110701c003612000c50401c18030b28201e0300004042058a261030b01c8a85600b885001101074580000d044da02e00546503060103610490503412500941c3d034120000c0c0c0b00d14010f1341d590310035900a58030885520b407042c0012000d0b00055 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 905323327 1250 905322077 905322079
    0x50d020a03110d0b09060a0513031d040b03030c010221090703020d06020f0d0b030c0307060e120a1b090b0406030302031e0d091113020412080c07050612091e1506 71
    0x3c0110001919520aa540c0903a02044190040d40c148424501d0038010190845003090075812280c0d11030340c0c003401160040300e0305d0241010b0800600b041e5540d582c04118030480103000d50341d40d0040b5042c418000d6000c0c481c80c62038912043d003980c1800400700c0ca9036220703900000003450618115000c0111344044640c0485603541c08004500307889031810041c000e00000860082450002001003606011845c40740034002e600c04841005003507406265403a8400c1c00388c072580c4042648000b2503090442e024005040c095203071410082240814141c242103400208080155014520410054980f284000340041e402407002d130500d2007403007142c1e150603030001c55030900d4203d00803200c4090700e00c404002e907003542e05e0000c0303841203040c100c488050403001700318210311301703414070004000707000c04001c01070185000401c2026031014100501000381c4002403150391030380d101003604142e202c030898503d03415014007413101000070350321281d40400f11031000c040c11041c00241902284054002c5c961 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 905324577 1250 905323327 905323339
    0x71208061c021903060e06150f09180328050a08010e10030b10060810120b0c040f0f090e010e12090a0b04060806090f1e15030d030f06050d020a0311 65
    0xb03d00d0b420000c500e14015032181d180403a000205500c0b0606040006014200c0320341c2e5a00100e10941d05c0d03402040840c0706c200d80710310741074891b04281c10030309403000414141c83c0b10005000c40c4047c4440f0000c03480c980040d00f0b110748414038041c00c41c5c1c680500074840000c01c1303801c0e0052144c4114041380a9001031810000310101d81c2da03440740865403070b007070365402030400300d070705041c07103c1c1c0d600c0002190b209036076031040700110380342401103500710740c5920001c0e09000c000c0020980351140f60003124010040c0050190030316071a0750a00005d01d80314861040503503d0824041a1801c060203504e0160b2014000351500600d06549000d1692040c2e900750f610428405c0c1c049034a100744400342c0040c08442ea9040e6007840d1240a01040d620003900c403004605580c0c080000303009a5038000049a925840000d0598032401289130070b00d071620317030f11540c5401810b81c0d01c000c15601d42d000c0d8414109952051001655490034440d1154609201030742014817103c050003c135400b501b444038110780107094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 905325827 1250 905324577 905324599
    0xa020f07060609020c010b06040e0a090201050d09031805030105040b16180b041a0412081b0a0f0b0a0b090a020c0a17030a06090c1d0102010e070b071208061c02 70
    0x2044110b8000360407492a03507902043d11403001c03509100d8a24001810349080b0303d4141001000a6060740082c502e1500350b488403030301b00442e4490002d40341d40b001851000d21422000389000340c800e642240c00041c042025104c005900d15050007094000c40c0c100550b800103440c3c840c402080c00b5406400b0301c0a00036032002403801c0042002c00ca4008281c11400c0716203031030400d807095078203903020a2050090b4005207c10b110f11501c84009901080d4822941551840004012840520a111030601c1d82c00342d0b00b864418040780301d02200b4001d10919440700140e81d098101000c0764810201581c010400d0f0b000561310b07032203550040100d4448034045401484540c2c1c0c40d12603481c580e029544140401205201c41040d842c000e035005401d411a003445580b0050200601c020740300341030b00f00005d6400c00014100c0c1d00039401050400691020f81d10001d031a0390300c40145911110045072081802c2c0401815144603107040c500402000744468108090058480c10007084035005903030005d44005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 905327077 1250 905325827 905325833
    0xa03081b0304061a100801080705100f0305071209080d1401060215190e0d02150708060f0a030b07051809100b0730030c02010506090612011e06050a06020c01080a020f07 74
    0x17000005800315542c07040020341c1401816070401c00541c0c0107902816400c02c030b480046070441c0500d048a202d500d00080c4a6480b800120341c0c01061402c400030b51464020f45405001600000300200c080500040c09141107a400c24564000300f4410307240140c009a0681c5001c282c40c08450781c002e2040c02c180b064006c01004c1c00740c100c49910040d292a984090710540341d268060003021000c02080340d80070b900340781c51800a401000b000340814071032100d0603840c558541c0e411880c0e031301441d040140360300d1506c0c010b00b0141c41640581014014000003a98140071071418200d42032007081e5070898617001d6494542004074170b40150104070b80b00212010f040f46144540451200c81006406400c1c5c0d141d00a21400f030112100030f1040d00031641014204903040d150b134a04940c0290742a02d0004000307044645040c011f103941c80b500e11600480e0b0000341e0300740707100c0c0d0469015660102c844604003a6565000e9079281011407549010548080010307d0448131035000d09550b000e004d000c1454404156 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 905328327 1250 905327077 905327089
    0x606030c1b2310140105011b0b0601031d0a030f111207060509030415020d0906022b05160b0402030c030303090a0206071707030c0b060105040302060d05130c080a03081b0304061a 78
    0x202c0743d51130302030b40c44010081c0c5d691084a403400160314042918001e54103440d040e50401d401060a070625448512045004000c0c40c65025041501e9091314016900761500400e016008240440090b190045501c8800c20220391a102029140c0c040e5140404a5890303401406000b8103411071400103100001d1894030403140444c01150981c05001c0d20105070780050300003083e1b81c22030021988505404c014010b030850001c103810071408a40840e040d0a070104031140d10030780c0c022070040e0000191200c20022400007413030085100324162941e003020803040c96a0381c0403c9440402c15400503c1c100d016080500041003218000e8403003409071400c0070400300043c1e00c1960100c000905140c02c0d501440121510b1981080091801a24051a40c3c002032000e02510300c0309540241d81c2c40c04030300ca01c4905500d405400380d1140d48075512540d14590aa101d0300e540ca810340210315214002002c500c00340280d411002d40c0120580d08549564030344400502d81c45840701a60041c05900224a603189 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 905329577 1250 905328327 905328341
    0x506090d0c0f181406032e020a0c0507211e170304020112230a140910051b1801090302031605010905030604020306010308030c0d0606030c1b2310 64
    0x51001c100781550400400d004482c902000304403100c003182c0511210303a401240c03030b00d0000354402c40c44000c0b181d14040c8486040303010307a4a081f1341c4d100040d00c008043d0401c400d00d0089009a09903103550b0f81c0c0e5070b04068480300300c2400004400c0d0006541000504007254811441c01d0625490341c0301c80181d48080950544501c4c5600030701e004020042150707844483c0b400924000d40d0f00f030013802d00804d104540c0d0320481c85946400c00d40c6400060146040d03034405080c0420072010900c642c28807a41850320303018040036a18040c1e0803c40000c07115030bc600400d204156410700664600000440048000701c2030b00b220070304015000d1000000b50303404000d070140310140006900001c518000003d44505040e505c25030080e0480420080540d40c0032035140d04681c1c008001968960300c0400c107120511907a0510701000e0704c0c10002181203907040d444486658407907100d009247c10000c0c09020440d00e8003400500d081645c0036030500304403400d001051a00002c00171118403030094031800c0c0c256110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 905330827 1250 905329577 905329589
    0xa030e010f050105310906090515090706030b090105010c03020a0b010f0f060314040b09122803051003080d060504181101050a080a0507091d0901150506090d0c0f 71
    0x8070702c014000342c40d100d52911003411030030700600c6a8040501c170703a035180b8111414410344c49a41c0c0b500c8030240110b030b030081402e40b070348041640e030b1402070a015024206001d0f2520541031055903004030700755004c3d22a030b4012090082c40c02025a19200c01126031300014017086045004600303164001443d2021503074081c010240200c1c0c045030414a14400c540d2840c1d106100700750814101e400c0e07040c580040d031b641281d04428010081d6490f5400700d072410032101800304408200003024040c0071080700c0030706410115604203c2c1c00000c801c4045081c1c400a40303070150403d500200401c00a10300d0401071600160b0541c003c248640d603000010216445000054840000010301908120754620700e10b600f0402402c1c00c60810100000040c01c0c2c15005020780586984c40c804202c00034011034904000340200d44107440700c0601100c80b180300c4407040d507248100391708207000d6402000031511071005591b07010300080d040c80c0d150300c208035231503240780070aa5072860100b001080e140003450038100a494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 905332077 1250 905330827 905330831
    0x6130f051614010c260903070605031609060e010f020c0a08070305060915160e04020c010f050138041e03030e0a0b0703030b041d070f05060406020303010501050a030e010f 75
    0x2c68200c0a01400081e4041c0c42d04000c030313644415001580041d4180499401180a255548a4520914120300c2408031065140c400c0c901c1c0003501c254054000c501c10030790501c000c510024244410740708110701d0301512012400000c4649055441a03c191318104002d10444440da6a550007141850502d600200c0700c94026160070300500000700a469004980e0300e00038503400d4000345036400040c1001e8055442c0641880d07540d8115440380c03254050800f00140300b15940e00c5203d0342c0b40d0090600d00c0202c001d83e800d05000003030017072030316002c08400c40c03207030804000300000031215450381c288151100300c40481c10b120119600960450419038402d8140f810741c0b48500718100030b0140041d098017544100c503200814400180d002007030b01c0c1c1c0a0b6040c1000306007110600001409000d403549a0f000c0e8864400350501c004100160402c00c0f2100082c0314840c45482e8028004144030b2806000c02691003000100010b51042d0000d0013050300e60720b0009940301034440410b003559845061103039199 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 905333327 1250 905332077 905332079
    0xa0f03020a18060f1e0c0f0602070803280b0f010f090f060807080f0c120c070b09011e020c030a1b2f03030a02070608070c0c09050f1806130f0516 64
    0x81e0489000d081503001c0017a0b03541031181840c0000d06030012054000c12824494100004016030fa4042c0e40d0034a030300810140d00d920b022444c1e10070601c0e00c941c4030100441c0282d4140701125041c03044c5c0b818140c0180c082501c005c01c92005464200d80d900d80d00d01049100d1100259034954055000080d101c5a950b108550400c003070010100d0001a00100c212071242c020710100b59201000c44800000b0b09400000b01d5032003082ca07aa450082d150060984800281080103401065015800e200d403180c105511301042c040c006004c07806450b8198800303600c10401050410702907106501000c0310101d010303502c1e4044d075442105016103d4061004451403000700414a90150703449100344005030021800d00407004030096517840c00e803055109120b001404243e5080c800c0b40d40c0c100d4190845101c5400c1959800324900800c01122070b681a08900d10220b4840400c40d4048450b010281005028548651501800c0c06e81c01d038400315851a070340840c03400050420700c120305038554140214000711f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 905334577 1250 905333327 905333357
    0x18060f030403020c1522170c12070e04021207051005130e091b0301111b100e1c0c0f03020a030909060b0f0d0608010504050d030e030a0f03020a1806 65
    0x40f1800c0341130a403080c080f0801d1420b4413221078050700c801440c5004002040b202c02030000000c414141c1064407040d90743d140c1031008020014a5910400040c2c442041e107070610030460344c48110500a007106d00c84c461011a01600e414401400050741c0942510304507555000010181c410300c3e803002e00071400100343c45900047c1c2c1405003004110104c24000d0a2070122852900c488042403201d154030348096080705180c40c2507000e1282d032200100080e50b603410700e0359a034074210b4030104084a00e204031001820742c0703561030003503d5403441280e0007003009a07504c03203400c000e2421901c000b0040040040350800451100c00707528405a000350042c00c031a060038240144030b040036070400301d0f1460401804000010700c400885e94600f9082c00d410b5120b1446615620251010358021106903080006001c28800e0204109092040c5034408001c09d1101c104641e841e03000302104074011503412850001280c6c0039800405440da000e14201d507484c41200100c15001c10382e41c004800141440240c10700d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 905335827 1250 905334577 905334583
    0xd060b1209071406070807030c32030f091002030d090809040b011815140301080c12070e010e0a0216150b0901030b07111006141305070801030818060f03040302 70
    0x1800c0c3c4003888800650440021583c9489260802000100b0000700c08060621505017100042e42c40160040448107005c0310a40d0038002200a00e5665804100ca814502000040781e20a20400c840c060400c40720034200022081014584007c2d400100300c94000c0036450303c81c911a0f81e01c00ea4201e900e48461009100072685524806814403100e01c490f03001d00d004030103840c13040344c0020b020100124200742c0111159200c6c60040120b2074804000442d5200d004102e1034180c0303100741c4141c80b8149501c0c015590313074034052103000088055440140b00e5030181045580d41708811030000b52801008000d60481c44400305070a99902c4130281000d03401841d02d00980c024080c3c112202481075065485407501040054421414002100e80b02c0c89118820f110034512141481820044d1591342c10080d102808040d045030b114110709510603100da41380348242d030700990700340d40c035101c00380e08554802007194421125003160301400d28000900c0c2e5200c1000300304003110201c4450b1641002d1a01034a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 905337077 1250 905335827 905335829
    0xc0d020309072d0e180f03180603040b1b0c240606040810092a03030e0a0311040b010201020c0102161b083f0a08071103040b0d060b120907 61
    0xc1903211003c1d000070481180c041c4031003540c007803500140b0b01d0b8550401d00d00c11601007105448842c040c00a101c84114000b00141c450514052041058111044100400d91004907030041c011511580407682249800c07007032201c040d21082000345807036162403404c1d00c1c1000c504050420848114221000005458003143e0012000c1e5241420a030a00ca140d035240c2268211007240141d95120060074890501c0c02d06a00071240c6108440364415030400e000c0d000388030f000a0740801c80c142040320090416015031b40072640c000710607440b80d503450b00402024107180008681159024044d008403c00b0070700c01000c4178a190740300902030303a03041e1600c2a200b10001402a0130060810f00c1048001804500162102600085210f040c0c05480300d02011429450f10862075040340c090102c0b004a90340002c01120b08591505180c030365404000300c80300c00075040044241e4000b0701c4204400080751010303080c002c3d1510404100c194a40022049540102900b200c1d80c01d201c00038410880701c00d1107224 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 905338327 1250 905337077 905337119
    0x10b03090c010f140c01090206040b0a08010b130e10030501051e01140108011e120c03022d010e031c020c01090801090f08030402120a051c090f0302090c0d02030907 72
    0x40b402c1020f900d80a0a403408483c000e00c080140050010b0188030f00b940011034055000381030030b441e0768403082203010383e400c0b50710080c011900000011601205180c07e60340150745244c03034034014500703010003012584070280080044400602e00800015800c4c01031621885048901c0c03064900404c1c160700b8412410f0344107600320440c02030b203282943d82c020921070665414200d400da900d002400c0c0c403c01000b503035200600e0410845508401c02601001c440101c9000b00ca540b03400c1901c0c403e4281c03404132400d502589114020045071115409228040300060009094410b140140c01401290900f448003d100680000c003184100d5a04080b4075409812110020001c02c0da107a80d80380320300c254040c006042c401d80440040c0c110350740c0c80900c0040344400020354400d480039191990703842400c11503440c0000084101014020b100300c0202081b01c2005240c0300f00c1d940f86400b400300d041006003050030f205604100d1f04450521600040d40190000c100030009289090200007110050300551 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 905339577 1250 905338327 905338337
    0x50c1f090608010803040b0a05040f0e190b0a180e0303130311030307020c0402070c12031205060d020306180a050a0804030204380103200d0b010305040f0b040c0e010b03090c01 77
    0x14800824000146d0b41940c0e9501c00459072503840f420b06844a00856200c80343c00080810081500c1d00d54280c41070080302d08407541c00c0d5042d0307040400003da0703203005907854021181103002c201042e00e100c200305a69240c03900009a00f89a10758103400c6610490ba0b0201c10743c0d8502c0010205940030050801400b070010146085003402200251034942d1400100e2080c1d4000c1355076414011840300d410010490301f4140541d9022618020740820520300a003000307941b402c000950307203041145034854910340c0140030340349603aa03901b01041c3d04081031a00311160706c1040307408400501c0030894080a00e0003480c40c2030310340e03243d441040251402076402c00ea8060301c05550161b621040d04490301d000078060b01074203d804207100120001e022405060b10b41986100c7c18070001c0e0740302001040a40c10509003030054414000055042d240705403001400d85540d660f40c44007003607100313140640003413055044d0b0700d0349941c5000559602c10300b80c01101010500005000d4403503020445480b07140340070f0801e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 905340827 1250 905339577 905339579
    0xf0f0905040e010207021203250201050d0c0825021002030c0d0207050312070309020913020409200114030103050a03110c060a0f020105060a03020f1005120702070305190803060409050c1f09060801 86
    0x6c4003034640800074905240803000302750110381c007450075143c1c002b4804204001480354000010140c1c0c0050303440e290b03920195042401400b06500030140d042c4442d80041480c580c40c1a41c000081d4402010500303010310901010384440310728001041d00074080c00007580c441031411504103116801900030402c3c10316000008005844254040381e02500e86403010029440b20b00108000e0101100700130400d1780128a10746070340b20100c4206000d0742082e41c880000c05102150f001092100703000180450380a03540420010784100c0d1107a45d00c03e103540944000e012113101040060b080743c0450404a50440c200d000601d609101d0503a00c0941111900c0242d0f02c2c42d0003140300b951010b02c20f64001c514407a00d0102103030064049800001c0411240411031030150380c02911500b05010440e15406440c03000c0828041580b07188c03152036040300310f052031502e400c001c010081018000c112001c0c0101e840001c5140c2c0d449442525001c0c841e29a101c9051010030010460b034130b240c0011090000c6900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 905342077 1250 905340827 905340847
    0x90618030b07020a02040c110d0507150b0d1406010e15012f06010f150f050a1803080d09050105100b07060203150a03060f06060e010f0f0905040e010207021203 70
    0x940804a940005041c0007580350420124104000f00350003a403c541414500341030303140c1c800070b030304201602c10341555100d58003140100c440b03100381c207000b600c102c0d105155030300c0b2510207a07c003400030b59004145103000707074403962030012030040c40030403d020750401c000401420701c0c8401c42d60f51200d06056211214841840003800e044103a0a01e804907645c00819000100a40c0c224010303100b0108040725850340e0b45100c100101d5038140110781c64042e0b411301c00040b00b8014400d25603040741d55202c050900c07050a00407580c5110781d14819503110303680c24001010170700180042c8010840080c1c08900756245040107801d4031405400020b45203d50031080220300101c5041d80d5006520039800b694945600c80242821003441c10055407165a1050020400140d1351084a140200d401d05000c81da07501c00c825200300c941d2386c0c1c002d404176903071401e2819500d101d94404140f40619083c811003664842c00410115078015801d080c0c5698001420300962030f1080682c101d00d034116004500d0852040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 905343327 1250 905342077 905342117
    0x1506070210030c1119140f0706050901050403080c0a030908030915030907030203031218060c0d050717090a050c06040f0b03041401020712030e060103021e0406050d0308070906 77
    0x4098204042e500e18101c96110710414041010909050450b411041105e03460004812048412248039a003040780ca0300914002c6820949001103002400708180382c81010f0f075481d03020070082810000200130100001e00b074403001d010880c04000c000d011484080c6000780551800340c00a9a42da0710900003101c1541c0d0301c1e6541203111800414058494985007031440c03800202c0e41000394035010200b284001c0c0084125403a10640302a03c014001120ba89292910fa90003a0755200c4400003c1098414081103500403d8000c00d0038a46541190f41c3c00703845072a040010b464550441d00700e5602c4405005c02044140d500d0042102e002d03191a00d00b0501842d8007280307110707286524a0110008003031024640c130306080100701c04000e43d900c203013500e032604409421214440200786400414000c0c000b001507054103995002d0282038000d1100c0c0074105a800006c00b0865000c1d46440000c1016210540440381c5248a42c90b601001d04040304081c0000c000e0f41c025600300010007802c200420703a94 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 905344577 1250 905343327 905343349
    0x91a0702010e1b0a08010e0327060306090402010e030601030506010f08011104090e0f0a0b0a0c02150c03100b040b0301032d020f010314090607090b0c0604172115060702 74
    0x12001c00608201040440c080784c4407a8030146042d40b03080c184036138400c804001400e000c07c3c6c1e000f081103a00384400351000300b10b01d400440c40e0009020700001d115824a80710590b0454014141190b40c03907119400030b494640d098000710341e80e4000e04010000004407114400150062100a21013400380910b00d5201d806144107540e24162500b40550b0050001d2100043c0c00e80c0001c261006072010b810010b030014401c0d50300901181c503024410700800e1011442c0c1240c0a040400700080d515004c12040c0c03160070150491000c03280560300054405040001400109092821181c6075031440c141034489030b02e4000d01d0b00c001c9d800300d0410041a05044405012075038126030b030004402503940102c0003000100440425030400c001030140c02035001900720f00c1610146e540c45032458552105a2640c069104c10b90740990050000c980050001030340e01d038403001010240b60500c1005c0c2025444106030b014104003810654091042d00e12400300c50800094040d1080340c90706400342e000c24000216 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 905345827 1250 905344577 905344603
    0x6290a030b1308070c0f0f0e1311130f09020f0f090112081c0b0a090204060c02041d0102030412300e07181a0405010b09010c050a0501091a0702010e 65
    0x14070044082080100580c0d44013900090a298a61b444840c030304881c5800340117005081040410005848224808080c890751141c1031000c5000750642c3d4120b0319400c00a01968880c0c106e0f0015030003007549118403404020211004228041d450051092028801e10070501550340700c5500b150549071070ba03000703046032803003c43e400e119035103400c2103a0385000d4a030084204a101d44800003115113941c10424584804484881500340d68901c490700b01d1107988510341c0072540b1201420003620b880c0d03000741e20060042c140c030303030500c400e1048050032070344101d608a40f004021059800c07042c0c0c1c0001c144505441000c1401c1c1c5c00f140341e4104510f44440313502c071040c031030351241c0c0038104112040c4108802032000340c05d44502000e804820001800140c65007042108101b543c1140794a468000c080c103c07140c14000514109150004482c0c0709144441038034188951201d020000fa82441180e81448c05000c903a18419409014003a4107480500104110f80c149040107242031030105514030b48481c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 905347077 1250 905345827 905345851
    0x122301031407050d080c06150a0510030b0a0906080f1f0c02010e06101802070f12020325020f010503090705041a061206010f0519081306290a030b 64
    0x7a59080340c501541e42e0410354000c0e02c0000c8850811a803d40940b0050200000381c0303149503100300c03d406403603200010706548160a80c00401103401c1c0030001c220700f8942440c003c00d030f921040000c941c480d041c0b036014100c5945d0302e903010004081c050011a000d111104050012a014030301390444484080552000030790b41c9070142d0b40700500035446200300d646640240c40c41881c04400b810000c0c145482005401080c10b020000c4402c090f2080f204003551200a8001c611125100c100100d1592010602075210400c40d00703206042c0300011280340034000c0302000c4002100d206210314640350780400760600005000f407141006000c591801692030503600000c0048000e200c1e0301c45060000d84240e00110000f440b50b50304078a00c0c90a620540007a2144410014000c80c03c60302880b4003e014030001010501c2c4006240c4254600340d0403000d038092881c1c1e003010b240c9400040b24241400d044e1256144903400c080f8000700c14907490003844c00c498019020713265448072122500e0007080409004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 905348327 1250 905347077 905347103
    0x1807171908030f0a23070f03061d04050c0a0b0717070206030622020f09030c0901030b0c030903071406191802010804060f02030906010f050618100c0b0712230103 71
    0x5181984a031030640745130020f45580305c0080d450440c0825084d80d10314005022600d03800111402401880c040321410081100c1d048101c4039200300d1014090000c07210ba0144c3c80c50040a651114845d1001d030580310b0b803041d070311650351810500740012595824210242441900090303034608043d2503101e40c080d42d282e41c24020105020140f522580c3d01540b0207480490030a4060000340007400b01c2d40400c1e030407074194a0104042003501d9009100c002c25400d440c0303000490100000d0080e6070044d50120440b82010016030369048c0200110b11040340303a5100c401000000500210b14042d0010750001c100040e400c10003116039440a6200c01034184840c01000c07404002c05a400043c05201d4003100319140d00700340c04801d0312000d083c4101c030a83e030650700000c06d00785012411500703440c560185444058442f04144619801e51001c2c8030309020b034000c10100803c2151814a104a00c207a0710f6441101c9401d007001c1c100c6406201c203032802d08025100c0d44402090a104030b0640350001c130326501c16 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 905349577 1250 905348327 905348341
    0x4020702031606090905060d0803070f0318030f0305070801080c040b1306090e3f0712050c07120b0601031d010f09150b09010303081807171908030f 65
    0x40600500b2400361001110018081d03602548500a46401d25018030140c4c50380e8080180040f00d04402a00001003000030500550052904495045807410301041922859420401400310b48034140c003c900504d250b040290b52500c2507a41c064803074140428036504000d182960b401030081c116004641d00e80724221156a40100918070300c0080c03030180a4183c4440041e00a0161802c140d81d85109a81c15020f00d800c05c000b4400c007041c4903260381d8100061501808885500300c0d0000c8501c003100f0000100440c07000d06007842c000d070554071000d83d5501c1d02444107140c00c4071075200e00d04014040014400146280b1201ea0308440c0034078021840c2ca44078104c1c0500004001030290041d840c1484c00c0c1c6181901e6044451000d0151030f111041007a91a01314040c0c0b80302050300f42e03014100c0001480028020025541c014080c1d13071582c00001e40403020b507440d01c0d049812446034840d038241c007a60b07034900811000d00c802c0624503488070040c055a407103000c03901024020300350030740d0300340f00140720 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 905350827 1250 905349577 905349583
    0x270204020a090f080d030c08010b07110a0509040309150e030304090518030408150f0105060d050a0e15100b07030f0305070e0d0605070e03030a09030809030c0d05160e10050402070203 80
    0x2800121140c0c058684e03492055a0307640080c030b60200d0100c0c1c20503084070a21401103506504030f4540c00c500f1807420034980d40740030320030800c0e02049510503c00c2c04085102d40303074403624509c80d40c840d840d0706e01c00a06240c0e030b00c01c401c041c20108804200e0441005030f06910080305580442c1c0b400304d001b09030b903142d0024401034904080c140600e41d03c03021800092200e000901800300712240910000542c80d290255064200b090203483d400060820010362086041d6210540c80b551040c0300140c0c2c03a5055603824144081941407050300015017090103002d00009605100418042c090b951412001e40e801a141c1c1c080c0c0303c0c0348800d0540da04000345507140220340c040c00b88203005244140810840c82c0010084c401030796110700040d00301c012070b14642000412588490b403940c072100070891556a41c104d050340110f1509070180070343c961018481d112a2040c000c118850805005500d92101000d04040c4690380034010300102d58081c00748000c00c880340041074500503100076036901124000b00b45 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 905352077 1250 905350827 905350829
    0x160501090803040302060109150302180a0f0509010e0f060717130c0b0a08070c20040b0301050705040810060f0b210106120c091a0306180118270204020a09 68
    0x2041e080d001042004040d07000c0348840c10384401880070405020042c21720f1081d07495502000303412044001003420900c1c001c0180c10b6102d0406100032426151490403102980d100f0b59166403542c1d190049a04803682c14407401d40d4101c2584010040c2c1d1512540080600c411407a600d010141c0010100c1d80111f12044103c0c41d1a400010740e901e02d40d910442c5101c60f40c8464580000600080d0104484612481210b40d10340d400001c80800030f050b032492504072003800002241d109a0300e80810226841c28050944910151b0b01c1e044e40f11484c01d141641442d10034140c9500c100c6c50304205001402c20a0723914804d46850f9841d00362990b4003050804103030700e8007c075502c50500c103a000004106030f001c400705003a951442414001003240c00c01c00e50b03403003a00d4011803441c14940c040303650b901c120020284d9401080180086d00b07202e004074158545030420380200041040308200f82c200344a403400b80d21a540c03012018013134040010211025040340d031000c0248541e0700003440305001807240c0c0d42c2034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 905353327 1250 905352077 905352083
    0x6171f1e02030403020c12060906010b0c0a14010b01140715110c10050910090b010905060612040302010b18011203110106230301060f0501020a030e0d0807062f16050109 74
    0x56070b030f050a0034040d603500c0082505a10580715601003c200e110003103500e9014034840801030401e80d00b000d4182a241c1c002d070f8010030242c400c018402e40442c3c42ca841e85203042035100b0000802d4175245c0001030500502240113603205108100450019003100d80007080700b026114000f581080f0708a0f244480d1060344078096180c070824480b41b140504950003640246080d000b140e012007440c0c3c1d00c0f002035900041d001ba04190101e80100b1502d15607802642d4005002042180f0780307500c10400d04240803080ea020780050703542e07901c00426400d10f42089a00d000040042811039898440d407484980803030040101040400305220b0450f00c0309400003400f17400611005d04a026041d0302e203064401061300c0c814801d60810070001507505112070460305641d0180d024114a0015803829940300c100086615004a129031744040824000f5000e0324400344550404651010071505040c4604500042074445681c0e084681c01c000c0680011680c54000c0b4030868900408c96090150040c52552400703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 905354577 1250 905353327 905353331
    0x20a020712080a080a05060a030212030d020f040e071418210c0102010b0604080606010819150303030c0e01051602030a0b0a0b030601090e0c0d060b04060906171f1e 72
    0x40010000e40030054a500302969851040701c0e90385c018290b0030381d1070540c1d2440d0000c000103003e0026003030661060501e119940d080780d1034408030703255140403030303004214668500c48049018002c2d0312082d005603801070201c0c80d01c8144c02406010702d01e000c4c41901907500300c0e40c054810000c1e0700d44410807500886840c450300303002800c003051211501d854503100f035180194600b803041400c5203880c0040d18141d40c4450010303e01ca80d07401c4010b40d08030360003524075181901c910000d002c0100d660300803131080c44004600c00000c01c2c59460040c00703650040d03203414203028800c02104116640603058807408820742a01220000d4603001003420001d80350740c080c09501d408420051460102d40148200500c00c0c2c044a92581c2d0b50400d4004460000400c0f403884d41245d01016118034098409840311b0740100400681740b0719071030024046a000358040d680c100d0300e07440100907160301d4512050107207070003601900380d030060818240040c0e844821712040d100d969041c105451601c1d00108500c0c0341c2c1c00a01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 905355827 1250 905354577 905354609
    0x509010618181b02011e06081b03030706051014010c110f01090305030f1209030f1c0f0504050a03020f0102160f08070203060118060b04061220040b03190b1003020a0207 74
    0x1703028001007001049811000c4070034503490f070304500c140300c1268081c80c090018015403940c074000d001140108281e0511003031040e00c020a040c0d100b054080c0958028410b034107454400d000c40341108040d1031034103012041c55410b01082442030310714070a507011581c4280030802c4500694074080160009010b80c4404203100407010380700d0005002c440a064507001a5075582c0821a0f584d220b03614811015403801d00c444017130808013418003001d00c00c000e08041a42d460600382a02114030495042d14240d114001c0501456010701558100384a184002c3d403810300740c05449001c119070b80c0402001c203420314000c0000c1c42000d006070341c1c08560050549010396551451201c0d007103000c140c0344220300e14244001130800c3c001003c4400301da416031280c86000c50810080402010030962110014000005406110748010000c0020300261080c2170f40301d0608010782410b0034510f602a03001103182202d244843d41d1400314080a10b40585005a41c82d0b000103022402c04405a000041803200031803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 905357077 1250 905355827 905355881
    0x130804180e0105100b0406080606090d060c080c160b1b04060906020c1009030206070c0302030304080a030e040e0601030f14060a0219020601030308061203070b090106050901061818 79
    0x1002403044641c00900564551042d010000c481c1c911803000d51100821041107140d009001d9564000e000400302c501340311003000807402501d043c0c50112401e950391b0409540d03854100320140e400ca0500001141080c685618148103094640005024041d4000004124602d2898001c040c0c071007840d00151036641d2800090640b82a500805025000341c14018569050210181c03400b40c640f13940348103810b4695020b121496200391800e55900c1003510011000d61410401000100310f440010000d8005504004141d42080b1110074829801d040106640f02000a98581944d40108002010340070a00e80006221214004800d05010304010049040328070390281030b12a102803030821035982d100307204030384074482400000c0114081801041e4241403501c140104902d1503021289408203e8484400b01c050450307500b20140c0d101c0f1414006820205a82d500401490030b10300c2d40354001d01e030b64070748070301550080d410b00c04510702e100d9003c0744d603070f81144030440ca0300c0520603010382041c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 905358327 1250 905357077 905357081
    0x30703090516060804020a0b030403021c0c0c0f050a05030304050a0501110703170304030f030e0a032105040b0a0b0d110420031306110f070803060a031506031208040201050313080418 80
    0x7207040e44961290f21f030014140300f803d402c030b80c40780f907243d409080305103d4030182d5024411901000310030082c0c640b00c40c0c000a01404424400b8089074800c0000b07d0b1303d444204250b690450700070034040e0b00b0510042146889a810360004e4070700c2400d107440d10010081d100c52074001b0560000d00702203144404085038900e0300c0015400755003c0d40d42c01c4010040c3c003106030b040d20a01407051070750390f200040c85404244208005500140d20b0428922454030000b180d0382518001d0700c041d500302203018180308101c06035100303004002c0c07010340350801840d2184d281c0718004820522401d004a44405203844a2000d0172081c0d010b6650b00d411081d00ca040c00940141030507101d101c00c503091850a038501d0824402081611281340c19030568a28010503035a441c05c0035000500604e07000342c0d0240b40030002a14174011003940c40124080011198554209800c03c061003002c2002403010400900001d030740d0040450303a001c9502444000745a08038580040c9500c520350110a154000418011100c0565 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 905359577 1250 905358327 905358331
    0x122612010503060a0c0c1101033c151403010b0406032004050603032a0a1406010b03010b030f090a0209160314091c1209030c150603080307030905160608 67
    0x40d022110f4554884070001e040700e4a0410341804505c038071031900d001648250100e0303840b00e010b150109207007007480b042c5800c6c44029800c2c0219100075002207030703200c0e602c0044e15510280c207940901050008503051000c00c03800b4046c5122301d00d800030340c0345c3c40c50310250021421a81c0143c801c000c019900d042400700085000880c000303103490115041c0c110f191034010b05000f482c0041c0514039059006e4140040d0310507090709180c0d940f0250181d580050000d010007079025000708a2100d034100c40d442c1e031508082e0141c04c4402f0307151061005100400883e41603d030f11600e607400303441c065258484114600b070203501c3c000b50700c600361104100711540f1400c3c9007500c000c000d40b400d1100c141610720820304282d0840321070702070364400c1030081c1182d034010181d00040a0141044500c416101d8044815528209010780c040b8505507400d9007081060007d13207005c50703401c880400480381155105092440050548000c05481e4580041401010322080391440582403c2400c62661024060b00003001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 905360827 1250 905359577 905359579
    0x2150a0917070f150e0906060a0f03151403070b03070c02010e040b0301060303110d05190f180e150603160f02070506070501050403080c033601050709080d091226120105 74
    0xa081c5c29801103061103c1e1031801464000c00c41418245104011a098422a108203041584640809020340814010600940100d101c180c40803040d081c00c0c103180c64580c0c0d020584039401002002001c9910204103200d081d4240703800c640c101882d000040c0130b4521700f0016980342d4a8079a002007010340100446104a500b90b05803040d0480c140c00c00c0d6801d004180c041116101c070f85555800d028480c000c4402034450a0038520110000003400c41d10181e4070390440001109060248680b00480c260b401c90b150340111000c0340b96180042062043c8100145c00d40180039210542c03800c0c007030003801100064500a46956258803403410714034081c21064034194007241115000c50300c480010310850344541c1e500d081c1c5032350010f008100b0840e00042c003140c1a0f204c1d1030803400351040030001c0c00342c00d005101503924a01081d007000591360a00b003800b46110305200f01520200f18942e1f1541c840502c154021035511450101c1c541601000c00f10308002916031100024070110302c24041c00313102d0517030304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 905362077 1250 905360827 905360837
    0xf050d080c011b0f0509130e150103080a09050a03050d080c0d0e0c0910051f09150216081603031233060c02091911031302150a0917070f15 61
    0x100134410745030f52140e0280d450308103510842440d4990303942e4000c01041820f20b4200c60002c02c101507998507200082e042103d4840e000614403402a9010000102074a011071340307074400700d00e160341c0c041d0ba4032401d0a000060090401c0040e1342801c50300155208004c0d00c69081c0078064a0b017144540b0f03081c1c40b0901da48036801c00d80108082042c0c1aa82c8407c0c3c900c054003060fa000d0580e40e846241803070760101041040b0700c26101040c458142003043c8444401754000705034070342109410350b4811034140c101714038551040c0c0184a0003500040858200c03030301810710754400e41c41e04001c90702403d2143c400f07405e62001b90105401d00c20050803403a14451001100402468946208881c50040d000029601c032480b4030100750012184c440c81141440f003124000b404c5401000c031940f41d44c1048685961202549050380c05504001c03011407030000c140c0c2151480c0c0b401c071903c003034440040c47c01410702c009210244e92400d180108100006040359801000189540d5801c0c0d106003080c00c400500014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 905363327 1250 905362077 905362097
    0x5100906201207060f020a051e07080d0f0c170a0e12031006020f0604050709020a031401081b040509070e0403111b012a021c0b04050a14070f050d080c011b 68
    0x105c0d00e4404d81d0040070403650b403a07181040b15410b1909551990811040c1200e080051b0000980c4940040100710b0750300201184011925603800203e0f400c00501000348146a8070807965640300040051303004120100c0042c49045030710038a490841c44444482d40081c000092050042007501400304481e0f0603822100040e507101c0071203841c0c0c0000d807030040c015403003a1001d01400c2e83c1900507192400c22403800062840c801680204008004c0c0d12000041d044480306905007064580801d90141050310f003400b5504226a0840d950300711845a1011505110f0100d000c140c030801c0c80f02607442d0050119440308010700c030619011140380a545022505850707004032140c6000d010410011096001e00c1c5207030050760240107524000c404c0c0c03110403070312401031000003034060703400940201c3c010002800c40030294900602c8500d00c4800f07083ca0381d8402c031420440702415644000541d8030a40f010741101e426468017030300c40e000b16080084654200000d8010124001d54054020714095651003040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 905364577 1250 905363327 905363351
    0x40305030c1b01180e0a020f0703180602010c09051e10030b0108060913170c07060503010e072a0203030f0d14062d0a0308071208010510090620120706 66
    0x213100041c10540c8040c0541c80108800c0194081c0582d00c22100700c009843e01d8000300c00c0c0c0d0b10a500c0a10201c1c04500d0103030142c1600d03175000390f1030405011240000c00100e04900f0700038061403103512545218584c5100300794184070048e861007a81d83e00c007134a246025a0825070240283c004604024001050f07000081c00610700006841c0c000e0f0400c503450040c4000716200e001442040a602c900d00220400065207241010480300b00200303079665030207440394102031100010001c087c1201c41044401d4160520b41c004414030b0481ea03030745030306c40840b421000e803000c86d007940070340d00c0362205101000c0341c000031640d000d400448001407044501049036032000100202c0c20108503001292110300c90090004680b907400180ca2513a005001d440c0c010746d2541d40000b160b22240c411587c0b038001090404070f0503000308802c0d01602c07044403031a900307001e001070040c0490200c0c4250000c10141491000d1070382d03c403044000000c1002c000381d80690083c0005072440341e0065008030740709460000001d1034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 905365827 1250 905364577 905364587
    0xf0405060c041d180d0c060b1002071203031812020c010f0813020105090306010b12070c020607080a0c1703180a020a2601140a060506120a050c040305030c1b01 70
    0x703540502d484128030603100f1551690408008266282002038503610412014080005681c291000e55464400c00410702d0301a0580781c81c4401c2a000300060400c0701c2070b194001c95940150340d00c49019098035070450038102c1c0a05003a00b4410900307031401100c0700501c0340398044140149a03d40844115401204c0110385181001106100150441012030b0794804008182d103040c0b801494801d04100d004800242040000c1c1d01c161060040014902245e9010b05030050b4801803e080c100b5110100d900132071180d00c1080c2c001815400c00003480da10190080c420f90069540009a0881600080b0030003140c0ea4010f94800c00350071640f918031968103600141c010384290f0702502c02029149424905e1502c03401c5442c1c6201d030170340402d0680048a800748a2600c186645103146503607130401c42036100458005030841da000e1b800c10007440310141e01c0c90f1542070b042280f070400004c0c595506042c1480c103010303640000b0400e00001890440d01c01b400901c14a000034456022840c14107081d0056417 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 905367077 1250 905365827 905365829
    0xf030c04090c0228030e0f0a0305120703020d0807120b131d2a0f011b0302071401030c0219020310020a09030c09020a0c1407031a0f090d200f01050f0405060c04 70
    0x3000a10b06d0402011500305807000742c5070440302400190980c0d07101d40c2c80034140030f0400301259482001060350400c0c0341d41080020040812420304016034240700c2d0008203e0340003074508103085601d82c0e071104107603210f00740350010460f40c40400308112681941140320244207c400e1004c5d5120701030503100080c1c2c109025251780d000e286006500c020403402032001019003200f90505101e40144186001c04803468000d5a0034803a9014108103070820390705040d07280c0b010407190304151502c201c601d00250002002c030b01900243c1c020700708040d400c1c8000f0389405580044a0049400030400c488020340110544040d00d12610302c034850191540158130490180c070303000d0307070000e01d074156100046060041003c0103458400c003a40c0d280d9480351185240360b035010610003a403181281c1000300d0003441540c15a0480a1080030340440c1000c400300402103401050660000f1160fa28441c142d0788042280160500b00c8000a001d6840c2041c280c00802000722001e82d41401801c000442003507509045034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 905368327 1250 905367077 905367083
    0xa03021b06011805270a030801092c0f07060e1302071713050306190513051b03070f060c030f02070f03080f120903090301061a0f030c04090c0228 64
    0x1c901000f2000440e002e44800380c02c0c0743d10110120071400101d6050100c40300310303000b200003d105528032460010402d44050380000580c5151500c28418111b43d0f503a40466003042c0d40c2c41c0506400700441080c01c21107503d402c0045846019000200c0d40e81080b0110490300e0119582e507424001c1040102c142d105000000b0071750500012404000420321019128030000350482e403081c15111004245421810b0b2542c00c02c140e1a907803c00c0003405680240d0f507014400d07103011074503641c042d40c5159981e9030f032460709600700e9003004001205d501c04102c0c00d0014a914422805007031b54400c40503244070741c020416000105034292107c80704e4000980d0504880718480c04e140043d02e180c55003180c50300a151005a510001c0280130134003081600218002d00451000e16500c0461004250841c0c1d0070ba480601b0603007091035100c0407080201c4c05e8452400720308149030b0760395032507892620300340c41150031080c083d0f442c22880422281d17001501d400701c3d0142d4840300c607013039480301d85440036081948001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 905369577 1250 905368327 905368349
    0xf0c0212030609181002070f020f01050c33180d050c0c10030212091f0606020c27010e241e0a1d040b060a030b04030806150a03021b0601 60
    0x20540f0303450401c1d003250790f164101c030554041c0c285d044020400d913407180c04151060180d0104000035407412103901800001c0900b070083c0f07400000000700d62100a0740040b84900007540c180004d800f0241074003040380c290a0421600146030600301c1c4a4011046c400000462282005441040c1e024100f200e2036040130100800c1c0c0071b4510b00801c208a00d180c0c0c030b0002015000e004034040c0e000e040c847c95000b02c00c140d000e8401003100382c910380c503107510345062051128101b1500f080101c3d00811040740310801998103c2c40c0e003260754031062151003071089002c11400c4d160000141c24843c81030705400f031220080c044200079580f0141403043d5140c1e0498680c00041e9002e500c1035000014040c020002c2c02902e003032a90707503070b0b910100d03030160b00d02008120071100c141c00c203c10401d0701d40a050740640c0440e0400b9130765080d07450748200507500500c01800d0000910100315665106a04903500342c1607450080d5607503010500050181d0030058011f21411100c41c03002d54101000300310b0340c0c140da60890079 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 905370827 1250 905369577 905369581
    0x3061d0307230c06180111010c0e01031802031903030c0e0108010512120406051c060305030405210304063b0d082a06070c151a03010f0c0212030609 65
    0x1c2c2092081248900c40283c820343d4a45641a141c10f4040c1c0204046400103c00700510040051b002080300320400c00d0316454081c141c00c020b500103551403100202883c0005100311468101070707440a001e44082d605100350b0200b0003020140100c000314542c404c1e40c00b03103d1141c125034165a209400d0004a020802d4680103002ca8240020024280c0c1e8a0351304481142a20304020708040d4046e41140c1d000400005216100c0426000c8500504241c0c0d441008a1880c50700c42c642c0368000c0c2d0003203038401e03640c500b404441400a82900c0314518902021b4a95556560740040d04060300642211000e40b400d00301401003c901c903440f003441090600c122800f603c41c80c0204104804907060865520340140804800544003060303039031800074481001d0300e500e01d5440c4a9450710074000c08000030082c0c20540705d40050000000016282d150501c0840d00061350310441030002c2d10076644980540c0391581904880201d038220401c601c0e9290240e40070298503801c24440c5201c00c0b658290803142c5e00d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 905372077 1250 905370827 905370863
    0x110a140f0a1d1002160608090601060c0201170901150504050f0403030c0c0b0103050708011d1c090312030618020c0a1112031201060201050c070f061e0603061d0307 72
    0x56028007a0109405003050810342da0000340e42d0100054036000142c1c0100701716000085462007980260041c3c3c1003c200615012406030340e2924140600b8041003001e41801046901561500c101200310704191101880c06a1441e4001c102d1080402c08050303081d540005c0300d00b0107115080c095250b081243c0600d03500c549040e0040d1500d90303102010000d044c3c0c9010b005ca0800059079010710b21507400303080607502e082581400d50301040010840800945150031038000001101001c0c0300c01c810031803403114901c14080d540c441c0ba640c0050240700400c4450201a945035100d081940c20341c0c0da0764169804030503120300480c026a01385206690149400602180740304036090740701b51000f40304003621207203c010703d0b007075030004400e0b0029014210014001a80c080c000c00707902c440c900a90354140541601c490000078408400541074903990401c070345041040701e55011442844035414407149aa130710b0410012300351900c0004006540f86075110220101204499005820402c09009005091 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 905373327 1250 905372077 905372087
    0x3150a0b2b150c02210901080106080709360606090b030612070e09150f070c1518050606030a111201020d090609030e012c0310110a140f0a 61
    0x88801d88049400c1c08602c014140d241c020b00e1a880507640c080e01c20522035802401106680540400c0b07032203000d00003032806990181d0b00c90b044551914040416881d80d500c1910a06107a402424036090050700482e280b490a8541c8000307004e242c514200c281c010031b1070000c2100c040d405044001001443c042040c1c4a940d406160404002030650114600c01000b5a1810a0a903c010000200901040000740342405141d2522000102c1c441c175030f142c03c140440c40080000d1048085c0000481c110b014032100c0100800c1c058083c0c401040105000c0100024007040440f04590611860380010043d040100c5c0080b00698004441c4131000501810050300c41f06060003130030159800c3c003840d20080c0302c80c0a0400400c0c09000e001079003140c18200103100c512006e134117606010852400621020b01d03600352400900c1e01c001d0162001c80075000103414402c1e01804e806507181082c0c411750340460768100038002c0c11050384480701101d0660800c40d4090096490344000c0000a2014580142c000c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 905374577 1250 905373327 905373409
    0x60111160b0c1203090a0c0f0f0e0901020720122b18091d15071d0d0c0f0501140d050c0d020c010606091703030417040503150a0b 57
    0x1001581c14100b040c0c80c1c4a03006400485a0245e05c4c1d000001480a20010000b5a000b803c2c1c01c15640b1545402d01000c900148100d10400100c0c0c0d03408800034100c1007083d81510141d40c0c0c84005a01c1020903241c0b10710007480c030308030602e01c50f0300382e202c10040c1c4644c00521005054030443c0d1650f9002c10ba8642001000c2c03090703031b2030310a004001020400c61417103055020090b010349980041c401c5450403695a4520706090341007041c1c0d000441a105444411012a038480402d03c0c00310102e011100c041b082950320440900e8000001c07010030010010810440419501c0212508502680e1480111000003040f003505603d920100a0600c04005a4206980c09008070f41140c0c50030101c82032104c03ca030b104031440c20390743c0d540742402d101203070703001005d9001000d00004c4141400081c03040d0310340740d20015000501d0044015040c18454408070f059034000d02c40141138441854247c8034000101c0800c03550a0901490205451864544065221400701e442c03120781c503c000c03034100017482d50390030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 905375827 1250 905374577 905374597
    0xf0215040f0606150903031e020a0b100b180418080f0304031e030209040e01060501120209040605060c0d020f0616031e0606030c0305060d0503190e0d0b060111160b 72
    0x541e88003051418110540c420503041540d01c2641c451b1441c10000c1c10144101e001c00b0079100301c4201040410742c000703000502c00740c204203510b400392034941c40d41801003001c2d4840c0765001008030711181a010388040c90b940004023910280701446080c0074840350150702d21802425201c040c00310800306042e0a025660041c401d081c1207011041547d00c0b90b00444100d0340040c0025000a00b50303681d410640030f0200d41e1090040248491800c107800039011210084441b070b0b00ea0340c080398141c0c09540c0c90f0000402480043c0c01c0c15901c0090948450300d42d400002d1100161241e00e00c8850400000a0120302c91020600b0020701b4110042044001d80745069000d0046040320101c5081011540300f03000060466450000302c1c9008500090155800200303614820041c400481021440102c110340301c102c04001203407401450100b0a58000c120440659080159060280100038800382c0b210301804003620b41c4102d0100340c2d41c00d20364078100c50200d5040044021420080400d06601405248031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 905377077 1250 905375827 905375831
    0x130b07120608011409010c030b09160e0d0605061c1a040302150108011d03090607020616240f020304150e03090904080409050921031003080c0c010f0215040f06 70
    0x2d9101e01450030344504880d02440740c035142d810701050020911036100c030301800c1c1c1014030010010900041c10306600070640c882e41d05104a038400c01c00c0c0f00d90149415004010207100f5468500e041040040c0000c40386c45000e4040307000082080750407a00c4e61024158001d555054a040c4000500c0740d401001d441142940300d0003211000907050414007a000e82241c200010392400c580400041d02d580c1503941c003c154004105c42d021507182e00c1b08075480310f070b0141c42550b030b50b0b2903801820300c0307521450f107001c1c001c188601c4c094281089801c5104510030301c00907062210003040728440d4100e1100303032801042d001040005184450b030b40d800c603131114405a800d4900780814440421a40f800071501107854080000b410321548880d8440d558000c002c4a00400c107096082c0012010205600040f4043e920084002082200c03101d840c076019582c000d000c2501d03010340c145036594640c2c00000681c041084011030f080b02e0352002030710a040340743c891440e100070b41703451312628083d0750f41c0c00007512a03035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 905378327 1250 905377077 905377079
    0x8030703031d190308071106040807031803060e060a020a0804020f0102030c031308060106050307050a1d0d0809210304030f060b090f011701022b09050601060e09130b071206 76
    0x10105210841d40c40f500c951144004001c40c0c40c00a01e14040180044280301010303048a8080c0e030000b9046610a500c00c0b01e2070b54403500350405a13010701500c0784503144801100404410050340740c10001c0725030070b02c03070445081d81c071100b144405070f014640c01c80c000a116480021301629000080c81c0070303c0700c180140c0789410b408000a80c11940180009010708201100030040740c0720402149005210904e0900c3c15414201c10092141c42416035003000c0040e4100b100314802070a448400000000402d604030100c800e1801b0b00c3c10f5008171030719034032038484e40c00070907500503156208401d004062005949007900303642e40c00000c03110b81e55040d0385081c1c3d2030300240169102d45010074010070495a2503070703543d89084d4250707000751000d0340c104c04240d00500c0b8405c5465064000b038401026003032940030b129247c071841080100424000582a807044070b00000b4256081065240550029201d00c103150303441e5404040404d0103150b0092019400c00c00142c00c4600c50941441169941e0302c000c5041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 905379577 1250 905378327 905378381
    0x200c0f19090f021b0708060c0c0c0a061e0906020309010f1205040c080f010207080301060c03121143020a0e0a0605100f09170a1509030e09010803070303 67
    0x1521140c8084240350fa0000d0302040004903a551040c810064400900704242413400807501c1e400081d01e00c00401c840070584641c5c0c0d4200380603031400800080e14800645541e110020b181d02a442c0c080303400c45d030041da044001c06101c0c000d008151071003900154502030440c0011207402d01d00004000c10030104140c00c0180720094040d00b405280213610030034a203800e0410303d50a280e0208140d00716030380f040241c04d0004600b5025203044640710300f4520116521410b080d070307000c40511a403107407481c0340160880c040304e22540680f0145416943c081000403a94144688402e1084018510800040d0340d03000700d03030100701c4402c03260762019040045403952000c0c00e07080002d0540301c40070119220403092180b0b04065080c490b11030384500d0052002090200042d0955419000e002007118040303000380681c00c4100054035041d503010910303008246003038440200626120004400041e4282401d14580c6041070304581a10000805503240000f540d406030001c04804058001e0392202d00070a1840c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 905380827 1250 905379577 905379581
    0xd21090909030e012f0109020f01020601030c03060207060e01050f011a09060f13031b081b0f01120b060408010b102307030e0a0605030618190f090b07200c0f1909 71
    0x5d121a548004550b03c11148100840c0016048840341194041d50040001c82c00c501800300032690001c03401a500c0449003406005005003027501c4e1061340c2040c00f071082241c0d007008414101c811a400c034900205500f5007400c0240701c0c4080e85a4011400d0010500e048030000041080d00c0d402a030421101d65255070315244610f140001d6151f4500000301001100d80610582c0340c2d44ea090000c0945030308014000031010807602e1003260400004201903080c000d40d82d0301440c00d42e040100641e4840b60707108a250301070000c001c1140e00130040903011407105802001c0b508000762030306130b9010696640c82c0d1144801c5e04520b00907410030040c00306c080c29503100d24803000085d02055451503a285880c4041c40812014103021100a00260081010441540d490707140440740340100803940e440d00da07001c40080c094000c07018080c4d0400f6014000441e8200700d140c1001c105645508040d1024580c00c19102c1d91240501c0e41c0009404101c0d040c40e1409690f90101681c0ca01c4503144015198010002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 905382077 1250 905380827 905380907
    0x605180909160608070201050601180e040318090b010311210403171905092a0604090f060302100f1b02060c010e0c0102010e010b0d110d21090909030e01 67
    0x4240c006017489482035080c01015031000b802c2c2802e070284064082c10000d07a42103482060300c4503c01901203401c0602c0f400700c0b10140110b81070782c543e019880d08102401040a042202c3c08203243c0007588007000c1d8107100b5980d0382c17a68465814041610410151034047c0014011001c104d20f1510741180200c55002c07040c02403540d100c69000002310405039100b2114050281015540040c2d103121040c01c0050078034454451020140800211a1000c1003040c0216009010110301340b505181d9035210a503c0101100d0080341c01600e00e00c45040241d405048821403540011044070900c03030482c4401e04c0c030b8440385101400451800c59101e803500c0c01c50b0440000814a034106034102001980d0901800c01c03c056008020404520410300241c01c203106284000c018a2441c0800c05d80ca513210000c40e086150018041016415514580540a01c4000300301c000700700540303c0402c0c181075500c0703604a003a0749a1038147d006100c1e007005540c007515180044011030301055510582012440740c8030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 905383327 1250 905382077 905382089
    0x70506040503091e210111270105040f050f01052a0d050414040908070f06060612050c03060919093203040b0703170f040b01060518090916 61
    0x54403003180f00c040142010030644800c07020f24030400802255a01c40c484403a001c088150034101d04042004002e0150030400d00d00002c00102281000d1040803262459100c3c40711401007d40566190006461502685c042c07030b8016000c0035014081410704042600c9900c00505007203003824900442c2c00c580640c0426000c0110b59034803809003051004112a0200100d6410300c203061500b0440400b0340d080b0560035030b0744141e84807049541845007000480da0003d80102c051a60f13200ca605217500078100038862040040d168002c4400c1c14107a52140a014040b0f4501c01c41c03440d1200e204000d4808005000845240d1220035a2a80c2041d46c1c840e1001d40383c49a1a400c1030000c001c030300f890022105540640402440c0c80407510701c148040102d074242d0b83c2c240c007001d81b0b554003818221040d1a100850700c08a20341d4005214511000e4900907229074800c079100b19041ea21480111031a000c1c94045581900c100d940500c500d29014010f1030748444500c00301d4110030711107250400e4044581e8010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 905384577 1250 905383327 905383333
    0x905030903060603030a17100e010f08160b090108061201061404180f021011060a05090f0a05071202040f1a10030605010507020402030a0b0d060b1207031707080705060405 75
    0x14005401c05116080d4082801c8000d142002482c0c4000b902c0501885e80504040705800c002401000c0c0d0000e820010f030000c1d400004040da1100142c04687d0700c540a4044a481003802c10038024808103c584141e890302240c8900b8001010010350310300b60040d16155000d445c900369a1100b030405d10030748000b004903040581c0341214030305c1400111116064046502d40354110600d011460380001042101e5064407000d03121800f1200c100c64150803481007004900401c0207000b04a9143d4000c58018030411095440d100300c0110115520394103130100902c0c07500000d40421002062204901c110f40c005000410b00907034482400f811142d181242520b101d08514080c0c109040203a00d03103145044904041010508040c0081c050b4014110300038419600000003c100725104d8100c0301c0a2040a031100e405051a0300d0090050100702c891140100305412030200340660014850040301d801406000c400b02406090180780e900441090300c03403190030003040c000a0b40c20131401f80706074014006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 905385827 1250 905384577 905384587
    0x6120b190f0902030c0a0e011e090609052202090a0503060f0f010b03151c0f0c060210021e0a030207020a0b0712090b03060d110d080d05070c23030d090503 68
    0x41e2032840c8540d9004450322500c18010846202003100440d80001d4050920045a0007030701c00490740507411003070450507002c011108480b55900000700c0016613000d074480c014403580741c0303060055040c01d45d000d141d10003107840d900001000c805d50080011400c00740446107110f84560100303141c1101951005c981011610801c900810b28024840c00b40c0854001e0b00e16508100b60285050400241070074464440c19021114452014100005680c0d206008140542c0c040c144045264014131405026005942801c00441868402c8403070001d46075101e81d004899030041d03001c0c2504000b240c135080c15800c100f407030056581d4100e01c2004003458a82c01d646d4240314500142d42d4204908004103001a80e1000c2c050801c0c00070a40c3d80c03004050300c642d41140c01d1420300009070b030040f804071604400d030b00040ca02800002401800d095004d00c41c14000794036070b508111980e03660703e1400f42000c0d80d261034420f08010801450381c03000d00108216800d100d2101c03040811222107103000c507065031001403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 905387077 1250 905385827 905385839
    0x10903110f0a170a0e1008040b0907120b0603010f021201030c05010f0f0315170a062301260102031602010e1f0c090b0c0d1404060906120b19 62
    0x107884441441039015090202c02640d4103400c541d41248061008907001c60f465490034420520703600198802400c2c510800a8100c0140180c4002c1d01c058485603c03480000c0c00a01780064460101c82159040c1c0d00e0300c110580b94083e1451000e02501c0d419500d03034070b0944101c54180094160303515021000201540746152a002c4802141c2c4582d044c41002e210004000750010f0f04010140350360b06001c40c01348d000000b29440c400d00b40c0c0010003d16008001110101e00020341c011585210b03a004015072645103141e2195000303900680200041d40340c005001271095411448440c01203003140702d00c410303021510182aa0001c07100d100101c10410710090085074240504070729410711130040c1616801220101c1d003949075401281a0b969222050b000c0d41510541224004284228220340c403031403e801c0c2d4603142c903180600c40c0c001a00781c2c04040d08181c150030440c0d00b20307089074880008503480d0a1040e900709078020318134850541c0c0c455002c071180d11400410044100f003c00c1100030349040c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 905388327 1250 905387077 905387083
    0x50d1b0f150f0e010c0203150c0307030e070f0314030403050703030509181009021b010f060518070806090a140a0c02061f0e06270a0b01050a05072301090311 69
    0x4001e038020800050507180c405600401030f0340f030110080c60b0200c100842800402d00e4028140624142505684204280d80e42400301540c000c0e20f15650a0260a880c01101e9035076440038062410300202900741080021b084000e04a41313035000c2c0d0140d90410fa900d032195814440d190380140e01007a000165800d2a1038224207080301200c00c1c3c0440c0d411406c000c507880d00c969504d401940707842917000505480030111011046050110940280b140c40350350810300010788003900c9414028100c02d4400701ba11804999441d21440c441c0d541d0750465620036041292400018140c0540e8695550841c160071600880d4a440745012060101c0c4484280740c2c001c0c40c0a074001c5c060025242541c512101d4001040d0201003101c602c43d030b02d5040b41e03d5000c006100e001c82078461400713003c014004100a0441b060566104603e040020465910ba110044d1554030584600800050341000484001000040c848241e034402d0452102924110200d442c210342c080309043c0c010906c0345d02c0d858010b41c3c3c10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 905389577 1250 905388327 905388359
    0x50618070f02120c0d0e01140408071403010905061f050604090b180613050901020903010e0d030605190909030c02030607020c03010e030415050a1215030b060d0507050d1b0f 76
    0x1d480002c0c54150b0941c0f200c0d0711410b5807280d010804c4000c6d0081c245a80c0700c0d40003180c02d4410950b2955890b641e94203010341d03401c1700d1b1103600e2402c40f6890043d08640b406200340d501042d0000043c0019030f90b05200e81c984034075002d220344902c038284a00400c05894180162001c0c0c51070070720015500074200d081000c400b030785102e0744040b030040c0d20801000e034803544000c03007400c0819a00840c50303858820415019004c3c1c00300d03060301503103040840604c1c00b0740002c4804901019403020040e48d6100c8062020403599022002c4000410403c200500f00081c1c0c80700304414080d29101c00340e40307100c0d400603090203015030f0300c040141c0c03040e507000c44946800c0c860203c0818103107008525103441c100c91007168000c940091004c1c01408546c800c5094027510400ca640700b4126000c000365070b040251030303030085141d010580c0d001d02c0380d80c000750a50030304a140704031054000c0002c10f2000e1074081000039503412104221880c6140c83c5011203400d07203040e406805400e170313500120011070074261010440001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 905390827 1250 905389577 905389603
    0x3112d06011a070c03050a030203040314030307020303070f171906050f0f06090d08120f01060503091015050411040e0f070c02040b010c12170903070213050618070f02 73
    0x21004000c42e611141010345901d40c0a502140c80c0d42d25800c1c40b10004c07016502c09840c5005060a01c003c041c2d000c002402500c1c401c600340040b00f1503d4412503501e000880300e0f40050303441040130030f0602d401480104424010b03498460310800030204c03100700c00882500d000f07869500079525801540032500500e006031000b41c9607940e0b00301e890300c0000d02e402c9404003458080c00e00094142d0050715220b0802e604c06411401e855a1a5501d20241240f43c000310b0712039a600714030f10000700da21131142c01100d00440203c2c0c002c022441d100c1c40d00f4801040c00d401a40c0c00c1422003400081e140c0c60f40d000c0c0381c00440407007000c0768442d40740104681c200d080080c540003030098507004106c122508001ca40034051f80690b0002000341c10a00140c650070380c0044040e02a0240513040b01005070701004400b000354800500b8a22510f03040c44031680c0f0700681c2e8000790b11100c0317420b418140c858203500880d8024401008446018060b0840b03c600c400252207100004074103100355040c99030100902150030507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 905392077 1250 905390827 905390833
    0xe060d171206012606040515180a050a06030b0403080a0b100302070c0f0b07080306030111181f0203070b1b0a0903050706050306131a0a1d0f0108030f030403112d 71
    0x1125214000441301d0081085210701c5c1e070b884c0452242004031001c0c142084014001c0245001c00030b0484c1500c08040707908440031410b200001d5292a1280200001c0301e0b4010f4415845480716a410f0b00d8202c13000307000d11446a55414480915558072045201900700341d00c00603a03509041c20040c6441ca1581c004c420b40303038142041000004000d504440c482500401d0003070301c90b11004006409000354200086103c807000c58540400006003450200c8041b08842c0750342c5e00b41c115408246030030311004020300582c005105200c0419034284003150707c070300d00d00101f480d0200c01e00d4450074560080120b0b500001c0621005104000f01009240d0203480c050400324114034011000415444800b0900c07001a0344403000441c0500c0307110807030b03140042c00400b0300204a4031641e446012006002001c06031040c400c02143d0b060a0b1389000a042e1084900550b10740030000d9190000d07580068021820081c41003d07020a41c6014004140310705088841d4108100c0104a0140d490421146155960b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 905393327 1250 905392077 905392127
    0x2011106090a030c080f0f1b0708030d0c030b0d0c17010e07051c06110d0b0d080d09050709020c010b010f020d0f12110c0102070b100e060d17120601 65
    0x40d4001803160281d690626021005100700e02c0c1241c0c080c0144000360a0b800d2000c16004410814400540b6540111003000304100c8c0d210a00e0030390380d008603c6210b07800c0e0400c00498a131554183c114040300d14a9003004140da50344100401d00201c2e0842050350b008007050000e10a501000072164110310f00d210080c045005603104898603000903114040c403910a409904900326909059080427540202e000c100b50145140c03101c000c0d40c418040380c1c81451600200305003a18002001c40381140c4c11042440c01d000c0901c100302c0081440480961b170030700c500c410014201000c2d00003400d480c1582c02c004601258081c0002d044c041c2d2140106096400100c098094543d00071920400c0c0151407a003529414000e02501340208801d11041c040c6030400140d00801c03580c15002400346910401282090760349100c2c1040004603030303000e6034800708070300c0000c20658502620745084031402680100182440711030720f000b055200f84401a09000702c0c10800800c1d40e00f201015208001c4031003003840c44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 905394577 1250 905393327 905393341
    0x61e1b12040b0a0e04021611010512011e1208130b070510050a0b060a0e090705030f0a1112011508060102161a0d0606051e04050a06110c09070c02011106 67
    0x19000314060300c4030102c0c010441d045090b00c500c510502c0d4190183c411035a400c82504240e03020500c0d080c0c20389209081da24000d2030344d4840d0301225151407220f1101d00313440c2d08001240740019202d1342983c0300b1841c20038000c1800f0401000b10725a031071042c28515030f140030071010b08200d50310683c001c0101600c2840760002054002c265220f01c00c0300940006110b540c3d0900003030050080900351a0810004907005030295001801e020446400325041c100a03543c0350030031561345c8402c07155040001c2046000c01c01d50f000a421500b903070b20400100900b0034003480c081c1c0340482004d030301c0314881c11000c10600d11010f80010100317412070000c0c80a030484680880d201100030507507118820703c0e0b6140e81e1401d0082e8182d04151020b000e9a03603414042180c0d5048006c003241c2100c04104441e501c46842d0407150803e0000301e5045490147c020300c0158038080e002e0b95000d4088181d40303e9400398641d1403106a4030b405100303108103a26100c42649101a00005203550254015466141e02140a01c000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 905395683 1106 905394577 905394613
    0x315010c030315090f050112050c09072601090b030a0804060e0a12110a06021b04020a030912030615091a09120313090c0c20061e1b 58
    0xe42d03600c038901e204004103e000001c005a01c1554103500c1030401142440d07200072142400f40042240d03500dd0462204840781c092801044000140101600780c41a07080c103503030940040004681c01e0b07403844001c0c869800b401c010320000c8880c0c401c1341d0b500d81c2c4003030b0040c0c0544294140c4500252405410301ca0024140503c19015900041801e82c40050311400f0f01c0d507110b0409a41d00c2c10b02041c44002c0d032017401c08404142d107075564140070403902c41c80c00b500208155400210249041546001c01e07038101c00311410008076003004c000002010700c120003506c80d002d06542e51404942d000504254041c80c0f20452800042030000034903041c07002c2501152200c1d8028400e0640462003151020031541e0000c00300400850300c801e10703a8220122030100c540141c107462900005103440c00021541c480107580690740001c3d54206410050f81c2000b50a078070b0401000c00c0c00d072201d00c03191 = true := by decide +kernel

theorem cover : BRFrame.Cov 905215827 905395683 := by
  have h0 := BRFrame.cov_init 905215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 905215827 ≤ n) (h2 : n < 905395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
