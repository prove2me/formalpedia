-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1574
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:47:36.755709+00:00
-- url     : https://prove2.me/submissions/fe12723b-fec1-49ad-a888-3b414bfe238d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 282913669 ≤ n < 283093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 282914919 1250 282913669 282913733
    0x917130e040203030f030a090b1f0614120709030611031518060103051b0403200102031810120e07080607050405180a0636050408030f1005060403 64
    0x1695281c01640e00400645c5070402c0b06203580e4080e00000d004083d040d07078800030b0314045541c008821b841981c0880c6219029440e8072484220325070341390070410810000b1080206200140401c4901030075502034001150387d6210700c12079070248940c10041c102401d08607481e4101340c60304007442c0146032001c210300348141c2c40c8061000d072085541c0700007418190301020650b107500030340c0215040869a41071803030720450b280f0304200550290340122040811036400807804000340400b4145020248003443c544075080c1c40000c1d09091080c181807055041d403249290741ca0082ca184005414010380500543d40b1f403440301e0b9203801c01441418050700074100003803c118442c10458017601c00041094196140724007603401c40034401003041d40c2203a40c81c0070120364500050303000c84904040041c0b208010421040c1c0140b4107440346c0303203054000d0a050a0000040240054950000c0c1010000d80c00da5900c2d1840b10301320303015510031500f01000160100a001050307a00d09040300015101d035100300030003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 282916169 1250 282914919 282914939
    0x201030b010c0807060905030c12030a0b0316170c0a090b0f0f22020f041707090c1706010201060b0f1e0702030c0111010b041b020610140d06091713 65
    0x500402483e88030f08100d10380c0010303900d0b440318180b280240f003100d080c0448080040e00c0c1c8803582e000d90340111808820004006507c6c0112000c41200354040e0518110101040080020501402810b402e038504001c14a410400c1011200a0700410b1452080d03501c1c80800c00822805030650b0080c40c4200340d0802c14140f21102840503140508030405800815014a04411100404080c2c103902008114034101103070b40988054001843c3c82c1d140300c40c503c60250700c2d0203525403016406a08100b8146041e07038100004021004104501c030580342d490500403401411140c00c5180090710105216108061038000381003030381582c4010181002d00140c90343e180e8050608000d505a000034540d80030780d40b050900b1420750100b80004030301120100002416500c0e112400c0b000d00804030100c1c05c280b86c1c10402503070042c140c4000103ca803414500816005480303508594020700740c1004010400c100d0b644000241d0b500301c04000c41c0700c0661000000307581d0299983c54014001c07000082486207a03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 282917419 1250 282916169 282916187
    0x70620421611011505041116080405130b0a03120c0c03150e0a020307050f060c060c070b0a020304030e060c0708060a0207030e180609060402160f020a1a03060d05030c0703050102070201030b01 84
    0x1858072040c40741d03250804101c050000387c03e55425003001400107000903c034500c0c42c2c00d0041d1164425944660070001442103c180c04415410414108000c84d4900c2c4c0fa00300d0014103a075040701d102c58650090000640342d8042e0f01c44010001c03240c070400081403103054644010f034000d400d9000d0241c4101039600d59519440080041d6054100c8801003106147c001510010f005025000d1820029454886400c200088070056200400092980c007007000b200741e05076025044090031425420306031401010304071114103140c001c0100080f09455001c7c104125401041040200c501e140740101e10b05010790801c0100b2404100c1c01d5401d0b0960340f0f03001140265105002411a85a07500d102c00c0101c05400a07003d40e0304650700700501f100031041c2c0c410700500d40d40a4408004c3c4003846205010f013282d006d80c0a1101006080000b00038501100c0031290424021104082c0b0b2405c24140702d4150302c070707800495000780b044140001c108403045d0082c107200d5000341ca0401083c01030b5001540c0c0030070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 282918669 1250 282917419 282917441
    0xb060307020c0406153f1b050c19140a050c0a15020303191b0216140112020f04121506090204050a12031107062042161101 54
    0x2000e0425a0808100d080e81c03428a4188503c02c0460940c1b0304018508411014a031035009170b49070031540c0b407400c03032072159400103031601e00d001c034a080105170f10147c884054100342c0c0e4007450403220060900090558030481c0aa200040d1903840c4032038a0501d6899020f04e01d00c2e801043d0000000902804000c40c1c0318094040b034029603e5a0b4512804902c078560901901241560b82e20b141000c1181040c140684191030350002c00045803007103088100d40c072290788009180102002e0541d04d46c1d81c42090080c41c0c2e80700003005a1629070b08000200c29000fa5004042d410401094803414000d004001421700401c2880800c100398480a000040c3c1c80749010f12900002c16040400562005030f59007500c441c0030389048003003225020701d580c0c28034045030b20050010325003a01c09400c01e020100048241150070300100b142e110203402b882c42e030816200310391003240b0b1003036941054401c0500305180048010b0410b6205480c0100c140743c85210390400303900004000c0c400690b4640d20521402030701203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 282919919 1250 282918669 282918677
    0x15080a050708010203060f01140c0d030606120c0e0f060d0903051c0507140705160605041406130303081b121501030c020c12010b03010f02040e060a0f05060d0b060307020c040615 78
    0x45587d46c01511041200c1410060800d0f0400440c2c2001100f40100384215071159008120903241620003000078000c0c040304038030a45010520032211707030000402010708000340c803010b80101181c000102240078000e41079000d80d080010540801d540800140f4503101032150000030307411000e078414112a001c0b0341e04000701c0d041200d100044a0b0900142102c0d500c161700710360070701e8420000d8030a0040b440e804000410030100781880030302c010b43c414078640e0800342c99090421003401c005441c200700e14400901801042000308048644512880100421041c075243d5104400b01c800168101c04440c501401e442d2540b500045610a0041111400103503000380300200400c0f0401000041400001c02d841d0369560010503145c600b8001d100382104004c5006032142e107403902075071144200074503547c86860005410b2110401c480e41240540b0700941d0034603256241c81d020080200124407400354048804400c02543d20380c00200280549000e0b00c0c1806410350b110000c0d40440c101c0c000c0f402c046 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 282921169 1250 282919919 282919939
    0x2220b030f01030312020c1c260114010c1403071104060b03070e010201021b0a020a0806090a06021e071514060f01080919030203041707030c06110115080a05070801020306 75
    0x120380308000c50149920941d00040c0342c42003103840640b821a00080c8000000c40c0360723043d804100d8020390701540507000300d03202030424135500c105028101014001c1000c55810b8842a20060340704401c0c0c80ca80301c0d84100c180c490b464200c1075080d9213420141c0201c5541480601d09038503401c1c68000d501c22101d00300c40301400c40d03e40301019206022991420f50440d98244050700c45200203801100781200d4642c00f0701491401401445140380d51504400300d940d00c4401404440754000403007003d01a0030080040e01c1d103850010b15010b4031010766150080748004141c81c0c040c80b0747c0f00e40da50b200d221071b48010000500704d200d00c0320320034404a503d16884519200c91035000c0d400342c80e000b0f9104209030266002c2195202600341c403007110b4607065005178800f04082c031000d01081c080c125869003a90041504624540d1174041c00e4005000c0c0c442048594030044036006e509403caa0821600a00300b111481d844981e11642c40003503c505842c5803203501c1e0006904041807080fa4061b91016060b0304803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 282922419 1250 282921169 282921173
    0x905060d09060527010510030b0414070603020a0f0201060609051302070f0303091b0f0b070503130305160504050f130c09050a05010f0e0906010312050702030102220b030f0103 77
    0x45034100c140c0c01210241c03075445880000b1a684500c5100c0c07802e5070304100680c0400c9010340f8184034043c4c00090940e143c102480244c41d82401c00004032035104800201c4c5a81c0e42c605001070303210071001100fa80c41000c2020aa441d01030300500000300096460305403000c60200100c0c20b0721458824407012440a2005121a0808803260381020340410009454416560348800107a080d50005400003943c0360203040030410341e0300001c3c5a000600b440b6080d003e0406507080e94060103032040e9040c204001030b46c0002c200c41031080e100c01510f06000c1710900c03543c0b0305005880e0101250022684006404081114581480703040e0282e43c61480d07041880d9154001c194550350103107800d546d250550b24000850242c1ca01a09214007102c61010034194902645c904500d0b0725500aa04451a03202c1041051040003c080d411241c001c885101d03d2400c114003912140314180019400d07500004104501910340c11311a4100400c0340030300074440d680c40d85032080e940800d540038117a082e41c41d0300400c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 282923669 1250 282922419 282922429
    0xc0b07021c0809010b09010b0301030c0e0f0f07030b030a05060108071703091507120c021009030209060405060411120417040b0d110d02190e040c020709090c090e060a050a0209010905 80
    0x3a210508000001758240402d001400e1000c6c01d038003007129014000010f2080080741d5003150010840c2d105d600303440d4104405251711100008040c01c120604a500090ba0301c4d1090b0041811840d0140583e00007420a0030002d4858100b4050203000e403084220000383c1c038000003100301c07050116002540c103091001042240b43c0c00c00d0710720100306060600922000c42c4940030702100110150301c0e1034800d40c54074410b100c4030504049885040c890321078403c2005da1180c00359254000300480d40080c040d620500050000e0070009944000250017040080411000c10383c101c5c00740b80100b00004511009001c0000c1038072643c000c54003105024407084282d9001038008101c85140000b0450406007644810403c0360407280b020036014400c04180c440c0943c1050040280c194150340501c80400c4c0c400010707585000500c144040a5030707820ac050140500000c1c490064000701c0d009100b0713110350200f81582c40c0026908056214904001314070039115904c2203880003c01a1541a01c8901d0402081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 282924919 1250 282923669 282923671
    0x307050d1505160f020102040e01030201030506041415030c030105370c03060342020c060702011b17040303020a0c1a1501110726010c0c0b07021c08 65
    0x81d1811020116031a003808a4000d1a1103280c2504601840080b0080f005286030749031240c6505591041009209503c140d54000341980e03020f090201d61600c0c0e04002c80d000300307030118404815010b01c00602920040031b118001610404030304403101d03004080c08060807110255000d000b455600403036a044002550211141c520001c01180c0354101075620090994800c414038900281d41d86209204010449400c064940e91407030071518003684608003209007402811041e1641c00626900c2c1c040043c2a030100c404039aa810300b0303034802d401d2103a80179010309040070300b044010051454881c0c4d520300c60b116526000800180c4d081d8181c0711038405070000d40c013042c2c2c4002000035000010b030220b4480d4980c0304210310803c03400d4115140c0515009641000c0c00921410004500b03991403005000080220a451203503440003c5800350301400341c7d0f01000140002100c0d428030000d441000e0b04041a101ca41d4011420301c0f00556454200300d0300c5402e14600507002c0a21554440a9284501d00305 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 282926169 1250 282924919 282924923
    0x60e01090504021201060e010f140d0215040f03260c030304080313050d0c110303070f08090f120109050106060e011b08041a030610020307081e09040f09060b06090307050d 75
    0x44d14982000540700c0c00c2da42c050300310800e0040e0070001084174400b0301803005d005000e00b180c904000c1c0380780030028642018501c8040c1c4074030b030805079103194000036200f2500141030a0740c1c48000250b0b07a1914452840d0211407822010540902c501d00d031842d640122880300d40702902440c55641d65075100c0640d038102500116072101e0380c4021000207401000401413100c10390319208000c0c1d459260256006036809040c078000c2c0c100303100c1c07100042c00d2841541c0240d03500c8040706032203034649008265105c4409044c50b80c000140c580002c160761041d401110006d02600c0240003168407081d041e1400004502e8142c00545214003000c1c81d1200c012168100c1e5100e2981d051801e5614140303200c20600c024100208103070b000042c0000c901e803203052904142203a0010f103050543c1610390081501501c1882920742010380013035204050107404a8000f030700010402c000035217074130200400405031802c003181c0301ca15000b0021114982802235501b107000040c001c005a41c00c2c04140117240d0740c11401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 282927419 1250 282926169 282926179
    0x910091e0501020f0304050c030c0a05030c120c03011b081608010902160213020d0b0d0f030807091d060f0103060e06060d09020d0506070909090503090f01050c250801060e0109050402 80
    0x416008400c44d90029070245000308028a1400d60420401d81801c00f9075010ba4415140840f08004580303000c940d180c00d4030b2048541d29420302c0290320403400c4c003400c040d02d103626500c0c0c01402110550f041d00c40395022400c079a110b00c5103a44a0100404141c000700030140401c2c801c4004200b0211642c0003400303401210400004081c64903804907540142d00b0f10583c21454002ca91024100075038400e604981c0c208a07901c1e20503030015120f45482100c0071380c0150421140c40c0020b90480d00616108009100000340b44100039844409031800b000c095032410700c5161101e492069541c131074099242541c0b40d8207483c0c2c40d2621448200a00c03a809007188889a51b110562130001d0f0f0b440340440605540210054007991515090041c01d590454118030000d070315001d407030360100b440013041c0e405210301035403403640c01c40ea01c100507102c500615204102a01c640c4440c40c000d03145460542c110700646910070130303850b81c4030040703942a40c6180c06001c0032860144010031400407144c101c03d411500142c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 282928669 1250 282927419 282927427
    0xc070519082212060b1207030b011a1222080d061404150e06010309081201030614040b0601030507050f13140a0803030a0506041509050601020d080f15060409140910091e050102 77
    0xa54180b0105900a860b0460389c08010040d5401d400c03940409112401c1089182440ca03c24603005164040d01090031503880020f80b8419069550000110942241d210b42c1c841882c1d20b0f1b540301401c0c1c503004508848488919601017800c090003091844072684054082c5607090503e40081d59030014420350405844000c81d00106890f0b500900c4800081030760450150304509080c4141e5010a000c0303400d08020703134104404100b55000464201c0400d01c1d001c0741d140c4030410101c9040c0590000001c05140006041e0b4030007182c000a40100c4a801443c42c1c0041017000400269100d18400d0440ca0b0b0410000200340e00c605510a1781d004100400025070913402070700b10381250000d60807400300300e9903410a203c007544c2c04012003040c00c1403600d08444146042013400725803010142203003a40030001d000610351070380ca607403d4070050030100004010102c0360410f80800c120083d5800c440a00a600c0602030655032805000f04098000d4640300f656170365405444c420ba4031206050340c45550030b00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 282929919 1250 282928669 282928699
    0x1420305210d1505091f0308071110080402090c03010506041a130e1909020d020d020f040e28051c03140412030e070e0c070519082212060b 61
    0x201c00d0001885201e00d80c03640c000c1c148030074000045c1e0042e050354169803107451134048030a4490240015654003411080c3c45e41c80fa80740048903411000303083c1d54000c00a11425803003035440245240305500840741c00c0c540b522450074a80e4580700230b004068110b0400c03c010f000341e2942911142011584c40103103854010406441c070545070441c0c100746010b034005004c5c00910051800c41605141c848101000030b84981da0001d401000103c000034020300d00402d03150255a80c020b0191242e1002030810301100705500982ca8481c0d0400420309008000345c401d034002c811040c03138140302182d880402440d40d0300000f000c070184c0403c0280c0c20303002c05d601ca0412a05914000200901541c441e1607801e800d104034110250070781e561007010186035808410204035041014280310b4020b0510000c507656405682065800c040d881015061005903400c4d0311001c00088400800070240505c403540040300700c2d200c04101c1680710b403203400c50015101c2c44080201d804d0b03078401080c42c48001c004080c00320b414 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 282931169 1250 282929919 282929921
    0xf140301120308070503060609040e010b13022a0a141906053103030213170606031204060206280e060702010b01050a021e01420305210d 60
    0x36000a881801c96190620800d50009815504403202c0d040040c150701c5c109010070001c1c012240c40c248120707101e0b44002141c078800c2d0305c20451000d000d400345036480161a603140295104080c848080800144000d01c0b01042c4191500c5984200d00030b0140c07014a620b440e04066a1004100703064041c4218108000420390003d41310715100e58004501c034500481c0100140c2104030b00100b0401c2100031a80f5020f01d84005605600da05080068569160150b00c4451400d950007148200f0701c04e0752401400d4100140c140c0c42080124119940c01600c061140c02c5d90066110303100240e4000d201261740100c40701c0c861884070521010001036134035020001001d460010f100704180380c00c00000e01c42d000d0781c207000d40c181e00c2e1800c0c208149080084480259980b80c200e0300b0701c1c0080c07030050394144800420b402a10082c1021045120840101d0079115004c1c0f059100c2c401420b000c1c506000001c00c264110340e403c9079004009050030290314240e180100107501a412a141800c00280d4988105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 282932419 1250 282931169 282931171
    0x40302091f0519030b0c0910121d01050f0709030f1403092806051305010c05010b030f07060306050d0f0602070c0e010612050f010b07032006070c02030c120d0f1403 72
    0xa90505a48010b04c3c500b405d11480700080c0c61009040c208000135059070b101c3c0007085005041c1490840c1044100d42d004400620600341d03511076416080b01ca464004405401c02030180d5a00b240d40182600c80c5401a00e0b803020602c0700502d6501d042d60858041561580c025032040301c01401c0d24035116102d4005202c100002c5248944600d20841c40807035254400c5183d00503150030309100c2d2815001a03102007118000380b05a0b41040344c10701d101c00030020290001c83d158800a800c480052061030045070b01d40d84c0700d02410000070320342400024540360580004100c282c0040d41401c0500e00c82d00c464010794000741098420705280341001588204100105000344a555507600e910801b4034410000d940c0081d0824003d82d0842c401404280078510440e100c45a050810b07c00b01c0e00060300b022005000300d40485194081d820400c01955001040700030103070310172002c0c3d64000018a0030000c0b90101035940c0d040c0f03035100059520a040c080c40d00c0264002a038100311841e080601c4502c1c02e0b13640 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 282933669 1250 282932419 282932449
    0x100306050a06032a0924090b130c0f030203040201110619150e0705030403021005010b0301090c02010c0f05030613050103050f060919020402130503010c110f03040302091f05 76
    0x2d915a420414414a400500c405a81008000c82d0810b1040d10910203140d1381d00580c1000c580e02c00c101c0e0030000f02c0514224801a008003084012031355050381d100140001940d903401100b0140b003040c0d4417261442003540c0c520840c2c403031741d01c180d0144000302c00a40004204034144210818480b4140d6002c2003854070400c00700700c0d000d9501c0302a000c00c100b6580a00c544d044109440901800001f01440060754048101e1418503141d942e18141240b41400082080c40458505030001c81e1140d06a00250705035030010070107001a440000c0100c0c229115004a440044c507040291001c40788a00c00a5820820051030b428584a0b10a460340442e103081e80121002d0740124802400c0403000d0000300e40c8080203001422074846401a2125030301d4904078001d1240364009a1000f65074030861031a409007e0241c002c104e0300d846a00701078411502401c240101c1d1151414000e261500003080300c1c02c1e254040d00b012aa070321074201281e60b085440e50a041c0691394254045441d4444001c41403c00c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 282934919 1250 282933669 282933671
    0xd0501090b0f0603040b130816030e092211040c020a170403050d030b030a0c0605031e070905060d02070f031d01090e0408070c0807090914010c0f0503100306050a 71
    0x5494248050101c031010360400e80075080e4008241220b036200d006803513020790061040c844c0e40d5560002d02d40d0b45c40940710020b12404001c5036000d00e00c003445d07040c4c2c4100e030301c40c0e01c0b0501441210002c100c60300f0030803240c006217000728070401517814442c080794024481c440c156007055444000e00160a46201d64680e0300146e003e05000000d004003060b18040c130142010580c2d107010b086840300340d207402421101c0801d00d520342504e800191001c01c401c0c60515007003410042c50a4540c03100a00d164419a1101e101303402031507a01301c0d01c485c010a514004c050a86a8000103032602091088941001c0f181002882d428840744000c14901070364004214841d594a0310030740388a00070f02c0300700b81408a409042100181c020b110403070f01c1400464100380c01c491665160910303445c012140840c607030090740c400d01510800042621081d0070050311284204211014111140c1c0d03018201c40303d20500c8400140c2c02150800032500036801903802003100c1c0412042d881e01c035240d00d0103440054645155003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 282936169 1250 282934919 282934921
    0x203250c02030d030c030b0a06020304121b031a0a0b0916051b03071a060f220c030e01061a0304020907050d0207050c040e0a2001030b03061501021e0a03050318030d05 73
    0x1070380c544242c184030b0301f04548000c00303581480c2000f9580d0003140a0b150900e103240080006000c03401c4441640702e448041c4d0705e80b82a46a1a00000c001c40e00012404011003400105207030341c0c12400340c1c1c0c18521003d084540c540ea00c3c148110000c1034030040e00000d12104002c40b540100c4629201203400c4800c00040d5900e0016142907040d010814a0b4009000101002e110103503555480c86c14600904840d0a60740c040107501a000082180111100361860b12500f01e0b041e0b031301a003005405141d110000c0207103a07170314805040007112207043c40800d18030810018005191040266810a0040c5025800e05100f008004201c2e402214151030503400401c10300c0c10743c0b0f080c0c01002c80c105450030191084190743c1d03480d400894880f0303400140b012304d82c5121042d164800e50105000010007401c844050410000211110412001840c01401703040c148952042c07144020b603000343c1640005242d12401500c0482d056003010740800c0302007400002842642d60108080c020350081000d0000341 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 282937419 1250 282936169 282936191
    0x210509011407050f0f07020621012909060a032004030209100806150303160f020f0108011203080a180b091c090303110a020d051c030203250c02030d03 66
    0x141c800020000c1d002c000707040059605840f12002520814091540110b454841610001d409802480c2c40c0c124120400410004141d909071010343c101c505038940780c103c42c846920400c400480c40d2248500d01030b4204001602803c01e01d0050015084510b00001d64071b0155891410f41040400800c041c0c94000c074050003546030182090350070400211052880d6450301501c2c640b40c080c000e01c0c2c6081d00d03220062058258600b40304880d8007644034200c03101c44100600c0c1c040c04031410480c05034007a20042c0e03c0780c450b550082c240355059407003050240c200f92680383d8040f240b9040040050b6030301a111030440004c0d4484040300840380340b094400124515081801c20f00c2c222080a03081030310a83c16100b080d02d030f90000f03811400d0380c1e01803810302c50740020580c80624000d00b42c2c400a40041854014400380840400c465407007800300c46800071a107000d45401c1f4103900050700d442c140700e1700d110403660008140c211400c01502c1c244c1401044c42d0301c10707000681049405001e0001090300d607494208 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 282938669 1250 282937419 282937451
    0x150624030e060105010816030e030d0905100b060702060c01200703120c0504180e030f191d0f010e0d03030605010306080a080d0b01021207080a171621050901 69
    0x150007030300710001c0c81d041d0b240c5000202844e070040c2c514043c034801141221611807094000d1004c03240401d003103d5441c600b100254000f05884d01d820380b6030703000c0c5441d014a00b20141c0900e143c0344070020001c07070611055808004056000b40c500c001159a80d01c080500040c0007003e40e040c061490681d80c2d2a1002c0b82401750680c00d040e902400c07030a00e08100c079005217070410250350547d02ca039920584410a4100700f0001071041c1d070407e604512000c9102020514054028240c09010040c01d100b94a048142500d880028111190440d522010070502c5410112801c0e200400149001401103001e68049104000e8929003034000a40f240c6d01031000d542c142c01140c00408a2800518061203252030f858080e002c1c200d581d0882640381e0015049aa2080058046a0302d0500310341e0781d10030240c0351444240c0d0019902d180032039011820b503100448036030002489003000c01890040c145030510200c49065100c0707422111050000c00540d540741451180510503106034000054421192240300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 282939919 1250 282938669 282938681
    0x1e0317030604050108061e13021905040c080705090d1509110a060912020d020f091f270b0109260c040b1e010203040b0307050316110a15062403 63
    0xb00c040d600c980f06011414882c00c448100c5201da580081c00702c0d80f00c23032040505480040402039840440c003000c04000c41988080e800c211041113608000c540f1003d18280c80040084a29101103003017403080300483e08000e034072222501d01ca44088420250380c030018030102c0344007010694100c107002c0040140750501c886020301030900e40c01e080003d80d14100003040b00c8414850028051241245e0a07401c41d2030314440202803040052010752686010f260398070b01c1c80c1c0030007240e2020212401000900d440803c0d60310b98081007261050107103514800d0a40064140c080308076041149a040002d128180760070302c0c801d03240481501c40c00a41c021900d60b89000403c9007250302ca40c1c03410b80b01070102c1d030340c1284008400c1e4180440c4044d00c440a00140d0541c00703075130700a02100c0400820081110350150095100e041e0740040c10b02c81442c0c0050407607101170007003200441c40d0711812848010840031001c8000900380040081166a120f401014040040058604000c1444480c42100c0d0390180101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 282941169 1250 282939919 282939929
    0x2b020304021201110d0908041d04050c010c0206120910050c07020405011401080402090903040e0406020415020705030d182c010608040206160501020c06100612020c06011e03170306040501 82
    0xf4400304d0042104259070f481a000800c14540e0769540560403c4440c00c160f4000748918045010661044000041003000480d0111000d00800c0780c0b076400b541c040c1c039800f44007a801800c184d041420b0300b403610011040c050b1140c84544038000d0403c0105c551070080328031980c0701c90909520740740144140010b942040e0002304054441d140c204074141d0b440802150720a8045035207040c1501e0b4801080d085206542014504586110400041c00b44c0c0c0e0f0000d0049074184524030250350400003003261500c1c05401201da00d50400070399648000e100d0750440b03d000d004500c45448095580301c0d1442002c105ca01c82e00003d08007034540310b0805036030076a1039004045a00b800807140c1f0f03083d40040c0362486005455400303941e040d0051000d02c2030950540e04c50344200c408461003070a004210282c0030b4030a1194100144842c00482d6404607103009403100990800c0041100342d00704000c2d03000c240b4091a1142e41c2c4c4881c07000c0000440c030007104001d040510510155603a040140500c0f081d03a03416008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 282942419 1250 282941169 282941171
    0x612020301080604031803060c0e10020606090a050709050a08060a0c020313120827090901090f061a030a0602030f1303020c010c081308100b03010b090c2b020304021201 74
    0x4200c0038001040c3c0307651050703141c07816054200380d42c035817420a401d454001070f0031345203810100218181c000751044008481281c6070380c3c3c7c7d1140050100d035590000c940b516005070140c00030540018036034101e16080321450030302d00480c5844502050004400c2e0b485440154448014013951107080d00c1460b802c40e003648050340c50061440f4440c0f5a00a86110700c03501c0001e00801321050000d144240d400d1041d801148200041e0248403a40c14072814007810703881001c1c1403001c610f50550510a013102546c0c09a403d00400000d40c0356000100041030a2941c0810315040b200c110355420303c0645066403150000507142d0a0030760300340041d1304004104502d2902d03100c44100100e40c00085100384d20200340780c01e0b03070300d581c04c0c7c5080b040074001d052402c114065840c4003c40c110308003003905102400440001c02240c545403080500340d460054105410400d4400451820340b00320340106000c4c02201161041c0070a000c40003040c0700b24104511810300c0c0d02006000451070160a0742c03004003510b0300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 282943669 1250 282942419 282942421
    0x20a230a060906080412030b040e0309030705010f09180908030c030405010605030601050105121503010e0f060f0105150d14010905070807020a0510020d060b040609031401020309030703030504030c050f0706120203 93
    0x40041d1044e10043d0000e08016490b00c4001ca9a134801e800211f05188040d00920114180c50031041c3d50350000034000d07109002d000000700c5c06500c5852041200c1301366607105030710742c0c0c54031070b503036004807140c01440e22425100c649000104020340d0046025012030700d03400d50f0360314240c1402e41c00c4411a403c10b07842900041c0040101d681d20406890388056600b242c10900d4840d103240c00d8010b40f01080c80c54065090108144038544042900e1250210485c00e441c0250b85003003e460b041c0703800740602030380022100032200410400030301034020103112100008400b104d40e43c24103503d200c241d0161aa0315107410422145650110302c40342c101074140001c005e04011039441517214400314070300d001440e60209451b00c8001070390704120f0040640c0c540300b903034a603104c10b0020b002410500054640b07189010301c0800c81c0d07905208591103520500b01450900200c0c3d42e080300275210180003079041001c054403c0002c40c4040c000c103503e01c80703444001c095051500601501384bc10400305e103604144180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 282944919 1250 282943669 282943679
    0x221010b04150518030d02030a0e0604030f060504020a0f12120806091b0912010c0906020f0304050907030f020328090b040f050715090302030c060c03070b04020a230a0609 75
    0x344001d044401d040c00c0030f503140d010701404a92407030040807041d6810300c90f041c414114581c010006004450181d510314141040d10400d104c15803265200047c09214842c803200086081da40c0b0503a0000e10003403a840d030707466036040910000138264000100e00800611480704010300540c54452291070760400c030344285051000128002c600802ca0303490740704017aa21034131720070050b821284007202c01800213a40c1001c074800540244090101c00d40840c441c107001081f072600000c0d40c104070041e441c0042d0300e880d0030310702400300c60782c400341c0700700c042c10307150140381d0000c0c5042d0003e184203202800c04030200d40c04e1a0311450544491801032009649800314400100d108203c01650194000c0c0200e1101001490024a04003980d480b12483c0340d04114880900b030340c0714804070112170088044881500c41c2c84100141480340250081c2c90368010812200050100f400d440e03401800104521540d941e038411a00940c001c06210718050b8410110002d403602d009422180370f40480d1919944041c201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 282946169 1250 282944919 282944939
    0xd080f061c02060405030a0c081203010503120d020403020a06030b010201050c13090b0f0603010305060708010801020315040c171003031e14070c270e0c13020c0109060221010b04 78
    0x110aa050195840ca080e000390b454900813a070080c40701030100c03811a1081c2c10120a01329080c018284240101d10708424a03031400c200f03490580b800280501503140705e11407540c0c0c02d50301540d00010340c280c00b40800070169032100e94503c01800305450125592140b60b00081c2150002048040c4c104402c2c00317510340c0180d0004c0a8026070310722003800a00070780c84000103400e0751502e801c41da80c45400003001004220010034018000c1c201d03901c0d240c49903622143e015080c2d02044903e080c3c00584543e032104603141a40000401c0740341030a0101c0b80d180e89540c4200300d4842200c0300c06146d030080b0320400804d40d01800344038000c0448070602d0469245413070300401444181e0035001142070045030200510070b0340344a400050004c3c603c1c41c1e190000c0d035000b05210401201e80c0103000c520f0f151030a030020502085001c1032034001040e2a1f210760034924107400940060300f040e0b50940da10032020740000c3e01b030f10003040c0340d4040010308145403894550000260b2416008021410300a1000300011041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 282947419 1250 282946169 282946189
    0x507110a150507050a0c09060e0c07050d1b0b01031101110703050318011e030504120f080105090c0c030c0a050f190602090f090a0c08060a030206090409050708030c0d080f06 76
    0x30901c0d04569a15103130800900d07222440802078800c42035140d0000d05520710341e02036012111542c9800070a55220005101d10303005028014007141c100100c05030001d07100300c40c0300d0401114008503031254489a01c0301607010409030002c95441d0035001d240404c642c0c1002940f102100740d400141403a90035a500d513610390240001180d1028482c03102c420303050f8001d115035034100038550310748070410285c507100802401d0291004d8511255041d4560000c51040c1003e4600705e01c641c441c0919a4a00400e00070f044200030b040040c050030034001c034a40344100f031000b03140140340c0100030102c09d15681820b5050808890b20130313055500440034408040c1124119002168000b02c0041c0c071a4102c801040113010075071065a4440c4100c0c081042ca03040e00d40c004080400e80307540c1d40c1a182d0300c24050240010391404040c1d4041e0060060038101c1c6025049100e465205009403002d4a645260892a58000c0d503120012034029000400c41c05511440b00ca503c0810a100d90920b0709060f004140c000f54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 282948669 1250 282947419 282947459
    0x30b0f06070c150302071b141c140309120106032307090515090901050411040501060c0b040503120103030203031902040b09040c021f0902030601090b0303030610090b0a0507110a 78
    0xb0f0107030300f81916a03010764151075020340c0009581c00784040c030721400d60f0292928080c0e1801d59007442c1000b0268100644044a540b810916805071501240c0b16000d140303d240d803030920240f00801131040030340c5415008014280050002254190852404040b1040d10881482e4504502a0900d451050008400e011101b1800d4001140d4488a00004d030f0448180c03540c0748c200036050180300c200c1d041580300038421401011240f402151036000c1206940003842440c00090a80300c544000c1003982440907081880f400c00c89242101c102207000c1b000b84240d10607005030b013000c42080240f900610690b4420303501c001c402c514080c18034600788141c0c0141c12045c0d0060740e4402114800134001c21101d0002006100e01c4c0003072250180000300070b81700c481c2040717001c1d000380000024038107100e008002c0c202c240140511b055640d8041030001450842e0700280402c01600d40024503204800000c088500c5942e452990320041410401500c9100800281c02021459401c00a02c0680440400e10700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 282949919 1250 282948669 282948689
    0x13080c03062a0310080105070903030f1b060c020a0b0c0301030b010b091801090b03010e1609090f08030403031b0c0b040204021809010f0f0803071709011e030b0f06070c 74
    0x105501100040c03100280c207420b01d01c95000001d000405106848201c202d402100091007595a590000ca40d4031100d0311008020500f10040404418010b00d012039103020035024100307150300346869900a03141c02c901d21740d0146e000007005805020b00c071080c4541c05103144200e03a113554556511001d0144052280c0c0209550105004600d1b550740c6241c4e036040340160408103003650b120b11040000300f5080b02690b10941c6031080c00d003100d02c004280010710600b4100d04004e654945610350b4058036070000112458440f21b48420002040700001d1401365000e980c00080c1130304488405035459022200d0311091003644c03032181c400590000c030040d61065060700c0158503900100c07186c013290745140114135804030114002240b450030020108003280c000542d40810b0b2582e8640c07131a103e10501070040c03ea800c41c1800381038200d520b07400a212640040c5072a080d186120805698014101c84c40140004e032145e14407081031070034200e1101044002c076005440c20600b0b50710300b000c5081c14402c40000f4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 282951169 1250 282949919 282949951
    0x4030c15260a0207140105090c100e0906030a050609010c14091e01030b15090a06050313081c090807120908030a0c0606210c0f030f06050a0605040204080313080c0306 73
    0x42c41150180c62219a00181c03400602d00e840000758041e0504840d80343d00c81c0711b505003014103071515482c070148260301c0340c80d130a106c0c07a440c806005d15004000c22003a014829022090000340c41045001e00c40c54500000048029003d42c000f40306074030f00c0d411a600e580041c450081c0c999202d40502c0100080e20241da0101c0342e8140046c0e0140c4400940c142d8401c0380506021090041d135001001503800c200c450911203611601c0640e003600041e11503c0d2002c001c03120b00000550390702c00905014132901d200fa0303013002102c41e41c042a5030700c001e030850350401c0202e4000704000c80e402c02c2003201049418500b81c0c407810321017510f0303aa000b1440440200680c90000d1004d100541c0c0c001c40242060482558600900c4e02101040e0540a1011542060400400610b601c4100d0701c003019641c1c1304284454480e5103840c3e141c080d00c03000e420b14080c540d40e010000f8090340d40b80700a10051901102070f54454200c0c82441c984100507074440b0300c058100c012524540c0d503001c61b16690011a0b1070002c449 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 282952419 1250 282951169 282951181
    0x30215030a0e03030106120506030303090c090a0e010c05040303030f0504020f010507230309120f062e0f140102010626071d010906061b030503180304030c1526 70
    0x15002c44031008049000020011410584c40710410041408120b810b00017030b124601815900d110441d940708494100b910003000070718080403d5900400c80170000305000c80682070590031103013681c200402240c00040c04104054050003086820800c4200c1085645850f801089800b114a000d2a0401030006911070030040c2c0c07403c00040250020040c42031a5402c1c04842380d4075403205c3d107000c0c890b50365881c4400d006d00c800148182680e00c804003a005544134520701c2e49280c082c8a100c9100d1043d00c01c6216000001491003030004c2c194081c2c0000a24600003403460850b034070003a070038116410040d0070702c041c1801400071404c0380440ca00044080e0186030081e802c2c01d546800121a159107200b040d1044250130305118145c5401e135100b04585582c1d04025515401d40304116070000064103100004640910007844d48120b07510300441d20140201d55407130941d80941c0080f540101d20b81c8041c80010081035003401d06042d2800c1425805500b0390000f244241e000100c060812a44000218 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 282953669 1250 282952419 282952421
    0x190203070215130201090f0b0702040c030b10120606030212270303180d03061805041b0f1a040506190207051c03030506040b060d0e1207080a0e0a030215030a 69
    0x2004119a204000d5903040522091512a240301410707170016014440120350512031000c4042115446010700c0e141841c2582880b0142419400542c14180d6035480c0c146142c07100340001c584500107540d2480e4045101510f103044500c00d4005504140c4144605400700ba68100301c55004030080003126213540c41809000460b03581124400307101c0c000842884600302d104901c4c0b1124481c42e005031586129101e83c2202101d50070f22074070340640450f0400e130741b0101140d0710040d0418020034175607502001e50180c204c0c0503c040d82c4029800309040c602041040304200003004001c0580310000d203030a1400300065010b020b402d00c4e10303034030085805c241ca8409000300a171500406014250301807a0000c41281c44a1841c001e00a502090030a07000a20a18181c4240e8000340801011941000400d280d00310081c0030350444112030b0f01c240140c01c0c4c03c910500015002c00c91041c3c0d9125070f6403200342c2006082801c0203035034070700460940c1010310040e5910030340c1509012403061110303181c0d611826044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 282954919 1250 282953669 282953683
    0x160509131721040b011202030a050303010602101d071e0e18160f0b0a020f2b09050108010b090619020303090106050604080601060f021524091902030702 67
    0x14054041e0308080c01c8403140c041c014041c1c0390004160302c2a811103103160400284000c0710300800300c4910310010301c0280075603030b291900d4030300181c200c0b2009080c6a40d914030b03550084c1c00c41e20142e4414090010103030118050343c3d241900001005061500d40c207101c555403011805000c01802000d040c447c1c0c0c80310500d041000070101000422080c1c10407242c240c0380100c901c05988264092507165001130140541c17034404541403031296042c034916000321440190002d00c5000c0860058800d895410082003044040900300300a0000d207882c404d8154003000c144550031141801a03644041180d0f81c3c0180744c8504444000f43c83e60b070340e001483d000602c41d201d001002c50880060703460083c2201e5000001d5403040710b052000300407a588a10410400c1e00946c4924602640301ca4014028a4031820f09040054070754011a131007000010300c0400c090f4000c031101c0c807080c400148811a800c03582c1c0820303c0300c1001514000f0361820004100d5882c7c0c0c551a04580919400101050f0303290710800c015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 282956169 1250 282954919 282954923
    0x405071119020a0e061f02010b09040b090601230f010c0503030901060906050a0b0d020a141207020601061706091503010603061a01030612110a030609032016050913 72
    0x941d194140a03941c0c0c410300702039010282e00400e55200c0c0800d54182c03115440d4094900100402401000e501081c14910b500c0040c03a411552100d0985600791181240d46019a204030742e91003607441c1100d0b15074a8000144d0211502c10740f10401c6506030703112020741298555050740c42e00d840901260040e1500b070524030f001000f900c4000104014007074107512240680360380700d0b07003480340342c3c2d0307a10400080c0b806c0c50140c0c11422904100c41080100154000d203103918290814804124a202010756550040400c92032910007080030401069410f0003564054005418842e00420440caa40284c03550000c10711400b880d0a003011420440c0036000340b03000502c000b80203215440c0c403494100301411507406041c4001d49007088800d00d56009000e120241c0740c25507107800040c01c40c0c0e200c508462407488561500840701c00c001101086180c0651300340d060103030316216001a614800fa0303400b000318a01d060926003000303c556001208011240b0f007291422940d4035843d4940130960401c00c1a40c00d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 282957419 1250 282956169 282956173
    0x1208041706090606010807021f11030c0d0501060512150d15020403030e0a030b0f070516031d0109050603060f010e030601030507080609070e0106122414040b030a0204050711 76
    0xd100009040021024440d00320802038076403d031103110064903c842c054411002681250b0205182400c901075461300020010402142005104200c40001d40c0b0507a40e845040070006070b0540290410300409005160303600e40903180680c5c0d10032210900c81c0c0988010303089170400c203068102c1e0360b8040c2d0349210036400c4101c0c0d8045070448071390007000394001d2000b07c01040242002c2c82c690300d08114084c00b02d0b50001803003581503540c401d01002c1030310018644014880217010658104804841c0007146507c2030301c3d4040342c01003201e103a0001d00d00401d400350401c110000240890f4440f40c046d6504008196884201480c640c8010f07900000d00c001c046405125a000000501c0000140c02d001c0f10610020346980d40c40b40c41900e41c41f600540114806441c09100400445100e24109401904200c030001080701031700c0c100c52206010507101050351001808140441441e00c0101c180040088504004482c58000840d4850035a8000039106954810002e00400c0c0142100880302050100f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 282958669 1250 282957419 282957449
    0x90b03030d1109030c04140a05060114070f030813050d031e112823042411010e1c03060803030a0507020d090303080f0613020a020703060b040b0604120804 68
    0x16600c02e2540000140c144a4403a00c40d52241c203042c10b2180041c0390060440034500e903a2140c0041d0043c0c00090319150400c01c00c0b8031080c501040344006851018422407040c01290383c1170034001c00c00311000e422102c280020800c1080040e10000d00c0b41080307816401c1c0400c5d940c2016010400001919900030341941c02c003002040400c0480000380180c040c01d200e607610850350321a070031032560300780e040510204074040c0d407084c540c3c1d00c14401001700032501c01400f840c240c2c0b15603034940326400ea000c00c403059240c80f808000c0c40507040104114a804000c00801040380301d80b000959030041d00100e50300c1c140e400d598182d0703041c0c0b003500701c01c0260000303400726503880c10821442c3e4010541240e00320010701038080c030140820b21408801045941507601c034102c68842403103402500201405071a4844403400c203141c840000382c00640503000054018101052840c145801500d5403c0c0b49075200da8030b0320080c00300555401054506489481703880729003000d5946007481c080c0c030450304200c269601d030003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 282959919 1250 282958669 282958691
    0x50601030b061c0b0a0321050928090f1b0e0607080c0c0a0308040305070527070e0306010f080708070b0415020a0602040320120d05090f04140103051b0109090b03030d 73
    0x302c47d0050f480d40c140401184080300b20310480d407600417054080d512a8405040c00b01114054600703001701200201003042c429030f10454503086401211003c01c0264031150940031080703041e680350880880508100c08184c7c079450009509111b51032005000200c0403038480c02c2c0490821650b5020134000d0704c000743c2c0903100d041c001e00f941c02038441100d0520440c07002040d03078200408103003401150a091541588a41d00d41c507003500200900c0c1c0f40c01c1140c0c4082200c2965000c102c00340c000d161a41c6072050240c103100c92a410641c0d150002d1003d54004d4100300454000e035021a070450751701e034100d0000c40e507078050100d06007010080c024242c103002103070100030b03c01404032414161541c0703c0c20308841c44002d0144421200101c8507880350f600f0801140500d140508001d01c280c280082014481c4034041e00040e04480c3c5040640140e18030610040c010031504000203804000c6201d20b07020003a90b0440000d00f51039903800390041d1140c0343c1203d007126031020404c0c1c038990f12640200b401248164 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 282961169 1250 282959919 282959933
    0x7030e090903040f150905090a1514120c06030f04020105040f180b010f0807030b01090302150a140403110d02060408011d071a041211120d03050601030b061c0b0a03 72
    0x10f00402d501200340d08400514409410982401a091038503070003446c40c5818200041d2000c000c101c46041520b0b440300044503d482d8142c10040c0c2030896140266a0300c0209014024464481c40700c2181d00a00c0070181d141e80d11015a079000c0403918048030039035a6440121107901850340040c00c01501c081010a0164080d0709017280286d019000708160760b0f102d00112095034041507154003045600d40800d100502ca030308008030f90501810041045981c1e44d01240d009905650300e0280c040c0c02066503a01c40398030805610395010301181040c101411038462445404101c121141b140c001000280215103900d01502e000340000402000807002c044c6200820035600d2036400854012801c0206030950040c000c500c0011005000500745800d104064000003c80142034600114001c0c1910480d40c0324480c0c9903005001e20098500d074100098081c090303d40141000341032600340310745000d56846107400e548007800144034050500c848041820001c08100c0c50702c0f40c00c03402d200c00100c288056 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 282962419 1250 282961169 282961177
    0xc090403090801050f01030320030f0705060a0b0a0e191104090506010f0f02120906070203160311040c050a0c0c0905010b210601050307050c010b03030301121a0411040207030e090903 80
    0x1042d00a118560702c0c0c0345c42c1007003294240002004612481c103004012058100c1c80c45100d440c0c007044a18094000f601d005450700408422070b5281d04c503008105c0061814000e10682d04d405899801c00b00c0c0c101014184c0410380100300240c02c054070040150f02c40c0c41600b210385082c030031114255490361a140440301034081104c502d40890784030001140d1a502c500d80c003401030720b80c1707a020b0302411204550300351195015078900d9030b0104050000e5030159034180308015201c1601010030800515620f010001006c69901c0984140d241807041002950024219841d012180c40c18120368400c0d0702d4001e92810701d6400c00340d161441d000000c030b10210020010445240c201d20100402198020896101308045502500180003400840d40c20750064018040040b060400440c0e014582c501003860341c1c009a11403074800c1c01d5402c91505000c0c040000328001b640c0740a00503101d2070b00b92908030705941d44000c04c0e0f0281d40e00090040c18140f0a00c0c025400000042c4003c07402d0900942e01036480e04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 282963669 1250 282962419 282962429
    0x308040b0a1e0813052401060233180601030305030a0b030102030105030d210e071a03042003010b030331031104021b011803020d0203040e0402120c09040309 69
    0xc01103007111826400c101400d103400b85544040c2a0b650355034064203203078560740044449104038031101080c010030041800d2964418012245550701d00280285403d49407601103840242001c0c5440117000c44003548200000460020f0b51707035842d8a80b541d105902d1111040b440c900030740001008040d4460011400340480900900c4102d504404143c200e00c02845000d5040c0d001120b10800103006800c0440d0141c45c40c1074006144001c140b09900b55000e400d00d41ca200d8121000034082d112044804490410320f010800d0f00710b2415940f5010849074400240c00a88625071010003295002d401205d135403070002e426207403660310124584844880da005011a94a200b14540881d00070500c01401142c0d04021101807044e608000d01009512010711180c5c003c5494a14000c482c009000b0841c03c05207010a45001401c2410002e007007103991400542150410882003044400386020b00707400c2038049802d52940458200b01e1442c040c04500d6041e0040300302e6007004103054006c5501d2003110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 282964919 1250 282963669 282963677
    0xf1b12061314190605030304120218070309020109091b18210209090109021518041b030507110c01030e0f070605120f0f1f080613030909090f0314040308040b0a 70
    0x500d52403110998102d0300419415030301c184010010a01c3c0504650741c0d0900160240c07130740c801019000843c518083355807102082d11803444208550788104148003c10801c1010060002028a09484400e002c0800010012041d0f50f040d1320000411004004001000c0c2c00b0203a40440c010f5000707014400c0a0a0b4803c140400009e401681c060040309000e50380184014159007000c10380d82c03010740090029851014881401e402c00d1746907849590110254a140441039455503403008050f6040201744404000c80007001c11160100010300081e00c0d9400d083c0170500400c0400c00f203240c402481194815840f9500e400596107030018024800010712aa03c107125944800e000d01d4480c509071025000202244002504c0031001e4003440714000300480b612541d41d5503200301c580382802c00d0b9000d072601c2c107810506804054010010344c0050955240034401c1700141d40300c101500d014430340b015040c88031107420741072a0540401110043d56010700e1117030300d9036151400c910194210541e020086 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 282966169 1250 282964919 282964951
    0x121308010f090c0312050c0d030506030c0102161202031002160309140604031112070e090f01090b06151306050d050609060a05060a050f120f1b12061314 67
    0x40c44a4041c03070b031990741c1061014604904c0c640e60100400400799110040040c10700440307030b1041d0207010b0900108442e548c0815141030180805041101f40c179003050555008601d40350307500700d40c3c10b145005c5640913400d60792540454000b280c03c04600300b04800f038a602c0040e0310120030900d0000d504102d03000c2d03518411000d071103a20070031480748a0140c0c1c6038481010702003000029401030303001054010140140040f4580c036400c007843c05400b504680c0784400c503007080200e83c040c00c004200180e111803001b844842034544403102e02810142c20140a038000d0301c0c42103640e1110008407004800d2240c014030403140d503207200900541080001c49089030400c3c01113409840c2c251005409584002d00c09a403c61030041003140c2640801c0b20381050150500c01c0110081001018088400d10070000c076031645852200703001004002401400c02500200a011002c0c1e644c2d420b40d00035050989140603613840d00000501109100000c40180c1c0381000450111040b0000c1d40318050b4200610246c0070f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 282967419 1250 282966169 282966191
    0x905060403110d02060403020409050703021302210a0b0307060809370c0801060b0c0f070810020306220e0c0a050312070218040b0403081b091212130801 67
    0x34421440080c00c02c0c100305248422600e8480c401ca14402c0c8001d1000d45010354a40c003080c00e4440150b000d0702c060308156010403c1d400c0609110309041c0c5941c10451902d040d011200050003d9a1030207607080515100142103008594084012518024101d82d145036442c84010100007007180d02c0da80c0e902075107070280b071050300801d0b51030010300c0d0031445040e0407101940810b00c040010348080d00c1c0d00c4a0842c000880200a11507100a0328460740e8480c0d80d0b1815407038452511148661140f11a80407110401010401051240008145500c00359494030703980000380c010b0070001c028041d110780c01041101100c1041e4414424405c4220550750740300180c41c20080d41c1034261044580641100148175403455a40e001001e0322807008100b0040d00780302030f10506c609502204d00b12441151142808103150b08038440503407040074050a82181d002e9201d103036240cad000d01e8554900070740c264080807004003810b001c2501c00421103110140c46118045501104030007a10030318016510744013070018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 282968669 1250 282967419 282967429
    0xa05031e181009090204171506151c0606050a020f0109030509101101050106090f0e0c0708160b040506011514030117030c12030103061416030f091e030905 68
    0x40c21010005079140307030034140c0c020310040c0891100c1000800c60400c80104200c0c0840c8080d02c090101484400342d211072020709940f401c0d041c51800062075858000704850340e610950032008070084011015200d95841044000000391220710400702410640c01040465120700a07104403030856003115000d1414041c1103089410881c005000120104400400344c00c0c000100b00c9060498507102d604d21070000390190171240d081c0c21000c0010400c40c02080000302d0400400c029081c00f480c03418407400d000c82800002c0c8a16440240500e01c0840d01c4441c2281507062080042c3e0040921140e6203007501d0f00702e403581000d0240c0b00750301c6402c3c0d50280c011407141401541c076059050000b40b640c1d09115a881c00741c441c84810100130300c0100900c1281c45028803400f083d804010700059200d50451a104080d00e4414400207084078041040102e0340c0c411a012003c04503003410700142009102d2001005884c5a01010341410320040380b030200701d052070280e925464001d075500c00d41c807511102000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 282969919 1250 282968669 282968677
    0x1406040506010f081012080702180c041401090e10090e010c08180c130203090d050a0c241802090a0504030c0b090c04050405060603060a020f041e03050a05031e 70
    0x540003e40c100f0079507841030b004020094103c10740722080380001c3d0b42e0740f808010603013a1000403581c84601251000860404001c41c41040307901141b607030128540050942c4540c0654460710f0141e8030244942c100d01d0b40039181c104081d2103c4240400c01d440c181100a000c490320344521070301179181a0b204170040b9018403490005030a01e80c0c6800301a2903038141c4402580c081004208503000300a4051055a60f041c2264100c040c50703030300540c880c5001c0041c2800d021034591207005220307040000c500356a80c801c0c0a2402c456001105c440d00194040f0a00064801611b00e81c607841d01e08500000c03242b01485003081070a108543c40015035580314000026078000ba034005010841e003420715400512181c1c060350f4400309845c00c590a0000100c0004d0643d4000c0d00c00ba42d2640060082c42140e040c00c0c4210f662000e01008198648940c0c0142114540b25038030401d40144904100030b03a6038401950580015a00b110403a00c10120b142400c60303c1e80e001d550b507846003e14841815850402140036a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 282971169 1250 282969919 282969931
    0xa0507050907021f02040b0720150f07061d0102070c0510090308160506100626010b0c070305010f1e09080a0309080d0c09060905030303040506060d05120a0314060405 73
    0x144c902100b940214141e0421500700d02128030b9000d00c80800c0f0718a1103005070861500462051504800e94405c240100d6140c1c4007850003240c0d00d4850300000450a0100c4e03400c0070342c1902da49d503140032900b00800204840300d662185e5025103d22103100c8a81500039040750b0307010395946a000c41d9698100009400b840410300086282030380100701041a002c0644401607800d90324480e8400c40c0c0c0d5a407030400c034040b510001000010b40c801c0c0410356222841c0c0406c51100c0d0160018000307038043c25925241c0520401442c0c540c00500aa4071400510011004540c400d0003031250b241d1a20340300c409819404103442c8203420700488881e9604690107201c2c5a2500888018038040c5408405c8010701002207007036410341403c02c1030050090143c8100e5100b5451507880510f02ca0601400500c91107660344400d00c60b42c404d00c10720021a2010440381d030800400c80e400004d07060b540ca001400c0402a0a2401601c03801003140f01c1d17507070781642104015400880185815503034070001c00c01222000d40e00f0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 282972419 1250 282971169 282971173
    0x30e0a09150314030415120c11060f1302060705030322170729060f03030c070504180b010803040806060d080703080c09040f1a040507020a11010306090e0a050705090702 74
    0x400119050200000f1200840b00540746010744640d80d5520402c03500c032000000481000300c109041d4028484c00b401000e0602d410f400300d01c10181030607905e0002034641c24214850a000c9030b904004002ca444000764060b2201740c032a2003d0a00a48980040b151141c4803001600354910103004414200c100340c0c1d200d04595645807104968601d550000c10b070803a000340d1005440305581d4240200c0c00b0341e0101000e8101004c2c6800410710598443c0007007414020307401440400003603400440c510054070701c10b60b03001a0740c485803da91610325194a2018101030070050012400810103c010300c240c80969040380d502d82c490009011031100c13041c030080d0081000307009074000030307101ea1000ca80205001c0344980c1000c180d4000141224106140105041d40d0f44020309544600060804c0a00c4000c03502006540b81c41c2d8406910340e019510010100d0b490b11608000c0c980c06a0301c100050100a00c04100946400700c805903035030a02c810513152407080781f00c005028074003a101144113103204d40c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 282973669 1250 282972419 282972461
    0x130509040c0603020f0d06080f07140a180f18051c0c061805070f050910052416060515150f090a03120e19031707031803030e0a09 57
    0x40124005d40104c4041c6588540c10490070701c0e401c40c1806404060300c0520090030009080b00a160b24108459200407120b9082144030a100d60706c00d409042142c047c02e03444815502c0340764070ba40040c060051140c51462400031850300100301c01c00d85d07403049440b65048540c02c80e450008440c043d0780c41c208400004a9552280300000c0e0246c10002d986036542e00f1101d0781c2c140030b0b5503150070503080350070150b148404c280007040710707280c1402e55030b410a415401c07038110b403414000400d00b844049022140305070403581700700450306021001c850300c0c0c00414964211030300c0c0307a141040c0600001d46003020b8016004000b00001c0c0390203451003007800c0ca4174416900c0d00d484213502e240a03800ca00c078855800394030110000041504017518540e44c2086903500540501c4038000c010540104200b840208050480248001000c1c940150700804039600d066032030382c809141c1205c61084000c03070307400c199414000005c2050740201640030352501c11210b83e5410f83d1948111030403514030b03250820700100108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 282974919 1250 282973669 282973679
    0xb06130216140c12101812030915020705060105010e03063306070602040501090b0c0d0c231c020d140d0207230c120a061e060605130509040c 62
    0xaa0303081030003152002d0f5a28072609000140c107110001100e00c42c00d800002c0814901069807240340c0850a4005100002c101d140c0c888a6005911442d014280340d50f694401040c0920103200404800d051501955120707544d10340310f500c0700e5080c03050710f000c2400801d20006510300032400c40e1140100303144200f00c0e032a404441d025002b6a903d02989041c80458012a00c3c2d11100c0c001c0c42c20300d00400b4056a40e81ca40310005220050300e51100c40000024010346880c01030104081940100d40d2070120003911a605009008408107000b140080c541c0080702c003c80c00d4007280c800c0c801c1400b402e4a810002d05001c00340d0300c0c0d54404000c1800114628005498012040c020703244400c0401c100606200f06580d400040b540490000035450946005207005c2d040c3c1007120111003001540d070924581d0b400f0702c1042d55074600040043c078058035045e003220216603030641d2000840d909842804803a5940501800035840b11040e524080c40901300405d06081000d1094050340d44001d9041c1224500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 282976169 1250 282974919 282974933
    0x20606060c011b0504051f05031b0904020a1d060403031205100f1502070902090303090603130803011d01050301060605250204022d1213060b09040b1906080c1005160b06130216 77
    0x1d42b44030300c0c0d50b103030520032000a900e03036102806108003140c43e165001c64801400080422b6804a4a48682002c0100340000380c0d014000640326194004080ba080c0c464000b0840c90740d02c00d4010030340800d80c003900003c01d83c0507511261700d0a0141e4007500c030484d8403409000164441c250015826900070020079a0a080c58030055074401e14815441f031180200e503445400560003a80501710510514102d88042491030016a004010880013040b803580b610350054803600801d00c0c840c1c80e600c0c480c101a0400034440020041d003a900030800c660701c00e403040012803916880e101b01c00b654144205031741e5001094038111102c3c88000c0c184102c656481401240801000000403035601d80c90714505503260b1106940b25001d64031420201c810707843c042c0550942603910704542d40c2007a0400704100001e81012420302e080c400c0c1070b03424412042202d00203503170394440c0d030f058203210140d10507551003071000c2144a940640b904641800307140a0b9188004264098680780035002c144080100c000101e603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 282977419 1250 282976169 282976201
    0x403050f0a02070b070804030203070b12040f0f0c081015030206120403210204090b0d03080c0c070f150e24030406060b0711030607020d020606060c011b0504051f0503 73
    0x802e20440711255240c1c06013045a030041e08003119040f0000c80d00b13100310f15050003505c003d04401c1610341d040c0852407210412501d005030021740b040000c0c0c0041000d1001524588a5054006140348082c035943c484c0c00350344810041058105500d00007070303101c00700b16007101c203002c8079001400c0e1418800b09004018580001030822018065041d500c00301134a107005541102c0c0562010060702c40e403500401e142514000b00085208000381d550410002c1d07000031030780d0340005480040310740307848030401d400345810000c3d004401c90002e00c0c1400610081d044000030006a1b443c0d0701c03141150040d0062148841801e03941100c240352804401a6130f4100c1805181d01034080e850201d94a640c80992242c41d502c8444140d1b0081d014803070705c8117981070030410301c0c1d00210f00344000d00100c14000402500c1c1c40d0003030010b0f4414030700000d03d204615001d4114404512400200c409440c0721400043d00a60091084500030080f03200c4040751501c0c14844070340300910f40d840d00b40c9595645a0100e41c0651 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 282978669 1250 282977419 282977437
    0x60a0e210a03061d0103110103020306061602031e1f110307030509030706020c06040201030b030303011a070219060f02070602070f031101111b090906060105071b03050a030c0312050403050f 83
    0xc0e491500003114003100d0b02c561135100c42c203014000c1c9035045040480c402041d0800c0c85043c14010418441280c561104440305c40c1c06000003100f04a100d840001c3c01d020300b9514507807801066004c502ca414001182c1741d000c0400050213501465003040724003064513500710b41e130354a42c00c0510005920500130b404c02c0382c1c0403507a00180c0e850000b0b00c1c0d0340e41c2c003207801000d28079010342d1108c070400045507003600c00c40708040d0741100150305540c5405290b004440002d4601d0790254130115411045464068070010940d9142072072015064456400801c00d0003501ca401006203d91080010742e1800441c15005030b880d0082c028410340d082d901c0340001130340c1d150780f0301d410000031f034002c6440600b05000410a8808008501c2100300502c000c10140300000f82011000c0d0700b0810034004a0303a0081e084420f0540e025501c000c041000271000c1e1005d4000307a1000e4043e01030040c03074504042d4031403c48a600c3d4400d486e8001d20480706e040346070803100115001400b00c0c07c1084a01c015007088009404405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 282979919 1250 282978669 282978671
    0x30702100903080f04050f15030105040c05070605180d0f0c0b040f060c03020c01060e010806070c0f08162325050d051c05070305090603070e030a05060a0e210a03 71
    0x40da5aa0f540210340c0c0c040b500c00c2d540980081403d20640c070300140d01c900340da40f04440c1040540c07010f0114000310322043c45218031883da244003035401180600b003664002c2d80c001c00c0c01c01c80341ca0031a070b58801d282c01840740000300b4002d010a082840b0701801e000c3c0218226aa24600e04041c0c2e9070b1211500c08000d40144c031078480b0920004001140e600070b24610600ad81e0317000d41c8800c003d01c0c030a82560b626420800c0392040b04801408902c00004423103500545610306040c00241604002200c0442c5041c090307c00200003070160350001c010300b91412040c0c840e0a101c445ca80310201a44030980b85281050215008002d802003084080d480c0700040840c1080840c8140e0340d902c2c001003506492220072503030f582002c04051261005028214004009414460b1800302659002051031250302c0410740308202c0400490784040c400d6900604000006d400c80340c4036001070030000c2d42d522044481d00680fa084c001c41c0700d082900820100342400a0380a030500040304505d035011903030401a142002c01d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 282981169 1250 282979919 282979937
    0x90f1103040f11060c160816060516080c060f011a0414090c0c0a0f0605010e0f011a090604090b100f0203090f0d050601060c0605060307180b0d0b0109060e1803070210 73
    0x4003000b400902650441c22030300c0b0840901c1c1c02451414022510b20416000e80003c404000b02703600b2800b10b500d0500385a00344005072586140c1624503024584031658144507800402100c100c0303010a040c142e074519101c4051180c10080b6031913807441107004103c484400c00c074103038041e030515200c0c03190002e0140072a241004640d00032240780001d10201940d031106542191001d00c0854481c26000d4a036410200d1001d290241700d5024404040c42013030529807004145402080091040c0c1c0c0c000782005142c59a1a0369800e220400340500c520982d2041d044074440320682401541d10582c2601c00b90099400c2841d001c00700080804002d50080e009817502c20080c0c0000c1e010710002c4d018049130b480e503c103140518104007040354030040c03003180682d112108c1881101402c1484195261a541010860b02c1303429021499800e01742e2001050121484004603250945030412410303036194241201942d9105602d80007203042101816000e030f0402c10441c4050b0074070041c46000c00d40d072410b000743c3e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 282982419 1250 282981169 282981187
    0x7080106090c0f0f140313151b0f0201090506160e010e090a1a100503160e130504030201020c0a0c06030b03030304200102071517252304090f1103040f1106 68
    0x102d5802203c1144158140d500c1410402c55100303004200ba80031801c040151140200030000b1000c04c0c801c127842440381907404117203903d100b500314200c000d030320900b501c00c0344c148a2100d40300842d08400810200398680c0910380254428800300702c01c0400200904215102c005046004244940d1507411100b207907008401c07103031101c0e14000d407403044503a942036503440c0c10306043c0c04e245014a007400c100200200074184687d41d919801c2c0d9000320032200083d0545442c98181d00920402103d4091070103510500400d12003d62104400c40d0b8040e01c0c24025144840d041540300d11007101c00030a0010b481a062440d0b42004405034607120040c0100e0b00025100c0240340052640070341c8040004006020b000b0900303515200158011075280d40040158425490b00625000040d405074200001c582521010100040a15106040c20a000366803151030307a1030100a0010761690701d0840d81000700c0e112002e0104411a03102c3c40d00160071034820320280c1d50b21122945541551944645c040c001d0f410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 282983669 1250 282982419 282982457
    0x5060f0403020a150305130503070b0705120702070611070b030c21010906031a040f0624090f050f07020a030503060a0b0319060501050901050d050415050907080106090c0f0f 76
    0x207044c0341c91030f403a1606240304009040c0d900c000c003044401c40c51080290000354000041e1410300e0340c40010700d0b00d01c0d520403000326450b004401900c00741081c0e890504c4080c07234010810b90300b0f41e03803d070361a0500402d0800c40c0c26900c0b616403051070140c19003000042c21900d0b07050040c08015000544247c42c1a101e0781d0810f0f01000e0a8005100709039542c4070400400654105100c9200c0854540b401c1600c1c041c2c64001c181827860720040d060a881300c101621714207040201d807400810301c44410140301d40f14002c1358010800f0103070301d081043c507190100b07140755501c0b510603110780c14a40c02021403000550b000c540c140c002400840d041315609001081d621441d101552041c1c80300302008101d1001201c5503004e842603a4404e50500004004142190760b100044a00884c0411004070700e54840e0318024500500c09078002c401f041c80c000070300c50022004076003001240d40c514000c1c000300c2d4444200074100d0b012868010045116060004401d5010b1082004100f0584c140058080c1014440d20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 282984919 1250 282983669 282983689
    0x9040c081b070524070906140306091018090b09010b0616150218010806091b07050c030a03050901021b010f0e21010c1b0f0f050f0a0309050108060d0c05060f040302 72
    0x61400000d9000c1200b210b1b8403c0e4000b0003494a40b4003100414100c3c401c0310218400902035500401001c3c0014029003c2c1c41c18610040c04201c0511100c0007400b8444002803411071022150150400082440480140150f000c0315100905072032622400340d81480b0845c0c2e16020440c0e81807007800100b4015503461000d4020729142c1d0220007540d004031000180021801171296110b00245828440b09200000900d00c0b41c03450701c4080b41c0e4401150030018a0309046004182e85842042d01c2c1d1010183c2c09409041c03100c07000c0e003c0f500c88260f0180383c54076180000b2001030005021040e4a11071500c07441102c40c9045015003910340001c0c1d4b040d07880c00e10020381840d00846a46070034140e845107a214640309105507800000c440000c01c40c0d0f80c1c00e2204115600094020150100240c0c24801e0034454420002900c1c01120304088144c030f0b0107810658140b10b21808501101c0c005100d41c01c000c0f00080e001075101600102e410f040c4030402c03285401c2000e6000d80034900780320100c016200c3c01140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 282986169 1250 282984919 282984973
    0x90203130f08090a090c02060a020c010b061c0e030a080703020d11160b0c0412060902010918050f0112030c030f0e13060905010801090203060103080f070b0c09040c081b0705 76
    0x501c0d603c21504050200d0401c096001c400c0007803408180513500e40c1d000c940d40d600148200b03005070f82c0b41100d0a406003d04250309409a0112002aa8030024140c9040c804608101c0b11020700264a00b908203988034050805e000012172024000911740c035205c2d900420000c200184c0000e54400c45801031109508901c2a4007440340000c00228140b1031031900003540156040451440c06040c13016488581c00b800e000146141d032034503140011680507400c000c006c0c0101e4070700d2800504039480f560303000e401d00340d60b082c1038585a0b0b80040786074031a0400b2154844d8260b1503000e04a941031364112102c039001840030007089a1070310840200e6594102525010032480e402081c04e41c1040003410480d41c0683c01410203a2610440d000140c4000c03400604580c0c200038103540340c54240c10b41c04014803a905d801000c9200f00010000503046080141010746003e40341045603600c030600076102c04005031408400410540040c0789448030810082c00400c2c441d2003514007065003582131500c16401c4000e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 282987419 1250 282986169 282986183
    0x510181707051513030c050102091023130510090b161b030b07050a090504060303111b032113032103020f030705030612060f07030605060c030301090203130f 69
    0x1030140902080f004111880301c00c006481410704443c080400d030f03c41c540c01410700c00d0241040d8140a400c0d410350760480c0002d0034500307004000c10b50050111500c003841407011081441881c106a00c180d054420b00000c200c00c020200d4142002c011140031035000d524100440c1d03443c0810981c288901900c3c0780c00418405143c4c45420b4580a40e85013000c0194007100c0e030307503000f0804c0800d6501c1c0882c2d400400c50304010740d4600a402d03044507418900e42109800506143c000002c160f0303c0003840903d01050300580345020440c2038105614000b0342c0503980d02d80d1103410580c1c100515403031990b840d881000c180e03610b000c0c0302c0d8034030740c908140c076910585490b002510030018242c611050580501c0c0170340f408500d425540040002c46000280c13800c802c014012000581c240c40350004d004010040c44121410b51510f036130900b00300b4038204d40a60000b4205003000400c0e08140c0d0a4460306284000070310b0850303003410010130003900010050720080350031611020101714080b15061380c0c240901c107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 282988669 1250 282987419 282987427
    0x5070f050703081c020f180a03050d080f0901090507090b04060e0406020d05060102030a09060305061215100b040302030709020d1e05091b0f0f01091a03060307050d05101817 76
    0x403483d0003100344c43c2c010510700d004212080880c015542205c4029034a28002840d071202d0101040d1044400e400c024200d1185074101d50303060341c0010030584201c2200206003015030369081282d01740d071504c040041540e40007038000c0c00144119040202092130142001032425542c8800b2168050306480c01d61b805640050280e4214000c1d0040a910250a00007540343c01800030780201800c0d0944074550801d65a130f004514541c2d91580c0100c60700102e1700c01c50b010844410030030b251445060340c19840085000c880085d11811110645089039001005840d0281c58251440e01039032041e407203c80590754450031002c030341754640e40540c0c00007806a00021186848041e5034503020800c11440c085150301800c041c10b81d52060620b820300101624140108840d100058500ca103d98220a2a4044008020316810261030140d88100c07421000ca403d52036541040c000309440b401c8002c1c02d6504154686252801c4035044141112207610304c481d240c400d00e8803007010705030180e03010fa403030098005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 282989919 1250 282988669 282988687
    0xf120f070b1b03030105090f06011e0f02010b010f050d0e1002070b070306050603010b0a030e010f0515091b04120c0306020316080a05061c140609030a1d030d05070f05070308 76
    0x802d540300141d50b2000718515410000010b4113410018000000c0170501d4001841c280d210705c42040090f00d003e0000038007042a40e03c0501405030341e8814600540c0f07070070703a4034506611421003205030442548070741e440c00010381003030400703040c080708074004030701c2122001c861001d501e100802e03446000d8100c1948a05014400078155411b6a005501c685402c0c001404003003090740c2104c0703180011f400c002480c04500502036014040514031081c0d103524000400c00118a802d4659401403030803510500da07942ca1003509080900c410106038a0000c0512090082605015040320014041d50b4440c4610b6a0307540c62006903401215200300c160034103e075081407540c02402054000301040414451890201302040c03809510603590307015030201d405200244400c0c1e48172492465102d00a941d0103161000f06607a481c0d21514810700020111040200610451885001440001130107480071500c4054200e4580e002014183c480b2100495031b400091000c111070b4006510402d00729440354880 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 282991169 1250 282989919 282989947
    0x10b0307030b10170705011b02040504050706020c0102011a0405090709020408070e070e101202040b030a02030720061612050a050109060f03030507020d050102040305070e09070f050f120f070b 84
    0x981c3c420350b0800890b2440310903444005c20110250381c020b203420060640440300000340450410f4010750054904001d00040c0400840d0f0001599591b400702c9484000500049080340d8404080e40c0d51000c1c850543c244078909a003025401c46610021200d080d5126031186040364003540c050261039000c8030040150300e0b011040654004510705000600b000440041560f14401403408001c0103207540c0401030101840e41982c0240115601554503407414014500082d841600c00c0360100d1002d000c00c80b10003055006d14000101000090030381ea41b00c01544d0001645134031070520a12140c00c101d1000d000940c400c440c450751a921740841c1c50351406e00903070b003110401e0b00002601c400704076041c03001c26088030850300050b81c141da0307201c80703018141045030090155820040850144000001d4a034180300050b9004044c0e210944000c60750382c2041d043d6001032071290035082440315810030090326158000484040c120380c1500c11002514642d94149403503a002101c1801c0c012681505034030719 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 282992419 1250 282991169 282991201
    0x1505030708010b04080a060e1606020304260d0e0103020906030a0c08070f140f0f03010f03060e06130b04030e0a06020d02070e060102061303050909010603090510061a0903010b0307030b 81
    0x2440c11100d1130079007812106615004040b4025244540b280d843c00d000e0784040012178680114000e000350300c00d8032001e0007074581d4440c0c45000701c0041d000192407590301403102c201a0840c1c0c04002000d42c21b9120100b030316640ca005d00d04a040c903600b40403041c40d585603440114890000000c0c00102035105103805400d030070380a4840310802c50003c0d400c2d45000d07001b84600c800f00401e2001c0980b248424038503101d15100d49481e611000303001000010740c100f0410610000d40303101d08010300c4071200302080c103a607603c811105085845420f4040c0301c003142c017000b03105130002e00920b0b2000f107441000b80030840024590740500016032283d0700781c516850341070010501601c101ea2035620079081c0360b00002d5594501400c50b41c5609400c0103d00704040c00350089070701d03412000d08103102540e545c181c040d00615101d50261a40d00030000d85a02c2c00150f8454042a00c1c205008036003c030300203100b02c011a03006040469003540d41c0300e48183c0c1950307040010030f00440c85409010010701d0000122905001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 282993669 1250 282992419 282992429
    0x1401080a15140319051902030709021801080916120311060f090c0904020a2d1203030c020312040305090f0904080a030e0a080a03110418090506060102030406050409050907150503070801 81
    0x709944d800001610100300c1119988202d41e00c500c04014a00003c0d050800c0f550054184078800901c000119000b00c2c10003d003c04c09032101e000f947e4036004e001d625255006020802c601d20460140030240b00003c604d0b001c0c6010380b410300703001249100303114506001070364403411403000071082064034642000003402c84c000c19581c500f0281007941c00700d4010101800388080041d207607021300c20408074151440c10324080750420144ca10fa075400c602090300c000210254000f82c240807801c1c0c10346000004454104d083c0542547c4d0355503c0703441c06c0b41c0300c4e040f00382d0007540241c0340719841e1450303690954004c0c01580143d020395a01e020301072014044032052283c10500e50040000a0003245951090302e56284060078085a00014010f03a503542c6e1107113401c4500442d000ea15070b142145426400640e10038450011150f25440b42d10040e40c0d01e0280748101000103204000c280821181a000160003400c108112003000d9220b24a480c140310180c2c0d01500010303c08010042e40c40e6201242d0340c0148 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 282994919 1250 282993669 282993703
    0x5150c04031106030a110a030c0e0a03031704020a0807080615030c030303010b091314070201050a06080a02060d0e010507050309070e1b1303080c0102120c041401080a151403 76
    0x600d07580e10900c01d000c1100c41d291041402100191160440760484074524910180195548504002c0034000300b410304d0845001804507200b9125906140b0042d205890b099280c0f2400740b528554082d240060003042240c11900e0144006441c02003040700001428101019003420302d00380d102181c10b11100811140300741d010078854562070f1404411241910700228455035a2000c210100d03003485803402c03103038490306d00e048410f41c582d50440b03031482d015550382e50007800643c80315180396080d11024042d0403416002110040014a40a001005041100c000c041020380c0800d50441c03c4070422699903021035400410020100030605c1f03100060008000c0741041030404261141e4000e0302c4240220782804001807040355111022400f80065074082516603503550040a064080d410131512418250b803407401092542e011a02a507080d04d64600c10700c0191600fa0004445044000d00700b4500310381d0755810320034605602c2034040068a0082802203900d445241410315203151540c11100305 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 282996169 1250 282994919 282994927
    0xf0509011104060815060a08040b07020604020a1214191b0b1e070c080d030605151e0d060303030c0f0c0c0510031e0504060c0c030f030f021605150c 65
    0x10103441c01610700b41d460500d011600f594480d009100c0d4904550b9007140d00180101e002c05240364011502e0744150721444021656440b4a0410390f80c417102900e0003503000c0c00040c03003401400c0340000e1031082280503c501c0041c1911000f641e50506e030350451308920b001420340500d02400540303c40017500b00701c64002d680c0818503010f5001424062210000d070780b0302200345080e0000010b141030369440da03001319844002d55a034111180d0744103501da0041002c80e091403c00501d0b85440d0540c214a9000008400d10b40201c420400c0405000c024800395001020b221a0042c903046108000182d44030fa00d0020702c800c00c03408041c220304241e011150030802c0b00c80d001d4001800c480c80800c2254002e5807058291220f115041d005044545006c44c003450140c8100924050150085405a405403104011b00200d0190031101418150000303000304041a40650354a4402d600983c0b4030408600018248426504d01120301c0d06003800c1900c050784070700c604144100700e580881e504074480d50341c100d1034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 282997419 1250 282996169 282996191
    0x60607080307031e1a0108010803070206070f0c15020606190501051603050c15060f182202150c0c0103050112080c0a0605130b0a02070c050d0f05060a0f050901 70
    0x110700c00282004201a04d88500200701200b915202c280680c4200c41071140c1d058004d00140d00409074442d50f80011032a500001d001040881203855040d0050007407403900d125038550345000d90480340211800c4c44004800104003d200191101d0540c456019000d107080003802c11051031880c50034500105203200e020480740c0c0e00300d42100e00e01c0c604040c82c41040c0702c090034161454040d03414040e900d409200303000030361551403401042c450309040340c1001004111708103110a60345015200550520183c01040800b80010969142c6032800503068400303a400d17901040c0640700342e00b04001040301c04150035001c20300070712801c48010020300e000c21096144c290012000040727950050300c001c000042100405170140300c00000141c100a00740407c4c20805203010f030b4002044410307600c2035080c030f001c01c44580c918001c55910076041001340c40036500b0001002289400340d0402c0f0b0f0282415550741000074414898544114210700303000030492001107100c410360340c000382841e8050f41740c0010154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 282998669 1250 282997419 282997433
    0x10b030304150f0c061b112404050a060c0c02040b090403080105040903020304080d0504031202010911040b0f0409030e01110f0604030807050409060329040f0605061302070c030209060607 82
    0xb8a2100524220b03010982420043d6035040750300001500c1070341000003251a60782d070121280c42c1660395607154034100401c08074085d150014140315410003640c110590540e4900c81c910307140c0050080054501301e0f0b5003642e9510840e0800340e0110003048a6110010030f520b07040c07180b041d481034192981082440d0a980081c003140050042503c100c1d65240064185882003081d90301822060085541c00d02e54408080c0031a0410300c803c440080559040c80039079071041c0030b25420150320411301d108201d0598100b0000d0480e4124490b0490740d0300190840c155039a02074514401c0c001d40320404924a4040014034491807194000403c0e40003003c1c141f03180d0000030310142e00980500d8001d026490f055412156842550f021000e07150410002009020495000c0b1b00f05030012040c41442e04004081d00c1d04a810440e0058203030310008000c00d02041c41c03074000d182d1000c0300424101141032002c0c1380c01c0498105000943e6803031041e00061003141000070115401c440c045455a042a000355503481d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 282999919 1250 282998669 282998699
    0x10c090902160203070b032d060d0f08160b060d020f100207032a050901061d01020c0a081c110d0e0f0402040326090310110d060b0408010b030304 64
    0x61034080d8001a84200c80001181c03481810340d004041c0c6003d10342d00c14103075805410503503038004101010344908114086003202c41c107038100002c00d401410b51f2024100300d54428110000d071001e1205011a40024800070010819607203145c0780c0070180b0510f414802140c100c01003415010352107400800d030142ea2065900101c05008603404000d85800740e800728104190b682c0000d00c10b41903000642015410501c074940c04401610340076040c1903031901004031f008020701c0750b0404034000030111074100c07070391030000044224107004903000035400c04c000c12040111944000200d8000c84010040200c2c0185030859480d420300e01b0240000f03008501075120407800c2c2451f003e201d407407907a00601d6212042d4210521400030720442d21580d0740d05050204a004a0030030b07081d0307090102010361a45000c01514a040d20107002420300034101e500120007401061041c40301c2e20000d00c20034022041c68040d21000e80b152a0442d40c03a6803901c0c492074292a4a200d625219410500061142400c411220 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 283001169 1250 282999919 282999929
    0x309060e030a020603040804050d0f1a0105010f03020705070503030c010c110102070320010605040507120506150d1509060b0c0d05030405060f181e100203150d020310020d1a03010c09 80
    0x6a07071780d00e5520b024091482564081c6130080c2e007034404201407059104401e481680520740381d15044100d002c5a5102c440709019144c00328803000c0180c002e032482980070b0032540d4822021a0743d000d0312207000a245401c0751080000580d10380501c900d80d550310850142e814101800250b040c0380140c0d401802408100c10503140b01c00048042d0304034403800350044030040030003903c03c2206060851000700341c030210340c2004031140c0c209000720352241400080c00040c903540e144038600346006003419402803c900708544940c20805030300455062400d1181e200180084000240d85d4482d2407586828501803501c8503091000500c1040003003200441c40d1644038624482d40c01d0a5501d0460201d003440100307020286601c180004e180307144000c0c400454090f031140341210031841101030060141c2c40112441940c0c400016015070b25420046401140c03d4170080554040402c2c03590418101d03044409081401a20781702e00c0c0321113242c101b007a40d140c0e410540c0244400c803040d440c050101900b0740b02e2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 283002419 1250 283001169 283001179
    0x2031c0e1009030309121e0807030e060f04050f06070c020f01050d0f0606020705040207032019030914040209010206070e0a050a0303080103140d140c010f060e040309060e030a02 78
    0x1040000405000c81d4070080c40c900d004201c802e1660500030010805000d080303c4001c800810b00038100d00071a14660140000c0f09445801036440380e040341e0341200500038600745070b11040d0100b0060310a2104078810340344821340d03003403d140c80d0800c5440c1c503a6066000100e900000240510241c0c800040040e881c1c064890803541c00440004803464403079a824100709034900308003501c0c02561030700004119000c40e82228003130340e2036004000807841040401400300380b8001c0b0381d45540c6102d140300f022840c1c080d4155051420020590b00c001c895801d401c070b0005079681c07024800d64080010303003950100255421410004d00400103036807920003030303c240c0c20f02a114440c1703101540d580040703c02034000500756190442d030300d140c0a0941035082c00222940d1400c1001808403a1300090003109071112565a003408003044036501d9500d600c12107165406548400400310170001c02d000d54fd004124140c401d00b980e250605004013060060b030040c504100b510311030b1500a940c000f8030901d0071501210 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 283003669 1250 283002419 283002431
    0x3050a08070312020c0d08060301050606070f020a051906080c0406050304150f0e0102040305010b0d0c030201050a1404032010053a140f0906010e07030905012a02031c 73
    0x10140c0c3e2400301c030249250024000102140807000108910002d40c4007a00c403807074242c607810100740c2681c5007200c001d904910b00740700000208100d40440d203120360004c0c0420803016100c0307010a40c4081a024a540c000110210403c1129482110142d02030402515942480c0c1044030041141c800a0000b40120704404c44003000540d55600643d844442903008200e101c94243d2858047d42051106803880d528002500e200c9040c01c0c0071591019a01c13546003280c075802d42d030054445400800c080d100b009003044c400100c1c040d01d8801040510b0040d03080c01d25460106140200c5080b8028003180503106d83d101501d01107800000352980b0740c0c1ca00860035004a41025640941c055900360030400d801c2c0032411801404242d801410010841030140f41c86594004c0c402c4c00e68503081e01e03c1412035001000400446030030a4107690402d00300e14011503440c1094a4403402e42d40d18054800003000401e111b580001d940d03a540604501482c00511304100a120b1150206040852690302e0691901 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 283004919 1250 283003669 283003673
    0xa0807110f28080d0213030f08370f0203091e09100b09060304060902041a010201270209060402070c2903060603060103091b030b040203010b01080103050a0807 70
    0x912000480d100c240c1140c091200801c41160340368010206900d0214201c68807541241c40e54030165072440d04901414505201160100025804082d041c100b071104504003000080c103d0f202009090b0003403d203642c80f861214502c1001e095280400c4c000400b04480013840001d041210030078141c441c0c00d041030a007582d52010f0341548070b00081203511072a907201d00c0c48e50456003030992180700015a200300143d550742003200e5802025020791124060309214800151501800940d8451b2240d0400300e4803108540c04507013604d900c1c0422004e004d42c00c8040800b1941d091260b07148080c5490440c1c9410f0b40300500d00303040c7c0e040f0742501074002c0200e030001404a44694041b6129241c1c420481c40800356511800b03040030240c0130440d81d201000040d541d84205200084d03038014500204407610b144c030342e071005400904c2d00c0030089600c04001c441e459001c110302c264400045010784bc82100030b180503c10142142d02c050785a6050101210051010420001c0d040b041b960344103a00f035544140314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 283006169 1250 283004919 283004927
    0x305151011120304050705091b0c013909050f0103091406180f012a020721030e03010204060e0d2f1e01080a0b13060b0705060a020901050a0807 63
    0x703491080e07188605040807a0520350302009603c114010740654086030b813104200980700e1416106030150040144d4540841e41c2e034400280b0b0003021410001414000b8201c80e1803031500303000403c400442503401d80035548519825215181e002d9468410b2007141000c000440170b80130a49014101765542c070505080094400420280180810440d900351400082502c01c80c014030302156518011841200c13110b5005005040f41c4080d07000514070060285e6207100700c0140541c011004502c0f0381c1034001401d6245e01d0044050400d40000d11820f040139042c05828414900d8900e4042e82c4100001c019241c0d010140c40d840b01011505a03103001c07400d081007201c1600000b01401c00804c8100f0241c0b09a11525401541c2001955032030b03040c030103d50152070140c09110750703140812500e50016035000002c0e80f24201c560700007829001200c0520600404403443c9800400f10000700150600500104000d4258001c81c000015480c0980400c00242180034404000c0e080c40a024045090103001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 283007419 1250 283006169 283006187
    0xa0c05070f0803041805040b07110a150b0f030a020d0206160b01080109060c02030c0718090803090105040c05091308090604091812030e0703080d0b060a0906090603051510 75
    0x180001001c840e98581c0304040d220340c49881003030312a0000f5004031070201c03140d01400d44265000407030030605a90720031041d1903c80d40b60004102ca40507021405000031405500d054204158a400107003281c800c00903c0329403030040840c144203610003804400141d5803404071016295068410300d4413901031000c1407200d02d45a00700204071140c4d000000c6010441548010a41805400d05018102c01460300b070341c403403040d8100c004050704512014403542c0380301d000c0c481f00007445120001e107803e919200c4040f1a00150743c040c0c1c56945031b500b48414404224110f00107031804880b03400c0036080c070700c030b84400da0215000024007541c5d002c1080506590341105440051050100c1442030f0181c04a1004031780412090494101c10076804d50000c55200f441100a8018480020010f0320700b10f0300c4110032600115000c04006858036842041600e6078806001255596128110380504254010b0482d22854000303608151802080212410603c0900d0025a4040d51203400b8900c4c248400c4810000e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 283008669 1250 283007419 283007429
    0xf1809020a060f03060506090904060e1c02011505010207061b020d0c0801020720030304032a0308040e0a0b0f130e12090f04180b07110607091e08030a0c0507 69
    0x1d10040028000743c20942802c8003240315a01000744546581c100180341c02032030849500414100c002800289a031780c040c8030a940c001044a044a03c0300c480300c041251300594001c0113035180d0800102d110321107103502025101c2400507103040d03802d0020090055203070818207011200750100500554440503400c0400315002a03800c007009403520740c224040d40c442c2130102c80e00100380b42d00d00c403809070b24034940170000c0000b0095071801d80b4603111280c103107204c2140400701c040015080c0c00941c4a00000100440c41115015143c5140840c40c000d020402080d040b526410f0a0740e51010750f40d462022001500300300d50045080002c584514000c0032102c2c4d520445110301881c0d440222071040140482540445051401100000c140f1040c1c55151010854416212000b10009100c680500ea40410135103841010b001001b240d1505d020720a4409102240d444102480b501c1007600001415803c240e807017940c998030709261203035240304e00c290802c200b20184080c401040424815580240703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 283009919 1250 283008669 283008679
    0x504080a060e0c01030e06150a0b041514160f21020c041a090703020f1c0b0a0504051006030c050405040204080f0609191220060f09070f180902 63
    0x6080d49000d01c010040900940040c3c854000110f049604c030b401201000b481480161401e921903c03100b41d4100ca2900105030b108410f40e901007101c20501c0040c1c401002001031304609401504000350060082075585501102e04000718040c900c40b16824100e401e03400a103540d507a449509114140b2503020451304814a000f48070b01c0d0300141d00241d40508840221010488a00b0100000105204141c05142c02161007000a00442c0c0030b51b003d48400400c5004107840c003008000d0f400c1006a00c2205620460390f502811005030a0040384800030b02000d036070800450601440c918200c1013141b0030380007055200c860102185100300242c800610003d0001c0d51140c3c1c480c3c10340343c0c80705ca00d45504031142c070a28001954220000903c2c06100080c44515404944951618145401c02c0494841400901c54400c00400000e07004104005401c3c00a40814140b0090080c8540170203494101554072079007003482003454180524003192100a400d01d20011000107038800f1f0070341004003030b40c0700c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 283011169 1250 283009919 283009933
    0xd090e04082a0a0516050102030703201204060210051602030304020d020102010b0d0f06050c03070912030302040b041e0e090c01030f060308030c130905040807020d150518060603010c1b03050408 85
    0x4140040d180e104085c24a15040085880320012030b41d0b03000d8410041c0000701a128448070b00704010000c40c1e000c40822080e00d010807003017407015010790b0140d030154005074440c1d00c00402c0000c803485266000b200301841e0700c0a0020f034020081d9030b40005807001e40b00324401d011400840e8004d60040b12010b80c050400010651a810241d50000304110b069804600b07010001c0c024900100480f441140141c03603900702c250404840b4041c00c03400750021010303d58200070204a20500c00c01820040660600c504580d443c10600c4030840ca00591081810fa483d0303800740040400042001a83c0c0382c400e103400180c10418600840241a003544041c0581e00b00200b0b2104409444004100701901582d07000501035171046907108403041290041d0010209210200c01481c2c11446250030364082c0d9091418078803000c408d1802c4030000d49400024603580054840300e00760034008a640404210000c0000003042d00380a0500c0081724a42404080301002c5402050702601c20713500940b407401d04480c98 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 283012419 1250 283011169 283011173
    0x16060302031e150312030115080903040e25031a24041509080607020d0503070e12010e1501030b010909030504031a0f010806041a06130e0d090e04082a0a 67
    0x201c500c078400f6640240120303031140c0707034818004048034102d410022040740c00c0d8494036000c440c1d085015021050901007048000745001c441007500d03024500c0c4401c0941900083c002980c486d60400644a0506041900c01c440728800d0501079424420103a400d500f00d041550b000c1000c2c41011140c032444800b0114012410800115260036040e40c81d4a500c4c00c40e0741c484103480e40e1620219840001a8859640c01c50b031b4502c14005185c0042c928100381c18408818030000f0380c44051820304a046a5550025400042003001070764018000040ca20800d54115103130081181030500401244986944050341014441e1b0b04850045800c104100f025812020007040f80c5030f4180c0d08506460600c100100d200304021840030300541c0d0010300d4204814003100000710801006101c990b110502c103d5110101c2c2040c003402c4407682041c00500841c504180340a4854480d94001041d4850703140300704000502140d0455800241c01503011101050f00d41440202d00201d030142503042c080c1d0321079881 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 283013669 1250 283012419 283012441
    0x6030601142a0f0d050f040e190614130c0e0907030504020a0509073608010203040b09030717090409020a09020309011a101416030f030605010216060302031e 69
    0x100da00d02e10300d0702c080c0740c401c210308035642d4060f9565126550424121103043d54010f40007010524203c0680c942455a15092601805011508860807400345400c0d01054000e0303100781000b400125142d01001c2c5403440201c0c1e400b103d80324101c85900c0c4d980120f4641180500070300c040c000c00050202d0441c0c5800c8030300401a00c000d94049024078048900450286042c5905520451442e80c51219240903000c0c80d0310f244181c3c0480551540c01c8002603d045040e4440d5035002c4d00c1840005030392401d01d0b1800b0312019000500e103014a801c1400340701c002807424003181880d06004080300d5290000c10f000200207199000d0001c0d0701c803090000c0080d00c60302c030790040c0d88990b01541c0200032240e2034065020a4400ba0340d42300d07038411b0b481c20b0360b034103c54040c4020b90300d0340c006019094101902c2c006d161041001c400e100350007003544102d407042d625515010751005001d080c405000c203502c48564404240e107650285102345038002c00010011403074441018039a005c0171035620080c1c104030160803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 283014919 1250 283013669 283013707
    0xa03060c120e0102180402070f050102030c1b06010807060503090c0307030311211603020703051b0901060905060d020906191d041a0f0111010f062d050603060114 71
    0x41e00c540d0500d01030800821044c421764000c4600940ca0942242044003004001d5224140031509400748140ca240810024400f55100d1601218071540e147d2005049804c41e9040040c0841550b018a0041c010100b000c11040119803c42c01c0c4584c5135120358030b2450030031000000880c0c140c842c40074000141544603908070040000781050394000c20f003040b02a6017110400c060003103404010804803907440030a041000e80e8500a1068688640d2a0394030142844280d024804048c00f29200100151400303000141c010030842c10607100c40382c50140800c0b100c1c043d2400d6160002e9004c1110001c50311450b04682c9001000c421401514820f1000600310301c914000c1e8840d030400c8075604120303608003841150000000300e6014024000c401c420410646020b12582c0c1c100301406d420b4415142d000d001e0304854403801c0c072010540071306040507020509a10501c2d8076030485003000d99000400c4090210043e40ca040d14515070303c0e52804010b07a20300e555510f81e01c084400c0051174030f6001c00080c403c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 283016169 1250 283014919 283014947
    0x30c0f030405100527030a02030a1a0603060906040204150302090a060602060604090c03082d120a0504030804020f01091205062502030f1305040504030806030d020708070e060a03060c 80
    0x50340203c0081000320340c1d80c001c1c0452903100008088580e0380c0004a8488490060340080486560f17852603800310341814140e07202101c4003138513104503440c054806421a50700a409400070081450040f210355500d0502a0000e07011300d50750059020704d540c1003000080515009040540d050a1949084006145a110328001030150101040e41450140904000d0640069401132214199282d5020a5000300c011514a0102c880c548883c0d1075100340401948105100c0035440d400710410054285100601c0b01d44618580b90400001070340000d105904250180c900381030f03140f800b40050b501118a90441c086081d0007085800800c031000442d180300c0c1482d804400018a00581e0781c000e60128981e50320f01680040c0060b984551464010304405100d000c074920440340e951001c5002c80e04262801e5001602d1507080108905003044100c00600d141d10040000b1840d100006440c2d00c298003079043c0d510706441c0071070740c6945d0b800812005075400000c01c2007030a04070540640103a4480c055 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 283017419 1250 283016169 283016179
    0x7080306032a22150305071a07110a0b130302120604170a0909020d020d0b1e0f03100c020c03120403261b0c01090506031302060c030c0f030405 63
    0x448a4886200c00004104440084501030404034a020001e1400e601c1c140f80c10f2144948000842555160255000c00120090010641800c40c2411420560140c001802d110300e4641512014900702048922040d013081c518480d500c000340018070114007641c0036240d82040030903803501140450580340100c070f1007240c3c64000c500744600c8440c1c8030341040720003a00c00000c00c0580c030070f02400500207010f03015091410702e0241d84c0311030807034040b03800100d81e1400c0d00e81d0115171a40504a184103c0468040c11540c0b52000c2d900740f0f202e40010003c4805070b50250300e040c42990310544003008400d00403201c1d1941031114981c074540085da07401550560501c00d100d40d040f0614210b903500100c40550790441c0307008201c0c1d41a80701682d8480d8071400b0310a0702c403404000c02000b00c40c504089041041009010f84400032521700010b01c02c460f1500503500c40c03c010000d12140d81e42c4510a20748450741500c036680c55520409295003140580e40110706ca500810009881e1120044010000e882c001c641d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 283018669 1250 283017419 283017433
    0x60b0d0c020601051c0f051203040c050402030622110d0f0b0105030c0a0f1e020f01050c1c050709050604090f050a1407120e031201080d030209060304030c050c060708030603 76
    0x412a5202d000303202d51a0018000071080b0240c0802043c0824000d0003026040651140783d61000e20300303607242408906150010050208205200c4903501c01054101c50542c25420100c0006001001d027030b03c07500c081c4400c03114041c420441c58204502131601c000c0040e45035886052100b000c0c0c10502c00e1041090710f8128083c42039809441541c1c0101d551741c030320314200100b0a0782581c02d0b88509003071030f040c880368600a00c8200e04034180c842074414564090482e5401d180d0040e803e581c0b000d402c00d0512441407104003c03607402032844181e2030002200100c1d10752581482070b00c040c000358201c2a0400d8000030007140c0302d100740e000080303a409020304c200310315940d407802c58089030141468803415a8004010034034403445a000841e0450001d03900054100c2030501c01455584060010b400380e03282d810040000c03200600c12254000840d017810752401f4025030008007140f00c018402000d01c45c0040803103061080801441072085000303010140c0c0c6000d5408c05090340d0300125912446442000c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 283019919 1250 283018669 283018691
    0x1060302090610090b0c0102070f050c0108070809120f07021017060f0d02010503091501061d0409030e01080c1207030225050d050f0c0a11030607140403030c0f06060b0d 74
    0x302100e08001044d684800300035042c500103000991180c0b01100700d0759020b208410204504503500d40c04107108030010840c280d07501002528646000f0024014400b05108202c0c07000c1d004a60604c51503810030300f036961018100c11505440c01454406500056000c2c8a00d0300c4607000070762511074020b00118809642d56803000c0201102c4110f11494200402034480030040d409070b00078680114030340007602e0000c10303101600f40d503c000992200002a0000c0001210303912a00418040e69000f51401d00440e16103850151400041c00a0b0504104481d4001241003106109690201101c41500c040d5030805820040180d00001015049462406540d11030300761481d005050556100b400740000094a510a40303e54200820b00c8160000810914120907400d000300c6c15250b202d030716000b00c041c01c1c150525142505c0244402c4c10310290440c4440c0c0c980135141a03d04803239040c90f010340a80d02510b0010b03042c1c20700c107100804007800d0880101c0d56841900c0600080c02d40c0100400c0030741ea2503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 283021169 1250 283019919 283019929
    0x2010c1b02030c01120b040e06011701020c0703020d0c12060f0c0201020a0906080601051201091a191503091509021302040501091412070306020a08010f03053408010603020906 77
    0x8000c0254542c1c01056400c110b0350080c1c207014180240b0010010317580d80044081410740e90f101c441c04034642c01c103000610807002036005004899004500071030810001c0b482040c0d88451038003010b8487c00c5d00d0302070901040441d5190101a103026001000e080c0b25510b0000c1c0600800c14480200c0c50909241e14403042c41482581c00c01802c1c3c0c0d4543d001245051415900084043c12260400c407081200002c411810144d2900030601d01d200040c00044400d0a034628814140d50107120340441c012030740180c00e01c8414807068807040307408000b0055141909800500315914024500da214003601040c40d0016030164080760b0081c2d840c240c2c400b400038044c00c1240708600038280864200701d0284140c0943c00d212041c2d80074050039800310f0325074030300c20b1074a800d00c50f074001c84000c0c1d00042c100580c10750060075036004182440f0b401d0445ca086980c0c0644982c42c540442c040520002e00c007200f51082c48008010b201c11011800e51001d448400c0c41d40a0459400281d00480104010400600341 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 283022419 1250 283021169 283021217
    0x81b031c02091f0507060b121b03060a022803090605090c0f0102121204020a091e0e0a0b070315150f031a010203031f1a0304060e010608120a0215010602010c 69
    0x25a26517151035510f80c0d40c1001082d4035829150080c5115000000002c010451004149540b64069175111500410145045030007004142c0c142d00500c141c800d407071001104030b140800200c07407200500030a07900c114001d284c4031102800480c1480c0c01d010680e007011540d020799034025100b035000d2820301c800599446600b00c502030f83e142c0080040a10414030744584980041c80206041000f6681c1c400200a885150300806104640c0d215400e0b2145001d101e00d11000c1d1100014101c94401c81c1c5036040746410042408052544400c00d880c6006000800c1802411820f02c20b500c2c061403190300140f444000d4440704000c6407909890502c0966240e8942d443c4010503070003903285a40788410f49103c14a07116030b40c1002e68050802044012464014001488400c52941d0300d81c6054104101070751740b140030700c1000c0d0b4034040b010b00c078000c008110380c49014482d6000654a804c1900100c1c82c020308030042994280900001280465042d0040050315220b0743d0340101c0c00c150190f0310180e2004c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 283023669 1250 283022419 283022479
    0x406110a120f12020c033a0f1503080a020c03060f1501021c0201270c060525060506040b0a060801030b0a0e0d0921081b031c0209 57
    0x40740050003600c1c0c42807a00481915403490184140d00c428442c03038082c2c0c2c0000e02003c0042d040414000c0088000702c1840d00c01d0b000003480301c000075140440c0c8039111040541520b000d10b031240312850700d04049401c1020180300301407050400c1c030742d61b08201c00303c0e8009142800c018042e100480d059464006011800340e100103040652607100c0c1d0131b01d2035506142d8000d8030f0650242c20300d00702c1044080b40c3e5144003203045400200c1c0303046064003031101100b0340e05404e410a00d260020000032481c03428107a8103503600d6041c4182e0f2004d40807103100d6180b00801c4e1843e180380389205824100081508501d00511041d41c05020091a00c6e040041d2141ca5001e28000038551600400c041044418402c3d000f02032080006802d00382880da00d410224402076110104102c503000b0400303032069400942c000b401c805075001001c0c006648208407807046d200884d181d803d40350303e1410f003160103008668010342d200c1c1d2900c030074480c00303080d1402030f401000e5001d110b0340b030442c003602c8400702d06241d00030260 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 283024919 1250 283023669 283023683
    0x209010504020d0b06030f1012031d1309050c0411120a091109041a011a0f0c0c1903050c0102030304020607030807140a0302070b0a020c0a02010c050c090c0406110a 72
    0x103800d0500748002900500003580d075903500c440000b8030700c2d01e4880056004880c0701140c4800c51504001e0003c0c03a0340d180c0c0c08201141602204000482d52100388980e040a80701031840e1180c070306c04001401c107050704902840e034034136005101c810450001002641040148c40610a08a0380b40400c1c030030340220194200038401030340002d450400d465000c1e00e880c510946030804043c00070030125602503030499084030094405c0186104103c803900c40030780103000340085640c1b030608845400000703005551002c11000404034071030031403910510102003205009030042d4400c00080240314402c031000c0c4030540f4980108802c84143d544040700300e0348140d03005401a480d240041e5400c403043d15004280078100040501090052221a4000c00154859580151f02c0741ca035800c5c8004101405041a80a9031040094020394200801c01c00d41207602421310100307544040c1170150820000504043d8003140040810004452140103003064840540d5500c04030410005c219584014800c80540b00e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 283026169 1250 283024919 283024921
    0x11d0d020d03030603050a030c2307150519080106120504020a050906030109050703083001090c090b031603110304020f150c0a12020c0d0317060409150f05130209 71
    0x5414048840d480311031083c900044e5840c4d8903200d040c2000000c40b4214006100d1500000c1806501e41d5000744240e0f0710300c0300c594681c0d4a0640c181ea0307150944260742040a000c1c0717403002554024025154210740d41c8180210700b5202180080c141002401540040f4081c00c0f07154890403030901c100b0b0301c5540c1c00f84c5907a20440c100b6007003010700203000305150b03451b40d00c07070801d2400520180540e00056100309891512103290104201c0003000301c0741c80c0718180c6403202d0b440a402e01c0009001b81140d0600f2000640e040868100b141e0911050700b200608407000818001451b00d07c01c004040c6080035030b0300b0404015500c510000300c1c801a503000e0741c840c4002c03180814600d80000b038a60001c1040d19034500d02070f4203881440c24880c1680c8140c0c0ca110f00c10505400054041c444640d808004a0700709045038085d98015083e82c601d81202401050711070005546a1180e901c505801070304240400c20380301102602c00042c3c0342c0c109400c1c0d00f2034103010118009011205041c91066801031281d00b030707 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 283027419 1250 283026169 283026173
    0xf08041a0402040605130504060e0a1703040501181a010e060f130612060b090a090b0a02091801031401110a0203160809040509033103060506010c12030b011d0d 70
    0x2120394080c1c020303a8030903640d440c009800e80d41d40c40321035000c5140c4100892070b4901070500008403489554800080d8001d070780d050000a0240d58510b19958515031002e440f03446a05140380141a0884405e00c21f0440f00e90200a100c0c00104080020003a4509825540e0b00d41e92491242c0d10280c8260790401446800410189001400d01d04505500c58002541c25514401e00004040200f0140d803004c0c1c1e0750031050743c40d040c101822588100e007840d040c49403101075030704c0c0684d481004040f411201e03400b0030008066034881c628461000f4580c59202c40c90350f140d050016810b001d03040220802c0d86030096401782c040d800c6003500c0a182e0b058000d9814071409900c1006115030120040340c4041c020040300d65244c0d00c41c1314240c000c1e2513400c000c540301c11006a41540c4031415250070f000c030341c400b1080c001c14400c040d0070080540703030700510110b4181c840344010b90702490b0194004012074407060549036816456800020b02d00803d81c1c42502c0394480e081000141c030401c466150b04481c01a0385000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 283028669 1250 283027419 283027463
    0xd020d0f0507150f02070c090b0a0501051b010507031b0c05030a200a21020105061e0111010c0210060e090304060f02030c030a02010b040b01080609011401030905010216030f0804 78
    0xc5480c00303208011020b040c0700d0f00a0b421121040e0080020304e5012418405212207400c0d100040c0804074400c00001c49004009520144a80f28990400c1000580008000d241c00450030001c036004000381f003542440d0802401070840c55400c080c004a96000b0b0400e064891010386000e150040b01030740c41c00000d0342e01120000742555a03942c0c15240c1031840c5145000400c91540703210300030140032086001c1c424519071561101d5402008682c100400d03c80c155581401c500c002d400112144010482c2c984d0060b980b07448544a12080c3d5403030001c5c403007a9250045410201c01c03c0d00c000070088551164401300500d8002c0c0c83c000016481400284036050041860b4034600f501801107d041104200007039185602030303c9541d0060b5190602d15200341040c2c00f95104121003400e04920342d00c1d1003000b0510003034051266150300c825101480a469000e544031080c000d40010095686142030700384200c01c0713803e40d0780803030019000c031400701d013000d10410032140120b6016504a04140303005503085 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 283029919 1250 283028669 283028677
    0x180405060a030507030506010e0106020601060e010f0e030a150f09080f090307050d050d0201060b030408071b0b0c010e061b03010e04020f04060801050702010614030c01050f04050316080d020d0f05 86
    0x2507040a151000880401c000308041c10007140315074002d00300e640c100135010000e00c0c07040e8041001d5510620040c800c10307130450080c501195007842c00d2081d020501c1d0086a44112054080d9010301070302d1051400c0c091021052034040c031550006004c00001c1143d990700b11400800003412010302401503051910401d0002c02c242c0d40c000b000c0390821521140021010701500310220340c5940440b2034030000640a001d80001486440051801d40ca000d4850346214401c0e1070000b8580010310712291a1105c0c0760b007030343c006018404007076078880c1c01c80750105000b0011600101140e101d0440050501104964003400000c0b62189043c1580d1030010300d64450790b409801240c2c00322001c0ca421545440d2480b41800410700b403400400da40c00d000f0406800c4072400d800813031038003840c1407980b034041e00c0c000369100d9020000e280c4940d60719240840441280190740165a05000d011a1a00345c01c010010a406984803101511450000200183eaa901e805070000000c945030113000c01e1500d00640140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 283031169 1250 283029919 283029931
    0x120b011e050c0a0803011d01080c01050a18180b09060307050a03141002030f011d01030320010204051206040302070f0807060503090a050a0b011a03011d04020604090903021e0102180405 81
    0x46102c1c032201c1e81d1340a0190000d81065045001c0c484105200032035507401ba1b8010031406018000d82e500250008116100c1c4640c08828084d911140104c0810a180500010070510390008041d18140c3d0080700501155032810b0b10400c0580007007600d030314010810f44c003240d8004004641d110311750307580e040d010b511107800508240503030144050300b2005d500046100b01406071503501c4540c1003107000140c0c1d008050400205000207401800020340200104420b840c40d009464100c50544000602910072900542d4101040a0480b8515540041c2c80c03802039201e03409581c0c01c4d40d2200360005c4040500d120708a8280d125280c01c001140c09030004540060862042d0340d00800700d511054900080b42030201c0709590000010400e0301c0b2400030010307038560b000610302c0c46c41d4500342e03203006c6032005507110745400c04040001c0340442d03562500300c4008280d01282448880554100a03460301c41c10f840c0c1002c4e500c1c0d80c4241250783c800601c2261951003030703041c0140c4060f540d0f805010041c0303002420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 283032419 1250 283031169 283031173
    0x70b04061808060c0415030902090c1332031b10030b09270a0f02091005091006091221200a1101020d080708040c030c06120b011e050c 59
    0x105110300d052150a100d803580e5122030342d98034500090100c04103850000b401c10145000d40410050382c0e150000cad60054050030030384d41c50307401c01480d002802c09240c0c03220945d06010b207013404c1d5000d807031144e14007100d03e1450440c0b0404100c4050544401180303da0340461544520909210700c2c0200329090942010b00c1c001944110790400f07c2c024040540e5034403d9006c5c1c0c0e01c2c1403800808542664900c01007000041c3c05c244286a542c406000c0880000911840c41d01000030310b0202c0e002d10305c5000340001040c0d0780c0f050410580300200c1c092540103010005103400804114101260752601d1360982c8656040c1450b40b03090703c03849268102101542c01c101002080c2c0c42882070030b40714140c1264440e409000507840703500d02000d005543c41906415504203140507051b0301d400998141d409501820080603d5a851601031600192500010418904c240703021440650203101e640d540405002c0402c51980100011340d02008a010346440d18400e21441000c0d0302d1240000d44041848182 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 283033669 1250 283032419 283032467
    0x20a030b0a1b110106050402040f03081606020a2c060301181e0e070e06100804060207051006060807030e0606010e040e0601030506100f0608010e13050601060503061002070b0406 78
    0x203501000c1100010082000078000014443e00703a00c207108500041000706d40440c90580351440010004016200c050010000400d80001c1c0070380c600c44e03841803035501036421236903409040030140c50305202220302c074441243e4081c0582900d2100b60704200001c8001c24260941e03180c2100307451031103011918024400e40f078900100b2301500d1003ca0311078a800307082011403c0300d61301c3e408601d007900d181d10448504d989030301070114549540b032512248041902c0c01d0208c2d5980d905110b4082e10882c80010503600c2031403c64505444180d001c04180c075000e0f034500c51a5150b600007207042e0b840b0444106240d80000340850007e6008010f2246403100241000c54010000c40c03601d4180380d400d900a035084d4016004229034403210001d248007030101c141c1d4400d0010700f012402402031005010740310b543e032007410220f2400003108011050869000c811241c1660711540000c2464009803505802407a1001c0c0984810340042001c4044c0c40401e40c149041c03501d4030030200c0d241c052078240b114525486003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 283034919 1250 283033669 283033691
    0x60105120a090f0b16051305090c12010b03010321020d110c0405010b0c0d02031309090609050604060b0f0a0509150619210e0316080903010f1413020a030b0a 69
    0x10550983d8107000b50071500a40c0b42c60890f4020f40e02e00b030501c0504205040207030515541841d030615090310300030f07690080707242d5407000070703160502c90180e40c0305000350350000014006002c0c00081d41600d108078a000b1400c41039443c210060707103c2e07504490141c0c001903d01d4021a00c80c06410440c0403e0504444140d00240041011601e081c0c010b87d041908c00907070a04d50380402c1040350091a040c3c4000c600d01040c0003500951806180111401203403201203100601030140c0052501c40d0b0031600303480030342c241840c180000b0f0106400030b6000d2034840204088501d4002000c40c100e900281803840150f8407204428003d14440030340a81c0030030180000d05020211040d0711158007507a441d90b55070052071900c4030b20705103d480e00c4c0200e41070810041101a10b030103c1601c0d03260202c030f4400e180462840ca4020310324085d4072001c0c1c0e015841c00d102001043d8040c0c200440030300d8482c0c0080c80070f40b02d1080031880d251203050041d4020344907090800024400c500029802103452400080f104010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 283036169 1250 283034919 283034933
    0x13021e04020c0307120206330618010e06031b161a010303090e0c091207170304171b010c030302041a040509070315060c030c0501020d091703060105120a09 68
    0x5030703082e1003403030f440400c020f800c10141801c0e80500540714002040c05140c8000c1c2c44400000d00d19060200001e81c4a22030701404400d082c0c901540c4000b0050750300c400340c40f000c00c181d080072600d0f401e00240684140c8885420244102d0f401541e200326110100000210310a0035a4008501d007282e02c40c480414102181040c002e01d00e5146000400480070b506d141401001d20000343c100414005410043c401c10700038403003c075801002c051744c0c0e80c2c10082200905500340b250f154030038001c40c0001449008180800b1004000f45c1340d0b0902940781030003001c980f069403000e5801d28000548064094110150f014410410140e0302c20315025207480d0b128800060511400400041d86100c0400e05214900d003d94409501c0a200c0c54100070320721681c50303000140b031080c2c840c00040c0000181d00310241440341200c810010781020095640c1c0b48905245802440c60301d00c142ea12062040701c2002111001382141e00401d030580d0b940d030030055040b6265001160140c91040142c0ea0703004c0d02c00c001105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 283037419 1250 283036169 283036177
    0x31407300f05131d01031401051611030904090302030306100c050a0602090d050102070614090f06041b090612050115080c01080a0612050609070807030309032013090201020c0913021e0402 82
    0x5880c1543c4855407552805038502001f20380e1510b80e690401003001042d0186180d01a00b4420a103400004400c0541409040d403042d10b10310358001c3e007054075100070301d40c00100540c041c0c1310549100544020b941740482e80c1e012060002021900310480d41c0000c00c2d0590060b040751100140031064403440c0c3d41d01c0380d0032a845113000700c0d611911019010390040000100701d0b0b001d000c15015108004900c0d40301612000700802c010281504000c0c24041c01c40501510b5000d0001c0ca203041180ca0f860f03001e0010a0040482c04503095820600000b0014a4240840048601660081003120352080041d40c444030700404103140741c0d5031402e0005070700701e11040c08500c0754021800b502d140d060902c103050901c0c00b00c1e0014400380c2d000507410400a580a50198202c5c4c2d0800d4403c41402140c0350321140c09680450f90a42c402c23462940c0b03400090165200c00700b0b10f8402d80840c0c500c0d45041c0700780b146a000481e1000000e00a41c0d6802d809414004c4010000c811016407021404405100280803600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 283038669 1250 283037419 283037459
    0x1c1404080f0601060512040609110a030308060f03030a02070e06041e020307030b0916050319090b070809061302060a0e13060f0807050d0f031407300f0513 68
    0x1000c07401ca103507100030a009a501401492030124035004950100f0840200b025000a0449a580481001380003094000c0302c400500201200002c0b503507800d006201c1c440a48001e440345c2d280c3c1009115030b1600004485414180d0b4010300100d502e402c1c030030f84410700c0050800781c005071101104402c0740d140205600c2e001994160042c0c0760b0070301407002001c895202440d83d01806000301440002401480070411808403031070066582c0c1c1d202c1035604c85a08212012000c1c807401c001b40d21040060240c0b80c01e21030880c941c0c8100c40303590b590714415034a80c8151444038074010015207400260800700b00a040340c0710381d801e11283d41890040495048102449a94000daa4a510610010a1900c01003000b020098020030401d0706102c00200c0d9804106801084100c2c1c00b00207008150240c40e490010b140440106030302c80000d0b0500942114546101c0700e0403610507000392800451582200c0309410f801d5403824405210100280d8265104100601841901401c005448519011094800c0b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 283039919 1250 283038669 283038673
    0x3020f070b03190608032502030a062304020916200c040c0c02090c09180a02120105031914070b0f040801050106090303120c030e1b030c030c031c140408 67
    0xc42c08101000c0c440580b030340030f4a4558106042081081c200005451040e01c24240c5404100358010320b810408038000002505030081700045414001154402000e480c0340616040c20304c0082d01c4c0300814448102c0e0000c0d40800740d20041007207041588091141700e0a035051115280d06500c4440341e06c1d1a080500119130740c05000f803400b59081a015403280c0001c40e0414052802c02d560004100502c010401440b1403800b180c50181540c40c0d0b20690340c4101440f001e81c4142c02c0410068000c1e50040340008648003c3c48000606402d0006002c4c02c0300c1e8002d419407810340b10507070300c4410b85440501c0b0700845104840e4046200b0580c40f00400010403841000c0b90f880c0d1030012290309580050780201c0a00925400410108c3c0d0031072580340c80100c400310005170500c1c4d0b14405600034000d00c20004864030500d600200c915404a003d1441c3c2c04007202100d90a128010406580306000360754243c064212070b01650407080e517030507054403515513804d001145940344000101150800e9104407919 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 283041169 1250 283039919 283039921
    0x412030b120a1110080a051510020303010e0f0c120405011d151501050d0e0a0b13140d0c0602030405010902030f03040e1b0403030c1b0807091a0a030f03020f070b03 72
    0x3105140c3c192010080c16a082c0042209036030010b040e045004200540303244e00c07070001820400b18044441c1c1120801400c0321080c50545500a669030000d0261169001484011550240010340180d1003400000700305403424030345c02a01c400da040301801c112510764032603440f12200e0808010804200e44000014041006003142034014410050b0100c09030241005040c8d030700780da03c0b41c1192000740a9802c042003500600d09070324980822000040d111304500400d002c000803240808000351800380344000c80d1229a03081c0c40d40c41d6400e405510300820002086c000000b040740e005564418090b800000700005582c003c00d0510780780300412203540d080043c0600c07040040d40da4107600000140755810070401a100d00807040d2040d0302010701402200380000f810002d03414a088200402c070201d03821142da1f130b480d00c04d507180c0850149401c01400c041502c0d883c03442e140312889202d04005c007020b6595180d91141050000000020b41c118001c1c0706551100c414200305442c014400c0500341552 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 283042419 1250 283041169 283041173
    0x4030e130f09022b1b080105151801052202070c0e070908060609190209030109080a0207060302090f060306032503030f080f01031103160b121e0412030b120a 69
    0x190900b413042c02c1c0c032042c00d0340c000e125141000c0d182034480a5112014402e92141005511308031072256110000660801082100c51100419003803020300041d90710015600c042500100c04034024020f0f2078100541e48102940003441403c100d40300070010600601e0302c0301a490714200d41846030048040f4005000600c03091903030142c42d41d001022450040c06072405c000c00000c00022000d0080c00703980520303242801842c10b4550441e4071603400103008014a03045031070112801d40140e020040940248240090494007134022142c8040005003180c1c0c403000e0700010882c141d00302400b00760305403103180c0c2c98140c0b550040da240541c101144000904032491032a00402001404000b9001c01c00030318184103200004212181c1074950050521042c3e0281f0004649810f10a00b4004541044414000b940045a07001080448504102450030380d96282441850a103010192130745500e014002601050000d80c2c25464107020f8a40442c00552030070004400c01a00708660003d9001440000c007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 283043669 1250 283042419 283042429
    0x20d081308030313030c0c080105132916030219080603010b060c0c010c2a030c05030105061302031005180a050a0c02030403020f030f0d0206010f08030f0304030e130f0902 75
    0x1005428002c41c5146024401414240c3c5111001400c0c42106c000100400c40a040381038007408012000304803e19044d0312030002c014041c00c0585900680042d280308001d402032110203060b046403a100300342d8464030341082c1c070580c0c1c00a48000b01a403c3c00350708200c0404082c9404110340665417442c160825504050843e095540728601c02e07002040f0440000b03501242850203000309007449048149281081c074a0341114041c01100c0c41c1c0c150140c242580d07884090b540031b0fa401400b130461a50b448205041c2210400d9a072a0350001220309490f2000c80e964000b990711030008684900401e6580d004601e0840040d5041000f000c0d0080401400030114800d0542c03000d68218140f0104254010194483c0305500002c1c1c0106000d4515030b2080c1c80400c541d0180f00e0144044444c44030041a000f5201ca80c280a0401180c51a400c0014030410000a407488102c0d54a485491a241d070798040d0745012038a05200d401141456000c0300c809079611501c881d110002c81d0200b104c0000c3e204000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 283044919 1250 283043669 283043707
    0x1e03090b070c03020402030402030109020a0909050f011512050705031b030c0301060506030c0903031c02070308180706051c0e010b100305010f0e0403110d0201060e01150e100c020d08 80
    0x54058401880400d0102d5040d281c00d0080380c1c3c054500594030b44450022034050300c0000c0000c1d412580d114800101481d1036806040198001e009440e8078022042d8001e090715014000c10425014141003808041907101e11683d0481c4240e0890341c0c0c3c1d59481010a01388084810903106a6107005100c00f441d060612010400f40412002002803e08048c001409404040c12034101807802003000c0c40c8984003001211003a2448268070410310240c8100c0d40080d60109408400060030800841d01342a524134402c500c01d40c036000075001042c20304c501102c1a03000700d40301000c182e000000c400d0300c0f03100521030100042c10b01000130804014807401c2c8940000c40340c0d10a41050328000040040040484c07840c0f040d999011400da00984450030129840851803500c0314003402550608485590150b01c0701c422100c1109036019540e036101c2080d0720119010300000041100c004600e000c1d40f901c08c5074410042c1440c1010165404660085941c0f401b403070004581c01d05001424283e2400140620 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 283046169 1250 283044919 283044929
    0x3032c070608280c0c0503130503070f03080f181009060905101e030228030f020903030a18150305010e0a09051207030e06070503031b0309281e0309 65
    0x143d41190b14500345800c0030340c0324000e03c00c1a80e94808804084038410000c00800c50341000482e80c46540e1000424954182449440d100b807280b490001155840e207200c0e001107c1d00050305a040000f4180f0142c090b500c0f07228030070381307200d608000003010341e88105501c495044a603592104003800c0a40c09031400001d90805c51045003541108061141c3c07010408890004420201d02c1e02e413580f002c150080c1c020703071842c0d4010300442802924442426440b50141e54820340d03041c0f180481c048034242c220321812408a406400401c01034012900420000c9688100d0040d0b49032243d50303500e041081d1000e6a4400f400194403080100840c1512030301440e00800c2c0141d0801a080c4903a5911f540c0d00c110990f004894000414514141400b40316641d003101406009180c0c0e0716068900300d80c85e81d000311018480c00031b19050f0003001d007050100303030780c4540301d0040203000a140a02141c00090701300a00c4a6202d0900700e008800591500c00c2c111540048030582e0408481038940644103080325004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 283047419 1250 283046169 283046191
    0xd0203060f011407260a110d08070c02120717010e011103010f03170409020a0807230301090905010b040204030507261c020f070807050f03010509030703032c070608 72
    0x1400c3e81c0030548000b1200c81543c031103003100f400114043e120398054506040485c4201001c0751004600d0b400159119084800c41c06507000650701d1038094981d11070076a00c0000080005002e240141861114807100c90904002c8a900598900302055200d1291710452001d03511250809110740c824040c07080e02103d005941313800c0d903042c07070304c004003404441c030026100b0700301c001e24020221042e504a9000d484990700940d600e10700200c0144c11003809580b00f0f80098040070300c2c5d0009007401d4410081c192440c0d40300305e28507460481401c0141c1880241561103550b41d603c41340340b60b85c0d94030040000394491400b40021520f880704421b02e0071074941e00e40c04202d000c110341086040020400200d07240c500b00d000c42d20555440f00c01ca18004011560300c4a6110b81302000c2103170500016a0170071100221440d002c0d244c2c1c2b290915003a00c0301500d06154a1380140202c3d40040d01940080c032480300006081d00c9101c8620500c440038001c0b0340310782041034001d25800e10803950f00100c2c132a8070a4003000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 283048669 1250 283047419 283047437
    0x906050a0e06060318070b0a08010e041208060f1306030309051509041508100605030d03090f060f021318050a09120807030e0f0303101212080c040b0d0203060f01 71
    0x6010100c00c0109201d11500d0f0000002d0340c00c450043e1403c41d80a0141d048400f510f072295050041d540c0000807a030003081c03040b0000290160699980d512a9620840e01040d0300d017a42e0301640e000720042c080d580d100300c148050180c940c8680c050b5080481c4140d50100b1428994200640219a50740005000e011020111140c400300d04e8100c41c0c07544010789000810400142241d41c003001250000c204038080c50800b01044040c580001d810743c0c070114155091003114110560481d02c035940c0c01407841c660b801d00c080204005502100380d40141c00005032a04894082c44c0c12403c144d5007004e08440781012020040001e81d20443e5440303c0d0309401080f17401c1507921011042d080c844000f80420840c2c0c000518a907109030000c0c580b0100c0d010844400c4a01a101c8907265001241c003d40045244040010119030582840400d690840000300b111300b4110720869015900030400c010848013000000f0300c01081c6401000222241100180ca0342444400c100d00301c090120740504001c10300e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 283049919 1250 283048669 283048679
    0xc01092f06070809010203040315200405010f210c05070b01050409021305070c020406080c01021002032a04050d0b01030b0a0515040b010e180f070906050a0c020402130f0906050a 78
    0x10848602c941c02c10b4581c2c0d1203050000040f89180301d6500300404041184c1c4034041070360461340203820b040ba58a00e1150f0940f486c2200c03c800343c000c0f44515030002c0c0780d104249034a10700808000d503006412000b061084604070714074006803000c2d5005540010b2000440d6014026801051030260804850502c03001e050fa40015242c1816200d1a88010380d580000c0340b001d6008207500d00c0c11a074058014000140e50382001038540982c00c508502501a9401d25030001102d0720880703200b090210b00720320603c500032816020460a90313030b51199031541000042880e80e02c01944801041c481d10310b80c0030303960643c60301025100000e00700c070b5a083d007454240000255801030002c5401e1091f80c00056454200c40100c4154000360350454101c03103070300c0c40088190910710b84517100d210a82d9504d59140ca07480011135000c03440d8810740b00000e40c1444020403561107242004041c0380018805410454124040d104050700c03076100305c008030700c0701d0300c100403484242c0180402000200e45c0d03170020502d04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 283051169 1250 283049919 283049929
    0x14070e04120e06070c0b09040c050c070306180b16030f0b0102060403050307090e0c0a030c0203030f010311180f040606090608030d02030417030702030c1528020c01092f 74
    0x21400401401440b000c0100a62510000d54580c240c1141a450410740d4400c0000c855034400e00c0c19074007540c10130304d0841d0010301800454224500f600011705205245441e001c000346803144d08102c00070742d090401c1c40801e000508090241d03202c00482d801c880e000b00c0d000340850301d184a00e00e20040c184100000c19030b8010900c10707400fa40509000e40d481d1b03113041c022254542030343c201600c0104000b050281c0e007440c0c480a4240c2104c107031410084084501000d0340d584c041100c84800c21001140103100180c10300d5000b42c20610090841c102d0700616124020361504200c55991044e0003150410003400401c0c0146001000c00302401c0007001d082a8440d5142e01c14001c0e00c48040d034000001c1410020012950701144c03038040f514503201d0800100c000e403244c5c01003000360703001c1c414a50300c90304032031001e09a24020440c2807400c00c041e0450940c021b0011144c15070003100307250b0030721203480c1c3c0078020301846180500c1140c1c10316000f100594481c00700141e502064445003e07000101000d40c03a8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 283052419 1250 283051169 283051193
    0x305061503010c1b11040e10050103020306060904020d060b0f120c03060a15050d080903030c030301090f02120726010623030606040302060c010917030105100c0503030a022514070e04 80
    0x22000700e0495185072030111b070280c145261f03007e40c544200002600113150359400700f41a00c0c421400c0d50310304d03107804040100c0140c00f541c000e0b6002c6101c0354503c0010301e059000c84941032002c1c01d060243c40c41040060041030000031000d4a5400540c520821850140501a40840c2e006010807011a40d104129110b040c140517180c041ea0766246500207001da41000d0f150841c00040441c0d6568010110080d202d0300b00388030f40758403036041c001d0b40e03c1d48020381d000344d412904089111851316030354401c0071520750a514003920044040d501c1d040300e119486001c80d41c042e1105840310481c0c18103400c03859030403c028900000c0421010b00c00c3c80b12a40d03403c3d0468046907012036072541c440300110a081c5c010410030a00401c0780c076201c00c0c610b241c031502c0c9014504071407045030306101e26018100281e469844240740200141c004100040d00518142d015000100907201117030800050000c01404a007928002a100c043d1120034000b0751160800140d0040c220100d0100400d0402ea036030f02643d20f01c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 283053669 1250 283052419 283052423
    0x50909060f06120705030a1208072c1329060313122c040b01020a0b19020d020414121903030f0209090a060906090c091703040305061503010c1b 63
    0x140c1070502e0606620200113a034007501c0002d0555000c0700d46450002589107070481d50a0100d101000000c4542d4000c501011240e1000c028503040440d01200e2100b03001c00710382c41a0ba220b02a106400c3c4080c0039032040340c00340c000004940c0007911078141c10f00b681d040c1016200384580000c200301311001100701c40715100d079039001001c03511640741e40c241a80c07140b6a207806c030491490183c1c0da80c138443c01c40920b0400005400d69007004813103d40801280c5901402c10043d04002840001c00c10104a0551100d8002c030a40380050400c18a18406005c1e40d003d54001036a419146980329054642903880d1042448c1040003802d0080902c0058030071100d40d07400c09800d059031411044041407142e0101c802c9403a0040201d20f4510700540c0c2d8030000c2c8914018605000d180c50800304017608503100341e0103410304a0b00c6800d6002c0c5403a28035940c20501d08201145808240000030009030100000750080c2c0b401c0d0601e07283d004400040c1030031148070540c81401c10030462589800d203c0a03045004d00d642d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 283054919 1250 283053669 283053679
    0x20303041502010e0f011b1d2103040623030603060403030b042316050c03091c0503030c0c190206090d06060308031303030e0102030108070e092401050909060f06 71
    0x61441d0069004010b450b402c1d101d035000702036134600b01c620198000c00c06082c000c2204a120807014034200d40308216065442070008404031f41c55200e00e000482e100010b5a5400103048032407402e1109420340e00158410408202c0081c0705507030744502040f000c00f003032a04040c0603085207000c00009541d0b240140028007416514110354116841c2c1da001405240c8a82c800c0403951144500e2117034510804450304080540e115008100c0c2d14480d00403500320751807c000941c1052119010440b0015454060b0324040400b5842040011400c0c8043c0d44210903142d442520741d07414000c0d0350f00380031000c0b503140d95042007071010800580d656019181c00c100e064410f54402185484c0000c020301042d00082d0200c44040100800d0707010a5001c1410b0600c20390f0140510903943e00710714280d000030702880085800204061205041e0544210350100c01c04084a40e900d00c3c0151780702590f8524228415003090f60030040c003050600768406508946880700078011843c09030302e401602c08025000e03d110b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 283056169 1250 283054919 283054949
    0xb0408151f18020f04061d0103060f1701140106090f0f06020a030c060209130b1e0a0611030d060603020703110604260909090105011508090714060d09030206010509060d02030304 78
    0x150b05641c16a1107003060158216604ca8589a020307088010710181d0409100344440810043c1d4403e000e1401110702003c3d07484c19080c1826541d03218040c007403480c81c00c191340e2202c2c0c03500780362049601c0b98024103458450582c40d604261002043c001e5a410612503518140c508008281d80026070240c5240c051812108000081c81c1c4000a0301c501c4800310742c00480c030003100f66400440d80c8202d00240c1c0403500c600d85000200a810300204034001c2d5154804203400b4200540c0b4069031001d6192844101501c2c58500382600c00f00c101c0d200d0360401000a40e010810380f080640003130b284502808800300a24007440d05585a4030800e4460101d2098580d50303048491130700c900c1c8030a4416500d001015101540381c4440742c1802483c09100c0c3e00d4078080802500f0340114051818580a0300600c00070340445800e00c0b82c0c0201540403800016000241080941c46c000350724403c40e017065110f98042d24255140c41c1c20444500001b07007030340d0305c259224901c120050b5000403c54044440d100400014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 283057419 1250 283056169 283056209
    0x1002031003080a120605100c0f03020106080a120f0329010e04140405010507090608070c03020a15051b09130504020303040f080a05070e07080403180b0408151f 70
    0x11040d02940000c0c89060301246102c1916003180504282054220081042c982d03034404006484540f507030082d004c66a0007506802241c00b851103000b6860013800007107a0f035951540d0951801c01c00a90544403992800c0008102c15403004400018904602d428044401c040d000c284904082d980460b9240d400c005041c4866402034480d00d12038800180b08010080e40c0031150541400e00b19021103180d464240010089405444c1c10016100aa55201901e07038071800d080e107040c1d07042d001c20f40540c45044000400640c00b400303504a041d0a40c10085034500f000d000c00c03140e440d040400300380322003c10321070020740c0d40350244014041e0490080c085550341752800402c2c11440385030007902d902240c40b02c0224080c1800101e9030040b52240b42214100307583d07403c2a51000005440003c00220044045008a0300c140e04080059030b20040070508150b99461402007a132040c0c0c01540103070403032580c1d865003080300300300d0b10750100710060a0070910440c2101442140f013540a25400050100346501d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 283058669 1250 283057419 283057441
    0x1008040203070e0108030c01060503030c06010e0a020c0109030527150706110d06080601060306030b150102010e010c09060f020601050d0803070c1202060f1e0115050d05011e17100203 80
    0x1006020603082c583d42941c4801800f81c80c0d40c040750600180e50700f00f060010341c50800100300c40000045001900ec0340e4240f4000041c541d5016010414080d000d21090803004001e03c6817a14040c400d480d41a03403080100d0240090740c0d10b41c0301071500500248450f0340e103038a40c0304461034807000026800da940c1846181413001003030b002d01c012441140114510b41110026882503046e503070b52008455050381c0e5001c08a0980c4c031f0034040101502440f00c0071814400e09445000181d032030500021078903020f825003640c04c4030300f00b400b070b0800a06440c004202d0f090700715681e82524800d0b840036140c558100030208000500001c0d00030b1050344000001040944554207180742035910801544010286201c003d43c1ca0505868482c030150080300800d0380c6000c130400301e4209074685805900180c4c0b0300880e0b0000612240c0710101800b6080044140401c07030f40c494030340a082070300001405924013003020b0200103001d4018410600d0300702c0a02c24042c0f000541207120080c140c0c4056030300d07075822510003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 283059919 1250 283058669 283058683
    0xa110303120405070303030621030c0804120b061905060909040201140f0307020105060d030c020405060118031a060306040b040f05031b010b0906030715030b0d02120d0f03020301051008040203 84
    0x30891055407001e0204000c40428044100e9001e41e1781401040d4031008805044425681000b4441445e0010900041c0c046c1c2c0b400d600c0c1d10300614400f41082d07556101c10b1080780c040441154001500b008001d500e280000701c4030392480150708801034150401021079100e1081c1c00300c0c01d116000b00400074003160321030704401d80480e008101481c0c031803c01410810090304180d50324800340d4246000070f072075801c1c41e0b20140b19949d0950703140c0e508480345800780030007058080c04540c1000543d61060056806100200c401940709012468030341100012034010600044c1200d032013074009a050001044c84c1d0801e19800c29000818254072a0f1945003161171407155800b541b0745030303c1b10070f42c2c21a504410752025903042810f030b65040056451900301519292103000390038001100061595000744280c0c0b08008004028000c20440070785900011a040440c482801b681d034040d800b41d84002d40e0010394050a854641015821941071100161881da108014102000040c000140565800300401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 283061169 1250 283059919 283059937
    0x209040e1605060f04170a12030b0105040603020304060e0102030903040f0b09090417070204090b0103020f0d03022107060e0102131a071e1202011d03030408040504020c0f07080106091406030a110303 87
    0x20410441c1c0f2500829220b24a005098800401c070f082e62324641c17402405a0184403005a403407030302d043c0c14908103500075000a003096a146035900d00c1c40840100920046028030840d00c010342e203c40c6002c24007503441825401180700e82c2010300c50440c5503210303143c1280e0481d9001c03461350400e00342588200100d000b01d80020b0740c01400c01c568132040c00300400c121b5040e00e00a8500f0201d200c00001840301020030071000400503403001415903601009203000c5031620030b000381120321b8010f46807648829107943c42244c4130f40d654000741c045155107580181400404030805070000d5042c1e4400d003001302d8011140c0192103454210f01c002000b404411400400035070040807000c0702820340100134001c00264074142107050401d050858190340010507203128591002d02149054244400d01000e0b4000d008144818861081e0800c00b100f0b0074011100074083d04400001e409242c0309165040e0346caa0b0450003070040501c003e02c2010384000c41c010050541010402c11a180380c4070110b0301d07510803407210b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 283062419 1250 283061169 283061189
    0x1605010c050405180910020c0109080309070f1e030b07050f03040515062b0f0f0605090d17060108060a0b070803010504050a0c0801360209040e1605060f04 68
    0x2800c404940c00c240a0001e450342650010001081d440c0440510131043d50040c100380e200321406003601455400821240c001c41c0700110340d99000ea5200c2046800c242e0f804111038010700780c240850b6015114200041454480242d14000411020680110240009889007182c900040c0602e405201140c81d03c6919051440c0c4d01d00d00360400589414106d0600341c2d00240301c0c40414128607200400b1032900d0341700c0300d15065181d03c800400d4041c5100d12000c450508003110024085600840c001600a020305008a900d2801203886410003803c1d00d183c006004810080b6030456881c0da118507407281c0c003030038200040e0b00c03004005504200310344e011f14483c603400920036007001007600107141290342c00e48041c00035880725607807841a40e50803940d810010b444880100140ea2410b840500100c80c903c0e0140b1107001d101c1c034a44040b600b0300300c03244190741e0001131550450416201702105001c1c801c0c040d06005006040d21000c0c81410700ca054451000880e400e41e524040e201110014880914 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 283063669 1250 283062419 283062431
    0x30c0d060b04060e01020c0402030c0d200a0c060c08041a06131a040b1219080910110d092301020c060703210903050405060d02130b040f06050c03030705160501 70
    0x90080008505131941c40c0180034030030030b8290500f41030003980d000f01c0f10800005e0a1607442181c1d80f00401c4040800c003140c6070409d41000ca40c142e00c0d801045c01c2c08556503200c2c10014a800c10384282d036000c055040401c91f21404001c0410901c405042c240b40c5007070203142082e103400c0001403100344100011541c15140c019140150780c104da1600c4503515007950b091100f40c0080c8100017100305054880c1c841c039085082c0c21003a5440340b0415445182c0309400d4581030081040101c1d103450720540c01c07a00400c1661045248000040100e120340b0311480ca060845075040c6068501003040c2c2e0103006174800c02896026005a000340044072082001418803034031007030a8240100514111000303107c148000d141e0b00700e200782c1d01b40903d0108a070142c59040c40e00b0700d40818007040d94400c141207510b4503804d0101c0000300e10422801c4008002e20f090003900e030707410404000080059a40420240082003180038442da80c01300a0b00e5000c07010742800790300d030703c0c020745110bc0000c0400002072040d46044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 283064919 1250 283063669 283063679
    0x901170106030c141327050a0f0e0f07050418020d0b0a11071205031806090606010e040c020a02151903090510020708120901020c030d05040204150506030c0d060b04 72
    0x54070200e00000c0c542d6580e0103110380814100014402c0301050b241d1401d00d400288090f022100200c000d03c1e80c030200f0700386d24560018030141110740a850138000240c890015071b194000c2c41c0200d12a80800340040c04c8501e80d0919501d59904040c494540519150f281510010440d070b0703100c070551070b005803032041440799616001854110031200b642c147c51809400001042000742590a011750141c0420b0b0800911078082d95150002803040c1030f440502405001c030f00b1400c0c083c0f24000c9610100400003424640c001401b040441051240558070307048940b0340c01340d800900a20ba0907010384030641c10020500800005100d900da004040d20095485904850707810b81c444000c0302d01810603100400c00c021101800e81c492442c000e4007410050254000920020005a4004802d4400185130421a004d00e0f415604a00d058121950741c5400b00301c11750074a409604c100048107028030165034284070006556000c081c3c10001210300c00310b4290302210f21540042e024120030326a0585031541e40c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 283066169 1250 283064919 283064921
    0xb2205041e0507140a03051f03080903011103060607020402030402030313150e010f0801060f020a05060c120f22030c1a0402031608060105010302090a0506120f2a090117010603 77
    0x18420300501e80e4540300c00950325034800c00610900310181032110f4500351414104a000d8900a040b080c400843c4000164003c940500d064000f1740c401c05a4a4aa010180806007100c42160803081890700800c104042640d41c10101c808281d0704840041e2662224000702e442c50107207642c007180410100304041217080000103000c8000842d40d5a80d03401007440c6004482600c190039600e008500e500005000550041c22081100c3d10a071040380d801c1061354443c10f03d00030050390307007110650001904210510481b1002079015952503001c01907414000c01981800d1070101a207541c400240809604142c4900603a9075010b400c80b01244021907580c845203803c600c103132412031003840b4401614076071540b00300d02c100031500e007040035042a138680070041d0081c0d48494800e83d4010240c1c000800c083d522100a0002e40c001d003070700700e44a0700c0d05003038988000a000d0075030300e52010314000a04502036010100c40781000c1c420141e940301c4a00f640180c80141c1e101855814034150100041203050385 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 283067419 1250 283066169 283066211
    0x1c0c0306051503060106020a0b070c1a180c01090803160c080709140a0b010f0e0126090f0f0a0219050402030f1f0f03020907020c030703030c030e040203010b220504 72
    0x82281903c9159a1b542c1060745c1d596000c05000b040b030200000003c01082c05003503030b812098014480c840b406890000f1404078620122100c80f03100b16a8030300004003d108104101c8094000e08100304d00504011019540b8002d85a034072504c10214625070b000c00c1490b285881c014240c2c941100d00c0c0704d031252240c5c409010484281504030140030f0008011240c41d000d4a40301d1901030311030b56040c00300040100c5aa4013007080e0740d8144035000860324555803000140c001102e1850703040e030200b4207103541401d05004086425000a034001d855800800740085a801d4140c0d504030f9828440d881100146151454540e0120764014404020001d45050805030b542c41981052650409a10b0714501c000884200340902210440301f908148014100041148d4108585004980d031034051030002030300c0d20f8055001100020300f0075104604244d00446003008011b0226030660840d1304142080005000b520640d0101040c20b5140c080700410030003c3c2c6015150141c8240130740300e02d104052102ca00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 283068669 1250 283067419 283067461
    0x807060605100e10270e1602030f160c09020403030806011e0203120c07020901030305070308010e06010e0409020d0b0c04140f0907050a1e0305070305070e1c0c030605 73
    0x1e201d11401c2042c9100c1c501500c140d640c024444c640404d141c1da0116007810381d1000e11100d2448114010900145040c0d020b0002c0c584482d280b01507203840342100d000d101c205001c07441954020b0041a00d000c82040941e03040c00504a0003411207041410408007481d020343c844c0900510008001c014150310000140c0300344400c3e01d4030420705101c9000f940060841c4a0b141e00160024011032101070004806282c0100c10b11410508240070780e000075102070740c281e000f100400d02c005420b00400d60001141030050201800c1c00b0107620303051002805040e00b41120a10581c2d503001400c00b1036882014500c80c5940240d02c92240346444000007903141d0241c007c0f0101c486d240149003440e460881c80441c0451009810310760340b0344952400766569080b10440e0000c6c0951102d8030311049050b0300010030941007a85d800b08847c11710040246c1110b4001c0c1901d400c10010510403070b55070300e402e240303101070450031400d0718048200f90512040941e05604001cbc100c80c1030500344010102081000c609a078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 283069919 1250 283068669 283068679
    0x28020a09050913020f15210601020d090806043e030c0301020f0f0c120c060403081602061b040b043b010b0319021210140d080c03070807060605 63
    0x51210080080040c01001d0f00a50040c4940305000e03090070200c106c10851400c0741e42050514400d00700ca030210b2102007085028400c20101045070320341c2c0c100640d480740b03481030070038a940600f00b00c595500c41b40000c1001d865174a803025045200f098895104000c003110803807419040441d45a030602c0340e031400070f141d44039200752140c4100e64507041c421035401c8910280198a0306102809000064000503201e512600810b60000b1000f50040000d1520314210800b40c10341d0714080c50042c250342c40c0580204004448044800c4d005a000100c540e003001d03814600c00c00e18003090100c880c161041d42c0040814600100300010380500c14603420440d110303281c090030485c05c080c404443c1d960700e141c5000044640c200c3c004105c0480d00e50011500305d00f4101181d181c07125216400420b9a00510410b00201901c00421511401a0000300082c2c100c03e040714044032080c02c0040c440040341c2c0303400341203441c0000314010900030400c1251101e0390310141c225221110707401c0c460014440c502c0781601030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 283071169 1250 283069919 283069921
    0xf060d0518010e150615130f17030901031109030a2303120103030c020103060b07030c0506180a110301060806160f0e060a0809070b270d0b28020a090509 67
    0x103004503203511000500600c032042144c3c1d041381e44210080c00054002e01d9001c450202102c0410042008202d070322462107215203401c80d6080c1c48041903000c04d5541c05842a450350781a00401200c4001e0700902e03000c40c9214806a550803d440346400307050b171500c50301e40d00c0420802d00d65041070100100d15100421104144696078a82c420031184500303d0584000600c006401440118900d90041c980014000c4e100c10b4a80c55070345c0003100035004076025103c044100141081b00d503920542a00201c00060480340d0a01e81d500c0d030030ba80080c0b80c4804003240e920a07450950148004122a200f101d600741010070701200d1001641142c0000940d5611000034840d005e1226101107944c0544080d2030400480411581c0000107030400c3c0d00c41c01508000a0420080300181c548603610303800456601c103072060b03001150140d030030842c0e0150040c003c14001080b50b000841d940030040f00c00c0080c44d12203146000300021103029448041610210309940c6031076010348a203042c0c402c00d507480c10786 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 283072419 1250 283071169 283071211
    0x30e1c050c09040f02010c03020a0b10230a121502070807051006030506061516030e0a061706040504050a0b0906010510052a011e0923030d0b0f060d05 66
    0x203601200c000d0103605140c44d9180043d40704036803005400b8081c1c41503400502c0c0941d50544205d000780c0e019128030f12601c0341400651088541d400c282d540700c403802c1300005001808a407d905035031040b5410324210300d89800070b126641d86501c400f400c0f0f42e0021036403001c884c507000b01c3c6074225140982d540d100350304a40350380d22043d100c1e00054031f812070001d010b255184030801c0342c0016414000c1c2461182484105560658100c0030001213102c0c0c0c40d243c5d800b0200100b40b203420708095000e0402c0003603a910002202603201c0100d500801e00391804961a071f968240140781060a10300140078031102c0d4108844680d0114019042c0e44044032050340c0300000b08012102e60003100010050b2108040d07072012102004205e8a41c40d066040001c1400c4880075119011202a1690216501d40710b98880003080f81d0007041850000b00180044400c11050b40c019a503806140240c0d120617a641401c9040303665010801046144001c10380340da00d8000f04a11405010241c0701c440308400c481c60071501e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 283073669 1250 283072419 283072429
    0x9060b03250206060d0206070f030c03031a0120032704050a0e100b1906030906051605040e06060d050112030807020c1305060a080f0d0f0309020913030e1c050c 70
    0x44600741d0741d8024a11615000204100700714100d00c120783c0b203241007000c030000070742c403046100055000e6129503100d4403107824040d00341e541030a2011900c541e0350040c1d83c0c650380c0010800001c59030b9111040100c0c04142181840c41c071074444086a018181a500450078070345001c199080710301590148490b0302d4150b04641900e00240760103405403c0b0040ca4481003945600c0750074030150040650b81039051024030388065116941100b00081e80b900c21a20602c00700c5e01806420028070030301d100c03103a003010400804a00507401a05410140200030508903903600c0140c441811154804101d01c1d44e50760301c2c810700c171130076024210081516000012942c0d8000b06058050000142000c2208503545282c0402400300a201c2a8081107115021803018803c00110010002a0300200380205404001511603040000c858080504003041200141c0301d000f82c1c03941041102c8111103040d426440c0581e034000b0184145600464002426684c8100c920318480fa034078007a0007075403c000f00b00800e002c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 283074919 1250 283073669 283073731
    0x3060b03060103080906160b0a0c0e120a030c03090803030a0207060b191a0c060a090c1a0a030203220309061d0a052715122b0909060b03 60
    0xf60891a062190403001d040800040260703203210442e1444082e8181d95840b1400004e270342e40381d02d1039038404604806a0700401c0c42d4040c00011160005440c880d820026901d604114004080111020040302014014007561002c0e01502080e40e440349010f9000350001c2d044882c09950007402d001410340c00d41409046507954039103041c000d4004606003100d01c240d1070b4201d1104501d08408010b1051110b00c140041401544800c202148500286c240081d4040e0541c02c407100024071861407101041c40d1008442c1d04506904000d0384a54034013954040b03010015200100610020028008169004040c02d007620f2094450003c0c11a81c0301c804600ca10f207102160340c10010700c044c10300c5a0320305034030f040d102e071001a01d03881c06030300384454150030481060f074801c61b04060301c054001842c9040c200201d02c01c4104030050100d100300c40c20b2440358035502d091209040c031200f9041c15990f840750028030003a103181c01040c031405a8442c2482c1080d030044614202280d502443e415414075541c160b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 283076169 1250 283074919 283074923
    0x3190806100e0a0306050411152701030b10020106090f0e1e0106120f0c090b060d1a120c0a050409020112020a0512090c0f01020102030135060c0403060b03060103 71
    0x2446400c01c2000c07050310503000801040b036108159a10010000d44240500f0f40301d248146001c1400801c07040c1803000701d01710080111880042805a01003108101e424035258107044d140d2a01101400801a0020000e660f403240c3c005c2a082d01034545070790150014011650110f40411400521019641c1180d8035460440700540015034400c4001d10320040d400303d015580d01c0005601035991803626825600c554086440c0d24505a00b0014009030b260010010716141070184641c000c03050028180384075460020880c55940c4140e204130041c56680b5400f002030140103400c0401b220019141d070340310000400c0f489800342807404601400d00c0d0142102031541a11803020311084401c006029402c1110000100719051240c02c2c11a841020000e0051600c1c5010f450100145000e01080382008440745043d60300400040010384020012021600c2c00c0700c0103101041c2602211140784e0a401c1720054140c85008240444010000d00520440c0c1c82042c00300b0058024106064841c5d03401d100c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 283077419 1250 283076169 283076179
    0x10b040306090809041e15141e040f0e190305031909120804060c080c03011a0903100b0310060e0a09051f0507090f03080304060c0210050903190806 65
    0x420000202560403030785500e0b2043c0041414015043d011a040710500d00f6000091000000c0b8050f075003005208401403c160040704140207820000041ca400070a0040a4015124400220002c0c07010700c1070300d03001074070080c0709008075442c0f0940382c0c02401203500703102a07600989100c40d0000b20b54000070b9418945c90340f562429952406000e40300c1400044605908a4803922140001801e00414945d03070741481e00c41c1102400c0500b455021500000c0f002130903c50000e00703101c46c201800080d02d04654200b0543c1000034003c0c04c182c00d0b0750040500c280d07050b01c58100042000802c039002558290015402c5070400c0c5003041d602c00940f00780344161300c070804824011400300d400a4015048240c0a07604850320b61851442e00000c458507119a40e41e010b80d03072024094000d501190203002407110000c1c903034509040d0780b90f40b0806e2001a0000340010341e90001400458020b0140100c22004100e08102d2032401801c11600d82d48015a05044554070201c0120814007681440f800750b400680 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 283078669 1250 283077419 283077427
    0x3040e062704050d0912020a180902090901020c0f0607091511030c0c010806190e0a1803020c040b181303031d010f0b011704080304020d120302070203060f010b 70
    0xc1406101d10030781074a2040290300740032001240c0201011180140c1c4520b004102e0f4441e1600028a104100c0d0409048001500c43c050050fa0703030002004241e91244a11240301c011030121040101a0200e00941102040c0100110010b065018015001d411070644090448040300d40761101d40c00c90f440004507914a000b07020341902d8080f0303100e070b9078201d04120705803101c12140e0514503007000078184413035488414000307119640301d4000b0750440f00684a10300d0400801c0100d100c510101e00030340b5514840e10002441411040e005001c1c0c44540003241d4092000c0ba05000713440d80b80d900207860180d4288060100c041c100300c0e8030f4814001c05515840b0300d5403a009a0500c01245807001901055281c042280d20502011150f450024102c0e00008003650800c4050040d9441050100e050020103e240d80010000c002110341c03141d03001000942e81c1e03607079200080c21450300e0341d806007541d64070035003540c401741d0941d00408849000b202101c0c002d0303407a03c0e54000400024050100d00c850280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 283079919 1250 283078669 283078681
    0x41107020109270207080901090e060105072a0f08010c1d040209130c0f091d0f04050a061803030e01110910030902040c0203030402150405030d21090308090f03040e 72
    0x301d01400c3d44041010318180700451420f08420382c1c001000541d03180d9070010351001c0c1c640c0c22107400e40041040001e2031301286040c50019005000b00000034001300503290801c1e00d189050b200d10742d0010408021001c025131941407148803500503000d02c00c410362031300b5001d01185004481001c0c100456107000c6190900100074803002c0e400c41b2948a822640401e6171800084050045030341a4645a4402140c03403d550700003024014558400c00602100c4200c4400b03402c138032544254800340d10303680d081e040d48891521910700310344d001c005802c440c5440d04130009080d00310780061400e40280c1d0140120303100148a2400c8880b442104241007504000e4000c2c0c07400c0010a99255010324140046c91100341e0b00400e040da5841c00d003003001a000042004114504403c1810480b90b0003552541014186004130b9a00ca10f540c011800340443e41c6502e442e00502c0784004050418001000c1c455980e4074079003d800d030802a10542d41c24064a4201e1000100c000300b0b60342203031030500d07002e1b03480c0e02c0e90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 283081169 1250 283079919 283079939
    0x5030f071104110901030c0513031101090f03081e0a0f080a0f02041d2508040c03060c110c0d1a0612060106050703120605010c02151b01020702041107020109 69
    0x9031021078144a950580c04003075601e07071169001039200d00350040d03a81d49491000400301c444a141c1501881424080d864642012207000c009032607204040700f00c144520790040c2d8442a25a0040d0501d00f401c640101c00c1003400b00144c1b980218440c5075070f10802000ca6988214000c0a200740005415000114085445090899040794043e040090728800b000c4050060742c0c0240c11995207180701c492804d206440c40544e141d0b2044c0c040c00609071000700d0400c40a60030003000103c0d400c0240d580e0214081c021010740c202c1c011030307100c3c1d001c000d845514080a00031030003c224800003800341c120b900c1e01d5800c00249400d00542d0041d4010942c90400301035280c104405130451740c0000c3c0444148002c64400c0006901134203190f1200c546901052030024450108989c1c1003240074140f5030204001c1e43c01c210603c0d62981c0c101d40001150105803060101c43c0209403102c031070700e924459081c7c90728406500415009000f51401c0c00b00d4100e01c001440741d84914100240000c04000c4208003413646 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 283082419 1250 283081169 283081177
    0x210050c041505040807050405010e15030c0603090c0a06080108340806101409061c0204110a170112080703030212190b150f07021c05010603030909020705030f 70
    0x2610041420542c0740c090074200b071181ea24001001c81c0b00080c09020a1008000312002003800b1602481070b503061800b0188d011001420350b090310111415130300c40360b90307060003504e030401c4014283c1600d030b10301050071a90707504c508440a0f0044a0a040100307005101d903103400d041e02c030250f004110a1942044035000d5461800c42c020207a00c99a403070203400c0107984c0b295401852018010302e05400d20182e882600f20326607000300546441c0300000d007580d80340e05940d40e50000040301c1014440e114100f45c4505908240c100a52041ca0101c40302041c003c00b9010341381c40b00030340d07035414514a800d10104001e5002070080b060748c0b40c030300e010040001e038072800100403684c46464054182881405200008201580d45814214100e00c100561443d68130440141c000111040260300420000010381441590911615810009540d80070b5480300c0c0000c035210392040c81150010a008e0a19500a28640c0000c800089003a4030008110f0058001c0d5038100b07800101031480d010f500706c62101c1c2a48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 283083669 1250 283082419 283082431
    0x70b1e0a0b0139050718020909012102010f17160e0405091209031002030a0b04270206090a030203061e10030305040b03070e040c0e12030703050f0f0702060c0106080715021005 77
    0x8178100c008a04207103610406801803e02c00c00c007684804010007008a505016002850301c82c0082c882020041a0ba00c0603403500da4083c240607884000c504012a070740c81203424201e902d5081e800c1800003400f180d80c1064000103060351448000740f64041044243c031403e0b59050b001c0d500c050b072050001d02c4000001c00d0178000090894601c002c590200c001642c208540c20711a00b903407142c400c070781810301d401500010411194040c40c05100052500360b0705a01c2580607018180c0828554001e0704d40c41e0150003d50f4008044450918010740c407000f0404640520991420b10040481d65400048903400240c80e41030b1105414281400080031040d00018584410403140c0d049204545d1101d00c11400034849581e034440711030803d0401e10183c0400858103039490780c410002500480d40c004141d80c0d0041054000d165039102140b030003021405141c2c006035102c1070000d400b119072a01580801c1c21030740c0d000c0c1034480c2107541e00c440307184504900d119440560440c0348206002c8905502c600c0d8008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 283084919 1250 283083669 283083673
    0x9130c0c02030d080403080a0504230708192604170304050d0b070305010f062c04112508070305030a09120917070803070b1e0a0b013905 60
    0x64081d0002442c0920110a041c0462207100c04d210602d94460402a400108480c0601c014107040c0d46064501c2d02e482c022040f10f1481070704040c4001800c2c0100c4006012241c00c440e5020800200307020004617401b4122185040c910101d04c0400b01c0409242d4880c2c000303ca22801c00d850300c9102c40c00c01d55404010407a9010030800450303240d0f140b4200803030320740c000d1030b0800443ca40164050221801a04010b69034000014200580d5a01c885446100d01c50899030500d070580600790844400c65958106511500f0046003540f0139810030050310406100c0d03e4602400c0030684000c00c5c0042c0c0201010701380d040c08110810120b4050402190007203c12040010074640688a200070400030000400002e00414010002441402d011820107060308014001981c0761224941e503d203c0d403100140702250030350000700c540445a0080400c0d4509145c55030003850006240c0c2c004144a01c4191702040c10044242c480f100b03152048450740c02c074011409000507841c4010b0b501c910184030120303054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 283086169 1250 283084919 283084937
    0x3040b180d080103020103151a0a120204081f020a050d1d100c0f110d20160614030402090a0b031e011d060f07030c0306051f02060c09130c 61
    0x94a001c00c00c07503800084660ba80750039541140700044c1175035210408110300d4650910709101c000340422892043c00300506405680300b29040055030101c521200250b0114030220b000100d5940c04180b54140482f079044428540e000981c0000413405450708410010701d0600c007019010889900184008038030303400408004660200f035602d055003000c1c4441002e0f0721485080a62504400c803603005910600b413a00008a008007c559034542160301c00c4100306182903807420400e20002490290491038040e60014200c40c030349a031400056102d4840010b00d81d004072208607030724031709607402168000c0084400780c5813416620003400c6004065039144c0100d0350420001419000c102c0e50385103126001180b2964001100e2000310304020107509541c21a10401c01840720b17907c2e0095100025050004460108007412001170215800450700300107038071419003000404182c5076414101b15400c8900c141d070b541c601300007140a64840d03542c01c02000c031a0284030102035040006044080d2400700300b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 283087419 1250 283086169 283086211
    0x3060d1506210201050d09020604030c0f0509010902180f0604180603020307090606020a0b0a1b02060f070315050409020315011d070c021020030309010b011206050603040b 75
    0x280300090122408565520a0204124049142d5a1503800c00c52445040c0d8041640c0000e015445050420900c280e5154134031421580d402050310055034005c204030984640700c00168540000c180a0540316460303070800000c01202600845181d5a40c0c844031001d09107804040c800c111f02c2034100c15602c81d0f4140008106030b072540c40c1c0009562007241022139280c4c510300501d82000e1140d001a0815400c2007014010b5640004582d04410340c4005000002d03940e09034900000c240790780020a01c1414070007200481c0f0343c00203c071802203038030200740042074403444416000c6803403400c000403071005001c3c0d0800035032500e40d0112004d94005015035645500001446034041c100f49c00c0040000d0708102000314800701051103d52282c0d0038100000416200d40028285403100c815a00c2003000122815011010064180c1050b44552086136240d0508000040c0a0940c2c2d50003039002803070b0174103822014010360142d04c04545000c1d042c3c40c40c6480f5500c0e80c008c1054010a9810a07000d800170701c0e12 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 283088669 1250 283087419 283087433
    0xa0f05010510080603120c0304260d0c0c03120f020f0d0e0d03020c0613150305011a0306030c0d061a06040e010e1308160605010506030f190902180f011e0b03060d 71
    0x19034011210040c43d5502d003006400e18461400103504c804c440e4440455102203400041c0d212800101c504cc25252100f851503c920664101d81000389228142d04409512a402240768a8941d04a07000c2e80d44006d004d4902980c0d44404000307480015852103150219801d000159403131450203481601e0000312442e0105041c0d52210341e00b007d02d50102d540405c0681004010135070307007507000e02c0d0521140d41740c809090300f4140e0604504201100c0000070502903602001703d4110500d020380204410861401d050000340800655500b282c0400c1046107080c1c588442101c090300d6a920039410282d00700078000300314841c0103042024a41c0c10448040116100c84044c00b400b2141005030491485940ba1840c00c1d590117a011a00840701882444040f4064030301c40e541c0001c4849a0902610f8550301c1880540304c00d15004e0740020607070004003001013805100d03d10960303a01d4a140350f103036a02c1d8103100140381070140814403002841030501031044e003407004580100004000010604040e00c50031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 283089919 1250 283088669 283088677
    0x9152c010e061f02060a020a09030219090b010203071707030c020303121501030608030706090302030f04090204030c050906090a1e0e0102030901050601050a0f030f0e0d02060a0f0501051008060312 86
    0x24140d41c00a8100003140c5004200c0301e10841150f4503c80710550b8000d0080d51710310002c2c004240c3e0640128924100d039102da03140388020360300100103811b101d03580d08504031401468020340d4800b070300f858007903481d55000008880da91680041180e1000110340440e10460b0001d40d82101044038130410b04016903030810142c981d00780741111188403420090050540c404800075040d06041c00c000041080350700c04002e4880b070903003002001c2841c2e070662a08904601c11003642000601c80824081480b646542c0504240c81c070616140c084162190100000080105c6005601c1403512001400c2c2d490146c20040081880c00320746d00450003810704400944d07035090b911070385907980801000f0360342c4001d00a00f5004102801d0640c030740001c151004090b44d000208040926803105e83c0119200c50360703403180651050744015101280c8088000079140c080a40b500341c4401d0030b04035445025111803180c18100c1c1c00080043c00095501502a5003c280092502d076050280100c40000e603d41c3c0b500034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 283091169 1250 283089919 283089929
    0x30712110c01020703030c0803090c0307180e070f1a0702040203040303050f060a05150c21030108071e0302010804030302090a06021609020309060a020c0a060903030c0909152c01 78
    0x109401800c12162841c00c46150301d40c904550100c030082012907002103c42d480313550490403003036889d5903640143c1d1810321119403c0d82c06104191000510b040010305600003130310200c0341408900203015540396140568090a42c1c040e50014040280005004408850260982d0b0460030700415400050403608212802da004c20f8941c41042040f0700480b80c1710380d00030b808a410750181400d000108049070380b01038815100940001d002c5008020800026200b580246100c20301c407c03400300010010b800070720a208441c821203502142c071500d060640b10442c07641c3d21444280d5803440d001111001405801138051507401c0294580c181c403110203520103040346400416410380d071210244050140380d0302c1707211940e10500c2803003254000424000d4001c29040b40150300c840340c8240481c100089002c00074809841d01030554101030701600020303103000e01c0f80c03101a0038039a1000003c003681c0c280c084c0103843c0050303202d0500c0406a40c043d208124240500c0400340c108040003c3d100f155800c0e082 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 283092419 1250 283091169 283091177
    0x12050a150b09010602031603030509010e030313030e0307230609060705070302100509030705040902031204030b07090909050a12032301080c0a21020301150b130e01060e010809030712 80
    0x14500a04102100b64010840d034801076140850b6182c01801d0001e591200078101a22440410880102500f1181c0000c08410036645da908016441505101032040c04502142c0e00d00c200c5a543d10700450400129980c00901d10b10000d4081e61600c060b1043c804826030194080c006c1d0051912900042c110181c41070340203091041c258010085003030401074010007004000c010b480400d45002c1181001c55a0a44001c101c8107920301c00241004004030f8040180407000c80e00000b0300000206050007905141c82d64554180c80d1a07038002513551828000c0c2030780e80002030500000d074407040481e1101c0201e140000301c80784041291601740420b000003049030480b140050204010a10441c41403034022035507003400c0c40c94100c2c0e90f484803021900d0201c0c00e80c0515044015500c1c00e4104070720310086110401130444d01c40d88200710325000289996101100703202c0c045071216406040b2416204191520740c04640407400459200ca401000c80215002c2400804001903802e400080414010b4803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 283093525 1106 283092419 283092431
    0x80c06090133080307081305010203040f030b100302031b031002090f10030f050709150807020c040b060d02130e0f1006030b010507051213080705060412050a15 70
    0x200940c144d0100040c44410010300700010910f21400c0c103407101c0c40c60780b41c1004985c0c902890003124068400740c001407001c00d50140d03019500c10340321200d45d91207540765808072b41000c6032040ea40103101440901c00c40346d440c0600000600c1004060114180f8032040c001904600c04101100d006c0e88402d0680d9407103600c07c1c0c006449034141b9910511260800c5400108406290700c103544001c00c1c140d41c410489440b9254050103455943c0c000c002c044100000c00c0010070102e0041076100030300b0001c0e008010001e00140205a000003840005186003009e400d640260003001102003981070010801a44036040407030041d500c1910300060300001e264010303a00d600c10300c0d01c05001e901c11290030341c0e0007102050040029480710520903000980e10858195140d24a0060580c424001d001c01e1240341c0c408100914028040c0c4115070a258098564588810007107900c0e01a107500c0f21 = true := by decide +kernel

theorem cover : BRFrame.Cov 282913669 283093525 := by
  have h0 := BRFrame.cov_init 282913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 282913669 ≤ n) (h2 : n < 283093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
