-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4997
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:24:45.595641+00:00
-- url     : https://prove2.me/submissions/9259f02f-4505-47c7-99c7-201cbfa1ca29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 898561151 ≤ n < 898741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 898562401 1250 898561151 898561159
    0x14090a0201230409020f1902010c0c0204110d0906020a09090b1008061903290609061009030c150f080f0601080a0b12100501050111030409050a110309030702130614 72
    0x480c0d62404202e8580c0100d42010b401c181c400030b20740b5510401d0401034800041e0103c031147c3e44205802c4c0c02c900f6140c20300721500c04a081141d5040041c681038005842c85c200161425082030082c400c1d80c020384020440940d50190700041c120b1111b60711459a2002d444208400d00c00380301c0c010007040803280f85c007081d04100005800030454594a00713141d1010041000c454484494030780c02d042c801c0100c070784c10390480f2201c0c80b4400e50340043d14200c010b1065400611800300c580d21003091003050f9800460748020003410060100006a0041c21200548240b042461340840550b00282c040625519500c09000c0010100032611a500c02c105500c11300030f181c5000705889002c0103a01801d0b846480942c400392200f12001c9010001035280d2000204410500140e641d5500648100341c03400c0c1c0d0340c28190010413040c44404a1070300019005070701e00b6000200d4803030b401107240c0345420550700c11500340c000180000951400340c001240400e80e02000b04507061070100400303003009081c2c01c0d03a401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 898563651 1250 898562401 898562447
    0x302010b0f09150a170f06150d02041d030a080114060708040909051218090115020a02120c0415030302010509030f0a0c0f060f020d060e15191814090a0201 68
    0xf03940c8902101d40010511702d501070030000c5c4850742c2580c88912010110442d8441e090020b94803e52810003002d9641000e03049a0204500c3d03028000030b80419102810081c1105a80c03609044081000b8120303510f03280e841c0e003031781d506101741171141c0200717010001e02c100b83c14088000440c41400031102280d048980c0014100844c1c54500e06000030301124143c420404226005050784648844400420803032316020282e03210b0710200100004117007283d0041c0d000003082030040c1845a1910b00040012044a03422000d1b2000981940c8000c091140c00354440c06003081010340901840d600310b004540558140741000803486110701031900704008001c0c207865050f042c0030009040314070107900818144081c815801c0d2240181d0311020400928918103600062407034604100e0a0151040030b2031160b01040c20801c1089541c1403046006601c090b00d6000608001c00107a41511071095510126604075580c08010340c81c5030080104544d900b224030310000503a805907498040c0e40d0800b0014103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 898564901 1250 898563651 898563691
    0x506012105100209010f390204090c06020d08070804032007081b030c0a05040e0721060c02010c022a06270102071421030a0c0302010b0f09 61
    0x2404031208000030700903009070490400d04405640041503005001c3e240c40e0080c04103824100d038028400c00003e1140a141e0b10008458200400e441801d00004402c000303d13107405800007011610a1407045a018403140020050907270184070142a0111034203004400380ba000b04050702610000344024104844410b00b1880c0b030103050212401b000e0a6000c0b540382c162035a14080d0f840201d001503180300140440c03402c2d02ea02d0300080d001c40c056009003c030051107140405000c05424910511451405000c101090085440c09508280e031204221a954030080341880c008444150480c80c00b1641040c1100203440e40000320641411008071801007a01d050070507a01080480d4010540c0c0a10000740d0a0820702c0d54208802240000425610000c82008016a500e285d07034480c810240348201c0c0d51401754a005039040c2281c04950a492424441c101c00460855108a034080003084460920605159091044402c1400b0594140b0303a01c030001c7c00000c04c1298001c12740180c84181701c0e0122 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 898566151 1250 898564901 898564949
    0x315080607030c0c0b0f06090603030708120903070f030302070308060a051e061e04030b0901140a020c0102040f030305130b030114040902030a0f0503220303050405120114161101020304050601 84
    0x30884d03034004005100c2400d1400f8040da01c00419140648540544d50110b14146070202c210341040303038883c0340c041c03400d010420503203c0004001c250130518042800100040380a50b40d41152891290f40d00680e20200381c135020b4240440909082c0c0200c00001c1b080c40140c5134410144000e40300301c17140c25101804d06000031801d200b4810301880035072405400344c0b801082078000d403056038070412512030766507250144103007201c0700c102210905610341400f14004502aa005107401c0c40028000b44c80c0c2500c52042da1030030a000c2c0d000320001080054400644000d440b0004003410082102c1d503e11b514107464411180c249042c1c0521447c2c0c0d80346000e085503030802500d02016800121022507020604143d501c940224a0035024940c0c00700300c240041d0050800001030f2070745a268070703082600340814031403103041408840000351760301d100706002810303181d0a01d8424000100040412009100024441e010503c0c2c0c0c00120f0b80144280070000d9400300c1c000c0e05599240b0300a4583e040002046 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 898567401 1250 898566151 898566167
    0xf030a090204111801080a230a0e030a0e031005072309150702030d020a030219031101061707080312010b0a05160605010e0f04020121020408100c0315080607030c 71
    0x4050724001c00540928894030303050b44d40d02150401d0301da03040c041e55400c4200d820354546050200c2c0744403011610001c242002c12a098002402c600000340354102104e0300d6185030b0041d161600171503148030010100b89001c20007000070384a010f005105078209880043e05403001c2070141001c1051007c170a20750080040240e480e1007900404080026001c42010340340c2c0c0e88141c009902038040c020711707000c0c134500000f0a000300f65807560003030000c82004502d402244003002402c0b802c00c02d44403c1410408006d0040c1030103000440c10084108440003610791600c0c4680d0302440c001e40003803000501c202c2c0140942070440300071542d4140d0318454040110f907039119022030003240b80c039509100310510503580d1180c0c0c180c2c1d411807051941500c03a500d0b2404071940444000b80000d44002c1ca0600480d158070b441102445803120250801e6168074045007082d528a050081c40c5584010011280d5071500030f4071641c05811010380c1802d13040c16401511404000c1c14a014140c6070a04903007003508c19000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 898568651 1250 898567401 898567421
    0x40902060f090a1502190f0501150513060f15090506070f110109180b0109050a080a0611030103170a0203070b0a050709050303130302090910050f01060201050c0f030a090204 76
    0xc2541d03021890151061a088200102d00540b950040030030403c0300030341a10680b0800d60000d01c0d0041030011101003590305503004544144044580100059090240e80922aa10b820b01c01619040c18248100f6880e9205c2e68200942480c800b003003507001d000c0010041e9074101d40d0855419006100c10707a0072041c41e5100b45d0b04034500041100601910b2140141c07414840c92425445658110045858134518041c00c14408030010501c6211449039000d00d10201040c141810196556000100d46142d69800044203810440700360041081c580300d881c0c44c0d2008884130320b0455040d900c1e02060840d03880c495100c20100020401d41e000c0c001c0040d507e03660f502004880c628036000c8002b0000d0002038030000c0201c1c2c1e03c00004a0545004020f884d4544010321020020714910303000c00c80c6518014082864600650342000c000301c1c1280500f910070070007000c40820704d500d0031740000d003103a000074048010361206000010810501da41201d81240030118040340101c000c0c00010020241840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 898569901 1250 898568651 898568659
    0x1b0901141315020a330e1509010b01270e0a020f210a2d09050102031e011202010512180703050106050a0902040305060c0703112b1d0f040902 62
    0x1107400310056000880304840e600c07850001c030308a2008a1009030100b121220884175007000da00304924040e6660000d02185140001c507050814482c2408030100c030152100c805036511001d003c929940c120600140d4058003804a2041060080c003003880741c001801003040c0080000003159440c100c58065030920300614410035036071a40084000c1640e6503c0690340d001c400828000b6903140c0e0b0a10034142e605000c50100d00a4030809001004061480004078030700d141e8071501180401d900344051803251008812040c0c0064400a00204151050380701c420002500000d80b03005076404020398241c03000030211554251945008111044501400d1500c181b0412070700106008054000c0002c0b5501955507224180d21450035030107a1140d40005407950740309101080c450318440000700383d000c3c040d00d40418580160070815040000c0349142601c1224262440c066009072382070f00e22502e0500c3e05021240d880040c40010300f84c100b8a80d82440b07141414030a458135182d981083c0903007a4010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 898571151 1250 898569901 898569929
    0x6030703121206060519050901050403061a03010501050a0b0d090f0b090604060e0f0c1311040e10062604021201020403050105180705011706040b04020c01051b09011413 74
    0x440010503502c445401c1c280020b0500c100015654040c1d0b08132607207610019540418035802c00c034240d40c00c0e4011503034141002000c100000100761035100303581000080000c08001d04030303403a007010300303648045e00964855903c1840400042c0525411182d80e2040d0748030105102070141040da20f404880b5001400441c0c034207042004581011603280e00c202d11401c02000000b2030b400d210f84d43d9100403103040d03404d070388159402900303441c1018103038505591490001c00c0c00c0d40c8110f10700702150810307440b140002da0141c040c08100031030256804041c00d080c4c41d140b445c8500480712200c00c142c21550f400c4003c40240081015911283c0713801c4200c0742104000d554480e80c0c0e1130054020070b8200c1d00c5648050030b04038103009000004c00c00e801218016910100c9070b0068081c56902654003800e0070754800d2391207030104800d481b14009001e01c54501c200008140c504020400540700030440d098400c9101040010481d80c0c00640c141d507600c1c0082e4071a9101d0054030004540e0340c0345a000314171524505 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 898572401 1250 898571151 898571183
    0x20a0504020f0c160501020706202d010b0a030206180402030705130b0f0418020d090308040201030b0919020c0c041b0f08010e06121e07090605060c1506030703 70
    0x120000d1510040e100d088a40905401c2241c207480d0444d8010b9500607000a403041001038800e04c19081c081551428500b000e08102c4ca00170325198000c41e4804c8807030311221284010034104020009d21041940c0280000c00c44007000075091042408002d1050b03c02142242d0b80700385101d5134202003080504215a00d00b0448009002d0740c0040c0320000200080501c0807401e14010f030296840c40c2c2801c0c00c0756017001d0410407a0104504040c0b44a64181d03420702098031920918051000c0440c001e455190710ba040a000050079100a05081802a0000e80030308c025a41810503044000403408001a1641092074040c5c0c10101c645108a80c0503013080c1040c83e5800400b42c1400300340155480e42c2038064140d00c01a10090001d11075114603500030390005009042c00003420070f6507034503030060301c400075202c000f106c8025540341640b0400d41d000001c140080040380c401d400240400f180c50508100255181d01d5903990100c0c110601003000202250403501e0070441c039805158420001c84401e031807 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 898573651 1250 898572401 898572427
    0x50601090b0307081b09090f0703080d050a15090506030a0c0305030409050f041a130f060c020d02030c07030210050c1207201c0510060f03060b0a120b04020a050402 72
    0x10201c0180701e40260b0100161144000984000025028003074024248040741000881000104185d5450250311001100e6402c14020f08010354800c1004649801030000080c04546005140c0780069141c02521200406405681c8040700c01e04000480d81d03968600110307041c0303141084020a21000d0076004030800c6000f1018009542e80d4030020441581d898644503241e103400d4501601c90f0003004903c42e614000040d00c1644401400c042c05040076071a0780750904840d54550540b10709503204e48282085e81e051090040143c201c0c8000c6080c070400034440380c1c480da218840240b060500f861204c1ca091f0140050307421142450060341c100c0b40d20300c40040c8140d032102804840031021480301d0900c21b072f14182c402070490030142204c41c21841c00040140241403c8006441034031031040e070038018407094080d80d0003610000c00c02407142c82c034521700a0b0950341040f8046203d6100452705210000c0b40008019625800c08480d00064580c0e001240f03c0205541040b90040c1c00040c3c00c091950b2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 898574901 1250 898573651 898573661
    0x4180603050c0d0b0f070912120801050603010b0a1d030a05300a030507210b12060f06132a081605090f0423240d0807060905060109 58
    0x800303802503951aa0980003040903203c4542002800554418040f888000302102d180340d01101c1402e0080c040c1c0d4407021390300c10034041810122101038013068408071a07680418102d0042c1010307507030281554100343c103104e80790188401e48010490310725140f000d110881203102a1140d8040c0c10f9600c10035030b508207952264400c44ca86c01000036483d5003914030a1030011070907611f2150f019840d080c110183c0044010700400b420341c00c1005042c3c034202d1008134514400851909007041d0010740350070070109000095140d0080140f05811072000c0107032000616017865031040040700e65900c1c00001d034603807100034405e2929600822110144440341800d600c10324010016503a190000c040c0c0e40c00d404101007609071703800040041c0060108000c14103100400000d00c0c80d0040c8080341ca001c081e419101c045284079030000980c0c10340018441300540c1c8407040200f0700348401c2c1c200302d403100700c1d40410002d9002e594020300b4108002411004d20400350700540f50710b07501c082529802c3d6035401d9140c0281ca = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 898576151 1250 898574901 898574903
    0x2070b03040b0906240f011206262a03100e160b0a0c1e02060c060103060b120c0108040c081b030c0d0510020304020d0f08220311041104180603 63
    0x1108880105040310416804a105c03d00c41d01e000d4842d8801c0e00041c00703901d00110803440c3c140148086006030040321402018040c03e4000d40c075010b18907541400c188407501660950300c0a8014250200c10082455040c00c011209000c410621103009000720385481d8034602ca40070020303c3d03c0d40c2c040840b400072aa500328541e0402c04a803000391940e0041543c0e202d005a07020100c0d10080c082e0f40010603c0e820005007400d02403c01004180c960003040050780150b001c10502c3d006000140100101403040302d401f03280070b45291410300d0218000726690dd812200850502c00c0e4100020200054055444c0c0604410800d031000d4240c4074006101070510840114030900400c1d00450036400e0001d2402c06241d00200140070007801c440d40d0b14000d60010344181d8200c40e286c030103207001c2030703400c000744489910074020544d492051410040ad00e11402d203186008100c4406c00b013001c1035440c814813200403404c4030001141340e24440182c0c0c292049622130750401400c00564040c002e6140d001c2001c413 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 898577401 1250 898576151 898576153
    0x140903070b03071806080906070e010302130f1802160308150a1e051f0c0c0807060503010e1b0304240608071a0406081909050a0b1602010605030d0f02070b03040b09 72
    0x1d605c0b60310550368507100300c0b20240ca50744140b0001d500a8400c04020080c030308103040043c68006005905e400d5078126400070702ca003089020342001403c00d08a1042881d100a0408500700040c540d0035160101500601400708503024002c10042d8042014140d9451802060505803a80d503401d040c55400092514411982d03103888005206e040c00c0e080300100f80c02c50403041503241018102075856440b494010740c0c99640780380d00443d0601d4108041c8029004503110340f5201c0d03240038040581d00384020030100c2e80c1c4202c0244c0480851540c810390383c00c940e006900d1006111400d295150104401900700da00a0516000050b42100820020305503501c0d100400103c1c040c0c4641514107100300e10900c000101e030400080c08201440d0599103a000d1079a5012510242c2925002c2c0303049005d170380680d04c002c0032000380309200041003089424000140004d02c0a030b0f00c3c000000b5200c4039801030707501c1444a0760800b034100718401e10124029021003a866622403c05040240140c50704071503440d03103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 898578651 1250 898577401 898577447
    0x40902120a0e010b100c11030105181c120c030e0d0f0f020307050a030509030304170c0109140901060e0d290f1614161b050d0201140903070b0307 64
    0x8640c0c0c113010b00611484040e001c2c44107140301c0c0744102c0d882c0510540540700e44505503c0000346a500303000d840d014042d1a08a189001d001c0d80450f4104440c0e2408152410998079200c681c0d03e410000c3c10701110f180480014071050719500540203401c072001c1d0542c160140713422030520740c0d4101c024165000010741d1401007014840720706236a030703200720b0384040c1070313540b19844005c0003c1c45038000389580c44c4c019050768109581d030100c110884000c501c80a140741c024841c51541540c2c0031001c003004000100402101c40144000b1403070b0b101c0103014900800a0030b800e842c00380d403600110504610b50200000003040d505134480103600c1ca03009105d030403603c0840d000c00e100d40403000c500d0340201c090300d2010905800b0803c2c151400b4140806c2428046018080410142c00c0c01150f403516500a09440800c00c800031600120100640c00c164450000400c2040160345d002e00c014462190046585542c1d0035000002841c0c00a950f105410f1150004108400d20b0340c132a050b0a40b4404007950900703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 898579901 1250 898578651 898578671
    0x204120b010e130c0e0a0209030706211a01030c0201060b070b1902042d0e040b0702060c1602040209060705120c010e01020702091906210b0a0506031c0203040902120a 73
    0x3c080041c000b0207006124040014804803141e2110550002d12081005283c03011120219041c00c0081d40090081054031248100b4403140c2c2e900010502041d440400c074990042c45510543d00e084290749040507603a0380b1020181d4001d610000c081c00c2c00c1045603844842600d09048925000c4484e43c0c20882e0503420b800c180c2065000f42d80907202040029202022031740022107851b40701c4800c0c0c8500103420a07000500b4030440400c1c500403070150030803000301e142c0350f20082d140500c0600701e042c05d41d00810103003407070a01807030128440d41d604a0b00540c0c0c90404400254481c0a00c1001404501516500c0800030f24840001d03e04088404001c1c84002c880307440160807806001c2c8041d4101085500060761003e40300074020400400304d10000b09140c4810103481c6010384c1030500d50030101007540380001d000d88090140e600c6800ea20003880f40345081400b00382c541c621411100d40c002040950b0320250b50080c41680c0180c02100c20440d110502003011810030101580d015401924015400b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 898581151 1250 898579901 898579921
    0x70206041428050f040b18150a03060902040b2e030f0501090c0215011203111c02010203180a11090c0d0f0b04110a0903020609030a06051303080c07030c030f030204120b010e 76
    0x406400200f103540f4442403a049814003600003005042d0007038422000c994660f0390302d0240d0340614001d2f0301c001303a040164414441100d040401c03c0e40304440c0314003030381c0000c244103c202d100741c1200300e00315908241e4a03d068000c0c148020b4400c007064100800407031000c0c680e90060034000095821203550b1780404800d001118000e014404a90340321548a8010a004001c4100803000840442c1d402d4a41c4020f502c207545040005080144d400006000d6202003042c5c200c08268251005083c618040c0c0d543c8038249040515000e000380c403900e00246880d0381c0c98098400c03500c541e902c01d12100807000031880c018608002614481c0d0314110005c0750000000c03007034817800402c03500c51b0381580e415502048110b82005002c240e06100d5519204c1c000b8405010b518090f450f642c00100c0900154503014103d828000e001e80c9071a130040c0102c401096220520803441c64060508d84524090701c00e084010f4030694206480c1c8010410000c400c1082000e8024122410200b00c0c60840c2c40e00d8500b2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 898582401 1250 898581151 898581161
    0x702120a0807030b12100b090a0c08010312090f1d07140a2a0f020f090415020904090c031b06030516080a06170a060c05070206041428050f04 62
    0x420002801d150002e0312490199000b1002000f004003450301540801000d20329000031258418403807034483c241242c2500f0900c25040e0401c3d408031040c0961409000c000b4180f51052101410300406a10800c00403400b541d03602c2d002d0400c04114403080c82e21900800040401d84000e040211070040c0000c042e00d200e240500e5189011503640380c40c026032403004840450f8040001c1c1640d801c0b10551000c2422081c00800c0c404d441091905558540d900410444541c45c0440c1e078001c0701c1c800104000584402c600c0301c1c4091141c000143c8805040d4042001801501e40090408896000100500181000286083e00b11803032a44045d0f0b10b83c00100c003954030a5408a00345440000d01780380240c000c03028a41d10604101340040c0c2d5558404003005c00c400c2c08032000003903400c4810f050b0705006c0ca07405101c80014090921516180c000d50100303020348194031443c0c0c03c0c090444035034401c0d40d0302c0461512051460380840d843d405400c00020007900401e1107900d210303c009034015071141c1001d000d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 898583651 1250 898582401 898582417
    0x9090d020c040605090423030a0e01020c100e01050c012003253603030e010908031204080901020a02041d0106060c020604090c121a0a1d0a32070212 65
    0x1500c2100d40701c598460f48003d010080d42d07d040f43c160401602e9508003000a4410b500503a6a008241c0203401d002a003030820b200b038400c2c040d002d40802c05910b41c1d00040325007040503080c41c19a07070b2603800001e01c5006010f00c002d814031948892080c00c01c008101c0c80910301551069403002d82ca29034450041c82c840000d41000400b0422a107003103004c1001c480411080620070b030701031810440c2c0d030000314205c8800c10740045001c80c00c02c007072040701540d004a0b4900603106003002185018469120b06401d040d0052000301500e0001807a6071003640f081c4415104194082d00c2481020281622100780c2d4140048061a41d031a20318005040b501c42d907216080b8540281c0440e16050030042d504c405010018850760034499440440304001c6031a21545440c0c41c0380711000300084040c40c00b045982001a401348440c410941c0000707402012a50440d600100b2a01000a00065040800c8206607048800050798003585500b100100c0501d00514031800b100d074280d50b84002c00c118841820b02135420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 898584901 1250 898583651 898583659
    0x14010314090706030203070509150c011b020a02040b0a05040515100f0e060309010b03030301060c06150513050a060504020c01090512190807020307022e020d0c03180509090d020c040605 81
    0x1000c02c02903010317030300039a001541d601d00b451031b18002101040103480c8280700ca08000100083c0030b03a00301001c0c42140082c0f00e82c0c4541c051500c0c51040002d60301d05820b01c000e40300f2560342038803624a41d10154a0030040001400a0003181342184909440c51000110b05008002410b1002c0c02e0920400b600349070381e003e5440300320b10603083c1414403100340c000802d40040c540d614141101940d5040028500810359599014100410740c40d006046d102d990407810280c11410400740310907a520040c11b5501e0010150001c1d0960328042154054411648104d8010f88001070862800006404c81c500782406842103c4980c14030302840d400da031007081c1d000c00f401c0c4000092400400d10442900c2e801550f148100e82c01c1ca1030740c0c0c0015840301000c2900c41c8006010000380740c0c075400c0f4100b0000340a1805d0000e426504207042c1d0140c030400d034401c0000d04200020b2987c100b03000c0c5400408020300406005c6004a14100540580e10403a90030600301510413aa003208080c60a8043c103405d403107000d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 898586151 1250 898584901 898584913
    0x3020a02150405070f180e0a080306060d0b1302070b01080604020a05100e040c03020714070608010918060e07081009050c0907020a02030604061506090f0b130b03011401031409 77
    0x720030080114009001102c0718020a90f00040d80392100d107110300684161407a11614110504075a022030b00644111000d0b0341203200000e005c1279014081d43d5110307000340c41807641d680c0c0b40140c41004005503195a98800d1049000a600451a80c0078003a0359104640002483c0d0300ca2002070340d501c10071100250f21200c58001030100d0304208400a8603044a42080111a4600c20010b1700343d0702c2401000c0002680402c500c401d11000b05482d4491060001c041c112060410301f00030001c1c0c0741400350016072031312924544803940302d10b0110320110350003010170840300c07809030850340e00d82078a4451800c10b4843c3c3c05a4049422052280c18100b0f54000000d00380c02e41980b00340000d031407005200340c080d8014417907100b0140c0c8003440002c1c4500e1085c2400103d2107454413100080420070b80002d4100b001c00c807802d2148440340301d292019108264851600d8005200c1880320500c07080c2c004081c0c120b0003100000b080013540300d2030001c801003624184443c040d9480d10800c000c504075003099460f4061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 898587401 1250 898586151 898586173
    0x1d04110327030405120a080f07120c020120190819020f25051e150c281202010c02060a1406210a050f0f06131b1502160603020a02 57
    0x2403010705e4009511031003a00c072214906d40700d0052a401c03201c6a8030440074005501001c00501d000d000c05c0242d414148060b840c80e47c1e800003044010443e582483c40c4005075801c0f4804c96040100312800350201c0c0351a02000f02c6440c0034182a0001c2400306803280d0054814480f450006c40c81e10f00d08003690000300780114008506000d80c1030001c42001003030180b42e00100c0c041d2110810507044c0100721160004d5035040c003080c005000090170b100403080c0b40522000c0841000031510100519500c1421950f072855150503940b0103604100007080c0e001910001e02a10b0340641001d8071503113268003620744030b565644019081c2c50180200f400307458a840300040c120b240c142d2002e01d10700404401c0c21403006980d800285440d010540681d030540c00040d02040d074040c00c00c1010308061840000d80450f0900b0080b0864401c01d00100506212000350b903514a003191030304000042c4040101615a00040710010751681c00025030055030807000080030070120700038001c580305413504d94000c0610b0043c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 898588651 1250 898587401 898587409
    0x71a21061c03090b0c010c232208031c060e190213080102040801060e130c06050a020a0f0303090b1b030606090a05060a080612010c0507031d04110327030405 69
    0x30401e02107080c000d450b00040307035141c0d000c0301800b005110880005042d20800388090146107224487c5554482a071901504d44255103082c0c407100c151050f84481e00070004200e210010f83d258010900340e1001140b1021808040300703822840850001042040743e0316120031020b0028100d5030099058100d0780030500c085040c0e4010140d40401c00b048445180e00d82d9010360983e88548e010041681d10f17841c043c041d9039454402d694011090307a64810542240340e840304e4000c0f4052149034240000850303004010b5000780090002558002c200460810b00c0d40f801500508034850207131691685030000859900c0c1c00000b101051003203002c06404c540c0c9100422825500810405d600028002070009440c2c9031b2030043c1c034110080e43c6407051a46045018425115102e8444007080d84c103004440b1607164010085981607505403410303940d4801c01c00076403159070400d4115a40c12501c0c08003180582c90420019600515001c080d0144a000320300b90508c007552040e52100c900d1300204003c00c11441c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 898589901 1250 898588651 898588699
    0x90c1d0c07061b02061905061003020c0304091515080f040b1306090521191b020315070e01020309030c210d0c0c0e091e071a2106 57
    0x1c8a00004942050710400e01031124030010300d203e015900c207909020030404041d525007401e640701c4c8410082d5207072401c0010600e240c20301c1c000d0281940022481c079200300a1048a0252000d08014400c0404282040da980c10462080c01909031a00d040040f5541c811a4128040e0302014080c80c07250f2900c0e10b4071440ca407009002c20410130f69150b405030000d0b00034021160f20500410240c1107109050621445408a00e400401240e5041008412211104549008000b210325180304400700c140d890000e0001c100c00e002e541481180a02c00040e408011340912a021913a40c00b001c2c80000c0c1d005a9483c082c0e01e2034242d042d001510b4004160034035814000752220441d01103558280a000c80b2400c00e000c00140c00d00241501c25075074240102d94a09c0401807100c01d04010031454445550758684640c4428034203c003445041205250804201c0900607005540c0c0000342074040240c5407081c0c0e4460707018041740010140208450802e116481b600c1504040d00022481e07410180d0f20b20041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 898591151 1250 898589901 898589903
    0x305030610120e1b010203040609060e04060b04150332060d0b040b181f0b030c10020325020109030b0a060906060905180106020309010f030b13090c1d0c07 68
    0xc2103402210ba8480a0194142000804025040b402070072219402c101e840028118199402008100010355200000400f00c600c00c1c6070a1030050071020015024000c95880405c9005000c40d020071442c404001b0415120743c152402c10400400301c1c0e400041903003001c0300045c40c3d00065900780d1480700010542d40d220310000d00c3c0c900d40c2103032a520340049010680307003503e00100c64020840725603c1840307450f54442800d0024042d1700115014004054800841c408905444100c050201d8508001a4040b40305c01003000c40144502c2200940c1c3c0e40018003164542e0b5044220760b000c0e40e0b00180300080d0ba5406039928621207046883c0d2814000014041c240b016640304c90024070304a142c80780030060a0f4550b601c620081c9040100b109030030041503492030041503400100704141e00042180d441304002e00307020078881701d00141580200209000241c000c81e105802c056441d405a220a8044d13118004151a40b5114190404c0c111030001d030440118069001040359101c041001d41002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 898592401 1250 898591151 898591157
    0x201050c041206062d14100e011e0806040f02090312070804080a0b0703050f070207060f0210020c0f0d170609130f0b2d0402040903022a0f0d0305030610 67
    0x441e80c0e01c100d5015038044051610906980c1c80f880142c004c3c0c2e071a1703410010f104d60501c041d8400780c1c0c00c00080b51100b00d0181807051110f0840d00f0001a4011241c480e02c0d1111000c619400302c0064501030141c00701114040d11035494507050700702c020554401e85242c040f0150052a44807100c2c1694402948810390a40e03550405200000d58540100107100310903108420346000c03800c055030302a090390005840d1800c0188580708010409038002800401ca4840d4907060800b84901c0c0c500342e0400141142482d80b090002034449801640080c00800d0940e10104403a58038403c840101d441c421200e1042c50701c031503544045402c82c9011203810f500807146118070304031420140d4600072031003011031301241c015a0281c1084014001c0599a801820030840b5030400c406200307a40c0d1140076802000203100365a102c04000030725108000030b0300c440341c0c0741a00b00008805412171180c40610103070814880c038094203412925051602620f107100e41c0c95120281161500340400101801c4a0303034031020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 898593651 1250 898592401 898592411
    0x200d140d0e0d0e010f09030203060a0902060d0603061d012d1b1808010203010b0d090c050a03080318011506050d090209011d010f1d04050a170a0f0201050c041206 71
    0x3480c141400b030018440d100382c036003030002009180090001a0000c01341400d100c07500b002000584c4001c01c4107a8004111032001404103d54400940e050103100c9520a0f01c46c43d2101c0841004550781c055505000404d400c48180720504d0342842c240d03001c640201100d4842c08043c09502421044c06e6094100b110702d0110703156407010101c0c04140d0320000054000740040d2100b002032151300c00d02d4406420300000a510350760404100fa00c142c424000144985903030343c0c6111040c096000350307500c0913000082185030050b650341014103041d0402e444000a08170150300a850f0000c0c148907509003003030f12514104145251050039249030704030b020135000d11a00d4001c0300005a54030f0b148540603000b08010003030001110080d03400e403003805030003840000e08e8044041c0580e498601040903483c04c04046e1000725610b5107451400d00011240091086502000f01120440b810001d0800e02c940c0e95602400c091070010203d09a034820740d02d50280080402051041c183d00c94080c250281c0104c8000c58 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 898594901 1250 898593651 898593671
    0xf0a060c03140a0509011112030c07030507200102120c0706260c03010f080a0f0602090a0b040b1c090c03060e0708030301080f0105160512060d0b07200d140d 69
    0x515522143d107290005000044151142da08a20b0314810082c41800401c4142150a800c0502d03200181a01e10722250100301c40b001c06124000b02c9007150391000614020001c0a801050640e04010040d0f016005c6c200e01d94034244082400c1e140c1183c00800108152807604c081a200003601c81c41e489900c50900f03d80c1099803100890f240d014401d1160520b54a62604003442c003041c040da04200200d80002e1401c0c00413411310b40148142c203030880401644c0c2ca102d80009158440306078801c4190f410045400034080ca00c04014240402c4510090380d08070020091400445414060060071106241401d001007001644044400c013062030032200300341c0c0c40d54605840c5800991003480705038002c10040e0010359007030180350303004542529140800c0d440c0800c060501d0140403e071500c0442c216001902e15642c04815480254105110036502d040c200c4000309407821007901403024801503015100c1403403000030350f0032034140d1641e540c24901c102d0750480005903108042d100242c40e220201d180d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 898596151 1250 898594901 898594937
    0x100e1308031003030f050705250305070303030212013816050a05070e0610030c14030406020c06220803060a0b0f071a0103030c0803062115060f0a060c03 67
    0x141c051400b20001010880c650316004020407040340c3d90200300001486044000f40c40014030321804c0c0364501174240030184c10a0744481c00d200c540d20190461160a10010a05402d0b5009140904020085034816a226155251040c68a803c0191084241c20000c0200d0504101c4003e503403403041d480500e0044110109851454000c41c180c0316500400380c0c16041040030010500200781c024140c5040e45491000940740f12401d960342414103482c2c28549068030f2003071300c140b9001040c500403d134981c109402c10744000d400c020ba401e0064419070b00820000f0388540c0c848105614851009101d640c0e40f591810301503000608244d0308901c43c14004104048003401600c1001800c0c3d291548950940c00c0046450032850f00e5482001960300042c80426800082e40700865000404151340ba10342c800407404c3e224600600d1400300000d0405408800008196074402204034000d06c030460706c0360801c1207610309101b1209644640520f900300180c41c0228090400d10f1b0007802c01c94007486030048e04c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 898597401 1250 898596151 898596157
    0x2090a03060518010501062c0121140a0207060f060f0b0708040e040308092a04020a120606090602010b0108133203070308013215210f100e1308 63
    0x500201e907428011a62014618028880c1b540c0040c0005004001050010b4071f020400ac40d22400c01040c8410701400d000f154006840f80c0001d611407900500e03081c2d01003802500860003c50300340b41029401011480540120001ea03010134104d11000f41c42c051000e06c5640c0300507012201c0000603c0001030410741400403a2203107000c0d0b2241641c41c54114000d03402c1c03851a059402229007030511250118249501510404030151001a0703101d142e00025120310350404142c43c46d45003801e0003c551194402030354021106590000c1c824544014015903180c20103e42106160f400004508086040c0b03c003528040301044022140f0340440394002842e078114820b003203000f5880054000c0401d5400200c00d0300615203041d0b810305451503042c4e68455900d800880f9021070706660307075083c4650f4070041ca554040c8d659854081d6124560036004100040725000e42d15101813410000e110320000c1c07401c2910401030030b484a0303556400c0098400040c440039003440c0d0401c1c1103816440c001400340d401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 898598651 1250 898597401 898597409
    0x70b2104061515090b0702040608190308160e0d290f0709031119120f05120a091a12180f16091a0402071a0a02090a03060518010501 58
    0x20031055511071041c09510160790043e400b82455010268607070794004074840685071018003d03a960502800000c01510701a00060040c0c0100c070500c41324040120ba8002801b0300c292103580b000c0c1d46400c100c800c00d080885132031300454910035504049140140b80603140b00c0c450581300b61a1540c0090b8401c040303603004942c0d4203074074010701400704a43c0800305403540b0070b005142185c4101d046a4984040645160f8041e000f80001c10200c04c41c0380616042c8030107054800551501604075003050742d640e0031603880075103650140d0305882040003800c10407500c2000e403e468030000c46140c5010b4424a495582d40c214440100f80b182c1000d002481d9009401a0071024091000c60300c0e1101160a00d00404403415440e400034409092080d1110b07549012038a9250001410710480d44003107000e02c5410803180e62103840002c100d0200b10703007543c0310707840e0f002e4681c3c10b0100c65581c8809181240315030781103e540503082d11820000180c040e000700d64004060500654511096891503007500c4085e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 898599901 1250 898598651 898598663
    0x213060e0705041406040609091a031b2e0804050c0301020a0302070308070806011d0406080a050f0609060603210c010f050105031203061011030f0301090c0e010c05070b2104 76
    0xf400c1084d03510b400112104c00400b21540341c41d00b80b13405030143c103940841c4660290180c0322070402d451f004119400e50301c5e0b04409003c1d140541000140002001c2001d12898440c40301841941c1c9400304007a860800d450003004008502d100605060b42d416100810441745482480f008400c00d44003030000c0c046c0c00b681d40c4c40c05621441503103400361001c980200000c0800400394200b00041ea4402c5000c00b00355001c01c6460181000c82012030302a04040c0c02150052146000300410040000340340344210034034000b074403250744070304405907200d01c1d003552066812741c0124030160000c3d4102c2020070600607080d80d003501d42450a5150313402e5441030b80c00d60050b03a035100010001070609003c81584242104202d40c40c514102000410b100d100e12445020018150110511480c080089414001c4c044040585968bd140c1d80f49000e000308072291070005a0300c0508107180e50080c0b0030a0301080d13000014148145c100f01e414141c541090500b0300070b00c4071081d180c0d403021982541c0b16003c1c40c041c0b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 898601151 1250 898599901 898599907
    0x110f03180d1202071d1009153506010e070f110f0a050106090b0d0f031808070302010e01050c0c010809100204031406060114070803060d0803010909140601060c0213060e0705 76
    0x10700500685401c50301c0d001c110a81904204160f03804d9030a50040d02c0024000158503c146240084010680e820060412a8001c09c4c1001c1c1c1d009400041400c41d007120850b205850010324407502e411b000c5c4941c01000340100003198030f060007401e003c4040c80903440d20f560381181b01030066140104900e108050794000004030401e2080038042c860162034100d00a008640110002c25041c0f86081360161110383e441080e002058070890143c03032844803071003071910510344800c00d02c2d4441945100c12800301e600421409100c1d409642522509000c40e405018400c0210006440440d0f00074400c00140c010050b60b10f43d402c5192000c2c0c400765000702c458a820303a0601694900c0c04c0b202800040c103010000303884030420300260301160086079006120a440ba01d403180802c000015003003005044207408400895400f0565202c90030b800d001d203101c0f1080c24200388100e519400c084c081ea070005660306c0541c001609010313000020100b812100010504c2d65050044c1c43e442c1c041e500500062000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 898602401 1250 898601151 898601159
    0x1704030b06040605010e0f041d240a0b010c06020901230909061f110a0203072c06310c09080f031c18140d110f03180d120207 55
    0x10b845184013401c02820040c4000b11904001605241d00c1c03603072244159103803510344a80350076000780403c070700a660084520103121245040340c0ca500141a10f11203411110000d80002d0450040b5550014181c42d102004001512444003940c004000c46042c00403c5406107940040f020607041000d441030080c81d241d1064208101608201038407261266100801c070102840180000880c01d68140c1414614803840800340e038140300241c5030280d41402224000164040090180768440300000c80000c409115000d14122001042c3e81c015082209a400c490310701b50f404d1450034140d074101c0c10400c150701240e141034040c0d6001400010010704040700800960100b0001d00300320b43c0508000c0c40c01d06070b0907038020310072039a801080c48581e910360061409202031a85024591500300c99140102c080d81540166911001c0c141200042d600400c901d61403000071502d07007601006000a103181c03072016040784045044502000780c2c00b610950314040090444542c4142019140d00038004192078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 898603651 1250 898602401 898602409
    0x1e01020c0d0b0a0f1a0d0507150801030606120f020f01030603080708130515070f1e0c081204060c06020d1119030515030a0b040305041a0310090e0304060302071704030b06 75
    0x4000844211242803018039207415010030351840d43c0d10001c1d46c8444002005080c010b10b003412340d502074040754585181451483c0d500ca06154143d90048034184401542c0d0000850300c800180e0011f00118080d1b40b10100500d407400100c02043d03014500030030781d240c5070b840f580d00035441035000f10f07002d00c3c002502c0d40c411008041014014001103a000e0000354051264081c58441d0b0800240040c180000f020208611603804000c041c0c40c0720004081c000c400c2c42c010000368450b02603119140305892401c401090044102c60036031b28142c0d120540c240c4070340e4907640a900113141c82482d0689900309110060880380191000490100705012400c0070001c02a007142c0b0080c0020041c11103078401654140c400081000c4055806080f800d030302d6a0743d04040301c0c03501558110416900c2d0b00080000710281080c00386008480810301081081ea584110324100ca90400400c01e0907007042c00100a00d074000c1d40a013207400d0284500340c00c0b44110b5825401c0e56841034008451000c450420b200711810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 898604901 1250 898603651 898603661
    0x2604150e0f0d1e03031e150e16110c060a080106270501050a1205090c0f09151009080703060c11060c040b071505010e041403091e01020c0d0b0a 63
    0x1c41900ca8a40001e0a51140220758403031880e0300c002c140c2200d0442c1c00309440390348400b0311500c4081c08040c08a2005440034040c01184440b00c0c05125425808507401d5000001a0302070034000c00d4200403007606403410344000c2005000c142c564041c0e6040741421385c56000c010114003849a607130f0055581802c1c1d0140c12003103001c0e0300220381c1d030b00c2070b400e6800403e07120910001e40300c09003029500d4044c2c020088952030348020f5907892190a0100b4070000303d0001034900340a40301106d080c2501c044150030300c0885070702100c0595080070600c024051500741400b58900016642c41d1420b195a12420032600c0d0003440d5004544a690b50036443c0c00d0aa4003082c184080c40b03464000e04180c0c108a959404103010b9070181d0300380ea4000046000c108144250000c030340d40e4901c1014866980d41d8408561850411101a1440600100c800504000200854420100013810030340040f4901c5060f0001800006030541544a68150b075100e5690340228000c15a200d21001d00440c13400c00e03981b4003a15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 898606151 1250 898604901 898604929
    0x30212030103030504090915110309010c1d040b131b0311070f0b0a020c071502120304030903110d05161401020d021011070c08010213122604150e 64
    0x1803005200003030f0b1000858080700c0c1ca5650208039840c0034104031028420f000d04c0104e10318640b4500d44080c003600740103984901c40c04002000240305201c8181c9a400284404244503c900e4240f17044e0781c5000d81c44408101030113013202c48002c403008910800c861209030301d0008ad5494030301310100c0940c1070141d0300c40307203170030b82e0086041900e1f80c1d40b4a40d00f070040c22401001042108000303031020320250b050b00c03c2c00314050700720750500b079480750080c4e01004d0042d034042c018015a2105489081c2d1310003224001c0341d05946030050685035440e106103c1b40c40c0c091950f031102c110325040020030403c00401e10910400b0f961146203d140c004041d69003c0155119410b5400c40c5140403126500482c500286000903500801c940e0307600c800740782983c030415400a0405502410201e05210158003a0251b800303070b5107102001035140c1041c441c01d0002c6220043c001084003980341c03a4010a18003103500280c036801680c1c00c4c00d4a03070035108004030980c070583e8001506c0d0794402c015442e001c034442d0410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 898607401 1250 898606151 898606183
    0xb1e0c040302060a08070516151a03071a1c0e150114120309030303040f03030f0204260c030d050a021c02120a0203130f05090601110303190902030303010e040302 71
    0x200c0e1031a8042842400380215610070b100c220800960078a0041080303501c1b40c011404040d5480d05645011115800710781070752403ea5181410f403404000091200409150008005090540c50001d445403c0001c005a0103400c0d903060180b0202203a080e1492584103170042e50120350340308409401490304102841c00d4042c031b0080c2004000b441c111522100d40804103403054681d00c0301e4041c405d40345100302c090315605440000100002c1c0652a407403103818520031341c1c051041280f02007a041c1a030089008840540000c01d008000301d1000031510884070f840b02c401e40d985403030401c00082c10004080c100d580401d00c00580d159210743e041c40016070062803046008004201c2200095951100c150250184000020f9000300d4078000c10645000355100d0254050b015161403100e44601341c5c40c0710750790141c880c001c08a11b5a6000d1000b0f2040c0c40610310017541103640c0c8403000f0840000c500c2c802c1e50789907503881c0810050703241030000b10301904036800c10160360b051520b802444d00d5005071b081400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 898608651 1250 898607401 898607407
    0x510030f020d2603180c0634050601050a1203050a0503040f02030a0b1b18010f11030310060f0302120601200102041203171b03150607120306050a0b04090213030b1e0c 73
    0x56480c4030a0301c1c2d58007064408c3c0d10900d144800040340e556400300c20100708046005030300d000c100001404034107841040d40e003a50055500c042c1941c100301c800d10300401080d02840000c00c0c1a11800145500c540903164118a4542ca600820b040040f03000e01035640050050400000d4000ca040c048030081c811140c01c4e02c0e01132880d00d944192030b01170304c0d4981007043c0003101c0100301d403140420b40d00c0c00f00580256543d90805da00e80d03840744285803145030007260080b10342440c80b40c000c2c404c0d6461000c00302d03800021a41d0740d07001128100361018010010b403c42c1d905204540c503091001d04050440541e03030b07061860140c24060106019070104040f45405a4104a22540c0752030b100540e00908503400d90312070711584002c0c071401c02031881c1290000306c041444414030800e802c101c2c01604258a040182c41d48030780030b00020040c1401100007542c800c00c810404180d41394001e06543c0c03c407015070f00c40709849035030b00308181e00c0070364490383c0c08408819005a4181130481e22900001c00c1d00c3d8142c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 898609901 1250 898608651 898608673
    0x906042106180b1605071509020a0b0703170403050c030a09050a05060412060209040f0504080a030609020307050702151608070b0703020418150e0109020a030510030f020d260318 78
    0x90140104603003544010907050380e040d05c0c0030f941600c0e0345c1a0300c51000c0c9000f000c0c094605008041855003a403140d014044009240d030072000880e000150503503683c06003e4001880440445000303841181000f0b010000940c00c0881800500302e030103050b5840c0401a468801086504007083d00b1140c0301348000c00003040134510910340c101201340c0c008005600c849900c40001e0003019048020a0624204800c200420160100408880d191900c04100241d01c407209c01c81207003c12510301d40403420404c205405482c09000381031001c42d2510400d4034001d60000003001000480310200d0b09240e010035820100f01124003020703401758a0749000c5007040e103026200042041c1c1a420f0041c6d04d5554100e001091040c55490806085041e01102e49035a503680401c0095000030340c42e000082c074000105801d40440d402c0302045a8110031041620021a000c10842c5002400304417001d02ca0a10942c001526100171200150f1070034080a40303a01d426048490002902070142c3c0c01c982060690700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 898611151 1250 898609901 898609913
    0x2404082104080712060e0106180c020a030806010c052103070906030504080313050a020918010e06010e181e01060f050102060402090a02030a1e2a05030a02090604210618 74
    0x7408850a004c4560700b0000e46081c841d00030b00701c65400b19815424100d0210303d4507200300300317207c40c0d903d040d074104070020007048102e031104c10000004000408000200e40290b22914900c0ea01c18007540580759181549417650320407404590300c0114200002c0100500e49411a85500003015103040900035443c1a544d00340c410312000701488011510035240e0014804108240103000e507000d09240001d0800141d18001e10b11903181070f10213903081c034418001244e000720345103041b900e141051405603140c4002c54842c4c9a0f82c2e1012032064810700a540b0000d4072100c03a50b16a00c0481800055114101040460014896009117065602041c00d110060322001c184079480441c0c01d400580325281e000607a0003070514102c9110500c0c8441c1080c03403107000b2580c403d1698056441900c03209040c2081d848480c01c0010910002194091000031012881d03a0028800800c2c002d1403145800d888260000405001d00c08505030400c4421003401084141d22a218000340c500d113100305998101d0b9105 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 898612401 1250 898611151 898611163
    0x31c050a081009020703031d0c0d080c190c081005090a17091008090105060913060504030216090c11030c030f070203010902150c010506010c080306240408210408 71
    0x9810440ca000005200901c0b001c608009400a8501555650410304004014141166100103880c10301c802c01c1c450745800081d005007a0001610300c0c900c61280c0d4458031030a4001003c501410b0140c2d691701035140c0b5820320b00c1c0c40c0c5c1c203101d4042c0c0c0c50340c2800c1c050080d02e40140d500d9440092454801400144c0c64002122020140e1000d1226851102801440035a01520300084c0c0c005680aa00e0400160002e06070782c803951500d0020091640c0310000c21846000c10740b69906c00840c9805408082800d1b5001300e0f40c000d00034011103039502e07080302c00303620b010f17105901001c50705a65205440425a0050740c05098203060b900a40c24803805181c03140c2c69102d2545540d011a0b00003c03801d045403400e400c44103105030018801b42c8007030382c41c0c1107100c841d5000214055881d4640300000390598080d000610328290402d81e01800c40c1c0c2d5900500c8031042802241812580300d07100299400c00a0b0001030000e404200b024040114402c41e0071000418100303d03c01d8018010711045c07011043c00220 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 898613651 1250 898612401 898612417
    0x3050705090a170708030c1e030a0e0d06140c0a08060405090717010e0303070c0c080d140f070f06020904140408031f09060816090e0a021e13050402031c05 68
    0x90b0500024851410f41c0780024640c0885034500010070340c80c10707103a07001c15540c48800c40f45003015400540d407000b10b616441850504004105107a0808005041c41c0d41c00f00e0541d44110130000300001440600c0c1140003044400c080b000d0b50010717500d11800e50009a441d00054140e409000c9800d0000750240ca4203003a0103805446582080b00da0510340d401d40040d020440e1080a81e0751364203121000400010646030b00f50342c041039440b0001001180062030f02d44c05143d41e1364012001c540b101c2c501e244c5602c00015141c68501c1800350742d01081f103900c41c0e80300b10362043c140140c1e51684a82400f05840016001c0d20242107460100030106201ca000c4070380c01a852001d0240b01d40344805006d00311038844c0c100e00621490444080381031240062000034440030321102e103402c5e5a44850800944104240da10704a0300165160340040c1004810b0048610b0700340c102d8900078401b0004101410100c60342c011a042d203460520055040611103003800f0200c110b41850303810075540c030207050f0b8815185 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 898614901 1250 898613651 898613669
    0x2120414130504112b12031b090b070c080102030f0405061506030c0901031808040306050105040203042006040512100f1b0c08040308030f060306010f140f0f0301051603050705090a 79
    0x3484c16003031789034403075600c000c05101d50756001549207401c043c181070114001010105e0b241c00ca0503608411091540030034030340075a503041041e6040400b021541d402644048403420010030b4045030b590700a0001c1d61040c20400008100c1d49043c5c20110324128026044e410b08034103540c0b10795090f07181c00045951010b088407015942d20799000040b0001c003d50802441c075040c000c1081c004108407003008000b1a805100103102c0e0b641c0b00c4082004030702c1305403801452001001380d0010003141d000c4140f48000780080505080540d150b0110308940c40d20b45100c440b940184101310348181c41ca21032503030050b10380c100401c502c04080c000ca00d1401c21920424061126001c104020881b150003250041c40c0d2027034880d505d81c2003413030a92a00d40780c16141c2d58483d005d107000104440070800003140444910403669846400c1d41c01c2070143c01c0102c542c0356504003075442e00d20000340d00c00b40540e5006a4084031040400c520102004046030000340c903c4041101c20072218100380d413180a0241a512446 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 898616151 1250 898614901 898614919
    0xc010f170c0412050f06240915090c0d0e070506030105060c030f070803010314120d02130306151508010e01090b01121a150301081207030212041413050411 68
    0xe4901d040307000300c0d80190b4481400e40040420060701043ca18076428018044a20395200c84e200903903444010903002d1103142d80300c981000030380f17400c0e4403698109081d91003041580008001180c4c07030b08402c6403820040100054045a0003a140c89071040402c44003010341040c40c104400075200d0311061150300c0c40741c0c60201e01c00d8035402c000d000b2690078032040300c0170307680e500014900040d0b10303042440260740900d81503924001140c0d0207d03910300c0e02d21548850500d40071003400414025003050b55107c000c440d00311130210018030a80f1a00c05441d940c8640c1150a919102c05840c03404581002c590420684c20010454000c8038560709040d0f487d00d0320f011501c1820180100c801030f6180445401080c100300c3c5107041c0804e04022801001c0094038140c2e5448102e001d00050380c4801c1c42101c140d0ba0064400034003141d0048081c204040c030905c141d038010f010311071010a840d0450340007800d01c2c1049610746105490305031542501001404018030152802d0340700c502032060741010307440c01403020b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 898617401 1250 898616151 898616161
    0x806010302044a060f07080a14040b0f01062303040611120105030c0627060f040906060806010e090438090c030a0b0711010f020406020f0c010f17 64
    0x4030324007407249444a8800c000d83c04030f036400404210561850072043c189101242070300703c1400f2480900c0340c4915180d86804d91550101240c003a07000408003024241d40301141520102c58101040c001d07401503c40100701e01702410500c0c0d410344181e120405102901c81c0700905945c94600314114120b044d003510f40c403996907040883c080c1107200030f202f442c6500058004440c405901c80d42c0e040e80c40a07000c451025000005000003071207103108400c7c00d20b05601c034000d034125105480c292101c80283c5101c0c240f151084208542e41c00c580c000880d220780342c41c4103000316503002160a60106003403808a650311251804030b4500b640250003c0c00f801200c523428013200407982005011400002c50203241c0061440742135030101001c2d10034a81c0d5000d00990700c03041d49800550348030510b0b0021880b06e41074680403003d66008200d03600a141c03a54039201210380c01141440940000c0000c1d0b0050255420249085810840340d80300d8141807040c284c000840300d0b0b600002e0280c0d5a041542190900c0d214 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 898618651 1250 898617401 898617431
    0xf0303020d180b16030e0306100504020706140f091902010906080a0b10020304030203010617120d1116030810060203030a09020409050d020d081311010311090904140d0207080601030204 81
    0x503e421012076142c1c001074072001000240d082851141c0640d603101b102e04019020940c030b8000c1610440b501e1070000700f05201c0b81c6003a60081403590311a01c0002040a2243d50b400010401250602249240c19080107082d9130180022841c045403031500400561032035002070a101658041c60040000b4440000d4605450383d0001000d507100800407080c070026400001d50b00c2e40207020490095081400c001400c3c1803030312000b001d40da043c20140610040c94aa00141b6800c03040b09811b505031901d2402c14025a502d00030420031101c0010710340040c14500300640040c401400f06030030708510f9003040248035400b00560b500958141c40104190038940005006801d1500380900580601941c06210580000c3c0c016003550040e1a52442a604c4a1000c40414030241c8003801600b00c2242d4109150721982c000030001420f2044a41400000008079101080484080350a00402e514040d5410350801001401c01c3e65440281380603818401c40640b102010b22000340150b440c0d490040e04801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 898619901 1250 898618651 898618697
    0x903022b06020d09021230091903060f1b0f0e22020d020301060e0a03080a08061810033c0305040b1216050403020f010c0203030d06030b09070f0303020d 67
    0xb80040c1b03e40b041c101e02401450716181408004800320300961801f12054141d094525900c904140d5060309022611003800050381e04844400c0203034514000c0440091401d00c03c0041208038044005002c3c0d01841c1c4c00d04004800d6070208040c0541810510005540140da901d13040a0903120305501c8202d0303501a031000d010882511100c90300129100d800b410075035001c1c5048038141c1e568202c41d071320080140081001540800f8007007003810007180c1c0c0580e02400c90140c018801034101000024000308070790740b0f0340c8140e0301d0086054070f044041003407101c02144241c3d082003211a02c0d41c28240394880c1300d5400c0a1443e0340c0030f850b007032400400a04d8007038800d90380203100c404c2c000f550740c3d140d02100c0c406030007040300c516060800b40350040001c2e40c4100e046c1e8055a5010f8007880d00900302000641c0d80e10a0400101da26200800c00f0036040089406424029031180b4000621420301c8095507040c030925070001922055849802c1010039800030350403122041d2401c040d44024900326480d00081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 898621151 1250 898619901 898619903
    0xb180f040906050402041503022107030c121205032a0c0f0607020f150a02090a090f0902280b1c060608090f0c130f0b100903022b06020d09 61
    0x91074154104240704403600301d107204034400c0380c0c03c2100749412030003501d9a03046400007941054a1381000c00b402d02003410200001c2e45a4422540b07195602d41d292440d12500d0380100284403c001e81070410412901c6a50761204028105113085142c5074800b000d03c00461703500f8418240303015601c0c680d0070031002d04840c800c110880907540d0b485650990b0a54880042d00c0e850010f01c02d10440200c6400c000c900400c000e00115951143d0381c6034a800c0401a410060905522610302c0e14001100010703441030600d00684958042114201401000715107441c450100c1000d0000c0c03103000a8071000d804200050701c240c80e5030390b5180d40404d0040540d042c41500201034407032405802140e010340026030184501403c204032407920f001d10440d40d483d11050b040003900a2401d61055400d46d005800c0b4900101c000440011214030010001d02003441d404072090100f42800d40601c194208030f600c5107641240b80c11005102c201120011030005414000074151940c00f00781c4c0104c42c510b5801c900700c1c40e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 898622401 1250 898621151 898621159
    0x60a12050901060501140304120e010e0409140d0203310315050a0b120741010905030d0503150a08010f141602031e0c030c070914010b180f 61
    0x2030300d014a41d0a000f49014041d6a02081000c42132205090790a01241e02c01ca0740080304c0c90b10842c0d2140d0954070850b2400066061140c3c2a626000e1921303180f2500500500501003006a510050701c02424045030340e00100840d0401c0102e681c42001180218103c201510255540e02c2002c940140f2035286580004000813040c100d0303545000740e01c1e00b107a0300581c4064000c200c60301035001017294042c0c10328030240d419041034404000c0c0030030380600005074040b50300b1425012807140b404190140b28455004400c80c0b5100310001081d64404002c00181000383c00506004000c120050158040141030401813001d03c0c1e00d5550707075140c0d541d44100502e01d2000900c221451817081c00054030500e0361050705c8040301e4000a2500c4907412000c0e0510945070065440d001080805800502c11000d91150641d01001510a05801040100810110003003e4941d883c2068086400c2d40e50701c0040c2c0e5945074000c40180704961030b202c119101045280c25124045038000080346e680c069030b036002a48 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 898623651 1250 898622401 898622411
    0x41203150618091406090a0f020a090f09020f1602190b18040c0903080304082b1a0a0506090a08060106031d010c1413030803010303030f0f050114060a12 67
    0x162904071054145044180840140c2c10380c0303480c0710a040f5100b403c064582000d0600104a080c200080d6503504080c0e051170200b5541000310b0840180c0e4002a24400002c5c10040c04215401d066204903000c1d200300c03403041d40303450b1230f5240300b5485000700d1202c80010002034280e24110342d00c5148020448034811b0901107403c2c0d98100c064110f40003100f40f001e0f0260401c0e01100149400d208034060080741e6114660b08500310b481c2c5680f1600010800c0f01c1c207440802090104025048124100c0d11400b81d07a920b107080114011020303620a8101240c0941c4007500e1442d0035980c04030a4001d0310410b4903020781b03901c03909000441c0c0307101680c072001e900d0080b48008a682071340354210003000aa00c0031a407031003264600c807160880d015a20b0500014100356509051108520010702c0041d14054108019586a8640100580c070aa0046012030354807403035150380d0284c50151308600480c01c0310402c2070b0b40c50548844a001c0d54080014819400000c030250242e0086504444031380030480c007042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 898624901 1250 898623651 898623659
    0x70f0e100f030b030f2e02180316080604110102151504110f160c080f010f0f050417030705042103080903070309050906040b040504031e020304080604120315 69
    0x101102010908000081c10041c460305241000903514140d210340000604c40501024800c0c000401c2c0040b020043c14110203440c10382800a0000d440c880d08082c24801508e20444201441e12121240c4990164140030080100341d03004076281d54041d4008603c001ea021480c00101e080810f942c02c1411500d0b090410f1103400b02da9002c074813200c0842135a0422119402c03088544c00340c0210384071000d160400f0044400d0481c0080c9880c044644038000104516413105009410701280c0303040d540300d5079502e41d860301c14481c0c503004000b86200015000c00042c05d00d621948000c0c5d068400c81b220310080000852009403007402150300a10901a00c481e85000041c4c44030811810501e00794001894140450405200407048900c416415201e100700e0138a405e042c004494401485650b100340d44111441064170b43d4001d980c401da10994a500400480222101c43d80004240c0d0170110751040c0704c00d0103020f100081c4150002e400070490146d101c032804044011386508803400801c41c0109000003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 898626151 1250 898624901 898624907
    0x109061d04050a0906021b061e1b0c0a060c120606081807080a1b0905070c0f0f020d0b1801060602032208070b19020a120c060f060828020108070f0e10 66
    0x1c0780754401c1810b4820781c1d1154803010714524004821020f49c070041b41f011440722543c40408061480509441904021031010b07842c0c144112140c00f5030781d45840790743c00710219500420141c0d070741c0700c8000c3c104900e0b420b01c0c1004201050040c0b035103207450340060354003a40c0b11003001441c0040441c04101c0b5031000b13080c5000c04507805164201c0d0f02209171004d000c6040701103802082d10409440c0c1c0d410045c20b426407103c03820703a11048400c0d01c401c00c0308801000981c0b030b2441d440f00e000340103c09406107802d001c003c0200015558150350b545900d00314060000d658084121210540c004401300040602404101d515071542d5000183d1440b5001c0d00244520600e0003506412600c1d8030301040c09484244140e1311104014001040c041d05141e50301c0b0420300405000c0c2001c0e010350b50000381918004101c0c02102c1c030b03e40200c400783c2c1c480c59100000320a0b01c1e0915500001c083d40014440c081d070350020b044140060074450502040030070504455104a01000c0d200c0c00007060742582100c000005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 898627401 1250 898626151 898626187
    0x150702190e0a09060b0d021f030f02030c1804110d0207170408010b09012903180a0305090310111e0d0c0528021b03010e0a110109061d04050a090602 65
    0x2204c505091041d02559840c00c055043c0350650042c2180415400803030507421112a141c04074018140d544c0b4040003900b80720720145202342d81c40130350155624080300d0307580341000020048603c01d0341041000c9208011101c265007405000c0030015880d105c0c41e140c00d11404003005101e02c5d4250001c05c0004c0c80fa81d05400400c62084240d070350003410f0340c07181041e8640b414201d01c000000801502c8225001c0c695600030750b40304808400d0404800c0001c1003103800d004000109400054000c03641610515003400840704271112018104008015442008802d0250341c9a02c040000400e00b8501c40500034822207015031100340040040d41007801c40608140c002d6402000e9950101c3c00b503210b02d80e900d1050040fa40255001030040c0c0d20301c04110f10448070700c01c0507140c055480d05e0140300302c04030802000c1c90507407040c81a91340340030209000520510440d4010b800704120004001d00c8c10400c5c0001c0e4040c08004d480102d420342d01c40c41d10f10050103102c240103040e00e20000303103022a50150494 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 898628651 1250 898627401 898627403
    0x20301050f0a0e040f0c150c060c020304081e03040806071205070c050a1209080d09170607050403061116061406010f021b150423150702190e0a09 64
    0x88110385607a4148402c448003070140000708021440030401043d90500c0b1220481d1191142809541d100c030311800300c0304480c40e030480210300414114070411486e07000b4004e080e2403602c0111706013860f0401442d43e4500c004d0b41d00b12641000c0c148102c02c0030b010300484000d005454100e0300741e42007404c00200100041c90902d80c0240c0f8190220391060701c68007100030015044002041014482c1c0c40d500c6201c1d50480d40720b001c0c1f143d00d00c07001950200a000c007540e9a40140c0fa0000d296280c41016580e0313468405154049810030f0042001e02070700941614207032074010800203100c40409041c01d0080c8a19a6940e44c3d041074460800304010894003e28000900103a004405440d0900151440c1240c42204030141c0c0104031441e240f000386900300131081c103004005800340340d0300d0001d0800399489500820481c00318050b46484072031401c039804140702029030f48012041c0f0403240c1c030352450003400c00081c0300b202d80f1610102502500a1070340041d000c48005980c40e81400a0712400500c59210 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 898629901 1250 898628651 898628659
    0xf0408030c0f120d020d060e070203070c050a03030f0f090504020711031015120c03060f230103020d060507031b090914100b03070c0b0106020a0b0c0315011202040e0a02030105 77
    0x380c070790344110049096038840f041c582c24036003004003200c0100040e400110b0b43c011440d6071654000350a10746a1212801981d040d00510350b14040c90600401c010307001c1d04250f001c0d01d43d0360003c0001a60091120200302c060f03150041c1c412101142c02c950700d80141d48460f44c014000300da52818002e62124501c820003085040350780143c103002d60fa2080e0707018298840e40081948030100203600d007541c14411914807401d031108480da200d5031003004413015600b000f010180e451100490548140211040203200980c0a80081d031459001842540c20417000070013054807440400c40c5180603030803510818000c1e03640ca41d82188040002800b0031001d100e103082450602060003501c448407410103000e0b9580b04034180046045c0080448298006050741c020040740303400786d8000c25040803180340680321a43c00ba1020380000d04290904200182655604146c100b080c4418060310310301e8691400030a003003200040c404421407000a0040307034401d95195a00b582000a441d034940d00550507920129 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 898631151 1250 898629901 898629913
    0x10501030c0e030a021201061206050108010b03030304050613020d020d060c120603201c060209031c021c11010606020616030e0604080f09040e0102070b07030b100806060f0408030c 79
    0x92000c42e218402c40e85801e4040e044a0842c02c05401e007010101604031581d0000f040702c690745c100003010209285020b8070815551300050051003028040e41d020710508400035030641c100380d103415803603110280903008558903540d00d90046480d03031010f506440b900240004840010390418601a1640d0110800010b8540014012010162180c4401d9a8000d0807020010005418228581a60391801d0398803402c0201410f81c080c09920300c1c500010320820b400341e10365054506141c5080c01d604c03d651140340d81990f002110a1f80001c00c807032001a001495102840040c40c10703982c808180c1c004910035401c140c1c0c0428032540009485011b040030042000300000500303021011500c074140c425a654110b0b20200e000309a00d0005084201c010030724180c540f00b030010004048174826446000e03540d4000c1000401d01590001041d03110f9042d05080c400341080c00c0c001a224025034040f4003d2049240105485840f124180c85065402d913441d070385da070742c1c844108035030365009110031160a00c40e01d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 898632401 1250 898631151 898631171
    0x1f030c060e1219080c030409061d130201050d0f0906020d060e0c040b0712210501140904080a031109040204030f0210090f1502011803030b0f060304150905070f0b0301050103 76
    0x72100b15440d01e5451410340681240d41d14440d91740410400c004900c82800046215002c41c4201c43c01808400700b100030881040008140040d4001d100c0640442c080c0d40460160344c10408603440400c0001001540381d01800c400e030010500340d4006055148080340c0640c44680c0740d44244103075010007034210300f1070782c034007000f0151449580a02c0c4041c1c04207002c000006110b07200088000d00c1c51b0300b411980c25003100d01900400602021509905440d03c00400003c0d035543d103840c4c0c0c0c1450a03070303955a080c81c050315500518812101380030100340d507406024615901240984541c01f0340100150741c1c8030383e2414118100c000588050748148035050011107124000c50320744044903c4401c2445210b80340c0401500c0d001100c1b83c0c01000d554075a51040460385100c00116950b511079100051104050030030300ca0702940d0b410f0054040c94080040c000881c40c0341100307280da0304c046880440c05000e42d01e08641403580540c00b82c00004007940c03006c00c980c050b50011754182d440030f81e0100010688 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 898633651 1250 898632401 898632403
    0x1e071a0406150b18091b1303120309050705010e0d020910090506090907150e1206070f050a0c2307090902090c210601140d061809020303031f030c060e12 67
    0x2218140503408100113400062400d003128a2a44410741c60783e0f0f46a107942e00e0210301400e50001400d400715a0f40c65106004200f000c5590255103800b505e0304022013030341d84e0340780d681e0b91466004090500c80035403a8803400742da5140044008541c044e050040500707285020b040340e428a8050400454200300006000d420000791444c03044210740010f084442c64001810403034040048101c2c02c011400c400c0d900b140c1c42c2c0032200324040b28010700404462808400040440e1113401c101410007004101c15070500384c0c0030490a10341c0d07412050840818908011420700e904030b0f480d110307115020320000014004180d0348000000750080e200030095a0b18903107a020745200b0b040c1d8400802000c191088414982810f03007942c4581c041c1055440010442c1c8008107540002503012102511600180304401c0701f0106200c2c058080e407020b20400d4142d500080e240d010080c5800560703007020a00c019641c80240480340110313004040e801c01161036600007000d8141c800c10080c06000242540c040c4448 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 898634901 1250 898633651 898633657
    0x1d010309030815011202030c0d0605150a080c1303030804030207050901030c060e030f031602010207050d24180803040317040503041401050705010510150201021e071a0406150b 77
    0x64940c0c2c0c0d00030542c0d5000810101d1101c0c1c001c0b80b6040094a030b07481901d01040d4030065018900c0b1071036003503c0e90801840b000079030b11181c100e180a17003410001000c0812172141550000c0903542048502541d80702c030311085602440e14074054007100c0c01b03000010b058101c20018011400f9600755607182d91038100740070301c400b404e1200510705048820300b082504c1c03158445180301c80c0028140e83c50f42c4003144903d840c40d042444441300081a00b94110210741e010010346000300030540784903c924500d034032000280c505007000381314104200e001040b10f203142c1d1340c080761081d6400301890820761003038106661160400c480440102e000c50300880e003000d03070306c240543c401d5900c4401180341c00e00700700700c40f0310040c40b614aa40c10b00c0018415070000500c2802404d21420b00703001400542440c0941a4882e1080710340d2400541e4410080c14800c140005017002c48030881c002c8895860006240c00c1045a641883d40c0014200c604180010055982c0100d1781030088110400078071074a132015100e4a01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 898636151 1250 898634901 898634903
    0x52b0305070f030c0e0904110f010c02030c010c0507030b10060927020a030b060d09030e0613120f0b0a0606351308031609270509010612031d010309 65
    0x60031565082e54010b11a80240424140c28900384408000d8800458540070064070110f400d0b14464543c4105810894141c0b40d10210910700b5142070748454000c82d44401c2c1d029a039904101e051400d00c42401002c0020800455004a0030340d001e103448401280040c035640602000201c4e003c40008034644409a800103501c000048540f20481a9601350000d6001c500001d080c5a10b500801d6025034941001e0710010814240c0412016602e14000f1715141e01e505175248030302c6040c81503010a82190600d941654014907808148654030300380072405a1040d01c000f010842c0b824108009d803491030b0803040448019460399070b004000c02c0105041000c00c000d03030240008240c0d80d0400045070403c0365580000c0e244964504a040f1521890810ba008036101c10f150640c001b00d4001c001d80c001007110003401445003108071040d01030708600b1611600c0300e00c104400d40f00e10205440c05001c2d03205400800f580480041003040c2460f0183c0100481d9141005401070800b541350154003034028902c0302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 898637401 1250 898636151 898636157
    0x190305190c03320c070f0f08070e0c27090702120a0302070f050d090e100f05040507032a080117120715060b0909060d03020316020d052b030507 63
    0x40c002a6010007076495080006112000320620071002e00910b100101101325940b800303462404d081681c00d2488a0850f400041c61030a01c0d0404c100e2000301048220590388503010001c035070740321000c020b0403074029124007100c810301c610700000300840300c03c035280c0003064296a2090583d640b004140d032074800d007034410180031030100000d5401c3d91080d8000d1801e5481051040c6518506031141c52810007007600d400040340e6002c006001141c449081182d011506450683c006420050148010b900d03610441c0c2c0201d450f400441c50040c000c0d08490705861402c900d1145e20701c0e6072140000801c03420381c0502c0210b81c00c0302c00444c40441d48150501890102d000400380c02c88501c0940a09900c407180640ea60341d030703007001c4e1542e004041c003519004180030950217480e00348132800c100383c070030010300040d200300e10017415900041d4000c02034030003103c008010000070003100d0000c500d00d8080040300900c00c0c0a41c070221098101c103444079a5450884256117021460041801e40448000782e40720004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 898638651 1250 898637401 898637417
    0x914010b032d03040609061209020d030c111806010e1c03050f04170102041a0304020310020f21090f150a0903110109200402040612090203190305190c03 67
    0x7411140d40e00d2035082c1514440041d203003000764403949082d5003041d007051000801782d0750100725841c4e020301006160302e0398140c00c1180303000d00d500140c030041030f0b60780080070311444030035031000e008141090303010590340500082d0444401005141c460780c803c551403408181c039032000700300d02e061800e46c076040015032540554008100b61000d0340c0503048466a0801c0100030400412040410352544001a2608002503200c40c01c01c1081050180180032150134401e040c01080301507500000d21010f002c400c034900580d1080b106c280c0104601c5003084990080e100c400a8020407001c4144c01071041100d40260340711a8030300d000c032a032a20804280c1c200c01200344c5001c140e8004c010307070201c038005200e41410000c03081c0c810003d60951f8890b040a031640700800510741122051500c0c0710f81e00307010854046203000e04180d0060400305101511242c3d090b99004540c017103460800a070742d0011200d01ca401943d019610703006141e9480344a081801416940d042d8009600070039601910b80c2d415212095 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 898639901 1250 898638651 898638673
    0x623100302180604110c0604211209060204090e0c04110319050a0f1a040617030f1b1603060c020606011706360907052b02090a0914010b03 61
    0x100340401421041d801a50750300f808008440f500d00a03d4400382d24801384c003c901d058103022002d85201e44030401c14030289070727441d08004c0d8440940c4101c404945000546060b43d800e048009010340d03044520b01c0392925115514070b84c40018501c031a00005c4405100b014241460520340d4001174401e80c0b0051082c08200140c12420303000280d10221a032000140d490000903030b103069400d8466028243e5000c50355130411810075010300c030058211035030400d100d24012030307a00d5030760301c5042c11864a210300410803100d406826044041c400c4685021a02c105419030041c4810940070300c01112703410318000c0c0080d42c05002080091140c44161030380c8520340000444401c00d000300412603030780010400c00d541054041c499950658220512044090b00d04030a4203000460000d44070784210361100d82c0401c0980e0743c0981500e81d0b0400c0507103420012001c2516a00c000c40744210003076012001c1e500304071100c01a40e00c0005543d00804030304c1d11012441128034200ca000d0042d05806070041c504880c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 898641151 1250 898639901 898639939
    0x12020f0c030102121b090316050f1f2312090d030b0603010315020c060703020901091d130512030103061a060a081b0d090b0f0c0f071e0623100302 64
    0x82a000c1414032100d15004070900043d003070062442d090035a07030308014403c0c40349e401c0029401803240c000707030b41c580300c0c3c01184000052054900c004120401040f80d42d103030100201a05601111410180000e4580826822007404028201d510440304d20034401c02102070740c401d0040c80f0b2006405070002c2c1c80c59003903881c0d45095a00001c940e1a402c3e40070000f0010f550020080988150000d076001030301c503c4840001805481194017075499150071740c0e202080300c15440c1559800428040c6c501c1c3c0f12210301d03d060340c10655550303d0710481c07100200002042c404190801c2c0305140180782c403d165a5515420041c0c1070003032411000005505000288140700c0000303200240900814595041c0014403001e40300f40c40d085a0215150b030071550900000000503000d031070304100140131280c24603001480300351550095003c0684030000b00b1102d0300001c44100102c14402380c01c0345c0c05000e0086500f586400c0e03030741c1a40c2555164201032000944000c10007518106507540103080c0481e040700c1074002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 898642401 1250 898641151 898641181
    0x307062711210327040c050d09030c0c030c0303030507110c01031a030a0609060f0623011808030a11070f1419030c080f0a0f03031812020f0c03010212 66
    0x10002c0824203450304902c074603007000a40105040c0e280b510b1004030248420b0500f100842d012103016a04181c2c89000942e0001e054500c0b190702c0702d4000410000c41e050461301c45124030f0020f0300c0011155070100500544102c0b183c10703039010ba101444a5198040d0480310118855010310b042d0300f0036801c2448940c880e030020340c04407044140e050380c00344038400068141241ca500849030a40e440c1c80708010845140504500002c800400300811850b041d07520300750490004090030301407608210301c981c0383e000e02003844050952503a5100d910751100315440c0d4a522865814021982d9080c007502241000100042910481c8016080203480c0034424811092a40303e85540480070034644403001418101200095003c2e80200f1503103072401000d64142304032414400c002e6000000507401251840b814036590503410b25001895040f070b080011461354088400408590025005a000c2c0382e00060030003030041041c2c181c0780b1150420041600301d2240c0c0c4604c19a0045c0e960008114074000503203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 898643651 1250 898642401 898642429
    0x8070e09060f01180b0c07050609012a061b021b0a0501050f16081207020c060f09030a05011103071709060a0b032401030314070c091802030307062711 66
    0x105214040d01c18418990044c1a500f00e4001070310007081a502041d13003005503c0042070255401807410803490300003000300a08025011002c6004120808017600000f58030030b1058101104100c145200b60244032441c01c1481c150005204900d80c0302a503600007a000345941e80018001c001d540e140c200191002c2d00b1000407000e031050203004021000c014002d154009074802d0b60380d43e80e6141540c4401e001c10101609420455000100c0307844291290000c1703c00b443d08906200d901c170403007140042d140414100c2c00824a5081002e00190500040065070242c041c50700d418103982007448441c5070036a002c50380c24802d5400391020130312100c0698010f10300b030080a410f42d4030318900340c140d207044c060381038100c45c3c1e0002c221001003082c10b0348006405512944038080c03910700790781500e890006040794003400b10050360718004405032070b1000400130b440a6004d42940c1d110741540c100b01d00241416880300b6003031221005941c0018000d0310004030125400310042d0a040c440343c05100d117260900b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 898644901 1250 898643651 898643657
    0xa06080a020405210609060f01050d0804051801150c030c0b0604110301030803070806010516030e0a1205070f090c05041a040905090c03100b06090f06070c03050d08070e09060f01 78
    0x3202085544550068041012140c4548400f900b4404c01c59480c00c0c00003044000d07240c0100c1d041c00190300541516504441d01210000d1b131b624540c2c1007641081c803c561040760302012030348440519103c41d01c1d94504803010318016441080e8840f5050743c0740e028a110040c0000e004e040c841000031171032060303180c200c03102800024408403541c070f0444050b4004e130002e4464000c00b1040007140c0f54440c0c4516400134007860520b0502d611801000402898001c0003400e0040c401c49419003500c940310040000e0088a42d13011802506051503502c681503401001e03290594001c0114a404042c0511180d240350390380c03414034040c41c28404104004190ba6a110b00840030000055604a03501403140200d40300c201078940d1800d440c042500e080c042c1c40d80c050520b17007001b800070215905c1c80150349201d001511001c08071806d600014a142c403814a004107c424040004030502030002000c000210040e01c030104075440344c41c01515402c15114800f90701c004001c00145260800300d4041c1c24920040c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 898646151 1250 898644901 898644907
    0x7031d190f08070b18070b091017100f08030f03010e07020c03060f091504080409020a020f0307030302121b0d0f0b0901062303013602040b040e0a0b0a06080a02 70
    0x1e0303981402d50380204400e030b031035032180e1041c06000341c01c995910b40c981d1607030001032004524088501c0e080303000d54012148a41d5146140400c21406100c5083d02016007510b10011490003507246012034078140600421048041c0c03002c654410004229080300d1070701d140b4281582c2c80c003d0306451800c070040046045000342540100b80d6102040320b00c0c021680144820f01514010f480c0c280b50603008207041004030b62010501000c21911000c9905032411100b0241e5a00f20004040e8a4074104820980a6100c00503082c1d0074554941c0c040c1000c100d518007098250b8695081d06190303086280311410040384104550000020fa0b0340c00f4901040344d6003808143d03520044006940300744240c0c8010049680404501092441d8002d2035811900c14030001c2c0c19941444c559541004086019a030313000c10700c441d01c1c00c07100341c074108001c00510005000e540d0b95883e80180c0c003540c0c00070b20480540100d0100403c1042e00140281196018040c1210030034501c6c00408035420758005c0c00c8410065820 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 898647401 1250 898646151 898646153
    0x10e06041503050d0825080f060103060b0c0d030b0a081209040603140708011118040c0203121e0a020a02030706090c080304121b08190305040b03010e07031d190f 71
    0x42c060440d0703030852505e0750031083c5000440c220103000c003401004141c245100d00001c41542101038180c22a81b041c3d08038086540d81c02c0140c000306080d4205840702d5001240190000a0006165540c0c4c00652b40034031010b0000c41c107002c0c1c044800d01400400d40c0021240000c1a003440000d08030a450042000c1000b55480d110204080d100800095280e0010201842204001d007c0d04040030006c4ca07806280030501001c1c010700c080356444d424800c07511400702a000e14420410307105c08c0440c0080542c1c490401040b03602201500d1011185100d040703c00090f442d003114130a6551048254014619205c41541c400c0300030000f2000440f0005d40000d4080360340102000604090448511138801003207513810000c14280b0b000000242403402c84005100c100004149040000c148108101c4048050314050741d17203014031741280ca42c0800100002072403010142c03030700f80110042e07203003000783d000c20104842d80a201841c20003416801016811034031001c80300c1507100701e80148245003825000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 898648651 1250 898647401 898647403
    0x503130902090a05030622111011010e060f04140a060c020c0922080315130b010e0a0609210b07090314060402010906030f0b030706081b03010e0604150305 68
    0x19084038814a40c0450101c4150400c0541e800c09000300314010700052800304400901134420390601c42801229526000c00c12a28600c0310b914400028141044c021500e03200914401494070a8002d9608203450300d45014404600140a0810355a4840c6c4a0317480381c440701528035943c03901e80c0581c494171800d00c001c00c81030312860500c14640c1d405052185611420040011800740c81a40900034900515200b07605400384030382070540c0aa80291669142d4560440b030124100940341c001c1d40e404101d0001c4562a0302801200c1000d03200c02401200180501070b89032072a001d01c0c00800d601460912620803944481596000011403040c145210350b42c48a0118200381d41c0307080032481414082c0100882d444071843d1180034040217002600d003e0700020102000da111342000d26988240706152015950000301d61079801608030b03101d0030f07034881004152000c01c07680300840c08021211078081c003101c442224103e600c0713000794440589542040000400c8102c08114a188140c0380000001d80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 898649901 1250 898648651 898648687
    0xc0703050d0b1908032706182202030f090319080934150804080315031608010c020309010c14160608040c050405130b09010b2215050904030302070503 66
    0x10700f5401713941c0356031402861386484c40b181000360050000e18000e030a0982c8450050720300c05507010250301c44d104400b1010600585150581d182140401c7c500030390034a03c540c00a60040804041600c030382e94a0b0303c036003600c0c0d0060700b01c03074081e4000403020707401c0c50b0b40300c3da11440c0c0080800c0c09546010602c0040d0108080c5440a450383c1c0c11049030800d81117843c81145d202c01004c0c0100d10502a126002c00106803510040008043c98004030101e264800d0b03000c84810582e07409002c460000d200400c091f08810b280380b08903a510760030070001d41d401501c0401500c84071034041c1c42d03401600b22179550318412503001c055104603a01c50481e01446821681c1d407004c00130710440c1ca9009030b40c01d140c1000084c00c10302d900020b008500f041c041c400003070141858183c1483d0007010407401074681c1c172072590160440e03c4031154402500032140c03100c40c0306000c40010800030340e041040a01013240c800c0e00101c00741c0c440c10340d11040000000c0e020034025001040250b104001303407490040c5050010603420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 898651151 1250 898649901 898649909
    0x60e010f0212041106030f010e090c0a350c0d0501090204090f050601080d27050307270504080405061b060103030f0201050702120a0e01050403061a090c0703050d0b19 73
    0xb150001848144900c00c04000c09032a81501c01510350318000301c14205901c810310482488141c03a400203440a402481100000400207000b4541280d883c070b2099002d04082a0344200300c2c03500d4100d010311070220b0071124aa03480100107040080209000c000303114881080c290760079500c034030601c40182d07118891000c2c598400c2010200c0e030360513818101d14043c4160403d8121307912019080c0310454220030314010042d81c1c1c10b20a01032441c2800080105d107819030002c8e03010300c5205c40c04160300ea50b510b015202d0b01d140410340c8008158894044060710400e48010382018400c0000f4059400d00d440201184103c030004441c41c8002c10f416103203003800c00d030301c29000034801406d120311155080c00741c2904071540d48020301c00d0058000300b9401500c0b8210034102031005183c0c100100381d01a80940f001581c01c00401c0100d8254422008840701c001d1500a10513007280300040d10404203c2c05861011390181e542604060407141600001c0680f1010103a101540c0022031604c4190184444050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 898652401 1250 898651151 898651177
    0x302191d240f030403090b0c150c0702040603060b0415030c0e0612030c1e010c09050f1924020f07030803060619110c1005071217040c0f050a050904060e010f02 70
    0x2a150174100204910782c076800102c241c0804003c01031444100281e0103111120584003440591a644660240c40c0301d603090003904242044c1c4c5c00001d00c001540034101c8901d06a9083c840e07101040702c002440113090000030145240582c00303100c1a0050442d51790304c600003810794441c3e800c00d03140c858a90b8000d01c20104c5550f010b40340d2105240c01c092001c04a0494500088c0890040f00c43d02800d024118094035004401039204083c05a0b05c641c03007024000c40d00d4400416441d2101020307a0707107400b5012480000b0880d03006103240144000f40c0340e0400307440301d0007401584d41181c2d90301c0d045a00103800705510007000d120b0b110721a034030000240780c8808603844514402d242e050120741010504004107100c1e123460f5941041c2c0e5500881140d844c2507201a031410450450803003030f24003502c044180c0c0003601e00b27441000104040d50030400305882840b00103a031815500d03000c11041d90706500403141c028050801080000d81a50060301c8002d000c2070010075410300040b400400c0f1307003000100b0030071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 898653651 1250 898652401 898652407
    0xf0c03160501021305010801030b07030b01020c040e24041a0406110315040e0102190e030a0c0323060c0409090303110307090e0c031e04030309080301060302191d240f 73
    0x1240044c030f441c80004080030700307080b0304640c0345840e100c0051030020311701130a058580650088aa10034842e1001c5d03440001d2041000102d544c070380320340c2c8003041e40b20021004540c4002e2040000a622901d210ba0f500c143c1c001c40543c40c2005008607200c02520032103a01da1135175210710302008241c01942c416401d0040c20000b028a00082106440411a46071341c3c2d640304122501c07001c8960f0001c000484081d05114800c401d038500880d1034100b40b003402500b107045101000c010001b07203121081e035481000104130301103102690007945a600035201c1507440076041208000b0320b20950010000745000b410001049101038621951540c81140c0f003d0010781c1c01d907028480d8102c2d003001e40d508100a5040c03a800c52800030000a07440c040081200746a080b042c00050825200b40c21281555603c101015100d507541d0501601039001f461414640d82c02c005c404102c0b040c031601138a440d03180e98105a40fa095030351010702c00c030300d0440a551480c90861049010071039034074800601000510900e1036903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 898654901 1250 898653651 898653667
    0x6150603061c0609031d1801050d020f1522080715120507050d0e07030b04081b030a030b180601080109021308010510050123030606030a0603020d050c040513020102030f0c0316050102 80
    0x2400e0500116140c1300300c422039803112111603440b10188c1900d2041d07030b5201c118840380c0000750302c041d040c2d024150322946000000c003800000384060f0030414010300c105e404005025545501c10303141d90007081c01d1540182003c00c040c600180304441450741c1e83c24400402c00c41040c0c01419075500b250030300d000c1000010424825007941c4a40442c0a110070041c00da102e0965480203c181c00c00362000d4000d240128122400c09000302c100c03032110a48108595640150b04006400380080460b8607105040c2030350b844006054032550070b482004141d507400c4c10382c0c1c01c0c61707031001c0250400318104101c003914201c00700d80c40c28244145401809141055048507203800b00060031959001c6410f4008080c000c0505800c01381e680a8981004048407200e48039920440c0341802041241d001035482844200b2003c103100713010030701e2200c0a206580501c025640c0c039110110f24004010028010782c4200091440c403041e00c8041c04108100d1401c4d40d140502d04082210b211030080b45c01c0d40c55035170002d601c074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 898656151 1250 898654901 898654937
    0x121103070f020a050102030a0e040b030c060a08070315050120010b0a08160807051c1b3f0305030907080a031d092e030606080d0206150603061c060903 66
    0x3d0001d0400b480298038000740c5000003800c2d05003a038205e40c0541e4480520140641e014070043d842450090049030700c1d1039001c1d81c010080901500c2410120f403804a850b035403082001152002e682d01078580b9004c80b8417825039041805d000320030b509565580c448000e101e0341d03182010b01c4010301d0303114010040c5c0c0c0d92501e00012012a1944407140d207601c4904108129101c901245041c2e01403508580044a80b504280078603586040000e03000a5000d2404950103a24030019045100144100071107054604d030340c1e50035448841600d1203a40d40c001101c2e000244100f00a540c0001c145081d100c929030780c1e1100f5803420700d01007012008a5903500601ca03072100e00c0d07817130030190140031a51103500d410b208015010107100c1040c0c4845c42c40340203854a42c051a1100c0c114001c42d4030601c1040306c42c2e079405403e500c6040c007140c1207005009900118203a9002030440c0071042d54000c0040303203180c50308010000341c05602590348041c4080b1200d0480070030402e03c03521411600903181c4840040246c0700034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 898657401 1250 898656151 898656169
    0xd1110091d150603040507030501060b0711030d0813020301140106020102070b0f190f0b130c0f03050f0604090314160218091209010e0d0c030302010513050a121103070f02 75
    0x15074114040c0c0d404014400344000045580c500301620b41c43ea580c0ca0301d040140c2819000d41014100c0d40c00c0c25000200002e80c0e200a0540314004c54642e90103000000405883e141da090742000001c80c83c40c04240c001809101c0300c01034620007800014502000041007000c810264040000b50350302007010b00500c4801e580e01c0307901001300c80c4040090300d0404201d0f090704008105014480da5500703407a4040b144150310495401d04000d05403400b81087e400c0d00c0c0041c156801d031450025440a60240d1081e00034002d40b8003503942145560030aa0b54041404020072035100d09400b0040a4080c1008080b40305004000f06c500c5188164500130203801407010294035840c04ca500c1040000401560311008140034000060014540e565404c0020040321142801c41c1c50315848800080b071002041104841c0c001264400c0d00240115034407030800001305005014060b2254201d1560000000c074002034a044550860a20070a1a0070284c1e00310701d5500811822500400c83c201010103500c0c0140031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 898658651 1250 898657401 898657439
    0x17010c0e061c180605010b070819090806100314150604090203070b03010f090c050a0503060d0c0f320a03121211280210110c06240307140d111009 64
    0x3030320b10b05050360b6a00e042d244507100d00150000890401080058070904001c0c0c0249038210883785103041100b24401d024030180704c1242c10380841d46044400e481d0109031504005203240011426959000900000e480042c204036410b01540f1004078924a9400196010b00026007000c03a95038200762151007140c800b0140c020603c80b05108100d440b5078090200d9603c01000d4442d1540c0e01c034140340030510559240c002003a42c041e48130300480d080c80e400104007409100b01a0058846150058407200440e90000c820b030040c1045a003407010846c40803000c11001c1403442e1501440000c0c29049085950602040011702000649480440d650701416805d0401100305000b0300b80c11b80307202943c0c40b41c41d050901c107419140c48034a5484a6042c0584094080440a071100d901d0b000603020300844d2103901c918040300c405240300d0541d080c00660f400949101c9840b00e4103041d000030130400c44081040049941010403500c000340d41c3c50300b00c1040c0c1c06085c1c9440fa2400301d81881515205549041c0e2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 898659901 1250 898658651 898658669
    0xc1312030219080313020d02031f061e062d0903060c09050f130f1a090c03070c031407061d011113030b090307050a0c17010c0e061c18060501 62
    0x61004040f64044003140d4005a030300c042c03005050f40c14030108414006100000e07500d409a058001081c1010241c00600340062940401209850348ac42c10b02e180100311019503110702104040c06010b01526440580742c4240415010308c5450500e5248104000200900000c6c040d402c200704101031401600020800e0703080441856041c00f000c5a21200d0705024a48070355410044200030b0310065000c0404640c0c3d0740814884500c03454080e1105111440005014000d52400188016405c100784c80c080c06c1c441c1da95503601344664804070344d681400c406001c854a410800d200008a440c401c2948004c102411641c5000311030200c40e084420201d90710314211020009810071408010b0800103803580b2244520150700c50b64415850f41c020131074010158841c0740c41c11014850785180010841d9109600701070800c0300960818265543c041c018070108a05404580315417138002c0c0581815943c040ca00e0000846400b01c42c401d540c68800301c450b040000c08002428020680101400b40400c6c207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 898661151 1250 898659901 898659943
    0x12060622171b1c08070b0f0c04060e01050a030b030604050106090b061e0c12040b0403110d03020a0f170d0204090c032003060a15050c0f070614030c13120302 69
    0x1d140050100c03103141a5220360f0904656022249070074061040703041d00903141580303400b480d01c1c0448040d082601c0c43c504400c030030780c000b403103d0484a0480b0195001070fa1814030440d042030041d69550441c411a40616884400407140c03600d0800131180700d10300540020408502e801e48980880341888105402081e003007000310031082e421007007540210b01036400640e613020050040b070304110001c0a82c0c0413a81c00014009411114070001c2c1080d03a0042c00310104860784d2000f0050300d084001001000750700300d07120160100e80a400f403205001e000e18034a14a09810040100641d4880c0586800c2c0903808281407118840b188a07602d18941a418200200c5859201d400d011803000000c00d06800000000201c885d250040300c14024075014100c1d440324400500041d005400075150031005208689030404200e00006441080303d9107900d540c0c031003030749280c01081035900051450070b100108001c0640c0c511003048680005101302c066444480e845407030003e0414155809002c0d80f20004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 898662401 1250 898661151 898661173
    0x50909031b061006120b060c03070606050f010e061c020c0a1a0601020307120905060d02071b1a0a03020c0f0c1003050720160305031c0509031206062217 67
    0x24014420658084e42418681c00100202d03041c054012544181e400000c0881c07844040d0100101a040c032600c5048144240c5889400388101d030350000751180d00041d0300144403551070408a0041c0000c0b2110540030b01c18107190b0300c01500341d92040340c0d4801580c0c0f085920030180400f50030340402c941e2803036800c80202e08007440002d40d45d018100000d401036004040018642e40543c000c28000c05014001c1e54551540d070502c0300080d006223400340e4440300d03921160384014403846013550a503028082140c100a6840e21841075580050074440c007031507402c21800034406030130414050700744840c80080103d103854034123001e04040c0303482440b0145810102841201604a00703840101c5260f60b030132aa8896850095a140a801919041010074400c0c008803d001c40400240346805a0301c07000701110340d020000c0d1003210070480d00c0c4102c54109004104644174003420081c2c2054004260340c0c189001201e01c5480070400040c0080804030360041000902090812011446011700240c1b83c01c2d025 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 898663651 1250 898662401 898662421
    0x60609090b0a0b071103070e0420010e0109060e030c090a06031218271401051f02061b1b0102030901151d04020103020c031b07050a0810090c050909031b06 68
    0x384007802417010850140058803134408000303207001031075200105a1107041c036050540f512240400102603001c8081c2c04c444443d400790120010400041e9a80c100041c0b50001c111a10003034100203076494022401710140c283d0300c0011060084000100018072a07103540380840080d42d0007810300003803184841c0388200702c1c100145a50212031b0544190001e900103c0c009054003010fa0741e810045600d0038002ca609006120140c506940341a207521311030011610032040860640100100144e002000250b5405e8010104140001100106500740080200045200c60305204100d000c6c0c0e50101c2000007680090003590152646443c4030340c0c1a5090801c982501039085a0302c004260300a40441c0c1164429070407030300034408407000c0e241c4403884201100300318034000c40088070a108096001c241c03450301d2481801224640002010102800000c00c0301410b9480402d5400c68404d520000b420384030f411175648559040f001841d9200b664600200da0441c0c04c64481000358011010005d03001c0d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 898664901 1250 898663651 898663657
    0x703050c0405060321030a020928060e06040603020f0403140f210304120c08220b131802040305010203010b030a0e0c10110c030a0c050108090c0a210501060609090b0a0b 74
    0xd1100c5c0350550769030314078a9035406882900e40752a00402581105000c1440d00000d040005440c09070000841c0e54a100417104c20001020856003c0400c000400040b4041c2e401400d010741d07020490381c24079540f501d41c481150801d038404916504000c6400f000710b4014881d000c2c610042c03035641d07084500c0040643c6424000100010141d455108901607181d01800c5c0d01004d10b80c0c050300d01c2d551924200d682002c0e007010910394900800e84100c021810403030902c265015036030500f2900503024941486480341e4801110503946540d402c22010012800a0000754003804600b042030356603003882030808003200c0e5690001c049035040b0014464080d0740712800b5a4070350003280744c40360208881e46401e604001c445424181d052081650840c10084140c8900013119002d0302c820f400b9580b050042d0b0303150120a02c2d134503841156108180724028200c4404102c3d160300040e6031591641566078242155820b803c0000030841b0001d041141d000170703028040c100700082e034000f010380f0b10700720903051140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 898666151 1250 898664901 898664953
    0x140c0a08071b0f08011a09150604030b15090105030313180612060b01182103030207050303130215090307030b130b070e0a0914190e0703050c04050603 66
    0x80d00001e0048240120981c100c1080d800112800003055940d80f00e401550181d0310442c8155420b00d042c1003a02103140180b0b00340354002030302400403035603201c0109075507000222000d03500240910021001c2000050164440d280380c1110303402c2d28810a0070082c0280050748607502c642d2040200300a02d20005040900300c41501854440031f03021196007030094030710358106041d2508000c1d0100c013441596000100382c100d081e02e81160480002c06107118112260180f009044142400c0020b9124802e0394983c1450003031400504015a90761146c2c1590710070b44040051481e44013102c0c0640c0340003800c03291004407810300b8610340001b12001c40d483d40401d10010308519034a0000403440054403015150659114000491600e402d41018010440440328540078540031031307002c00c0740341081c841e864240158010580a0741d4455050076050a5401d10710800562984200c1030360790020440b1401952050025014590302101400200c64005203c68825400b0825010004080703082d008004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 898667401 1250 898666151 898666163
    0x8060301060f23130c1d151804140106110c01111b0402130b0301092405060304060e0d0e181b0a02150709050f0306060f040903021c080403140c0a 64
    0x1c0380b5604009001101891303074580d070440c100143d00710034544c802819030300d060050750000548900710080c42072200e0b10f80e040b240410010403030390702040443c082400344030000402c0403511414102640380208001c3e401039010030940701e9204050743c021301541c44003910a00c0c010311a04511303130031143d6414501110386c1050902c0189a030f2a41c5480e0100c0b0007050307200e074202601c95600c00350800ba66109124109000c0c1c42c0c8041c000d1454410441c4011240312120401400c50030601001034541c006001203611680d15204c03800ea2400c24048001d8180c45902e5443c2c40741506c0090042200035031030f1300c1c20780341f000104110411600c0d00a0b01c001d10385005240b070312040084026468914065044184480c200307082040e21070303101003c0b40c25610159604001c18410900381541d510051361030790390008080d50b08012504050b0300c501401030091046401020b50700440940c510740440c004c00c0001c0c00c0c10108418980c11100e03107011301c10000055803070400001480e03900c4000d8500c0042030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 898668651 1250 898667401 898667459
    0xb01051311091e1005030708100b0f0a0c0b0708010501020f0105041a100306150302040b031c030e031314011b110d151d1b010c0f031e08060301060f 65
    0x103015000c0100c843c0300050040840c40301c0c000b1028040da001241c0590024a90a00245031052413002000480f5107507a036407802d0082d21b42020b2015085802c14204008500c5180001b08107811a02c6026900a48540e0b1903541010002420b240b01600c84400340d80c100001d0000003016103440c080c010035240018550703911480b5002d041e804869201501c40780c24000607407290300040c2030040840f842202d0410100344082d05240c1c403070f81c0310a540c48220041006880729107010fa003200d9011000503055038a0807020304038144044e0010740004607190300c2004030720010750700140312a500341140084190000301a6449428103100ba01c1101e0203818140d40030810021030780e5952816034070302c0d04c0921503640e07a40300300e000180e4400d4541e82d40744a42c600300c01c00200d031840031103400581a903482480d04d056031034104885a131082c00310301304104074200ba8410b4140b103070181d10310902035407000350030b0914404040c2541c940e5013102041924151040046002a00c0c034564005001003011113 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 898669901 1250 898668651 898668679
    0x12091a04020f0a030c06023703260a141315090b090f060a0605010e0f0a0801050106170702011e09020d051006031502031e090307020604030b0105131109 67
    0x140042c0080d0348260482d43c2c0107804420810b116000700241c42c502d03801c5074900c00346800d800f4290b0094004103201d030300d14010400031140c1c0311049029580d000b41084010720022000700340119016400480c0c0801d058010700c807100759a80103801c40307400e05401001030350400c07510382c26900c1302c0800c00070251050080b15101c18007154101c0c40c00c030358012000d5442440c00c100440e03200c0e038080782400c4450083c030300010300a14140c8190000d540c0184d46e07040c9039240207030a0040d9440c200101c1540901800000180f84409025150203090f040e034814800344540c0780c540454840c0038045005690600c0d424101c020030031400440000300c1ca01d8003041c56103490010682c0b080401c40701600e81d008907070300e070a0001030b240c00c044102c2c2e2040744032007410407040b80c1d900224041540c81d0b0018140200c164401c40300c601d02c82c184c001c1e01101c1924078011007540001c2c0700398082da1040743c2e15881c0400400061912a44651001204043c28003a200c1e0200707141c40b0034464113946a100d0714280348081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 898671151 1250 898669901 898669909
    0x616031e09030201030c02060108120f040f06020120040e0406020333031e0a030305092e0608030325030e060f0a111e030a09060c0f12091a0402 63
    0x103010510448418030040c055560020201007090005074042400c1c0180c1c21440b1b0b01c0018088d0488520f140a002c0c0c0c403030600540ca46540c88035549801c400818400811310304114405940100a143c000040c48c0502c02034a00480074000040c01140009010410103010780161856010780e112030016aa5500c00f00700c61458544034108040803070380c0810020682800942a04074904110100e038407065054800358071201c00c420942c402c3d07410401e40000003c0c0241c20054000d1895429a8100a0442840910091440d003005c01d0310500710301c0701c0d494060504c50b410240050b440910300d50b143c02012083c03081e001c010360b5403210580c11f01c0c0240c0181300f03a212006690556040d50305c2c500741410400e0800c9000c0d2400340034145081e1a00c14027100034812200c1300e0b86100100d42c0641005c1258585139080107100c0c55205882c0d1146000268a902c035181c0c1c0c209854803140c41c0207051001c004c2c804120749109007034181c41d0480000104102850140038083c2c012030081003607849201103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 898672401 1250 898671151 898671167
    0x1805060d140c0406080a0f1203270b01090227061c06090c030c0210050a090b090a121b20090921030c070227090d080c0405061603 57
    0x1d0080600c08410003280003000c0361200c1c07940002c0754140070003a20b503d040741c1c440d06220001015400030142c4900014450389400c4c5485007207080015540c0c6041c115111086d04000c86500d124003580b41810030058400d4055016040e002d20860030030002d081c2e90525042c5062000262681d01d071005803542d51900202d407841c072b8681201d60229901110003102600c528040c42c8400b5080c0301303048251520a1185d14400b4200713074020074010740300700300400043c00090007003910240c4400300c2e4404120076610460003407080070001c1449050901700307503621440381400d22080201c3c40000303040c4480d129005030020741d00070000254071b00788034005842cec0072882c0c4d07085604203024504100c6010804039030f0f40420007a02c540d1844281c445244510700b44000c8610704541d403018403840c3d0260904600c518011103100e00c5140c0d860840340c4601003604021a1180010390020516124181e4400000c41c2c01040d45409541018280000120356000c0c200500108544540219003411b04c98009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 898673651 1250 898672401 898672403
    0x140105090a0b0c03042f0a050301090b061203090301060b090108070c030e120f0a03020102040302101b06050621030415050c03121b04060801060e090405060403081824010e011805060d 80
    0x1000d40316460030703041c880d088203982840c85241e85d1f901c0000d09040600501c120705a004e0300750041595954100130881003903035000c8400784000c0c03107000c610b9142449100081d004204103030f5111580000014410f03003005140404018941b281500041c1c1c101ca0600800c59040703d0461680c14482030f02440d10701c0c1c80c414039085205010030007003032640650040041e680261146119003030002c0b410f80d0380d096500c01454140008084200c003003482944200d07000b1000500780360030345110704c010500010701c9110100321074100007002c000c4a0956020001504418149282018130904c00503459000300c030050315481c445000002c4551428014481d8010f1518214a88564807844002c0000c8024014900441c0c0d1000c2004c240d4038002e061184100d80c00f60043c020b0395900d9804460070003015001c6402c0c211541d40442c0f216005004031000c0f14401c4880301d51907940c0d01c62200300b03490183d01c840e003260b074a9001401110780742c012440b2600140400801d040e1540800b159824001c5c00c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 898674901 1250 898673651 898673693
    0x1209100513020307031e0501060f091125021c030305090123150d0503031305010506060c0a030c1b1202031005040b0a180206070303020c0d02030f040504090618140105090a0b0c0304 79
    0x5404680f2008158540040c1d41c501d40d0304210304060007000110510640709100dc05003485141d002c00043c04141010b084d520180080017000c0c401514964903210001084011a8440082004189007442400c90740442a9000384c00e008080e9130403030030440040d0003103000007003040c012505030719034060003034415a0000448c2d03500d2409041d400081c5d543c1100403110b650038080800c2051400d03c0a64402d1101200601100d941c41e0b902951000242c95044566001010414001580445210004241003c0e40e40c02800c041e10400d4248041c0c03100030b4002d00d28103c1400045800d000302d19610246040c800910b040700d00304803021aa0b50b5242c0250b001c0000555041059450b402a10158004104880c1020007610050740c4900440034a040c0c01c0c14240020803844c6026003103440f03182d024450009079107010400c4500d9000c442e450940344c00c91320301030317101810340309119643d8041078400140c01c0c0f20100e41e0318107002d0b610141186045110110202d41448113004040440c0460f01c5e03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 898676151 1250 898674901 898674911
    0x1e0803030c0d050f0105010e0103050a1506020c0112090b04080c010b060304120f080103080d0f020c0706020a030f030608070e150405040b1005060319020f1209100513020307031e0501 80
    0x42040d841680c882d10201c8102810880030030b4081541224080c16648141c42d80307405800b503540114014500140180c40d402d8031045005601c4584504490241c5010343c05801407035040c3c070000d0000c0c204000c1c0d1119070351910071f1020200d100103400a412a40c000d503000e40d07511001c0c900394050040f41420644c0510000148420842034014005950f84a501c8201d15180b46480c25603440b0024400500424810850703030101c042e0fa80c1c0300945a000754940182403400b0542c64500d0000550859405680518494800d02d42c20880340e0030325400ca464280001c1313051405540d100c0e03100f440b44902000b2008003040500d42856469004a6000350040010349054142401d01c41d209545800c91508071000200343d82c1410003c0300d02c00c50f82d509074110076140000e006e02c000e40c0000b50924401d94244034401d4044c0d0003821843c090450301004049149824628004881014081504c4c040c1140c0129006031800b00e103000442e80c010400c4000c000c0381c000c02e04840100010b005055520b01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 898677401 1250 898676151 898676161
    0x613060504051c050627120414031b010f0507200405063007030b0a0501082413081e07110102070323150c0a1205010f1e080303 56
    0x10201800c201e0714115541c49865080343c402d01050700d076181000d0402d40080000031441540b0f0700b0301d495138402a040c81000744150202c0c26040c80c2c0000e6805840a40000d030401401d008004200440304080703019028550b05e1101c02c88001e182400020b060003000f09049856a00690940b419550410030114131003008000d41120090361500701c911407440c24000c5003e608144203010100c4003504001101d040e028000707104c1d406054045c4502074894443c0204c00140c041610324040d20012002260035414240d005083c02c010000b648032080c440140d800400700c1c0302c40700d60b8020b03000110301400d400180c00e24800c13611030500340307812280c86007505121000c000c05c0140b10241c040e0520761303841c64010004907143c00e12803102074581085000d0b013030549810740c088005985081c0701180c5450503641d00340f5003180e070101c48034201c40c00d001c10210520f9421101c0004460918001008150304001d805030002c419030090900d07c58200300d0500076500f00000341000341000d001240c0d01d078500703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 898678651 1250 898677401 898677407
    0x60708071803060b090f010b070f260a14032401110d0c02090c03250302070b0103030f080907081b0103090503070c0f090b030d0302160f03111204051c02061306 70
    0x20308814034041c0d24600c5c0051801410908000d0590341c201600381e14014241d1203030f540d10f503080ca4094880243c0000400e43d42c040010340341d4001c07980c50f03030700316120000c860010b01090204044503841c2201002003040400f50070300002000c11985042000001000f401201c0d101d03c80c0041d41864451040489405a0841c605200642c82260140c1c00c82d6181e081400c031074082a0b4010000b2100c40355408050b080075140c0d80c1c4000d80c980790042c01c125840c2c41c0c0001c2d546007030384207901298aa02c003540302194095140b560042c144002042403624208055030b64208034a8004904000003482e5062a031103030b0403031803407603402c201120707200c0c140da0400840442c1c407413207043c010050201c800510b5a5860089140c40c681c014041c0ca00c1502c24a0240c1c00f80d84400000840e42c540d448002c3c0000e8000554a1800e6010340e03103020032050103c03016407402894440a1464070420b100420090340c1d0002c000860032003051380300100c40620310100711a80590301d5501c0d000803842c4004682254 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 898679901 1250 898678651 898678661
    0x3210904020c251e03120c15090803040c060806180c070f080a090815070813020301090501050604050601050403261918050907020c04150f080303061f0206070807180306 74
    0x1104401c524540c00c0012082003581a100c01806e40d004203085140541c0201d455002050182001b000000d980d499054102d9107010b00450b00d90002105110078005295081400b400d02402c1c403403040c3c1800000907180070040c1c28402550400d002c001001114140c0540d40d019610907905580c0e4049440c1c40313041c0342c002e1980900052520b480004090200195000d036161014410245503200c070032044070413410051060400c101511403c0c00161024800d80e40305030b015000000305030409038100b00649501414003810040180000d00128101c0e041d8004010003064142d82200ca4269a01d0fa81d806501c00f2078820440300100c0d035070516002001c5500c007031002c85001c000e554035001080310a01c801d8a9950040e03010f1044120f06050660000c3c0c56400241490180f2076901c4103909034465454220f0714480e00044103115560030b124100d00c40340141e895118100c0c42036007500035a01c42009000008108094020640d1039000d40229a42c203da504410716a894927410840081c2c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 898681151 1250 898679901 898679909
    0x5070b0708060a0e06031e060601090f080c0904050c21060901020301030b0105010e0d1506050f04091e1505070806100201060b160203010b1306030203210904020c25 72
    0x580000108618465a1010300c1510300a004028560070503401c1412080002c09081e0188a40ea0b02c10410359903015141025000b5000203141c0c0d03142980004000c82046d601c00ea8101e041480700b8090b9100108011424200035a0408242c1e502c0c2e0401c940b61007100710445421100d84d5546641f0800050000522511843c0440d0a0341e29104201c80c200e22003448017800d0b080c00700d00148103070b40c0b02c0c0040e6100800c0081610942e044c02d030b100d484403c0d06d01e284123400c41d60348440402c02800c064030000c100c007104440c00c018990b0145c0f01c000c2c054203a081c0c444041c280003400c2e0700801441d0122002d2200c9900c1c0200702c02d250120b0041d110f00d02c1070b00c1d050320850651803400c1c284c92050241d4400c1c1d589014078a81081150309030f610254010700341c2260315540b1203500e1140c0d84c03903501003c04031562224011601c54914014141801099180490010390039a410482c5055074401c8075090503068400580e140071940b200303810000d0384201d0f0101c0f4825100001a01182003843e40b040e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 898682401 1250 898681151 898681163
    0x2070906030b04021503071d01020c030106090c030b0402090a120f050f071701180b1b0c031305150a080402060c0a050c03060115120c1b030201060311040b0108060d14030a0507 77
    0x244504000345c07031007404103c80c56000160300e656240441050310b5003071624048180115010b80c990180002d0955226810140416a07034100c1c074400f050f40b41c0981c0050305000d89007186440d05090124244402902840801c0d200c51210202081008405410101d070020300b650030b03070100821180d44030702c40c51050044002105070000300102040c410303a10700c0c051a04840d00c07518582e44e0380b003601c440010030f0745056911400075212141c2d00d00d402440d048071400b0103199902040c00400100e041d40e50441d03030080640406401802014034219401c284250426980d59601c0d440003e5042c411441c5440d114043c3c480e4040c10051300160188100400f10301395a040ea0321120402a0403103413480c2c81000500060010382403050f1603004c000044001c0c50507904d0000700c1c00281c18080d003060001c034010b039900c41080090205004e43c290010000311414071005590b000000d03d0150042c000d240b00c2e4071041e00b40e400300107a440701c2c12848210039059941301d1116607405401504006030590700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 898683651 1250 898682401 898682419
    0xd0c02010506150a2d02060103140715050d090204021c290108100f0308120106050901090b0c100618060801020412081819151110020a02070906030b0402 67
    0xd4500f0b42c40111610710004045810090998022680c602d03058103150b000014214000200c604900b0520100d82e513181c000300780d554075620b41018030b0011803003600115002204d081c40801c90082029051465514029403540c11241d00140107201031030b802540188000740050700744a03004030b991003001c80084100240c5800395140b8441070717070000245505d4101e084400e866503005001158001c603440340070342091526251140c2d8400c1c0ca82c1c1080c1c803d400080b908502e0707222205074141c0501440c1c54540e042520100019106022034065000600004100c4000c83c1c40100010b040b00c5203402802e114266841080c00306101c803004070080300600745600410011014001c64007280d0307455259010b80001c0b0703211009250081c221800124000d04d1080586540304049035802292041511601500d09103403205404880d13500d02c01401000600c00c101d084021454200f024414400541d60b00c021220407802c00120360414030031940350038004024080501c440612a42c400d880c0f0310a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 898684901 1250 898683651 898683661
    0x50702070611030909340509040f0e060c040e0c04050d1101111f06050a050f010c150603060b040e16170309040e10050606130915090c020609011802330d0c020105 71
    0x420840d1030340c6d480205d07100b0450380000c0d04190348000b01c12441c60100040b04426a88103d08096054a041d813621350702090030301408500514054021008020b00c0d40360901d01400b18001c0c3d0b10100c00680144e0107900c0c508072036409000324400040c0035905450488a84010142d03088100d290801d402a15250b00441d440c2403800780078040e40d00040c148200192840011108500b0f070020403101c0350202c100d501c1c581c4c110b900924024512500c0c022500b078a2180c144000c84090f0f83d585440b66104648a034200350b8072110900643d61240d070104480100100b407249036100381030004d078102d89411043c8007082c2d004140070204691007081440b141e224103081101c18094400c0c2c200a41001407410040341900364840b22004c1270500c5805541c56480c1c00082c100c6112a40340d8000d40c00090810504400070301c0740c07054501008403400110800350700071507017410609070280407442d540c18403504120240c403000f009030b000c800c008a0ba10007c410b00c1601407c13101598801644c03d100c003090f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 898686151 1250 898684901 898684981
    0x102070f050c221a030303010312080c0f03070804020303160f060c0207210507031205070b0906162f0a050c03060622060302190810050702070611030909 67
    0x4614400f0800e44501400d8220000404d20122500c42105103240c20440c1c0d034a09002440c029406a01d1013080e00358a050041d00404008051036500c00b0304011140ea500581d5054a800c0145403622150b141e45510100b8558401c01010710190041404007004108071241586446441a00140400340b10b440040c0c1e42d4021034000c0c44206108010480e40e45c40305945101d100d92f000d40200c41485642c0d40301e400000c00710b10840000a00e0004641e42404440340b0030b150081c9100000301200c0c50024100c800340443d60401504000b41100b0300c8011100e0b04126903482039400c00790800780c2c540111180c0d69140207070340031255401410a1416249404203c1034422000030b0007400c0c503041c02c0540c9050684048400c43c1c00542c0c0d840700800561240e1710341b00c1e08008000840104603040001103460a02c1001d1404242c9080200b000303581a80407070a0301c106d40180c02c20390083c00504901d80c0c103502412401e00d800441c803e0400030350b48400c0d84191481013281880e45d09040ca002220 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 898687401 1250 898686151 898686169
    0x5160e0402120402010530041b0602071701110a021f0b09010504090311010f0e12041202040c05120703050f0f0403020a140c030102040308070215070f15020c0102070f050c 75
    0x2c4070040010000740c00340d4021707401499409200400d9084403804114211400440300324007201003c6c540d020007040107410720350b000d580401490850180c515001c00255544210701800d1388250b0b010002c03541d0070200350002100b242604205940715120404002e41e2a552000b900705017880c00720080292000300d12030f40202400141c0000c010781c0c240401d000141058200031400c01100c3c84140d40c90440030b2040700184c841c40c00c03002c5203040241d0000352404903070101800000204100400c02d940ca000d401032085030703040d0340104014003868000d4035240a19a40501c0c2107418200708120141c0c158001c600c1032804060703208058541818010000904480041c09684001c5c0040045106440201d024202c40c4c0e00701c92200522401003401c1e0f80095004a801e0407000c52108110b15080c031040c144080382c1f03041c1600300344440e103580500c40c00918000e06002d000190b5240600d502c1e8040351030905a0200956132842980303008641c1c56040101034800c2c3c080c03084001c00516180c404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 898688651 1250 898687401 898687417
    0xa141b030103110a170c0a210615050d06140709030f0f11122404051b061314041a0d030e060c0a1b150801090218030105160e0402 57
    0x1100e095a08607503490fa101d01c0c400c59095409002480700003812100780041030038044551014108000f008800d01c0700300070032a04006c0381c4901000a525510345017804030004c0035080240400e203141e03075141031107103080e0f0b17504081c0c0c1040b8003c44d5030040c080704d41c100814000301c0700c00c110b2059494120448a940250100420002d0002080d401285a0108044d1340d580249206051050014000b402c40b000c504450031494002c840c10042c50180c0081c040a41e80951114150920b0640e49032501c2c0c8406482501c0700080e0b4001201d0715459200a07a01d502e98104001c6004940310000405921917400900f80f090341864403d6020840c40900d102010310050400004407499a41c1919041c147e40f581c140c0080301480146c075881401c0041072034a5014a60130244600040c08040120001d900000c1118007106c03d071110055105100c07a0449150110058036008500740014003e07094003803413030f810741c01c03d014031130340384401d511001032202651140e1041002c2041800181d01031020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 898689901 1250 898688651 898688701
    0x14010203070801120614090d11010902030303011203021c110607170a0c02010b03060a05040c0f0510050d0e0d0f020d09030c030b070c05060906012c0714040e0a14 71
    0x4004e120204e00d01c80d0a002d200d010085001c1c410040882c3c000c440c01ca450a00c07990000c19964085a0802c10819000c001c400082c402596660080f9903284018400c030041040d10b45602d030305040c070a00c071009520085d41440a42000309a07801800c0380b01201031005075001340008115103501840c8d91240c50350b85104600c50130795030000480024580d50103110f040d9500c505c0f840b45541c6d005d225241c41010036840004040c101402c0004400340141c1100c034241d03095013028865075490307020311495960a85040c9a42c0c1c801a40000040d019001001c00b00c0c1c0b107282c0b400d0b1743c5190000100304048541d5406c403400d00070785410842e81c02205d8400500754150000c0140013003403d00d0200b96218265017400c100b948070658489140c80811907549050f600700381c2c01801703122a400380b44070134046d0303503484804100c0c011060440c9100c00500320405102002182031072054156098800070444003042841c545004001c10004c1c00343c400c9612003200d40c41c40050b06000101e03240b03c0e85079100e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 898691151 1250 898689901 898689917
    0x605031306020912070e0a0b0303034003120c0201020721020712120806221d0a05010e010609090803070c0305040b0d1415030a02090604271401020307 66
    0x2840300c600940c8400b45807608043c121003000c4d88a2400c002a8006142000c0842e03903e103007840e0380070100c61926840c18400d42042040c00400183d6641d036542032002d0402c5400040030044424501ca80b6072003100103030312003003000001490f400014103411100d0200f4103014070294540c08a00300d1050a00c0200300089400f00402c18510040443c1c070b00f060540112654181c80c0c01c501031122a11910440d08220070500d1000210340c014080381d04003006031100b0a900d22160b10940105880903079a8900d282d996130300d641905440942500044e00560035101d0010941c02d265003e4452000d90b500590300344100006c11080328402d80c9801c7d604050001c0c1035440341a4212121441c101c001d8040040600000c646910100c004000d405604d01c4000360712454101c188540c500020021040c00403e00089801528042504864140c0c1166500303001e54078000060000e000350b00101c5121050300c0303444c283c4016220885003501c2d01034030304d640807400c2410b8943d00780d10040340d848001680113 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 898692401 1250 898691151 898691153
    0x10603111e04050613060225030b070233090a030903031d100e011701051c05011805160816170c03010c090603060506030123010c06090503090a06050313 67
    0x8003900100d228034001e5142ca0240d81d00000380300c0ea00031020006021a550300308201054041001c0e00007000c071041581e56a0711050300040344145184400380444101400180a452003402408800580c10b441425805503e20b5503800c13100c02d03003030200910b6503048003140341c0050000303404142681c1580c03006c40890541c3d408680c880c0004090110840500901100f81d540c1c503989050000c1159a03200c2c100255580010103402c2c0d0044540d85c9042002c1c0180039645620913511483c0c0c11368054144245000d00d401030040941001e100010202c805944e002c0240104400d20140000e812010b1526140c600c2aa1562501822120121022034003089664841008a28400c0c9070030113460300da400302c201007820b4481003a08a400112941818030003942c01d44108000f824040e11050b00710b40c1420b954031410314400404500da4400d86e4001c00f080d03031058002c004000c0d4420070034000341509150607981c0360400d500091181040400c042030040c400c600b138074412010102c07210701c5140301d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 898693651 1250 898692401 898692427
    0x60501050312181c0c090207200a0308090d0b0a0902120f2d0610050109090c0e1509030a0f0611070f0311011112190e030706050606070204110a02010501060311 70
    0x621085140818404c0e000c40d030200c0c04a40c0000000e1107070f000301503504c0009103042c402030842108070080a6070320890600031910b69064a505580c5d000007480c0c5e64416420000b031740710001010041150703600000304500500350380c01c520301e00c42c82a2140604914003294180d2903480c03034400801c8503030103911504010a004000500d03091011030f040000d420150241d04d0070030204580e0740080c180d084408115a5900001200042240440400c043d01d840b4a00074804240206014840d1040201601140d02924222204508002c045503c903201c0c61400e46d030312a103402c4040d9402482d1100d03c10103070b400141211009980881010740e07040d0341c2c3c1e42c151840f40c045c984002c800d41d0b03122000b40d4800e450000400001d5100145d8001a250034072454a21884003e2400403244c108004126484000802c1d50542503000c400840d20340d5482001c01c0180c061013001a42c4141802002a40b0207220002060304000c00e03802484103a0301e5141c00d4080c1d4501c0d05a91280e6241007000c1caa01044c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 898694901 1250 898693651 898693669
    0xf03020301061415160609060212010803040f140a080d080114090c0301030b1519180204060f0f051c061d090601050f010c0c08030918090d052506050105031218 70
    0xa84441001101a15611400116400101e023158580e500040e2080d800500164a500424042e03006500c3d04c0d0170014180d41884844c400c80b0310b4600c4110f0481282c0d56607440354005444400112501e07490380c00340003048041c0c00e00c28001440020341e40c1d00d103c2c2c05d00c08040341c42281441c0038140b540e46543c0e9824403040c00102043c0324185d03103202544690359444402c40d0300b4181000c01c00350441c1011800081da00482c03d4040c0164410001041903a0f0014a14a5202d4042c1001800071565800a4405104000c84084403040c40201c401e80020180c0c40101034030140f01e4000511912001d030085108016504200554005801004203140911905072800b2041c948941c404400ea40e07032143d40c01c490307084039482d9000810050510300300b0400e5501141c0c140340780c1e00c1036030a01070403040c0c0301c1801482c2141000000a0454054425681601485440701e40c00101d000000d040c81c0008140a0007190f1090056044074006070003c003041e11504645028031280c1182c0c5041001440c01e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 898696151 1250 898694901 898694917
    0x10c03050d05100f090b1e01120501060915022a04140f0103050111070c06080a06031b03050c030d0210020d0b1206040203010c090305060412180f03020301061415 71
    0x880200320008001c007036402158002c08403001d040c1402800c045075000c130030010f030b0040c201040c03400c81c01640035030303a00700444038800c00441640f4407500c51000403200440f82c1841d800d4154101800001c25584c801e0200c805c03207459080b01e406400007808105d07210407c04903418005151801d003601d103802c07584000201c4080060000030914040b03c446000c480701103440d0174030034a043d401003080c4070782030040090520640ca182031801f199565240702250960094174104040140050034281482e800100a141c01c90000d09280d001c0307103020950802a0302046641e40550010b0084600300001c0c100d000c1001a0007500c3c140c03124070b034548003d40000501c0d014040e1609022680754030fa004d42d0904d2000e2003c0076000c5883d01d4010300d030030740f09554002800c00400345406c10201c1d00202d1000e800561200d85142c0f409416081110a00c030068401c40514420b12400181850070380101d0045034401d4000333002c1c081e6222280c02c00f16035032802494101d2009141d08003440d0081004005013 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 898697401 1250 898696151 898696157
    0x50d0b0a0b030f07031a0c04030803040b04020d0206040909140d020c2209050706030e0a170703021e10110f090613081506040e070510030b031e0105070f090b040302010c03 75
    0x3c0907201e03582d10300c0c00e4240c0c0d0040d1031100d60104001c20b100d86088107541d0101610000754078013860744d03641031031a11001b0400f4082d02000f10102d01107581d0240412001038005240f00d85407600d5040700c13801001202c0741110300541c2800c181c0c0ea240740201d0003080585070b81d0040c2296440300e500f400f800840510b43d1041000624004810341380c890f200c0c04040901403002490034508000c400f900310342501003200c90580c03186500e44001102194084480102003480503194141450b003a407500c0b80b1040120191100c910300c503002c0c40400130311190511920f1000b841b800d00c1911000c41c2c540302e0387d1042c43c1d005408000505140c1007403002011100a0245d40c41050750ba1030002a080c200310000600024586100380516031406024692000d941e107000f40140c0740c900000500050b022180e5a810325403a80c0c6880d206907414448001d602803140705502100c041000e03414000e0400300c070b610700451002d000301c0c448a8400e04640c001c0e10003c000c824030301811600150307a140b41c1c0560407010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 898698651 1250 898697401 898697413
    0x7020c120a0b0103060b03060901090209152e0210020315010f0203130e060103110c0a06051f03060b0108010807120204050a0228020d030c0509040b0a0e150a050d0b0a0b03 75
    0x10300400b0040740254050540000e01082d0842014103160010b00b40c0070580e03040c200050b0240c1d0f108003082c1d40091001030096903048400c00419600103001c0315421420003c0c20000e49809504203a0310140b080580c207588040d201074000104900056643e000c1420072589505501d500807001c4980c00c2c030907801100e041c012209441d40ca0548140c215200c0d41c800380c014421196010f01810710001c131050410707800c20110540c03840d681c01620602421281e120f001207140d10f9450881c1d17410000690245d510a03035103c1c1010b402a0251000441c0001d55950001858080105600b415180361203191001601550200400381c0006001c0c1004250300f00003401c01001440c8907080515140381c80e4440604009801030300304680340350002c05142c1407550401c8015845411581c00481c1290005000690b0501188488600d5040003041e441d580003400301d64407202c0840700c00c49104448029031151280c050190500d550301d0010040c002800c0400c0304a4425008540500e2020b000c6440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 898699901 1250 898698651 898698653
    0xc0818040609110702130e03270105040311010c02150c210f030106110c100c0c0906060c38010e070c031b1a07050d06050405070507021009050d0b0609060907020c120a 73
    0x30440d4046200041d1b0102c46218604d581c9d0b00d4107a0305003140e0001d0800c039060a1954654112203442c3c07009c01410080d010380d2400071560742054241c0d50380024480c15884401e00c481039691420b080402c8020360f92004c00d80894004000111001158401c1c9640d00f140d203441c000f41d50f2440c03000013400c082e00605810098a80f00c00d0106401d0070440e58668140b40700354100403144012940007905124103201c810b010700c9070840c1d015880c0c0d9070321800310390640d410f000000024a100411101300700040300f485158a4540c550480c2c16141c04500c40881130301d40b50020350320080c84140040104403203074014200001c12003400309409001b0142d180b00410740c2c0780605c0150387d0480f20140854008240d504640007039200d60009001c00b500c0402250602c900090564095550002d200c0e2040030582c015580c41079044c94001e090103003080101041e0342c0b501d00c01030700c4101d40903070040c052040094141d2820941c0d250182c10741da0003820404000c4404d01447c00b8131014140030510a440b4804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 898701151 1250 898699901 898699903
    0x3080327010b010e09040c0510121b0230041e0602030406080c2d1c0b0a0b030c040806010603091a0402130507050708070b0907050306010815070c0818040609110702130e 74
    0x401c84045a84800030103254141c0ac10032242d82c400600c0e200c2c9a202c0c240007181d42c000450100f0020410700d080300c4c3c14099111042000b10404103401003050120b40083c2030b021442a0740c444402400e203110440b901c64030126500d005501c00e1000044104002c034040c0701d0010000d003012010b401c011030204c07521061443c021000900410004800001e1440450515101d0030480381200703d024851846144005640141c1c24018080f6114000001c9016002510112001400304000b61a41582d4480e400340c0184540e10042d12f051007210507091040c03404200c06031089500410317103000d025107502510000c01d0000c0c8128213204003005100c0210341010003500d9020700c0780012883d00e00d008070115081041c1035000d01c0c0a584820014082e20002046800b441b101d8204503085a80d03074464100c800d14074100000c0d1101d44000b0742c07603d03102c080361825804000d007034074148030700ca590746a440101d03801610040010030b4144100b90040ca048404e6080600e00c100340410344503600581a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 898702401 1250 898701151 898701169
    0x30d020d0f0905060c0d0e030718020918130201031103061027120203010e0321040c030b0f160203190503042d1712010e06010903080327010b010e09040c05 68
    0x4407815400101d03031034221688641fa140340300d02c0036005000250310349804484410f102d480d01080442d00811154401d4691103a4051984490396200899042c4010400c009095040050703001a00702041b002e00c504200007100c1c00703400301a06070403500c580110115141911140c1400c4c0d0960448020154034490b00c0c0900c0c041c0c41084101e000c0070348180b04260849041400c08040c54106105c905800060f2404c0025404a1032503c1d20090b603a44c0b0708650300b118241c000400d001c07000320034800c0c0030f0410101c86204010b0440c5000c26505e003610266a01c2c040c02a00c1d100040c1d1101c2204006071054010b1600300f4440e1024000d080281405d007440c4403840300c5c441c801001000101001d00c5123124110203690201c456a42c9400d000982000b06214140214200d54004c100400c1e002e91066248800941d001800b491700d0f4146005000c2491346000d06042c24949c01003800504544180300325140034005840381c40205200100744903441e0740c0204251221a041c41c00007946450300504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 898703651 1250 898702401 898702417
    0xe030709020f0d14070906180e0c0309010b01091401030e0708031603180f0311010203070b090309010905062d190306051309050a0b130203011406010806030d020d0f090506 75
    0x50ba03a168402298070804459044403100380786895803050000850304204103006449891900450051003261102c45990043c5e100c42144001c1a042010844c01503016500850052000344024178181c0b00442e901e00041c040c44050b580580e29000c2c0c1507019500c0098403100f20819200c107640c2e01d0881e541103420400e44c00600061499041042603800391202505011096803081c400b03080281c40d20000146010050081107295006a0036a00800988881c5588403482d50f65500d00401000d4403a045000c500c2d010520004003c01d440c07404000f40c600ca21035840c3d102d10104500404103105601c100e40d0070840b600b0410a140020031400b084008003081030b1400314401c0e00c0c142c14030003000c414500340418603140c09040780c00200007107070000071581c00946840e0591907a2401034060980d441c00254198642141c481411040b50091482000241c0b1110055681d00303040c0340d11107000c6200240103130059090170603101d00940c150352042d1190310f028046030b51031b80081540da9019000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 898704901 1250 898703651 898703677
    0x90e1807120210090b0924270406081b18181005040305180f040e010f060902070803041b050a06021f02210c07120c05060c12070e03070902 61
    0xc00003056003400212203162410310304d4001e6000d03190420700b0400c0c5c0034101440b0702c00d640310b07e800e44001401080790301d00c060038402010303569402d041604240b4140e06829040c00710340060306a803117240034810b03503084400c2e61020380414085808824981c0e6880d0b107420ba4031964011001c20070882c401001885180240d9000c064032214102c41c600e000304012007200c0c01d9040100300300001e68020252089104065400440100300000003103006240d20000c64210346841001440224150000000b40c41c9500081002075241d83d02501648580140030300341d02c0b020404200010750705180000000384604495250750b880b9000030b807030b017440c5610583c0160301c0ba4840d1001030618826024070320307264081c2149010503090000322085920012038180c032070305d04000b841803041d1310200c6100aa000e03c451443e0403401c0d0300500120340c907031001d56a9119590004910000301d00464280748117804224100b50341c0c00104a03207032469202019018000c0314000141da00d61800034000c90440d0270 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 898706151 1250 898704901 898704929
    0x14190c030e1509040f0605130204211a0a09050123151003020c070504110a0212070b0105040902010e0406170c09160c1a07021e01020703090e1807 64
    0x204005054004000d000303482080c411650b0794451210703004039000c014042c0c401240c1043c3c203c0304040200800e82c070042e0000f0490a40e1210300180b94000c0003030701e048100401c3c03030f07040b1669000d2109041c8400207003448076200c40c65089880381640b0030340c401d825101c0810380e01c050356540e500b07458102030b40840030002c0700300354a442542d001e80e9030b40c04410303d88440300c0c0c044180001001906064540c00500d03500041c542d0441c80288803400107444080d10502903200000881000c035031141d5203090041c02801d504c030020580c6503045070307080398010071040b41d140d00b840c0403c0003c10018104a051103450161311805840c0e41c02020024005010001200e85d4070100c4141840c019030561441484c210b000c00c0005860301407180105600c074600702a16041500d0031002150519440c0308115840c41d04001300c040c2c1c000354641243c00e002c0b110f903808803405418603003070340213900c2d000b00030408801092081c12103490705180d01540d80300d62000607821500c0c1582c1031035140d410241c0046864 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 898707401 1250 898706151 898706153
    0x90b0a050715240b0a020a06180f05070311120714010521090105131e260a0e0f0319060605210f030405030712030c0b0708060a1a0a14190c 61
    0x50030f141c1c2c000e0540c481c00c07610b49100e81000948400405000030445640c40081e04000000003074212101c580c412100c030002c69450070820796031005072000716145003003850741d82c84605040000080c00301c00320000301049030400c11100044021707c1111810003d05001100765031085200034650f0582c40c0354070f08124101b9050040c2594001010314812041610303445001034080416003036910400c19201f800720150b450005111415804c6502c002010b0000000306004860001d050202a43e29003150000c0380c0d40a000c440d094448006170705410032592800074480c1d156003070014038407402c1c0001d03000b0348590001d0301e5502d1500080b60070b0b14101070038110000c030403c04042251844401141014500000281c0e41d032110301411600380c00032081e960405004603c3c80c900c16601040d000c40a181c50b11001700300c600c085a450741320b021203410014502d411101c03941242408074030380c50300d082030182065070110b4100540a03c0c3d8902001020311103102144d03005012401d1780e442031000703416 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 898708651 1250 898707401 898707461
    0x2603040813080316061e0e071508060d030f03110d0b0301060504060e011a1926040507062109060903110102040e0402040c0e120601080d090b0a050715 66
    0x1081d00700b090198402c00401d9620080d03514413003030095008101045012103544030b44000702c10200d02034191130034900d4032120701c140403480e0000d484029003042c5140c0d845041c222030404058440310b402c00b1504d00a000824030a000300200f1003401c1c2000f29010540e15a002ca143e4800510103041c0c59a0b420707003a081d0728080c09060010b0008440510910f400c00383d02c03825108043c45041d00500c94000844e1b001010030f415034112080851002940110084000d406400362a56419040c3e00701d1520360000300c0e04511003070046800030004e240c8203080c040c0648869044005d2040605c000ca9009002244a4090310700b850b88103000118071075007185070250400346a115031400c142d0061205010156003083e141c3c1e44682c0488011901001007001680c14046844490340c00401e100602c0040e100e001a842d4103e900c030790115a540284030b0011501c4114900035104051010084041c0c5544200c01600285000d0102c20900396a180033b107004450881d16200c01c064043e020308003828407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 898709901 1250 898708651 898708687
    0x3117010516030c0c151b020303150103020c0a0c0e01031103030a09090506030304121109090304180b06090303120f0603010b090105090916090b031203071209080d06061205090a0b0426030408 83
    0x51b00380000c1d070550504881011220201034400b60403d035000c90301003541d580c01c01002c0d1a00d80c000c41038001540d10790721000c0d0120007d00090700d000c403071420400428140003040381c818241075500c059580f410420321a000e41300160030180d151000340000f0901c00c00d440240146a0312030403655856002d404140040345200502c1043c0c0d94100348010403d0040c01e1800c1103034082c4407480052201c02d1304002a44d14006c6850b0035800d403002080350f80503106c0414441e8000c2c000d542180f211a5202c0c1c00309802da9035246101500a8100001003005042c0507254540000f203440c207440708480c83e59160035810190780e00c00c3c04999256000c001e081c4c00e0a004140c4d4180d0382d600502e00d07516000038003030700e4440f030002c407210b166a50b10410401e01120744241d074050403080d42e040c00010765030300000744001c44050440b4405803404000c204806000200350b03604c207500c0006920b031070b501e50f15840703150202903204158020454110089040c0100015442940310f4800c943d207070301c0000c000044e081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 898711151 1250 898709901 898709951
    0x10801060b030105030d03020c0a080a02030315060405030c0f0301023903030114120a0506010609031407030317090a020904140f0c0f063117010516030c0c15 69
    0x9070400061140b0f40300480c1c9585030160f5070801694440304060440d14200fa000b01c0580307180c0d00130400000d4580e000c0700541c05a4003c04403d01c1c8501e4100802080340300328802c3c80c0d4140d2040c004059641402005403219001c000d0006041c654206402010a080c0c540d03444418036803a0125400040381c0300841040c090080f006504544c1465030b0307010501d03006030741c0c43d1044201400c0d507400d020f070801150b05055846001e03035100d96500c050242084030b040c00101c1c0c10046003002c0c03d03403804000810104030382d05642c510f42c01400d83c0c03961640e5088041e010003000d005020301900581c0307840078881d014034400c10001c044034900c5418141051600000b04480350000b8042c400259221000400000000c6401541d24100c0c000400010709514907600721241a09000076400102c01143ca011079891906c440a03902d05c1c01c02c400c0c202c031000ca84403c15038091428941783c2511079885005002101d0400b180a26255202d2501c0c80c10051040000c05840c0c428400c400401928454024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 898712401 1250 898711151 898711169
    0xd0c092d09030c020127090c12020c071e1a1b240a09050105010f14010c0506040816081b0d0e01080f100e130204060b09010c0f0c150801080106 63
    0x154507903607001002e425100340e029040000c94150300300012000c0c001e184c0000c1ea8103206000c51940e6951004c05050321032201c00116003c00c400d0300d038410b1140202d84102d03a0300400b4207403d50500f100d404802450084c0c045840001c5400400ea022002c5400e02c03401d00d4011015407145a81d0002e0003004000c9a99400c0940011403010350680389407140000c84283c40c0d107641102d070780c1c2d1034031840184140c0c034014100f9800c2800004001805480140035104000c1d6003c4a114400c8015a002c13606610010101d501c0703a000a00498443d174003800000c41400c8441c804128035449542a54101c0350619618143c070341144158003804010b900e0541d4814100b00c1156048000082c1c00c10388000c1c0101c08004074240025401a030342c1c40c0c0040681249844801c0c1030400d0441030084000003241240181d240a50100c0c0780d014030303010388a04420513900c10740c042505964181100810315400c407540c40d42c5d0400890652910b03416007449000c950740e42c005642c900ba0409081d512154000500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 898713651 1250 898712401 898712411
    0x2120c1009150807050c0a0f020307080a120804020a1a0315150a030207020a05030106030c0303020f03031003060905010e12120f01061b110a0b0a030c09080c0d0c092d 73
    0x16103600102424402d000d030309110f00307640c0da02c00040c0d0711485400400c000364000c072440c0c1c03000c1000f110260313014240260203ca000c6901c844d140703551050014000741c00025000d4000320030600c121000342d800341c40030700401a52982c03a400900c41402006582c82e01c080d001c002c01a800411101c040c8460350110f69583d40c500804e48002031502c00d501300d110405400040032815505c5104d410001014041d0082240719900c0c1001c10000850340001c80050050720460a640240001503901519420019901d1a4036641ea448010000c6040841e032a5480b4980008145020701c0202c04000400c50840d6840d1030740c4811405840d0018001a0036040d83d00040c171240f03502c103078134500300307000081d5501c0780c5240b84c213100b035a186000800c20750248280101058164070a005007240e540d403a102406504000c02040d40d51040700e0040d141c556022904406603032500481c850540ca0245140e01480354030303061000280c41ea8507141c040308103000860f00c400e200d01e601c20244031140b410b00c1001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 898714901 1250 898713651 898713659
    0x109081215010e0f010509032d0d09060c2603060406060201050c03070c080d0509011d0c0d02101403132d020d08040905090703140c060f0f0702120c1009 67
    0x400d800c0180328013516140c004a0f2490340500119a92004010103c1e221342191143c6600c20401d032200d10704a0800fa1106404880c84c0060a0010080c264541034401820300504070b40040d0740c0003048c0c5100842d2400260004070481c3c01202c40c112000304541d0764034112003448156411607001c2c0e0110780c9040100301d2280ba5140680f90454590f00c0d20450b4880d8030709241c0454010140200e51540c43c0c4018890000700551208a000d5003c01c4504003002c103240ea4140c98007462181c9682150004c141240145080d44684a2424241c204403910b10010000e07600301d40c100300ca065010f4451192800c09000039100c0004030100c518080c0012000d82c0c1e0340d08030b58004d02c0e010003402182100c07030510820441c0c00945010b05640007080015141c41c0000740e40d02c542920050380c0007003000b0b030f600040f13400c081a504c1c04928046d06051805c0d05020140d180e07580000a1100034260900460700180e4889030707406020b140b802c0003070202c00c03042d50810a0f1001c4844452081c80a0040104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 898716151 1250 898714901 898714907
    0x30e1e101404050d02011808010b0910030237030b06032107080c07031505040b01050901060e060318060c040305010605062802010b130608060f040507120f05010908121501 75
    0xb90540b0310588045414444a10050702c0c00c103203010b5100299411900003241030901580410002c1408807102840d540310401250112000d40c080650031103583c1048440410301007083c10f0701480e000400100d05000145034009699070fa4108498220402c0b0502c0f1440c03908101280080705504584590091240502502071007071200040819071f000c01e00034120380003481070000954107d54011a60a450040607000700f000310303007c88803402d0850020400d400e2103159603059075420340f250b9100700c448404222054000030921181001250505035a84030140011402880c602c42c00d0383c1c44504600c0c2007401d4665542015008903c24845400c680245600a155015541d1090816408580c80807030140a0714580d40340c12a0503103080c00f8400c00c3c2c591103602140c480e01c00b0740e415910b030010007540c601070544000e400350388062070510102c200740b002c00c0380c0d8602c904801004025113a44c1c0e9400d507040c000d025905030714041529a644841444e50303680c0028042100c80d28404150000b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 898717401 1250 898716151 898716157
    0xe101110060e040210050f0d0e1c05180604030206040303020109031709030904091416050f0904083c03040b06060910030b0103150803092704060504030e1e1014 70
    0x1902c10505c4202024059024034125030f000280c8124440e5500c210903400409402c0203645c1e840c1902c60354403c3d00c8490740f00708000000342d41c03a550703851a00caa10f00c001c2038881c0640c44d050f648444100400401a640c01000f0001075110360004072345000607040182101d0740411800c14041c0c900000c0050b01000070045034100102250001240e05407801c00c800390203190100d080d0030340703d10b8001032100700b000c2203c0c47c12640c003100c5003080c4a6007402031105112090724024600710052002100003409104001a5020901c000c2c1c0c1c45240070001084611030012010484600b000041c07200380300191009030b504c03620076201c69241c103a000303002c9140c0c5c0c000100100c04041c0c0d0b82492124907846600200501c0c40c4a00d0000011901d540c000703600d940c050752841e0710414104034141480c8051510700c41100c1d40d07019003804155100e80b50702000d002c00070822420400b916245000558500d40500d0b08181c040f121030240c0c0860806004241c1042c410b541c041c13104481c800e80e9094910011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 898718651 1250 898717401 898717403
    0x31410050d0309050405130c061b0609030e09070801030218010e06040f1b0914040b240d09120801060e030307060e03120117120403030906030b010e101110060e04 71
    0xc0501041c1d40c078103003180c69140542120384e1140c1040b043c0301c02549080340b41d03880e444c02141c446c0980c42e40c8000c151550188403646a441609118503240481c06d140e0048004034042d05140840500543c000784103400111004408510040c00610540c202040401c600c001da0f5105184554104004003810030b0000b418948602e4840a0b03030364100c0d4036a0000c080102003800032101e20354200c880600a1009809541000000b11138000003500c0c6c5402507080111015182c4d1800c20004103806071800c60f20411558071180400085204d42103510030000780364080d0300010355200301703004020503041041c5e204908010030308501d074103d270b40c010080701c262960009000425920101006045003e8843d4519034808624000038090380b800404a08031450b40d4161458594a003c00e1000c600030303404050000f81e0050400c3c840907005e07610985c200c5605042070701c403180f40c0300d00044814200070704500024000311104001610100484452144001000e001060a05d442c0500b89200148 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 898719901 1250 898718651 898718659
    0x212090f28151512030210090c06300e2103060d0f080a1e0f090303111f060f061d061614070e01090c0801050907031112060103141005 59
    0xd00044004656000c101e940f0702c03100c0705403181991a07078440d030018108030050b4050b014001c18600b1609852189811055001c0d8224506a0138145d0403070700c078508009110340700b40310140600c604410001103400e05204541e80032402100d031103212414655048500300e420310000b141c2a60320721070907080d03e500402c00c0c1c584014617807080c1004844c40700c00100292148100061040350749030300c04800310700f13440b428511910300d4032000c100b120541721404142c0c000400000c000d000082c0f041d8010f004070f144200851b0015616004680d07042c903c105a241c03901a42c400301005030780140f41002c4003c03c1e0340e00305414000d240c0c00300f0b0700c4807103a8405207c2c4a06400210480200c03021068000b4154001410502d07000110704125610034041c00b0f071038003001d208000080d160429008003402d0000c00c0c1d9507000703141d00c1c0000780405504007034582014192944488400803000c02c0103000304503040560304010b803e00c0c0c0b001400f02e8411020111811807140c0c1001002c41020300007030116a0152 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 898721151 1250 898719901 898719923
    0x9060f06071502090a0b190f170703090b01080c130905070e01030b0708010e0402030d0807050c03130504060834050603252f010212090f28 61
    0x240020800d01c50700a00401036055401005800410796004d0700001009690f6000c8441d00c40600c658240120f415003d03c1c40c0401165200b043d1040d1a846034120040c101401c5248040000e074140210407199035001998440c0c00f54180005061540d004020b42c0d0064247c4100c110042800264402540801d5545810f500c1c420801d040100100400015848402950316803900010b003d0040e2501d10004440000204160b17842c44100c81c0103d070300400030040203104c0380040ea911400100b4800903c2010300005841002c244020031a0b40e407968112100d0904050421080b10340b51340290303105a100024035090002800910401a8925a60341e074013215196a0958180203a4004581104012050041c1e00392245402040700700d461542c14122811800c2c1201c2001c20a00084080d54000d0004000c03504034100020036620100c002500d0100b030041c1717030034822006480ca409103500c56038034000d0301d400c1808060540c41c02f070146000350700c4000d5044944203032400c8029002503246 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 898722401 1250 898721151 898721179
    0xa050121081b030307021f3e0a0201020d0e030906030f18070b04150c02030c121005102402100c030209040501080105190207150b24070c0e060906 64
    0x48590b02c840da504070b03402c0380d98a103010715009481e0346010002014598000c0d592055108542c02100f082c000f442403000142601d00302100003034107405400d04000000c00c00c0036625841c0c84001418503c203039400141c1d50b10b032541d020504844150900d6055604144049205684c0da40100ca402160405124100d40c640204045100d009505640d605100c2c090f07002034850b02c054058002c0300c0c0d41507584040181ca00205903410021100000d41c5504040c00000c501e140004042c0f424030341c5003040f0b0340c10081d8007007160116403054501007142e80b00c0c0401044000c04801c4148038036281c5108100700d03090b01c100042d548181220318151800e840703d4080b602984285d0546980d00f030018414411942e440e040c140c001e100540c1c07140303040d6441e45074011181002d8000c9030b0342954815a0b8841030340c214805400104013401542e03610604c1008040e038605007c0c03401c8203644c03044c0ca282540c0c4644515041241040552060150b9500081085129034456509991020050383d05508415003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 898723651 1250 898722401 898722427
    0x60420010215100e0c030403090509070c14060429010303300614040209011403040c0f0305030409051302030a0b070917010e0f0a0c0612060f0e0a05012108 68
    0xa0070040d6815196803070403c903006800040e010216a94075001e21180d44440c094032543e40300480c1c01601090741440204480c0c00c040c10f51903400703c881d1801c03089480c030964919903100c451080c3c1c0e0b080c540c8004140018402c0070261092404402e1400c2d40444280c0c06094036046c40510010b4288008118005510030f02082404800c1d1400807241400b4807160b21900d00030040d5002d00522072080e9405122181031031304c215418180d05858203002c05401072484d09055000400c00c0300d21070b4460400251048064803801e0255119030f0103140c036241000d0703440080b507c0007000c0088050781c03c803200c00981c9010403a05034245d0840380301c0b21541d981910a617040450303940141146403c9030011000800103510820704125120f0903903070b03540c556072041d40c0d96440e502c00c0a03040d003044200c01c001c418010302450038807903011480400c41998561002c1d03445d00d9030b50b1201000350340074806c00408401501c61103001d00b4199414941d000c0150b040e500c9244840440240340480c000707001003424030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 898724901 1250 898723651 898723663
    0x3060e01091401050403170c120c04030f15050a0902060904020901030e0f0703030809060702031210030206030a09060b0d031b08070c030f150b0102030901030209010e03010c030605030f0604200102 86
    0xa00940c0038815104a010b082e40280021142a400148203441041d060826040c4540c0185105003a550038680c4036210200441000743c00c2c0c2079014400c00000000038010000c6410107400317030210781000000a1500801d4841c000e11000400340b5050000005968bc041621a10002540d00581781c00441005030700408401840e0a51486480c0644032500360000b40c2502340c9200769694603490b11500705156481e001961300c41c015820a016802a041c4c2d0401c2d4a40d0003184003d150701400d60325000b082169200352421503804d903e440c044030038443c1c1c90080840485064500c00303940d45954800502070304100c411464944081e41041007030246103402d40d54400d420100c140360207a03492500b070780003407881081101d00ca400f00302c107e00643c1c607074820082607040680207946095400d000440080d4003000b00a814040307260740300180d03903d0912940e40112119100040d085090078205403030043d0803a400d140c55482003040000040300c00511101e00d194040c0e0454800740b8400050307003011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 898726151 1250 898724901 898724903
    0x210050d0b0a0306020c0705010e0a09150e070305010501110c090720060114121605090406021c0902130204062c100503040312060e270a06020d05090c0a03060e0109 72
    0x11000b2800401882081e500900714184010b0841e940c6aa4410040d212058598501544103103050000c0009081c2e6422030071401c1415452544560341302c038180004801c064034241c0000ba640da00522095800c48200c40305c2c03444043c0244046d00310000000e82055004221000700400380248105a8005c4d401e00082c1c8050001594625070b1900c800c1403641600c2090584210795040b2105c183c11404102d00f5842e07491b058008608504000611161081c05481260b01c03030380c200040500c903c0042d0f500d07960000c401c030022909100c035004101004031010400700e4903d104100800c8940d4004540d003521072400403c0e040400801107440c0100b6440b00380c45900203106c04501640f40382c0c80b00055125070b200e92112240982c07a40c5002048485502601e0a110384841c0030901e6000c590900407484501c0c10400940d8101000b110390812a01c194110384107500460368514032100e60194680c0103c4c03080c001c0c210300381100d000540b0000240f00281c8050350f11280e100aa02c0290003040c01d00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 898727401 1250 898726151 898726159
    0x60607240209040f0207111f11150a090b0109061409060a0807030506044116080309270103020105070804090903110c0a0305031b07030f240501030210050d0b 69
    0x701a910703803010081e52111808441c80000b14035011010300d0035081080b00405100300c0188089056001501ca01149005104162080000c11005034015482b5070307210b5450a0f0b030114144003075141c040780403041a003200368442e041c91000d001e500c24803268400021022546508180c6070300c000310301c40642d940c0040c5094001d051022050006c0014445d00070785c410b400070685507581c680500c0400c1c0580c0025541c0c1c4e240381007007070700c44d004010303802c0e0031404614241c49a241c2e4280e403200f6068196480654542c001048407095031401c49200c444070f41e090001002000c140c15411205030340e050000038140103012034464280304031182600c0c05000607010402580c003460030040d0202c0c5441072410b00c588104602210542803000c3c0100c210b070340c010011030520b00e054104000d4007242400c00d00d810700c19000c2c0080414031114440109901500f88290030b03050a804020b50340c100c080d040009542443c0c010070040c0c4031161030743c4000b03d0901d895510f41640d1300010000e03103441c4600e5540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 898728651 1250 898727401 898727411
    0xf050903030408010219020318040209040e01050f09100504051c0519200312010b1c090812060a06050403080f040b0c1f090312090203030c03030a0c0806060724020904 73
    0x303e8805500905c204c0401c0d403400c01c0d00003003400701243e4030b109100e00080c50803041d5003401c0342820150040c00306000000c0c000305044000000d140c5c21a20111401005200d410050200d441402c1c081620503d016040521041c40d0076120280d4805000031030003100000c3d0300e80500030922070015200c1114800b060b0143c2c080100100410040c19615422025201c11610114a40001040b0341d600340c4a188403001c3c0f070b868400ca4045642142001c0125131190903820f80c03c2200a01c12019410700c5a80c0c05519503039510a81d03913071881c008203204d0017070f0703c011800d100b202c0c0c106064500302c9920880c03e0341d840000000544280c041c07031340a480d40c034001141481c1100b4000c2408203900201c0b40401d00e0f80492a921041540c040640250108002403001024100c1ca500103984490002d03040f03070301c0c00310309414880c1395900840d1a603159a55801d0300c811100d80c0800915045175088800c241428015103c0041d00f82408002c4281004009100004035010340c0580e14110001041003007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 898729901 1250 898728651 898728659
    0x2130e070b16050d020f06010f0e070f09120804090f0c0801140d060912030e01150314010605150315040902010516110a2d060e010804081e0a08071706010f0509030304 73
    0x7590741054586020b86e40164070011980c81c007050403a00c1114080c1d007640b071140d15151030507103515518000b501e0820200001c042900101906401303031030f600c914003450f45c407454018034a0450340d200260005190801c7d03044110380e41d0200c2c51034107403028001601001c40c8284000380303039550811001400c45082910f0300701407203d4010880ad4001d50b40e1070500550b617561454038201c44101090800d0011902e0041c80401c80000789000c1c441820f0700002030103615074001840c4003001c1c200010004900200304041001460b9600800810a80781804054050350000e000d40c005d00400d0000100345051180c28820310340c20000303070070304007509030803010b501da45000003a070b460650032040000200244800b41d041600351201110411340d201500c04601c600110740845024106486040080c0038a0040c143e21101510100b4401e1070603642d1501901d202500500c1e00900381c000b400718040300a82ca464422144950000c000d1902c04004078610034155010b0140603040c0d0b0301440042000300e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 898731151 1250 898729901 898729903
    0xb0f09130b0c07060b09070f0507021203032a041215020910050901020f06010f06030c210b040608030703080a0e030c0f1510030302030d020f0415020a02130e070b16050d02 75
    0x10203024000c00c0c05210007800e10b4240706c2c01043c03c0d107020300016500360b0700e48041c91017030780605090380c802080001a4040707001210314640064950300c0c1c110b0359950001c44a5401d440b0001c1c1c011030b04644060038a4a03103400c166201c440f01002600d90780e1502c00343d04401615904807400d03c400200000d441d00c0303204e00300616940051040230f02520a40800000ca1140096446e04031800e03101c41403001410440124060200714000350140050300181303200c1e02904400e043e082c000100340014140110707908010540d0342943c0a0000e6800801180300400e81c001741c06980312003210b5010a01c1140041e60600d03611501c1d031081a60b01405090b1694030001192980081d024900070b00b940741c0307032122010f503c2e40a0740f00040c05030b031040041d400030206980180c05002c040c40400c0381001d80e83d04100340d031000c1d800080c000580000e2100000c5103040c99150720300c004c13030003810011111305078000d5541e0200b500901a450101094040104c280040e4081714254801e007600d800d001000790107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 898732401 1250 898731151 898731157
    0x620190b090a02060f0a18142103310b030118111801030902092719030509040902060408031201051009030308150306010f080705040b0f09130b0c 64
    0x46a4030420400414403000d0300141000100e0340041c9000d151200c0c03032071410146d0b0301c415000000e0001c00c61054081d0402d07074244400800d0540c0c0b031050241e204000300a0b0306190025000101110114042c80c1d900c000415509a10400000542c52420369008080c031460301d00250f4012068a24011441d400389401950489400116200f588104442c0b010291052032004c14103511003400b100d080a000d04100b130881240605001a0340032254010410740c140440c2c0640c0c1080b000300e588400c3c020700a0710000303020071250180081c018517102c03001911545241c01342c100702e40460000203550366540018200d42e8000d0404c2c0c1c0c1c031039807503014503266040803002c0e4031500f1540c000082d03541068000c06452030100d90300c0029560550350207480425020701a02000004070f2010301d816141008800d02a04101c3d090145042c0340c100c41500d80141500114001c9040481d6510b40307494404005410381c4044801015540d1000141200c42d614000086c01c1011804203022028043c0401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 898733651 1250 898732401 898732403
    0xd080c010c030608010e0c0114190f0e010c030e040207150c03140c0f12190e010b0301060b1204140a210e0105030622111305030c090c0301062019 64
    0x2c1441030070ba81e203140c0307801c0301c0c007808030981c0f45c0c3c0140341981e00310340c4a0560322031400c11014410b07080c20400418a0912644010404082498034000502c05600001d40c1c105104003443c01004202280e64018036a0040a4403075002d2500030820390708100f28116103d610000c111020052081c6140001b00688492140280488511000300f20050000030480f1010320145503c80d1810300464400a03480c40028400c00b0380b07105d025071001e2101ca490050343d4000685200120b0500050400c05007191016070011201500030031541c000c032811540382d030342e104e5002211003511a1149070103e08000742004000c00345948801401490440c0c000d211914004540d0764407511101c5a0041d00c3d14441038441d154001c0b01d0303002d8000e001c261104038200c800e40c4180702051110800001912903046508190240c9207170000601c66410200708200465401300c40810103410544248882d030310041c0031f400e0800c0f50fa144816000504c0102c1e00d00391104e003004482815291901c0d01d50306180c5444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 898734901 1250 898733651 898733657
    0x60504411617100b1818180307050c0613150f090b03070c2004020d050417070f06090c050619020705101403040f020901030803040b0c04061d0d080c010c 67
    0x3a1549115411080d188688410301d003110342d1034145400c9126542004a05611003044000004c010780c030340c1e280c50403070048442c208850f5400c028851f00c500c0c98124116450a6000740a11300210703900141030120014107862142c0e4071440300000480b6008180c000510f084843e601d24580c0c42e03400700a003180440c4503510070380343d60f89403101c40180e0f01c815521030340050010301c0b003100483c801c0f066401b49810024003012200c1001404034003641c004e465600c1c506541d84080005000403c3c400480e440c160b20301442c5400c0151f6601c0512a009400241c0f10070b0303480913054100306c94030072200054900200460b8540103d50f00c0000080300f41074202e0300600607a400020303142406243c90030603050a44941e00044179400d20300f0750b541c00062003a54031407001d82c104030240c0c44044045010714000c0ca0056524980303414842140c4501500002c81440208000c121180c0d018604480c0b10202c80d440c40c0c103d6a14a000030041900c0340000760039010000b40e0082207071030550182d0000d0126403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 898736151 1250 898734901 898734917
    0x30c03020c0904080a20070f0e0901092406030b1303170705180105040b0d0204030302061018050c07061b02120c120c07080109050307060605044116 65
    0x280309003150b043d0780c0100454030500201c10710394010540c1d201c21400d040d4400d441c014602800d10b20b8044141c0c80b240031802d180c0814410822044240d0b640004810300030301100d41f481d40ca4510000040040f1000d84510751012510350302140c0182c40256044012101c3c10b09001040c4ca11810002c14100c02060381065601c411640e41c4510b1403003030130703581c5540d81001000d901041c2c0049900c04403a0402c1410840403485070040d174060174411440c1140107071500e003580340281c9131900280440c091000000d00802c40815080480113414560032000700e00e07510307178500c82207a6010340c80d4000c042c2d90402000750540d84515a02c8240c010302075084a00c4280040c4c04140144901050086180c005840c07034004421050001c00c1c44820520444200650301d882007421078201c84422141900002200400e02405008a201a01c002c80c0c0c20400b0300c40750000d44054800780540f41e5980741c0c101041d00c4034214007509443c803c49a00307040500e14a030644001c0941c8030103065442c00b042e484 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 898737401 1250 898736151 898736173
    0xf04150e10030515090603070b040803040303020c1c0204021c0515012c0f0d0210021606112a0607060506040e0a02090c07050115090c02010e0127020d0204020403030c0302 75
    0x81c0a074900401a41e213000022480b28014000e04200081625030148034042c1e0009058103214028001401c0020203107894a00b10314000703040a04c184c03101031143c071054003480b00f910940c0e40c100e1420307617040700c0040e900c094603882403400e10a1003c4e4030600920700340400c0b10100415101c0c5402e064243c1e01c50841790300c1000007000000c1ca040c3c405015400740c5140b6040c6040c0036a42086100004080311200000340e400110054000e0501100503041503220099444601505201901c15810710101004442c0d803041d0b0385041c905c2c031850f4070742c0c0e5050349411b00304a0590114403503100504061b64900b00b900b04000600400c0ea0300b00c1c010f5140503e00e00400c80045183e85107140c1c0100b84a234079482d112501000c5410507002554195a520115000c207141180d03200014142c0c1500412000005440a0308503440000740e803920343d0401410288056014148051180c0f070001c0d04124030941c0c1c0003044041d00603120003504644002804810b1581100c00b103103c95209500315880310040e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 898738651 1250 898737401 898737407
    0x5071e0e030c030d0903060b0f060a26040807030e0d0c09020c1b031c0509040510030210020f100908090307060c0c0b16060902131a0310060f06050f04150e10 69
    0x2210011380c0014240040a00c00100750360441c0c19003c900419900000c096140021065445070380c5801c0810520580d0f00070300210340c03009607003112091031211024a440c0c2c9401d0a01c1c41646802002c00010306a8102c15070354001031031740c40070f4118840e2464161502c8554009500000c02130f01c662003203032001116000f00d08812241c2d84805400303801d00e181c405464941481c51a2035420900c43e05101c60303402c80c1c40b0b0748281441081b450a224018901d10300501252043d08003036074085400610140c3d8000c2c00c00941001c0c0c0001490380051003044070b0510070118001c2d80c00f640c2d40360140b0302000070300c04d40c0003010080b08c5000f001031012041d80c6041048091041102042c0d244000f80400d9001c500b1903800398100c0d5001428011900b0384100c100c0c0c0460b205504600035084025104007400d00301086010620b1540040411079a070030005d021546103c2841240100000050035295081119003560005d003242b04000303803483c1250341c028120204402640740036140050b2904441c0c0c1c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 898739901 1250 898738651 898738663
    0x4150e010e07200f070b210114062119320c46020606010507230703200121140901020c150f04030c170a08100602150a05071e0e030c03 59
    0xb4610032100400242038140403240c0c009041d00039030000c00011031540340b011880c48600c1207103166000c00c1d1011039201e11600b15001c0384c00d204a8003800c0034412490318080d0711000301e500030337071018000d0329078541480403050700c6200c0c055050300200300c0100e6000702080e04241d0115025100311248084040c0404400c00c0c56000c040b40181d03c58804140954090401010014091380b41c941c1412005084910a401d4811080724668403922040060020b0440060340c0d820602d600c0c25803542020000030700c40c600e44600107c11201030080c00111055590124101d542200c080501034a05204200c0c001d41140e11010308a00480b8080c4104120b0040b2880c0710b02600c042640551300c494504035095905150119007442240349025224800800a05440c80c00342d81c40c4086403400003544140741a40e07034012000d44d030026030310090b02d50a20600c5944511240c40c00155607654601c221070051086001c100b41101d020022000d455004040720a251010b40481d408501d1b02801d0660f515 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 898741007 1106 898739901 898739909
    0x304030b150a060e131125020d0b04030810030321060b0f070311160303050d230a0507091a0a020a0204150e010e07200f070b2101 57
    0x1c41c11950300031481d100544c003403100d81c0000d10060031b82d02900401c0300390400440250380102081030401c001c001c0c0c004000d86081d41441c201540720500540d42540000d030203e0000d6480a588007070202160303031594030030b20403404202a40c900b02c118041c0d0306003100c4d1281c80004401ca640c0c000b40c80e10a001d06041e6580d4840c42c503020740b02c8000c64031410300035080f510001004050907131607501200e4060a01c10b87d03c06003590610020106d03001c00076446000b41e0005440d0302821940c03e8030503c01401c0030001601d0702c0c00103a6107070f0000c0c030840ca05000d4994440103822400c102030105c00c0070500458105020300d030b0020b025103003c5042107a080003041010041b0341400e01d03689004003030307409410702ea40c142840001c01c02401c660402c9139a01a008142403c03182c10091020140019825541d034261158424900d65104c1024000e50780040400d90700d4503400c50020324103c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 898561151 898741007 := by
  have h0 := BRFrame.cov_init 898561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 898561151 ≤ n) (h2 : n < 898741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
