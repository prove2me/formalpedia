-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4797
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:45:44.852974+00:00
-- url     : https://prove2.me/submissions/bd6a6708-b101-43f0-a2b1-3dba40456cfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 862589928 ≤ n < 862769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 862591178 1250 862589928 862589951
    0x705120a0b010e0f06030711151609080d0f08190f02090f0d1e020d05032805070f030f050409021b0123040201050318030d141806010509070c0f06 64
    0x40c001445403681c0950740001c982d012175501c81003580d91107400351400c440c2c048488401076207098004079124a40510000a102c082a03462545403424805602c402e02d01903503030b400032541c0308010104440094001e00c0384a90051144154540006400298421901940e52800100c0d4503440d83c07141060390000d20003440b41041c0400010141046030594421022629840c1c01345010600e0311502d84590b003041021980c035480c0c02d008150b0002d048a8546040f1034003201400c1501800c2c108861075031200d6042240301b2421146801c3e84801c80740c25500c5640e90540e42c0e01c140e5500c40701032203028800070404050034405031540b88411148091a419041040341c00c598a0151044056802400481da002086072a09801c60307828030f81036a0340c3d66103080e0b80e13072900000c1d4201e400f035010000d850500c0007115000000031810040650205403105400d4507000e9416908101ca150051001000705142102c0c07250380c0300b074590504901890300360350b4090042050749000c0340c8041d51500c60902 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 862592428 1250 862591178 862591187
    0xc061b06091e0d1b1703010f081b01020c0108040302240f010e1b0705031e0702012a02010305040f0203030712081005060d18052d07120b0705120a0b01 66
    0x8100244405400c040e004003100400310341c01d03108420b595410290200c1c040000d0206103103917000382c104c03515442c0d503104d8030b02d2401c0720031511802c0303910710070055800404142e5079624120382405800520038040c01e10015105100010304c01c0e41075016210020465045110f4916561101c0607490300301c80c6050a000c0d000e200e010703004107031074100210030800c44000700300040903494011903141d034a42801e880d11916503c9800c0c5e04400302c0c02a5031080380c0005101020307122080c401d80f80c010008454010301c0141e804000007000c9003001c0c41c0c51400c0554000d50080350858026505030070a0105a00030030f2071070f03000400480b5403042d1015031564441e8400340c8141c105041d6600d5001541ca8030307001072a00d001d02c000668040b50389100c03020311081507045c501c420903401300a0390041840700b107461011010007a04c40c2c0315150620240c0c1030002e00851000282e40c69507041c207400c0c00807074540c0c0411000081020050001c10405486100300a01205118168030b0f8404030780d03010440001130 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 862593678 1250 862592428 862592473
    0xe01090606140612040618080403050d0e06030a1a040903111501080a0b060d1502040623040308090303071e0314070c060e0f04020f040302041404050c061b0609 70
    0x100248900d42c1e004280f95a550200d51110241960216441e20380b401d060340240500b184c101c00214030180048100162a0301600842c1c0c0241c05440701d0305a6003074107499449501e4201c69100c8401c100040c201c40303081d48950814203000d111100b20260880105049445503032054000c14040d8003a0908481c04011000300000825003003480e40d4501604030b035944080c07107001002e040c41000003030360b55150450769041c043d800144880b9540143d0394564002d60242c010400002d00504c050700c010410090800c81103001035100c6c6180500d91f4071011010307001101c1d03081d4180000c000d940d000c105104403e0309030701514529a41084002c0c0b401130104042d910031101c0d01c403400d1008002086200c02b00340115041030038a0012070913246d002580c0d1524544156903ca07101150091701100c04602400c1a2032007510100303c00325003000c1550705040119402081d550107000940c2103401e109010b01556403850407140c0c000076007041400e003896070427034a400c0d442d0f02c400f1110304090049100031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 862594928 1250 862593678 862593689
    0x20f04081608122812050a0c020705060c0114040813090e0a020922050c1009050d1b0902070515060f0a121403040602160605040501050a0e130e01090606 67
    0x81101d1a02c00070300d4480c440c100400c1e815030b4011540c0c41e003a0f0076408074142562401140464561040703000030700381c0d896049500a602c0d04d444000340f0740d503056100300307810056941c0050a546203131008000290f4480740750001e840d520340014102c500c400e010480d0046114040d459220004810b00c10088040e5a01c61940982020381c80c100c0c848000c07540c020956016240002540c0d82c43c0f40064800d8071001000407290140c040d0081030260108080d00041011514060310001c2100c0884006c81140501c5920170441d629401c0090700c1150f1000170401821040400140d40d640c40e28102d03049188140c46580080e060425080c4240700c1040d40182d044030304480182882d0301250581003540103150320480b440d0b4a403014000c8654a00309203e0004c01209da507a038452600039140e0301d212550800d80c0d40700c8440400c100d0301820540e8103940041c2e40362400d000441c001145c9031350401c04050341050210810038041045c6000359044205014000305142260f032908200f2a00990f100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 862596178 1250 862594928 862594963
    0x2010b01180509090a0b090309040608060f1603091a0f06011403241018061416061e20090306011502240106080a151a040306020f0408 59
    0x30702041041e441070341a108141d07544191640d903d030307403a0318001042d0400342c80c0343c03402c00810a401500000521221400b5070b0144642a42c840c48242c3e203c03030036200d500c0500420400684000c0c80c00e150040d0a6003e481c001c00c5010030303900c2d0031042c4c1d801c80031805490b4047ca4100030000d0b000d100d031250414802e00e88400042c1c42c040c8c80d14600d00004e002c03444044081e50036103000000001401042c240018489035000440d40000b40149c402d01007140c4803500e140d1400a415805102c007901400c54201d0407074508001c00044141030480121308441d082d50380c0048403800759156498081c4118000000140606034071000041d001b6039107078040e0303011010091109180c5001c00d84034116880180d0040b41046c0c1e0030410303820500c0719200c42d0141c2103d00e4407a0b0b03074000002401412620135451341c4240b911551030010030740d40e0f81810f1410020003414200448001031283c004030400040ba04d80c20b10b612980d4640503640040b2001da41c81130082001d0000c80003e00810b004003010000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 862597428 1250 862596178 862596197
    0x10311190f060f110a23010b12060703050f0403080a09020d051b12010204050102150408040e0408040e06100c120207081213080613060b04020d0509060a0f0c0203070215041e0602010b01 81
    0xc81c10800c441c4180c4541c0c81b5200700b8500c01030148250000c81107490010b048922001d04000e481d903940f041202c801000900f02408107106400d201303007d900981d0942c0d90240f1036075551481001030140400100c2c1c20200d003503000b0002c00c0041c031030072417001c21143e03404079040300010800c10201d00000740c4c0100c0d648104010019a81c00148000c10701650140c0c48003e0380d10750900f503515010b0380e440023902200000420080002030801001078401c412103850305c58403060180149986c00e800800e001c01e50b10b1008a020a4084a25507100709042c07040325045500c034289541031080c601c590b038000c400046a130394080d42c0da02d030301d9801400d4004010050307840e2255810030007403103003e0080e21441c0e480208440d2034640b6011642d490b5211007051109040502d9025924041250400c54851403d0034042d03c0030f156000b00041004070b64015800c000300360b000c000c03100031000760003505142d080100150140030241c032044141d03281060786c2c06003460000041d0035103684e008120304226280f030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 862598678 1250 862597428 862597433
    0x10120903120e0c0108010f23060403020a1e0b03040c053c010e03030f030105010518040c051812030405121504050f151b09120a1b0e010311190f060f110a 67
    0x110700c1c0c1180e165070340c44400c003041c7c5032340440d025200d00d41000e900710481d83ca0200700540d1072007100f50103c0e508804011a696140c0700782c00c190100b580c0060226143c0c8000300080e2a000c1c0560307200341c459400481e18002081804d000e0801c211a02041038101c80e00044419a00b080d508691018240c010b1858803031f0400d0801d203075100501685045c82400300b140b840c00300b00f8043d60400c3e007201034001c004d581000030003c0e00781e411222180e04110420300c01da40040c14012102c102941075071009608260812040025041040b401c0750f5461050891601d01d002c2c5003c0002d010b01c2c0104041c0c1003900703800e007840b400c1100c1036640d01003401c00902808140c00700e039401440148611034695481d07144505c005a4240c200c0d0916500c43e125482c1014180003408a4450744c00366000320101000c0c2d03441c0031140141d00f092002900c0e80344980141c40c142c0c00c1c00321100b903882040d001c1003040b40381c84102d144540e155030340280d070016a901902c031040c16080940c5114504101000b00400209603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 862599928 1250 862598678 862598699
    0x170c09040804261005060907110c0f040b0301021603140307020703030f1e2a1502030901020408030a05120601091410020f1e0c10120903120e0c0108010f 67
    0x284180c0d071107007964030f0f4015149104101410b0011003d002900c6881013900801c80280c0307010b403546403040710040c011442240c000c0030081030b4034002e040600360300320030242080001c0700c90496890b001502d4002d031141d00d80e23080c0f0040c40c449640c3c0c0c90440252250741802044400e0040600c28900000c205000700d503500060580c084a80c585041854400c1c1991b04440701003210422218001c89201d164902c02d8100d01c2140810207010700c9008020b415602010241600d0513001d85800149160300303030302c50300640007942d215502500140c80e10f0360355141d05103594411011140002d0001c41c82140e00248138003c00d1b0804006d00e0240c1c01c050a00243c030080012143d500b9124038001a40200821700a00c040341e54000c446090318081403114007000c0d01030a0303500c0d450030079000700c105103070451904003400d0002c0b154680d10040402aa100c0e070b0340051048120075424030030340380b00c81403840b000d501551003481e2640010305001d085010014203030030410b0f0418440b24003844010310451400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 862601178 1250 862599928 862599937
    0x180e041707030302090a1413110406050c0a08040303020d17061c150c09080709270809041e0c080105010f1d310608030f0a1206170c090408 61
    0x51000326910281480c0c103900900c2001d4a154100004004c0060800c2e1881e9003030012020907200014104840d4a8110884040304084420150180300900c0310b1072184020708010a100e00440358100b540d510780c4540d54000d079104400507408101c0592000c2c0e84145001070450710b803507182140d03081640000745003019408180300e0003402d0708801000c1c030200030380c0030400201054040244d0555806c000f4035812160140301c0082c41144d000090348081c0d4410315850b007104108034400c034404004614014000c1c05d030181c0e0031507410721045400c1d5445110f0042c1e2100114003003030710341d110b007181c00007034958082d030004c2030200701d000400090742c1100110031301d40d02e50319090f0a84800c0347d07a0714410307007412400305030850881c913040c0e00c5d1078850b1134041040140c07000c0c0c02d425541192200341d080d0784582c001d01c00c40d50002d202060f804034511000d42046041d6003400c20740700e20341a07000400c50b00642d03c01c080c0290f40134030750f1640d25410b01c41c5102c154800e0712400101e151544881005118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 862602428 1250 862601178 862601213
    0x7080c0f01050901050d2c0a020907080601020715030f06050303033114011d06010602030702010513051905040f02040e0c0904140411030705092502010e0d180e04 71
    0x2c1c001071a1403c0d038400d808403900c91074400c0c800c01581d0110418a5082c61141c0c4551034010342807414070b82005400600e0441050f030061041190355607a803021101100040e0015056200b00303440481c120140024500314203007207980002e40b0072115061038094071401e0f40024040c1e0020024000c4403120060588000155104042c3e61411143e4104100055009001d04010200104011060b03c190011407a000342d05518686071810302c580355448020038403030340003d6801004448015401030024219800c10074583c03c42280d5150082403c4074180410000c511600030000d1049241512541302c003042104021810300d41041041803c085010741000300b19180803030316103125a507941000c1403050041c84a07050600300b618081005070414040e551080c054070502091074100b0b940018850940000068801298040c060300740104005009045540b01c1c4512980090200f015030ba0140d4a90740c0d80c801440168240d040c10807660704400007503410710f4180710100e580324049124810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 862603678 1250 862602428 862602437
    0x50303060f0316080709111306030c0203070605151002060c0702010c050f0a0c0f050114070b040501060b0310081009020105300c040303021e1b01050903030d02030907080c0f01 77
    0x106a4001900d041d801145107034900003d110081001100440c00b841111a40e910500810550342042d00d0503004200d1910410000c4030000c00c10640b00350001007501c2c06500551345403034013517140c01c0c042e601c080350024a512070300c60f060151410300c0d00981513021402d101070282420800e5005000d44a000d4010381000a06060501805010304c0301e000c1030003441c1c0031a80b00070340b5840c0c00303152410544074010700402c1060000500d54019803444a00c00003400c0700d0f602d03100c10b071395a0108514000d40b003a5601d40d41c51801080ca40d511b00000c6014480c0c191134203a1107031500c2d071080e29100107204240001c5080c5606040143d80110982d0b0385c03014040c200307100000300071683d8011a9101040d0742e40090b05030081c4000c0c880d112004100b62070180d42070ba1b0500070104591003481103240da4040ba0359200105841501c921440000380407101407503c01d10341030244000918540201d078040750050f40c000103002e041041084010014403203040a4113418009000090000309074011050600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 862604928 1250 862603678 862603699
    0xc021e0604080102043b060607080c120d0e1c260a09060e150a02130e0c0d0b031204150504050d03020a050d0c0f02060a0e0d0506070e010302040305030306 68
    0x568490050341c01030000b40b40210f407665500c1980140030406503aa0a900d81002424851105070745445808120360514100e20a501c4410502c00b65a00548090300c203100705002c00000001d050000d46d080b180c001d10020380b101100f40d0484200d440300104110f49900c0303a150541503040340040864016081c1c01c005908801c0c40b02d281e102012008041240480b207030b0104801d1210301da1021040500a5000f04064402400c03410391306c0d4000f141c00403200001d140024012489500201313a034111420001010035520744001002c440155111601c401b001f01d515a041001c9110b0025459002c900078448032640d02e844500a110300e024241c00c80c5402d0030880c0310f1307a010340200c0b002000c020f409905031440d6820025194060400d00726054000c00440c541468415030008905a800603540c1403030f01100d0b8204240f5600c10b5141d4401d00c00c40c28010500e0756100261031200174000c9010b00315510300310b13200a140e00064000b040c107140c0f0500090005c19400800d8940c400f005a9118141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 862606178 1250 862604928 862604989
    0x50a080f0c0a0804030303110a0e0d1e032c090f0a09210e04060b04050d05071d010e090303070801050d170c010204091b230403120807020d0c02 63
    0x240310700305190145105250084080040c0c0600500c01c40f4020f5808120749900d141110300706100b13000c02c1c0d100060000120f01c00c6444c210310058000c07849401c448a020003400300c485508840800150003140300104100b400158007112201c2060207003171011503c0042c1c80010710b40c4440940890f094070400c030700240c0c8141c0c0561098280c00d81042a030b4505815084030602601c04880c10100001c08801910b441420b1501601b402c2c1c40e214480300b400c041c108014003604480761a41a542845481d400280003014144009064507154031250f0b80c035030625000d48002d0341c001c0c0031251103510170001c210215a00c12903d078151481140c0700c071001c0c4451b060000c1803684500b03151008220010f02c4121510f0f05500030421900000340501880d055000b48030f44016800202d4004039142070803000341c040d920002417000035588070305581010746a44801402c000b614841e0307000700e0120000d00010540400100c2c04295151070004000403ca5010410200d00345004800120100401551 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 862607428 1250 862606178 862606207
    0xa2d060513050f03150411152104020609060706020f0a050717090901030618050114060a0f03080d0b01021c020c0f1f050a05160609140f030406080a060e0a0501030b0c07050a08 77
    0x6907147c004101e511000007a41c40800c150b8402005014039940e40c20800c0a100b00010b4001d04c100c0e002030000381009400000d00040344c2c00a0000c4400c950300f00445030010003070002511420b200e568416807501380c07902e03101210454101e055040700c0fa080c402c010180d607903400d0060560b0b40c001c20100c0e01031003c1400d07003040c41c100324004000f94203201d00c50311071142c07140c0c0641c4107440448102042903907494a404003030000c1d000c060320b516410004c010306c20b407072a04150712104e010b20440340503407000703096580503482e40c00100e80160480900000d0074980404a94120841252000b60180036070802e00410700780701c0c02210a0000100b1a4280c1d140030304161a40c04003010003107a6a5082441e00c000200034418040341d841e0100d80d09004400d000240400c405820b5600071403900d81482800e84aa01000309411441c0382c4500c40481c0c55a425400b440c01118005804100c07035040d840c003038500400c02448044a020309201500c04a800043c00d058550340000300141d07100b468411103907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 862608678 1250 862607428 862607453
    0x20609121506030606100503061e060c070905102402160b04050406081c080907030606030308060907050a05120a0603050f0a050f0303060a2d060513050f031504 70
    0x40341802101501c0140c01159203035544122011010744003103546105c1085202a469203509002030342c10320000c0d0f02070404404144501280c00020000f02514034001881c40d8400000800150003d213002c0041e00401d01501e5004248111042886070400090f0441c4c40050709082c0c0b001706490104c1c8060318001c3c461100340b45443d14205040b0340c0c9400d55401aa4454803a080c052468000000340028005c01d1459200380484143d981068503e0011940c1d0351024001c0c0c0c005024600c0d000000600e40c0c495031009500c20380b5150342074a0820104a0100d500a1404080c070404011800300250302400f11401c08004015000160721b524422400401042e0402800ba1003a041d500040e4040001d0810319584120111146903003842d100700d45902050707444980000e05c1e85024003054509014081c2c2e040740b003c0400d518901181428000004103a00103c082080050101c4407620001e003000d000e4002580c8911400c541140400c0c3e6644c00381401e01c950484002c042002c0060085504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 862609928 1250 862608678 862608709
    0x718080d0914040b010e06070309120606030302010c171611030f04030c0b0405090a050901020c150105010f030e06010905100306090305121e010b09030c280807080a020609 75
    0x8a002991400d4007802006042c016654064000c01c10008035182c54000c20340e82d01010703550350b103d500766081480084e030041c103021428488001d4020445111015841248500401020035400c2c0703141000390868030400d501404122a200b681050409400609500120b00903003115400e0b800c5d007021101e888002204040b00e000000e048640f1013040c00240003503a0098070800026695418850040d228a1052a0700000c1440c00210030000c0c42d80080e03808138030301001525180342c1e280ea00e42000c00d550104400400740c000184030f00d591068030502c480d00b41e42030030060b0460105810380c1c1d13031605206040c441c680301c0d40002c00e0440c00508043c025907002c80107108203106417901501700e03008410fa900d001590b1400050060b200e9284105c4000042010840140d007800480015a400b000403180c1500c00c0c9440e4030038984611001d194810b0480c03032050b090802c0320b0000084040660b10507640e69112100a00c980324010400000c0c0a604546240d0741d40b2440d00415182080700078132 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 862611178 1250 862609928 862609933
    0x2150a0e0a1a060603041109040204060308030f070e041a0d0c0e010603140601050a0806011d1003060e0a02090a060e031e0109140d0507060e010908031305061e071808 73
    0x400c010001d518208400d040904030480d0360310340c3c6580074030110340070072a00981200d440300240502420a400030640090003d080803c1681c0c0300d4440c48a0750b03005643d80d0600001d00e0040040083d840545407110310700455040c4805401e40f401d03031841c2041001594846c80389040b00720104665a42440000c2c0181c40b0840d086603907030840a00204a40110008413821f968000345503036106804980005000d601c540ca0301d5190742d0011580c0d16640541c1c01600c4040f01d00d420300380d036256096403010050580e07000c80d285040c0103151004a001a000c100c05900500c0301920981d11261044166481071a03da045d00000d58002032410541c2c4148224041c242c011842e1001819007210000d13074001d0482080030403d5401243c0e44028002c0208005042070083c100010f8543c1c000040503a042400450031030102d0315007200540c0180c8403a007650304840f070800c01300b00e03044c0b00040d071040000c0c242e410bc00c88020b0421034405001000c000801c0408001080c16a0410400340d0240c0440001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 862612428 1250 862611178 862611193
    0x2090c090d0b01030506131227090603030e0f100c05010b10030509061006050d0c090b0c0303061905030316022e11010e07120213050a050103110102010c02150a0e 71
    0xa08908400b000e00042ea001d006030000540d21050110800d007030300380d00c5646c0010354079500b01c01320380e121540100720285607005a51140b040644075175090140040c04d00c00a8442c0c51032501034813900c030001d02d860180b20043d00750b50300c5a50b00116021685894207164600d0340003880c1840c0108541070811340e11400400001da050341c0e0540c401446070070864121036154664940e10b420b400038910a01000840400104170171682c3d80d04048003060590909000b1503440b5407180c0d101c0d13004000b6040d1705510100401900345450b1751200340503040006480115401d10021a40b40c2c815158140d8516402d80a84400c549901968181d2a1540d00c44070030440c40411070030234181d15070880c0100285c1500d10200c8204010b229118908400e000204502403030080407480140765038200742c0e4401003140c010705440c130301d034040d41c0d10911b0200d0b4002041c1d81940703020403615504c00b02a038110381c94504140182d50700021a15070f0340c0d40800c040030a43c0e958120340800740600c0103a000040c001c202 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 862613678 1250 862612428 862612433
    0xb130816020901090504110f060d09080310060f3e07060806060c3003070f1d09071409040e0a020a090903080a0e0304090e100b060a0c02090c090d 64
    0x32200540d4800c41d10401c1e40d980c2d502149003580d406a8002e461241108151841460103240050b500000523003250304107540742c881d480465a10072002c1e200c2c03410000807c500d0324040c0c80781c48c014248074141740040c000c082c10000c110030b80ca00126150000011000e47e00e08800b070310b040d8003107903180d801e4041c007012025002c0d0b2942890b100d07034004110310078003090140c40e0000c00e40b44099a038030000c14050f1071000b40710001605c0c0429820304401c03030348038201c51003020400552294805841d8003480141c3c441005092200e1b6001c1c00d02c508110300d252584aa84400e00c10703800908a240210f500c04490292240318441c441d01329510138681036000401860100f06500114001c54950300081c0d0b55409590030b486685100a000446010020768401081d03400908102a05400c5904081e04c50003400300319401c04540c00c140c1d0348200c681d48040a0203014070151090141d44040c02e101a0107400350020960440003880b40700f8940015450507503400c2a69803505008090410340b51450 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 862614928 1250 862613678 862613707
    0x5130209040c032018040e070f08010501261e16050a12031d0a0f080f0f030a1b02030303070309052406121f1b08090304030b1308 57
    0x909a0340c056401c02d031540441c54080d00c1031036866113403907904107010003144480780c0c203c0d48520300e07a004009503003241c40c0c00c40e2100d00c0b07104d2501040c6070003813542505289115607221060b601c07030b07243d07a03060000621003600741340342074949056100104004411808105420040c0600c2c8581d08016814034500b044030001551400701d16050a001100640701c00034000f404e1043d00607907a0381d44409090800003442008680c5488e0703024202c100c4003910040000740d0386001c1d540108842e414540007400007440c14440300705a010100000e0044000d5500c0746902da0184d000c4807000e00100d540742c010314504828001c400c981e80101500d603a841c000c10090000c0603055000c0d10f0620821889a0303021700b91202e441703a22203110740d40108035070380e4004200c1081008202d4078080d00903140302040700c4a40201c030181144024001041c1c40510703084441c94401c40d583c15500f0049003009221840d04080708403025690860307010340007913861f00180328241c14404001007501100041d690a1416070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 862616178 1250 862614928 862614937
    0x7030c0215010e04080d050403021b06070201170a110f13060801060815040905010f0b030c04180f1703010b090108010b0f030613060b0c1c080103080f0a0306051302 72
    0x15101040994626502203a45600340d0409200d4070641c0e00050003040f030ba07500110f501620400e49030f0700c2e100d400000d102c1a202c05440c1100945d211810032040c0000c5580009442c10f815200141095690b40001700800307003030341d81c10b888070042d980401c01c039a656030071400407a00d0800e44ea40d40e904a0204071541c80c0d0000c40908070003d20f1030004100140705160560484031295140e2070300d500d409142400000020180c2540965510311400000d482805460f00c1140350000000340350880c40285820f01203000022881540f808021806032b00d2841d2800e800da640140300380290340c81c513140442c44e043c02d800c41e00c0300c542c1c000b000006040d040034008004451081e40c4180d5aa681e415402107a4015800070100b50030062000541e03500381110004100006001e0218017180e682044ca20a40d10050707020070550800c0142c1d94454602030010f40c2000c64901c0c0c024402d62440d140c11110340607100b00a0750014001410f00e14443c8203070012800350900400801d488052f115071900290310 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 862617428 1250 862616178 862616191
    0x6220902150c07080d111b010912230c18040602091f0210060b04290d0920030c01050c0f03030705070b0f07120b0402070c0308030601020f1204060c02060d050c03 71
    0x2440c24a00c0d1380b5200300c10124135081c090f002440f400c49247d50100d841c0b09441e803514100004403500160441c100000360200b20300581d0f24108400c4060006408076010411441c0d0540c0b01284259031500c5d0112418140e0318045d00c40b4055031114640900644a1114210b40c0f00c1c0403c21118558035800074001e10341c4590ba021030343c92012540f0000184e90f124801c4200c0c0303001c240010400d0746800a01c441c10038102121340c403045040000161980c3d044414180030032640d0700211007c10107540841a4030000603000c0000c1d0340400000203684800d240496410004007140500907520104040440030b92502c0503070ba22480c08031401011346d0000d15080c0ca120603140081007001a4030000540920b0b00d60342e803040c0407c0c1d210140c00141c80161400c0350029400c11070b03807010410020041014510a0902d540e4a080c40800203250510102203290342e6080042c83d92240090b0004a50480d14a42004140303905a0700000d0110300415150312001d40c108000c0149040b00200214480c00c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 862618678 1250 862617428 862617433
    0x1e020318150c150f010317030c12100f0b03011811071e02010f0309030c1b08100f050c1c0b01090302040f0603140708060103060509190c090506220902150c0708 70
    0x184c3d10315014407118003e10010f01380001d50105482510326400045a000d0408440305140200204d110841c4407400c0380c01812130114500103000c005400740140000b0451058800c0c20341d4141100140300030402c2c1c201d090010b0391400f00b0600c1541500a03aa00350f0341007001c0010114141c00125200c1641010807400981d03540382d01d9446600070311a42c12641e4140d0b89404e801c130078541e12444508a0303030300700c0440c0c2081d0000002e00803000300702101205c1280e40011520058928110741520009460088803100034445420000c021000312901c1001e0100701180c08e40c11000140c1d15603d0681000c0e41190524003110400f00140d04800e00312446416100d0495500c01101c0340c4441d018040c0340c036075803c641c004001254a540045030020030600660303000380c0300c00d02540044404450102c0d02c090009a042002150703600c11036030300400540300d9951148016645a0721400b9082e8100f0000c0d544024040c1592600c014485c060000352200301d41ea4145240402d5481e07210380314100075031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 862619928 1250 862618678 862618681
    0x10903080c070309241404120b0403020c1c0b09120a1202090a09090506060301020c0a03201c080a06050d12090e0a14130b0f04080906031005011e020318150c15 70
    0x11b10241085400703d810140509201c07001a0b640c0e64869540a0400e0381184248503541c0300035620000c00d0b00550b4000200700d00004040c0c81c0940d41c0c58001003606516030007103100040014011400c9980c450343c0780c901040141d0010000000038060310800c903410146000740800c80d400168803801049000d40111000c540d00d4230b081500344d2050b0401d0b8149030304460108400a401141504440c40044640c0b403885d8010706080c5142240c000d680301c0c0048400081d4212240c0c1050f00d154001c0000340c001c1c44143e0628000c03034030000c00307960010481c006005448120a00c1591041c0152101d803d002c0520700f00b0450f0003002d00002c44180c0c000b040038201103604408852101112540c0c05141014039075200f107164440050001c0c42503440403010884000c141c0d8074240114072a81030451881e0075039082034001094050041e01c0404010f87d4001443c3c00a03800206850041c5c041c000400c070310030a110040750082210b1041016480e07000705484d040c0d0440403516601d852001ca20b00e5025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 862621178 1250 862619928 862619957
    0xf060f15041509081515060d02040e040f0c060e0306010b0c250503010e160b07020619030603030f05031003260708030412180317071a0612010903080c07030924 70
    0x111305d810b80e00c25207003c0c0400c1944446041c50f0000e020300ca60000c10050500799650914107080c401190115001d100b211182010401e000030340703c0203408145007614855031454003080d600d41040c0201181103902081c17100801e1030801c914140d010b0301c0042130310b5a84202c0c0214803045903034001d0900c00c0d420060460710769140010501415200c952440000a00c0c0c00c1c0b502c40164008407050303804c03000130003008840d0010900241041e45003a40c00090041c030754200100780409031415601044070030014003201c4004048508207a039003110144400340225600c00041c4444249004001003000c55140140004540074501c528024048a0510058070500b00c0f040200001801c424490316074040c001715440d0320806110701e81042d4242c1c9026116200c1d0840d4040b203d40c000ca04021080401c000ea00b0900034071190300910500a00001c440c40c2c2e4054000780f0000c083d00780000300070441f41705051003689110000d02c2c141381c06101250000325a4803041f031001801e04049205504142034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 862622428 1250 862621178 862621213
    0x61d07050406150212160803070c150b091504060f0b0403061104030c0b031902070b24010c11030c090f010608060f060f090d0b0702030409050f060f1504150908 70
    0x64030f0031540600064001400114469003181002d8107481c00d8240682c000038200900550103240d142c1c8803200000003d02e000c4030b24662400c804070805041035052003598a03640390041e003003034a1b045070500e0301365404080740040c0516484208410000c22000401114420042054a014401c1404607030403450000080e48981d100c000e05038240948108248640e540140d0f4010b4125802c00f40c03803000d0038004070140d030080703201598401c0c2c001d014042040b40c3d0401c600034006c00004d0040d0360551017000600506208038000d0301501c65101c40c0d4100340d80510000c042502c00604180103800c02d000000807105003402035202003420700703012034102d10380350248048000d40108000d00c0c101c0204155006508950020760b08a56a9400e94001074890791820740300e070b031180e801140c40301e15101440c0103540d0081d118100500c3d01000f8842c41b030b16121502c3d85a081c06451718000c04081440b41070491151350712001e031061002e0300e1039003031540c04a250811612080d084603e245000f80400f51b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 862623678 1250 862622428 862622459
    0x406090212060904020105071502040807030c0503010f0501061b111c02011701050a360c090f030209041e0b160906031a0415050603040506100f0b090607061d07050406 73
    0x1b400b180301841503100152042d1200040c01d4262400903080c9603884000a00c0d02220360411541e50070007000074042d60170700b48144000a0401c503002c1c03000d0351502d4400740a0440a100550343c3d000909030b24828460703034078240c085a48001d01120b01501c921040002401c00032072003240020300342c00d010300e2060000c0319228142c40300180383e07031101450904511102407a076041d00aa445444c15000038589540c240024208030030400415003061040300142514199008046030f1a1201c506001503141e00b00003550003580420650b00c11500c10611003508406014000c03d058040380800168074003034014240140c0c40c54131280a400c1d11280141c040ea40481c030102044900200900614501900100702450342c0d004192400d5031514003051380c980c81100c003900d071544000d00380300941001080d4900101100c3c2000502c69040036418005841440741d014401c420101d0424180403455000000220a40c0000503400c2880340c142d41c0c0323448075071007441d200f50b1801302c00040e004c55102d01d19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 862624928 1250 862623678 862623683
    0x81c0b0607080a030c0908030316110109050a0f0201090f09020c010609180b10080a050105101d0a022b0e0f0313051908010c020307140307020a030602090d020406090212060904 77
    0x30b9040c911512800c80c010441041700b030b81041070880e0b0008188034244021405542c4001d40d0781d00810907020007404002c0c105440304101e80c50419030764081000400c031589510750100c02d0785a402d5a50004a8140500e81c0202513848240c840024250310203500500c0c00c01031050090081d40d554040e0002242c1c08650140302c01c0b1600c2002c0c00006401805040e4030819900c0007882c070710785900d0070a1a0940e5584210b840e80c1d520400e0252441000c03d00e240142004041807124644902001550400160a56100c00c0e000320300d1300040c004102c0d03010a0210703440010684014603000f888050310007006188600d002d0185403d42c0c002c0701000300e95001403110781c048810751402080c8a214091150b1403040782c1e040c40b00105a050080c0504880c80c030495004503280d80e118205a0900380380050000120341c401c10003500140c4544030441d04686c0c1002005880c0d000c03e078041402c103071040400940c0207203820404111900d2950141103440980100b00b10103680385020b00c021940f054402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 862626178 1250 862624928 862624943
    0x10b04050607030324060305090a050d111903050a120b0a15030b030105090a02011209150f020c070303020d14040e0c030603030d0e0c12030a08011403010207081c0b0607 74
    0x90000d41401e8004140b4140309240005d10b00800d109483c1001d45110500940c01182c01800c01c01580d160140c3d0307030000d00c0312000e803584100b5641d07070544e0341e03155104800520003072489004182c0010721085020912049500d41c4400651800814a5104907545004240c00c0300c18841e42000718462405801006001007200030309010000b40c00d40c0810314010201a21849007460680313085c010309014440d44002054007011a100142089940c10a4118a00d1131700d641315000c04c0f2040c440b08005580c14400061a14854551601034414980708681034490624000300705031340081c0e02130800885690f08c1d01141e26641e41c00ea0b140c4138910881c89040241408510401e8850006507000240201124503100c0d0032034140313041c1e40b9400012215a04900c10300c401504100d0740b15511001800d000e1881c12000c600d0141c015541806152001c1200100b01d403a2500d0950441e0000341d0072440d0303551101102c5624000d81d005e1b460388644290704080e10703581a400d2038800c0c5ea41c2c42c1e130b100c0c10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 862627428 1250 862626178 862626187
    0x3050c07030c11031e16080307030e10111c02010e0a08030a0209180c03010504050708090d0c2301020306040b0105070b1f030609050c0901051f12060503060709080c0108010b 76
    0x190f94903c06a600442c80c1d05000b0180d0000240300710021086001240c0b0000d440156902c140c0142c51112039801401240c01c02c118400002c4d80c8408000300026080700d590002c0801e0703d9044070790700346540b50b0046d00d01c00c1c90030740c00c8041d02d040d100d05e0304450551f00902440c200d6841d0036888903010000200209030a00202e0028103940d0043e00b00c00d4000750172501180440130b07034180340c0741050b110060481d00010062002d420305002da2a4010414203046250b82880c5011a03904c1414503000070800c95104c40f200d0401030241050b11a414640c2108002e441014900382d00035407007030b5401840f66150294050255000348140c0e0b0085400100702060fa64031180303400d0400303c44040781950813480c850040300069140c4103203d03006015100405140d80950103009060f070040e0400d5100700003071840034600c0c0d1086650080312130694500401140780c450f10b03490281c0a5500890b6041c0200020003000c203901000c1c440071100c0c408100e074220b074862401035070455028010301448240411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 862628678 1250 862627428 862627433
    0x40b09030a0f030b131d070909020d0f0609080c0d080f0f0105060307180b070318180f0212040f030f05030c03150619030b03070e01080d0e12070801060603050c07030c 73
    0x740f080829440140007645c00d00d29034500c0e03034200c88040e0524404220f00c58003403040210f080298501a28512404004019107600007800160340084d00902041016500d031040007a140c00956407564000308241d1919a1407210a455100350318404002429800016100313250221460f03000e80008010683c3e60390800e0b0034000c4540c0004e05250a0100b203000c103d880368050351040c0c0050000c62211902c1e0a0b4500e401080303509445602030241c0d80101061040e01710250080c08000c1000d5400034440840c0d041d4103000e801800c05030034203e0002e200708000d00c103a280c040008240f00b80d0380d0202500392084261041d00040e11103c980c040180300099014500d070780f40f40e0803158000c00b40c3e0705014114050410003808210b081e00000d445058000503030030b0412015020b0400a2950b2aa56045c0055a0340d2014101060302c208510140c40740070075180c01c003e00d0400180c3d0383c00d90b401c058554880d14081c100030b01c03c8100113464400094240020402500d400c541d060b0f0b5409001402e68 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 862629928 1250 862628678 862628681
    0x160c0905181209190e0a0b04061401021f140c0a2a0b040201030603120e1318060b0a0302103b10020331090c0c0b040507050603040506040b09030a0f03 66
    0x1040440000c100070408200c508107171107520700c2500c0303c03c0040790003ca4001071105545031a0300101c0f60120440c1141701c541e80100e035020106c03140205064920341120b13500e102621440c880b1040c460110f4040c4582452900002c294140c416226a0342241c241002c03500405590718100c10510303143c0340d41d9000900c0c41030150350040d005240c0800c0880d1a5187d000c400d1145000100100d180c40c820130103d0b090140454096100b4240d0411143303120a4003580e4200303c1400040440d07986a80354001907903106101005950007a10070b0f06445444100500014015401041800c145480c01595904800c1c802008084c46c0c00c400740c2403e400105001032803210404540c15800140305440c40c0154000850a820100148103d40441e6058540d00307054000c0d0840f0b080d0030b05080e142116507801c11401618968400050011665642481400c0902c0d540000307602c64800810706c020310000041c440d003d036005d00c0740100a6110b4056480d524820246840081001e000d4403210180c000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 862631178 1250 862629928 862629949
    0x50a0b0a0e060309160602032104080708030f1503120f03040606030615031415010b1b010603061a0904020f060d06150818030405010212160c0905181209 67
    0x32410300030307012800500010440d0304100c51020155020116072100e014005038600002c11850000d1858861002c88d505211417906d0300001940028034042030420402c50210340c0e4441e04402c10760744134107200450441c420419034254490049001125507503140104081c4c42080b8020031081c0740c004415004009600001c00903a66a95203030350010214525010f454a01940b8103800c100590851601000e025855400050141d008000c22050212082c01c92410b5907171070301c21251103000d030b0070312080e840304401c0300b0030100c0d403c010000003000384507000110914801c054840d0304e0301c2d8007030611626401c01c981c041e60052004050a070181041002030005017015000400c40988a1403101c400190003910603001882c81c0d810840500e0500015000490807030000c1c7d46441e143c040000e5079084a6030311030307000d910002041412001d80c11201d211b020351015003a0b0f01c003030707131903070321100600c0f00301c9400d0800140040c54980e00d02001c0346040c4a1381c42031018a01b8241d040040c00041001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 862632428 1250 862631178 862631197
    0x1c020f0f0327090103080301150813020f031e010207030306080a0209180a0b041104050105031203010603110408010c030902030c01230702060c1f0b1c0b0a0f15140a050a0b 75
    0x201411211501c403d002c03e4041c50003040e981c0c0d070707079450041d00d1402ca50046403800100b04524041c4051039010104080e1140c6e0110703401c199404203100002d0030083c00f00e0036090001c0034002d200f480940e041d0060001c0700e002e03890802040303613a42c002030b40b00c49611200035801691a00010154130100300d2002480b604001201c181e548a0395890104084c19141560703a8640500c1c00c5001e860305010781c5026110540251800909404c003009150006004860505895030b9401101032111800d64005003480ca00030310042c2241c1101400030401c0e010141d001c1c3c0200e0407698019409031a01400909103d284801c000700340d0b048801c4985c12025049070711900c1000180d00c030301d804000c00060f02c0240361040d0308542c02c015084084807900480c2c90300070660700c21002000ba920302c3d50705220381e030042c6e2082c0c41940c2d01080a402003d048418440992511000d5400c10584614510596502003456854400304030100311050740702e44502507100a0300f09051207007000b4840500345044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 862633678 1250 862632428 862632487
    0x10e0d1d040e0f011a090a09030206010e06030a0c030311060f15120330070e10080601110d2102090d0f0f0807060b0f0405061f020f1c020f0f03 63
    0x100c106010300f51200c05490a0424171032244c1d849540c500031400b6608080c000d0f030100a200e01c00c1c0c2e006515254144244020358403c50000390480d00c050001303c036101d0f400302d007001245850f03240142660340728401c52862413113040006881843d210754802d020300b11810301a04510044000c00c484038a07440c0b001441c0340002c0c8070b0011410f032402407451703426140c80740160001d000d081c201c0ca800507000f408481080384001c3d10b07070459110364142d0740d0f48080e14a0042215620600181c45030402e41d0b442e00e501d4030841c1000307440d142d8051a40d14600000409400d51200c11000c0c1800745e00480c1e9040e44d22091407504400020700480f21800051301c5481c964500c403115032140c81445c1c203c1c14050300c2103505c0d038883c9481031a05548208807040c0c02c0f542003040e401d2907004a52008241c00103242000307601061400c80ca03000300a9012803150354822108003200d035411032030719031040329002d402501c11a05103010b203840c0803600e00d40307084603134000b1400e00d1441e001c074041100c411605c040d103d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 862634928 1250 862633678 862633693
    0x40b06150706151d0403050a030207050114190608210c2e050f15040c0e1207060f051204030813140a11060c070b091c0302010e0d1d040e 60
    0x241d02c40c000e101205801441c1c1007011403406201c040841c03a40e000d402880603105003040002604030003900e000c2c1450b03240060316001d0a1034954018403110074881440d80307c480030040c2071400140d413035405400c2c2402c18001ca0341d4801d0030a80d00c46c90301404880e4210101c100c2c01c80c0c00500e4000d02410384442003120300c0060584098001d02064980c48075401c0c903480301070300e040300481c0103080c1c0000a1340320100c075500c1e0000b000c039801c240a0402c9441551507000140c0788912510440078050300090800d42c40102d01d0712283da44190611600c40400c980d4003211300803e000c2e00a949540000c412445c810381d1b500c0d03400f1981c03100300500034034050684a4640001c1146204400085105200180007802841c1040400b4407080041548544010028014548404900c0a0485041c0585d2030749850308100020700d000d8648242c0c040c0d22840300c4045040c0343c0d0540020300e813040f404060342c20641b03244400312281001803411080c00c000383c84d040b01c0582080d52100c090000b6070320644484 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 862636178 1250 862634928 862634933
    0x224040e0f06010f0908250f0b0d0c02010603080d09020a030c080307050609160e0c04030b04120f021b0d031701080c01090f052b0213050106080f040b061507 69
    0xc540152100324034038518008000c01e40d40c01c100b00d01a0080c950800d1050286480e40303040c0e45035122908a042417000c0c91200e002c0754031814610300541009120300070b9150300c03012441c280e900280805110103080100c601c001d2801842144181e036017000702c0500d8401260304650180c82c0107a4200e801000c01d56002000c0390801030140c01a0090310091641e481c0c240c204180341c1180a0709400c0541c0200c0051905c0c0458180700004a03070101d2611541596101300c000200c1c06198006441c80b441e004c208401c206c488140107241740000e4449840c010060078040380e441c41401c2c440454000d07044030521151504500001441c1d10a00d00303c0e204040d5407020705014102a03000061a81c820409900c2a40c2c0040d804405000c84000e0590729901e0000000c6200d014103541d11141028002c40825541856008405041c0c0140c424402d0800380b50948004000074420000002c031141c3c08102c130400011000ca005540048042001d0f4485100300000070240d030300d0a685501042007034000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 862637428 1250 862636178 862636199
    0xa1a0f010b13091407020c030c09010519090c090f140a090515041d07050609030303040809010507170a03050f0f0403201009110d03050418020408030d0b040e0703022404 74
    0x119813403002c2030001400c00f9400a89490b401340b450f0b5100e50000da42440d100c0d00c40b01000d0741180d204480000500c4640c404c8601d0130f2480340c001481280c2015540c060346608102c2040445103401d21401e412552200400d4202c0245040194002810704080040c0c000c550400c40d007240b184241f000300450034000150881e203410040c1100c050740c000c1480d201401c1800064018101503686074503041c2075a00103a184c4c0703c0100028140603001c075406400b40d228005840c2d000390300c54050001510701007400b00d450b401c5401c4450001e8140030001d500c11082e00c41c0c907070054036000c440803500d460325034054400d40b074502e00102c03100c8040340940e65030310020440c440e8840d541e003000240c5c04185085c0707209802c0d41400d0481c0140c141615000021ba4048103e400715240250310681e1060601010f10191103a0740c0518070620020415004462807a03100841050b001c03a8200409903009081c25200e44440c4006580200c0c00e0b1041da078880000d101c426001c140810303001d46050303290000c240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 862638678 1250 862637428 862637441
    0x1110150b121b16120903020a0f03050601050a03050a0201031a0402040e0901051806070804050a0803010803180a06050f1605070e09010b0103060f1401110d020a1a0f010b1309 76
    0x1150100080601040b400c60b00e540846800c510784031540b82c801c030300c11810f20764a07508800a007501e200c64080444540f1440484000d19030081007401229507500e03a00b07130740358400c1c0400d0b00c2a004201c000a07541c5020014007080b264028083c01030429250019401481c45a00045596000b180d040c0307000c0da071380e10082000c3c00081c110440325090034480c5c41e08452006100eaa5000b120a0000a80b01e000003115644400075107000f00e0540c4c1c4910340541019151000103001c0400440003103480e81020010300340358010307401c1c2ea50f02500004200860550184151404141e042080c040d41d880f08000800b030b4421360481c085003030340d80c0b640c400b071800d0740552145500d00c811801303210190000f0301404000c070f41c1c2442c2c01e110450401d9223aa0406115200f40a8482c10b8105030411690144000e6003050200340281c480c11120b50038060749414039150121000c42501c2c012848840151240700e00980c00c0c00c41d1294642e00b060648a0310707030b00c468100c11503c0110440010400f03002d00406 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 862639928 1250 862638678 862638697
    0xe0a060309060b0a0e19110304080c1902011215033306030206030a0c03090213150902030108070603110c100207030809010203040f0803070509041a101110150b 70
    0x52141c816041110840b6440710b2610700c11443c0e41002c0025076402e00e4460380010b1919002c0303821305524001000142040c00080190500110420040c007501718090030a00360390405481d9181d03803c2d208048034030a0010004d02140300103121201d1b0801c254020301d840c000c1112001c00071a240c0e12205440304504221340e5003542104901c031904561030000c444440101c6c1740a00000c0c0c00d5600045141c00014000f03440c80342d88400400a02c0c0c401c0e0000a40250040c1c424400b1001ca081c030000500b140c2c80320150b05007522003000416080c240300b00ca04807600c0401610031181824400c030302400c040c112421726030b03c0c00e10a6082601d0b083c027010170380300c80800e00140c2c2c410b032a142c0501040001000c002c4907900c14401c020214658006101d00a03a12005e00b41d502c0d070718003a066610313015250003e0f4200d0700e08145100d01035842d100080000100f120100180c209807142112040b515075605811a041a4261100401c0980140f003c00490703100f05066991a003004800540108480 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 862641178 1250 862639928 862639931
    0xf14070302120105070e06160611040b071a09150f07090e0a0b0a12050309040b13140609130210080a02210a06092c160314100b0f0603070e0a0603 64
    0x284441d083d0080201c8402c0d81c070940da0907041c20380f083c0601440b500c04110103009c450302d070242c12114000c01c10455014003c001c1c00c083d00d034902401e00b0712001c880c008020940c00100c1c000306001e220006405102240d800d0200091036580d01002c0d409004003504901c280001410041050304101088921402e400300000400c0404030701040307811510f0b580074000512800004101081c2e02000b11150b4000a0f10080b4480e82c062020078501031403241d04410007403408241035141d14103824641d0041104541c4403070552219495462011210280250311618201540340d1007805000210703401400301c0700050038070304007201c400101c40034585c0c240b1160030b400c1d0800c9100c950b035108040117400030f15020071810b60f240d4820780c0c9102071100c1e80c070003180031095185210a02041a407010034648121400c0c00b50340c0f85009003c29040040001e024011760070450401040703880340c0d14401c0c0c0000d10040d20011401e040c0b1529a0001d08404d0400100180068182d101d5600200003002182d40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 862642428 1250 862641178 862641181
    0x1115030c0c07051c060509070b040f0305010b1c1214070b1f0b090d020406080106080c15090901090f0f0c0206061e0f011119110a050d0f14070302120105 67
    0x541508100990300980e04c60900074401c60315081c0741d0900c4001440d8021070018603034544a060034034180f00703507000c80040d9000140214500c0110001602120b210324000e0080ca000c41040181c00e12002485000481e122409000454104640b50480074014200662682546148008254400c54040e1560f003505c006000640303150011641411018140a00303c01c1d0520038001a07034030668040b41c0c0726a049191503015903450341d00c0b91006100c0480200580c1b07595504603520303003440e401c005101d500d10002c0ca540640c0050200c0d0310309000280440e101e6800c00e0117074402444403145106c001035554202c564000c816200c0c02c1c049141c04c1c1c0041080b49400070401c0110002010400542050841924842d4a82810861a4003406d0038000c145030b2219841620307082e03005009d80d400c9107191007980c2c2400340c1d410722984000710542e04000c06d180c548091102c00c42208030001d20383c00c032252844000c00c0c00811001740e032840c26400c1d034003031070707640c0c0c00103124540701402051003a5034400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 862643678 1250 862642428 862642447
    0x8031e18010503221a1302240c1c090f0f09050a0902180115020d080402120102121009060608040b0402010e04020f0a08090d02070302030a0b07030b130b01090509010b071115030c 78
    0x5581c45d0b000d403a46d0060b00440d003240e4041003180601c0c401c0f0703464204c9001c029003124400c10084d50402c40c0b8650480e08002515044d500d0403000c441e0001c00881c1c06100c0218081815150070b5058800d10310001026900d424610f10040400405108640b0390b113039000c0c80148d88251a101d246c20a2079500344641d41010881c003041280e00100c1000c1d9440341a40208081d0070098480d0301680440741c3c030300c9040d050211280a4072a403d4008103000752042003000d6140749a8020058503980c5000300080d98403801c0030795243c07805880c048e281c1c0a00e1700c00140150311078540601d4102d40508003500302100703a0003291480e0070495004d000f0030050310400843d0f2a08001d91070303d0b5605803000b010b5040c5140c01194603042249000340c00d07000f89100042805000340c1104000f0140600b03800c0c51201403c000c88014a0720003507081c002901c01000080c10300c0d2002c0070505940080e800240380c490f690340c420f100b00c0064940f40b03801c0030219210701c00500e50100035500c11202808800c0e96081c1d01c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 862644928 1250 862643678 862643723
    0x912080105040e1209030f0d020a1a0c030109020705011506091404090b04030f09030b100519060504090f0902091005090705180603150a08031e1801050322 68
    0x50700414040d03464281c1c0e0081c0360000180d5900010701441801c2d554800c1d00c40828205101d00c03084003440d2146142c5021110350000b60414001d000f41c820880c907414580841c0d44103030040c0d416040c104011b000501c403e0344180c4c014201c243c42f90000040401c3c10744150f060300354050f4402c001040d00c2c200f040014214804203040b40210880703040043e1030072a9100040007001030300180410801700c40306004d41e801680700f01f02640d0030100c180d40700c5c540440c1d11402c40440e8000c0c2805011040001081d401c004010700041d01c41c07648416043c20b003461942d200510141e81400c4903075440344050030150311303401c01c114010300b241008522014245010300603072100141c0240c0400a04101d0b40a902e0368601c0340d118280c0703040701c88551b40c1d00d0707410302c002d01442850f419a40c801100c240006040600000600300e406084c22000e8000080e83d044003803c0c09001c42031a001055035040700055840341d001580d200040b60000f0300d4220708071103108400100181d08a0302038031003003a10900288031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 862646178 1250 862644928 862644931
    0x150907170106050a09021c0204080a060b1206150402070b010816060807053a0c0206070906090306050a02040f080309090c090d020405070e040903030501140901050a06050901050409091208 82
    0x425000b40141d40c81c102c0407580d600400c1c402c0f880c0b1035178003080110b000c03040c0c100c030a050000340c00410741d11640c845601c50344079058420300315041da140664020f41f5040c0f00712403011955840001c0c0a01d555020307000c08224000d146000c2d80541e00704000e20001e6440c0c0803842c040c03c1d0180040c6030f0188100130b40110188150401e205103c100420851225403260407100000304154000420100540c103800c590315004404281000c144255000329100c680c1c8280c908110b9642207603880d44030308009031090b901c0c030300540303001400c0244c0c14000304a0540016402050a034001460300e07030b0300d0045042603602034010005035000000d4880481c0791000c101c0360400642c07411180f81c040034400145010110100c02801142c03a000003850b0710f8000d01d80d0041101025209011801c07003403a0050007001c09015070403441c0302c2c0030301a144a06203100b40b20b05940c3c1c09000340d0002d605280382a00d403500034940c01e0381040f1041002003152074203030147c01d01061082c1ca031220300620700300003d04030040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 862647428 1250 862646178 862646219
    0xb0f0613081011031501021207080d0f050c070b0c07120503041a1611213403052d0a0e01030509070612090204060e010e0a090804140102150907 63
    0xc2207a03c2010302c00c4001241e810944170035034000300c80c0038440180d050000050032030b841c130f00011409034144102080103100e602c2003480204012100d80c0c982a003111b0003541ca1031f0804074148407801c0001c418103a091380080448403900d0500c0703001c0e900d41501da4076070141c010009030b01100741b1040105200c142c1c05200729210065074075151400c0c035111f241e80d0740c4400904025002080c8925820700788491004a1071080ea00240010308090819140d13001446040a400508036008400740101c2e00040703285607403005940e980787e0591801c5a454200c5002c0641c00002c0d5414140702c078030400e1082c80a10615aa544c0d11500d19010181104003401807a0f0b05150401e02041500ea101045001c1a60f03d40d0400c0807001c0c000384000d000501101e040250824503042c004107000e41007030540c0d812510242d510071020790702c01e8807803410340380555001051700c00103001c28070421584040c1c000c0360042c1881268855200408400d8044400b601c0030b80b0740b40c111240500c59207404161550030f156 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 862648678 1250 862647428 862647431
    0x307080c01110105280f1427030a0302071b060c021008090a031110060902041a1804181505070f020d051213080d2309030d0b0f06130810 60
    0x584202c820800000031171042c0d0349010139a60fa200310380c07a03652040515840b803100c100503070002180200d400d0081519048040380c0f503640c0c04d1038006a28600032800030042405113050010303080c420340180d0040141207604008074240b4071584c0c0c0e8041e140c84014056540c1e071a00084d0b5034014882c02c0709080c103602042007148010054070401c0011020400ca600d0320f46a020320240318040c0d81007103000720161109a007400e000003140f51490b005801a102c8115180501d5071100020400a1181921441c440151403142c08c8282c40d05a0040e04440120246401c1004a50b81e801041c0504c588071226880d81c0c8405000407560700c500d43e50f00000c0d041c0000c00b281c120780c00024000e40207102540701e2690b00d03480090701d02c03400b031981d01d01d14503030000788652501c583d000c3c00d0014007404080402004424080b00e41d081c800801c51900411080d00951f15220602c0103190103403081150103508840103c2d00d6041c15181d80d07008242c41166030003038246990504d102181032030f6180041400c002e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 862649928 1250 862648678 862648681
    0xf0b0304050613020a050d030806030111090901031e060504080c06010609062a0b04030c1103061909060b0613050913052509050a0b04050601090e240307080c01110105 73
    0xc1d100090342070700006010b000a00142c42440042c102154542205d41c200300d02204540030181c11180080c01490110001e0140b1804165500d500d402940302c420707071004200e80104080344020304000703885d90101200d40b603890142d45404090700d1050740c0442307440304000b4400400300000d0103034501410b072615000140c10f243c4031008089407140d02044101c1d1405d010058031302034159140100d680e51101014005213800e06010389401c09000381521000c98240b8444400c0c50041403031446801e503640248280d0a0071f2a1000081288103800c84140350381e04400f01e029903d03030010308684110740743c58611150808050000c040d8010302007401160340b06007440001000070800307103592450044078110169050203682c03010200c84e401044110320300f8050207036018440e0082228007109480a02882c1c0380d140044912500c60700c185281a240c90002c10140c6100394850400405244211010400040000f03810000c2e03560040302c0b96844000e98019950300100c024a11001c0c1c04001c002e036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 862651178 1250 862649928 862649933
    0xc0712110103140105120309030d050901020f06060d1202010b041d190b1303050403080d1517121305031905120403050a02040b060c2a0a06090b07030c0b0708010f0b0304 74
    0x60f0345040c052103100e0010040961080384041003903902d039200040450707480d21074459018119030f0000e4400c60042c010b076a11208410300001d4250700500000d040707002d4180d9030351038160315040944034410442d521350f19002500c2d0b980e4051400c02003428280360406c034800204035440c7c9201040d1228011039141d000e500070503400c1c0d820780e0348554181a01e0027400298a411540352080741c1000309144400f003000d040103881940002101c1c41600c8406074025220344c103602010341c49005d05071195000398210001404414058050007101e8008410f1041e04c50002034184040304041c1180782d0650f4802c8000d100302001660071201044807010701c1c0500f1512420748a2046242c064003d946480c40601192503900c111464080076405039200415003a40320020204501c0c000401d9990802d01602e462030070282d040304640d01502c1e45c0482514181080c0240d4110b41b0303040e420700043c0031442020500326514a0b204010307076629201c10b981019a00000c0781c42c1030b08186117804090040000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 862652428 1250 862651178 862651211
    0xb04060509100602061e06040f02070c030609061406061b010b0a0b071707080f03060102031c021b030a0e150d02030103081c020a0806040b0d20132f0c0712110103 71
    0xc207c1010f6030041400080c025400029106600008207020740b589000014004a6485000301ca40b04200c00d003c21641c0700180c00302c183d003c0e03403199403014040020b20354801d400340303519020008010000c540820b000c0700164003881141d1010503181d100003186410449450100c454054500080c0e030301b00a1241c8404415020b01c8102401c10600000410181d03802002035580d084441001540891170300100000690490540b03128010040591220651004400e503524a04950344110118104c03a0402c040340450a428803403d050403c00407500400300d00041d4003850081507400e0342d40c840100d20080c100c0d0a400401c11083c410f010156815a015042d540c112030100c40200d0400b0040c2d001807c0d80545e01c0000700007044100039076001d0075041004080f404421988000f940c00340341046d8050700c40c2d000035804044111400b40300300c44005010080326900b560300c0750741400071134003c0340e01d041d8041c0c1050102040d001141410801d0588914241910a180a2180c00c206038070100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 862653678 1250 862652428 862652431
    0x50106020a3c0516270e03030f0609010b07050601030803090309101d06190507031e08250210180602041d01080307030c060b04060509100602061e 64
    0x81503034800c41d20030103004200c60100354024949114140740e9584800c2a0b41c0c04000580c002c45450155614142624082c4108a4202d03070920700c28009101d10110000004c000c0c0300c81050030a5502c82c00703120006020000b542c850000e0b81950811424060108244c41005920021003400c0411401b00040c10100e1100d04580d800048207807079840714103859040d800f0b181070480d0405c6a80031a0382606910820703680d80040c3c3c0e0300e00520b200c51440144038080c80340c0300d8800a192149400402001d10030b00041008501a2402c040b08a01400d0b2010020400d8000300001500300010f00c03140704816a5141000c80c411119400c8154440c80080d40701c00340424080085551015005c1c110034209906160b200c2d03025800f1503a950319002c1007074003080b28248012180d400c440000c502c0c18400412221903a4140d1142004c025051380c8101c05403110f0b001c40c0b5049034641c5000596612200f0b0214003804440c6640e040007410020300034a444001003403030540c10b4641d184043c1d650f0f80d07105c419 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 862654928 1250 862653678 862653683
    0x6230118020a03110307090311010e1c08070807050f070b120f060f130219020d0c0b070e0a0e0702010b0102010225140607080a1514040902130e0c010e04050106020a 72
    0x7580718000e0b00e00c02d034000c1a40c420120701480c400820000b5455005060400ba02c0c071904032281140003e0004540254800d00d6442d0400000142e910b180a5024400c5d8202481912104e02d000c030a130340c5407400c5d504900340c1150785500001c0086200f440910014000d440b105500e0360030007181061041e101c40c006052801c0009500c0701041007078840440c500304064000c1c01100e401034121018400a5001d440c41d20030703000b99520080c640600c08a26444a100d07169100c1c400710b80306485081000ea4007030000b106021042c585802d1031303283c11040c00c00030305042c0c009074060301c1c160074081e0070344000c0301200c0d0469204110700041800c1403980141e08800d40c002c08580d51381185000300c90080c2da40d0b1070304190f200d00030412034050382c00a4014440c100003038040c4000d01d81242016110b54483c06840030b015800c0454030100d0a00d6801085080c0c00100035402c0f207080f900045088980d40500e03810f4035045014000c60658200b0440300700020261420422980341c0340c4000d40740c00c0c020000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 862656178 1250 862654928 862654931
    0x7120c080a08070b1e090304050109171c051309050a230109110c07090507140a12180b070905040b0f0a03022206080604140d02070519030b0406230118 66
    0x318014801012174a02c00035115092000e20f418038040890390b941061060300c1c002002940082007e042c02c000004020f1342100081c1f48100400d00d119414a0030080c3c075a003080010301010825404005440009265403030340040d0b2400d00341d0361202074070380d11299440e010300c6c0b144000050141c9094030030704403652100c000903a4840300300c40010360700c00c0c1c0c0c100340b1881c41410300c0480c1c407142135072101d4003441325515807100c008a0620640400d0241d92100d0f00400c55040c512400e41c00c00703400c220b400a44d18551a1070201040e900d8100e840d80c29250100082d0764400f041c0003500305841041c049007012900a14420500000a0000c0000e070000034041c1e43c0351500d0030300180313605402d01d0404000c2003041c00004c1c2c4030301403107503503c01c111130582d041024021444441c0b0000b00d89954202d505138080c1120a04080030301034290412950050801740e6144004041680c01c022640200d10544001c100212010f96010300c01c4030030b401803942240144e0040102c0038605010401100f000c450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 862657428 1250 862656178 862656181
    0xa0911090903040b0408060f0115090510090302180712090f060b0d02060a0c05010b0d020d170f0c0307173f07030e01141902071407120c080a08070b 65
    0x30303a2825401540e200d80340c01c004c00f2a001c034042c800440c0c9607100b000305540621661ba610910316090b0204080c206012801c040b0051129042020f100230a1a2003402c1200d003180d603d50100c0e401943c80340648030b0300c120131000d112005520400c00e410300c071485402807200d00010f80341d04180b1400c0c248002d00c4140c0d02ca140000c41c1e1030301e084092070fa9800408098980c402003034058031075020700d00100e40fa540b078014109001c0c07800c007102c11401600036100104502d0507540f01c15500c82c14100c80060040c041c4618103d001c0a000280365108400019540300c510a107030002e220545084039404041c01800310041401d1401d40d04c03d4050016009810070310103034880341018080607400c03185030b4143c0204000d9880d406070800c00444500d10020403000710f801a2940180d4400d94490910030395030300c0c0d0002c4020b442d4001d82801405054502c07424031030040311614210895020190250380301c820780050041600c3e90b03000411350f08010b403d04c00c040f42d41d030301e800740f250a030700502002d6a4030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 862658678 1250 862657428 862657441
    0x3080c1b10023a05130e1303050d09050d0c170f0f030a060302060703170a060b0a2a050d0207140a05040c035a180506040b0f0a091109 59
    0x240c1c0c5150307500a090683c1c03c401c01d2000034520343c00b240e8680340c42140c90400060002e034082d2000d02c078420030540c4005141482d5001c54140c0d0086054181003070300d400c40f1101045080c0110b00301c0c0c1b01142c4907150604031518103261000c01182030030003c0081804a200150009002c40e4228900441019925503840d1000c2c00202081c1e00080c2d00301001080d19020550003002c8100380000c0281d10058036a1090094025104980a031102008041c0100a40c07503008110780c0100c0c220000c40c106154920811904044442450a407410741c40896030700041601841158064903050320340d9802440260041071002002d0300c1120b0040313aa42d416081c90038860b81c0300b42d030081c00c915006600032840070103d41040300340b845140d00740c40720100f00668040c0807003c2d551032500180c021a06c602c1400b00c0c50401001080301c0000c0c410302a100035800502c05001c1d9510562142c62000e1075400e0422024503680743c01810841c4462130901404089000c0c8464040080350849612006a0303036003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 862659928 1250 862658678 862658743
    0x501080907030b161e090e062b02180f01050906040908030a0b0a09020412140a0503040815010f0b16140a03020304050f040207080d1503080c1b1002 65
    0x1680064150f000240a00481c0302c00000700b400d6143c034a070340780044000c01e030380d003a9004003d800c1058081405c40364100b0114082514981d0f00030780043c07008142416050f0440da01e00902407101808002c044468002c51034600e42180c401b02000d0042c4074145030100c06a1a4030360306004a03440b40c40910005075442e60749030000e201180e44030000700c2d140c2c00d140c4510000703005050920b5105404558001c14003034418426102100e080809074419012151205240201d914003440c00d64052006600301049040000b03000400280c4000c061441d88101507444071407040e000204140e0051a00300480070b030780000d4403000891002171125200107840c0100401c1c0c0d810501c1c10385800390342c0d8a00103050f00440076000f00c1c0d4007525403040701c1c040c4400f00022841602e80c002c1001d10140b01c1030441e0940e03507002820010a201c0141c40017030b00c81e2581c0e000c90b0008003080440d41d100c03018455014201241302c014104003601c041c009000c21010282d201e005100c51504502c01a074004078504040303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 862661178 1250 862659928 862659943
    0x3031801090c0806270c0108091603080414030d050406030b0f0a0b070c0f290c032803050f070e0a0e0403090806010803041a090402071b060f030b06030105010809 71
    0x21031011600d0707a4a43d000d03120b034000c44260740c1c65020f08035840c1d00c850720200d4810a10184501510540c16002c0c01034036a00c00c040e050300030310312603040f4806454103005202c102035401040000d803544d1400c0c241c8040c440181b440035000c1d805c64400001516040130980b42660080c0c140482d00320b0189010481101001030002d0740245005000140c0501c030f40001c0441601408880303000545078240c0340c040c40f04601c500940b000c1030000c0c00c5000042189000001100c1c40c3c01545022118203010745590402c801c80755401c10001c0d6035805210041e500c00d603501045040074821460309040f40c1146900050402c4144840503010601c21390702d05120102a14014016010701e06103402c00610740d05080c01212454803442001086a240000c1076130120b03031540c2c42001c6004112004600c0f42d4004180031a0015028084000000d03d0300042008000c2d02096030101d0030701d4600020498018150100b0605140041d254481d80f07910040381d05441742801c0000311520350b1450076251900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 862662428 1250 862661178 862661183
    0x1b0903050c15070b0a0f0c0516080c0307050706020705010e03060403020714040b03105108010203252a020a0b0a0305060102010b06040b1e19020a060f0203090303180109 74
    0x4d200704000328100903070f001c5000404091010031a2900701c20303082e00e1134894652582030702100c408843e00098a000010407851440b00180c2c0d080c86c500343d072601d18084807500702c54056000004180040d581c0401802c1001d0303022002082c0e5414552800f0303440d10090b003d00012801041841c800d0b070b44680e0052054030f94094101c4804a20901042c401468030304c1800c5600d80e418501d604451861015070115000481800c0e03919420891121080b05c481d0401c2c8241d0308250342d00002c0561081c4050341c801ca820071b0f90040301c0e043e4040511010041181c1100030302008050030844a8042a01000d58800607041c00c1000b60007400018a030403040c1d03024904d01d240002d2042c41c070302c0e850380040740920800c3e0002d0150390000c01c10007030385002e103024070110800c06101030590542c42204007043d2037085c001c0c00e0b00e4821000c000d5034a944405d18401c025900403030034481001a140309401d01c1c00102d0b4070031400d40c14a04c48158070380c400134000d60402041c0c11080c801c1c024080d408a14490b9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 862663678 1250 862662428 862662443
    0xa0b0f0604030506010323071e09061202030106080721060f02040f0e07080403080c0315031608060f04020a0e1506130509091c030c0e0a091b0903050c1507 68
    0xe0342c80c0342541d07580c0302c04d01049800f01c040715034801c1c5e5403802826840041a51b14044c007446070802e06d5603580b0415a18180566240e600c0d80040c0100c0c55110f0341c00a04811800e84290740c880c0e006150950300d040d80825425804400d040142c21524455858010460120b6003d50107442c00c00c0c0025008942114105501c00540001c2d02c039030710f1412008507404a80300601d80e81d19007500f85c07840001218042c010a10f58030008012205031001941e2288003035040100c45078410000c06d1504091a00c020908500705205000c080420810307141d0080740c030708800001d85456404104210140d10032845034001072004181c00c4021100d4842c07030400c0c080d08542d100c00203048000c074a4401da00c1854018107000c03001c01c0c0f0900001c201407800b2943c100c11400045070411007240145040f1480e4402c0040c80d07030408038103580c1c0c021148020400c4400c04a1032240c4208c040a0b1400600f00d49024081000020000240301003451140f4000071103c50212030303002d5800d8072541c85070b0000240300b030707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 862664928 1250 862663678 862663687
    0x6150a27020a0906020f0f060f0c0d1b090504061811040b0c07090e1603080d06090219020f0304060c0b150301020c011512020f130b1f0f03060e0a0b0f06 67
    0x195804003008040340c18036030031215454006c800b0251030781211400260300c1d80103400022035031040c03200210b0700b02c500e18500b41d1800e40442840e2003110b895121401c0c0d568078040c09040d0f05c951180d50900035140c219400c00c0035629201e40c0c0c034150501c0c01c0e14100440c0d2141100c0701c50205080545004180d03011980f5a600c2070109031030384407034203801903040c850305d0185d80001c480c1c0005a49026200c18040d101d41c00e6085403944180e41c3c202d02900074100c1d844000100e502c3e103c2c2e0018000c4072180700000850705405120290408841e405400700b198020b220421001c0d40c03040e000d13000d030f9804c810300d001d00e9103869140c45030090f000b0030a0341c1c0540c00003c0344540c8502c154009074442180706c2100301c10a40394030341010031000100000c0c1d4003400700a0301022614081c0f45d142c0c0c40009006000039200c1035000800d002150701094542100200c0441c030765215040444c8401e418100d140800c08035061445c0180040f0015141801840c3c0d200c00010413903c1d651440202c80c000200000c0d100e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 862666178 1250 862664928 862664947
    0x50402150a09090b0d0b07020c040c0e031e0120030a05060102030903031801021504080310050a0f030204050a1424060f030a090c030c14150a02070e0406180b070206150a2702 76
    0x1100c42c1c48401e6030140e0720f0180000c00751833140c801c01e100b030080240501030590908150320f030240c00e50000d40410f55611811155061385094860203406000c81100341c9a2400c1c1c2e084200f2140c008010300d055400410032092030b0703a00442240c62012189440380005406000100e1801c04100541040c0350340140920080c01818005113103d440f1000c03190504907147c1061020700152481640c540d0700c1003c0741400185069000640c6c0044411000140c034004007140510700b203c2034525010505485070003400c020200b80c044820310078103543d400d1802046084a0307840c0e101c024a00000603941c2d20100d01006400c400c00001943c10000040d005500c8201c00d50300c0c850f084103c02c0c4103853704035003a05040d08200c15030707242d419150050300b52945003105480c00102c3c0244125104c5684544120390722020005902040d800750340c10b004246880640a0314040028082c0a86417074032000080540c2e0320300800320141c030268804211540e0414440603c00d00306280031b6200c039400820318040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 862667428 1250 862666178 862666183
    0x90e041e0609020603180d181503110313021c020f12010e0604030f09170a060e1006080d0305060d0b19110301080a031b031b111003050402150a09090b0d0b0702 70
    0x50618200603212100050355023520b04100080040808000040003001140d0020114450048140c200458200115001c040c0d03130394801c0759802040160501c040040d801c0c40a03000341071030000c4000703801502c02500012540090100e80d41c2c07141c6080d41da900c107003590a402c010720f00071555080b034801d414a450060700b1062440d0b661310000310948000078041b10341e0510311110300c03031950180c1481000360310f51401801c41941c0440080c0701d0f40000221806152040c0001040320401400340c004090000909568000e032486202d188076001d03400100d80b102303145175040951036031415103128055152101030081c0305d14050503039001200025460340c010500f0856503220f5614901002c00329246e84d03010b000b41410290015410598071110b041034914050303941070058600c024604a800c0000d0242d450b061602800651140e003070004500380030030b214040744281240d1034140341c2156001040f10320b00c2d10500c412140c840000d5005070b2550078603190465007010302050907140601d006075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 862668678 1250 862667428 862667461
    0xe100c0215040b07061d030406030c02010606080705162604051c03050315010c02040516030605031c0c0f05010608030a0f030204050a03020d23070501090e041e0609020603 75
    0xc1c02000c1e164640c40050356810101c80035541d07003801880c200700da5074545000808901c88505400c2c0d44418031140d44010810151000b01507594001ca200e52417108000d0a4404c16817000381400001401c1c04103c9070040f0540c1c454188a1600b6800c00790203060240c0d0070000440c580d0801e0186100c10310388280103030300130802c0d40c100740c6100c1c2a141c3e1788204101c03010304910f4041d0000d4414000f007000d049598294440a02c41450085000c079400e4002074100d07070065030001c60070305051401070055030b00742c0110002403100300c0142540b1912185102038004421f0380325002c001d182103c00d400c02c008881107245494011000300000341e11184040e5480e4825000680460700c0095003034661032190003210b05840c0041c00541c00c1030310313640c24803020302612142103c52824105110b460010180319031041c802d000c20003048000d25182c005800201c0c940c2120341c852031501304200205920501e003d406001d13200380d448014005050075001014000002948000d002090007410015180310b034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 862669928 1250 862668678 862668683
    0x17070303080c070305040302120709050a0903030c09050604061101061e1a13060e04290f09040506010b03100312020105012c040204050a32010602031e09010e100c 71
    0x205420b031990400348803940140d10004000401c108024401820050002510ba1076a00d00301d42007180c544601200b40c4070210f0304d83c180e095442510105165150041d4100d00c4034a0400700d0450b400d041c0800d40303070b1055010355810301c05c20810355038810000b580403200510039484501000842245d040116100c2482440344140714800d54188210105d01150200e400b07400012080b94980b4400b61130110301061103940c01943c075890000e080d80300c0944903805080100600c1c5281c0c02910410480d44480744100c4d00804a40040200080c2e00050442c196400000d600703031a55621401003103000300036003000b40402944040402c9080c1c054026a0695004c10254181111000c0001d415030200120000c2c80c030175118041809400d259201c541c10010740100402d0740c2c14284004c46c407001c40004080b01840460101022003256900c99074050085803025600d08000b000c08840002c04011035040b010800213000002d9a00a2041500152000e0300c05486c1d9101903070013405240421805 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 862671178 1250 862669928 862669937
    0x300b310510050c030903090415120c0603050702010e0703060b0307050a062c010e090601050d090804080607020105040c170312180d09080d1407140604060f0b010912050717070303 78
    0x100780304603401c3c03007524860001c1c10015810300381d080c802c00c0050710480100e6081850300c0310022850806030484950250b0107a4401e0051501d846002000c50340e00410740d404591600c0301d100400540842e10b007040b00d8100101080020315100040c0c24058280d000550104519100140e6a41c101a513040100328034400c0441407a852500c103034070300d101426054001203d114030b003001e07031802080c02a0012010300d0704a04000d080d0503404207c554400c415105460089000c12010b581007281c00d42c40340961009124600702940c48012110881c0140075503c580600805403103c41001030318408451010600c00d6030a00c0001d030100d26403001d81c03100301b0f806148580f41e0205c1c000c1300c2c0c100071541c450004012002902d201150b542482184d0901d00e80420403140022841d040c20103007603a4800e070060881c5091610740300d811510b8403c101c1c3c6040d0b040102c03002e00c60b0f810040b000c085900702d100100551001d40303032141c241000c40e00310301203840301d142919419610000303020064902c262075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 862672428 1250 862671178 862671181
    0x18101a1908012c010e19020417012007020603071101140114120c040c03091709180402010c0b090a1a071107050306040305130305030301300b31051005 66
    0xc54101060058031000c0700358090b18010002046010280c59002201c46c141d40d1b035180e0503203a28016a40a6804200040c4201d440c450f801c0d40d082c03050034503540d055549004800d80d1001c2c020202c0c0a2800301a125010100008040d18010640c200320103441200130070520101c005c036001264401e001d0003150020603052540c8500b045020b032440380100200601d1000c400e001040054514440038404064a8408000000e0f000b19400b40741ca01000a01c0380e1074502c00014010b258a001034000b60703503001c007004e100260740c01c24280024030740c00c0290000707940ea03010001e910708121450000d11140d40100100d25122500c00c03401c0c000c4030640e03070311101d02104800140e030300e0351540981d69043e08a0408a00005e009800620b01101c201c01c104040341c0d034035100e10b8110381090b88100c6041e00741c120441d0702005e051140c07040d00403580c1149482402282c0f207542d8900390040074552800343c0b07204020b85024501c0040e00343c20550350005045015180340107074944001d0851080d4050030f100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 862673678 1250 862672428 862672469
    0xb03040312050a2a0e120a02040e0606010e0a030b01030f03091e03061104030b0f04061d1c110a1401180317070215040305180603010306020918101a190801 68
    0x104c0d036030f0041017681e818403580d03100000c001c1c0814103484040400d01c01c4060210050300c0d1406030424902c0180c0c058440d620707094001411001c0c07143d81ea18480d2601c02001c0c000030351204101410f407038209204411202551500f540c00b2211500a44001c44006001036948008500e407007090b248a00c42c1400700098400c0b030405a4026404020701c2000607070000703004a00f402c0401c0354020b005010205200c44801c004038015140d100c0502c50603003110420418240700c0000580000c9910b03c0c01303040362654a4049903c4410a16000700071a15010000e44060004d41010a0054101940d41d030407940c00c0c03038050440b004950000000c1011480050348044c000f00320004003070180b20600469a035036517011500c1d6030001c0d0307401003843c00004c00c00580341c4681d005980030310711400c80140e840d800241041034074003107510f154141c000345004000701d848120010328100c440c940808412640e00c0200e0b2801e9005e50200a07410b6400c0b41c130400c42607640900250304944407039410b502c44038800e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 862674928 1250 862673678 862673741
    0x105040c0618030f0807080c0f0d02150604022a01150b030106020d050c2d0f0606030d140c060406060e0903070f080c150108031e130b03040312050a 65
    0xb03084006021034241020004990034121242480d48110001403038040c190760f50b42400d03001f04540e006140e001200c04201020200701c0d1111403180d0b400108010380c1032041d401e041401c0140003e00a94020805085484400180781846152000812064040041c20500a09549d50344081c0d1001c0c1c0c240004981c1482c20884e4140c3d0500d9019011000454001361215803102190b18001d110f001d400d41d2001102c4006000010021991030301c00f1007141070030b1458001d00903c0c54200c2d400c2102403000a58001401c050418100c0c10303c00d50911442220700d030503004a1161075224020302c400c1000300b148540c09982074582001c8400460748400d90071070750700c3c0a18000180304501d001e070014085050080900b0186a00200725042103a6032102c0c180040c20a0740091055880413845039000040d112942c3c0503901145400750805151000140c0c00e8003081c0306242c0b00347c600002040238940316010802010761140003c1c0103606201142e280101000c0000d400840008d0300212590a502c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 862676178 1250 862674928 862674947
    0x220509070309080c030712081f050108060d060f0b1206010f0302060f04082b11060c07050313060f02010609050f180f0f0102030f01060c02030607120213080105040c06 73
    0xa024200180d40d505425001009855015100c0e48028000c00081c1302c4100020001140703d1240a01030300040c4c030002e0103541c0081e103201110340301000e400c00c20740b08015072841141d0302460141e07010b40318040861000041804068119818500524030141c8250003c10141d00c0a4509041c2480d660782407030340f01c05082c0555801604040020005450321a01412126a151103500c0c5841d6640040602d4a200c44821012120b20324000c58189038071035107005094141170070f00d070006400700d98003180c460301b00030606055400c1c04a224014410100103031100c181602c2c1c01c450303980341c689402814141100d40d0102c010b40c24030388086400e01c054026980141c9003509604603d4a62520210030b4481400403e2600d01c01c008d642d20030150f040000b403600e88056000140d89007010481000f400c00160090014001461040001a00c00040e02c503801180c624009428aa0181c8558040c0c8249a036040c1c0c5030003148400700b85802d041d44441d0195200b0711070981403070340c2c411090310200d82 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 862677428 1250 862676178 862676189
    0x1005041101050307170702010216030804020909010507050d0f060f0305031c14010306180501110705010b06030c22030c0e01140a05100332040b09010912031109030d0522 74
    0x51141c04201042c111348040386e04012180009401c00f1500204c0342100c4242c800250000b4810300306100550810819158105480c4d034004e014034906010081c01e1842061084141d040c1e4a241e0382e910100c00f0b0340480054100804c031074501559904101d6130340d4120700d600d1178100184071700c28480748110703104484001501c0001001642c0c60f50300c0e0301d002091160b001c005140348040e00c4c800041c0707080c400d000b4802012411162900c4c0242025401c41d0107411036035000328000c00502c403808001100b0b4450b42042c80b02d40f0a0413103058205441020501c0e80300a210102c42035005c100b45052401140c16101e48007445140807030712008000d042c941c01e101d0913030070440d42070703240400910a4005000b0b019419401c1280c0352940040e05001c40415195400ca00071102c090100f00070740c0062090308030007402d009100d040095120340000a1300461701c4000c2c141d88d00510418002c00100303aaa540c18010165904900460070240035688801505460410076144040e40c10440d0500b010690b036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 862678678 1250 862677428 862677437
    0x408032203023d09060e09100314100509030306040524040c020c0d0c050102060c1c1d0f07080d02150c0c030403120f090f08100504020f031005041101050307 69
    0x110079a1080305a40c00c0c00d03c0301c000c0030488031a1030050742c0b00c00b400000c1d1440a540d440c0101c80c5050310003414010b400344524030580109080c8036100d66150301c0401070b2030300896004812a11402034a2038001c8000b0804181401d107400c00419603000b0000e18428407082c0c1c0c1c28042651071003050401c40c42d065090150f6034101070342501090130541c0c00324070492070f1401101c0300341c2d440301e0004a403031004003c100c8407214209024070071964180426a0482083e0069505000d03e81d0071f040024000c0c96800600b41d541ca4805d608000003070514203106500200507220000780c1c0c0802243c89139002d00070064248540000c0d40d0800e0710000c0e1030384800e54004840070082d02c4084511059601c0f03081d00c00c4081c4403e010100205420440b001d1607035159131207030100c3d21002400a0480c80150740030400c0160040000c11010340d01141011403003541e0800010640d450344001190110480c810b650035128004a002000ea800d80c0210f0245025444407400e60074580011501440111454000038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 862679928 1250 862678678 862678699
    0x10f090608151801090f060606030c0c060f062303070b0414060c12031303030b0d08071e06020313061b0219050f0307080d0f090b0705070c0308040803220302 69
    0x504204510780d0412608a08140c83d1860041007509585600005032080c113000481001000820301c140d400501391418144008000c030316010b04100b0742c0400c00b620084d190641c00284107450381c401000fa00e0403604100c80184070303510f80d5001c16600d0882500900c0b8900021440707030400015541122148802444211001003d000720b51300071004417640751280070320240d02201640059845007110050166001c038240c20002c0584103c80061130007803552504c464042030701c2204551200d80c0011f10100705040c00240700d1460289244003a041c5071003c01440300c80588408007041480c0144001d119401c0a401c0c065442640c0303103000c1001da0b012550300c0501040303002c51445d2090083c002d03561008168924582190f100d2101240c45100025a5910081892156002801e144401007000307500b207580d40d141c0b06030003070303c07030001d1000224001c0300300909044080c02842c3e00c03540b40d0380c880d035860414030341d6500091712072900d101c2070300c0b407000c9000d040500d503030100c030340081010034803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 862681178 1250 862679928 862679953
    0x1020d08060a0b0c0106051513170606090411030706030f0f0b060723010e0a210c08090a0f030f0b1305032d0a2d0203030c0a0203160b010f090608 64
    0x1654001c009413607095481d02c01c0082c15940300100b000e01c03581158803881c6d07179008603480e0039124802c507085117410b280c501c010007a050b54001071165200505403150aa5526241840540850001ca42c2e50307040c40340c000d003c00d075280e01d600400b03140c03c80d41c00c09212090031071030000103907103446000507040345041c014140480c90300044042e4100801e01007002102c0a00030003401d4803c0b42c03100742d03429030000c4010b4040140e46100b802044459203c428a80d0111340d000418040e0481000b4141c0701b400314043e142541c45282400007003076132070740032545550790b450110462200000280c44000b0308400040e414420540040106940013019510300a00c00240e000d00c02d82d841d04040f065160110480b035541c04040042241d809561070384001c1c1070304859188141e101c061600004c5200d426001070b4519000400e1740d80000d002c00c00c036515035000000881c070b10f025128054008907004c0c841c1c041400980602d260585105021814440340c4030621442603400a21a528540d07021480c224078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 862682428 1250 862681178 862681199
    0xc03270b07090e19020403021c1b080c011d030d0201090b0a054515150303070f020f09070908011505010815040b1e033c25030201020d08060a 62
    0x180c130b0880400060600303071290007194914400080e03e0880f000780d01c8681050043c0d6807405034008034084001e00070b050800340d00b80c1c0c841a45116882c14451024080380c40c44544e041c00180d80c10026086600307107514688000e004e0070380300307030142c0e19203d10001045001d851801000e1141384109000b1410326a4021610400303c010381041007164204004100044014110b002d01140b20780000c6c2035074468a00364400e4104050070644660700f00d80860106078a010054410b80d9270041e0188407620440c1c00402c401150300300144d070780b017001c5004004005810030440702c2520508002008031000740107542001102e00e0090324045580d40c0d0014034100b50400c81c0001421006c0c101044805110002c01c41e940c13584141e442c0161046a000505400d041040050350404182c5980101d40300e1202c0005012810030348110f8420044502109004200414110890950a075001c5004661501640e4407100c0c04204e005005003820b100d0381a10901115000764801045c0da100d06e4540402c500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 862683678 1250 862682428 862682461
    0x18020919020c01060906050909070509010506072307080d0809030d0b0105070f050606100302041410020a1208061302070b0c0904060b0d060f0f180c03270b07090e 71
    0x803245a0208801040e02c9428000c1c0002803002c004040b40d000d040c03c04002000c08020144462a405120104080c0c0c1e50b0006440c111441030b00c01c241d0320680741c184240c584108080440c2000c6610510580c880400a501c0040350244800c0c0d5500c42c2c8881c0b0f0840b10602c0958141c07078039903c00e00c00d03071078202c40c00d90004080c0c1405040007817038081e2a41d41d000c00304250801c1960140c000340b04214060501c080c080f01d00d410286002c602e45414000c6060801110110b6180030f541c007030b11441c260302d0081249103100c98001d00782851004a070308000f004400202c0702c1e03030300540080e801f4000406181c003da800903035100441e1042541e03403810710750041d000740c00c009030f005480b8440001c002c41c1440c001d02c0d100b090624040f81c0d41e42000c10301003600601d0344c000d410f8040400b008118a40c0801c601c40100440044003048000f00341d04103d020700510a41447d0325200d8240071000d2250556880310a42c1c412801100140c0e6040f0051320600418880c0c2040503850700c0015034012402083d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 862684928 1250 862683678 862683721
    0x3290603033105131e020a02070b0c12180f09040b06040c0516050708010e0d08011404020702040c02100f0509070509060628020f071a0c011b05090103180209 69
    0x300740594400001d030707407840d64614a01c407041d514501744525400310500c0044100d40c1c0340d8190b1514000380e0300203544407014400c4080040002c5241e180141d0103121fa111000f015003480d0b40c44282005c00780d01303800c140c1c80c1001c0c4070703c0c040358422410b41099040d4602c200d401065840996a0700810300004e80f82c1e00c1e0a0b042027100070000c0c9412100c1c50340800380502e020700d000340038160900510608588403548510700e240d101a40f40075016070711412030303819070b03140c1680360b015030000c0c50100b8003a0040302c0c40290301c64102140c41010a40c006810403250f911b03807070144140c104418101d01101d1003551030309080d80018000b4081c3d42085500e030754111401070203a500d40b15070110500708041c1c3d030081c140441c00d03c07403043c40c60b21941040300c40c44501e1001d000d010103a117001c00d60342e01c0251000d021510030002050f43d404902080d8003034030054135a6038603a40352020841000345540d000b40300d600d01182ca42010368031002400e5500f1881241d0103007507074000780c40702c074103001294418540b43c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 862686178 1250 862684928 862685017
    0x317090a0b0910112a1009080307030b0f060415121b140a210902040c020607090902090306061507051b09070e0a031101090329060303 59
    0x6000000d4070064810744100042000741940e8500c06102c101641c09100c03c0381c40307041040c02410003c0064180100702000901c425000a00380e69070031a00305a00000c031128400d00d440601820302c0104c41c005d40c424031841d941048000d410a0801002100720b80445801070020302c01400a02c0406417010705003411400c0100c2c5140e0744e8040d00b03041d0340c00c072980500000b0003201d1010590303410a0004803641c1c90383e081d41d81021409580100980c945805238441c81e440f034280070f4480010b80d40031482d16600603005200c103000b0b0180207940e5a00035149900021445a0001040714181c802e0303440300c28000380600540d80303611007000082014140c202c1c008420030000c01d40018000c01c15075841c150030502040d0582e41810400c0240000140041e0501000c10340c9200c0b2540d40c51044019203500400041e011030300200125505601a04010308a90724170384411804003042200e10360a0008184a0605503588000d058070b90141d58443c8511100c4100703055500b00854403428041840c003d031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 862687428 1250 862686178 862686193
    0xc09060d06110403020406050102120d050601140a0305100503010e3c0a11060403111201110a0302130f0506160204090605040b04020f03160e0a0b03060106020721031709 74
    0x50710340c01c46868480d182820500058200b085050034042c0c400182004d0000e0001e0041071880c500c1d251098100c900c180a990300d0000c0c80e668080c0c60700290a4449014158036100d1282025000303102c01e40b648a00d45901840c00601c0d850705010324034030140c924000c3d00c545c3c0d200c842c11511550304c42240000101d0500c00c0c07482801c45141420801d580680014214200c941c204400203174034210700c50380103003002c002c14000f259030001d29002000c2c0179201c516064601c0200a4010000d4226201342c2010014a1014160f41070700503204662000c3c000c1c10005941b460060010381d9a8804d40ba0000030500945040c905007410400d00c450000d031000c0780000c000e50b00c0d1802c941040383c0c211031a4614105010950402e40c80b42c0d01202c40c00d0b80180401c9685981210150352030f44141241c0002c25030001b000140745410032040b0100203002c603a00e650310741001a45500003070140b0070302e0707101400540318000600540c0008d207030b4050300c54000d01ea4081040181c8020000d0800610344200003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 862688678 1250 862687428 862687433
    0x1205060a0503151b07080a05210a090b01050405090c01081e0c071a0f0c09010201020d0908040302011103040f0b07051603110420030a090c33050a020c09060d 69
    0xf040d0070b085040d4002d400210f240001c0b1401603104101e5100442d240300b0310000c00000e020008403480d403c0c00c1d05000307403101a4030b0604401c00b0011003900641e400b6a0091041c0311205410481c00640719501c20041a078a075020701084800c1120032800f03e80c05040c400f400755024002a45c4c10071800c07400c80102d002013151b10130003000c050f01e0f0304038201000549441406051032030f844803001c440c05666140d080c030a000c0000e4000142800900f03000005422181e03031b00075411205a510741c0c60301445805414180b200f210380107480147e0100d000c0d0300c01150503035004000c0f10300355009030100d41600c40c10101d41242c3c0c4d80145000b00c45510410500c100d406814800c4440214811828401000c0d016001e00c02a48c01c10050008070109010104c0c0c11801e28205480c2e00c002e2110340003441d010305091155078800c1a5000c00808089031400414650f0029100711156947d00079070070791036000f242d00300c640307109640714000140c21100c48480103161440406400000041c02071005c1c0500380c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 862689928 1250 862688678 862688683
    0x11030408030a1e17100e011502010b0a061e11030c010603020a05010c0302062a1c0b0f130f200c010b01080f0a0e0111070303200a1205060a0503 63
    0x64016100951011850190099210504495840070a024140b4000031400b020308112440020604c403030380748800140e501d51540314000010802141601c002d0b583d65000e41c1c40000020314040015403c1191003041030600c40c40c1c607022102d0079503c0416041e101c50445000b00303081000f840400608058451385d00e0301c00c10207060310b11a40707000000e403e407070b600c100b09848080344d20160600084002c07420110b81c00ac00c01039805411011001e142a104201c0281100c503001c040303100031000422400c0d5aa48440141010700c00950401c004405064040020300c080d120500c1d944110000d4900b000d054454010020400c050038010031000e42c070307003d583c0c00b14501c00041c2c2c1c0c00000124010000312024041e404144000b0b0a14900f5030800003226508044010030b8019601e031983d0544550501c2540b111004460b68001107480e00205d01c0c0c0113011b003401400034914210341e9903110705840214000c031006a00301d5204c0e20703100280d94850324003500005000c0703648a0301d00c0704001a1a00c0a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 862691178 1250 862689928 862689937
    0x70f0503070b01060816020f0c0618060f030a0612020609040b120d0c020901150221070605010608010302190b09010f09081e160308040b160f11040c0c0c05040c1103 72
    0x2500c805e146403410b90712042a1000100103042150301517403944141a40206141d000a101540ca040d0b4502ca60705034001150040701c03500b070304018002080308222400c240518090154800140f2400740e0f40c0800b2498101e000501940c050300400c091080c610741580001c110721b4010708407500442002c6c01e07075401c0803540f18030500412103011700d22003146008041c0710302406095003084030030404468000d548521a40e042c0100031076400d926880708410718191108c680c1c2c40a01404a5a120300006050200030320041b401070070055030b0700e5042001c030600703141034644a0311400e040c5144207004640341c1d54103400c1c1c40180301046801194007181442100312a218020b90001440d644221a45c40c1c104c0c6400c1c4440c0c01d1403840024800101e011048900704c0e400301d80040d490f1035110487c0110f010300002d00412901c0d501019508002c2340300940c4070442e004030780402901001440513a1813404100740141080d107010000d0016217441c0e403000c0b0065603180303070090100406e0122507203144d20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 862692428 1250 862691178 862691189
    0x3060a02040b04060c03030f0504050106180203130b041b06030c091401020c1314180f0d0e0103090317071d0316030f0303090b0f01030506130f0303110d1503020411040b070f0503070b01 81
    0x445800038070200001030100d4542c0c001d07923b400c602c2e6191540c07800d01490b01004c00106103036401c0c40417400b0703c108000402d809a4440c0101000503560b03620240040103450802800301d201c0c403100040100140e2801c0b01810030603009004146401c0c1c041003600d41d14010701306550b0f0364450364110310b02c107020380440c400c8040d1012000d0034820380c50403d1400c003160340341078130b26406142c3e202030450380f01e01304581040003800d0116100d4007d01c3e0a440040b402200e510f410f100c003004112446074000700841c9009482e402044000c440c0d001815161140c00640b0104c0341c1e60400c04200180000300350703444860203450009180c280517a640b81c880a0b054400c4502d2803654801801841414001c0075000640f14060844c801a16541c11000e1000080042c0c01e00d903845a109074912521421102000c81440c010030408483c01b1076032079070405500040e80541d1500c6403103140c5000d801e0272181a1206081050304009059403012607400b0846011900c90005100c0400000c104400c500d02030030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 862693678 1250 862692428 862692431
    0x21006060503251d0a090e161509060507060f0504030818010c0e10030b15120108010504020a0b0d020915180306191a031b03060a02040b04060c03030f05040501 70
    0xe00c411000d105284110540f500d0465000050384030580050680c4010b1003001401c44d08805504001072102040764001003849080003134503105400f0100f41e40c1c040014031030b0303c41c0d8801c1d10b036140c4219100400e003004011425418041c48080c0c040c4c0301030480f2500c00d80011036080040e100c00d00079601c09407011001319203504d05228291103500d44c01e00380100b610000b08906507a05400400c2030000320001030060030780c190915034841c42608030007001600a40383d4000c3d140849042205a8410300d43c921010480e40f0010440720b4040c0201402260001e14480d43d40b4100701440295600c40f80c88050003030f030f0030020380800761a1a65041c1c0031401050382c00f5140c02c540300c18480c590b005911038521940100003040800a1002c8501c901401a41c5c000182210b000c507200040038071024155905120b010211021b1203001c200002440c04160300b55000d603282c80e04043d00380d009500941803280d03c14441070015512841000c40b149000780b80c04540c2805040d9010f04036201590300f550303540d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 862694928 1250 862693678 862693681
    0x80406180b0c060601030b032a120a0f140319030219051216090b07060203160207151404030f2d080313021206011514040e070f021006060503 62
    0x18800ca4084001001d4854601d460300a851590390384824006084034180b656500700c1a0564030200b00340c0e100c41a8a0450b4881c04120030000805034401c03038140762007500c040e54004110240420f0b00002a940800c0c04040c0c40956610600045106001180c0500c4144000b8407000e087c800c01d1b4040f0490380d280140d1b11284780e0090350801a851003087c051280400c03903000d0b00c9500801003603004285840700700c02d81200650840d110060303507106001c1c0704004950700d07086c04110b070300840c022001d0780702002c02c074000c0800990301e07460300344100c0680c910105c1941e5181801050f10344818104130702401d140035265604c12244805404007661a040d805402070440c000500300042412400000d60802c0c10041d580c13200c05202c0140651003407021500311108644071081e940d10000c00c9141555890b68403403c000310380403408207601c030008420841801c01d512024084405a404090b1807102a0f81c40103000c0e110700140800e00c00451203181c180c1800c4400703910510020707000d641d9649649 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 862696178 1250 862694928 862694957
    0x504050a022104150e0616210204053105040204060335180402090d23070603020702060d1508010204060908011a09040b0a020d06151e09060507050703080406 69
    0xe482030b1503804d850540c0b03000032000005000180c120f42c040514040841800703480002221365031300e4010381c03000c0201d2070080c080d10701c2e0039500600141d81050300d0495405404082045410030b0000310240d00d4400d500f201d0803900c103550055940135001a00215002c0d40d643d0b9510707200c80c2005281040700d030241e441d0012460807032068030b103400b424082c2141005a44007080c4402e00394103609504c12640001c1200b91a02c6828064902c2900410100501002442100d07020600104003070040d028110011800038060b109032802250050422400d280181c0340250047c1b00003c01e1607590148880000740646090000744003030301c09a92811599813803c03030070b2403c1d83c2001a075080249600010f0001e1920749010095029400a14004943d11140b0300c440080c42000041c070b95203410b1040106d0b40002c031511014019045a44407603180e0710701c150541c1e41040d042ca821700058254981085800d200c0c0006d400510b000700207035060281e595444800d81e40c0b11340c1c030030b00109003103028002d03c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 862697428 1250 862696178 862696193
    0x1b0a03020901020d092103140c0c0a0603060b030a0b0619031505060403021f092103080c07050a06020318030c070e011d0613242303070504050a022104 66
    0x80307901c45400c09031441400c094090101341d0304039046c0008104d217034480500341440341210105042c001041e041d607a48400d204241ca9042000c000f90052480350300006034107119110310401ca8503440c0b0030b40e045469448001c00900140039496034400410b1002d02014445079805000c15440754a00041050680d02d00a40300d0b14590300003881003070180420000340e1111803414080c003249040001c89040310340801c1c3d40e104000c0d0021078100c4c80040507001081808518080c4403030003900e500c0465504c525403101280b140c0c160003040341d002586001c0001e0000c4d00a140c11400808c01500080404031090349181c200040000c81603000ca20700b00a40d013007500c2603e000d0b00c801c40591800b4071207070400c0e1a450a0241c0000d01030306c090386480010f00c1c0f1990045074410b001207460040004200c50200c0704031002d01581390150392040480704444000070444001c5070010b40600385142c80e00f0308000080800030010740c030641e02044413442c41008038032180c040c00c580c42c04a00711801c00703082150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 862698678 1250 862697428 862697443
    0x12030c0f120c020a050d111903080c0706080a0e1c0219051c0302030903180a09020a020d0f090609030204050604110307020a14240a0f02030c07050115050f091b0a0302090102 76
    0x14000c0c201c800185001c07c240d01c07104901030400307a40000b144400c041d83c8001c1c140b40fa50000d0011400425013103030382c09001c102d403003c0b140c81d035950391245d44400001d00102c840c1c0c9200d4504540c005a8100300480c0d285039040414941801940c841810f02c11101692500d8000100c1f82c0360083c1071101e01d4003032813002025a040e100d284c1103045180c020b04507660b9204001c00c46109110b1a1544241070351211054000707000901000e6442d0001d0710000796480542d4080032010403546400171000b5446a1035150440360350340c0d543c8098500c0d47d02880010a03002d03002c1508551140c0c0c103a4481d900a20085004001c59801441e12410074248025032800e03241213500e09070010305500228030748a032007040030114406401409034540d881c84000038218510003c0070180007004115404200d04080d05129003c0c00081c08080341144940d191b60340140111980100c0107803140b45281000c844140e4170500d06240c40540c429110740ca00700c140c10481c0b5020000790001080c0885590622000707 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 862699928 1250 862698678 862698689
    0x90e10060e06120f010f020705012f1602040c0c1703010e0a020c1603032307080406081b190e041b14091507060c020712030c0f120c020a 60
    0x20401507051400803048800094880343c465441000c140258a03400c0c084000102c450200030071401c0748a100c494040c2d00a030105884a518044c6034000d515008008440c8000c1d1402c0500e020200c1c03001c0036400e81c3c002c90326684650b101c448040340161164443c03100480d1041c3c81e006192080f42c90301c603d080140403214402c1100610042264555008045130811001240961076100c40c08480740741c07100250f41c031b0711302c00e09420b800024540c20040d141442c511000079200d07980c4c00e40030090b8070f51041142c0180002c1c1c0c10801041014420010140c00940d01f0100e10800c4411440b030304442d400c0704401641d00341116001c0c4800300c1e08100360003900e4409590920454103c9400307245125a00f03090b00c01400054030034010444d03107004c201d40f55141d0080c102c00c1800030f46502001070303411103a070071504945005030b00c030401c0b4000100300c411611550081c410300c4c1d4199508603248030009d08204c1e9501201c00080d8009880100c410090796407540c4c4220f2006c1090040000c0b0508540c0078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 862701178 1250 862699928 862699931
    0xf0601050a0504030f030c060f0501080105010b0a0914010e03120307090504110304120e1504080c0307150f05120f15040506010e1c060501030b0a060806011206090516090e10 76
    0x780703140c0325085820784044980081c0c2e54001300b40075041c181c44000020f50011b0015181601028030f41219a11650584403810000c05c500e03a282c0d40382012522440c102000452450794041103a040710300140b2070b10a4061501d86660902340001c0381c5001c004031322001c280c00b00441000520707075200030341a000f003504450600c0b0351981141c0c104528400074001604c000f402c000c0100000c0d0040304218412480908a001c098a20100f4142580c00034014122203010f01c3c80710040d01d2400240c150300723070303502115100e80176400a801a076214500a0604050080a0284040e00c0d04004c0c4050310800384030700c1c0000c00345003e40c1003034012038085045a01c00c80c0340c001804810b980c0000b9001000f501a1440c0c145001143c032680360115071140c0041100313080c84002300030400110b07a054042c2c4540ba10500045440728111a203480c801d0103040e11141036000e8130404569140c004041c1c4502400a5884400c00c0f00365420906030241c000c2e050207a01c980c0d2040500d54100a0003200360b588103030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 862702428 1250 862701178 862701187
    0x20c0d0f02030a1d120f150109050402210a1b030308060a0b0417030903010603080a080903030601080604091a0903092403010605250b16030504120f030e0303010e0f060105 75
    0x24040d00c40b40304c81034034451644040200c4500f039110101c81c00c0200c9032031402c480054450b0442d103a59010354803448200c0d0800d0030b0001458080034043c860003a5401010030118031201404512005c00e854555151846444001070100d00c0c070141d842c10802c00201d1000c0c00c0c03802d60801404014002d003c1341d01036800700b0800c0090858003001d803815241800e00039030300700b01c0c00c04c11a441c5000e100c0c40560306510b031405c008208000400203141c800202d4461480591b2008078098690004503011404240140c000903154509903014480d03842c4200000381c440c509800c003c0c03d541c3d1040b60214080d52000440b82450b24000d00c850f0341c200100c689000c01c031103202c00d10008600041c45000e0074014049011180310007049001c0324444401c02d079030300e40361000381800c40310000d00340c41c0c080d02418400e4450403014400d0045a104a800c02074500e0001c0301c1c0c03901101c8000004004a0800d0369031b0350415034408050000318000d041c0400607522a04011340c3c01302e83d903400505440c0c1842400c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 862703678 1250 862702428 862702447
    0x32009060f0901090c020c06040f061b03020303010509131203090311070f050d0f0503181306120b041103031804050a0519091a010b07030e01080112020904080d020c0d0f0203 76
    0xa0b5803419035003c11004940d0301e200241c240d140903203c0c4000344d400140460080303058020041d04c6012101d00e41d0341d40c0c0e04408103107000400b03020340500150060b08100010700c101d003071954203603030000400c6000c41400c0c01191600108140c107407a418000035110459003051651002c8954084109100581501450700c40802201d1400e48140360180c520a4129028408404610407525400c041542c1c0d65907520740e822100581d0b040790142c8074200c003120b4500110440c1c401d80c41078500d1b075065000528402e440314250500d000384122450304030005080b426840910181c51148844050641e1a500101c2008243e41008140c810340500d4030007000030140302140343c24408900e585001900070624100982d0303020142c100348030070b1400e000002442140041c002c04034580217030b84030f0041c401a40c0045a00342000e1182001424a100095003d4a0030030714841d006031182070710034617104400000e0300903a000f100803101d0a82284014681c00b40d000030240080110070302c045d41c900744411703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 862704928 1250 862703678 862703689
    0x10f0f0501030504080c011d060106210207110619110604030903030f180b031801110f0a1e080108150c030c03090f0f06070f11030f13032009060f 64
    0x244103590425440d040800c00740242c0204840c001100000248015001d4501c018454094040074242da84190000010035a20540c2c0c1404000d02d040c4020b0100c14036002c501000c2d4000038010f42d120041880580143e41d10080185446021611400001ca09406000d03004c4800422079940b150004010072000a81c040c00b5030003601e926040150749442041350440300a032210070003803c40b10014802240c2c9044a80213144203060f410b070200f954090071003090b400d0300c400e064400700c2110b05100240b03488010700050714001d02c10346410b442c22004405c072495050308201403000800d000c1c80050080d2031050144d120700340740d050809a4241022091070140707100007044480124400300c04145203040a12000d021165403034116008003420880745511200c1c01d8800c000450302d01ca03100c04646000d80d010000c55049032000d075040904401e0f09450396400401003c109030112500840003440080001c0c8481c0f0300e015681602240300014020880005448180b040700c80309000c05107660340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 862706178 1250 862704928 862704959
    0x91505102006070c110f1011010e070b0705010b030312010303120603060e0606010f1119050705030604080405150412060f060b0a0e04230f270d08010f 66
    0x1520300002070502020316440380091101d9030300414000d040070312960030340c0030034a4103405018074a00c95070043c01d807040140f9040d000e100346400c0b1080e8042c1d20013860203081e410612079864000420300410a41d0355900b0200190800d2203c0803012079090103000e400d210301013841a0075001140741511010010701c0c021014800202040007a01c00451803c4807900030100a5134040001d1081000424100c1d44401085a2103400a81c0308080c14140300c1c46441e200706a0040315002d00101c0450601502000600d0304040d03c00c0d02c56984000b030103850422809200b58010303d10651158103142c1004804c1e0340d01c20503480d1050b000c0c441440038080710041e0703480e066401080042d000301171080c3c0c2c1c005444240e000100c042004520b00070700941115202c0f4480c42c046500300b1026044c000300c8203000b40c50381070010300c0b690000c0000d40365090b030511840d0450441c18003000b100c1440d514941030041c0c81302c002d10b41908095000c1c040307980c100c00014050407590704007510160814048000c0000c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 862707428 1250 862706178 862706209
    0x40b070203030f0f130b1e061504060c080c1203010303032306130603151d0106080604150603120c03020105062d04180c06120903050909040201020c0316091505 70
    0x5601340030a28810755628040207003a40942c0d40d498905e406006001d40e2038a078955031008143d41d100107407885ca40050f01480a001d00c0c00805e040a040c103d040b074250100f44803c5840078000c001074650038000b00310070b40c02c08800c508420394030341c158900281902c100c4014a80380c2111400c00a20100d1802c80056000b40c003038603c03100701900f1780c40c000003600303c0394000340c85103075581043c0110b101c054100b9010b5108144030130a40d040202541c500301c0d101441401d5440c1c200d40b0100b00000e40700340c40c110366080d03100400709003141ca03030325540321988041c0041c4000c1041c0d4507040003010303020302035294491412034503407070043c864108959400c0c80071042102506003480d03041a40b5950f40d480740b507400380c262070b0541d4031a901e0314040340c8086040c042e00340400e40603030441d440000c1034040c4042650341540e039030381411840d02c1440030f40074010308124154040e0300700600054908110030085071295408103007486140854440c201c0e42c640040c081d40c2d2020310b0040c4002d03215503002c804d6080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 862708678 1250 862707428 862707451
    0x1204240b09070e061201060201020c16150c02190b03040209150a09050a0e0604061d061b1b0f06100b04270207050d050304051902210c18040b070203030f 67
    0xd0190002501d512a00e0361740c12000c50542c2c000b0401c2a815401b611081c035400044800740c0c10702c00f03a0543c012910303204d0074220f0100d41d408010b625104120a5032441d1010701701e40445042542c600303c1300040c9401c1480ca280c008000c11040d4582100e40942180e50300021620440d07405001c107104407014094100d105032520040313080c0b5a0280e2040700c800c0f24900c241c0700d1900302440c00d03202401c1040c2501001801105600750a10400b1404c607011303441c0e003181081081000d2000070501c0e0464000500700000d40c0f5000c1400c02404d2110040410008000c2c010030b00d0110b01c00300880c4903030340190703144100c1400240080420502e070007010202c0740c6c5a000306c49181901980192203208030050071805031a40d103480c510b030401c4c06540514420410303105010044140101850702c4100040e42c8200b00c855540d6000500c40280c00381c0c0c0c0294070030b85074011125404245e40320380d20442410b10000140800082c8580c0c407a038281c1040252000d18510709021000e00d200410143c01002d100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 862709928 1250 862708678 862708697
    0x40b041403040f0609031b0b0a11030d02030a02090a062a1118041509020d0201030c020109080f090102070905070c0b070203070c14100e0319081204240b0907 69
    0x200420425a4000c01d41400c41c10f0040ea12964001d241201d1380c482103642c4400d0382c1554030010813121303c0105443c440c0364014241054403d00711068440300200302c5a42c0410007560f4031b101c8140c001503200e00780340b400c0540d41c5c0034030701c4c140139560010360700c03490401100f801444001411a1031143d0342c2c407205000054282c005080292500c902503000a9104030840c00030380c064451440c5203803007280215001c41e1100c041d402c0480c1601c400800081d070200305050040c0056020380e104080c401880d100008000d50150340f408400e5100440015040c01e0216442d40c00b5030b0704004450140a001c101070026082a0380080c007408460800200808070000002300341502c200251070085800102000300e850f41d0b2030113014500f1a115040d80142004821100c205018203042070245c8409001440251000c1c0614070701e584000328116030100d810030034000600e100302c12040c000d86c01034020706c0b44400d0101c05d004084503c01401d0980d50b0822002e0a2140da80c500042d0307002d405c9003080d5008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 862711178 1250 862709928 862709963
    0xc0f0a09031a0609061513030f020909011a040c020c09010321030b0a121a0a060905010e091c03020412050c040507170c16050d1d03072d03020a08010506090f040b04 72
    0x45001f00111b12103043e0311050000140103c648460704824021b40c0d000d4800c1e02c42000311803d030740b00100b15a00c14005100040c0b076608195010f280000914410303070340e079501200d00244031040b083c0d00944265200300300f881c440f00e200c21031146280070281010050b6008203804160324804510617800d004111280d0501030080c0140c0c00703080b080a9200c0720030b40b4507199034080c00510190007030120052800c0e0012a2461421101600810041000b040c81a0036501090344401480742c140080503000c2c0700010300409101c81c00001c983c46140544523030007c9009010456030020122800c004180c6a81e8510f00c61441d8182d41140032004542c0d03992090301907000201c51101d400030443e220b100390f030544903684442140085040405040341d400e50040415560700c100d4042c0080740c80d4008c009031507007141c8072941d013904d510761040c25001c03540d03a40005451351955800204903075140c00c10080306180c0000e006502404480244019081507104d42c80382c1036004000800828080d44200300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 862712428 1250 862711178 862711219
    0x10060e0112021c1407120305371e0903030903120201060506070602090a060311181906021c1403130318080c0f0406080a02090c0f0a09031a060906 64
    0x20f0030322046051111103842d5240905402612060168903400b40c584040b89005c1d09914040109030590b0f01c46091142d4201b0800b0020480000796442c0c10342400c60029100741812000550520f58641c83d10300911401442900780540840034100480810140700207500452040c2c150703071b0404002500011081000d0b8010081074004031740c0b260380800c2c4035007040310320b80060103815000da8120101d599a0841a0107654070040589000d0405000b80e0ba510190005450900700004083c801a9040540900c042065513041040184c2240701a0568242058a01c2400000c24942400d02c5166440b0045060101030709242078110010000c0e800c2c1482118914010402d1490580030f450f03551034800d1382c5030400c0c1c00b1140141c2c03a140090003246014842c1000304d0300c00e070300030b0000c6050580c00c01c04a84e000820fa076104840500c0f0740e03c2a240c607440a4030b2003001c1f94940700e40e054294203050180025403281714094900c280c0402289495042d9601c0d044407042d12001c100d8088484001c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 862713678 1250 862712428 862712449
    0xc10090626190b030d081f0306150e0c0301060c03051c0c05031518280606031d0105160e040b03100504060b0d030219020d02030f06070210060e011202 66
    0x814461054050001c501080c101c2020080d04441080144582e10004d00d600c9244601c440b00114001d000061681804c40340c000003802c1c172901d60b0251487c0c0781d58580c4100c90715810b0150807020006d13000e000340540c2e42031894000c100c017482e00d401d6605d8080010507020080314000c0800c480816074600700c64030b142520f40c0a51390410180210166014000c2c201d4000300c81402e03484207a0704201d241c0307091242c9410801f00000180310415652480c0100c0003507200c0e030b08a10303d040f1024081d1100a039901c84c1802038449980c02081600c8800d041329800700b82a03108000507498034040c09442e4504c240200b00d0000700b405e00007000401e020003e001002e400d03070500e4140c044c0d0010000300b9411540814481c500c030f0740b01000341c00c00f99000d000040340704550060250b03106440c50a00303040c2d03000c9101c958a00c0201246450203e581c042400c0141e44060705007140e0242d000c1c0034031a50180700081c036445c0418000c00200d8a80520f0280002043c41007540c11408200900290340360882040b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 862714928 1250 862713678 862713737
    0x120406060f0b0d1815090c2c07020307020915010806010305060303070f050c15121308030118020f120a0e2409010603060e0d0e0306040c061803050f0f0c100906 70
    0x94000c0c03140482100181001c4c6c04101c1d10441300c000041401c55119514030010400c2503d600c84001528541c036105c41c2000c1c00c95801c0d031105000440050b656030f10011304c514004264420038100c10000501503140c00384c40d0398149401c020411403652000010741e000581c01c1244c82d0101200ba00b845400c0c420000d80072500800d040181d12400101d100080c00b1800c1c1045602c01c41d60340d80c640611084007841e10080420303200f0001003100c04030760408c078110407100f5000180307003440460103003a440d030100c444440e0040710301041100507011445491016000030001d0b041025100b6010749007503003543c440000010701c4001046804009620030805594003801c10441d01c442140782c940d40d00c0a4410350b000045002610003014140071920a000c0c642c40545105034606042055500d200f03c0108456050350b11311001003c0303036041140d42001038840700a40204413005122501742010f1034a5240501e210648a07010140d000c200c110850302d40b07207880a01c007001c0c030aa2002000824201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 862716178 1250 862714928 862714943
    0x1503060c111b0108011e090212150d08040513020705060f0906070c0312020d02122e0305060402090c040f0f05090106020c0307140114120406060f0b0d18 67
    0x2400c16030452a40e420890078501101c0d8003107452400600d000380c41c0b03005180010400310040105100c8011085001c0f030308034046596851311003e1850072a0000e140c1d45c20b030303490341c641848044c9078180d010003180c0070142d0748600c036418030b5254001644640e20500d40203a010443c00013166907103905a5540030340c481c05640090030514145000c50744141c8208a00340145004035040c0c5000e4076031855615416111289807040d290384c0c440003504a000003038401070b020003101902080e002c0015225410098408400c446454020070005050741852a50034800f043d0170302c041580002e51603401581100c603040c0030303542c107010b1804501483d444134120880010010560550004028003651000d90f148420340c3e90b15002266541c60104030b940d0160090348040c0a0200e40c0c1c1d0b8200081c1206040c0080450610810320300694400308000640c2100f01c0180310070866070380510f134003e00900400b006e5050820041c0003041c412508aa14140d80e80d68007000000100c1c10034455443d04000d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 862717428 1250 862716178 862716191
    0x615090907030b1003030e0603090703030c02010507051e0c0312070b0612120c10051e04021518040608060709060503130c1401090e100513111c0b010201020f0d150306 73
    0x4c0900d000c0d24001200480c044411451041c140842628421444840100a8185161400d880d0500001c106904010080040c00040740341000604440c9466541051900711968406800d10684a503024480d802c0640042400d03d0302d001628081600304400280503201c4900250150040c0c04a200d00e034012107030310760213074400040030701412000b04003920104401f2160000403284115440c1e10700b00465203d0310b40c84140d80f444070754030900c05000008075201054000070903401c035910351156501c0300c501402c118100390052000800b808002000b907030a01e00c0700640044640d003e850100a808000682d8469170038464250b1a5003040341000199201c6418550540a50540c07034080f4a5020300014055030170144a8801e010715000c0d03003003040c00d01c410408101d0240d501c083c00d16446040e100f44480c0284002c000d03030b078410540318541c400145440c100740d680107110641907900c140480c008200815007100c89517200c6035400103084211141d0000c45c22081d41010344094945503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 862718678 1250 862717428 862717441
    0x30a05011410050a0b0f03070c021e15030403020c060a0302040f032d03020d03020c030408010e1c030b010905220c050d150b0703030b0a0b031f05030615090907030b 72
    0x108418025584024010b540644440c00e0006960403841189001c0d2010003204861900c54800f0b0754024800d171910324070280c0a500004c8400c0e0300b9100305141d032544c000c0d180d403043c507100303c2044900c030b206800c450030351501f83c40c06511819103c0b0614010720000400e1801ca92280c0c0c1110050650250000300607500c80c00e0a10030000c00040b08c40354540c2e2000c03002ca01003100c7c2844801c596242d801850344c40009681180a03400081110072284401d000c0800c0c5001c0078020040804180030003801d002a640c0303840008010a1080e0005148c500b03461034920743d920120100582c0c10a48000e010101d4442040108160220110388114a4400c04509865002c4000c01020003024003d001884604942451016041c4950501004100700c5c5c1000240641c1003e880208003c0500c0d82c0c5a03501c0301c078010280e20880700c41c1d43c0202c2e444000311801103c2c0145001904007a8014241403410520084840c1000d4040e24440c0081b0400074018030001c20001c009180d2005a1203814103004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 862719928 1250 862718678 862718711
    0xb0705010c030c23090109030606090e0114011a03040206040e361f060b0a0201020705060f0702030901210207050c090109091e061107030809210711030a0501 69
    0x3034600d20029040c81a100000b51103014425000c030080c111440c1c0002d010070b03204e031060f8420041107041c04000c03000040031403120703c0f4102c000d000030040402c0c1982550921400c4601c6180d000121034083d80060000b00307813510140420744125031003941c1d43c0d11140006552130065a0202c80d1840e91a0200001c91040040800000c80c1003000c2100708010304017591421070b940300c1130ba034090f444400141c2005d0780e82c2014100010001000069090310750080046941c4801600e40140c0c2d00007030801c040080800007179501003001d1100c1c10403400c2c5204002d48074820344070054100881c407002c22580040c1c003500041d45141080d400c555510452429545035250994828412036001d000041c90607400d024400c0321036442503040c040c10340a83c01a04030540d4269080d91f11955510800004803041c500030300070607000c2d48a10200f8680300e2035681c40c01414000c1c070550399903e12400c0c445d070901d0405a0321503076884820701c030114014001081c80c0403801d00020308250b003071403545214032000d0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 862721178 1250 862719928 862719941
    0x1508062503050903190e09060402040b0f090406080703050d0908031606090201171302210715110d03050105040e0a020609060915210f070905011b0b0901020901030e060c0915040b070501 81
    0x3681c7d100041e030780742c00800040f4016841400154203040100e82340049100f4010240100000c00001d01c85807942d60f40d074130f4200b96400455580c5e010a0054034081e8004040600034840c01c001580f400c800305c1410215060260001045a620f0f1281c8a04581c01009600303801c5d02c0381d440c50300c51868903840358154404291410303406030883c0c40d52001580d01c8a402031146c80d070050001c0c400d140c031305280b2101d898804100201040101c2c44c469081c02000c1c40001902c01b0325a40c0480ca55044c0000c020442d0004c81c94010300d90320040d000c0c0c00580303441003a510701d5001194180d8651b820400800ca605e100098103424003a80080c00d040d6200440d1005090601c0e0811111007a540d80e0324602c00242050711780f50045a00d41c0d00c1041039600c92021201181c4000020b1850101c03290b403995040607050364401d002d6500440e250b841c1c0d590500c01d480315021148024074103030600480c50702c050f1007540402801110680725400382c0f410a02e04440c0241840040642c2c0c4218604105000f02070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 862722428 1250 862721178 862721207
    0x801051f02330a022215180308041e0501020a050703021905120604062306060a090e04120216030305030f0402010903080c0610050105090306070e1201150806250305090319 75
    0x9030764507000300c500c11720500034084d12410500400c1c0c90203062019203480c80011801101195000310110004400c08050130003480f54514450240c14000030f2074201c3d10b0260485811035101c00d0003000881d00c0000c02c81c045a03016502c0c6051050941c98050709400942c000e42c1e00400c04420920b00c5c50b030002401c51240c1d00910040003a00310b008810107241000300e505045150741c080214070b8034585400100480c00355400d00009141c1d40381b9100b050500d04841c140d96110001c0019521b1980510501000e142101c140400c620f0455030054010300000e4003c002115202c00094116400b5409190240d0740221b01d10380c588001030440c035a1600129441030240c4010080060a54003c0041c0e0341825002809844d4030b5440c4c0e9401c4824940d18022507510a000600c00142c400c0c00f846504064601031050f40d001c04d007011885031500700041c1198183c070f4098510829040801820000420178a00e070101e015220761103454070714046d203e03400c003c20003030800402034150050250950b500c3d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 862723678 1250 862722428 862722457
    0xb03070605130509040b04061814060906010605130909050f0a230607050a0305090a12031401050609030703151e060303020f1c2d0801051f02330a02 65
    0x5456005004d040725084d40c0040c0010600004500000c50381d030018181c8010b560501c4480d10400d0721110750190ba00b004088098204400344140100c05228180c0034011508000d4034240745180320803c42e0b10b0360302c194401c8a5441d03543c603003082028809841d404040306d0441c2c0c042e500c14207000101b401007a4000c5545260300d08103040b0701d00b0104040d880785003252185410f0040038201540a048010000b5103140039001940d000074415205003c022080c907a0001290b0b100301203c0c80010300d060b00410701c50719081c0548682581c00007000ea0680b83d0149040d44200c03c801502c001801c051440140b44289008054809442c540d01a400b141e020f5422031388032111060215484031420814010341185030010705500c180203560310841c001c40300c008440c50304580c00003014035404400d07180e030003d10a48010081032030070765841070125a403507003070307582400707411001941d01c05000c40d81158a1603010014507180d85c149214070111040c0307240d80724180c5025880700d0001c1d84048a01007001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 862724928 1250 862723678 862723717
    0x80d09060201060f17030c2a04051015050d0905030909010b12180f06040f06050106050f0301030303110708120f0c040b0403060b1516230c090601030b03070605 70
    0x141d105001d000300300c581c1a88202200303820510f40c4c414180c0144031000300c03403208000020309400d041015040c1100d400c01045640809000c0902c859856401540d01c1542041c2c1841008184d66003010121810300ca24050498041042659240115101e00c005985070400d4071062040c08801051407030800c0390a01c0141e078850140c00387c0c41c0a0703c840d00c0040740c000c0c4005021001c1c0c511003203040b8940380c0100c800c2031111000c0186000c0701201c0c100e85100260100500b00846805003601410b102e0a00e01d0a003403484a0f08944c5001c1440098201070316040c010402c00051412101441d41040d90030341c3e150600c55441e02480c8040d0f600042400c400c80028134000103003400e03601540d22000b00140760a146403607600103007402d901d40a034403007440c2c480c1c0c008140b8500f00901e40858091405c6030301d4000c9080c04e174110443c041d1072074076030a05510111782803500800c11444402e0115030099442d2580c2004900404004482c0c90f0513100315240401c9640c1c001c000b4007240c500030321a10001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 862726178 1250 862724928 862724939
    0x150901050c27010306152c011d0109030804060518010813390303170609010608190c09090b040e0d050d150b030106030507080103050c190906080d09 65
    0x1a00c1182004048a4214002d0002d00e410003003a501c9680300516001c240103440d20a110700710241001c891012480045011441189455070b00784070035086046080407070100c10000e40403c40c2c0500800801c00d00da450300d0003580c020007180014540150700300f6200c90b00c0d01805005a8400000c9103a020100d152a04196101d540a1031142050b28003800c46e07802540d8882c0000680078609407405c00c91015110100400f91810000990003900151009840c40c28040d0000c203010441165201d4024104002506da000309141114194030301030909036950110401c0c00520501000ca4290a00940c2c0c001c23203505c00d154100381c411210007006001281c804201c1143c4007504405196003011840981c21070240300a452031982000010840000e0f20704001d4041c04203401613440b81002000600c403080e40f40c4140c40d408039480c10b05500715410b40c4c40c0e143d5160301000c01c09100d04140600c0308100c43c0c49086440040000b000240901078070b880c00c0c0c58443d80c00c0800d0b24001140309100051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 862727428 1250 862726178 862726201
    0x30b1e010807050607050c06030a0c0801080114040b070507060e010506040c02061015020708100501090b04090f0b190203102103080a0b0d0b04030201090309051203090613030515090105 81
    0x407a08035000400100d803810044c0b1441341c01c200c00685003801f0303007041c0d10a26101e01c00290301c036400348034001030000100100a421003406812240c16030f0700d4410240c0845210140c040d4005403c000c410720681d50b1180122510300c0b0b00c010060000d8144001ca0804c0e00301500810b015040444040c054101c103090200d1f5aa03804580c00f00c007505c881181000313020769103012286c1d0810188150b40441d92240311940c40e085018940b40c5030035686000420490385180308441030420119814000c508070741e2a07180402404078005042483d074440030401c140c1103502d44400144002c80c065460f071806000421189149209881039455140e00c03e090100040205040301a495101d902240c6c983c1080c190081034418803180d004030000c2400c00c04036841034040b03032140d4881e078008541c200781d030305d001030000c41541d00040c0a4040401080340010303001c400e0b5502c00800355401d64583c4e4101c0c5018004440603400038001c1d01a2601200e20b00054004130742c810710492009202c40e0721290100503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 862728678 1250 862727428 862727431
    0xa06050a1b120b0a1a0706060b090102030702040b06041701050f01050402090307120807060207081902030c0d050d11341e052a030115030c05010c06060906030b1e 71
    0x80c0010042e40801e00e10750040c1d44038510348000070344030004180d11945043e2005092811900c01d4410101e148000c0080a00480340501503c1c00d21b1350800e000c150010395030703000e2030100038030640d00c85050800585982040d42c1c0184000300512020b06810703c1054001d00301682c40f400c00c01c00c4030300048bc0790b0900b8000c0b220456400340c010702e100c62a001e40104d000340014000c07a58075400304071460100d0814006410441d004031301295030b9104c0741008040a030103840b80c030410b542040c42101041300000c41e25840304443c5052466403201507581c050001c0c045800b55400c140004604001c19120030955548a140034a040f0b20010b20b045030400c0c10601155002021820f101182e030000803500c851052070706100700c08850b442800c01983c081000340000700c05214504041a00480d846c00340070b25055580100d400d90100341c08c1d6224407241c0d488034010749060240108500d0700300040e6912410051401d50f50070040551030345400004403000780e6a030414000c041000f148241c4a800f04613 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 862729928 1250 862728678 862728731
    0x815010506090909010204180f0c080106091a07120918050c030123030d030b01021e1203180f0709060902180411070f11031e0613020d050a06050a 64
    0x50602d150703030b02000252100180103041d01d54013030100050249162030345d5156016140000b082c008074803c4244110340c1030310643c030100f082401c01007050b81e410024400503181480e0704030490381c1a201a03400c0d0362186c924000d00310401e4a914582c8180d0050420003a101c01401e6000400c0700c50700c0d03100550b0030070390305141e20a10800042001d03501c003013503008842215041c61852040c0f100c1c0003a0612103c803030743c035005c01c0c1ca50340d00c0c800660341070140499010340450200d4550342c040304819650400d000c0e02c443c807a40004007040b103c0f00c1c446140b05a02a04030104c0d2840200d10301d641d6141c031141e2240c0c80115081039030208102c00702d402510884824180c40748207070601041040003a011513413100c44106010800440840d002c0805019250300800050b030344040c0d000285440c0c00c080116252400c90b0804040054200118900303400903021081c00c000c0405500025117401100340b4003c002c0d02c64600b54030100919900428803c50f800030040100d00700021100301d002800034940c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 862731178 1250 862729928 862729939
    0x2033d081b010e041413060501060c05060406110c06010617481b06091c3f0c18170102091507050601120c0b0307030e01021308150105 59
    0x800c1c645512540d98500310b450001c0010881c1d200000c1036029411041d5401440801c0e860011018488030780a414010000b500e80284600400c0e00e5460710380401600040820781c81c0c0c030911105c900c2800a03035030070300601c101703545155a44003070207031001c0315100c5080c030492050301c00202c00503072048201c080c0000c250041c80d040d881c0406807603210300c1d10140016815421514903d414601c0c01e002d000c032000c028034403207084601d600b48980b40c640020101c0701c40782c1c008142030814034100e07048440c454445040110321a00b0707940f455802503440c803030b003186500c001c50f02c1d030703c1030b00b601682e8211040d40a440410800301c01e09003c5400740d080140a420250f40c03103004201411868010150b8103040200040c14004200c0010380742c0d2650300000d03060080081a0102401001d001c07460050201042191043c049655100303e448078031301c2480b01d011000300000b07a141d4003075007101c40c45458001c0210b50f10728220322080d030382d61028000d101c114030030700036503440c5004119400c03030507603900804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 862732428 1250 862731178 862731223
    0x91e030913020d06080115180b0319060e152502061302010905061204170c1902030307050a0503130b39030328050609070302033d08 58
    0x8600180d0b01101c1c407483d030f0664465002400005c20300c80c01004100841d00c2040381490075118603c4a00078107000760001c0c1c50031072040b00d0b950340042ca0131034280765459000c0c04650181040002420003000a51740d60148646500c0d1601c2d02000c054400c070714014650042c022414440e00c505080450031101690150340850703240c018440903244880d10500d400380c403141d25078010503825004250300c848501100002c0c4810488001000128145401d0000b410010032468095684000740d203801000f901c0003040905540303081c000c03150342c150850101e030b0000c240c910306940c1e0781e40075100580400d0001d1101280328900304c405c0790580110b41580030f4a101200d41c000340e681c4100f0b400c400590f5840704404034108014806103200f82d004680102421506c000847c00d43c10710340d6000c0541e68600420003180396694031406802403ea441c00603103981d144040310000158007803919540050350310301200807403468030a205916101032050a4040e0751041101c1e904c58804902c002074070070105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 862733678 1250 862732428 862732459
    0x50c190305060d060f06080d020d0504090507090503030a1e030c09031203020c0d021c0f0c0b09010f0603051b030105010602120307050f030112020a0e010b0d09050a0b091e0309 77
    0x411a42d046031000b01542c60703014003551000e0465400d68518202d0f2911780350300f04000703007050240301e003e016540003400c1006180c3c0002812841213006408456584001081e4002c1c400c1e42d00c50007034140507003103e0f80c0d0850b002002c1c0054881a000b400c6007100081d049444a100b8002e094210007107440c1c80400034190b60b108050360b041030307042e401010b90a000d075510003007042041103510401c54000c0c05604400c00faa4444440c08100441c00303200948190000031944078050540c0aa00141000f1483e01e6141e0380300d000d051400c2000d643c41b0308026020080c8a000f00d0072110001c2c1d1800d031074100340042024103003030710403d04c200d0016810601c0b01001d5985283d00070756118010746011460040201042c0506800a800101000d0115401d810440c01d228a004c3d01628003140840c4003903141c038002d15181d10a088155072140d88504410041000404c145440300707a1000c060030407441e0070001e06940340c0740da9202e0700c2c000642410820314404003004842540d07101404509580c081072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 862734928 1250 862733678 862733681
    0xb03070b0304050a020604170d02030414040f1e020406091409040f05030d09030e040e070b03130204060306060e0f1803090603180a060f0b030f0a1412120703050c1903 73
    0x1c00a449a016a8913039500680c3c0b42401400680140e5403107070380b01d0300303407820f010b01d401030b890141c03401d542c000c00c018000701d0b80f5000400b0003004112008295100740343da1020183c146001103002240b4440003440004683d82c01030300c140d071020b954100015540b041041d007050f6055801382d8204410348081404146c00f00c3c05024800e001e031080380d00d0407540004080807503041040c25000103940c000c040b0058074050140810004c602402002c1081c10050100c4d110300c40680102480c0c2c1100b030310741c011519190000002150410810032000795075030940f0440510455201d648030501c0301c00150340f2007030240700c51200b40c1008021410016403000748151a0f00240c5507a0034a4541d8101c1c1c4110a01007083c0b0015500c00d490120b00211a510001c042e190b44503040d910a030810b100014608078002504031040740c01103502401802516401420400c042d070740040a2500010b1052000c14502d90040c0503281c4c03540e04202560318501c1e44540342c0141515540d4102140c3c1110042911a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 862736178 1250 862734928 862734931
    0x402090906040213150915020c030c01050a022a0f0d200d020301051801060503150f0406141303080c0708070b06121605040e0606090403030c14120f0105040b03070b03 73
    0x181520300c2c04585c131203150380c1249000459060008110352000d000500c000306141d598452540010704400046500198540d0208003005042000100e42401124402c03c22803240404902c4c245881150800720060074044102c95907010b141c1c0d02681e21a20b0400307840d50002650010001505459076408110084a00c103500582c44442c1075070240250750207204040c06181d1125540d600e404a10390002c0c213403003460303000324441d070004100689800205650180d210000d104060001d50300c81c6041001082c005400d04900d1220390104404207000c460511006c40c002d13111121070780e41d401a0201c06c0e01c941d91340180711803801d01400700001d00b8002d40e10780204000f0000039120409407a00c03450b10207070280c12220400fa0a504112900f440d01c281c00c11400400b01429103481c4c20390114840c0c010241000f41010350701c41001804e20302c00e1061b1001c007114000c5141e9296400e01d003400e0942c0f4203882c4043c582c2249000011103241610401c0c0c410709000d405031441d03529000211105400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 862737428 1250 862736178 862736197
    0x105090d0810140d0803070518060c0d0503060a030501110c101515020c0310020909060a0302010c03110c0306040804090507022109031516090902030f060d02060c01060b0306010e04020909060402 85
    0x130b0f0803e07508002528200694496400c69903500c0e00c401c2c142141c40540510a0701e05809840b040150303a500340b00115071703040f45d00402d0030655503d4441601142c003140040e48045c015511741040c4000001780c040c002d05010348910111207040c00040780b04401ca40c1050f07401d0001d400f143c1c8003000410b030030034a00c0040c0c001600640e09101c3c0c840340440d040050081d620100b42e41d0004042c01149040001d894001c0f03403d94610350103a046600107040e0302d20340000902031021540c024551400c0c104404414a0300141c1914510b081901c1c000146030040d0240005075410800000e0741e1610000380d0003800742c9410400e914561a1582203165503122050860301400781c2d882044507114001921030180e6a0f280c500d4884802c407550003840d448280c0c102d6803003d0300400a02c4002104030b5070198002c0f1003180c05500340c48c110b10008901c1e11452111540d1175003480300001d4120044e20241d031040800381c031070780700300b0b042d00042104170710840706030381d40c8068a0004140c1c241410303400381c0740320304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 862738678 1250 862737428 862737439
    0x1030f050a1202010617060402090c030c04180507030c0206100e1b041206050c070c0b160f050a0201081513020d110c1b010507080a080405030d0e0105090d081014 71
    0x8605440795100700703081100402c050b0f0b440302001c008181102510580c01d48108000d40702030f00301940011480000036041c1c00950801001007001d202890048a00804030300c0b0070341d1000908a40000f010f0035084600d41c012900e0025118407043c004214148114642000d451082e814502415030100c00900a003401001d000c00818096031594000e2010340014202451864142d2810505540008095011141c5c3c280f2004000866908642c0c044d03458108c4100d480c0c1c0e00481200c400344843c258054150340f0650003030000d0240108a20f07900324000c0c4c0c0e492041d41c0d9170180d02809080150f203240d400a02081c90205a01100c1d4098031402e000300c080858195101c1c0c40c1068140c000d9560002a60460800480644084c2e402018118801c0c00c200782446a00d850b100d2590090103415014400d80d42e00240070000c041c0b0032542c80b5450602d003003051031441030410780202011203880c5460b114165003217014902600240d881580541002d060b6141050090001440c084105a8100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 862739928 1250 862738678 862738693
    0x1030f0c050d270f061a0105031b09330a0509040b030c0604030b0f28090c1a0c07080f06010302010f120f02030f060409020a090207030915020d17060901030f05 70
    0x100399443c07055440e034020000401c101c48a81403110880d01e000000c0003641250021411069810106596020320b131981c42d8000c00d501200580781511501c400282d11800d8800b540c0142e441c510111000141d0040c1c0400070340d2040f0783c011100c0d1045145c510080f400500c02c0218500d0607412031120703404064192403105019102281d4a81c10581013111701c0c800c2c8204101142c0d04294543d54007224404c0b4200d101565a00c6021002a0340c4c50102c0c1516183c50102040c000070380d89050003000c403038803145108070413900f88021079000540c14115500500100007034154000482054080c4020046c00c3d030750b46140e005444401245040b08107000318118000c00721075840c0f25899045040c1c0901503070fa03150000556041d07034030040145100d14540001c21000d83c54540d00c01055800c000030060f550741031400c0513104240c0c1c60f03115541c680e100d280c03140c3d585680411110000416038071003420100403030011220141084642c960401b44100040000c2040392910309040b900500a580d0603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 862741178 1250 862739928 862739981
    0x10050c090d0f06090f20090c0c010216060609150e0c131208030106091706040809010207080a050a05060f1b09041d15090f030f0a0e03060405060601030f0c050d 70
    0x54402e1402e081c4da035a25480802400e001c6000b40c90864188200d18007203a031b501050014a4036880504919000d07030010440e050190425412604803032403100720a200b5645500d0098040c0c0410b004014200c0e040080c0c2110040c22890448241e85a24001d901a9550402e034481241c1201c5041403070000120000030708900082407800c0402d010345040f580e01d605110000d400c01c030480d8801c0283c240c607418200900180450308a41050780321903103035510024480100d103400001c4e00448884c1c0514003d501c20007000141254a00b40b2a00903590a0380d11500d6615003400c1c200c801c0045211002c038658800c0070000001c11880b80d00070000100e101d1407105040c0b40d0001204031038190b40c8080042d0207402c110000701588032078428001d1100f05110014141c417402011954000b0000c0444d1a090541c020356114100d69006001c4034034525241c280075680e0a415500203020a20303240d0b02c110704004d180a000310181160701c0b1a45460b02200c20400140000e28102e01180c602c40c245091 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 862742428 1250 862741178 862741181
    0x30f1e1107080412051501150c02030f0f010f0605060906041703040306061d0901020a0207060c0c0509070203041e1202061602151e04060c0311071d070210050c090d0f06 74
    0xa49607020044c00713004111302e4154a1b1051029405d0362071000c5800400000c03180c01c0740b10343c1070725562502d40e02000040c40820700e00380480300d40304014024855960040c480c15400000301e9458880c0901c500c0382d40e83d060100702d00c9076201a07504a001008140502101020703044440f41d184002c503460140d40e502e52030210703045e6810080325421210340c00b00400000c0d0108503080311507640210f1905c0c0d00c09401950310403441c481c1c00b050284022001091001c4059460700401000e00110342901d03001070001c0d02c90340107000d02040020021a01c0a407410004140d8090300c08807900000d030021590204816034208d4488070100341a144000401a1550071101081002d100c1150703440d40322200f14556800c403035a841040d04032091008011959005070060040c0760142050301d10700030592980b50800c1002d03048801e0800155902001c180104202184110b01650995401c5803012840d081030b80c00988241000000611400b01d8030300c0c082c64002c8170380784035680d800004c2c0d030144d440c0d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 862743678 1250 862742428 862742437
    0xc0a1b030c03020c030c06030115090302040e030405120a0321020903010603033203070e010c1b0f1d1603150b03180616080403050d1803030f1e110708 66
    0x90020700860241d2080680421580411078405c40240c2008a203400115900707000511511541c0f2100089000e071035801401000090f5401800902c111100030900550701d503c14803510340113862120415211001c042094281e00c2d50556602ca07400ca024192001f00c0c0700c503a407040e140e00780e082011035012b950920402c00150300c42d84410035035100e0740c03034a24a26002403050b00c110f045035481d0403084100010480c1e5100c1c8507418407800061032040120341103039007500c1c0204101641c581e00368130750401c46040805c507620a08440304254075407865904280d001a080c0700c2c41c48109001c9a80100301820b10188140c00b4680010f441103080c030880c405d1004e40c1d0003492a84000020302905154007148104541c82c2d0f039004220750705011a104040e01c803801a404200b0560341b010404240c403c1045507016048030105209210481101078810b00040100f20003003490441200b9202c0c015019050b040700d050b04100186c000b40c4d02e5a40007a0204401c1f51301e44802c20000040054019400380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 862744928 1250 862743678 862743683
    0x71d12031b0106060f021213030b0109090b0714030435180a0b0f0a0504090f0b010809011a0105071a070c0c0603020702090a15170c19030203060c0a1b 66
    0x51041c0aa0601018211580390b007284040216a894421446400140d14800603005c9891141c2d10081c165030614a4282a0002460000102c00000c0c1c450b4080d0414803c2c10700551400e4415100e01c1000c0c4d03003c0c802d906003284000814000100071030400c40000750400840c6842821155060384110044041220910312809000c100f00e10b80d001440104001e42405440e240074050070034200140c0ca0040c5070281040c8000003c84618403481001550010101c0c3d05003801903568140403c1c0103000303400c21940c0081e800c200090b4030b220050240d10405010f0141604003405500c00448442e40040002d54256107280c603102a0f0390300c1f4840241c0b144035156542040d007a1945003900001c0103660055007050b005000c1100503959100d8042d030401d103c0c600000c1ea00742c3c0301d140c2903120000303540845503c500e1012291142100428000d084950890300102081074040640603450494003001c6e4040d80311400080642d0080740040103441c01c2818803400340070030b120800c038501c040032104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 862746178 1250 862744928 862744957
    0xb03010c11010e030304080714010f0606030905010c1404090905010905070609060212070512070201021606051308120f03061206250f080705091810031109071d1203 72
    0x11500401c1c0c203104051030000034001031465403c194580311918098003e016010894440c80f15500600c254402c100d01c1840341001c1c0300003682c0b16000f0380103010180701520301c1d500349802a4442807040c8080300c1e02a081e2203215007424148551440101aa08000c0302d6645d81d0300b180c071000c1101042003400a08017541e40a40503403c04400070f0401102503011000741c44140f0402d400610701050903200b06203021903070381e104c0c0312030700040b4500440d4a1280e1b80490000e0310101e0216403010090046d03c0350b4140c814180e40d61406603a0380c0e0090b0b10f0010120740e105100700d2940760b038403000850f0040c01c0200752041005403810240e003424429154084600182d00c442100c01480e040303c07812540250906182d8850515405400440001c0c900410010005048415552000b2043c1c40a0b5008001c40341c0a00d04440d4068501404c2d00050f0348ca500c0c89164200a80343c50000180f041009948540902c608030960250b80780b1070006155000c0301405181c0365071f980410140400320300c144078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 862747428 1250 862746178 862746197
    0x1b110d0204060b04082103010608060d02210c030321071e03020904140403080f0414150a0f06080322031505070306090b31060b071e23010b03010c 64
    0x3101ea14160b0080341d01b41c1c241c0003000c0d42194a890003010b81e81181e00301e04114005507101c00000d525820040002980312101c0025240070320b041c03811010a207811002240d51101070030040540c5e0b23001d41c440d00304180036034920300050403012401c61a005440e40c103001000904112001d0b8015401a10070710000342c0c081034004203450680100c8082944003040c0150b503040c103417401042401e0040000d01141c0b4000d0114042000c10011a5405c1828006466803256004e041c0754040c001030ba45034850341d060158000b040d440d90300c922000c032880500250300d402e0290880e0141c5c00c001011081c111814108004081903103503003c140342040c14140084ea502d42800043d04030742440d00001031840c540340000050b03441d98485240304030070b204485818144100e83c00e07100f5606044840e0304603418034100282017050003015200040c420a40c5000078844d4860687d00080c0d01e800190403458403035010303c00010040b00b10096203a0300c400219042c01808082420344002103104400100001c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 862748678 1250 862747428 862747439
    0x3030525031107050d2d02040f0b0906030d02061609120c090e1b0d0204090c0807171605040f02070606170c0d05060c09120706030f0b011b110d0204060b04 68
    0x1100502500e403c0b21040c0d0071030556101e01b00c480c000700c0301c0010500c100300c60340d40021106a407002d01041d40280184005024a5113060140180c4610680581d252401040e0940b0703000c90052440c070303001d9004045903550044884034011002c2c1c800014040d61150208a620180b40844603407070044000b05015072600200c081241d02043c600d1150b03402040c0049086084000d2f585410403080300d145010300c038a80001001001d006130002d11822401d1400202d0040105039007048402214801000e0040480340b941c845035a003140d05000144c40c0018800b07807810394840c4480400201c001410024659101c0c02120403680080019165100800042d03c00800500360780000513030f41c680e07201c590781e80c50130ba1303400d0040c0c040642d201c00462000d03855140c0c00c5000d590780404c0421120100d03502d03a005001804c1c2c5902d0207a10900f000ca00800311750089002ca4180241c40c1d005a185003a00e88614401c0b0b166100415400b416455aa10141e070721801144007516036064502c4e45e503464903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 862749928 1250 862748678 862748683
    0x11040e0709300303110c0109150e16030305030a020d05100306110a050d0506030c0d150501061106060d03020f0106170c01030b0604030f0302030912010c030e0303010807030305250311 80
    0x1400b54405000e000780300c1250745803210b901e14400b0b50508020441ca001c5004500345401504003030000c0f580f80030324410a0001c800e000e08400444400f0800840550002c0300303844108070030480c0341542e142002000020300c070754000c691000007080010304264105100401340d40c000c3d20010007101e040b030014018841a071007051501300391684200d00d060031100c0d02070194010600c0d54100c031a03841000400d55101407210800c402d5008241022060040c072348884044903042d40442d25900d00300004c241c03030b070150504c040c00101020041849a64005c00c01454100da01401c60440c010402e5600c00301209020300d4000d0030700480030350300d600021079000d8500070b445200181010b0804040840340d80760b2608580659800c0b10180c80c03450070908050380f03503106013241a5004107203902a5840b403101035000b014100c80c030340e9040c40201c5003000c400d9640e00080c0515440d42c2c11444080000071300800c001c02d00340c3c614402503c0072800c54081000c2c103220a8200f0750204c1d00d02100c189006c0d905 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 862751178 1250 862749928 862749959
    0x9070908030711040f3b0d0c0f0602041d090109020901170a0c0b092407150213090b0f09070e010c050a08070302061b0322110a03050304140609100311040e0709 70
    0x42c1b0082442d0341c40c0d901041555a01d40ca0002c00074004840003070000e1207241c2d0007420010390025800c0d5a101c0c1c0e2030341d400b00500c065841e518000c5000f1000324901940c1030045c5460260014004d054507401d01410228028100c80090b0302c6105142285000400c215542002014250340c2552a0011401481408007088007444c2800424000c80d000020064007981c005580101015002082d50206d00c4000d12035103c03060f82c00c4c54072241c0081c10351850303000000d6213102980c940d501407421400380318400c101661030070041105080c0c211495489100c0e2517401e07502580807100c440720b20351a0818507074090f1f0301c1a030058001801b0003140790808c2105880072a001c0010320320310302e130401840f4040100b0b1010044101d455001c0e041c01d000c0750441c1ba400780400100b00d2001c0d6a0340b49071145d0740340e00a1150780711400038650290038074a010400e07120007407000740c844001042c140304e080f40145a010060303800c0903030502003c135001c0c001d40f000c54400c1e80c4546070121054100f0000d210500c2070b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 862752428 1250 862751178 862751261
    0x7030b0303090a062f0304050f031f0510050d0b10060c1e0c091d0c04060e010b0c0316030305040201020115030201051803010608010e0c09070908030711040f 69
    0x402c12441819407215a403403001c940e00f600d0700d4004903240c1200d000c00c0300ca40100e400b108141c081c000f0003500e5000b00081040711400c407545414000c0500034107840721003001000c03400d035210101216440c1080e4110590142d410552101615280c1c00018541c40c54444165400c840da5010442c621500406e07540c007400d403a0500200301645030b40c413441401d040110030105004c3c001c8400041221103000c40024043c18a41400440482c050342d040c0c5080309414100c940c81840d4400c0403504251041d0001d5400501c62100303568200045103d59600c4204a8202c600c01001030b02c0089a1501403000001e01c42d0b500030646d420940002400e4807480f03445009501040d080c01c00c0140c3e0058101daa004100003d07511207014040c0000c0d0040015500040c200e50070005405400100400d164115202c11180080180c0f80c2d140f049420314401e01031000d42d9801004006c0105403841c0c030b4410240c030000c1001c01d10002000405040c0c5038070650401e850308010303c002c0074844010034810320251 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 862753678 1250 862752428 862752433
    0x230a0c14011e050f130f050a02311a0f0a03060213030c090203010b0307110f060c04060809160b07050705060d06050f0d110120060115090902160803190906020307030b03 74
    0x1410103083e1460041700100038003a180128010342000414400280c5898000340b1091061200445046c080b48a440080e4200410b0080c4c4201105c00d51103041403075001d005010144903801e50901240080070030700c06601c48070b1800004001102030000b400e95014001c421700300e0724514900400c3c0c021a607042510317481d0041c801444400300e5a030903030754003803c140b91901c18000300c4d14026045c00d400d0680c90704140600d000300050501c10034014000c88071030ba5600c00680e80c2e4112101e4980041c8000d503c02c440581d0420000c14807014007810050313000e10180c070715075039071000046c000354083c030104060b841d1590740811891074642c0d00390051030750554590710301d0381950369003c00006540440c00c1c140b0000002900510400d4803001a600c0080d80c211903080d6140d83c034485002c01c00750040307800030f41151030109050308180244c4004441110345021001120b980c2d10398103800003008003e980085485518541d40240100c4450314094400140d490400e02e00040c181c3c1c81440100c0d0196 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 862754928 1250 862753678 862753681
    0x702130506062703060c1908060d03360f140d121715030c01020307031707120c1e0320181f230a0c14011e050f 49
    0xb6190902118102a403030004030103020b840541e482000401450b8041d0580f05820400c450885540014804400c0601c03152016034030124080318107180417156203800031000d841d00d03030010380103402001c0e01003895101c2801415000ad41d407840d01c46001003040794100b6280c000c01c201c50140e11600c001d4011a000d4640000410300880d80a10b80460010311080902c208400d03964400d407a210700c2032010180703080150401010781c030000c07008500140e1003805003074162107140d80004112448240d050300d80d03c807041c02d104011405040020312031024002d091800a20300c440512601e100c001c0e09480d4103e444402c44a208130740020030040000785494840c880b0800c21882c1c030032110b08001c05142560756101c0440c00c46003114640c130501d0300007403040c90b14641c240211484024070b804a0307480000c02c044050703949460b1407048080c10076502d0100000a00c0300e104546100e0a07502034184101c0101101034020b08488461a000303071506050554954199000c0c0266600b1070081c080d1010ba5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 862756178 1250 862754928 862754941
    0x806010f030507020c0114090d080403060501270c0c08040b0d0506030705010e04020c03091809012a0305060d05120c0c060c030307080a09020907050406020d300e1207021305 76
    0xd4800e18010340e414040710044400d00c002c1c001f01143c802c040040d0992009140e20301d0000f81a4126020885400703003002e001142e00c85e40d14403204072210f81102c10420303031805c0480003001000c0d1000803c082001c095000400f2400b81d8000300000c2c800d11030301369a01c47c091043e138012100050207442c1700707401c042e20810403070785d0051a4881100c0c04880050380e510385588003a1540c03140d40c0b5190340214421260410700114040c4041c820b00c201d200074094032048080883c41e20f0f5100e0019140340300c40d240d01d4103140348a80e00880d4482c030007522001c0c40c1d03000c54031369621b0080c81410203050b107500080c60700c4062105100c2800644400c0d1074660900c0b0301d001c007440d1a400020b00d102c0402c240c0d00c1c0024592a43e6810150302540c0180c110001420171003070080090780030340520030241c800c079101c42c414103100d200d014a140c145080b6013883d5401803500e190301c1030b6002506c4810640c650307032880c1d400c000a0040c000a02541c10f100c0d645c0300c02900c1400700481040000c3d45806281004011030b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 862757428 1250 862756178 862756183
    0x30e01030c020c060307030f061a04051c080f0c0a0b0c0a0908060c0d05091f060518060d060209060f190212030c04060c03200d1215150201020c0d0806010f03050702 72
    0x8205045007801b10342d08c0304070407105009022a90148038a00803072811a4251044c50303008000740c0740269007150019403400c2c1501c1c0a0038151000030105481080200c0300140050084d0091905607019a0000d4142d911114808a01903030980c1e01c0d001c2c00107620001d02d41204807403009240d01c2c00503003154642200c9403602e5020702095605c0359900c0c1d45c0042c0c0034810500c86440b09100d41541030b0740e510628807030940104040d028682c0502900c4008449420340380d059644a401d008100485030720050392684040e4110441c078a0b000750050010320004d41404000d060700f20003803440352070f1002603018000e01e84042180e40480141e0704100b48040b0715800d5089a00740d8030076081c0340303c6c42e04032489c0896141502505a9007042007044d4090041480400c105990322000d80c0c1d409003c0a13110b180e0380171030304070602d5050180004402007101081d109604102070300c0034000103003401040c02c021410300e0800d22416001440074010842c0319a0000040c00035042645401c000b28545603030041d6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 862758678 1250 862757428 862757431
    0x81201090b0d1a10030803010b0301080c010e0f13150806040203150403270e0a02091002010c05092817151308030402220c091403060f0a09080403030e01030c020c0603 73
    0x3c03100e034120800500300342d10703240403a001940c1c030040c459665070750391802080603002030080105074003500c944000301d58426075480451040c000c0c0380040c0203825001300000900e486043e2015547c80d240741d9444621510408130040c880380d0090042450309204060034901e186100840303000c034980a01c000b280c0d08c1045d158030307100d030b4091041301d41082d0406c61001b02c203d94031040320f103140d18003000403068498014004075001a104a8080c3c01d413070b40c080c3d003692940310743da00004409102d01606850981c401e1540726103090300e01c0d594142000c1c0d0400116110350800340056000f081c400840b0340f400c000302800c01075600d90340603403818038000380f61039602d1940c07018080380310220215082d50340345480d400c26211070901d4071a9650440140e40007514031010791030085451410300098030000c41407003040440780100608183c0e80d405241000c5614041c06030004140d4a009c0c81001843c140020806103009443d0f1031410000c020004040c0c4030085d070a0000c540090311110220344440301902e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 862759928 1250 862758678 862758713
    0xc0c04050a05040c1205120d0b031903120f0b030703030509011805090123100207050109050d0b13050f0d0504050f041407110c190314030a0c0206070c03081201090b0d 73
    0x392005c45503401c00500d45898400f00c6002c02c2c4000030803403260400c1c1e5108107000c80058055a81c40c034081e01e8103452642c0e00000190105030b000d0040101e882e41540140b1312040c8842c8005203240022021a00e0701c04603400440206500140e4100d4544c0c01c021040f400314080c0009051440c1414041020008184500044c0b100d030140420801d90006182c0c40310a0b2000c0d000d050340303c10588000350344d21300f20301c501c41c049842c8041c01305150400e0031140010b0342d040300304405030381c440b454010351280c1c20034400d803060700480020301e4940c2d0301031000f140300c049130790344050f2140c2c01c20b8100403c125400152a200d245805062689031000860465102c2d0702d504000c0c3c0200040c0c440c4504210031016075a503c542541a50b10400803800000c0c015207019500354040c44072449102680c80c881d4200100114454078207100041c5000401845400c5c842e5024414295881d0b844041031b400c6a0000c0e17410141c07020050080f03034086e00c00c9811050b012200e034038800e9229200c2860400143d81c60 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 862761178 1250 862759928 862759949
    0x50123042103020d0905061006020a0201051602060c0a11010e010f02100915060b030108060708010f140a030818030c1905060903030c120d200a0c0c0b0c0c04050a05040c 74
    0x101c90450081c1d064448502442d5801e008110040c540242c980d41d040b40d400d10800948040411003d02c0090341c001044e0341a1240d51030401d007580c00014000924404907800b070420009081904002c0c841c0c1c200c49440360025005150706900054000d46000207854100040c0c3c1e45000713200b541c0040c200f10030110310b0744009007501003820002110304041c845184040c0c10076500085000c100e4004504030741503201a52002e864442003215600001c0c42042401951030b0014041d8040c885240d840e2200001c0450402c0c9603266183d240c981c000b90155111300315003090401850030140800c459041c03080b81c0031042d0743c4c029444020210164043c09000e17400100b210640345c1c0301082114480311a41c41141e0340e803000890940a25800360302e0482c0ea26050182d04040c41c0e44c40780110803200d1034106007504140300307400215003c9020040c26103401c02d6001000641e0100c00c8000c1c40b0942c54034002d00b550002c08003c0c441620405890801024039100400c0040361702100401c05860000700c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 862762428 1250 862761178 862761233
    0x5010e0c060f1c02040f0329010b0a020f0601031a16021e030705070f1a040e0601030b06070c03030203030a1a0d1b1a09100509030a0b1b0705012304 65
    0x24088007020f9082d0041020a200090100b082d010480c0342008491144041002c540d0208443c44501c140640c10840f00300f59a500500150360f50300041c0c010084640b040b28152416070b5020b40ca0704000382c5c000c4c3d84c3c07400d040c0d850190314103282c0042e90b403082c0b03683d0303e06003807020551000390348100c81c0b5008603440800f0200031510800a00403150880e0f00325044a46483c0c60790b04540c0046014880d807201c0140c84144000ea005411007650102c92003142103406951724000150302030400003801560004007081058000380c51460314401450003607000303607100c0c581645180b0440ba48030003082031800700740300140780c25510407000c1034190341e0004403510320900c0c001d84444941495000328070040d0482c10303000e41d4808490301401d07643c03100b11110f003070004820a055903a0310070b500c40a505500609147d001141d00083d03101d8000a072000d80c581d8040c642a01c4444640080c2c804507410794442941c6007031004010701194010b10903298004450420760346080d96055003a0341060010410312 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 862763678 1250 862762428 862762447
    0x25032906070c0e09010501081b06070f0807200a03050a1104020c0304060c2f040b15180a050405014707121404050603060604031e05010e0c060f 63
    0x20a6501d1154070990501d202034640400d0188180200c802c01c1c025072030040001100003001038502c40c090090700714000d00c0e0074620b0500a0544c0813440540381419684240400202d95a0003070210a0003801078883c180d2007000d01148003414810308910620880c00103001040001c210060101d03405103010040c00c2c2c941003c100030b4040d0000c203802501001c06d00140030364000345200c84051003a5149603562503c4040c1da103a0210301c02c0c0560750b030402d05c090390100781041d0703020103180304004140e80c2140a1106422000c1d074000b40c003d070010302d040e20720300c14981000e454800180104680c1403000b036061010070280e450350f65008425030b0100d10300c08941c0c451211054401703660a04501340703a0344189502d02d05c1a41c8118030403a00c1c41109074800d5903031442220fa0320303002c18000180131320342480d200401400d50005044a0340c003880c20071000000440c0c80d141100095000c2180c8a004c090909101e03003190305c00403802005400072522101150340e010b017140c070703078810070030740d0755251400d01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 862764928 1250 862763678 862763689
    0x5090a0f090b100602060103031b0606090510050a2112181421060c070606091d190f031d031002191d040b0315250329 52
    0x2000142509454503412105000c0c8100380c4601c51094950064410f41d9100c10407039035140244070280008012540e13121101c001c031941c032b4403000d00500003c01c4e80c0da150f20210003280d0f0180c2c1c444186a400883c100041d04104006400401c443c03a21207042107080064400c441c0090321004054100450700c4107480c500851b5030302d480010031003104d18031a843c1e400070340c50400358050088c82240c0c9040030803003001c1d00e400e000c240c06804401404181e261380c1c850340c02325040500c0071a001c607210100400c0468841c424010300c1410113034940c0350ba00c05039049508100c0400c01d0b00d0389440100015001180d12260145100b6515241050501c0d05000600785160075070a0883d6060152800f020300c9421160054428040000f140b100e6040d41008107403110704005100c8442d80742204154021480c00e40e10182c2000405401c0e18000e05035412442c2c80c502088a070000b90b03044d68440d01803020702501c0f914103084140d060410624850b28451000c2810040c0351142c1685801028443e948aa = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 862766178 1250 862764928 862764941
    0x30f07290a091a060a0e1b1303121e051c0c020115080a0b1902160503130e010620011b02010f050c09060f030601090308160318080705090a 61
    0x450004003401d0500511015001c02c140985844070f600b4802e00340c405200107280e00a000061020307403054940b80c800104450000c6c49a04e041c2010240d20608201380e400038090461644c90441111b4154070b410005600d00d18084800c02a61410080200881c90a4070144a1882c1031607500c8042c007007006440141000c85050009003007e4902c00b5981e01500481c8a05a031100b05c00ca4481d102c00c1c250780d076000a290041e0070961440702080d400c90070000540e1540c40e11100151811541c185070040d040c040d003204076800e500004100e10160010200e060280c1280402820750b03500d1f118000304000d800a0303051046140c11441e440141809522082503202040c00310040c1440901003c0d00810819910500c03903428040000c03e04400380c2e08071003c03081e000f06143d08010410341d104e1640e42000740b0305414892840404004107007028080c08840090302c1d2503050b480030320b141c020b0080101100e507080100155000340580c48000c0f84042c00d486003a15031144590354441c5400c0900712 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 862767428 1250 862766178 862766243
    0x41d0a020d020c15010812121003140f060f0c0714012403020f0f01050703050a020c130204091805070b0d0b0909010b1e090402010c111e0a0503030f07 66
    0x1001030411241c20380800d141222811000e411404d982e80c5070a03a944170700401c0346210200608004171940c8080c034072400c0e5040607905003043c100503240c0d603074080350b9501c000c201e5040c4d80c0b0a0181164205007000f1260f80071005a0060400307040c840511205400348180080100e0041b0350071020f47d8000358016207c0030700c1040b26202c0c00401c01381c4c081c8000140c0c0000d80c081c450089a15881b414004089451007006079034a52400105840845003a000340c2840710450258502044140c5d4440100d5416480071560040ea503500d401084805c4608810a88100c45407035420320010900c042200803c0711221f9030b209039159000814000200383e04680c403540005d00c1414031175802c50551082c4100700080d01c4550711070784410f891000c070840c5481c10300c0c0e126444500040065204c0e000c040e0000e84900c8458503c2c503c0c04002600e0254803a542c28000c51110041c1942460701c1184a40200b40550266180c190100021802803007111005821002e101c0c60781491504035890480c601203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 862768678 1250 862767428 862767431
    0x4030b1b1905162003070801140a090f150b01030b0409020102120a1716021203040b060607031103030f040b010f050a0b0f0702061b070b0c100f0f090f0203070b041d0a020d 75
    0x511031164403500002013410603001c2d101d01400403605080510801c3c08648a440c082404c40e0b0303c20300681e020740701c1c1460848020300100b6100340051070303524100103611410742d40030515415003070005044400360301d07065104a08016008002d41d03000f00743d000304102c010b41d0507651002465020b584649030204510503003c4500c040090749a007807100f085149c1803607420f682600000310001e2441d40420303140a401c40c00480c0118489291902c01007440038428100191170f112086241070030b41c0c0044413400402c00d0984200000c104110130744a02408002d03280f14071403400c0c407000c10340e440b50703500561a100f00001a101460100482600c040030f5008101075030701c0c10300d40d070604840170328800000440d208a680125400050400b51000003d81d000140035850300c854100000d41041a0405105991080c000302d1b840000d000307a2000b140614604508801c141c8181072809c01e0a40c42030302080b4060206001540d0304501c040945034095070520a6926080c00400081c41901d44494045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 862769784 1106 862768678 862768703
    0x9060207140d0b0712050f0c070204051b07080403050d02210a0c061b0e151b030c030403032109020a180603050304030b1b190516 57
    0x708008040c00d008185980303032402c0d011001d890b12800103640b40d179400f201c0c2c003050041d65000000f41d01c06550034a4081442001d81c098840020700c40c82d150400b1031001840d003050a05c9509040e048a550350300325142c241c110b81e2040c44210348500402c1400d6034030500100d0000340030054050811f180040e420a5501e1542c040700302d240038043d01081c2a80415514801e05804100b2070b914560003002c0c080014240c80c0c200409248204911440d420b0a201c030346003070b6020703612a580c0c110040350030b100c035850a5004840c40c285c034030701c0003207400018103900c601e440500c5032290304038800002c100120030054650040010b5040303000c95004218a2844103480440c01c9000c070000141c1c03a480f07a4425007142c0c400c1e40f080e25004403280c1404520b0400340550400b9100e0403800070300c0c0c040694503400c03080c500c50107080300380320010170102c0300c0001343e5030300c0c4080c558400c01c2007882c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 862589928 862769784 := by
  have h0 := BRFrame.cov_init 862589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 862589928 ≤ n) (h2 : n < 862769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
