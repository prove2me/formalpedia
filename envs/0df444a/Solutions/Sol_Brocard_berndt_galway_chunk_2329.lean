-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2329
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:22:45.804971+00:00
-- url     : https://prove2.me/submissions/0261fa83-75ac-436a-a043-bfb037a6b61f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 418705035 ≤ n < 418884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 418706285 1250 418705035 418705051
    0x307140c010b130606020d080108060714041d010623090f010c020406090b01020c01020f060106030c0c12030504110402090d0b090a051203040c0e09071e09180c150c0209 74
    0x10385498003000948885520030149048a980c4d280420409030100308019800c409420004020340c50411216106c040050002090000071440c0c900d1b8503264034200e8020b03040c540f1205948000c0c98125800080090142c200441d00b07240e41d442110b680c08246540b12545100c50528091504c4244019070320b9a000c564140003144005c040169214015003002e0002900d00140f0311034284002803500350800d8929040d0342203000340200c0c0d42c0006c155241542c11500300441c041004940413074806101c0640505004155094800501c0c1d051700001d0141e402aa04020b42d2040d80040008034407400c03241c690b024020f4080400040d40c0c0c4004164042d1402040c1c032590802c0d600d505081c0381015041c20400310000081100700081980b5002c0580210401c81c289446c1030071049542c2d00f0035010b0f1000324004c0da40c83d010161071500507040a0005580184031162049014681e00003c1c1d9100b203900d40202d10000c00c0c01c90301e80d010b1803100c0480d5515130002c1309a5400340b26400c0d6020304440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 418707535 1250 418706285 418706291
    0x103050f0f0a2405190b040902032515080a050c0a1d010e0604060201200717030604020d020d0f1409030406031d0a081b0d080c0a0e090901091104020307140c01 70
    0x2d4261031562281520a00b00c2c8601c041100b44905c2607a0211060702c561288903034030b440b00b008050b07100000c2e6040c460040e91181c4141000c00000041c1c2c1c16841d620100c2104a24403849107a60f50184409018810004080c4400c0c1c07100c04800000f0f000f4140b40758006138845610000c104885080301800540604103928811000c2000c2803507030b402504044050703074544040c90035015a0303001c142440165400e080b410021165522904952a41e40340390399501e000c000320700c1075a581d030b0460300c0d12a044c103411584e541310f1000340c01c0580760158059103c42d19090782c500b407440301c8405c1c2c1031203801c142d00a54034090501d00103400034000043c1d801c490240f8940e0b20140c0b0030b420040040240e0080b0301d51525408a1045000b2056040c1400f003115080f01c90150700d1a03800c41ca806800007458031005481e005100710071909a9103e010707440d03111900d0b40074803240080c19404240118000ca05c000c2116003c40244801c0e848190340a20005400760510b041d1240b40e540a07090b508040300000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 418708785 1250 418707535 418707593
    0x703060812090a14180a1503110111060106091e030f1a09010c05030a020304110907050c0d020c030316080d050c09040501091b05030a0e10050103050f0f0a 68
    0x5140001e030300056040340d5400511024645480725075507008045001034420300d4924100451078092a4400b0340201e1103d0743d01049581607070f6007108503025a07000c000314145a6034103200074500452a01c3e1800308140005500044001048aa050fa001da8840e0600301c2e00e0600d40c144003409442a01d43d0501039403501000140740441c0306400130b4002c10200d0350144070420120302581d80541840b103640c2c50000c1040100b0341000507264407040c4500010b031203a90b40e081031092184000d06059000b1031805c02c01c80d450b500700028050010f520000c40f1100c42140720b090340d4811a94407183e5040d0700074012400460f50841d8031050040c4600b1843c1c0c04c0040390151300f42945c0040c0e035000d1100001003031410303503030800340709190041512040510841626a800a80024010013020b007044000400600a80443e801160104404008482d18180417041c100000d22081c0070803107442c01031b060075480080002a01070f1140c405003014000701d105660318144182050a44141d406c000036602c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 418710035 1250 418708785 418708799
    0x604020118030501020408030901140a020a110a09021b060601110a0f0206040803030c0703140906031503031603120f0b060a050d0b130b01030c080c04050415120c03030807050702130203070306 84
    0x6d40010b01c111001103484903e0100007401c10601c403440402d00b039006000d001d02055002442c0b114054200d01c2e03031910769421002084d07980c59580c01226100d40005511002d0700584145c0d00d5504841c9015964140c90b44401100c82e085400c03021070241e80140d4074100851038210780191440d200421940c9080d0743c415080f030071a001151a00d102d0300000c240e410a044e002200c168840c40e0001c0d2162510404100280550001419240d00c40400d4603031821348d42c90810444524610350381460b24001ca46160003007d05105000b00381c000c9040883c4400c0e111107502600002c07900040c40c40e420202d40807412036003a0002032030350303840607105c3e041011291108400300c0448001c0c0800422000c20780c04c0058107551030f0000060800101c40d007001007130711407141564181c9100b11004201003d4000d403076001104a50030000d205918210310b03904001e168401c12007140d22030784404810742e488200a8456000709100079401c2161040c8401076902c00d0703401140c3c886a24200041c4598031891 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 418711285 1250 418710035 418710037
    0x601080106090b09130f0e1b0307060516030c02030f011e0209030705090a0b040501030b0105190602030f0c15070c1704030b04110d0f0303021c050c090d1502070c030c0e09060402011803050102 84
    0x100d10847c0c3e401910304c2c590b1684040d906841045030503401011514500440100280f25915801d03032071061075402d030420141701e0700030703200016001800c8504045108003a54020280701181d1a1154045409004c0e074010034001e5901986008010700780c03903850201440703801103000f0402c5061940d5007e40340010b950b0392250b00d0281d030041000601960605080c085021120080000b40a10a00f03081000990000881d40110001039120303880f031a141c03050619211207071499086040b0308108014079103501543c1111154001c40903034003c41c0c440500540c2c04e201741d0101404030600b207030005011449103035090020490142001c0c41c1c4144036200c00060540c0688118006a000030f442da4500c88102ea25000e248080d03842002582014007078244507103d0305500c3c501445880720030205000d42a040c4420f10205048203664400c007a02e0210141101d0340003c84881c120740802042030303586600c050380f0a6000200500c0640c8580d001503488a44c0c504401e10000c03030640000c40000c100780 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 418712535 1250 418711285 418711301
    0x30c030402180f0402100315031113060b0a0f0809060c0313124e0e0316020a060906121a1201320c03101d0601080106090b09130f 57
    0x880203541c5804c1501c10403480346071030100f08041504000d6140390700d40c6c0c4495140c080b41e40c022540140c2d0161040420714450141641301d415a00c1c2c002c0016080603c54024a614641c1d9610401425500f10040d141e052060b2018806548804001110070590000841c3c02003060300a000f4850155a03500720881183c030080740004030805420b089681020440e1070080680c2014030440445400d40c403613180b0000210220440408403180d400c00320954005d418950240d01600e50381c1e9a0b1200c1580c14080440c0100d000b010100c0300021014850740c61201070b101c0b40c1d9103c011003003802031060301812407004580607480085000b10240d0342c4040d00207038a0fa59800011406900c10070036000c2e00309c1d2201170040c03c040904a070009800300721650b2076112020490b116201d40360440c0c0941ca5500a4100b140c90b40810781c988501103020440c0d1358031a03a4260f980f003a00e48c0c0c80b41c204541c00c240503c50b85040d1001170085c80d82d00d00d440a1410b41a0304003d000040c0945a5044a001e4031015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 418713785 1250 418712535 418712551
    0x30417040b090a0e06010e010309080d06030f0b0703021314031501120c050f0d0312180609060f0b0618010c0803281103040b06030a1505010819020303030c03040218 72
    0x38150954205030041c84000e04403580d08041c00e203056800071f0a00081c0610380740c10150b95046080070498030714151030a90400b04400c000c0c4c1d07501c03407804061810f04008140c039241007030300001c0c801743e2090003143d00c01c61002e030710440c055280540302d2070300717107220012194540900c0c1c295201c81e40311070310f810f8024a1042d900ca40e0a225500b080075881c01c05400c014000c095800002c0210344038405905081c40d45840c020006c2c00440d4041c100400c101101503280c800a1100038007889040c0e001000c0c002d018800400a40b0011152030007121000c034101504180306200f580341c419817040d4603500340700040c1002c103c0302e4410b981e82229a4011602580141588074803030204e811b180584041d01c184410041284181521100c00c0500000300005d0441c80043d001810b192800c3c444c841003581d00c01c05002030f000e410440000034090074050070305144140180f01400d030310311091516001e500030380654030b9502c4071413515240b580001d006907080601e103820012451725400d0028401c00d11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 418715035 1250 418713785 418713787
    0x2071421071802040302060f031b160b0a0c020d0807050c03040305030c010b01080f0103060c0c060f06061413030b06010306080d022505180402010311040e100b0f0d02030417040b 78
    0x1801d49681001c4242c029070842e19205000500050711042d04841d895580d0480c16500daa484118940300445503c0400c0020440810480e4171049192140b4030010300c40c410501540d070b41c41c804d000807a546280d41000590004010706140c60049901c82c2d0086841e240140c42c1c02001d081040ca140c0c071562007101c255200003200e10190030b00b8480c136002110240b8180c880c604080c0005100e540040c0400b803c45079864044d243d065008052205d40240d10100c148443c0709440900401410540f00b20004108400c0300e81418249840c12034204000a203035100d030650075901c0c0c003c10440000e08560515542c0e00300400d10b8031003045084447c0d50581d008080b0541d0f000c0c035910400494480d031030401c226599080c007140c1d86020001a03a095040d04842d030996036800124090070540c0d46c425840d08001502250350f8542001081c0308034180c424618000d0340e602040c3d203051240c42c070007040e5884144507441004504d60015500705001d8a07905803174001c00403510120341e00c96402030b510700b24 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 418716285 1250 418715035 418715039
    0x40836040c2102190c2112020f070c24020705360c03100501091a1e0c0f19120f12060e06030d020d050d151503020301030b0906070207142107 62
    0x86402c0c2d94682a0920302402d4441b21340d03088014000c1c0b9a0a0030141416401081c2240601c03441019207413030680080c08442c910341c0d58442410640f4008203040c3d011103026100039031450000800300c2c1207602c0070300681c50100c45c403104860442c10180f502c6c070070f40010705100c400003135050701054081c1104194051741c03400c060072541441d0a45074410f03814007903d04400c01c001274110141000c4000c5c03900502da03440001c42d00c403440701000404440f250703420100d071003c81220005070300c088030a03124045a18810041e01520003000320f60600401d444102c2c990000a64820402000f240000e4100041081e1402c543c201c03d450380780e0451140000190108815481c080080702154003440c00984091040301900030a180310701083c44424a03120020400b800c0b681c6826840108245c01030403000903c40c64004020303510a00c07041e66850f101c480415400c58000c5041c0380549503540040205a203807141d000072004550118940c8552500d440303510380c059200070718031480109000380661034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 418717535 1250 418716285 418716293
    0x60a111204030f09060e03030d09051009050309030c3709020c0102090117090a1101141c150807030609030309020d0c030b07020321040836040c2102190c 67
    0x840d255001104100000d00c010041f83c801100f200c0945560201c0032035079a03000d081c95482c0c44552410060714520f40340050081c401f0200203010a60700c110103944051160340c04005203030305100811600700d512641e1110f4980d2130880c4038141070388240e5202c04c0b503d80c0d45c1d4503c800c0b60403082071406681d4000030b0342042c541c1e00203c0751504d071200510300c90440c14140308030303592a04e6001000740340b0f40c09580006500da01542c2811504807014601c1a0740b252000e2a200d002030402c252004241d0502d00f03804040c248442a00040d0342008000302401490354035805c000d41103181064042c1503541501c00d0250700d5002d141d242846c040c220005c901e61039403820030003445000707041d0001c6400c18468510a190f03e8282d0143c118030f80755004c85d0701c2e291401c08402612a0000e44040f542500140c02d080300006000c80d2504074082d180c00105110310800d101c15115484c00d444000341d4001100385021010f042e4907111400e4403a130050800d000360950500d440190f01d03048010400b901b440c1c40401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 418718785 1250 418717535 418717547
    0xa0e031b0f0103050106080619050d150b060403020d15180b0702070501020118020d0510020a020708160e0106320c1e07030221030409020c010c0e03060a111204030f 72
    0x41c5080c42c08101c44c0d03141010040800d4000342030700e0310400b648a201030040204400f01409031000600140080d81d180c50300c801c0050302c141d04007585c9428503016148628110040d28222900030705081100b41d829503402c03c90925070048202a5030f9920020b1b1100a0421603a6061a02c504244c650078104200c010349881c031164403050441e0b0618144248051070b00c10049602c5a0640304644030050600e840c034205900c0703c01a044207403000c40c2a48003554002044004c80e500041a6442a5540c40c80c520401c02140201d043d142c60440040109600c105580904421203402000d0002a0344145844c0359440d0a501b041c090320200d0014541c02e02030018001000052082c48160007240021903203d01c000e2001138400c441c0b01162850003000c81c2640b40d4104c41003000e03a0341ea03980301c480d11002900b1a490302c1d00e5030b40c03800608035021409400342c580d800800400600715541e8801c0680c01401c658443d443c1019001e018040d5150304028460340190322a840b11300104041100017018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 418720035 1250 418718785 418718809
    0x322030c063605030702090f04031e08041716080406020106050604180203040203150a1406091504050c07140604020f06030f01060f0903050a30090b0a0e031b 69
    0xd03891840c652050500300b0441e04110100407541c9161504038a800d12509502035038402035000716030281041200a24030100e0707482284a0f40342c5031740780d400c100c003a81d130a042071038055404144100c01240101d03c1200c01009091140b2400d2403400d02c400b080c80121a100840403034096001081c2405841e40a00840d80504815141282858039080003106480e6500c10040c4202d5400000704040d91003d03c844070361404026010305160034032119250013404040e1040d105005014081000c5260181d200c5010351035500700300002e50640c40401008000107000c21091803c01c202150004090300301205c825034004000d0507451619005204089040c508001d101e51420002c0240014591181c541074941e60314144d540b8881304501a202201036400281403449044080c10401009852040c03159100070761005074492041c060f42c00c40c0700150301c2403001c50b512003014480c1203283c0e005860300710b03464a49450000050780c04241890141c280d45184a03401c141150b140f0305017100b000403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 418721285 1250 418720035 418720061
    0xb06151902012711010302160b010f05040207111e030717010507140d090c0b0f0d0b010f0f050c01021908040c060e09061207030819020712020303040b0322030c06 71
    0xf1240555215460b0301058001004002e40341c40e03110108070341d10aa05989191801d42200c4031142400d0502c0d0201950910443c840e048680c0320209503800c10307000380c9604590010504610b17509080801403010005038100c8860350001d5942e0303030f843c1d800b0001300c0b0050000441294a00449804117402e40301c6c000e12400510215030049038031444000c1c00c030390f4070442e414800612001070303140c80c103421a52b9a1007403030202c40100d1081038510290005292103042d0010401202664100643c4e11020650407800464440039010101d1402040108800a00640010700d0600344200308000c10704189144130002ea042d600700000c014041040c40041c161506000440444810000700b5141c4000e0030b15024031516a0b1100c10180100412005580d1200c1760a88440000071100e8002c4c218006070401480741440c00200d01e0180a4400d40e41900a80a545810f0a011100c8059400501074040e01041c03840c8223120b0400c2030250140843c0b09503030342c400244160900205032070012100315 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 418722535 1250 418721285 418721321
    0x1e060e01030b010e0c04030204090303020c15060f0f03011b03050601180e0601050901021005011401170c09060a0210060803040906061e030e0a0605010e0901140708040b0615190201 79
    0x20001ca100300a420341101e284421140c0990317291400900c203806150700c025001410031416104054040e00944000340001048070310009401000b940c2109043d0340d495040070381c414101c030103030902c4045a14040d070054000b056001c0b440240c0008c400c1108110741c0001c0c0d548083c00055a8808181c480310071284400d0007581c1d041c031501000b100406400d15051001c001562903681e4001d0109452210b0341003001c00c4950303034459181d990545948142400200c10364004140c103440301101701e02401d0b80740001d034140b030aa003060000e00e9201034291000d602c624100c0f400044110300400024103007810155403035610b00003000c0f0a6800b69000003052101c41600e190208030300042840c0c000000b031070702280c21141401c2c828208003540b00301420540c1060008175001e51389050050080c82ca06d4001c0245003804040410782d484256583e200050910f80802c0100e6994450369400900050802c2c2c030240d42403561030402d91110001c8604500c10403626282c1540a00c9080b141201d2403140c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 418723785 1250 418722535 418722539
    0x6030303040c0509041a04110301060611120f0403050d0f0e101b03031e02071203051e04020f06120901050f15011115041a06040b092205011e060e01 65
    0x50140c01482c01802e005581200008090129854011900b0a900421401c440c117150416231300c86014440a14060345c00c2142c00941c0c00d01ca0f903c1c10324803004040c0944260b0601d501961035036800901c0c0f0300096901484084081903040c00b505545005540303405190441d079401c017074101c4254015a501c503c1c0d01442045c0415045038100c44442c000c2070b19041100010b03c0c00f1b40003001d80b52042d5180b560f2080000128404680c01484264094040e0301400942d18500310142c81086034142280c400a20365401e0112002c0e4129030468402041261502a0b00307001c1a000d4009502c0c0800007001d041c00d0180009080c0b0440ba041600f2208600103450486013199003a4810310b107450401001c2c8a01c84a1f010082c0440d69072920000c114080da81450b003052450b0384805200191903040d0303031000c0344041c90305115038050b0039000741401b0540d98902d0380d0b02e28504215a980d00304110b03c0004940000ca0a120b01101c44401030044010a9004201d074811987e450f08240ca56038821401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 418725035 1250 418723785 418723793
    0x20304020d03200613021906210905031603030f0b03070b0a1205090a030f02031206040f09020409080301170a050c061308061e0601020c0a061103090d1a0603030304 72
    0x101c1500e0b00b5003807003041c0c00354031401c400303c54040c82c1a40005010341070a00c80642c012200000da214001c46a90002030038003880c0d030039900d0041c480e100112328540c4034058002c4880e021034002e2a040c00740040c0500c0309440301d50071a031120381c0b144007110f200d40b800020903030144580182c21007484003c00c24140200c0c00b0030f0348c80320a401540a490300104101c401d6a1040d9000b0480617100003050086052420702c9a503034030281031046020555262604020138400400c0ea10760b260a108000705907110780c1d050000070300c0101403440b1215201d555100140c2c80303d0040010382880340c55060307565031414003841201c258200410419801040201c00401d9000800380c804407000c4594540ea60480f00d50021040140d5011081c0c500030542000354100b4101d00d405055a00204154442c0d920030004903101d02d1851200d5510080d520030078009580f061070600328641400702201d181401520008035058100f10007200c005a81108032030650f9000404250000d6055000f94290300b0300b640c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 418726285 1250 418725035 418725049
    0x30b07111b06031012060b090c03090a03050f07201e060904020d0b0a060e0306060a18050c4303050d0b0f09090109021e010c170d020a1107060302030402 67
    0x45600c901008030111340e00c00e05102410000f40314500e20070b041601a40341501c0500802d8500e40d01ca070002900146c0d0185030942280d10800866018040140d00d541d001d89264100100014030000700b4004840040d140c9887c86010f100412942001b45171000300301300c0081d020031411000401e0f018007895064446406607403009004840260310740051075050001083e40c0c800c440d50154880320b0000380242c0003805411000344c268156402581e038030042c0700708212144290034002a10388868032070840c01d0ba02880d0044034404c42d032803400265042d0a141101d00110410004c02421200220709600e482107000141c007a00512196a82c1510050818010b604084428036107800b03000c40c05036240c90411000c2c1000411120107405c1111405000b4403881c00101d018007422082540203400c0d80303604d0404848160354400f0340d191030355104918003c40045141000d04203000c5643c1020150025082c101d4039580d8010b00e2001854103603241c45116400f1005141c810001d100144c1c41d450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 418727535 1250 418726285 418726333
    0x603061805040501140c30040b06040605090c1209010513080a030e06151201111b12040e041b081002030408091201020309070503030c060105010c0201021501030b0711 73
    0x101a0740300d0a10501400b40da0081d1a174264182c401c101041c1a000080c01201441c01c03148644a0610074104040ca100d1401e40369460b030b40b03c80050300003005507140e030b070340044054030124002c0e0340c0704080345c5800000d03604210501c10100d807800b01c501c0c41b45002ca51220035a0001e1006003003640c1200c0c000c220321140a03042c0500002c0914400b400782d08200d0115942d80c00300c800a141c00700e1800380e0100a400c0c1c0d18814080350618421281c014025a00750350004010350f4603201c000100300d0340c0804950140090b5008828801d14240c0c00313240900000e24401410b03107441d24040c07600480654003420f464040c000c1c207003c1231014400000380318100f21b0809100580d6612035040070203107405048141c5034081c0c0001e0300c1c80034080d410b40203540510f500701c1c110342c039140d01c0300c0401d500c0b4001c0c0c5000303908a9010318010000c962280c0c1ca060a1a8018015940120151480402d10f00c0e000d0b081642c0c111411401d014925a02c4814085001145c2020784040715101d02e000c812005c803a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 418728785 1250 418727535 418727579
    0x3150c0c0c052106090303061201020a0801050f03010b0406030b0609160507020d0309051e1009050906040f0207080712020c0a0303051b0c030106090603060c050408100c0203070803071107060306 85
    0xa4034000750745004038121042e038040c0020072110540362000071030b6a00c7d4800c99546025202c65640442124014020388039205210703124280e0981c20304091042ca41e01c0720986c558999252003040308907869034860200078600519040d0304502e4a070091001c00c83c4060403c2c1b008031500410200c0d12684002a5560260304464903405c105041c1001c40ea01c1004c2d801180d40701c1107144a1540c05600c61042403403034801034640000d56a00e0032001e8403424405d20600750441d0120740012200c0c0380a902010507100c10402c01410010103484042607500003040485206c1404901c0300c1503e90108180109002e0484d5040895030455034000d005016100002108514074590310710000c00502c214010441c02030002c2010303a40e64107840c805401a844145c804501d0580c4491641d4441d40460341600c5580000b040364107501406100280401c4040d081103000c00e001c01d01c00901a076008501805807662850000005008407a04054180d4003400c18545011410081c540c852072040d141c640c4a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 418730035 1250 418728785 418728799
    0x3040b011706010e071205011d010f0f03020d0206040312050c0721020d0c03240b0f03250b0409020c0c040902030706030b06040b041e0909110d02040e0703150c0c0c05 73
    0x2d020020380d03201d0000054607541d21f00f02400481c0d490395107541543c0460000481d452580d0340c076100e680d0606240d016070405645e0700581803001d030401803003901401e40702400491900780e9030b40f1380701c080d601c09500c5000085e000090307003004030904020f808058440f600600b00000b540324010703a90382e215580001e004003c070000702d030280701c41c000d4100025900306210205506400f00c0302c642c03009540c01ca91264510b04901c907009410491036501c07100002038001c060b5034585440b545001030700c00d0926a1818445034011581100b4840070704020010038902688802008621071b0074520175001890046140203c10009a43d00261010403900303c1e040c0010f4041c0c20030f001c03038100e1166400100c2c540c1c10001d40058a00c40c1d900286070304d600381500051809448128002c00d84603241c5014002c6400300000c0409882c1811520b10324a2005100041e1240821030030350401d402e03544203071091080340b01c0512140c115070090712420042890705001400b003690b00c0d2909010f043c0941c1c4d0080710 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 418731285 1250 418730035 418730041
    0x51005011d1e0d0b0a0507020106080703050a170d0e0c0f032b0e091e07023004032f0607020a09020d0b06030f060310020301060f030e0705060a0503040b011706010e 72
    0xca031003400c1100c50700541d038113200707241c41c142c100301510007640d1081c0150701c1c2c102c000583c614045644810baa91100c003901d81181146c0f580d407080900820513412584041080c0d6111480501c0f07100060345240c1d018203003a071840400c100e03104060000190198000c1107440211201d0703c0d00d00804914652002c82e11082a1681103880302048403010360082c00e182c0c144803010721080825402441001d10348c441c10b03691954226140d4121500d10742910101d4401d410b01d444042d081c60011156020000342055540e803030f660100d4101400003101d5240002c0262901d1300042051003c018082d0751040c0340c99040d0b80072541c11492481100c038076503404510b207182204181c000949000000304119164100000c801201c000c096910510070322560300301c0880c9046a0081e241202d541d921454402c20203828250007070040910804840c1c0185403020803207070b9a450103041002c40c0c40c1c1d9031760b4403464649848220300c10b040e00180411241401d40c030344503420004219054544a81400c0c049407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 418732535 1250 418731285 418731289
    0x2060a1b0b0115090b162d1e0201051207021203010b1b1c05070203070506190206130809040506180c090f0f06030106180e150316050f011b06051005011d1e 68
    0xa4901903c180507d83c50800d054010b05851400b507224001d1100b0301300541c400d0002040d07440305000085c00314005100c1c4601ca1031042d40a158000000d0050392181c1c0125032091007158426080000e990710041040604000010988504442100005c02d041e40b1609100c49607411255400c104200c4000343c00310441d1001c0c040d07600101000341225403550485070407046001c8002c0c4140c0c00503c136334030000752000030f25080310718119006184140790640c00010b200160600a03c03558200404500844601c20a1012644148106c00c011900c0e05100020405d080c554509941c1c4602c011112282c0d09983d2402142e0443c4c01c00c2c2002c2040da0700c0c0e20600b0b22100c589500008407044070004101244010b000e5425540030128155407001070302c180203078a44102c50041c07a400524a051078451540207039100054400320443d500c410386480c1d5100400c0ea0303402c0341c0c2c0c03580342404c401e8204072550b0400c507030115540b480707411800c0282e951804201e031203500310b90b02c41880c1c03400c410000e400d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 418733785 1250 418732535 418732553
    0x10503120a021608030406020607020613080f0c0a03110106080a151d0a050115091a1e091e07050f090103020310090f06030b010f08070302060a1b0b0115090b16 70
    0xe00ba50b10401c81c0c80d41c1300b040c1c0380c80ea0058170858000d03006900000c0c01251002c24041d2060203124a038244a0000d521440c040390000c1d01b08110181c0b0030400801e80c0788042003049400c5100c0d58a615500014000144c20351307165034821026a40400e900d00000341c6101600917290b125907100103614411a01c2400e107883c0b40e944804030902440100100f8003406401009086030009541601030365500251401c8500c1ea500c040030000c80c0c100b800f1001d2400b0009d500c01c20020071012115036480d0000036010120030f803511007210b40400d4102690b4094a1503041d4007944a0500d10b040c842a2038805d5000e202c0c00701e015040640c0000054550080683c0f500e010f081513580801192009402000050009000a661604020000280d200540c56021064604650140140a107590709000c181d030803041541041c07000c422004030300804544803100001e4083e01c2c51a2640d45082e2401001c2410b441d044001c10803202001e22540901604588001d904d40740c00d801c603800340c0d0500d10310b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 418735035 1250 418733785 418733803
    0x81b0a020909010f060b09030a060e010b12060a0e0a030f03090305040902070b101a0a1407050115091b0c08030901111c060510170a02040803030c0c06070206010503120a02 75
    0xc04000c2100b44004200705501c2a140034075090301c1008000d403100007141e41d07030081c0010f46505134095594140002c81e150042d2031000800300c00802c46281050000d030720798030821402e0007164040d0f41040740c0030038070b4000c00c0688210100900808100e548000b08000044010f4401381030300d94203c2410544183d08803801040128421501c412a0346404810410159900700e210000100d010400b160340011902e03030082c00e511201d00e4403102e040191084407940f405254044020b11000010640038064031942d0702c40380e0011020713581001c201034220340603401ca00140383c2c81d540a115423a80c00c80f070198901740e0441c6070142c80e82e541c841c01d00d0151a10450b80c030245807004c039204096180706080d88071051b041003000c0c002a40c40d901884240c0010400c0f00c0002002480341c0c404a0070056406138120002c0c44002d45401d07126000189190b0043e5405041003400041e0400f0701c5c24107110258120b840d6101501d440d500d4a00000d580c0c0414445505950200258005d1030500070009041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 418736285 1250 418735035 418735039
    0x127020304080a081503060114040e0a03030902130e0a1119090b12161e030b010b0304032703060b010c02030717161a36030106050d081b0a02 62
    0x260300c0ca450324000d40160040700b4828080380899010a00f8090502000c1107400380140c0203082d581c3c078020310450041c1c061140550080d80d18100c0340c0310392109200f141d41c094042d45010035218414070500140400d016042d40107c0d00e04140900c41117408208158510340001403080d4100000001038040741402e00c058044040e40040011340c165641c01850117294204e5003918000704800c1c200b5155109110107629500d44c00030184035521001058a401000790404142c8107a00c9a560041080003a00407690700350b804820403041580c0000e640700d54484940011080340c034036442429401c5d030f02c0d00000f071000d904c6545044c1d070759111321280c900041e0010b045558469445542c10304c03d484d041c2c0e43c01c5050040350000408440b01111241c02c8031501301543c0003460195055101c607400030707050341c260f0380100b941e0b012042c0c0c000042c00404a824503900071000c55041c042508565095205501075500c9510401c080343e00d5005071034140604903981000580802c0c4200d0034010005c06c025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 418737535 1250 418736285 418736287
    0x120a0e090406050601020708010c091e15020c0301060b0a0e0409021c031d091e0c040b1b010c090f030222090b041e0c121505071106160503012702 64
    0xa0201c03c1c1c02c01405103100381c003a14211911098030a0aa03400d09621002080d1003050400828868041d0b40044070f84650030201c890391a00302d01940c03400090360345030042c1d1000180303000d41d15081c0310300b5004003107500001d4074000c85d01304003401600355903a01c28819542c0c0e5482e913007992100c4031039800c65025100c0840d404ce140b8680944140400404820090500c40140b241820020a40c074011071100804c0701c100281c5042d0707298030450007800760140c02001c1c000000c068041c13001030a01401c1d5600b101031001c401c185120f01311002124070600304200f5507000c00280f031000300b07031100ba00d030161041e20350805038142d0710501d40c1d2504807006a0f94a030403491018480d0030480103004501c2007504402d030032a0585c000340301c04412400544070b12042141000007170099280d021000b440340078254100d14541180408580c0101c2e240300100360341d803a00400080d410f011166200c4807260000f0306514100400030507a0005014000889112120508100c642440403000daa25059019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 418738785 1250 418737535 418737541
    0x3090111040609060e120a0f1403030a05070e0a0b030a0e1c050319051005010f0c050f0c03010c09080d0309050a12050405090f070c060518100606090503030309120a0e09 74
    0x2440f0f01041e1051300006000520075080924180034030f07905180000c001000340b030403076071103e4000703208500e4111000d00c500d403414540420140051482000350000024091a0070b2001500b2700d101d800034140b20f41c240c414140b05c02010001503a030004003035100040e0480010802d640342c00c1c008617134030600c490b02c410400311203584032004500c0b500201103d00c8120130004001e5040e64400d445660f507a020f20902882654800c1e8600c00030f01c075403490034050440b05a00d990717080418507441c0c00600e400c075140420141c00c0034000d641e4a4211441c10103029864020b0440d2500d4480890364200b64651003000184a0104007610034540c00441800c202c0c9550355015081e0b0380b162040d50302030074030100040c40360f0780000446031040002d600c0700c074844c50a40c0d80d908007c1c20000c00d0390a20305169925078400501c10861908403002d050000211136080040c00341c940d0b092170b8040c9129078402c0007008007261f0302061051407007100c01c0c03541c1e07110506d012040d1400005041e40daa0010013039010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 418740035 1250 418738785 418738787
    0x421020a110d080c0f1905031e0f0c010605100908120d02251a150906030f07090509060f0c0a120b040515040608160b0366030901110406 60
    0x285c0801c1e01d024404071780324041c1d00145c00c242c5000f0000080c0468000b80081c042c59145200003210120131010368925140d55504030110303a801040103019140e64440d014410313410242d0746110740011608255a080345045030080d51124041740741c2a5458012802000c0d10762181c040c5c032081070741000444411701d156070041241d0703507070350000717440e601110400012280000b4030402d0044ca500d0245085001e0303d5400c6c0070502c1809009140c05100e5941060703a02c420500848000c4e112500001ca61070800840e120b00e040c4000d095487e62030b8096081c099000d08050031554040b500b420040b50190854040c00d004156075000039402c0760070320040001e03e8000c0c0c507000508090444040100303030b80b12040e065649505811400c28200c80e00300034801c500300f82c4099544040580d4290540f40c010b20a08400b10391908041900c0c4e4440b00c07040c2c00030004a07101009019800c08180c40e51414407610800100001142c45619041c00800700d40154001c0d009000f004d05c000740300c0c030350f600d6807064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 418741285 1250 418740035 418740043
    0x804030506100510050a1805060d06050414070e0d06020405100e010201051f060c020f0a090b090a0903080c07060b0a0e0a0b03030301030f020108060d0b0108060421020a110d080c 78
    0x5660720a050714400219081c1380042c00d000f1461043c2d030700c1d42e007880c4104070103039500850405400ea0000603104006074555401c001030040038184103002c50703054030700014001600c036078032030b42081580422300b0400819030003404c030718100c01d0449000440d80c1c064240364000b0320441d08003d8202c006140065282908aa0200c10004081e8000c01ca1a0343d071685042c1640c04503e003000c1548851075041000d9031245c8094800c1c03a00080c4541241001e00000502c03100c001d41c4804c040d580c13103c1c2098107514015500742d0b40030215010912654446507001412518002c00b0304103011b00100343c19040c00556440758002c0c2d580905000e414588810702510401d604a40c0b500d84c003810440311000d181404030030749040740d611122803440c034415030f401036801c40c000501c0301b0781061006143d1004984070b8114503008080b00d81c0908494101402e059056110000080c1d005404400c10361900303580c000380326909680c05c1503894007443c0207100042c1c0311605581f00071f00a50404100c6218600c4089 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 418742535 1250 418741285 418741291
    0x605191b0f021606050f210603010c0512060103020d0603051504060609060503030712140307050d0b0105070206093c0f031c03050606040b0d02070204110f0f160804030506 75
    0x146031100d030940740d0041242d40c3d01c801c0a42c6105101e0250040007041e0044014007220b07a8881e0303029040520b01110b6003440040f002c081c508640018052049a05080c4200c070f002c0f207400d00d0b00c20701e0000922001c10785124041e01440c1019400900b42162203c2d540c03000002e1640402a00d00c000300c1080302d20495901500c00ba0390305494541c0001d001e0340d0900c103900c21038a014001d1400d243e410744540c000c0341d800189040900c22101c01035400c800c078003001540b01d045c0365101e00d9112100d492902c0221a0b18601031418440200315000150b03854100755503400008640d401c0c81d80c03c0c072425250b030201c00a40e44a031491568010701483c41400055040b100c10141c412803070103410742c0d0070186d40d000d00707400c0c000084c1000146000c8a6200e500305541c0482d001d00ba00b071030b250f42c07407222010a030b100d40d105800c0e1070390208283c405c40c54a070191241c2c460240301c0e01d504000880b6221401c511a240740a04040300c0011028400181c1c181c41c182100d800010058440c0e0346c1e8200075444040c12 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 418743785 1250 418742535 418742537
    0x803070b15010c0f0816050a05211b070f09060e160f08100e0a02030115081b1e040e010f060203070804030b13120f030f0e06040605191b 60
    0x1881c103081c40ea203007406241c01651903035080c400c5511510210b04101c0030030340c0c0000c420841c8410044226400c0d1115078031900050440042508101c0e0904d0390244000040464101c407001208030030405841d10204401081d003c07200b0203099451900429904c5014012990071002800389450350140b0700f105c0304286c0c040f410b55506d0000c042d4038280070000c000840c2d0a410b204049d140f007480e810340d01050b80c400c0c031210f00380c44644607103040e441113501c020056000001030002d170b960b82c0e03002ea0031191541088025810300b1030041d10030120058040c8040080480c9601c20902040c006400c0701015a001c05c0d17580d500c2c1e490580350100240610300401d00f0300407001031036a20000854911540084240741481e0856031280f94809020b80065039802401d00c007000031a40c3d00d6440e164003003c0e62a0301c1e058000c02d4802405440c0c001c0040c0006030700d48400c00006040100e4501d0380150300110008550362600140f10103042c2810898103e83d2070001a6050b45803006070424103c00d071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 418745035 1250 418743785 418743803
    0x702070f060e13021e0d05070f020c030a0308220c030203010b0d110f0105300105060a0801090b04200307080c0403150e010b060d1b03090506010e04020118080307 71
    0x25008251000d81d01c2e0300072680c00403a202d9600b91400394039406030180301050307840499844010b221115064020404a80c03240395900180081140c1103024080c03000401c0c0081c06c1000d440c1400039448a030301c2c9402800344209280015414850440740c03202441240d40300c51004500e030305000707014410310300040b0b020b58a842902030702440e01d5401c0c019582da0018003141d40c1080b8100f804040c04003046000d06102007401204020010809030810f52221090114074070a40265041c00d843c0040e402503000d00710410140180c55800603040341599000840410321040d100702113001011044035504007000c80303600810f10141e0060046000e02c00d180ea4044154668680003045482980710082c643da5405561012405072604071b90b501c070856200006504244101080d010b6116465480b400c030398138000c1c008620442200038400c060280f50412040f41d0342c0d5641039907040c06020b114520102200014216131148194482403080c907001001c0d6655a0220701e540c03500111011a801c40c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 418746285 1250 418745035 418745039
    0x4061a0c010c05030603120702011e08190e030901030225031106060109060c0b0a06050a08010605180f06120709110a0806030d121104030203011103040212030c0703081b060702070f 79
    0x40f0030425a80640c400501400d107202140780d140d00740d6405104124180300c0b05c407007200c0050302d104000b2801c3d20f80c2078542104c80e150094007011800d810440c903405291070300450009a45001040d00c080343c0081c240141e40310040a030450407100c014609485081450000b841011340c0040a0300c080e02d19041101d2051b281e000c01505c59140300d01520f400503c1c00380000b008520605035050700a070340120300294032038644001c649008415000306000ea91202d00c1003156080040d203065407220034895004280c1040c000040c02041e0241c0110300c80e176020b5030312a43d003113020302020000741900755080049041007040c0b4503039508910901c0020840440014907035040218600b92452a02d42d50340c400c1c0340c40c3c103902c58020b02c00d1009802004100340004030051710f00b4402d8000030250942d00e40d80740e1509204000c98020b47d5854421950814000301051000c001054819203501c5000b540c1c07200080d02608040b0118260050001c5c421503050014864009c150b04050726000f41e000e03403840c0d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 418747535 1250 418746285 418746287
    0x70f02060406030b190810020f09030d0917150c0c190501060e0105100c1401020d0e0106030209010501141903091a0405060606070b0c16122d0e0f04061a0c010c 70
    0x446503200c1c1b0411904003440003454001e00fa0300a240c140300c6c40b1110f504041800c0086407805001d01c070200d021400004003484030b1010340d03905c21015103001004081c5a001c403402e40c0c2e88114050641c2400c0a00821000d94002050001d49070707042400300c140e40740f0b003082d0070840e0203010244184146400b802c0000318041c24854140e10103800d0075120007000740740507500c02082904a0300d980029542c02e220280100140f03000700d40c0742035846400030884908500411a1015060b840181442000d2401c028009084010389280755080410b181702c1d007004c624103402400046000500313a14581d14198122840990740500450041d41181c1c1c0c1581ca01091012510070100080d054410b54000110804070100c002d08805484e1114075444061550302e460b01207500c5c4402101140c40d902003e0701d01291005640381d600c4140da0850b050030360305070003d1f00320284d4035201401904540403015040d00d65070044c0006104014030303054002c90046842c082ca4000c0d15800c40507509080081c0545 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 418748785 1250 418747535 418747579
    0x1e05101407030c0311070f03050601050118090b0301181202071e05151e04061101110f09242101030b0f09010f150303030f05100b070f02060406030b 65
    0x950641042481c004035520141c030b402e0034211044040168400080100e00018042940104040044400c80e13030f0442c0313030481c14120141c01050400000181100e00400e00c00c074034001702c8007580000034544a40c0c43c0030a026056041000480e402030142401c1002484448032151154075401c0e41c06103038440c1a144075100301c0030781e0304401c1080e08509108614200f0140d0110b41e0100b030034189051100c0055030101c080c4640a984c103070402003000c10005421107600500c40d59910000c105032203d010300244c0c540036402040c0c1b5500300c04601081141c030b40907c00500c1c001c4540c1c8810714803c50180130300c00e55006205001c4440c1e42c0c0c10007080251004541070381a07a51050954041d80d4802ca6040711400005084a0156407900a0009030f500c41c3d12450005c4580740d940d21a0081c11070030040e00395003003040000030300b52600c4d00b000080760604100ca001d40b001e480d084e554401550a06a0301c0002c0720300080e51014000400040894056001d1103402d80c084c2c51008100309500349405c3c40c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 418750035 1250 418748785 418748807
    0x3020f1b04150303090b13090903020f122b0b03010e0d0201060e0603060c03040813030b061206040506160509120c0111060c0d1d0d0c03020f1912091e0510 68
    0x320380b10b6501030201b040c4140107005410580c01c018010390b95110b1084065903814503066000d60801001e021607003005000148140010726070700e52521409030340d0740e02c03040594140c41c1850804001c10225030891504882101800240284000c0001151190301c964000311240003562034444001a04040600381d103200c0c5200602800c1c0990340d2149000c0290300041c0200c0b1050810000c00146503040c0d00d40ca0040c500038400f0001c01c0c0307000c200b8030480c555140307031403c1c480d4400010800094800550309074000c41301191040c4801e80c000c01900c00340543c0743c0703156010904030134081c1c2200c00010f134801e01640c2642c9007080e20703440840c080d40f07804044d20301c41c910281c100013910030309400b90070802940c4076044400841c078520a404c03900780f0300d5042d12100082d21154075201416410030000c2030790321319000035140440d03030b80a100341152118400104089243e404864004d40645080c2c0c005082c500c00c4006801c0d01412400c18004c4580aa01d01c2441381807040304580b84500c03d0515 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 418751285 1250 418750035 418750037
    0xc050f06190902151e04080304061b0519020303040f0e06041109030d0e0a090f1a0a061d040908120103051c21110a120b150a0c03020f1b04150303 64
    0x7489002c0022001111307805849030362141c114178850802084041402070000300180c07405191154100400281008075209501d90492468641c480c0031840118950729040f26844c0d60b01e4800c036840c80803c0c2940110b5008400b04038003440c0c0064101c0c10140940e1107200100e0701005503440c0f1003c02a514042c0803452905940074100341c07581280a442000d040c400020504401240e4402c8844141d07201084004102074440703600900848064415903c42101223418011b00c50509a00030008690a003503048400e40d189a8603110351200d40c00321440c0e6400295442c1e9941c010200045407003428401240c0d5840740c4c110420302528911004881401d595490340d06d610340031881900c0f02407100c5815104569512280e54010760140c008200c0400c80d0f4941c41c02e00891141c0c42c0080b10034074440daa000d0382011018000002c0303c081228011203e50501c01440c005608040307107003403090b00c01c01003a0f2103200d000400034a40c180c0b2103e80030008440900a5600508485e58640c440c1e01c8020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 418752535 1250 418751285 418751299
    0x8061924060807030f0c0c0318030b150d02030a05010c02070e01061706030c1e040e010908030604050c070512040509180a030f02011104031406010b16060b010c050f06190902 76
    0x401030600c103081c45504008680344c042a04801107965104a8241e03c1421000c11071810001c820590854092000780d1512803039500164510740303035558000f03002000d001e42400745400001940e510030f042950560740250848203540014a061402170401040702c202510032140001840b4000300110350594040e07a5aa41d008086400110214100500410f60500442004c0314040d16031200d145640032081c050440d1040e000000c1c4011285045404006070f41409400008180c5040840303411500c1520000f6040da9000e48124840c044e0680050050055030700b000d01c0c0d1983d0401520980c0c40071181c4c2d69076504c54036201021120803125034461900899006000b103030080107680581140307400089001031580e40d942d11680c0c0310b904101c58141c010600c03800c42d0401040450b024040c02005c05180c941050000c040014040400801d5507031546c0e1100d11903442800d00d07a030090350240c00c44008000003040706072645000c60b1032226004d42645901c681241600406403002d070050601 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 418753785 1250 418752535 418752539
    0x80705030c06060913060c0509030102070b0a0f020405030705090709050d06140708061f050408030409061d0108070909080d05010b070b091b0402070804050306100f0e061c0302010608061924 83
    0x2c6001f4161322001981404024001e00d41d0a840a0004120f1244100007640f13036232402c1e012107000c441b02010070340c0446106100c18030040c0c500042d0a01999012250300d006c6940c0c034901100c40d00015080560010400c1d500681080040c1d004402c018110501c507503003596441030700725910102164800d5006400b0aa04002070010b0010141403a0042c5001850562100e110354610303400765110100050f914a010411320490a0b4001d000d01d12100303451465525001c4c00c2c55445003e406840c1c0382d50350720309107042000074000031a000f4150342c840a1101c1c3da51109818a290400c40059a840030003000041e21002c000c15480c043c0d1b80c0d8084864408001314050000a40000e1800c0300c030010300300300c08a280d54041141920a45181640c40111801c104441070381083c2a4018080610751301d080c04042c2c1e480840c0ca4080d611000c2e03500c40070401508049016088076032107451781e40a100d0611254501400426400340f900c081d00703011000403002c84010030040c1e080c48003c40318a05c202 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 418755035 1250 418753785 418753793
    0x25090303020105332b050705030a080906030c090a090c1e020d03020903030403140a03140405060f0d09020405070509040b0f030a0b070908030307090f0522050601020703080705030c06060913 83
    0x20030405002410100305c2a85c0034440c1c0f500f51049586415619464004050402c42c0800400c801391200381e0103400340c2c4220b40c1d5a0f145501508000c50300c44c102c04000110450904000d503164013030000d0540d80c610340d460401a008001d810051380008a011904004001e4405050f240d90440c550017402c071800200001c4000750001020355030f140c04200000000f00e50f00a603075004175002580a007698541d9480c0c058549403881c05043c012201c00e0100304859629901a2034040c0072140c0d100c0d54680c9803145442c0104900d14000b940301d4944070900c01220b1703000703019200481085c0d80402030030841c0410040080514440e00d230f4980d0000303039001c00180024004a4100b1810304228100e2901c8032445415904205c8034900059820070003000103014601e0350303500901c001c0d9847c003000343c030340404013510342e80d0307000211491500c66004c44c076542d100b00302c2d0000454100490787c0c0c5032102d5143c4107403207900c0700d9002c01c40ba10075900400d00a00d0000c8002d4082d007028020b010429031542da03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 418756285 1250 418755035 418755121
    0x807030b04020903010213060f09030c1809061a04200306040f020c03070501020706061a0d052203180812041e150507060617030d020325090303020105 66
    0xc094000341c007404070003d80e4a09001a0901501c046920780c0340d503040c640020f000941118080302002a4200e040002c82c014400400c1581c0c1c0b00c03a040004004031440c920302412045800600d218648000001c000842e40101c80e04920700b15802e0207200c01c00c0a040100e4041402c00c4100100f041000c107149107040c0d4025442c4100f0301c0f6002d418481410740031402c42d00440030664669400140c1401000000d10030711000c0e10f00d910a55407040c08088a010090048c461022002d07552500821440000d102c01d048003801d40010b400c0280002d40f800504408011090f907041d00c0c41038a02081074031002c90030081c0080085081c0b410f0500d4541e60700800308410060300941d603202d48010070252800c090800340202c0710307282c040e568000c5280a100f00c4a80340d206020031160100c1c0c61140c0d100220440d10b040f10380880140e02d0f500e581c030343e0502d002c115215502c04520104000c0e501c80c0d4000c01c0800849020f5002003100b070356101059004040c120380d0080d160040c88041c284005400c83d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 418757535 1250 418756285 418756301
    0xf030905010b1503100b03070903080306030c100f08090309060a1227050609011a060711060406020105070923010c050c19050406050102240910061d0108030a080703 72
    0x200081500000800443c810407036900c101107075804004100000c1c0c0d040c0c08a408000d11072225003624601e052000141b0204803400020300810300003010403003030755040116030b10704903004120b0322401036020340281c00003010311060804074800000142d422031020058600b000c402400d0185400750685084440f000413100301a940b83d031300c20304a4041c490790401c4180f244442d419980da1f0075a141043d81c50220014856100c6071306001c000c1e620340d40302c18144c1c13502d80c50584010392100a1440d110303505540c03440c1d2040c0c10480c0864000b818550540206001d4003042e2201e003013641d141c8a0101465a0b2020000280c0c801c2d0349080b0b540703510039240504114010f105a03440d034000c1a000480d10141c4210394150340340e10403010b0159151900c9400000c00090005054005042c0b154080002089015403c030005280019070500414401d608080180e42401c100712500c90400002c844444090240024030180c00440d0304c1e02c0020450b8402c0c82c0540341c0c4c148503619007100b1009000c6103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 418758785 1250 418757535 418757543
    0x7050a08091318021507020d0206030a11030415061a030103080d060503030a0309060605010f120c20010e0606090c031503160807090c030902180c0f0a02011a040c0f0309 74
    0x2144a0b1405000b541c400d5071110050264160a4480070b0300400c001d6103010f41c016401c0b0b0f11700708040350050307541c00340a190841e41560700b1500c0e1b0303030703160310000080c140424481c8941000204000400c210a0150805460b0a44040201d1501d9085c02104591006119170008074204014000300750300d00c000c1c0c00100c250b480d0109409442d100481e09540060515070086503c803d80c2e41d041080e20f00404020300028a00721703901c3c03104c0c120000c18272600c1114069020f69580e070303141e460030320401c1d20390707102150a00e0600c1c0310002e41d04c02500030107500c2280c02d03241c003e00c00410340030301e8030841c5603008071080001c1c281151100705200c410032050074601a03241c4101e003681803c00104544c0340b070007000744d440506101480c0071a11010349050034500e604043c42c2560800040e601d09a403d40a1414001640400d94030241d4411452040c0920039103c0000802d00c4068113034150465a0030708008040000118050740a05c001c0d41c230420001401302e00e803800340d0722610780f00ba84117192842c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 418760035 1250 418758785 418758799
    0x304050a141603240509030d2f030f0603060402011e0908060c040303030612020604061101020f191706031e0a0206130807062606040f110c1207050a0809 67
    0x2c0652290340c0c400340b40d10032141300000000305940082c00803030b082c003e03000605042c0300074a0000345183d2684680725840d0f0080783d0320310110400c0d60303050380c0007901040d12484004104c0554482000ca6402c101d801003000c503501000603074542408100030340101e506860304119038804440800c0e03041d400e08941010031005c0a000660712808002c0640a48411214160740b04d04605000702a95100d80011405101c502038140058480408481c21610b4510f0000500440c011480707000e0b2080c2c0c0c0003c0041003000c0395060303840a0012000c480e03480c031a10340f5280401504074040510a044480e0f59040c3c0001001403510803000180c074503045204020f5812455050b070000f1a03e801c840c1c983c1c00c1c6100700300018416800d00f0231001d8003034a0309040440300402c10012754070074a601c000d1a0420306000c840403c10700c3c0c0702c4e6000440340e142ea0220501c03d1002c03404103900c0c903401c482002d0034540b1600c40701c5c545944000d01103402f140d130410050080d45203591515425035104841154018038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 418761285 1250 418760035 418760053
    0xb070c050f0c01050d18051510050307050918030d0510090c030b09042009090102030a1119050d090f050a030e0f0303030c07020607020d030c050d2d02070b0703050418020304050a14 79
    0x6014001010351000700c1c43c00d010310342014270405020000c01e0300214001da121400c140619911140d0141d4003520f07603070000c8a84002815440d085001c0c82c0709205c902402c0900388400002d400d400c41d8103407401c285080003403109010045094820710001e158002c0100c2c030224010411050990107a1030004030305008800004010404503402140c107070382c43d03940c04424400851094001d03005010404820b150400c462624a1070b40c000092020340240000040d80007903079011a005800380d5a000311804040181078200a40c665500450403000150081017220080c03800901e40180d4407030203402135003036903a01000b41c02180c0c007548050740d0010003404854016516904010b01182c40b80e603e00d006241d243c9015441d003200d6600910074055400501040b04140480d06059007040034204200407121103000d13400d109494009840c1d02c200000d00c2c0c0140b541140042040381c402d882d0030105ca1417018640d401f00d000c1524020042c0c0c11061a61020070040f00304e00410016001c25618284 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 418762535 1250 418761285 418761293
    0x13020f04020f0d05040c0e0c0d090618050d02010b010813030c051e0a060b04050c0306040b0d060c021b060c07030b04030908010603120806010306030b011a04030b070c050f0c01050d18 80
    0x6004036100f801690384400402c030410280d0152400146034100031440c450400341105040d40c0100d60351451050f40d56500e00007400000d800c80d032000c070030788042101ea01c41c4505244da168103040341e98602542c20300f50511500d500c16000284a001d03012000c82100001e95000c031b8001091882c00c2e540d910400e50f003400c1d890150030002c4030308045100100200081440e201c41507400348008640728524080801803101c00d1002265800802110000f4201215100203010442c01d9500a012640303800102c441c40c680001e0704807645540029580100011380c0c0c204502c3d4881c6c0e000756000e540112204000241007040c0807900035219041c04100315866904a40c00c40e586a07006442c25804250b070a10041c1d00120280d07040700c000c1c079080c4041821911440d411103418072920002643c00d407241540710480909a031301030741c0c2c02010740d112820b10010007484009400d9065607940103140e81d0000d00e2800080f500e50902060311031500785442940000018502c2a000602c004c0501c10030b44009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 418763785 1250 418762535 418762537
    0xf032d0c03031908010b04030b04021302070b040c050114070c140307080d03060e0a09050d0e03011e05100e24041d07090509070803071b150908010c030513020f04020f 73
    0x40460003d506100b5041a0004015483c180d001005007002000306002017002c1c030480070750194040e184000141c2559103410000d205114000e4148225031b02480104030081c8803000445100342e032181d6082180e0006c490440c03140c948014a20440c03040c00b00b141c009030101040c811700009040da40840da44034641e50421011100360b00c0000c0d070b555000e00c844045e018400b0340298400c3e4080162009559540c0d50714030f4040d241e5014402d40c801740c002c10342d40940041c4450000d0f081a130741f0200030300c01101c024040542e849858030b404c420703001c24848240d06c4510700c5814401d0144021080354019400d0700b030500c2e10010741058031010302c0912644000300d80705025400800521a0342d02d0402c5e200c08903007028050039810381281d00d00700200b0303500000391038035aa040a511004c4c4489828081001400d80e4000f4446221107814106030a8101443d0030488203100001c0c00551241c440440480b04100c0f07103105070b851703810301840160070b0444110b03c050034054001490000303000f41051503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 418765035 1250 418763785 418763797
    0x101505060406170c180f1909060824071b0606032004021801080c0c060408030708090a0327030602030a090215031308030a060506030103030e0f032d0c0303 68
    0x42424080e140f00ca8920004001da4000c0c41c43c1c4003607060914882c400d84031442a0003803944220007208003001d07259120720543c00030101c42206421007655801050b00609601d00c0307100800d000700d1034400724142c10407480c80f040b6450074210070a5036581c500107a480c40c0c0d5038650300502500c924101400070b40940704000285000b500451204106688000410040c80324028041d50051040001e100c20501d80307546585070074205000319954040301c0343d849000340000c0d103000307215000a0001b8800e1710300045010b45682c2d610107800c0d5869140c0d80d5982e80c8a108018005480401c07108040c1800c400c0d00d40b00380349442030319030b540d6a881e240c483c00d80c0c00a80d2107444295541c10610210302e015041104144103110509045150440a10300c0c0d02d00c00c03010107000d0354800000070361201c0702c0e80d0020010303050042915071a540c50303003001840b41040da003803940104503102d00f4540d41c1c039001814203006032000620418680010542c00a40c0c060005654a148600c0043e4925603600340040c02c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 418766285 1250 418765035 418765037
    0x408030324010e03100b2803020102060a11040b0901020f0d0906020c09010f15260f010e1b0f161115040e0c131e0513020c101505060406 60
    0x20466425900c091006005a80c900d0503c1400b000e00d000984010580e5403001049250000e584401540401c583c5500070081458505817080c80c802880000040c0c1000d4900030380c02c80300103641d502a804100e41000b0507110301943d00f0b00041003082041001000510410306c1503030b0401d1138011406c0e10b0910302c0710003a40403e44003001484602e0b4100b0440e403241c1d804880700c0403c0d5161100c10340d21034140c0d0158a8601403410000081d0074021040d010100d04c80c945c01c0e190791a00300303001c0802048166180420704584100000e00100403400380ca008803103105180170850680005190154404154005040014090f8402e808100d502014140d4044c8540541d00140c0300108452041c004100412522061205000c208142c42a580c4d010400480c0555145483c40710001645925404401c04074449903069490f151000200c404039074083c5c03403c48184040f071307880707000b680a0500c400c0b94981c04008100202c6041e40c01c00e00c1f0040700a1442c400c81500e0780d000c907c85a2080d04810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 418767535 1250 418766285 418766311
    0x70302070b10050424050d03090e09160504092114131d011a0f07080d09300e04110307080708090a0f0b0403020f01021306110601050a0b0c0304080303 66
    0x800c3e0b00b001d000d585c031400500e10990101c0000603036110380a0103a8050140601400c3c0000d2040600400032100a00031200144c842c4e45480101295200629000c0d02c16000c0038000c0040c06040038041d4041c401d038800070b44030449610800620701d410991113010100540d24085c0905026004000d00c1d510003288030182c1002e00b00105ca4100c610014004c0b0140300041004110300d01595401440e800102c0b06619a140610760101030381e030041c01c4019083c03640015030100b000541d85d001200704d521860040c41c8044a06001681c0e2015195106c409039022080c1310800a00c01c00140c01252030083c800140884084108403682d0811208400851140c00500c14110341001000350300c030003145d0040c203200e416039071880d1040540c403000400d8030400d400481d08050003031101207024441c41000715102d903038048105400d11003620070b40d001b09840c030560501181c0d000c1204d90694101522948020b40f51600c500066440400f42c0349640c041030001150f540010300003180500581000309e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 418768785 1250 418767535 418767539
    0x907080604032a060f20070f0308130606090903020c041415010c0b0106051210030201351513151415070318240e1212030a150807050603070302070b10 66
    0x11980041818041c40884600307021000000310323242074000802c1d43c10300c3d2420b540d88480141002c803440f01d510081c299402e02e00080b0b402682603000d002c006000b5401c60301c240c0000c03000e02045681c24940c0e2802d400c900e01c00199000c2c10498118041007062500200d0100c4640b669825481e00703030841c40c0098400905400401c4501400c01d800c00606040703c6d03140c0b850340d030003e440c00345070b0034050020f24800c0c207a0104403500d0b0790b1002c5181d0190040c401e080e2a15840702080b408407001c10078801c40420b214080c1c1d000f124460030f00f505000b50500360205007818603a40100c1c40f02030400b5806441d0702e003202c1030049650041c0181a10a4640c84000701d070b4030110403c169080d8105107aa0802800307010843d580b12415025403c0c1c250a101803405001808158000c0c0b8040414455210b46a980c1d01c601f440940118800c0ca00d01e902004450350050a464803c401071084d06259403124409000d02d2401400958010301142001494001c5581d55501200c10171149042082000401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 418770035 1250 418768785 418768811
    0x180f0614060612190e0a0b090d021603110303040b0d060501030f02031e090106080106120501061d010330020d090509010506071104060b0f030907080604032a060f 71
    0xc0c0503042070040390b4050030296040220f908507000286424554009543c02842984a0368000d041e02e0300c1e040300361801c80f0010700b000341210000f0f90355034600c4c0c8103000c0780c0f0104038804140c801c13404844e60f54121542d80f271615080e00e81546861250f6040c0800c000000380401950010114200b01c083c02040e55850040090b08607019a950a4103184c010800c000e10800c0142600450514802c0006079503102d08030642c0c014140c68100100355880c004011a03503001d4003c5014296200e5070080c00304c191125130300d2852440340501000910f8000b401800001e0841e490f0a00301c80e060505000003c00f5450407070b000a080d840b0250240e00980303c42c000c0b0540c09070040c00a41400c0e0b515285551510b00403812500c00c4081c003502120b54010980c441e42d5881e04a0700c02840050200c540700e02c48100c0708040c5910070340b245c884d980701d0741000242410001c24128400e64040d1070304c008000c04210910790b00749483c062009181910303c03403440018050300c1008100140090700041040d48411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 418771285 1250 418770035 418770071
    0x91014090d11042c240a09080a0c0c090908090d050a020d0b0603060f090d03020901020703080427091101030207050c030609030a03150b090f0126070311031504180f06 73
    0x10010300d581046402040240d050130b102005e44800c00c041000f586d450041c9500140001c800c010411007001034800202d0354404c9410103d0b50284001581943da905004000c60b140124000c0425605001c02c110b2840e06400340402c0e1030044040c0c940e00d818540c00161110846102110003140c1c46040c0659424108103a81d8030040d54000c50f40c15003002c10841e565004490072034010190002a00240350b4820b0100c60011a80710200903185c40d12409040040707600b071594031019982d20382c50a84100d14034000c54190b95040341a804c0c0e1f203500c413001140070b0b600006040d5a1881144d402000ca500c040000900c01c1f180e00004c2c549032180540020142d91402480c100d141b20300d07d0081c0030400800b42200e9401c0000c4070095211241000140ca00455130320111a4050411f00d4040c179820b0040f59661046c04945e40070446a00c000b403011302940400c3e59500e005000d480b200c01a43e040a0380400309030340000005449000055a030070700b070710007240400c40c0d80d180c481c8844202004104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 418772535 1250 418771285 418771361
    0x40e04110607030e090705360a1404150e090604050d0e03030405091008060a09050d0819050405100f020702040b0108010513020f0717091014090d1104 66
    0x1c03855468000d950320010111071000c011540b02c1d84a01c404248502d010780300b11070401180c070700e081c0c0c07210b041c8510418980001015010910302030f150740d40101d11381800c078102034411600400c6141c0801100303000c02482001403d6030b0300f04c60300c040403d5034040750001a02c41e202e94001480350740f4042c9442c1f41021522442c1405000e60684a0312003541d000c01982c00b45e07003041e41c00004c00e585443c2d924594088a621103030140c0a140103000814030b05800074003800b0b0040d8202c0d02c652034480000c4034120703421030300382c842207d00c0303d0150403045442d00280d8200d40500102d64403004240d030f101048500890f855a021580055540700714142801a131000800c24207182141e9071400021603a8800243c41c506525940028112003a01d11082a11071080d0000c100c000c80740f03041300301440a60721403222584141c49501002e00c600303100e54507030113580044508040c10080d103081480310f261000c0a048410305450303180e203101074aa42c03140b0f2001c0040c00803070003050848080702c000000b06c05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 418773785 1250 418772535 418772539
    0xf060e0f0a200702040e030910021e0c0109090b040b0a0f03051e0a03050307090e01060807080901090c0510020c06070c051804050a0f0f0c030605061c0c06031808040e0411 75
    0x410010002d400c440140c0380440e0b0151008117403102c40659041c2075208000155070f1107070000a0405d081030b400500c02404501c103c48407041c0030300e4800802e42d101c101c40036540c00520070807424000d9034402c0d000f03642c040c035001d003021074095480c10003c0d14849843e0089601400c0ca002d082040c00300810034482082e09410000011102c0d000c101d64071400c1201d005424480d000000c503d006108109101c020142909a140350796102c000040c00c00ca01620b0420002d6a0000450704402040c0309040c20187d0014000c00700754540710610202005441c3e603901940102d140342e400c00c1c0c880d5070080ca00d0f1442400c960b0b05960500b8100060180c1240304804007406041c1000000341002403400c440c55040718680d1151000c86c60f1075418184d040c0b00003440003401c80400401c0000300c1c0c0019000381801c4403c103410040c24140a40c1801070030b0005801d07844c8185040103024043c0cbd000d20340740002e140c15001070042c182c07582e000c50380c42544030a410b2910501080300f0300400c603002c50301d500c04c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 418775035 1250 418773785 418773821
    0x5191103010308040e040510050108100c180e0a0605061308010e1b0d060b030a0c0609080f03190c0c030b070e0a1203120b10230705060a0f060e0f0a 65
    0x41d51140605401369000740c0f0041d01081020806000c803c014034541900d484900744580d42c0c40c0d080054a0306031a00c90360300c00c00c3c2805514004d450042c03000d441000c8181c2c80d04240503251045032102054050814444107a40b00c0300070410341c0711400140000000040103105c51482c1c074020302d01f100d0001848100715005101e030720012207007800310320005007030482c1c680386640301d541440342c018580c00102c641d152240f0100391041001c0a150b20040329004d07180c2111840c0d40e01001d540f074034110000c1c944030750800c10060382000018a41c0308070080c1285001c10421956913140c01141d94660800e0340c2018600c41089107103075001c1000d484030001520214450b40c6001507001404460f100c00038140309403d6082d16401216510ad00390601d8014100307140003602c000c0107020419495500ca64140613002e456552070601703022a00000e50000c0200042c1d644c2d100c002c0003c8c03000c08100070800e500c0b00b10000d0b100480310b60550154011445e00710450500a240302c1c01c0b90102e064502c15091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 418776285 1250 418775035 418775039
    0x8010605011b0201050d1a212505090705040e0703020a09090e121602091302031507090e040b070e0103061503020a03060504060b12151c05100519110301 67
    0x1030710882e40c10340d8081c80c051120091041e0320050b2030307030f01456201525040c03a100860014002285007030525103801e60711442800c1d4150003a01d810b82e0204080c1d1641d80c41810706c0c1040908040e2480341e040d50900c03141520a86810020301c2c2c4c04815500700d00040c0c004901807003172983c842041c0c0d40003011401e04500d0a608104050940303d018810324150555401605902c604c0a10580000e506005000741c0e0318a10107001c4421032070668030590041c0e804200141c2411400c11160f003c0310b800400074008007203841c02105402500510a408012040000095010076840b03400e0046128000711900c603d0941c2d002403c20888504040c10907007005001c100c0407411a82d10300d50020301c0d18015a882c01b4a013410340250141e607110035001031510100040f900034030806800540c030401081462922208030200200740c0380c06005074080c90074268481000e8400011f070742154440e40640d00380e1010001700b40110340003200d14078031700c4002c2c444d0320290b20744902ca03400e400170a0040b081c1c1154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 418777535 1250 418776285 418776287
    0x20109020907080c0c06070518010206041e03020f0a030909140f19180b0603070501050c1207030c0602070b0603061308040e040302150a0903081006080610031b0809070801060501 78
    0x1c880500034000380032149020890680345803044419500d160700c102c039014100908001c0c65903000610560010000d20010041c540c40801d10a000d180c03c20701041c50618490010300d41106280b108405610074031080e8000984140f00701d04d100d40c020f840784c2c01c0d0f11349400000c030166507010520100b60404402041820100c144030590800d2007040c0465110304e9180e4100d00814801000c0c05011f0048000e9408022213405498072600c0305500b56110039544c1d038010b466034002c00a12004a81001d2422490031086102806400380207103071510450240d610703010101d03401001c0c00c0d21416584070400146082c00c00840c1d80144c1d0100ca018035103001c40d11468124000d034000c140b02e9810040103d814075108214200c40c0a00084981c251804d044040c0710091542c41401c40104000c1000512002080d06910301220030607242c40d406992080c04002c11564044150002d240d901c882c1c443c0c081c0c06000e450b81542040c0c1c0c07918042800c18940c0e0510f04519544200314582c140078050004ea = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 418778785 1250 418777535 418777549
    0xc03090210030b0a0f0906260d050a0e0603010e0f150a140d0c06020609010f0b0f060a1e020a0303050c0306010f08040305070b0c0304140109030207120c05120d080702010902 76
    0x402032030000380c3c5148120015003c0546a40020000c50002a0204528120b6031140d011101d02c034021400c0c00b01c10100e148a540402c8102120f5a049121020015801000248022021458144440340e942d00014881e0b03003080c2c001c0030b038822181d801c1100705012213300f0394101003000c0107200040b01c400d0024042103001d0003221240c02445001d00758980b600e80e5a100c0907648000d00b0082e254460300c00a544940c1120001415800e150f480e484016140c400d9001c84036014201e251a031000e14107010003a030088800104009292401c87c00342c910000340d80060b0303d100d6001d08403465803402c0050540f14040c26001030900e0410a21a050ba040036807a80c0c100d0b024141014203130b5440c107043d1014040d1240181080c402d00c404c12010002c030720015846140320b9491840300007a0b480704103080320b51014004015901902051180416203c41228a80d00c18202d00140c1c50311103000c03410102090500c0c04081e0b0103c40c0240715140c00008160f40f0400b00d10082101a070143c00041c0c017 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 418780035 1250 418778785 418778809
    0x15030f0516180905030c01090303020c061e01060311070f06150b030c0318031b0601151701060503091609152c1e04050715110601030210030e0607050903010c030902 72
    0x1101c0da0350100c10f080050920645412001c58070007000903050504000d400380d886114808c040340106000254000035610103034038030030743d041c804000f1a03084c12000d90050201400c0c2c40d0100382e09020b808000340b51803210492007480f07100003040b0003864150440b4039019582052100340d00900c20054040b1000042d00da00c031001c40c05040d800c1700c00c51305082c01c40c883c22424941400381100c002d00d01b100005500c604070f891807260800c2540091742c0481d00d500110048004001c0070302c004000140c85030024503080000e000660f1002010381e014464059126030142c4811500c46d0820403080300c0552490300206003441d0b84402e212003510300c44400b0007082e02c0303e504d1441080040b4400d1402488401d4505c084d0081d201114203080c01d105d5618402440f90781d000800d03405844c20b07514859101c2480040082004000ca64219400c1013054001c3c1c030880001c06130b0300e250882050b1000c114082c003503281510382590320720580c3c0600d401e45d10320851410034142448042ca0042e01d880d29003401e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 418781285 1250 418780035 418780079
    0x6032a0b0708271809120901020c010c050f0a05060105030c0111030d0f0906020a02012406021f020c061f06020a020a0b090d02040f0218040b01050a1215030f0516 71
    0xb520703002040350709103000f03203603254903030030240028410403044048010507009140c41c00840d00d010b21101c4210030300d031140260480c0103810140c4d8052584d40503a6494143e14450419205004912040e0798603140380703180103803840d81c06000100003a04040c05000940c102c00e190210070460406401176683c0310300c00446c00ca403030740c4520307500c1688019441810f035258020001e642d15804040028042c01c401c1460040300441414200c4510079840740d10030807200c258000e0541d10b48208074002507607141d03407007141c6241e408200ba900c545030244a503030700c43e000520360070110700b05862000b4905901600114103540c0806004400b61b0b43d000e0018048510754001640d452040d0004034800704c0032034000941080c105000c00c56110601d4020702210b501c0c02d903406025948840070002a611503103070943c045001045482c1101c1d214a4208118080c4948080b41907450280c4c403030200b40c0e25600a481654030340707032007204005040c0000d5000341254216500b20700d0030180340c11040b15841e62182c0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 418782535 1250 418781285 418781317
    0x100203071b090603030809012d0b13022b1103060f0d06110a1202130519170a0c09020309060a020c01060f14030c090106020604030c030306032a0b0708 66
    0xc441c0c5a022400401600c0d492406000ca80d0340c80ca4007030899082500c80d00855402c0150304095808207544480c510740c0044036884a240380130300101c00130301009290319004910441c055448079402d000400550808000d4960070500391000b01004580460360104014241808000501c0660342941d801c0a800c698072100100c01d00001044070f42d80f06001046c441c204100002036000c00c0c4050300e0364210a483e03041c0006071010022040740b042909040401c5201e0350b02740040c0c2071288240e1050188200300d030740031503241c601d8a43c00d61420120b800030f0380c1c02009207004004081210b03d00404142c0310540c02d500748015100d8031840001c01183d581540804d5402c40140250001001016100003850341107803600d800401801c1004140c0d070003445075032080c00d41401c08051840c12200342d030f80900300c03036102d6560442e0301d6407001400354101500c4000110105411110442404102c041100c042c1d0030b402d4680d61245130703503501003103441034140215004603183c001218101c24041201d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 418783785 1250 418782535 418782563
    0x607020d20061f050102030a020604200a0305010c1205061c0318080a050715080c160c060201051503160b0310090908041802040311061b2a10020307 65
    0x155485a10741d0100c0d511849120b080c00003181c051940c84000d00c1d18940d0752882d15403580700690796440f81c180380d2401a446800054013050f4032007420005013100d01c0c2e0030b503102400480050741e9800e60b42c1041e0703416550b0341103180100b6081500400041c0322040248800d162650002c1d80010389000034501551145d5505030425200e410002c951a030b00c1d1000d0034040751210b800a42c3d9214540c8202e84a219240b404a0f400090400f48000684a41d81c0c400c515a01c0700c40f4080280c000c81c254a00c40040710240b0384c0000e0702d404041c0050b20107540001607500e03003098000c0240e01130071149030294018210320b03400e00c8400b100220a54210041550b62600c584d0908203010081e90b02030305e0f480b840c06660404007d1010010300c1107941000340e40300800910030529040348120311004181c64808030003008542441409003070401c64104424002c040e08100b480d00b070a0a13480d0320141c00c650200d1540045c1881c40c440c00301174006480e4403402484a40d00039540340322b84200548510520403107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 418785035 1250 418783785 418783817
    0x5042c07030c2a0b06060f160602040f09051f03030504060309030c0f080702090109020c031603050706060902091509060732010501031103191103150c090306090607020d 74
    0x1400440e07200181030161402030b070083d00b51401d034180c504840341480c000205d1034900c0c1040070384114501203400c0034944410704900d00c1c405403038020704071101074080c400080d034459413250500050081c0c010101d07a070714000d80700d0300c0c00d0340b4102035010020f403440109002282c0d200059a05584840c04d000640800909054503040788280c0700038159914060142d00300000103001c0d04c1c8051007501c2000a50740c0311020101a0702440d80615600d5205000a010f8080c06c84036140c1918028184540740c150587c4551090301c3c81c83c2c1080c0800d5070000780700001810b00c86441c00f5402c4c041190300d414180600c002500701d102d031603405001020011503d8402c0303042541008a500852041d0184e09055164994040d010901c8107130f40c540c604070700d4a0110306001c14164805c000e000690811034001d43e480091059090601d2600b6102da00c44000112801c070884078004c04201588584072a0030904061a1050003400d48000350081001e000300141c0004500308010501c0c1800300448182c002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 418786285 1250 418785035 418785047
    0x32301180e01020705030901021e0a0f0c0914060307230409061407020c03151510030605040c030b03010f090201080c07020103020f070602030603070b09060a0809030c0d05042c07030c 80
    0xa40000ca41d40f0001e8920b00300040080100fa0b403040c280c00360703650f02208294250751822841c4040c1003d8000c0241e00d00040c0000d50380c003045601c1814581c81281d1989118011215070300b040038500700009040c0150381c60708008041c000d2951034804540700c1d44202d402d803220b11070040075074040d5890f80001001c00040b80c0041210300a000c490180703529000d80c0c000d50b500b4101041e1030282c021205805c4600101c2d85000b489101e03c05136203901181d0f0b03002800651404070300d10800b0959184404200c03030765030317015103040880a95008501080c01c602050300f1241b01d0480034100c9441c0480c2c0c08010303604804442d41c0607110300e80c2143c80340035600040c1c010b44107010000e6460100001d00c5410406280d0285028000a400710b03522a922141c81906603c104e42042d94048401d10001e40540d20034040141d000c4020000c0c0ca04000704402000e00c1e0922440900e00410f4002c030b018814a012001018050308050304400030f5081d0300920050310fa203003e4820810192a40948520316000315 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 418787535 1250 418786285 418786301
    0x5040501020f071506091a060c010b04052706060d20090109051807140f0d0210030519061208180a15030c0302090a120f0c0902040603230118 62
    0xc00e070783d0b41d07441d01d4501000c5000700c80c0f2030741e20b40b90300c3c188011890108a03c141e40342c0b22020280344520544201c1042101d4005482e07000b1a5903c0703412003001a140e5000b00c0c0e0080b41d2418802c24200800070040c00b03886640c1c0f007080ca095000780200441d56882c110040d000715042901048101d424001c00c6958541840010b501300c50140000075854407668401c6200b001c1002100380320041480309261101c1c1c8510425000280440001e920b5140100d441c1c5803005005009240c0b541840d80860545040345448401003561032007004801062014080406101f80008100e524100740d01d440200c000d61001134001107020481c161151801c86076409502402041421090780d229441d1510605070104400000c0c1002110500180039000352029018024400d44d0807500b41812920b500440f55010340354090f0055545012070340301c886200250444110250741d0300e0a109000c0c09484c0114101010f00540c20070203c250035114042c40d064600300c150100388580c40303c65a6010744405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 418788785 1250 418787535 418787557
    0x4121b0c08030301061407030e0f0a0806090d0e01020f0d05070305091c15020f190509060d0203070215010e1f09060902120c0408030406080403030212070f090510050d0504050102 78
    0x1020010640301e400001030b5040740e1941d6035a0060100c0008540e04d14001c00500501141507602601a280382110080240d00400f900c0c0d1030040350784000c410310340641540d1000c09504801c5018103502da110f45440c40d42c502c280010850a2140b4201554940845000d0010010045841e40c1014030503c100e510a483c01809004086085400c001c202001c213041140d034406020401e01d5000801c1c001c2d2400540803554060130306021981d0004a0108854001c042020401c601102c6903640400f902d5408002100180c4234a400c0300081d107080c42d02c0d25108104c0320704800410003440c0441000b81d00156101581e035a1210402102c0d80c855925000464068186100401c000c2ca1541c003609003420200c001600d280c4030760b503250001e03200b140a41001031300208400e001d07c0b4000d2400700d4000744686030040c503080d13010a0160030a44143d4499000681000841004590000e040c1000c1d00302150001550404228044e2140c03043c900b20010039134841d40003034144103003136040e0341100b190 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 418790035 1250 418788785 418788803
    0x20d0b0405100c0f0c03050c010e070609030c08012007061d010e060105040204030c050928050105030105150913170c030306090c09090c071b0b0406020c060304121b 72
    0x103032a080ea00c54003034402e20b940803494002e204480350f20440342183e211186441d08a042401c6440480e903c2d440418049615901c4440c0b02c40f0803d020403400009194682e61500100d06514000c0000c041c01e034420007060b818402484104040c2c640c80880c0d011002244d07640c1c4007094030700b50018080d01c51010070b48514081586040c28019000000260024010b55116a8031402040304900560201030308007a4020003d029a017804140703150080d20b10000d001d41c0004a08803248092118103070946681c9e01c0303000400c8181000d00440fa040081800060058860b4a010508401c0001c2c02c13400c011001001d10402e200700f07010500c600300e88003c43d42d5500c90b62050750300d1340e990007a0354050140b43ca100000d00100018003e4420aa100500200c01604c81c00585051500422070603200d40d00d040c21046646401c10f03c261340245400c8502c00d403920b02e0f1010190600e54801301c1a4082e400410070000003454049842e400e061081c20444201c070741d42d54032624603042ca44001030003542 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 418791285 1250 418790035 418790041
    0xf020f0c090c07141e010b03060405030d05040503041a1801030c0c02090c0d0f09020a0b070309063b1306030b180f2b0f050a031d1203011703040501020d030207020d0b 73
    0xc0003152034044092003030700078040c040147c4140369507140c045402425503001407105110b1001d09400040d041070048044a04042c0c4985045142a025a0007a40561000161b0070036101c0d02445100050401f42000c00c00e40c00e8002001d4107070340c20160700074410344429000034040315100c01926141000343d03030100b0104c10900c034103a0040a16420991142e40b402d04c0001d10240010100d8605070b51559556400c14604442914003200d0200e411304030f281004d040f411501424a0344103082c05824200014040219082c403a9803407542210b20100c07410410140007140d000e504140d004004020107810340702c64034810718284060030340c01030802c1c014414480c1c050544031110407142e0816441503e1801c91021081c0d030111400500c4201113a0144440310700c00380694080040044d82c00d07050b010f03820710b400080d400c1508441c2c0303500c1603580110051042c20f02d24034024a40e60402c6c2e005500e0b0a0070030700040d5448001c9804a000c1617000a02d00085483e0025004e0007917501c10b29055142c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 418792535 1250 418791285 418791313
    0x6020d14180111160f1410141611010204120b01060e031f09020a09050c0d0f06050f09041104050703090b0702062509030c060f020f0c090c0714 63
    0x40015120000c070011001880d0388200010301c12105110302c000c07802031074079203150a90008070881e540103485182c82018004086902190040924905040541040f461207120901294049070307083d20b10f407202c0810040d031200b442ca07202d5400c0c043c40c00d01500340d4001c0b500450282c0300360380007030100040c2d4004d1202008100110941a1030480d11165160b11966040c5640e4000507602c2c0f94000c59085000c1c5450012980170600784e03030002d0115010b56444800d10015507000361034600d103454000070071800116140c800d0b49030001d04420b007031180919160000703400300f0301000361030310803c80000818100300300d44030700c0800d0000190041c403291a2821003e8000c0010010a0f280700d201400090781440c40840c05c20b1045c4113a80104403040c06d0141c3c49506030070380030480c1c070500c0070014020012524190100c3c00800855407482e0700602c41100090500d035042040034039030340c1b01c07410b4501142e9400218541c1303d40900100d6484050909104030100c021001c2e0016500070744254403244 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 418793785 1250 418792535 418792571
    0x40605310e0705070209040b0606070f0b07030c0507020310020c0a0510020703091d010608130503030906150a03050c0103200a02060105010318050703021e031b09011403030304020d06020d 82
    0x3a151a10901e84a035100307601500d05100c1d0000095100000200082c00604503101540c0c00a00c003030501d03030402c0200e13965440c0c0d42c0c0c100003060355a01041c004000d80a9814050303410741d016030b441c0c20350505c0a2940846d07903c000682c91000250b401151108074120104074208680350004200d503494900d01500f540254000e4405500140c22910086840031812407030b0010211400042a200da01c3c05004441e60134001d8540c000c0b448004000c18049501040135500444243c4094029424540d141405c80b60b2100301c0180210b0b140002000401c2c0040f030040400d0100782000b14000e00b23041080446039084441c011038a09011550345809640021254103843c001e072402c01690022000c4545d0303c2c40d00c440300a040782d1201e60203100505003071440341d10001d1103070035261a008502c4000390504120783c18040c00149003961182e11450803214960040c8a080c0042c80a500c10b80003183e120700c801400070f400380080300004010810a9030460324070404a00c010041540b094a010410b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 418795035 1250 418793785 418793789
    0x17120a1e05120a0c1d010201111c0b0301050405100b030c06030103060e0c030f0309040f06120f0506161d0d0c060905030f0111070b100305120901080f01060504060531 73
    0x2048022000a10502d80b2442844c841100586402c9007002186500c80034008600c0700f41411075403a040b000030b82e800500f010703114000c0140b150840c652980043d1404481c60601c446111303a05000501c00400c1c0c4c0130440880459851001181c030400400100e40351852910030281c020788004000018842503503c07450b405200e8009031126008400c0406954038a41a1440440c1e0000c000c8400c4603d8039500c100d42c4140f5400000c03a069035035510810400709450425200b81820008543c20048107102c00da5000d10b401c038010141c0d07030101c0001080b161000c004001c810507a1000c1c80219a10700f40e4442ca03d580c0301d080096040c2d143d074401402c02c803040c414680a0702c169008821048818002c036000328012003002030070f19405441d08100c6c14000f6101c601e5000d12001c01101040f428889460081e000c110712035640c05182000600007170f001404480d00c010102c0040c00569070100c2120211406403400544030b41d20014400300c22490f202078109103c84a84224111003070492124003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 418796285 1250 418795035 418795057
    0x703021302030f13080d0c1206030602070c060314010527040c051c0b06010c14010906020301060e0306040c090218030601080d03050912090118031203050103020a17120a1e05 76
    0xc036155010841284640584000c1200205001c41b01c0104141d600001c081d410754940070a0035503c44a07000125003184d00151541034001509800740040007807644010012464100100981c0c0f1300c0e8103c8008041c0140e40c4a900300030200000c6581d1511240340c0700c03004401e07041d0641068902440024024458a4003c4480801101d14100451041c81c0040d070040303490740b61665440700469101842000444440b100f0721004401c10b0310901c103040c02c0a101f1640140d407541005805020a003074180c0030303807081d8003038020000080c100c0220102282c40c1640003503201c1e100c1c4107020707044a1a2410803030b003602c100300000a040400003854417911125450400039a1244568591140034008070040d00060402015116511a0021440141000c14403840c0c031034486d640c000c02c502e609504503001a48850042c000d500d05600c201c1c1c024a10103803808403c0981107502d1b51110b2005200b6110080c000c00e0030100a802580c80a03040004070140d015920800003001c3c10a40114842032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 418797535 1250 418796285 418796311
    0x170901261602190209092b080a0605010215040816060902120d09060e0303040e0f060310150b0f09030a0b1603050705030a051801051006031a010917070302130203 71
    0x1407400e500102d00703408451040180401285030700d80a014690002400d200e070184104000101c1e0b13803100406c041e000d202c0d03900d2003036482c121014004000f40c0700070307005403c803905d0002e040080b070703070000780d40d0b105030424070303500c22559980d03007400d140303a02900001d01c1c4500001d100c0001003003225840700b0340680c801c4881c0250700700012100b40e40e84841044003008189101000d106840c01006040c0c1816401000c89203055110340040b0003c010683c0c10065640d103460600200d454184402d407803410190070100039000c280d4040c001000038911620b21658400260b03420f8070720080040301c0301c410000e01100d8500c40e0a04c1c00e403021103c110f54241a10180d545d408503030718828080c49000d89000d646070350841d12015680d200030100908103003d4603440e0107054110500030302600d0f1180600e50500f800e42c0740b03480406801d45143c10500a076110040c0004000e03aa0443da9500643d46a030b46440c5400d4030041c082c0d86861000d400181d4403518604c01c000404006030025845152501000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 418798785 1250 418797535 418797571
    0x80603011e0e100603050c011d0a03060b010f0f08070c0303060308070317150102070e0c070c0e160513060c1518021e03062d0108070305060f0417090126 67
    0xc00e040300c41170b0000520f25004003004401c41d6214403a9003555080b49049148581c40c0d640009611030350076442128a96190280e1103c19a04904502045030303441c1042100744400c0c1c040100200070082405051200b17082c03060041c18841e9004101541e07001070081d07a940050b00340034185502560078403242c40c1515001a210420805106410f418180c005001d0741e82000500d0802890084c51422102018441640420403200c502c034000c0880400380c083e9410103140007600084000f007400c080c044104043e40da102c202004d0a0111043c520300600c5d02001c03440d110b41880c00d0f9003402c0c1d03c41400d04690543d2000d189401d141850702c21034000c2e021288002c2d041c03181090b1600301c90780c035800c410001903002c3c4100f4800c00b00d1412000c88851f01d240c8030210044540b40a0b0408141caa00c5034006004000c0c040140a030400909040d1000528282e982c0c80c150f04089a2140200f07130002c00d0b80000d0b0b90150762042000518445102d0700103200c1da020f049400022140e6500c200c1d155404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 418800035 1250 418798785 418798813
    0x5040608010b0304060f0c0e010305071b1719030501140103090b0703150b0a0c0204050f010b032e091a0913061109150409150b0406080603011e0e 64
    0x111011658a91a010001da1a01e9141801600001e1094843d00d40f91a6a00002c82c190320410200001ea0340318200d500d8400300c001012900010451002d0090300c0d000c2c0303c85640c2503184201c00c103501124205e50755084414449142c05005d0942402a250780344040300141c00d60402410382d180111036910015000d030044081d5000c90b24041e0000c00d42001181400f84030f500b2404441210030681445190740d1a80b15601e81c3c4101220800070f110010314000b10720b40f41c0240d90f0005a0056015100d50500f0385896981c84083c00120380004000c1c0300455000700f50042506a902e00780c60150803d50710483c840c0944082103a00e4504031408030f14080c18645490150701410113401d8001c0022120341d5200c0041042c4c0c54104800c0e039050114002903a034484800c0311200c0c000012980b968030303003146641600c2402c10300d504201884401440f01c01503442c00c0d1011103c00d440d244c8800d884400c00329004111110f00030600e034a124501c0b00072440c854112895441c4280c0484120b810300d040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 418801285 1250 418800035 418800037
    0x15061c14191109071202280507020f0405102706060c060f0507050405010e0f04020a0519021207060c1107080303010f050a0b1204081204061413020904060510030b1503070605 76
    0x1341c11004658010500440c10700141e010300009071485c400d01424080b2800303204c2a03a010203c101001500004010046080c40085c12206040035a0103000c85c0c24003203402c1001072030a006845082c030300d5803454030744400400d910300108000722004001203502da142c020044d00440b602521101e090203a801d0101000f880b9080c418a000d607122420241803000440d6009814901181c0c0084004c050f80f003240c2c1e5601c024402050f082c2c0755180e03148030440454001c60805041c54095410501c492012440c800c01160303d40d80c0c1c440c90008408561034000d5513001c080703104542d190310034008041040440040114181c44125032807a621719507440400c4106c4169006032100c07007030280700c01c484032180030f040280c01078400d01c841d908080d07107043c01c04c0c0c0c254011101a140242c990120b5101c941b180c1070380540203c9941c02c0d10f100d120107500030403848d2a010700014045961480020035410090381c00501556100030391410034141402d95558007681101214803d0082000029480380078030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 418802535 1250 418801285 418801291
    0x70503070c020112110d020d0e06040c03060f1416030e0106080307060c0e10020d030506010f1d1c08030603010b062a030f040603020a0215061c14191109 67
    0x55500100985542d0044031046080c10007400300f145c80703250007800c2540b084083c04000c49003000c0142c503050045840403c0c1c5003030f0300781040315070070100500010804194020040e0798000a0200340b06154000042c0200f1070701141d11103203402c8d2001c0c0002950707001042e45c40e90500d554140103641001a80600700c410611691030759500c10040c660000300203400022141c1210708010ba200e20345034000c20083c050180801c00160098030610194580500c50150888400e1038050416549000088e140f00100b0174070790741140301c02400303150a0780d90040d072441182409441c5400b09d0107501d0401800e400c00d5840911075401d20b45e803915a8100102902c20a400443d402000c0c4007041e840d520150500b2025500103010030449019418041c6004000800c001d5500699405806900905001e2411100c400c4010b951050000681d6420466034010800400c2e400b503c000d82d151500b504035041d0001411030140140e40d00c42d84008015161019008283c81d03545803e12208000e00c800c022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 418803785 1250 418802535 418802537
    0xc150c030601050a0c020414070807170f040201050c0a0210030906050f06060306131401260a05120c07050a030b06010207082409030d0510050a09090206071b0308040608010e07050307 80
    0x40c0104840f261085d016068054006880054010614492000680b6045614034045081542413080c001c3d40040c075410348072a03100c542885418039400070060004007820280c100030300072030540714904040c03085000642d8010500460503030b0180c0040c02030200d01030159580c520b060f00044140c1410ac3c103242c0b00d450010030b03039441c581ea1203040042d44030011024400999031100071200e00000d000c9400e0103401d5140f03404c0001d07250b0410302100d11301c0314801c5900541014426000141000540d41d117607200a4000c01d441d07000c40d4404525221490b40030503802180f0f20300000c24085014010f600400b400c0e42507030101034580389803581c1c42c00140042e98111000071755103480c811900c00480d800c48148016685404e8178541e0310320030b803041510540141c9980c00c03800c000c945007040d40c0c64000c00c4c07003a0080c00403c0590300080d240c0e008420000c0c14804005c4840034801c40020015405190300085e0305031211345640c070050401500340602551019040301140c0540d001e507090700d1058001d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 418805035 1250 418803785 418803787
    0x111908101a0f150c070303020c090115090b0f1c020a0f0206040f02040b060408161e030503041e030c060512010f0b0910030e030a03150905090d050702030c04020c150c03060105 77
    0x3111090000c0c0e41c54160450091035010700514004e08001d104600042d03009500400c104000c2c2c404111403028181d224113940c1c51009403d041c030581100d410021100140c6000d6155282c0e803000303c40703a11900012050004076a40e11005102455010b070035400d116a076210713101002e42a080e6031b030301403d45024105041281c8044010300d01900190000f038800381589046c107940341c001d603140100c40f081040303110080b884184045200000380020340c00f100040c50500d00d24646429480344100c1c01a01606100c00c100700f11145441a22000110b03445011417030100d80d2440b0007400c0c1d41003003860140110410000017012181c108010302540d0742c48613510b140100020402c44454050420356040c961144080394100740180041d022021440e24081042c5400c110000400b00558100c0341c11a8609000d1003c1d001c0300090840313010303c850030304659410036400001d1604141d0702d441640240001038609042601007008050400d000e00228041d85814500500314002241c641d400035070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 418806285 1250 418805035 418805059
    0x10140109090903020307061404050111041d0a0615020706080601050f04060f0c06020415020601050418230a0c06030e0a0308060609060403021c1505090a111908101a 72
    0x110366001e602c003a48280100c03481c0601c250350392400c3c0e03a400301d0402e04a42c044410442401028000c6028075040714188070300e05070501c018220f090342c9600d50000ca0540c07240001d40034180552194001e01090413845000c071100c240025602c00c5203004a000140744e03c008a48554040d406455201303020242090600d400d11204540d402d81c0d200c0108200548000c0c4200460f509200030400761409036540000349044a001034038280040c2d1080b40034900d0a1841103030441543c1c0000d509640c00414001d8500c10000c100d41c2d2030300240300c2100c0d24054a000070040103140c2420b4402c0b03c045071010301c0098216500182c82d00110000030313003c24803101c0000da840c40c0100040280180051042c1c0c20f090f101c1d004a40205c52488031008455620f01c00c0c241400118520840c216a07244030a001e01d140c000c401c261140d81081c0014510306401d41c3c4018107035510107941e544044540b0b4620400d0790365500031541d550880c502c4450701464800102e00b142420b4a4203118420f002d060000d03107034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 418807535 1250 418806285 418806299
    0x20109150b030f06040506071b112704080d1103060d06090c030b0903030f01060c020d0b06010201090c120506130c290a0918091109100312091a040303021b01110f0610140109 76
    0x405203e2013940d4030400c03401e07241516800e02c3c50bc43c001c3e805501a107031619550108441110050010741c1d220107000e20411150742c0d00c1c1c1050f000c499038050000f140c00c256529150001441c00d400080000364020108a00c18000001031803142481103050050759a84075000c0d504403001c028007039001001c0081d0003002c25240c4030190741003281840006103001e00b030703158071070555850b0700300b00801c506440041d418090100b110541001c140300580280042c0d9613030f81d40f1024210f118944581c45450703030104d8800a5844100b243c3c0d5551181e180e80c130102d1040080c204a82317030044404c0101210020a00001c061040915281d4860f500c003151182441c03c01205110003403401000e84258000032001620400040800004a4660b204241c2c01d00c80c1140b44558072400580390700405001c200017180e40005e01188502c03c00420715000c040c0c15004862510900e42405024401c3c0007a00c4680c85000684e1031203a0b5261700622440713500c071000c02c00d1201d0101c43d21400125080300a202c84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 418808785 1250 418807535 418807549
    0xd03031b0806300a0305040f0e0112110609040f0207030311190e030c120319030c08010e0601090f0b0a1419141309020903010c020109150b030f06040506071b11 70
    0x1203c0c2000c002e60208010300800c0b450300d1113190088001540c085820022002c0012405c00600b4066410814560408030310042c6c032292203001900b4003005240b07910071a20b444c421542c1a0750054006d0100740c0880b0044001b030340c8485821000240b82c548162904c0d44600c0c159040c840400602d90380703d0791007010031545003401c49000c56060044045074402680c514400c0c948541d602c002031502c80f82990001d0041440c4c0ca444d00d02414102400c0c1d100c1180e1111145065034100c070b15010319600d8100040312180f0b11034000c10b00c03810846001107115104807018054206103550b51480081c107211030700100b402070005400591030500c1907200828000e9441c541643c9403200381d68102510044c0c103804075400c50384071154a40d4001398030881410f080c01a000d42111030f000901980225582e0b4024416102900d58105039450a20094941c0c1c10b11480c800701c41d0b0318003112105d042a00b4029200c180507210007000c140d004074024100f0200ca40b1418801b41c106c0074104941400c0b200340115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 418810035 1250 418808785 418808839
    0x7021f120c020c040e1507090303020604030f0201020d0c111902030a02090c0f130e0c03090c0609030304080102030118151a0a052812020f04050402090307050d03031b0806 75
    0x20742c0501c0400c0e03d01a152071084044420707885e001000d1055030040314000c02003000d4000010042d5089043c03000c286c00003a003a0300507905162040a41400110480c024000c100d208456581041e6210003003560000c204100d44440030309540d40542c4c892640710070300848403030003505a0031007861701c0d005d4580303680040d50200301c144806150154519800005500c544e4461002a0b80190103200b82d452100400340d2086a00300da0610318242603030345640d10307103c0f030947c0d61040314005003400b1252001d02c16200242440e000954032940c5035801c1160745000d41c0d03170401c1130f0f170716044c01078540c4d1041798244000c0b42c42d410b01c5140c06401004000c5410341c40300d810f40050140401c441c958001400b505d03148622070003503030400c40c042508001040440301c0d01b03441d02910b00600c007680e0041d4030b0801720380848808803401030b641e03843d100103c0d05203246640481d90001403a820501410b8041d040904191203011560041c04200784054503010000c0d0742e00c42d004000d22804081c5189000f84200d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 418811285 1250 418810035 418810037
    0x7090f180603080408010207051b0f090613020f0c010c1e05030606071406190b030c010819050106020d031b090905061201060b0d06050a080616030608011107021f120c 73
    0x9015034480d103c01010350301c01d60041c0d101d80c1d0300003500024440288041000440c00c070038036603c1c01c040100027860315040410698810002c031000710f005070350303501900500d800c0da19805640342d00400faa00301886e0880d0b200c00140d0750070954450585442076404002c1d80280d4041c06020032030b1680b0407101c5070001003000360031200800001000c2020044040000346c2030500900084c075005240d00701c3c8014900d0420072140c1081039101c2942e40101d04e409000c03000b03190000d1640d0302c0010204e000442880301c0c0d000307130346008000301f52380f5070100d500010101c036030703d046c00802c0c1051349401c00d13500004054000034040040600060ba25600502d8101030000c165200b04a103400103a400c58880364000040e440380020700e08020380c0640200b000a0400f100c2d0001c003680b0b0090150f4403050001c0a42d204a030028100d1b45c82c13070780283d01c0203000e004448020082004d204004000c1680000801d034443c01000d640f00c81c181d641888008400d402c20381e1000081c0700741803a901c01030500c0c2c0c01014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 418812535 1250 418811285 418811291
    0xc090904030f09031502030610031a0d02060d0e060718030b010b0a02030c0f0105010f0f030f03030b0d0507060203130b0313060b121203040b0603120306010503040c05060a0903050607090f18 83
    0x1251840d072240007800030800005030369048c042e0400c001036443c0c0c0d06403814903090944000c42c1440b1182c00c1c1c07202542c103031604100b001082c800160b0394403843ea8000c41c80781c0740c01d0f560035500d00005001c5101e01000d80b1340520840445444a60307d141c10b11005010800010040c4058043c201c0035001901d5140100d07801e1003040102642002c509441040083e95145c0040080c00356404e6050006e10400c0342002c0640d05584811110f1407000700080c007410344400303d00009450340f101501d80b581d088800e07104525150792000352260b201c1201090a450500c1c0d0201d460940780080301e0281d1a090001c408103d159500c64010b028010ba0301e540c0700415000300c040d083c00c280103042e411420401200d66034605860181100403025058a011340c0c0f10703010000546294400f1a03800003424240103850790b403185002c9201e5035003074011680140001c06c841e81c01d80c0d049881042076a1003001501d102d03075580c80b01100c501607036200b1080c0600310f140c03080000314509001405001c041d0710f004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 418813785 1250 418812535 418812539
    0x506180903090d08040803070b070305070302121303050408030d0b0906010306051c260c0d03090c060e0303280908010b0310021305040501120303060b030f041118090a0b0c090904030f09 81
    0x80e801c41c4c20045081d68200b0036001088a0f259140c860335a004070b8500741103050018244000341c82d004c004140052031548000305900741801101071320006d001190850303a407214980e4542014085c0315030441e0041c010310f000300d0465802030241506640c00030b008803020300111240c0c4469103407100015500d9500190480c0c502c507411183c0c5021000d11074103815900e00002a0f881c1c0350800b00400b03a4101458441280000b510000d00c9408455482c505082c5845040f40041c0c11403203130320079140c0e10b0781d081c00c0da00086050051101e0b840e0001c94841c4840107660325081401e8078010b082456141d004603900c504118002d50140c1907a1900e400318020386a2a807002c94200c44081e0022811402d00180400c10036601d8010403000e002e02d85606400c40c24a40c0d4481014440644001d015402c8402c0072105626010051032074100c0806250085003000c242c6242c60760b42c500d405951128072100002c00d041c01c0b000443c1c000000240c01c00036641e03226101203882c541d01d50f0100f02000150b02d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 418815035 1250 418813785 418813799
    0xb040602071b060c1421030c04080105070c0b0610090521011802090a0204080309010e030a05010504060e15150904020102150403050a030e0f100b0a17010506180903090d0804 76
    0xc00000e03081e0340d00da030744c80c0520038285400a2003601143c140d50b5442000c00c1c8446411400024002140c88011151aa1520581ca80260140c2d401c420380640c40d0000300540503610a4041c52400e000701406921519000240b02440410b0319405001c00c40241d002c02141c1440107030b4011003a60a0300c080084041907110300d0035204140304480340404095803460039458400d505c25000307203a01d042107103454036281c0342c0c0b81c49004119102c0e062107241081907925403024019000312035031020080003036160514200000301a00e40c040c4c01d2601c159080343e0b039002c07600700001c0d00810440c14a690780d00102c804205001c4002881203045000c1c0001303202c01c030703c0108180c60103135100303840c1c864451403070060080c2240d903401d240d141e9550050100442100c00414001c0e6841d604400110f41c9000141c0464235902d10b503807000c003c010440d40c55600c09441980b100303028801c2180e444801c55041c210000c18000265040c64003a04208030306c05891030503034440705c1c2c800d101d18500c600f05651911 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 418816285 1250 418815035 418815083
    0x1030b010e09010e0601090503190203010e031207050f04081606110c010207030f0c0e0910140f070807020c0a090b092d0901110703080a2d0209030304170706021005040b04060207 78
    0xc201d4614012b410000c104516083c0240440800c1c0d040c011803d001c00c85800c444208405440071040c8100000c80442c0e420651040381d0280956074121105202d00e0314813541c1c2c04060380300725800900400320101c040c5802045840002d10142e004000c124295114a00d85101c2108115145034004400141c0c48500d001070714032640307048000c0d210b64400c0b44004001c0c0c942001005440342800c03010045405824014641c1001441c40d0041955a412030b01ba0310b0312500e43c01d11036005c80990000504805660400040150207a461890648074850717605101c40755014414042240c44a0004541681008480c2d000b070f00100041290180c802d0302c0318540c1c1c0309420aa0000d081c0c1010400c06010601603000e404554a03c44540c003030000200b00f20b0301c0304140c01c02c100c0680004001945903001c0041d00c001e00340500c04480043c0500489544c6c038016885440c015014603680086400c11910500e8407668016a01000070394031552440002d500a21302101c901c1c0c620300c55440054002d403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 418817535 1250 418816285 418816303
    0x80304260109031d09270106030519031e020a031d0607080702040b0a06050d090516080604030f0e01050a1407061e140c070f14030d0b01030b010e09010e0601090503 72
    0x9111089501c07404002c03404030b00051600c090281140305c0034084c6902c13101089100011101d00f041c00031032440360015015001e181c0c40504503216003000042030301080f01031702d15240c1c40303a1a107204442c402034115801e166445044c20168004425000c0400c1c025002603801c07a6411034920b00203188400010010341000200351030b84100444c0d1501141028031801060b1030048bc0c40620251a044004220384206500342e242142c46603402d800b0040204824040c001080c04002055500d90300d289940d0074040350240c000038114601d1002d0b4900548802c4080030301a91034905c1d11804840030743e004105101c4c0c0081000f010850000891a83e20602111000440351200005020140380301900c6c0c5440d00c0301c000340c51410501102e2040c02d401c850002d60300c07603401002400b541c20418000286652030000c82d00000414607600000c0d50701045900c1001d803801c0240925000044450041ca0110745822800c80b0005002040000d22165030180c41450304001e102d0300c503c04242410585 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 418818785 1250 418817535 418817537
    0x2120f0d0905181614040320030c01170604150e04050715020d080f060105160f17040e150f03030c0f0d080c040e06030111030906040b09060108030426010903 69
    0x18981c140002d181100083d24803d4818480e400d00341064610200300d01c8050014006104140c542c003060b07004408207840c01150020103078a03400b180700100344200c0e1102031702e140c03290040d40c81d0f02c42550b0040c8492000c000701c0e4144020b9948e00c0c0c40621000780344110b0f240b0841440400e0004011400014851180384200042e182542c50100000302c0501c001c7c0c5082c06542140c0c0450b000282d0000c540d681c0150b445407011902e8031010010b950b54450540c1040407800b00100e0403050080d0003455031030300c0e071207040412028625014103089901450054110359040e10000c81da01c03224581c0280034100c401402c1c3c21409680000291865201181c6038015030001488801004400c2c0410f120000f0706003005003140c501100300035651311842c025004244030800100e60360342c90035400010800134011569540741400d1545580ea80d4003190b088801e082000001260030101142e880d040f91850002903040c2410700304694002400c2641c02c03102d40c0240406a07a1212090160182c86030007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 418820035 1250 418818785 418818797
    0x2040509011d0a020a1b0615030c1701090b06130b030616090f0303020a0b0705251e120309030c0b1e09070501051801030b0d080d0f051302120f0d 64
    0xc50340e141046030004244644a44c0705001c61444590817040d80b500070108000c8040c4ea03240346240810040c00c0036041b525030404000e401208000104069400340c03002c0a00391008401068205403c1e5104004020045e109600100e203850a10000b00b1110440010011656069050200c0d141c14802c946101c0540215a40d0342c0d40f0640110511005e88803812075040b01905580b4040c0d82c0c0e00c0d90175401441c40e004100025203082c894800c0e07848147c0180d8840c1400640019402c0080440900030b40e071803100c000f2030392840354082c5030395034007541d22880007a01c0c602d00400680003821007690903014000c030701e456100010213034481a4030488008001e41d81184941c900d034280800018008001644004414403540e0381010a690340c0d600801d43c0c000410070104012005000c49025454104281c901e00030200410000509904500c11200304605a920301c01038060742d809980c95813807503000f00200c20140c10a28036424410034801c040310302e0300c0410000030b4a40203402018000083e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 418821285 1250 418820035 418820069
    0x11b0f0305030411150d0b010e06040308071505040807152a110613060534030f140403030c0e1c060e100509070515090d02040605030a230303010b07030e03010204050901 74
    0x5030322544900c040700b0309c1c01d01d00d100c044501068040c800c1d13000160032400301083d0f110400141840024581c41050b105004900341441c0400e80d43d005448100c440c502200510360030a401841141c03400807550341c2113254003003140e170200c0da12003d07103407640c0130000020200140307107800b042818003d501341520020307610080e0602e41e088071070150004c1000900302e070800141083c08212510f12001d48030034140003100065040c1c00410394038a51030851424600c01e10b03150466249818400c0e40281c8092004124480040314400308056030568884030310a0180b81c0501c51034000d280d010300c600d8000400c9410b0442a91412101b00000700005440e0703c01c000c0311580a0242d90000c207c00d544a013030303111306586c1081140c0166060305000305010080d00c804e56075203402c114014040901592200c000341c0c10f101c0c07502c02c0815040d10303040e2100c1c417003612100400422281200d903400c801a00704140355808594404507004a190b03d590248402300d2103640d00440c0d28000e080c0f81e101c292800f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 418822535 1250 418821285 418821307
    0x3010509010212220b0a0903030b09100902130906080a031d09011401020a0b0c09190510140d05100e06090f281a011b0f030503041115 59
    0x604020320032100e076401406084404141041460b4200310564280700a04004083c60411100d0300c103030140020380759009120f0303001c0c8583e00c8007603180c1c040c0d41d060100b00003503403d00038109003e136080c0703000d827019620400c240c2d051a0702500c40501502200801581c1d034185110560390ba6801102c4c141d00000d42060801d0780000000910304400809071302d900c401c134400100072080520850404040d040d40e001d289030b02c248001641d880d071103a643e0200e400c0ca2001c4800300c0e00b11a440da07006031050941002c44501c8000e1000807210002c094140009403024101d03546400140c450402138814002c1d1001041140941403240c3e1030401c0e03480d1864a02000c054189402070181405042c03000240301c0d080e00b1003020039501c4005081503e91481d0881c107103000c0d4003100c190f8042d42c10b02d03054210040e4680040070719080301090b0382e103030789610780c3c6048800785006805000384030074405000000040c1c0918091a80240a80030380d0390800000030200752030714104000c0031a2090001046a0b0117 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 418823785 1250 418822535 418822541
    0x6080a050d09140603010909022103090a0602060c0a0315081f050a0203040c0b0f0705030423030d300c02010501090e07081902040e150928060c0509100e0301 69
    0x1c2910100c6941e0381c2420601042451106000313001040d529100d88d0802c1d51544c4c01400c03d8100c0140c40500b0303130600e0224a030744a811001c64180705e0941801c0004d030726440003a015019001c491030b81450401044001e40007852541c052040b0510610400613040d075043c41003510703811002c82404500c528010203101100c030010f01c110f24052040c01800042440c5031501825250407020b41030b50313050b0600141c0c4031402000c0700104a8800000e000c05d81040507011140c02c0681900344401010700c07003080641740c4005454240002d651130740520400e41c1180440c81160590100b03848e2055101050340095500e42d0b020440943e456100412040040b03100c0c2c00b810000381030103000c580342445030f180d8170b8000440d44c48050300c200d11581c009541d1254003040103c680481201c130350b894003803180350360001304941c03070602d038081c0c80b01846d400f00d0420103002212645524070b00c40c80c0a184c4d20f00000345160780300da0b01002014041e8103150340720400e02c103480550765251408400b40b400700305429 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 418825035 1250 418823785 418823789
    0x60e01060e091b0f061b0c01020325020d0609050c0123090d080405040e0718020a1704050115080102070c050312041211100305041b03080306011206080a050d09 70
    0xa510114070801c0041c640104110710040210115418807001c1203001401c0c0315841d2242c02d900c51030002e038003103040d0100300f000b10810300e500007510102250305005a80324099490407008000440c7ca2194a0400ca044030104181c4001c108002c80040c580f43d0741d0403160007500440b06540079000c140e001d0340c0c1003c0c0304159411003111030108044d15486065450103042e0283e401001c8010300f42e01000f1403a42520050440680100098040204c140c0d0307480196100b1b6080e151192100000d55070f40c240210341c080321a50303c64903d4480c041801c081c003008000c000351415503039520303141c0b010788285000c000181071150004d40c4031041801d1802104c3d20650000e0b11035070281c403041c030b80800b614094074112101c3c101038414403422410b048455810b41c2481c0e030360102d1494401c400705a01584420b00170ba000c2c101c4000c201c4188007070400b035801580001b400001050000a640f58440c1180d6002003c4820b0049185507403841c62a14040600b0b030112407c1d00544181503200368800d0300000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 418826285 1250 418825035 418825049
    0x50708090601060f051b0102070b0106090b0c030f03060d0b07091a0c190f1b030606141503062d1017060f04090b0703141501020616170103060e0106 65
    0x650b514018010301130f003050100706001d1000100340c1064020f041d0a00341418402c00d00250365641d81841c121b0003041c001d010b40008201086800b142c0000341100b074072035200d2043c0055141032001da640c50b0054200500c1c060b0300445a842640c005400790040f64003429503500d40e2618942440c40c030305104c1803004800d600d603034014007100400c44800a48070310302100021607a0705189550806c0441461240d00c081c0c407200080420f042020000242a0100c0c2d01071142084899202e01c1c400903c6582050440e51042e900c1003000070485400e402590010780003452188005580c510340700d1159018100c0034640444070346803420b11700340031142651200c0c031460440c803000f59161108060180c0904000d019110480008070540c4079076000020f8281c00c016400c0d0203151500000303011300300c903030150109911018003049914880c0401c1c01c45034201600a0b02055403002110f0341c042c03548590140c200b0405040240746801041007041c003840c0615404101185c41c190381e10700707480040d80100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 418827535 1250 418826285 418826293
    0x16050103020f190215040819050c060f101e0e07030b01081519090902040c0f090e060619170906060109090c0908010f0b01020c0901030c0e0703091505070809 69
    0x30781500b02000803070f1a50203a40881c8a04000050700c22032070006000285050540701c80309000902103890090b1048030010407a12000c140d0b101e1003140c481c010405e00d51400da00c00804640103005019559910407021985008082c2d5120000c4040c4e01514111140d560300a6509010a42d81808070340e074404000d04007845480355940000740910802088008031110804024509a480c2956041940788280d07025a544c2d40340c080c0500100302c00b1200703c0c0308074034060120240754003910300940041c0c010348540749403034509044100400d00040006601c150300300480c3e0305590480e24001c0c405441c90707076200c2c01c09203403820252030048050b150301c80350b5008100304143c982c3e000030a0810380d010140c000c0b0750703113030340250541c1ca01c000350b00b20162550a02d0354203240d101c0181e1215503640302c01d034211628908070905000d00c061003808082c0034034615503424000b40c00b4055007541c124440e881c000078011003a498908009141c2071181d0030070380c0c903581070245880d400b00b450b80d00030481034094 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 418828785 1250 418827535 418827547
    0xb03040803160e0607111009030b13021c0506100b0702090115050c151605040b1917100510110606120109080309010606080c04060504181d1605010302 66
    0x44011404000c2110003116082164a520a882624201d900700805400c0d0368482d170306454240140c42c441c0808038001c04e1a00303240d615461003030090104480d048004000ca036200c001d02400c05540c40074090b41c00020141c02030625080014640d542c0e280108060440f6003480c001107240f00c65994400c0380e40100500800b800360756500449411650b491950410010411009490900403680c0044c240c0c050b480a0f03200002c02031090030300c500181020201550318495064407640039500420a00355800d200c5c049030310940701c5001b0086c40700b0341081031080700328807940c0e52041c104503020050401c1d031240c200060f01f425070700303810406130a04140d8142c0a450701c10b0381d41e90400503e042d2248580c51580a0032907000c0d07204030340c4e180d0024110365680c50035070401d0340a041b0600c40c03940040d01007000100c4088941041e01c0664180d0b80e50710f45000d2602c0000079400b043c3e00c98a091066442074090008603100200c001c4110031075000c0d081d0b107c0d2041480841d1212588003034180342c010400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 418830035 1250 418828785 418828793
    0x14010b0612070305070c0203011509051f0314010e0d0c1104021c09110307091a0307030210111203070e0a05101202131e0e060f010c06021e160c0b0304 66
    0x20307842090362800040c41d58403404200c5071b910040030041c0d019480c1c226004443c0148800640607a03024402c03d02094440360342c01d09901c450603601981c0707100c203098107000082011b11005401c041500c00400c120509603d443c1c07e1800c0a680403001c0740b040c2c17600408206030400c848650b0340d811030f0f003107091450b20302401d20b03040898040c0208040d514001c04c1c04210030690403490404001d02110358454440000c0402080e42c5880c3d40320038030303a400b65044186000141131040c0c039800f800024003441c1040081d104a10f00e841281850f01807030b005402c06d00c822078050340c4942c0641d034440c1c911142074403d010075618181c11242c080d68955580306003c0707810100c0310b1803501900d0001603030349107071040001030341c0e4168203c0300c0c9400d030901030301c0d420f501320000c49400c0d03500218255100d0307181c0404101911001d485c00c140031498266503940403864660107007a181011a0f1505a901020550803030254030941004603040701ca425602c080c4184034000f400600408603031a440d601700354a03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 418831285 1250 418830035 418830067
    0x80d1106010e06190902040803070606050a050d170403060c080f1b030610030f06090905070e06130f0902090a0507030c020303041502090a0f03060606110c0d12020f030714010b06 78
    0xa1034001e11032a25240403454039814134400404000004540f100d8680c0c031005c0c2c480d409070b2001d80e50f0034203100010415180400c00303201100c4006002c88030300c00c12030352a6408808041c0d5100d010250604c000000b00d0034a0046008858069440d0005841c00341d046a60829000d040d64034024030001006404824100c112174111404a400e2400042e000508801911069030008540303403e000700061055011740100882d11310520596540d5512030084000100e4222a6540d01c400300180110320000c06034002d80301d003000f80d080800d030300b00c240d00032a81a246c16980d200d000c075a50020082030941c144140300c07020302584042d40c69402e20383c8400076112036040b07007842c026a00091111540d90b0f00403103c0000c2c00500f40100c0c1080d82c0c5d080600060003148141008900184581e0b500c8500100d0841c3c5640401032005400021075117503180c102d294803c036041503104e900607009504401300007801710148a40750f514094000440c8803425a40281c1c44640036000034050f07603090842070740d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 418832535 1250 418831285 418831291
    0x120902010801030221070e0103020a050105070312050406020403020d0317011401170a2702130207020105071b0504020c0715020c01090611010b04090b04020901050603090309090406021201080d1106010e 88
    0x540c1e01e242e80d19a2000c17200300c035807002170051030b138460408000755131401501c0e014100d900072640103c045030f5403401543c482c454250300400250071400c07003040c8641700307900c0240c106004401c01410503071a5030214140350394402d01533011030410500051102041c02145015040c080009403031180c61b040041c05903130f5009001c58816011600044014006a0080e5500900940c1d291610004d101c011050170302d54140a9000d05145031510f91071810038002c551089038180d50300c038a0061140c982d250040c0003901003540000c0302c0303400081d0990b00c81c0060046208041c0140003454588203580307441525141120065400010028034142e811000d00c0045038501c2c24203400c00c0c486a90618010f00f01005099441441e215921050083d20498070384074038401c5c5ca203075030740da602e403001c000f01400b08460700740369948200281e40840c1000074003160010b120b01005410501010200301e0200401d800c0740b07102da400301e440a1410381e44420100343c0102c590001c1c1c445541408401c06401e0401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 418833785 1250 418832535 418832539
    0x1c0b0a23041a070f0807020304050913020103090813050406050901030b0c0a0e150c010e01060b161b09020903100c0207090e0c100f02010e1b010f1b0302030702011209020108010302 79
    0x40000101070100d41c2d040301c2106185500c62009526020748081d00056010100c100041c480600140c81d680c000411541030340d1000340000341c15656410010f0201c0d90b4180304070f04154650b5400d00000e691000540b0151150b0100154039505003800e100884040d940410b200742c001c0001007000c5103500301100d0700320000c1584650759620340e66003a503004200c40681c6401020350620840030a402501030400b07000607400078094484402c014600b80d822501030f8082c0307200e0420151070442d04410703d211005204001d502d01076035030300141d0f881c249410384c409048240c001450920390b10782407100b5580c3d16000d000c100240300c45080000d40c0c0d54041d0243c80710b00c559444800182c1c1004100c004820385000708582c28040307030054000c00d41250b4001004c00340d030130103001103510003000c100b040303800307481400f0201305415042c011500020b01c100f00302c060007442d43ca09409504241a0380718440d01980046031b660391144001807000c0d0104071400d00c0c1d5840c0c82210f10041c0c1c0d0040e8814112601 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 418835035 1250 418833785 418833851
    0xd03060b070305070c0b0705010207031e0906050d32090d050d1a030a030c05190807110409021003091208010b070f03051909050a0e0c03070516021c0b0a 67
    0x1103450400c03517284090b044107518000105500040143c15002841e80038480d42d04c000144415482c036030040813889440001040b46244240403161140b00500f41c0004054404602058010f1400c81c2861180b41c5800c00f004145428072400d40c0041c03030107504401d580c00280006404424002d00714000c0b01a04d040b91616041e27404c01c9800b8040340000da03010001e0a58030051454075020f08040003c42040342c1c5809411005810300e0000414001d01940000700c8a21304060390360789481c6181c0c41100b0b0750f806a61251500c000d601c0c0c5100024140d04035071000100d5506901340080240182c2d10f00d1020099014010b001810b081020f454400e94804d145c1d075001c0e8413610f0142d8581c0240c04540a00b00e0400f11290030107540315480c42c0c00c070b070010340300c9034081901c5205101070b1040840310207100400c1000030075140c80c4100e005190004c40302c032004510304590303400541110b800800c0c03400d40000303c05020040c4495203c42c590812070656042020a034a5005850144c0c40c4100038070868213 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 418836285 1250 418835035 418835047
    0x3010605092211190f140c0106091127060a0813050303100e15010504030b10032a0b07031b170d0b0108070201060608011211090403030e120705060f04150e0c030d03060b070305 77
    0x41f0035088031002d070200482c24810998159158074a80d04230654001c0c2100c6042c142e014080d840c1c0410040030384014026a1500c8101e400a407003982c406805089604a0214240c000c20820700103140601c04000c0448440d41c40e03e412800d098a0217000c550402c405d84261350302d56a080070850302142c1d40300c90245c98581c0d0700e02c600c400b01c0f44260700c090104180c0e2500220b44070294100260280d111310a581c088540f40c0d0140b00e25409241d1000b0701041211400c051455102c040090049200f0034407590200c180d05041516a0414607403400d505444002c1c00c0320755030300000f200c0d51082161008025807854002c005207070000612030a03060b1452458410103006e0758052000b81d502c3c000d407408502e401c091800900900403038064015501520998403100c0101e1000c460180b81c10600600c0c80e030b2a0000100246880981304480b05402d000d011901a80c1600a094070204c6900143c00100566014141000600503001f0101464814207000309802d84090f1281660140b9016480350 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 418837535 1250 418836285 418836307
    0xe2e05040c02010e010c03020417060423030f16061107051b06070c0b030a140c03040201120e0d1107090c120515030601080d031103010605092211190f14 67
    0x2c03c07544e44800650070f0099281c400d58043c0c0080c802c407500b1170045043d6014584229484130b5050700e0040c2a08035442c450040d44409509220382c049203003050300d24110311801f02c001c1a9001003404d6840f004c103450502d042c443c16105291400703490b541c0d0075241c0300b21b550700c1c5925112050300d90050340c52818044142515004290350321954084c0405071040c0d21111245043c4d0003c64640b5056410040341040403001c0310901030049a1a01c005801e680340c6074010f44194036a00304d84115181c0d511248040c4120030000c4590610098503004101e8074808911401c00c1c0c00783d001000340505101c100e50300168465081000f8180ca503000107403540721a5131040e40152404c091b603078903100c0c140c0041206080801c0005d50008192400c200501031391000c0d1255000c244600c201040c0140082400e5003011030541c0004101d07211107a25035455080410b003120410340480c95080303404201001c0502c101c1001110034003190030000307c02c070404400100300c140d14030641c1380000e8002c03515200b09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 418838785 1250 418837535 418837541
    0xa0c0606080a0f060c0903020607060b040b0a1415030c0a0e12031b0601050307030c05100c020402031512210705011e0902011d030706030905070e010e2e05040c0201 72
    0x50071040d02074848840060501c00010000c0d49000e41d01103181013015801d003406500c0c44011240d02604035414052580c907500000d246c038000d26a002601c58500c8003180d6101045840a000c1010314200c1c0c40c1449824001c60340e10341034140549031810402c0c0410b489899099a6458020b0b00d8004010b08404010a114500308040288544004210148002c0ca00e40c101d0200c104884215040d584e41d54042540e504c02601c805080c28804800c14061410711f180c60703042c500b545052000040442d54046400c9070b100711541c1800201a440c0c5083c10301d84071b954280c0d1040f42d00000d080141c041c2c501c4400001d41504031207402c1d14002440020818290040201c0d09100141403000c00c4100140d200038180b0300400309d000078101000b860200b03143d41c980615a02c0b024008041d81400c004069005004004080d00e40c0d1068110000b01c074101108078034080c20b011413030640e507070a1411402c0b02d441c035101c2040d5100d8521940d44520040c044c0c00c14001c1750421140492401600c4c1070036801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 418840035 1250 418838785 418838789
    0x20a0e03012d11070c210308010e130c061d0f06090405040201180801090c060507050c06030c07050601300b0c0901120c0215150108160e060a0e190305030a0c0606 71
    0xf601001048400a001c51200c010049800c01a0b04560010100400c41c9a0040315031004020402d190018401045000c10f050780c8407159400342000c580c141e455150112000c1da10a6000440c00882c0d50009080703400e000000d490140c2e82e410400b140c49000950600980c040c640c0140d0f59080000c007568481c0340c40100740e1399138041c1444030710380300c1207050f0103081c0300310f4241c44140390b034200064103600c0b450888803801c5e0414060b02c88140310900300925039102602e8480015010b0103204042042840014001c0000404918450443c000d0300690750002c0d40050744416941100500803505911005620181c0180680d641d10403c20050319008140400e08148600d095151011240c0002c1d0100344205015040011561001c40726003c07200f6410f5200d000407400f201045042d00c1440c00c5650414450810b2120005020041195504800c50b4840061a00701c0004071074285848460190514414a0340d103107420340d101c40d80c0c0d03841030400e90b0701000f00030282d410921403240c1c85580 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 418841285 1250 418840035 418840061
    0x9150f04180501050406140913140115050a0b0a020a15140a0203060103240303051b0111030a0f0504080301051c1e0506061e12100f020a0e03012d 64
    0xe04444412000c1c01010240103140c0118502007001c5061040500341c04040c4500500051180d9610304844c0c660400c0148103c908241c000d100c141020828081c1d03020300c001e80e20400c2240c0c3d14141c10030003e100d040d445410344040801940740710302c3d0301141007845079400c5086000c01002403461803008142c0b000c6018820601501030100369007242e0000e40c01600d09907002d201036641c462508280c10401c0030b2074010f52114034000c04c00280110003803e030a400041c409030110f00b41c000c4441c20340b000e20160392054031000041055840b55840323020ba140401c05420051860076507107030005440180602403152483e145030601e59498404080031107a402440321a03c0015601c070251901d10403030b81100d01b40240c6002494030705000400c841c152000e4910300540100d00b8040c803d25030860702c103440c02801a803503010803030030b04c0340a00c60030340b0940800166505401500208a910810000340c402d90428204241500540e045009400324038440c121060074000c400c00010503440107181 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 418842535 1250 418841285 418841309
    0x13091b050a272d06051c05030904061205070b03040308130f0609050303010501170c04140a170a0623010501030c26090613210c0f120e0609150f04 64
    0x10202d043c07103051042a0300c081412640d40300400b0061070b410303038006000b41904000d404408140030f02a03c064061494054020b40f80b40040030404607003610440d0300030f078031785020183c400400c1000070054013005111150078a41182416580185616400742c10410850304103070311003090110b144121900c80703034065420005112540741040d12034000b441910f022400600405071180c40808030b02c0d01c80c2c006030340c048e40350906000341406100c00041384a900009403140210390301c01d10807401022600c02c400105005041840c10000303981000d03141c03019254603e4007104030b1107280600c0c5070658009003400b1849060080007103850840c1c15034040d11110b15604820703180794445000354012040b8030300381e4940ea42c800807040400801c1c0400106031200ca0a91490103104001c4c0010314104545020900e102145e1541b49540702c08150568094040991391900507400603c030768441d100035200e8a00340914400003030f402c0c00c1c00e920350004050001900e03450401519084034003800b42c1c28000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 418843785 1250 418842535 418842551
    0x92309090d02120f030613020708071a100302010c03141e0310060207120f06060e07030213051e1e0405091c0201022a07030213091b050a27 61
    0x18503a00c14103001c0400c0940611203e11006451100c02c813112526103102e190b185846040501502c1e0152501550f56551309101400010b080d040050440500a49a25121640900c90b0700020301c40501203501e0a03485010410060340c01c854002801c03a0103003800c440d50303500f403c00e0035030611400700240000c02c41081140010396603000658002c01500c070b10034070b02540b40d034000d80c3c4e1503d01c1c1c00f900384410002d01e10900019400d04140710180d114600204000e965091105003010042c0c4181003c0f94021515018610500500c00014882221500c0a50300c0702c4126403c45c546e140b101d81e0007101d800c41003030450848420b11180e404800350042251b85403c43c1d98988880000a606800580c49070300204043d00c1402680c05005800c9040d0952005092907070a5202e64001d01ca03c04d80118400040940c2c0d81e44156140002020808500c0d000300c0d1400c1c0380c850b0070301e41ea0504044031040051017181c407840880b200b51552004440e01c0c000a07204178141100c50500300c14032250400042d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 418845035 1250 418843785 418843801
    0xe01060f2a0302060c0a210221010905060f0108010b070303090b0c030129040504020d0b090406060807061e050307180602030a030605041e0f0216060b0109080a03092309 74
    0x2041d4090080d0f090b10601d4071440d80f030000d1441042034400000300100d240c0c1441c2c9001c9004100b00050206006103032510040d80c0003000d006240000c01c0010694004124031001401150791040c0112200040d092000c0d0000e00042d07010b00554840740c9000ca0f695080500079403006031101e412541212561420320b1041d64103600074086d46d14070b05100b01004500c000240341541c640c0e41c150414a08250800091000941011a107401000c2d1540c4040e8016202c8000f05809940983c1000c94403604110303005140c05000e900004c00c03c6003406401840d15241070715003a0100745483c0c1107580343c840038011113003020403907089400c2000000c40001c2050700040241800b10341d9031001e21940b40d8031020041100c0d140d50300741081c0091205288030f005a5540300c50a0801070300c00040c20118010103405a070002c2a00440740f06a641c0d406003015a04030066000920400008003601042990010080b444920800c25184004203040e08200b406c07580001296001030042000c502d0030b100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 418846285 1250 418845035 418845107
    0xc0801061d0406150f05070515041713060201060503071409042d0c1505070311030d111210030804030807050304240305060909151312090305010c08010e01060f 70
    0x311183c08a4404440324245c1401041034070012a000000307081031040e00000c1c0c512111008004540c01e000008500742c3c00410341c400741030144c0540600150784c90610030301a0855207a40c00591007540b02c15420403240140621881c22404260b404070119140c52404080d54400701c20000c04c1b949540408501c0004080c400b600c169006040a8024594540300caa84250603442e001b80000d000f0000c01c03020a01a98210154003003900c122441e01101c00c7c6c00c101103911044255241100001c0e01c004014545035a550b0000740340c480c2d80502c00d01e107944081851045210040034994045465028800103006a4008201800300711068000c840403446c0081900080740001c64030b0000403c10034245014144d210380c030744500601e90104011000564650010710451420515040c1c1e42c001030040d000b80b035504095a11005031a07410751800500391001c10012038100212500100302c0306200080c00760440b519410031754030b1040700325400c45040785500081380f0660000701411604445d800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 418847535 1250 418846285 418846319
    0x40e010c0f0801050d0c09150806010609030209100806061e1903150c02280819020d0311040506160b10090f1a040c020304090f0501090e010c0801061d0406 68
    0xda02c40721140c4c1c8440400819a0303403c03078003603c03141d21008240a901d201e58001da00e040c05544000c05026502c100d20340c81c10200760031000005041080800450500c601c0650700051182f880c1404c003420400043c1e500c0c107009100a00c00c28507203e40c100b900c0008201c0d0454101c02424050110070383c5804d10b524010381e8442158411450b406840182003e4820101040a1039014116001c40f4203a2036903000207070052000c00001d04181240064028001080501c4500501d4002ca40464101900b8000701d41c200101341400d042c800210108400c00321420b860003150001e4556800a007064003450740316400030003499a40c0c0c03d1140e090901e1070940122080388100313200b81e050300c11422042d81c00301f16413181d00900b200c81d401124a06500034040d42c604904c1280c0c00c20b9030f90403100003503828022500542a41d80c0f40188010300c028016040f600c400c280082c0000b00e4820b0300180310b01c005120700b00401402d0341d0303041501920420088100d40c2c0041c8144140c6403182d481c3c0c61072040315 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 418848785 1250 418847535 418847537
    0x1090e0a05060112050609040201030f0b03010207120809070b0712050f180301050a090b0a09021f0503090d08070f0806030c030706030203060906011b06110d0e250f060e040e010c0f 79
    0xc0600340104d02c024020144166070150010f802500c5680c015406041444a0301c00d0690b2500070031900c0303407401d01c003600409010b100102c0c000c4a07041c04c05025440007a002040360742214070140805a0114100ca44d81d56001c6030129181d548007000725203600881c40c48030200342d0005802039400e100094441c40119044000b0000c5031100510001180c00500c0c0043c28078103c540018440c00e03485c0e00c800030031400600b0110542600d0024403404140c1d0702c4165010450210900458002c10803044040350150f0615502c2410000005041d12659020000401100d4800543c4585040c021101252809012110820780795540a4088e40040321090700811603c00068103541c401c00183e50384100b501d20340c201c1c194140d1212000352040b883c000310040c104000c03500d0008018490b08501c3c03502500038240c10402415100070a483d0141c0001092984c00c006003e00118512110112000c1e41042065410000c021801908803640680d02c154a031044100c0803982013001388541c0146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 418850035 1250 418848785 418848797
    0x90803100b030709050d0c0317190302070b0a0f09051c02010f11120c09150a02060a0507080a1a06030c04151407110111070f14181501090e0a050601 65
    0x164503007101e80e0300040700c0240c0007440d414000c0209082800d4040605401441e440140303540702d4460032130b880700005c1071491b0408000390103c80140c480011654202c0b4503d0107500e00011502da074180110050309407408955540301d20014070382d00c0d0784146600c0e540318081d40d2030700f1051081d20f80c4015100010300055400e10046c420001d40e02e216070b2410080c0851000e04080c4100c1c50076094400041c02c01503410707420054400c0719502c80040402d564803840e40c490743c2d10100c050007402c00d0301c054100a5514181810300c801a500500000d82c0f2503508100000c51140c1244901075045000420350b400c4a00001407085a26005000f0300903a690091415020019001d0489540c0f008902004044005004200000d180c01c0600391801c80e052500a407030071051400700f4141a0941d0020080c060803240070400304132200c105800020084490b16000c2550360255074201d80004c040c00544051294aa24140c0c010701311000980003429000c5030f2490810041c500070142951401e0101d10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 418851285 1250 418850035 418850039
    0x6030c04050105131d0f010c030e0a030e121905060103050610060c1b151821020f0301020f040e190504050d0c02010e06120f0c0f04060c0303090609080310 68
    0x1024021541214006010b09822120041d1481c004025440605c000c2900d804845070300342070f04020b69821401102d000103101d1259007005022110b0103514210183c0000080300c0219400c114002c50205042d0780c16100030120f40045800c00100b0300100000040310000002448030008080341a01e00c100101c3d582911030200c2d9000840d107610a00340000d4046411400140454000e01c0c0d40c40c0401082c40a590b8480d0b03000c01c0c3e05008862440700190b10031440040381100f180380e010040407a400c1443d000b1400340d22a0b410301018081c082e00803e400d146040d16034400358100c9820300c1441c100300d525203848280c0c20b5148041666070300c400e4101e000c03099181002d6840b41c00d0081d0f0303012004145d03d8552003004c4d1210000321200b40d051183d10604c040580e00c0f14001841381c80144081000c9524000d600c1c06200f9801905250b03000c10244200c251010b441821501039076964184901612560302d01100600101c010040840c1e0030120780800708140c44028500a030b00c0d2220500c2c00b0343d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 418852535 1250 418851285 418851289
    0x1d0a0f180908072d0506070306050103021306030e1905030a0906020d080f04030c020306010801151203320409090b0601030c02190314040e0115050a12021605060f06030c 74
    0x240403004041c101d00c0b020014100000c43e6040c0103e070005031413801d8540440080701140c4624040e0109540603080034003001985981031080d00043c04003420218141821043c4100e00402207002e188107159031980d640c0002c0d04100401c10700c14440442641b49401a407421940320f4100c0012000410f50b01d01000c40c01a00104e8000030038030880d07503551016900d001e8104048140a00203a00780014500c0c41d002584060003c00d020b030040c0e10001c120340e80c1945040b01480c10541c0030b00c005240c86042da100003503000300c0860454220710340c0c05d10180304a1a010407182c1072400d260000201c0010b00003105c0c2101c1c0c10840310107001d0250f102196940760019019107080c491420016003098015405844101c800341c5902d90091401c01c0c0c401602c079501c0400c50b0b10940245801016240042004c04881107803c40d40444a1a2140c01c0903032248000d841c400c480ca0500c1107180e0081504640382459411484a0b03e82100840324030b030030090645900a9000e07a1990700030300402100c90368078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 418853785 1250 418852535 418852541
    0x50a060518010e06060306042c1902030a0b060310060815150d080d110d05100510120908270f030d140d140906060a14010f1d0a0f18 58
    0xe88402a0500684ea80c110800900b944001c00f5560700ca036072a81110f43c95a106d0101480058110804801c6101008070180c9040100201c002001c400b4101120040c3c401199059010740e201440c02d07095114500060b082540150341184114900b4000042a444c001048202c001da12454504651210417000c00008820501680c200005401005c0003805e0720b4003c041103c20340310001500e04e00140c5420459000045942910b612141440014082594860000c00c403c0320600c04000c82600040c0ca8030b9100411500019076170601c0320103025401089030000d0401c202c40e1030700c1c0500410f030503290540500299018040009059005007000510780e0121402511101c51002180e00c042405034040d48203c011562107407042290114404a1a4001c400b0280031780510701d07102041c88920011a0b00140e13149524803d103007100d03600405c40f03802ca0a01c520b0401441c0d40040c82d41b0220000714101c07a600540032010000c0c6640754401600f06958000042d40c950451725030a6900b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 418855035 1250 418853785 418853789
    0x6080105012003090d08090411031e10050a0305030309070b0c07030b10031211160608060105070215030a02040611070f0e09101d210901050c0c0301050a06051801 71
    0x4107140402d8040ca403580340d080b054080720742c40c2c100c2c0e1400c103000011a020800c1c5600490300f012010812841c9407500f8001c2c06c05d8500c0c007c80b0141503280c014600444240c4240415800c0707010030010640302c0405040c14400f500003d40014003059a900c1e00a50b254402c80300022540240f0002042c070362081da080710041c050000c001c150320303810341c4c50b4443c07040405414120401d00f2110000002400f0150840120310701e03407a0561103201102c844d506091960312040400b03210a0340901030b0540102c01c86e5000b417403e10308140c49174040c0c4045032104034000c68244071000003004001c5480041e80080040d5011030740c1c3c1058402403d19015070b0303100e85000c0c9c201007040c00c6c0c0007406800100c44050394884c200c0800c50718008000c1c20524220f4a28101036105001ca0324500c00706004100507602080c0d255081c041032440d120780c9000e40724051412580d0400000080100701224108084550048001d00030040346c200f440f4000010302040c81510700907610700885550300c558140345581 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 418856285 1250 418855035 418855037
    0x20a0203070b090303040302120d0f0e1e03251d0f011a160606060e030c010c0308150a0f062006130309030503030a0603020f030c030a0b090c03030a0314010608010501 73
    0x25442c20601001096008000c1041c0c2502c0300f8800040503035162011404881081c0028109134151340000905002505a0650601c09a211a12010346a5903901015409a010041d12001c48c1200180c02d243c0041680c1e11700d920a45a4410490b46600351241100c0e50803012007012607108064040b120b40c07c40e401004a46a5401000032505008250f05242c5c140d122036407a021780444d1600f0409a910700030741d10241d44010910590350411540b00d07000310201e00a218082d906800284030f54a000d00003401c0210940101c1c1049140b440c40d8058883c1c018010030155460f03020242070f041c041d206210025851745001010461045400c7c000c01070901e014005c00c0e81c900402e101c400c02a104214100b10105500002240041c000365000d110703441d03004105185076004006201142c2070309544281c2205660b001195400201079080a0b801b098500065440786041030501c1101400c003600741c0400038402001c00d605900030b01d91000b80c1024a4400c0e44c807500c080311100002d0007028 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 418857535 1250 418856285 418856293
    0x2060904090503070f0b1501030614040c09120305030906070905150a090306050f241311040503071212211a1f0206012c0405010902150a030c020a0203 66
    0x48241859004103001da4001c0c07084a2030a0309964801c0329441c0c01c4001a10724050306010300071100800303200901000d40918060100f24281543d0300e80080c80c440ca135a200ba95074001e80819180901107801c01844908a203901000e05030501034469403040301c10120074026400002c6056000e040c049040d9000a4942261003035030f11a0001c0360780c007014901080c011000c0c00000015400d0040b148075100d00035110078507050031020b40d041c0d40e4520000b9a03000b03640c442540720340e40b1414404d141144502c1d402003101440d0301e0304410f040c8116001181c241c000c0020100d0071205111325a0910791149407039950f0105000310031280080d03140c01124564180b0180d2104126184d009800c000d41103001504030700b5a50740004425518071250488001d03081010f49114a406020503401010035101e0124010f0110343d85280780c1105403803040c199128080403a09200d42580100a00c59004e084e540880030046000550b44d00b014000000080c01c2038202c0005d1440400d0030501d180d0702034020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 418858785 1250 418857535 418857547
    0x60b070804030b0a15060c12080103050c060a120204060324031a0a0b0307060f090f1559010f121806020406020115060c06020a090b0712080901090206 66
    0x1090300c61030301803c203003240c90720f60240250843c0c2a461410060003c7d0f222069075041c0b80c80e2403140a001e840180c002e00c03455800410104502184106880d0400c03100f503540d034450210150348150b4400403a2582e50300c003280100340542c01d80d0040c45a991248405a04259403080e0501d040c0352034000200848031154000300e1402d0070050f0550080c4070907074082842440200070034a040303d9507112230000f41182d10a504425000503400380640025900e000c0b1075400c00c190112810300c04510582044500250b0541d802d02620010701a03000803c090100c00c00b125440d404116400c9420031568400c21188194410030b005015180880c10b842c0c40245441030001a512014a0001540300c1c0751100d081c6030b8580303e0011500c0d0501d1003400300586035400c2410007070845451550307903400700c0c0110a0502006401c05031001009501400150f80c400c0c00b504200c1d2004040da01010300820f000c9019020402c10411383c00703a210455a07058030b19615014010b00342c504664010307400100130002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 418860035 1250 418858785 418858793
    0x9030d05091f0515040f0b100201020c0c1309080406111509100b03010f0c1d09041e060204051c05010e030f16110907080108060106140d0c020a02060f0d060b07080403 73
    0x1115911a910490013054204080041001d42c2c0e0340204110f941980c40c20215030a182c51400010400d5041c80210b042c4180483c0c400c4d81c030038101405603c2001d1b0000014488100307078028621140c3c2c4145000d0300ea036540c080141282d1501c10107005903003c2c1d01c0001580405c41080544510310020080800043c01c8164400805c0b4030358100d9010f548078022080718607030382e008240f11010b1969a000b0200c0e50000e40110140c3d88080d01c900c200a00003e10002c80e080d40c0ca00303d0140400c0a8107110444a441c08400901c00d42e481603812030304103040038102050445204400340d0040000b444010f070005c43d01d50700c0e4481c00000708001b02e004e118200110514140d0301f03c94500ca101503440d04018440050800d150480301c140009141c42c0041c0304440080c403180340140180d040c0740300e006c1d40d80741000350f0b5809031544c43c07802107541d001c2901005200704481503a4540140c602c999509542c03500442c10340c41401114010303400c0c0b0074005621340140003102d00381303600042d41c241070a0640c1d031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 418861285 1250 418860035 418860041
    0x21071211040e070e15091e0106050c10090b1e0613020f040803070606171b0922050616020a200a0902030f040303060512060718090509030d05091f 64
    0xc100c000d6104122011030fa0070130010100f4080c4400d5044030303901300ca80400b049140403004142e40404d40c0240e40000c03550701c080000d241914a24104107460700c40c80c00c40d4500d0815202e40c500b0915040813860f0040c0044060200d004801040052080c1c0a2031254550b00102c00e0350826001400300e44652601ca035950301510001242600c003500c3c182e1380d542d206165030000708065421554400702040400c000713040e03501610582c0c074090444540c0078128240c124414006050054074a01e00144110f1040c856281e07090041320004800e8032042c1c1045640d50b401201c40c83d001c1040702d0440010940001901c03440380380d00030aa1aa910300c0064442d007480080c804840c1c010080540105803901c03240041c1d88504406001c1d00e0a40c87c041c2001000d6482c103038019409020307000c0d0f81b00c00c052000701c3c40036800b56203402c14084610a0790380707a070302c58041076210009852402c03084c41a5040c2c084000c0141d800c014409000a0320f0700419961641c230001c032034105c210303545241f0f2500311000790 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 418862535 1250 418861285 418861301
    0x40201021c0311030115171b07080d0507021b0f1507051204060203131d0411031e06010807062111070618120504050d060902030307022107121104 64
    0x1150208a030600c4403c141501c0d0803c1e044946554290084003d4460340100340c10314140300510710403c3c60900614003103118400842426801c00001080400d101c074440c21036540b030205110030829460301850081d141d0002201201101207400a150300b0761402e40c8500700c440e41c0060050b41480c0d8403600010300b82c0d00071131040381c8600a8111282c00000300501a0008011940117580d807a00c00d41807041d01035200e0f400c522211081c88003040d440e6000301410a50040e8000c95181202c01d008000030b20308850201950443e520090402580301e00110b076450480b40600106c5540b1f949503d4286d5071400c20706201f80c9044202c1c40e0044024006030405800c0b00c07643c0e51a02c0ca0180161a510150b44600180d00c104030405590b120402c6040c2d0a4107000c584140380c81d50610b420900025500180b99401800391a20386001c40309640c1e003441114001a4020010306098100103e22544800204180c0d41580030780f0000040aa0001d8a02d100e25640240fa0100422043c810000201404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 418863785 1250 418862535 418862537
    0x30504050703020409080706050106020d08130201020a05070b1812031c0b060d0218030703020a1a120a090201020d0e13090f240b030f06010605070f080313110306040201021c 76
    0x254000025071510311800c0c0001d4040c0c2c441c0766507a1508d041c00c005030f88060b4003400842d07106114030005241e0141d811604104e81d00c1020303084280a0004034a00101080e02030800e00600c900050005940c00040240c0001100d61040984204082000041c6841c00c10700443d04204103076202094014200900303410050000602051801c01040302a001148420a0179500080100e5241072441164540e0b00085000780207040c156030218604a2051140780700101c10780b101b15111109013001d886004030380b2101032096292420750038000c2c0030041e5083c0d02501684510004051140044015446000d08145000310071302c00d2507001089610019501450049016030018070b030803882031442c0b0707810316130312411200340c646034812900c0e02c1800510aa005580c811010900442c140303044540505000707480f58030600b044012260510ba00810459000040141c07030750103107021203100c0340550500152500710101381951000240d4010f805031740482e12540381c103c080e07031000410f0506 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 418865035 1250 418863785 418863793
    0x3060625020a09091104020c0304080109060c2a0807080d0e060108160305060a0c110a1a07050702030616020f070305010e0606010f080114010c1202060714041503050405 74
    0x24012000d800000c10150069840c0e154800600307616101d610080038094840b02000300140542d00c03424400802c603c15070160341c02007004919148207000380d030000c28160000f404401c41078074084006114021200c40800d031440700803c6807030f2000b41c40d0400d01b088a00807881520103916030244680040784d048a502c43e003013203034110b108141e01900c40360806440040515504162307066040250951800c021151103c1081000c0345002802c180c001c03030b411000007241e01150204554158040c448040684908410042003054054002c0c07030166215429080c513844004045600d48200c1c0c0b4060342c9503200d8004603e151400f001c0080205c0c180740104c60b280244050341c1c3e070410449074400d4600d65540e00c440240d10405010081c0d2044003460202e05107508141c02401c00300060049082800c0c101e641e07031000f0b034040c107030303205c1c02c650002d20440c004060840002d40d40c00c4221a40000202040f00040c50140454292800d407238880c61100882c0d81c140301c0850062400403c25142441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 418866285 1250 418865035 418865047
    0x60c050a080a030f2d0905010e07170706030506060d0515091e150315070210090b01050301290f01180b0406081003030f050a050705060114130608070b030606 69
    0x920301d00402c14440d0585003c2018085000c02e0707011501204850962020110910308004c0641000b403c44075003c114006507030740260a01034010300c80d141174442140309612001c504000c0500108070603045110481e41c940d13440b44001c40a80700c0544585410800c01c0c030410801e0303030f9103400c1990b1246202200d03080f034200300307400680008000d540c120411001108800d0750b1512100c5501d5000d96003489503186500c640f400300380c0d0f0341d0840c56200154043c13103000c518690b10a02c1004401c1140e040309000c40b405a043c8401c00c0e082c20b2007030f20b02ca58070706450010f40c2c811030580c941c1e1070054140c014280400301c3c3c051040103840c07603568504225046807035044815a520b152009040e002c040591540d00380346000c1c4c0003810103404090280340c1c0041c00c03c00240d1002010310a0300451411070b890300c86a500540309400340c038000515a00921001241c0301007808c5070005422003c442c02c8122000030021403049602c140922070850300300e04018084409680d0042d0b070046c4000d0045807a082c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 418867535 1250 418866285 418866293
    0x80412030e0703060c09080a23070b0a0905100804200a17010f0c0c080a030902060d0f0c0932030a05030f070215040503030703110106051909051e01060c050a 69
    0x600c2d90708115641e0740e8035081d60300305e40c3e40044284050544680107141d030f48000d441d000704000c200c010690000458261041c0c0141080c80b21000410740c00f404591602800344e8042d00107943d80c001e09000740701840c90394910f0792080360514019904a0551031a403680c0d1002c5a600b03018505180d5000344140c680020300980c0b08a1090a001440d8000031f020710a0340000c5042d10800c00ba007500308548a402040403440a20848440420340d04001840080e28130100b0b8417405040100c1851910707201800c040400e0507080640800e0440d038605242c0354847d86407203a00d0100c4600c1541120491030113660a600100d0185a0f070100181190000e09250b0748140c9903900400200c11028400b007201c030214203251410340440460503240c9401c1905080c0402d03641c1c018001c018082080c901041c5020202c294005006800060082c4020b6099104404652103d510440307a0051070103002a0704500a800d2005d003c40d00741c1115000f9910704441110041c0b23074800103540500904590b18002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 418868785 1250 418867535 418867543
    0x70315080a05030c0d051e03060a030204050901050703051f090b0d051e0709061508101a0705061f06080a0f060f081e060718050409050109050d030c080412030e 70
    0x151142e4011507449012503202c60400c514890420706010041c0000d179001e44803402007a8090401d49074982d242c1d0740b0342c0005070b000c0c0f503103520180d0003a2410040c0f15041d013064202c18070558a5440c28401c1c2e84600b2841614407400010b0910001841d034018422402c00790081c1c60003c5009022821001c455150310f0700304504203180207180c00e00c10061808042d024003c04d0000c200342c0304200546890300b55a1000b0342000b484483c208100340002076004400060510050400200b0502c0c070100c28614204041c1d1001c1d40c09e82d400c0c81950001401d003801c0004801101d13405031050208a440c28005484104020300a480700380d85806040c081c03001c4502c00c0710010174078011404541c80c83d02620b54100460302d10709000b01c40e140300b00c2c0c0207000c00000e501ea400007428a0f2204080110f180e000c040604103030002ca40c001c2c1001d0102e001c5c094150030180d00d240c05031041c2d41043e40552015021101da10200f07034017041c005030009011540d5900301100c80a03050902141c01c80208001c9414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 418870035 1250 418868785 418868803
    0x203070201020712080606030c0c1f0e070b070c0308090102030d0504030e011e090e0601090512031b0604050a0204020304143f030114030307021e04180b07031508 71
    0x140c1d800b03c2d5a00038005803648000c4002d5a81c2400c0d95a82024004507240c0e22000b80a18040b200004600741c0c0404200a08140707042680c104680e000d11044c2418090600b0504442c0d040c42030f0740001c940e10250350301302c944440c1e001c5414000d031072840d81d800605400c2810030700c2c1580010702020a603135809001e2680300300c4c820350390141d119504030000f40000d03680b50443c0360f40d01c0c07041040c00b8105400c418464182da6400400e058a0f540710300c0102c41621380c0b604107a070800518200303035209210010150003400103615031038140c01e000c82e280543d640412240030702a40d00001c900009403e00e64000c6400500404035034250300058003090b450003011000051021400320000210010102103410f80d240302189101807150400302c4030b108500044c080e2200001007481900e9140e44d003001100e5a90b81c1c0546821460445801465000501046202d01440c10f049000c61100c0014102c1c800c030540c4102d15441d941c0760610100c0040c007241552911341c00403160b0104101400b0005104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 418871285 1250 418870035 418870037
    0x801060b04170c0a0311240d2a021b03010c021906020f031503011104120b100911130503010908071b080303131b080a020d080904050403030f0b15040b0901020a06020307 74
    0x40304d994a0010300010b54400d0b1f04141143c041d000c004d007243c41d003030021112840110503020032080421001c04000500c02c020702c0c80041c0004040705440c98012403415400386400c3c0c6c4216450b000c1d1410300d0f00b070381c15107902d400041e0491201806101d00241510340f0207401144014102800c401c580d800070340c0240c0300501544410013004010785001d000d8080e2809101381c1c1142041d140802072851035016440007000030880b800040d080344081c144203c004d10815400b44212504190303404000e9100400a980e520704204000c962424140207020340741c2d520140e058a40718840d2141180303041d02410b0310741504140d5500064031802080038500924140e1060400d0f00041d1500d154031090180020211202000080240745408184100426010f90300e03084410a0380c03420400d03038400e0042039035210746482e080c4001d2651590004071064211481008031035002d10402040c0f06031316283d0b5104182c05c00c002e100e0019244040c21410106004a4042d10110307560031041c0e80044448034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 418872535 1250 418871285 418871303
    0x902030a050709080c1e04090f150c05031b07060c02031312020d0b061306080706080a1505040b0604030203100905070e04030509091806041208010801060b04170c0a03 73
    0x2200040c0c061140540059160604800c4189400c642d25112062100320a10410744013401d100070070320303001d4035040d040d000038020044800c803450082150882c42c601520200c04010140041c070b2010f1103000850b0b4030a485003425541c444010705403031202c480b07642c4030401040c021b20700000c0b803034010030311800b280d41c0186896500416819903074071503503813101ca0359980e0700d1011b1307026850f080d0007803e03002d030041d04400e01303a44d480c004101140f2201040c0e0440d18900b007000185038402103940416990305a4407120a03880f00c0201c0300c00d444406038903461304090448208800c4c80e059001d11410f00d0003805c903e0400c0d80c1c03034001030b04080a00944200842e15002220b04101040c0070300d4000d40000075034800b03d4140354070000c0940c003c1c551040d00514074003001c5510700c0e8954640c1d400050310b07030003200e907545071503d41754400801104205010a17050b030008902d0320010302501301503801501d111810180340c03020b860000314416907150300794042c504c11500207480740c000300310113140120604 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 418873785 1250 418872535 418872541
    0x1101020a0e0f0409110409230d031d060f060a08251203081b07060908070b07091811090901030507231f030b0418061a0603041b080304090203 62
    0x1011541551192a9104510300b00032035000a0407421202c3c03205c00c050710000b410042034500b00254036101d0904940001c1050228a110080040e070551038955a9609000b404880040c034280e05145182007100be80102c0d000809030502e20003a181e00c43d01c000c2000c01101c0d1788900d05405c1c606032110311a06820143d00c6000412120007407000103101645000c41e880d90242c400502c2100013401e6030340300b15190342a030140141d591050302ca116412080030000300407640b80c104072070f62013000c3c103d82203140352000400c0c030790003800440101c0707240540d4a00309401c0042100020810701800000d101d9050013114a580c840010785d43c040d41c0321744d0003032507442e0070106a1030065000b40c40070000c89003031101a6490740c070b400c00000060070300c0380810880303c0ba800f034050700500303000100707240c20516242400a094003041d0301d80125900503081000002c03402c0360b0321040c0d600314041702d40e00a00200089400a074403000515060800102c81e0300045844402c10750440d0b00a50048141603004400c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 418875035 1250 418873785 418873789
    0x7050c0c1f17280b100c060f0908031605040911040f080105090d0311090316090e010228090b1603140702030a11030a020603010906080c0315161101020a0e 68
    0xc402d180c07544035101c1d45151481c50142018115440100d81110416000210f82e00d0354119043c84080140884222281100d000f40114034250040e1801810324076001c80307548803880b95100040c2c21040d1a45103a460740c2d09000b1500c2d0a000d82c01c2005020440090400400d01c100607484148100440d0707168601250328610402130740050300d10341d242000b84500107200045030305514920342000714611150301d00304100750080c3c6409175050301400e402410000034003101da41c1507840b64002003000000880780c45080b800f5034050002c4200460140c4d001411050f04410700c0300800340391903040243c44004100158010302c03107004140310032a464504058120214000c0140322070701c414242212900044d90b82e055440d0040d00303102e000400715003640c50038868901c6254010f450990345e540d44810080080030300e403181542030b00800000c104540f4000c11414140142900c0f116000d455241e2070b18081c111001d0450140400c480000004c0b110a0015108a010710380b80e05080c4a204c1d81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 418876285 1250 418875035 418875047
    0xb0403030b180118060914041712060f0d12080601020c0d03200106122004230901020d05070206040201080603070f0b0c070305030c07030c0e010e07050c0c1f 69
    0x840588103000b040b007500c101e110b0304440203045940700700c1c07044580f443c9540820003c01c2c03980c001c081d0381820042c800c1000071070302c0354480c001c0307220790086d210b14a29a4107006180c0074072452658035a2034100811a00c2ca480e141341c0019442c01040728080c10019a200c07410403502511100201d1002410031841d981c05100000107104140c070700c00704868040d5801045003107480040041906a4203903050220030942c0072002504540d200b0686502590600c00360039500a06404070480005442c1010360400d8000c030462000c42c0c44465410355980c4141c0c950002e40180491529036090142c811032401c0c1d805401c0c004c00d00c87c2c010301318900f03150000600b001e80040c48035019900903041044030111403454942111002906907840f030381206152428508640d2000c0c12610010406000ca04404502ca204513485010809109640e0300c1070107481c00170912848040d00308070800141464095401001c00d2490541a2100c12000c03900042d14030842c0705103046040e03c646400e4243d00c1e0454 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 418877535 1250 418876285 418876301
    0x1b070608060328030905100e090108070e07051b1902040c2d0c0f060c020708010c020a020618040911010306050609100c080d06030b0a050c13090203150306040b040303 73
    0x1801601180204003640c1e80d002c0300f0000084541c04401104505261140c81400b01034000200f07851801040b40030014464403030021007500c1601f09038000280c20400083c81d40031103012141004030b170307940c41070180d80342d800140031800c42201c030700071b003c91104003440044d801401010040940000c240180403c440c0030b0304074503092007680c06000343d0314aa1224580340e80e02c2c965a49a07480c2c00f4900c412107503607081c040000c1960682600e00c0040140b00c1d0003c981000f41582140c98055071080b43e05c1c240e400c054200800360b00119503810240c10f00d10003c0003600d640092a000ca40701c4a0046421503940c401d040d904544043c002403120340c2d06010b41d40041000311003a034205247c0a0024015404030803031071052029a4202c101001000000c1d60500c03038500804020071551380c10f016049010454041c50442d1518000400000c06201a40d0f1005030014814401c1410840701030025400034000e003c80554006028910b41d900b0400d80340710314465503490019081a140c0501560160 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 418878785 1250 418877535 418877539
    0x406050d0f15030b09100609050a0c140702010f030b1c020306070201090804090b011e02100c050a05030a050c1621080121110d06050f0a02032404021b07060806 70
    0x4540d902c1403010102c6070300820303250803540032942902c038229158030b0800b0044c081c2c0e00e04e038104400040d0b5030b2103603440703c1e10400901d0b909209a2140401c11190702d180344480151034035040c0f01c034030f015500c540c901e082005418280003800848100024021840700c0555074004014043c4003411420144449038212001d400284034010265072904070500807409503c525903501c55000c6480c2e03102d0f001812b403024145800c000b401c0c11072200203448044200b00d00f091142040c0e80214128400c0007200c00c528600e6460034110b0f19444145005000040c008040c0d1201c24001c490b00b1141d42d44071419014415a40001010b401e003040e81a0200c182c1d1500040c0110709004110f091111910141c002e5980c0f44411003c12007890112000200d048020f41c00400b82440c0348101700341c5601c594080c080788061071000d0b585240c140301c240d1004440b40c401d201101150142c1194260710314808001004202604019101c54003c0c8030b146000c4503512030341e00849041100a41040e2019000300701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 418880035 1250 418878785 418878791
    0x1b0e031509103804150b0309071505030c0d0b0604080f010b0d0507150c0b01140108061f0c111e09010f0b0403110127170705030c01080403050f0406050d0f 68
    0x40807400448218080c00c1c200320301c22030050f0524050340c450784001c8012401c4200d18402c503485801c0c00304607410490303100d170051207000008100e001519602510450159545074550750315190540001e40050403501070090f240c11842520759201405031002d4641d5000901080000f1000642518072090300c0500940d07041a03181c01090300825030b4020307100c0440000c841140620b0301210380900ca60310260452008034008035681c3c1501032640000d003801d981d0617030a03490701001c001b0b0310500701d0f040c00d0b010b001c03013100c24900a00800d44614024042d03c8034641c20841c82010901c0409440c5a541d80201070781c0300c80301d0501c0c1c0030b06514003400c51010108202400c1c08070210151059000c09804801c81c0c19140303c541e0b218180c2405c103181032080c0144403003120700e850400da6406025221608035081c0442c3c1400c40001001c000300da90040060172040440760065660501c0580182c0401904000848001608a0060000700402c1c1c3d10507036a0050b50078440220f510082d180400350341 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 418881285 1250 418880035 418880081
    0x80a120e0a06200d090303140624071505010302010809060903040b0d020d0f06080706030b0604140d08030403080103031b150b0102240a050105041b0e03150910 70
    0x9000072032645807540310000252201e03000790380700c207421104030410b440000006000c1e4035000841d040814240e200b40c0303007444600150390351498a80c5e400c958443e0410719481c0d4100f00701186c0700c80c1611003400b5520f16460030101c0c0d10348002420b0304104030740c02d00b03450304010000c650b4803c580a5204c41480090111b901700008083c6d103034441e900c18080050030200b07845105080c00c0d41120001060500200b1140346461942c902801062207000524081c600c1c0c00101203002e8000e039884031070001d24403450982040d54a104036035000c8035082c0c014034021005c2c0c0000f06202e000318000c6019480f10403142d8903526009104600f0440100c4a010b02c00b14400002020420240b296107910340703000c0703821924880101e10b0000b5848060003041c00c0351600c1da51091180419138007a807113080052200daa00c42040c4400d540c1c1d2480410b610b98000e0100c030804a10452417034174407840080030b46110b600d11140d42d000f00c0b182500c10899540040c1c0d01c2d5003040b91540b04d40d0844400780301032031104032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 418882535 1250 418881285 418881311
    0x12040f0611030703030c02012d1b020709020d2c06010617010608070c0602040b0a110c0307120c030501020712031a2803120917072106020702040603080a12 68
    0x1003c0c03a2001014540c43c0c034001ca020a00039000384041c0d0a0b001ca0004180c0c0340d00f010602c1c000701541c40001c8943c41c011800d078001081c40c4607814601010b4009000d140c0c58100500c0c000e50020a2080b10907989240d9040507850410414004002010b100704000b10071580103410070780103078404018002c07030034001511010001c070602e04590700303070910088030755484009645003a01200c1c0200101d100003008600d09040e036006c1c06000303045940b03400f1241c0381040c103e07641d0408131140c25410344c017040f030411a0380c00d0004108103c80c0f148849001480c6d42343d0b40c1d142a40c00042007150700126091141e142540d05101d8606122441490800301840078030105a40210760401c0d2004504070a03c08546250750340801d500860340080c00d401500222017000b0f140fa062409100d01280c1385d407040c5028901d00150300c2d03081d40d0544030002800c814089440600c1e80800004842d0b80d9000d010103009a5503034070440005600412406a48000b149001080305a5451074413605070726282d034802c00c203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 418883785 1250 418882535 418882537
    0x5090d020919050a020d110325050c0304060906030b0f1003051b180a050105040e01090209181501030b12063108040801050109141f0812040f061103 65
    0x1940c040c0e9850100352034001045846068280318001c0c1da9040400380070300400640d00070001a810b40d1010028801200010b56262106545512450107084881c41c1d07901c148480600d282241401d1192401c100b020b0442d003142c109a1212000c1420b2030010800590035000c2d040181c001120762001e03032201c8100051001e5400702102d41019900c4001030128070040c032400800b28001d0300c5088c0c89200c0c0c1c6602080c0a50b043d08a10b00030050200c0004883d40107206a4042c1c1c1c2c400c050b64078061f0b00744006070000350000d207070f601c2e81300b1825a000080c000d01c45540c07a0203440e280300e0260746411002c0c0003506490140f81c00c94000c000c0c8405030746d0b510001040042e0403640c2101b42d0345001d440b169078584095030700b900389007030ba80240445904000000d40208103c500c000001e110710307a660740440d000c840c0f072020780802e880902c4002854031081c11110a40340703400400c0f003064040d20b0307518880c0340c13003128080b4034400b050000f000e2124645c20112200144068902a00604503040840ea26 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 418884892 1107 418883785 418883809
    0x6020702040605030c03030304032304150f050c0309040b1305070c12031b180801020408010c020c030111040605031302131406010e0f060a051204140d0509 68
    0xb43e03814042200c49143e0b00c010b028506682e02c0c0e480c1078904039080305e4607000350202c942d0045045901c40c400742025100a10b0003191085906002406011254911034107020003071142e60075101b000002c45442000645010600c8507029000c5005902109c4640300010305201c100300d0300551000441401d14000c254180e03012862150503422101c0301902881c410701196903a106441c09140c000d441c8214070f26200058a40c0c2d208500e00b240c116401c080341c1c0765140c4415645040d410065540c1c02c2204500070031004200d08000e840d540302ea407240605021010000800c01c0095158121740c50344c014080540058a08500310024401521454040e1404102280e1107501c10138a410703010a0280c070700509017240b0301c10090b4a0308010160410040200954215600340d0b8290900492080b41c0070307449180041200d074201911070015608000050046440380c0e40c6403030700b10003 = true := by decide +kernel

theorem cover : BRFrame.Cov 418705035 418884892 := by
  have h0 := BRFrame.cov_init 418705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 418705035 ≤ n) (h2 : n < 418884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
