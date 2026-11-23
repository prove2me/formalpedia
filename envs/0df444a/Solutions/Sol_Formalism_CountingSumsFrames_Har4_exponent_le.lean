-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:44.721705+00:00
-- url     : https://prove2.me/submissions/90ffbe39-7333-495f-9df0-d0345c516316

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {k A B a p e : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hA : A ≤ 8 * a) (hB : B ≤ 8 * a)
    (he : 3 * (Real.logb p (8 * (a : ℝ) + k - 1) + 1) + 4 * (k : ℝ) * (Real.logb p (8 * (a : ℝ) + k - 1) + 1)
      ≤ (e : ℝ)) : (k + 1) * Nat.log p (A + B + k) ≤ e := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set L := Nat.log p (A + B + k) with hLdef
  set x : ℕ := 8 * a + k - 1 with hxdef
  have hxr : (x : ℝ) = 8 * (a : ℝ) + k - 1 := by
    rw [hxdef, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hxr] at he
  have hLX : (L : ℝ) ≤ Real.logb p x + 1 := by
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · rw [hL0]
      push_cast
      rcases Nat.eq_zero_or_pos x with hx0 | hxpos
      · rw [hx0]
        simp
      · have h0 : (0 : ℝ) ≤ Real.logb p x := Real.logb_nonneg hp1 (by exact_mod_cast hxpos)
        linarith
    · have hN : A + B + k ≠ 0 := by omega
      have hpow : p ^ L ≤ A + B + k := Nat.pow_log_le_self p hN
      have h2 : 2 * p ^ (L - 1) ≤ p ^ L := by
        have e1 : p ^ L = p * p ^ (L - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [e1]
        exact Nat.mul_le_mul_right _ hp.two_le
      have hy : p ^ (L - 1) ≤ x := by omega
      have hyR : ((p ^ (L - 1) : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hy
      have hposR : (0 : ℝ) < ((p ^ (L - 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos _
      have hlog := (Real.logb_le_logb hp1 hposR (lt_of_lt_of_le hposR hyR)).2 hyR
      rw [Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one hp1, mul_one] at hlog
      have e2 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub hLpos]
        simp
      linarith
  have hX1 : 0 ≤ Real.logb p x + 1 := le_trans (Nat.cast_nonneg L) hLX
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hfin : ((k : ℝ) + 1) * (L : ℝ) ≤ (e : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hLX (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 + 3 * (k : ℝ)) hX1]
  exact_mod_cast hfin
end Formalism.CountingSumsFrames.Har4
