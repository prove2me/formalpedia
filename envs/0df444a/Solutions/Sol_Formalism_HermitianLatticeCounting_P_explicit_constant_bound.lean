-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.explicit_constant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:44.273524+00:00
-- url     : https://prove2.me/submissions/ecb4388f-f480-44be-bbc7-e68c5f280d5f

import Definitions.Def_Formalism_FlagUnipotentLattices_BlockDistFromLows
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnAndSetIntegralEqZeroOfIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Finset MeasureTheory Filter Topology TensorProduct
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ExplicitC := by
  intro n q h hn hq0 hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set s := Real.sqrt q with hs
  set σ := Real.sqrt (n : ℝ) with hσ
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have σ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have s2 : s ^ 2 = q := Real.sq_sqrt hq0
  have σ2 : σ ^ 2 = n := Real.sq_sqrt (by linarith)
  have σ1 : 1 ≤ σ := by
    rw [hσ]; exact Real.one_le_sqrt.2 (by linarith)
  have σn : σ ≤ n := by nlinarith
  have hsσ : s ≤ 5 / 7 * σ := by
    by_contra hc
    push Not at hc
    have := pow_lt_pow_left₀ hc (by positivity) (two_ne_zero)
    nlinarith
  have hdiv : (((n ^ 2 / 2 + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ 2 / 2 + 1 := by
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := n ^ 2) (n := 2)
    push_cast at this
    linarith
  have n2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hdiv s0]
  · nlinarith [mul_le_mul_of_nonneg_left σn n2]
  · intro hh
    have A : (n : ℝ) ^ 2 * s ≤ 5 / 7 * ((n : ℝ) ^ 2 * σ) := by nlinarith [mul_le_mul_of_nonneg_left hsσ n2]
    have B : 0 ≤ (n : ℝ) ^ 2 * σ := by positivity
    have C : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * σ := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · have : (n : ℝ) * (q * s) ≤ (n : ℝ) ^ 2 / 2 * s := by
        have : (n : ℝ) * q ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this s0]
      nlinarith
    · have h2 : (2 : ℝ) * s ≤ (n : ℝ) ^ 2 / 2 * s := by nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 by nlinarith) s0]
      have h3 : ((n : ℝ) - 1) * q ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
      nlinarith
    · nlinarith
end Formalism.HermitianLatticeCounting.P
