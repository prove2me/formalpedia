-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.euler_product_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:05.38185+00:00
-- url     : https://prove2.me/submissions/ddf2c1df-afe0-4ca2-a7d5-296bed3b35a7

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 1 / 3) (k : ℕ) :
    1 - 3 / 2 * x + 3 / 2 * x ^ (k + 1) ≤ ∏ i ∈ Icc 1 k, (1 - x ^ i) ∧
      ∏ i ∈ Icc 1 k, (1 - x ^ i) ≤ 1 := by
  induction k with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num), Finset.prod_empty]
    refine ⟨?_, le_refl _⟩
    norm_num
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hx1 : x ≤ 1 := by linarith
    have hy : x ^ (n + 1) ≤ x := pow_le_of_le_one hx0.le hx1 (Nat.succ_ne_zero n)
    have hy0 : 0 ≤ x ^ (n + 1) := pow_nonneg hx0.le _
    have hyx : x ^ (n + 1 + 1) = x ^ (n + 1) * x := pow_succ x (n + 1)
    have hP0 : 0 ≤ ∏ i ∈ Icc 1 n, (1 - x ^ i) := by linarith
    constructor
    · have e1 := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 1 - x ^ (n + 1) by linarith)
      have e2 := mul_nonneg hy0 (show (0:ℝ) ≤ 1 / 3 - x ^ (n + 1) by linarith)
      rw [hyx]
      nlinarith [e1, e2]
    · have e3 := mul_le_mul h2 (show 1 - x ^ (n + 1) ≤ 1 by linarith) (by linarith) zero_le_one
      linarith
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
