-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.detMulEqSumAdjugate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:36.547866+00:00
-- url     : https://prove2.me/submissions/375866bf-3b18-44d6-9e04-4607217fd576

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.DetMulEqSumAdjugate := by
  intro R _ r T s a
  calc T.det * s a = Matrix.mulVec (T.det • (1 : Matrix (Fin r) (Fin r) R)) s a := by
        first
          | (rw [Matrix.smul_mulVec, Matrix.one_mulVec]; rfl)
          | (rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)
          | simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.smul_apply]
    _ = Matrix.mulVec (T.adjugate * T) s a := by rw [Matrix.adjugate_mul]
    _ = Matrix.mulVec T.adjugate (Matrix.mulVec T s) a := by rw [Matrix.mulVec_mulVec]
    _ = ∑ l, Matrix.mulVec T s l * T.adjugate a l := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end Formalism.CountingSumsFrames.Top
