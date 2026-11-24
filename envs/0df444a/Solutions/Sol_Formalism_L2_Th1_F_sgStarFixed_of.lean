-- Prove2me | solution 1 for Formalism.L2.Th1.F.sgStarFixed_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:01.434726+00:00
-- url     : https://prove2.me/submissions/c5390986-ab9e-4255-8461-79e3a27af444

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_semiChar_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : SgStarQuasi) : SgStarFixed := by
  intro L ω z hω
  simp only [opU]
  rw [h L ω z hω]
  have key : Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
      * Complex.exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 1 := by
    rw [← Complex.exp_add]
    have : (Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2
        + (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 0 := by ring
    rw [this, Complex.exp_zero]
  linear_combination (semiChar L ω * semiChar L ω * sgStar L z) * key
    + sgStar L z * semiChar_sq L ω
end Formalism.L2.Th1.F
