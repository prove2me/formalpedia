-- Prove2me | solution 1 for Formalism.L2.Th1.F.sgStarQuasi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:09.11425+00:00
-- url     : https://prove2.me/submissions/36f50ab7-d2d1-48d5-8b47-36e77b394e6a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar

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
theorem _root_.solution (hq : SigmaQuasi) (he : EtaSplit) : SgStarQuasi := by
  intro L ω z hω
  simp only [sgStar]
  rw [hq L ω z hω, he L ω]
  have key : Complex.exp ((s2 L * ω + ((Real.pi : ℂ) / (area L : ℂ)) * conj ω) * (z + ω / 2))
        * Complex.exp (-(s2 L) * (z + ω) ^ 2 / 2)
      = Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(s2 L) * z ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [herm]
    ring
  linear_combination (semiChar L ω * wSigma L z) * key
end Formalism.L2.Th1.F
