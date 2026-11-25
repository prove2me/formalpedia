-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.phiSupport_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:32.921162+00:00
-- url     : https://prove2.me/submissions/74a11875-dd17-4fd9-a1ca-fc97297c0aa7

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_gaXi_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_DjU_gaXi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) : PhiSupport := by
  intro k p s ρ σ d z z' E _ _ F₁ A₁ B₁ Q K hd hS Z hZ hK γ hγ
  have key : ∀ ξ : Xi k p s ρ σ, F₁ (gaXi k ρ σ d ξ Z γ) = 0 := by
    intro ξ
    by_contra hne
    have := hS.2.1 _ (gaXi_mem hM hR σ d hd ξ Z hZ hγ) hne
    rw [DjU_gaXi hZh] at this
    exact hK this
  unfold PhiFun
  simp [key]
end Formalism.FourierDecayAlt.P.Ux10
