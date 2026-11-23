-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.averaged_kernel_periodic_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:24.983788+00:00
-- url     : https://prove2.me/submissions/ff16e0a6-8700-4b05-8695-05f9b2f9652b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_thx_periodic
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_thx_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open AveragedKernelSums
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.ThxBasic := by
  intro hCut hKG hN1 hMM K _ _ _ R ψ hL m n₀ F A B τ cr hF hcr hB
  exact ⟨fun z r hr => thx_periodic hL m A B τ cr hB z r hr, fun z =>
    thx_psd (fun F' hF' m cr hcr => (hCut hKG hN1 hMM K R ψ hL m cr Set.univ F' hcr hF').1)
      m n₀ F A B τ cr hF hcr z⟩
end Formalism.FourierDecayAlt.P
