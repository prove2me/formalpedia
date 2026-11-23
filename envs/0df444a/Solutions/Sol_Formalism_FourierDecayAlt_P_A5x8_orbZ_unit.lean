-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.orbZ_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:54.82592+00:00
-- url     : https://prove2.me/submissions/49acde7f-d356-4013-bfc6-8362e7ed2314

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_orbZ_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_pt_det_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    IsUnit (orbZ w p).det := by
  rw [A5x6.orbZ_det]; exact A5x6.pt_det_isUnit w
end Formalism.FourierDecayAlt.P.A5x8
