-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.first_level_of_equality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:44.923998+00:00
-- url     : https://prove2.me/submissions/3714cd31-767f-41d1-88e9-46b47c14f393

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses

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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (h : SingleBlockThetaProps) : A13 1 := by
  unfold A13 ThetaExists
  unfold SingleBlockThetaProps at h
  intro K _ _ _ R ψ hLD _ m F hF
  obtain ⟨Θ, -, -, h3⟩ := h K R ψ hLD m
  exact ⟨Θ, h3 F hF⟩
end Formalism.FourierDecayAlt.P.A5x6
