-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.J1.t_RecursionWithDens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:04.454063+00:00
-- url     : https://prove2.me/submissions/2d9c17cb-7ca4-4638-88fd-7df1df87b181

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_J1_t_ProductOfEMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
theorem _root_.solution : RecursionWithDens := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', hC⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c sd hR hC' hr h0 hmax R
  unfold RecHypAfter at hR
  obtain ⟨hK, hf, hΘ, hS, hG, hKr, hWd, hA2, hEb, hDA, hEW, hP, hEL, hEB, hLS, hEE, hCut, hA4⟩ := hR
  have hp := t_ProductOfEMax D.r D.e sd h0 hmax
  have hb := hC E W D Θ jn H Vt c hK hf hΘ hC' hr hS hG hKr hWd hA2 hEb hDA hEW hP hEL hEB hLS hEE
    hCut hA4 R
  rwa [hp] at hb
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
