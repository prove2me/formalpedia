-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B2.theoremAOfAfter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:51.43074+00:00
-- url     : https://prove2.me/submissions/f5fc2d2e-f29b-407b-94d7-1e5160855811

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_afterOfOld

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
theorem _root_.solution : TC.TheoremAOfAfter := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', hC⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hK hf hΘ hC' hr hS hG hKer hWd hA2 hA13 hEW hP hEL hEB hLS hEE
    hCut hA4
  obtain ⟨hKr, hEb, -, hDA⟩ := B1.afterOfOld E W D hKer hA13
  exact hC E W D Θ jn H Vt c hK hf hΘ hC' hr hS hG hKr hWd hA2 hEb hDA hEW hP hEL hEB hLS hEE hCut hA4
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
