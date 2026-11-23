-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.J1.t_RecHypAfterOfOld
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:04.152829+00:00
-- url     : https://prove2.me/submissions/5229b5a3-049c-4135-b48b-5c83b7a9df7b

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

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
theorem _root_.solution : RecHypAfterOfOld := by
  intro hAO E W _ D C₁ C₄ Θ jn H _ _ Vt c hR
  obtain ⟨h1, h2, h3, h4, h5, hKer, h7, h8, hA13, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hR
  obtain ⟨hKr, hEb, -, hDA⟩ := hAO E W D hKer hA13
  unfold RecHypAfter
  exact ⟨h1, h2, h3, h4, h5, hKr, h7, h8, hEb, hDA, h10, h11, h12, h13, h14, h15, h16, h17⟩
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
