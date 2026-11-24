-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.lev_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:07:17.056903+00:00
-- url     : https://prove2.me/submissions/6a096743-2094-4c98-a6e5-924be6abddfe

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (g : Mat k r') (i j : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  have hi := i.isLt
  have hj := j.isLt
  unfold ιLev levPos
  rw [dif_pos (show 1 ≤ i.val + 1 ∧ i.val + 1 < 2 * r' + k + 1 + 1 by omega),
    dif_pos (show 1 ≤ j.val + 1 ∧ j.val + 1 < 2 * r' + k + 1 + 1 by omega)]
  congr 1 <;> exact Fin.ext (by simp)
end Formalism.FourierDecayAlt.P.B2x9
