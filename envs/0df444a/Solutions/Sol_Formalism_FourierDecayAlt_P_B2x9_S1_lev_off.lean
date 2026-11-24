-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.S1.lev_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:59.754504+00:00
-- url     : https://prove2.me/submissions/2a066eb6-3a16-42fd-9263-f12d12ca9cf5

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9 Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9.S1
theorem _root_.solution (g : Mat k r') (m : Fin (2 * (1 + r') + k + 1)) (hm : m ∉ Set.range (levPos k 1 r'))
    (j : Fin (2 * r' + k + 1)) : ιLev k 1 r' g m (levPos k 1 r' j) = 0 := by
  unfold ιLev
  have hp : ¬ (1 ≤ m.val ∧ m.val < 2 * r' + k + 1 + 1) := by
    rintro ⟨h1, h2⟩
    exact hm ⟨⟨m.val - 1, by omega⟩, Fin.ext (show m.val - 1 + 1 = m.val by omega)⟩
  rw [dif_neg hp, if_neg]
  intro h
  exact hm ⟨j, h.symm⟩
end Formalism.FourierDecayAlt.P.B2x9.S1
