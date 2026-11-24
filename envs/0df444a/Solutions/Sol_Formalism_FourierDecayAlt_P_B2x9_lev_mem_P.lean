-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.lev_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:37.687621+00:00
-- url     : https://prove2.me/submissions/204dcd8c-b4b9-430a-96a2-0ce51fb89be6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_heis_zero

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
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (SD : StabDecomp) (g₁ : Mat k r') (h : g₁ ∈ GV k r') : ιLev k 1 r' g₁ ∈ P1set k r' := by
  rw [SD k r']
  unfold mulSet Hset
  show ∃ a ∈ Set.range (heis0 k r'), ∃ b ∈ ιLev k 1 r' '' GV k r', ιLev k 1 r' g₁ = a * b
  exact ⟨1, ⟨(0, 0), heis_zero⟩, ιLev k 1 r' g₁, ⟨g₁, h, rfl⟩, (Matrix.one_mul _).symm⟩
end Formalism.FourierDecayAlt.P.B2x9
