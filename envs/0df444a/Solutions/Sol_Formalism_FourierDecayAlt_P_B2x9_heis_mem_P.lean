-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.heis_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:44.853748+00:00
-- url     : https://prove2.me/submissions/116593c2-0de8-4544-bfee-178110356227

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_one


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
theorem _root_.solution (hG : ClosedG) (SD : StabDecomp) (x : HPar k r') : heis0 k r' x ∈ P1set k r' := by
  have h1 : (1 : Mat k r') ∈ GV k r' := by
    first
      | exact (hG k r').one_mem
      | exact (hG k r').2.1
      | exact (hG k r').1.1
      | exact (hG k r').one
      | exact (hG k r').2.2.1
  rw [SD k r']
  unfold mulSet Hset
  show ∃ a ∈ Set.range (heis0 k r'), ∃ b ∈ ιLev k 1 r' '' GV k r', heis0 k r' x = a * b
  exact ⟨heis0 k r' x, ⟨x, rfl⟩, ιLev k 1 r' 1, ⟨1, h1, rfl⟩, by rw [lev_one, Matrix.mul_one]⟩
end Formalism.FourierDecayAlt.P.B2x9
