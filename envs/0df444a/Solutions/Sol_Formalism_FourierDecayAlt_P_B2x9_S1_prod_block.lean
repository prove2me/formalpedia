-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.S1.prod_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:07.173678+00:00
-- url     : https://prove2.me/submissions/f4e05fb1-e651-46c9-afd0-d57cb09c5cdf

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_heis_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_lev_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_lev_off

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
theorem _root_.solution (x : HPar k r') (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    (heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (levPos k 1 r' i)]
  · rw [heis_block, if_pos rfl, one_mul, lev_block]
  · intro m _ hm
    by_cases hr : m ∈ Set.range (levPos k 1 r')
    · obtain ⟨l, rfl⟩ := hr
      rw [heis_block, if_neg (fun h => hm (by rw [h])), zero_mul]
    · rw [lev_off g m hr, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.B2x9.S1
