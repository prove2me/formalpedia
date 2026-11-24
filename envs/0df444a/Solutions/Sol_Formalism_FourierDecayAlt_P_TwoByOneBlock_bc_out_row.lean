-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.bc_out_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:50.598468+00:00
-- url     : https://prove2.me/submissions/09389f80-1486-4a95-9b92-806ab13fe86a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_mid_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_out_col

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (c : Fin r → ℂ) (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : ¬ mid k r i) : bigCell k r c μ i j = bigCell k r c ν i j := by
  by_cases hj : mid k r j
  · rw [bc_mid_col c μ i j hj, bc_mid_col c ν i j hj, dif_neg hi, dif_neg hi]
  · exact bc_out_col c μ ν i j hj
end Formalism.FourierDecayAlt.P.TwoByOneBlock
