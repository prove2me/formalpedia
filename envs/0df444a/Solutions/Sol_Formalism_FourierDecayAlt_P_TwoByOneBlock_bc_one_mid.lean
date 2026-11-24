-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.bc_one_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:49.882485+00:00
-- url     : https://prove2.me/submissions/829885f4-b86e-4c54-b9ac-7c94a258e1f8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_mid_col

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
theorem _root_.solution (c : Fin r → ℂ) (i j : Fin (2 * r + k + 1)) (hi : mid k r i) (hj : mid k r j) :
    bigCell k r c 1 i j = if i = j then 1 else 0 := by
  rw [bc_mid_col c 1 i j hj, dif_pos hi, Matrix.one_apply]
  have h1 := hi
  have h2 := hj
  simp only [Fin.ext_iff]
  by_cases h : i.val = j.val
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
