-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.bc_mid_row_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:49.125203+00:00
-- url     : https://prove2.me/submissions/50254fb0-abd7-4046-8508-6bfc3001ccda

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock

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
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : mid k r i) (hj : ¬ mid k r j) : bigCell k r c μ i j = 0 := by
  have h1 := hi
  have hjl := j.isLt
  unfold bigCell
  by_cases hj1 : j.val < r
  · rw [dif_pos hj1, if_neg (by simp only [Fin.ext_iff, esI]; omega)]
  · rw [dif_neg hj1, dif_neg (show ¬ j.val ≤ r + k by omega), if_neg (by omega)]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
