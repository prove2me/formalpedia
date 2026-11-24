-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.eq_three_block_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:24:53.387371+00:00
-- url     : https://prove2.me/submissions/f3d213b7-b26a-459e-a601-eabbfccd7adf

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_middle
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_ext

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {u : Fin (2 * (1 + r') + k + 1) → ℂ} {a b : ℂ} {y : Fin (2 * r' + k + 1) → ℂ}
    (h1 : u (tkF k r') = a) (h2 : ∀ j, u (levPos k 1 r' j) = y j) (h3 : u (tkL k r') = b) : u = mk3 k r' a y b := by
  apply three_block_ext
  · rw [h1]; exact (three_block_first a y b).symm
  · intro j; rw [h2]; exact (congrFun (three_block_middle a y b) j).symm
  · rw [h3]; exact (three_block_last a y b).symm
end Formalism.FourierDecayAlt.P.B2x8
