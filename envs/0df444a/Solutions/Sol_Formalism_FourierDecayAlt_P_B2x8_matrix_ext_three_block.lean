-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.matrix_ext_three_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:43.13242+00:00
-- url     : https://prove2.me/submissions/c6643ac9-8cf8-4e1c-be3e-9086d8524bf0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta

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
theorem _root_.solution {A B : Mat k (1 + r')} (h : ∀ a y b, A *ᵥ mk3 k r' a y b = B *ᵥ mk3 k r' a y b) : A = B := by
  have h' : ∀ u, A *ᵥ u = B *ᵥ u := fun u => by rw [← three_block_eta u]; exact h _ _ _
  ext i j
  have := congrFun (h' (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
end Formalism.FourierDecayAlt.P.B2x8
