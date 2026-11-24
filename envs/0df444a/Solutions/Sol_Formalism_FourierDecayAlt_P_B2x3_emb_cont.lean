-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.emb_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:25.355229+00:00
-- url     : https://prove2.me/submissions/22fef78f-4599-4c01-9337-3fad969f6c6d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_eq

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution : Continuous fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r) := by
  have : (fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) =
      fun x => (Em k r * Matrix.of x * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) : Mat k r) := by
    funext x
    rw [emb_eq]
  rw [this]
  exact (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const).add
    continuous_const
end Formalism.FourierDecayAlt.P.B2x3
