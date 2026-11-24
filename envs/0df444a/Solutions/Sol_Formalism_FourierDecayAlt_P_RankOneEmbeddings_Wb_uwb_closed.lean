-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb.uwb_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:24:56.141295+00:00
-- url     : https://prove2.me/submissions/312eaf4b-3661-4f9a-b517-09e189196af2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
theorem _root_.solution : IsClosed (UWb k r) := by
  have hc : ∀ v : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Mat k r => g *ᵥ v := fun v => by
    first
      | fun_prop
      | exact continuous_id.matrix_mulVec continuous_const
  unfold UWb GV UH
  rw [Set.setOf_and]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.setOf_mem_eq]
    refine isClosed_eq ?_ continuous_const
    first
      | fun_prop
      | exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · rw [Set.setOf_forall]
    refine isClosed_iInter fun a => ?_
    rw [Set.setOf_and]
    exact (isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
