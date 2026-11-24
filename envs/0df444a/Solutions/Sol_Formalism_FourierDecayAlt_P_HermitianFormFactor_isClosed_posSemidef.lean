-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.isClosed_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:19:50.92283+00:00
-- url     : https://prove2.me/submissions/7aea0786-aa5d-46b6-801f-90349806f563

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : IsClosed {T : Q → Q → ℂ | (Matrix.of T).PosSemidef} := by
  have : {T : Q → Q → ℂ | (Matrix.of T).PosSemidef} =
      {T : Q → Q → ℂ | (Matrix.of T)ᴴ = Matrix.of T} ∩ ⋂ x : Q → ℂ, {T : Q → Q → ℂ | 0 ≤ star x ⬝ᵥ (Matrix.of T *ᵥ x)} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Matrix.posSemidef_iff_dotProduct_mulVec
  rw [this]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq (Continuous.matrix_conjTranspose (continuous_id (X := Matrix Q Q ℂ))) continuous_id
  · refine isClosed_le continuous_const ?_
    exact Continuous.dotProduct continuous_const
      (Continuous.matrix_mulVec (continuous_id (X := Matrix Q Q ℂ)) continuous_const)
end Formalism.FourierDecayAlt.P.HermitianFormFactor
