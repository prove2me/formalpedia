-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FixedPointsGramVector.gnB_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:20.434934+00:00
-- url     : https://prove2.me/submissions/c468895b-63d5-44a0-a97a-3e7e0585e1e7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FixedPointsGramVector
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    gnB k r z z' γ *ᵥ c = ∑ i, c i • gramVec k r z z' γ i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, gnB, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
end Formalism.FourierDecayAlt.P.FixedPointsGramVector
