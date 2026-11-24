-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:59.282794+00:00
-- url     : https://prove2.me/submissions/0f619adf-7a2e-4272-8ea5-c19a868f35c7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
variable {n : Type*} [Fintype n]
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution (H : Matrix n n ℂ) (c : ℂ) (a w : n → ℂ) : herm H (c • a) w = c * herm H a w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
end Formalism.FourierDecayAlt.P.HermitianProjections
