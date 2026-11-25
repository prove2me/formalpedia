-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:06.760057+00:00
-- url     : https://prove2.me/submissions/c95d9037-95a9-4399-9c5c-2e7b10e1f50d

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
theorem _root_.solution (H : Matrix n n ℂ) (w : n → ℂ) : herm H 0 w = 0 := by
  simp only [herm, Matrix.mulVec_zero, dotProduct_zero]
end Formalism.FourierDecayAlt.P.HermitianProjections
