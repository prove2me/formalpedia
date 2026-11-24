-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:33.690794+00:00
-- url     : https://prove2.me/submissions/64150a0b-ca55-466b-9a23-e5774fb0c3e8

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
theorem _root_.solution (H : Matrix n n ℂ) (a b w : n → ℂ) : herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]
end Formalism.FourierDecayAlt.P.HermitianProjections
