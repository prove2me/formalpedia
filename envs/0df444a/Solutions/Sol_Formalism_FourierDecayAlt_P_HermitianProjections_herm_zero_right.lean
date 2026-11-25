-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:38:20.208905+00:00
-- url     : https://prove2.me/submissions/193a647b-081b-48d9-a16d-f44f6e0698f2

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
theorem _root_.solution (H : Matrix n n ℂ) (v : n → ℂ) : herm H v 0 = 0 := by
  simp only [herm, star_zero, zero_dotProduct]
end Formalism.FourierDecayAlt.P.HermitianProjections
