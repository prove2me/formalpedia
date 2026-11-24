-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:40.41779+00:00
-- url     : https://prove2.me/submissions/579d1fe6-8a70-4aa6-9740-b189d4e693da

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
theorem _root_.solution (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a - b) = herm H v a - herm H v b := by
  simp only [herm, star_sub, sub_dotProduct]
end Formalism.FourierDecayAlt.P.HermitianProjections
