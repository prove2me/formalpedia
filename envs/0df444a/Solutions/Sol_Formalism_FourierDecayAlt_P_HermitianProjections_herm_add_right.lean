-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:01:00.539364+00:00
-- url     : https://prove2.me/submissions/46685f8d-abbe-4107-a1e7-31ab9e416acb

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
theorem _root_.solution (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a + b) = herm H v a + herm H v b := by
  simp only [herm, star_add, add_dotProduct]
end Formalism.FourierDecayAlt.P.HermitianProjections
