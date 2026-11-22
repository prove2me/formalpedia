-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx1.star_sc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:00.266371+00:00
-- url     : https://prove2.me/submissions/aeb215d6-4c00-44aa-9c25-0e4b396ec8c0

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx1
namespace Formalism.FourierDecayAlt.P.Mx1
theorem _root_.solution (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
end Formalism.FourierDecayAlt.P.Mx1
