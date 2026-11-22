-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.star_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:03.013337+00:00
-- url     : https://prove2.me/submissions/ffc41827-b71a-4b48-9185-b3fa84bb522f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution [StarRing A] (a : S) (i j : Fin 2) :
    star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  ext x y
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  simp only [eU, Matrix.of_apply]
  rw [apply_ite star, star_one, star_zero]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
end Formalism.FourierDecayAlt.P.Wd1
