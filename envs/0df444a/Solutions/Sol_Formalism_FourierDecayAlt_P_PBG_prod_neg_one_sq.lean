-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.prod_neg_one_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:22.32442+00:00
-- url     : https://prove2.me/submissions/90210cce-c0da-47e1-872c-3dcd03535f48

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (m : ℕ) : (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [← mul_pow]
  norm_num
end Formalism.FourierDecayAlt.P.PBG
