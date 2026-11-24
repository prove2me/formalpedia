-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.determinant_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:36:35.660333+00:00
-- url     : https://prove2.me/submissions/df79778d-9b8e-4533-9351-ab97104d80a1

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.DetNonzero := by
  intro k r z z' hz hz' g hG hdet
  have hD : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have h1 : Complex.normSq (Dmin k r z z' g (Fin.last (r + 1))) = 0 := by
    rw [hD, hdet, map_zero]
  unfold Gf at hG
  rw [h1] at hG
  have h2 := mul_nonneg (mul_nonneg hz.2.le hz'.2.le)
    (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))
  linarith
end Formalism.FourierDecayAlt.P
