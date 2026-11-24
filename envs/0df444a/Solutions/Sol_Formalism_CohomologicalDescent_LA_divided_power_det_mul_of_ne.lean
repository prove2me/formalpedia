-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.divided_power_det_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:29.385312+00:00
-- url     : https://prove2.me/submissions/a50cfb52-7951-44d0-8b1d-c6b7512586f2

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_row_generator_det_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin r) R) :
    rowDiv R a b k (genericDet R r * f) = genericDet R r * rowDiv R a b k f := by
  unfold rowDiv
  rw [map_mul, row_generator_det_of_ne R a b hab, Polynomial.coeff_C_mul]
end Formalism.CohomologicalDescent.LA
