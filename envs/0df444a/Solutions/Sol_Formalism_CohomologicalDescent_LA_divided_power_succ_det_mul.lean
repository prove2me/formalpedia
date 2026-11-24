-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.divided_power_succ_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:07.488903+00:00
-- url     : https://prove2.me/submissions/ffaef053-b58a-4fd8-a7a6-2f4fabbffa0d

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_row_generator_det_diag

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
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (a : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin r) R) :
    rowDiv R a a (k + 1) (genericDet R r * f) =
      genericDet R r * (rowDiv R a a (k + 1) f + rowDiv R a a k f) := by
  unfold rowDiv
  rw [map_mul, row_generator_det_diag, mul_assoc, Polynomial.coeff_C_mul, add_mul, one_mul,
    Polynomial.coeff_add, Polynomial.coeff_X_mul]
end Formalism.CohomologicalDescent.LA
