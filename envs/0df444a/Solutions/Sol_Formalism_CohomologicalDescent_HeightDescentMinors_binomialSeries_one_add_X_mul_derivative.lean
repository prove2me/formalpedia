-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeries_one_add_X_mul_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:19.056186+00:00
-- url     : https://prove2.me/submissions/854ebf7d-18f2-4c97-a0b5-c29292aa7476

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_one_add_X_mul_derivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {R : Type*} [CommRing R]
variable [BinomialRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (c : R) :
    (1 + X) * d⁄dX R (binomialSeries R c) = C c * binomialSeries R c := by
  ext n
  rw [coeff_one_add_X_mul_derivative, coeff_C_mul]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  have h := Ring.choose_smul_choose c (Nat.le_succ n)
  rw [Nat.choose_succ_self_right, Nat.succ_sub (le_refl n), Nat.sub_self, Ring.choose_one_right,
    nsmul_eq_mul] at h
  push_cast at h
  linear_combination h
end Formalism.CohomologicalDescent.HeightDescentMinors
