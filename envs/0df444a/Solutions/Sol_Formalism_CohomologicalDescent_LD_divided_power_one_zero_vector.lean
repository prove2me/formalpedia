-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.divided_power_one_zero_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:18.770418+00:00
-- url     : https://prove2.me/submissions/98a839da-13b8-48b2-932c-51c7905d36b0

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_rowGen_X
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_coeff_lin
import Theorems.Thm_Formalism_CohomologicalDescent_LD_generator_one_zero_det
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (w y i k : ℕ) :
    rowDiv ℤ 1 0 k (vec2 w y i) = ((w - y - i).choose k : ℤ) • vec2 w y (i + k) := by
  have h00 : rowGen ℤ 1 0 (X ((0 : Fin 2), (0 : Fin 2))) =
      Polynomial.C (X (0, 0)) + Polynomial.X * Polynomial.C (X (1, 0)) := by
    rw [ld_rowGen_X]; simp
  have h10 : rowGen ℤ 1 0 (X ((1 : Fin 2), (0 : Fin 2))) = Polynomial.C (X (1, 0)) := by
    rw [ld_rowGen_X]; simp
  rw [rowDiv, rank_two_vector_def, map_mul, map_mul, map_pow, map_pow, map_pow, h00, h10, generator_one_zero_det,
    ← map_pow, ← map_pow, mul_assoc, ← map_mul, ld_coeff_lin, rank_two_vector_def, zsmul_eq_mul,
    Int.cast_natCast, pow_add, show w - y - i - k = w - y - (i + k) by omega]
  ring
end Formalism.CohomologicalDescent.LD
