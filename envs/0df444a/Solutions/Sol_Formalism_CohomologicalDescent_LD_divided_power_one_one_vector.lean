-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.divided_power_one_one_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:25.629657+00:00
-- url     : https://prove2.me/submissions/12890399-ae8b-425e-91f8-4294c72ac410

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_rowGen_X
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_coeff_one
import Theorems.Thm_Formalism_CohomologicalDescent_LD_generator_one_one_det
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
    rowDiv ℤ 1 1 k (vec2 w y i) = ((i + y).choose k : ℤ) • vec2 w y i := by
  have h00 : rowGen ℤ 1 1 (X ((0 : Fin 2), (0 : Fin 2))) = Polynomial.C (X (0, 0)) := by
    rw [ld_rowGen_X]; simp
  have h10 : rowGen ℤ 1 1 (X ((1 : Fin 2), (0 : Fin 2))) =
      (1 + Polynomial.X) * Polynomial.C (X (1, 0)) := by
    rw [ld_rowGen_X]; simp <;> ring
  have e : rowGen ℤ 1 1 (vec2 w y i) = (1 + Polynomial.X) ^ (i + y) * Polynomial.C (vec2 w y i) := by
    rw [rank_two_vector_def, map_mul, map_mul, map_pow, map_pow, map_pow, h00, h10, generator_one_one_det]
    simp only [map_mul, map_pow, mul_pow, pow_add]
    ring
  rw [rowDiv, e, ld_coeff_one, zsmul_eq_mul, Int.cast_natCast]
end Formalism.CohomologicalDescent.LD
