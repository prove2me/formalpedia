-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.divided_power_zero_one_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:06:13.716879+00:00
-- url     : https://prove2.me/submissions/9ad875c3-b01e-444f-950b-5a1de95d9d30

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_rowGen_X
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_coeff_lin
import Theorems.Thm_Formalism_CohomologicalDescent_LD_generator_zero_one_det
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
theorem _root_.solution (w y i k : ℕ) (h : y + i ≤ w) :
    rowDiv ℤ 0 1 k (vec2 w y i) = (i.choose k : ℤ) • vec2 w y (i - k) := by
  have h00 : rowGen ℤ 0 1 (X ((0 : Fin 2), (0 : Fin 2))) = Polynomial.C (X (0, 0)) := by
    rw [ld_rowGen_X]; simp
  have h10 : rowGen ℤ 0 1 (X ((1 : Fin 2), (0 : Fin 2))) =
      Polynomial.C (X (1, 0)) + Polynomial.X * Polynomial.C (X (0, 0)) := by
    rw [ld_rowGen_X]; simp
  rw [rowDiv, rank_two_vector_def, map_mul, map_mul, map_pow, map_pow, map_pow, h00, h10, generator_zero_one_det,
    ← map_pow, ← map_pow, mul_comm (Polynomial.C _), mul_assoc, ← map_mul, ld_coeff_lin, rank_two_vector_def,
    zsmul_eq_mul, Int.cast_natCast]
  rcases Nat.lt_or_ge i k with hki | hki
  · rw [Nat.choose_eq_zero_of_lt hki]
    simp
  · have e1 : w - y - (i - k) = (w - y - i) + k := by omega
    rw [e1, pow_add]
    ring
end Formalism.CohomologicalDescent.LD
