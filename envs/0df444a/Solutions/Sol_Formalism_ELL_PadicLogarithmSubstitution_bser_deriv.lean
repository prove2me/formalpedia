-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.bser_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:36.758659+00:00
-- url     : https://prove2.me/submissions/b7d1d4d4-76c5-4dca-8fb2-b37f24928b7a

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_choose_rec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution (b : ℤ_[p]) :
    (1 + X) * derivative K (bser p K b) = phi p K b • bser p K b := by
  ext n
  have hr := congrArg (phi p K) (choose_rec p b n)
  simp only [map_mul, map_sub, map_natCast] at hr
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_smul]
  rcases n with _ | m
  · simp only [bser, coeff_mk, coeff_zero_X_mul, smul_eq_mul] at hr ⊢
    push_cast at hr ⊢
    linear_combination hr
  · rw [coeff_succ_X_mul, coeff_derivative]
    simp only [bser, coeff_mk, smul_eq_mul] at hr ⊢
    push_cast at hr ⊢
    linear_combination hr
end Formalism.ELL.PadicLogarithmSubstitution
