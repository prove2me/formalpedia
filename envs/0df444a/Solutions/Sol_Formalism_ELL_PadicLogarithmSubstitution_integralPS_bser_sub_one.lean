-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.integralPS_bser_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:13.75601+00:00
-- url     : https://prove2.me/submissions/3a245ee2-b347-43bc-a6e1-b09f6f9cac93

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_norm_phi_le

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
theorem _root_.solution [IsUltrametricDist K] (b : ℤ_[p]) :
    IntegralPS (bser p K b - 1) := by
  intro n
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [bser, coeff_mk]; exact norm_phi_le p K _
  · rw [norm_neg, coeff_one]; split_ifs <;> simp
end Formalism.ELL.PadicLogarithmSubstitution
