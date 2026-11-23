-- Prove2me | solution 1 for Formalism.ELL.N_padic_integer_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:17.913014+00:00
-- url     : https://prove2.me/submissions/ff930495-b38c-474b-ba68-696b8beb618d

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_integralMv_subst
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_log_subst_eq_smul
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_bser_constantCoeff
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_bser_deriv
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_integralPS_bser_sub_one

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
open Formalism.ELL
open PadicLogarithmSubstitution
namespace Formalism.ELL
theorem _root_.solution : Formalism.ELL.NZpSmul := by
  intro p _ K _ _ _ _ σ G hG b
  obtain ⟨f, hf0, hfi, rfl⟩ := hG
  have hB0 := bser_constantCoeff p K b
  have h0 : constantCoeff (bser p K b - 1) = 0 := by simp [hB0]
  have hS : HasSubst (bser p K b - 1) := HasSubst.of_constantCoeff_zero' h0
  have hf : HasSubst f := HasSubst.of_constantCoeff_zero hf0
  have hc : algebraMap ℚ_[p] K (b : ℚ_[p]) = phi p K b := rfl
  refine ⟨(bser p K b - 1).subst f, constantCoeff_subst_eq_zero hf0 _ h0,
    integralMv_subst (integralPS_bser_sub_one p K b) hf0 hfi, ?_⟩
  unfold logOnePlus
  rw [← subst_comp_subst_apply hS hf, log_subst_eq_smul _ _ hB0 (bser_deriv p K b),
    subst_smul hf, hc]
end Formalism.ELL
