-- Prove2me | solution 1 for Formalism.L2.LamCM.coeff_mem_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:15.146811+00:00
-- url     : https://prove2.me/submissions/e41f659f-e755-4b19-b792-1d35e714b131

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61
import Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_pow__280537c55445
import Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_inv__6d6a889473de
import Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_prod__e9d1965a7d60
import Theorems.Thm_P2M_Formalism_L2_LamCM_mem_of_loc__5071d3ddd352


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : CoeffMemOfLoc := by
  intro K _ _ g ℓ de V _ c μ n cf hde hℓ hloc
  have hP0 : (∏ v, (ℓ (c v)).I ^ μ v) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hℓ (c v)).1
  have hI0 : (lineNN de ℓ c μ n).I ≠ 0 := by
    simp only [lineNN, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow]
    exact mul_ne_zero (pow_ne_zero _ hde.1) (inv_ne_zero hP0)
  apply mem_of_loc' K _ cf hI0
  intro p
  obtain ⟨t, cl, ht, hcl, hv⟩ := hloc p
  have hG : IsLocGen p (∏ v, cl (c v) ^ μ v) (∏ v, (ℓ (c v)).I ^ μ v) :=
    IsLocGen.prod' _ _ _ (fun v => (hcl (c v)).pow' (μ v)) (fun v => pow_ne_zero _ (hℓ (c v)).1)
  refine ⟨t ^ n * (∏ v, cl (c v) ^ μ v)⁻¹, ?_, ?_⟩
  · simp only [lineNN, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow]
    exact (ht.pow' n).mul' hG.inv' (pow_ne_zero _ hde.1) (inv_ne_zero hP0)
  · have hne : p.valuation K (∏ v, cl (c v) ^ μ v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hG.1
    rw [map_mul, map_inv₀]
    calc p.valuation K cf
        = p.valuation K (cf * ∏ v, cl (c v) ^ μ v) * (p.valuation K (∏ v, cl (c v) ^ μ v))⁻¹ := by
          rw [map_mul, mul_assoc, mul_inv_cancel₀ hne, mul_one]
      _ ≤ _ := by gcongr
end Formalism.L2.LamCM
