-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.ph_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:00.757287+00:00
-- url     : https://prove2.me/submissions/057bfe3e-8658-4f46-ad0d-3688eb6864c7

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_temperate_quad
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_const
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_GlobalTheory_Published_Metaplectic_eChar_apply
import Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) :
    ph S f x = exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) * f x := by
  have h2 : Function.HasTemperateGrowth fun x : Eu l => (-2⁻¹ : ℝ) * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) := by
    convert GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h2 using 1
    funext x
    simp only [Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [ph, smulLeftCLM_apply_apply h3, smul_eq_mul]
end CompanionTheory.ThKR.LL
