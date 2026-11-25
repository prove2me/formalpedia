-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.cont_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:46.878917+00:00
-- url     : https://prove2.me/submissions/b1a9d55e-aed5-4c43-aed2-f042f0fea535

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOneStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSumStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_cont_ofFn_prod
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_Tm_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet qminor Tm GlRel)
open CompanionTheory.RgExh
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.RgExh.Hk.UnitPf
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (ℓ : Module.Dual ℂ W) (f : W) :
    Continuous (fun u : ℂ => ℓ (qdet E u f)) := by
  simp only [qdet, qminor, LinearMap.sum_apply, map_sum]
  refine continuous_finsetSum _ fun σ _ => ?_
  simp only [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, Tm_affine]
  exact (cont_ofFn_prod ℓ n _ _ f).const_smul _
end CompanionTheory.RgExh.Hk.UnitPf
