-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_hasChar_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:24.861985+00:00
-- url     : https://prove2.me/submissions/b4b0310a-c17d-45de-8d4b-3f7c46b53ece

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_pow_map
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_qdet_map
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_ext


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
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (hi : Function.Injective f) (χ : Fin n → ℂ) (h : HasChar M2 χ) : HasChar M1 χ := by
  have hT : ∀ (u c : ℂ) (w : M1.V), f ((Formalism.REAL.qdet M1.E u - c • (1 : Module.End ℂ M1.V)) w) =
      (Formalism.REAL.qdet M2.E u - c • (1 : Module.End ℂ M2.V)) (f w) := by
    intro u c w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_qdet_map f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  ext v
  apply hi
  rw [fsb_pow_map f _ _ (hT _ _) k v, hk Y]
  simp
end CompanionTheory.RgExh.Hk
