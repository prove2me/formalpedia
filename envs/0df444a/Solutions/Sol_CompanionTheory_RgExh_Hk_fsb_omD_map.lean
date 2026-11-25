-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_omD_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:24:58.675845+00:00
-- url     : https://prove2.me/submissions/acfaa0c3-b6ce-43ca-95fc-14434229eb00

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_omD_apply

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
    (g : Fin n → M1.V) : f.compLeft (Fin n) (omD M1 g) = omD M2 (f.compLeft (Fin n) g) := by
  funext a
  simp only [LinearMap.compLeft_apply, Function.comp_apply, fsb_omD_apply, map_neg, map_sum, hf]
end CompanionTheory.RgExh.Hk
