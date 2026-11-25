-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_aeval_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:31:22.499643+00:00
-- url     : https://prove2.me/submissions/74e30c09-603d-46cf-9cf3-89eb676053da

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_pow_map
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_omD_map
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_add


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
    (p : Polynomial ℂ) (g : Fin n → M1.V) :
    f.compLeft (Fin n) (Polynomial.aeval (omD M1) p g) = Polynomial.aeval (omD M2) p (f.compLeft (Fin n) g) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul,
      fsb_pow_map (f.compLeft (Fin n)) (omD M1) (omD M2) (fun v => fsb_omD_map M1 M2 f hf v) k g]
end CompanionTheory.RgExh.Hk
