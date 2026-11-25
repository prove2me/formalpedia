-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_qdet_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:08.881588+00:00
-- url     : https://prove2.me/submissions/96276cab-7a95-46c2-8335-75d7f9b0ea3f

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_ofFn_map

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
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hf : ∀ a b v, f (E a b v) = E' a b (f v)) (x : ℂ) (v : V) :
    f (qdet E x v) = qdet E' x (f v) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply,
    map_zsmul]
  congr 1
  refine fsb_ofFn_map f n _ _ (fun k w => ?_) v
  simp only [Formalism.REAL.Tm, LinearMap.add_apply, map_add, hf]
  split_ifs <;> simp
end CompanionTheory.RgExh.Hk
