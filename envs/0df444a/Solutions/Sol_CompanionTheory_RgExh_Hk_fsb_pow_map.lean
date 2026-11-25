-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_pow_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:03:34.843173+00:00
-- url     : https://prove2.me/submissions/708c62e5-36ab-416c-ae65-f454147a3fa0

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb

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
theorem _root_.solution (f : V →ₗ[ℂ] W) (T : Module.End ℂ V) (T' : Module.End ℂ W)
    (h : ∀ v, f (T v) = T' (f v)) : ∀ (k : ℕ) (v : V), f ((T ^ k) v) = (T' ^ k) (f v) := by
  intro k
  induction k with
  | zero => intro v; simp
  | succ k ih =>
    intro v
    rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]
end CompanionTheory.RgExh.Hk
