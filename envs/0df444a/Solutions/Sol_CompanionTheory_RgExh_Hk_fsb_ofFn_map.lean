-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_ofFn_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:04:28.328802+00:00
-- url     : https://prove2.me/submissions/02830752-cd7e-446b-b440-d94af29841a7

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
theorem _root_.solution (f : V →ₗ[ℂ] W) : ∀ (t : ℕ) (g : Fin t → Module.End ℂ V) (g' : Fin t → Module.End ℂ W),
    (∀ k v, f (g k v) = g' k (f v)) → ∀ v, f ((List.ofFn g).prod v) = (List.ofFn g').prod (f v) := by
  intro t
  induction t with
  | zero => intro g g' _ v; simp
  | succ t ih =>
    intro g g' hg v
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, hg,
      ih (fun i => g i.succ) (fun i => g' i.succ) (fun k w => hg k.succ w), List.ofFn_succ, List.prod_cons,
      Module.End.mul_apply]
end CompanionTheory.RgExh.Hk
