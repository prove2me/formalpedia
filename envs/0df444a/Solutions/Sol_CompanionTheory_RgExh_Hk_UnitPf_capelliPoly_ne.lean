-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.capelliPoly_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:56.639593+00:00
-- url     : https://prove2.me/submissions/54718e45-c2cd-41f8-acc0-f29448814024

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne

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
open Formalism.QuantumDeterminants (capP)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor)
open CompanionTheory.RgExh
variable {m : ℕ} (X : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1))
variable {X χ s}
namespace CompanionTheory.RgExh.Hk.UnitPf
theorem _root_.solution (hfree : ∀ r, χ r ≠ χ s + 1) : capP χ (-χ s - 1) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun t _ => ?_
  intro h; exact hfree t (by linear_combination h)
end CompanionTheory.RgExh.Hk.UnitPf
