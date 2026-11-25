-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.capelliPoly_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:52:30.212215+00:00
-- url     : https://prove2.me/submissions/70714037-8a66-4d44-a342-d2be1652a940

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
theorem _root_.solution : capP χ (-(χ s)) = 0 :=
  Finset.prod_eq_zero (mem_univ s) (by ring)
end CompanionTheory.RgExh.Hk.UnitPf
