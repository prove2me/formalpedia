-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.qdet_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:23.074728+00:00
-- url     : https://prove2.me/submissions/ab24698e-717e-460d-a606-15206af71d60

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
theorem _root_.solution (hS : ScalChar X χ) (u : ℂ) :
    qdet X.E u = capP χ (u - cn (m + 1)) • (1 : Module.End ℂ X.V) := by
  have := hS (u - cn (m + 1))
  have e : u - cn (m + 1) + ((↑(m + 1) : ℂ) - 1) / 2 = u := by rw [cn]; ring
  rwa [e] at this
end CompanionTheory.RgExh.Hk.UnitPf
