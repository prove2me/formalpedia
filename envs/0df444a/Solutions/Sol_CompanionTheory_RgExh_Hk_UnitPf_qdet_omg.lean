-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.qdet_omg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:47.295815+00:00
-- url     : https://prove2.me/submissions/27a4ca33-3a85-4fbc-b568-713ccd10aa82

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_qdet_scal
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_capelliPoly_root

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
theorem _root_.solution (hS : ScalChar X χ) : qdet X.E (omg χ s) = 0 := by
  rw [qdet_scal hS, omg, show cn (m + 1) - χ s - cn (m + 1) = -χ s by ring, capelliPoly_root, zero_smul]
end CompanionTheory.RgExh.Hk.UnitPf
