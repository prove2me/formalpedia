-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrka_meas_Kab_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:59.57431+00:00
-- url     : https://prove2.me/submissions/a209389d-61f6-47e4-a101-d1c723cf6606

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hφm : Measurable φ) (x : G) : Measurable fun y => rrk_Kab Γ φ x y :=
  Measurable.tsum fun γ => (hφm.comp (measurable_const_mul (x⁻¹ * (γ : G)))).enorm
end Formalism.MainNotions.LeviCoordinates
