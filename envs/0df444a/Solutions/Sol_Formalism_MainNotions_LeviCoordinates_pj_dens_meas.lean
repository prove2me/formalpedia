-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.pj_dens_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:36.275398+00:00
-- url     : https://prove2.me/submissions/7fbef38c-616a-4e54-9aa2-d6912c98b1fd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_PjDensUpper

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
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs]
  [InnerProductSpace ℂ Hs] (σ : G → (Hs →L[ℂ] Hs))
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ) (x y : Hs) :
    AEStronglyMeasurable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ := (hm x y).norm.pow 2
end Formalism.MainNotions.LeviCoordinates
