-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:20.773785+00:00
-- url     : https://prove2.me/submissions/bcb6881c-13fc-4544-ba1b-04fac9d5180b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_stronglyMeasurable

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
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hiso : ∀ g x, ‖π g x‖ = ‖x‖) (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ)
    {f : G → ℂ} (hf : Integrable f μ) (v : H) : Integrable (fun g => f g • π g v) μ := by
  have hm : StronglyMeasurable fun g => π g v := rrd_stronglyMeasurable _ fun x => hmeas x v
  refine Integrable.mono' (hf.norm.mul_const ‖v‖) (hf.aestronglyMeasurable.smul hm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  exact le_of_eq (by rw [norm_smul, hiso])
end Formalism.MainNotions.LeviCoordinates
