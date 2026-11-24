-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_inner_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:31:45.411959+00:00
-- url     : https://prove2.me/submissions/cccaf29c-4c6d-4ba8-a2ea-95ff989609a8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_int

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
    {f : G → ℂ} (hf : Integrable f μ) (u v : H) : ⟪u, rrd_vec μ π f v⟫_ℂ = ∫ g, f g * ⟪u, π g v⟫_ℂ ∂μ := by
  unfold rrd_vec
  rw [← integral_inner (rrd_int hiso hmeas hf v) u]
  congr 1
  funext g
  rw [inner_smul_right]
end Formalism.MainNotions.LeviCoordinates
