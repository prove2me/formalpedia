-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:39.626946+00:00
-- url     : https://prove2.me/submissions/b7b907af-bd14-489c-83f8-93bb5bcd45c2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec

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
open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}
omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace H]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hn : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (v u : H) : ‖⟪π g v, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ := by
  refine le_trans (norm_inner_le_norm _ _) ?_
  rw [hn]
end Formalism.MainNotions.LeviCoordinates
