-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:41.584446+00:00
-- url     : https://prove2.me/submissions/e10cd6ee-adf0-400a-b9e0-e4fdd19e8555

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
theorem _root_.solution (hn : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (a b : H) : ⟪π g a, π g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(π g : H →ₗ[ℂ] H), hn g⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
end Formalism.MainNotions.LeviCoordinates
