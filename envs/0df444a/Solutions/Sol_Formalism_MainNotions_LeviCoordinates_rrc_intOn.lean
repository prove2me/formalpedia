-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_intOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:10.986895+00:00
-- url     : https://prove2.me/submissions/94939618-a616-4454-b05a-228a2e45d086

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_bound
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_aesm

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
  [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace H]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : μ k < ⊤) (v u : H) : IntegrableOn (fun g => ⟪π g v, u⟫_ℂ) k μ :=
  IntegrableOn.of_bound hk (rrc_aesm hm v u).restrict (‖v‖ * ‖u‖) (Eventually.of_forall fun g => rrc_bound hn g v u)
end Formalism.MainNotions.LeviCoordinates
