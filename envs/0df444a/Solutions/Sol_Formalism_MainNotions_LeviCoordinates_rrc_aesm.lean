-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_aesm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:40.925202+00:00
-- url     : https://prove2.me/submissions/cfc1d878-9f01-44fd-a5f5-f7c5186fdbc1

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
  [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace H] [Group G]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) (v u : H) :
    AEStronglyMeasurable (fun g => ⟪π g v, u⟫_ℂ) μ := by
  have h := Complex.continuous_conj.comp_aestronglyMeasurable (hm u v)
  refine h.congr (Eventually.of_forall fun g => ?_)
  exact inner_conj_symm _ _
end Formalism.MainNotions.LeviCoordinates
