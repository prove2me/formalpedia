-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.lwt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:59.498912+00:00
-- url     : https://prove2.me/submissions/c9cced81-a29a-4841-b2b5-c00402f9f9be

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_one_le_lcount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
namespace Formalism.L2.SG.CovariantRepresentation
theorem _root_.solution (Γ : Subgroup H) {K : Set H} (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (x : H) :
    lwt Γ K x ≤ K.indicator 1 x :=
  mul_le_of_le_one_right (by positivity) (ENNReal.inv_le_one.2 (one_le_lcount Γ hcov x))
end Formalism.L2.SG.CovariantRepresentation
