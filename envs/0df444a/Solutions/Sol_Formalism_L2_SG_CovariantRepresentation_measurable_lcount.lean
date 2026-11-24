-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.measurable_lcount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:42.807493+00:00
-- url     : https://prove2.me/submissions/32eec6b7-6bae-41d0-81c8-8d96d6119846

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice

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
theorem _root_.solution (Γ : Subgroup H) [Countable Γ] {K : Set H} (hK : IsCompact K) :
    Measurable (lcount Γ K) :=
  Measurable.ennreal_tsum fun _ =>
    ((measurable_one : Measurable (1 : H → ℝ≥0∞)).indicator hK.measurableSet).comp (measurable_const_mul _)
end Formalism.L2.SG.CovariantRepresentation
