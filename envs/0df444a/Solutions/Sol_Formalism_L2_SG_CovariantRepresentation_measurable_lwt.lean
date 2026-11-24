-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.measurable_lwt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:04.890833+00:00
-- url     : https://prove2.me/submissions/e0a3ae86-b12c-4549-a393-12e890f5981d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_measurable_lcount

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
    Measurable (lwt Γ K) :=
  ((measurable_one : Measurable (1 : H → ℝ≥0∞)).indicator hK.measurableSet).mul (measurable_lcount Γ hK).inv
end Formalism.L2.SG.CovariantRepresentation
