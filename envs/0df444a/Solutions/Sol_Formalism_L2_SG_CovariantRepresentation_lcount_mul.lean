-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.lcount_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:56.892948+00:00
-- url     : https://prove2.me/submissions/b4935644-d02b-44f3-aa1b-9b316c8008c0

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
theorem _root_.solution (Γ : Subgroup H) (K : Set H) (δ : Γ) (x : H) :
    lcount Γ K ((δ : H) * x) = lcount Γ K x := by
  unfold lcount
  have := (Equiv.mulRight δ).tsum_eq (fun γ : Γ => K.indicator (1 : H → ℝ≥0∞) ((γ : H) * x))
  simpa [mul_assoc] using this
end Formalism.L2.SG.CovariantRepresentation
