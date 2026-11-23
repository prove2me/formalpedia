-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.one_le_lcount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:46.053071+00:00
-- url     : https://prove2.me/submissions/832e0828-1dd5-4cd4-9585-69ef305b9c7d

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
theorem _root_.solution (Γ : Subgroup H) {K : Set H} (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (x : H) :
    1 ≤ lcount Γ K x := by
  obtain ⟨s, hs, hsx⟩ := hcov x
  calc (1 : ℝ≥0∞) = K.indicator 1 (((⟨s, hs⟩ : Γ) : H) * x) := by simp [hsx]
    _ ≤ lcount Γ K x := ENNReal.le_tsum (f := fun γ : Γ => K.indicator 1 ((γ : H) * x)) _
end Formalism.L2.SG.CovariantRepresentation
