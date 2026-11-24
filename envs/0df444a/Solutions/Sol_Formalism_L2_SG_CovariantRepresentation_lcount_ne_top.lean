-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.lcount_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:03.445449+00:00
-- url     : https://prove2.me/submissions/15f20ddf-0ae6-4594-b76b-441a0fd0ccf1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_finite_hits

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
theorem _root_.solution (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (x : H) :
    lcount Γ K x ≠ ∞ := by
  have hs := finite_hits Γ hK x
  unfold lcount
  rw [tsum_eq_sum (s := hs.toFinset) ?_]
  · exact ENNReal.sum_ne_top.2 fun γ _ => by
      by_cases h : (γ : H) * x ∈ K <;> simp [Set.indicator, h]
  · intro γ hγ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
    simp [Set.indicator, hγ]
end Formalism.L2.SG.CovariantRepresentation
