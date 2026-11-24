-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.finite_hits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:56.233578+00:00
-- url     : https://prove2.me/submissions/e9455829-0acc-4dd3-a45a-f1d1d0f49372

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
theorem _root_.solution (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (x : H) :
    {γ : Γ | (γ : H) * x ∈ K}.Finite := by
  have hK' : IsCompact ((fun y => y * x⁻¹) '' K) := hK.image (continuous_mul_const x⁻¹)
  have h1 := (Γ.tendsto_coe_cofinite_of_discrete (isDiscrete_iff_discreteTopology.mpr inferInstance))
    hK'.compl_mem_cocompact
  refine (Filter.mem_cofinite.1 h1).subset ?_
  intro γ hγ
  simp only [Set.mem_compl_iff, Set.mem_preimage, not_not]
  exact ⟨(γ : H) * x, hγ, by simp⟩
end Formalism.L2.SG.CovariantRepresentation
