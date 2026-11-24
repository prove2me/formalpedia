-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.tsum_lwt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:37:43.276891+00:00
-- url     : https://prove2.me/submissions/fd122dfa-895c-4135-9c68-603b0eb9f932

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_lcount_ne_top
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_one_le_lcount
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_lcount_mul

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
theorem _root_.solution (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K)
    (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (x : H) : ∑' γ : Γ, lwt Γ K ((γ : H) * x) = 1 := by
  unfold lwt
  simp_rw [lcount_mul]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_inv_cancel (zero_lt_one.trans_le (one_le_lcount Γ hcov x)).ne' (lcount_ne_top Γ hK x)
end Formalism.L2.SG.CovariantRepresentation
