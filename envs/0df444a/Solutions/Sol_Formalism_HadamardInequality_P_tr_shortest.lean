-- Prove2me | solution 1 for Formalism.HadamardInequality.P.tr_shortest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:47.463427+00:00
-- url     : https://prove2.me/submissions/940de00d-1303-42b4-8b7b-396bbcc1d82a

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Submodule ℤ E) [hQ : DiscreteTopology Q] (hne : Q ≠ ⊥) :
    ∃ q ∈ Q, q ≠ 0 ∧ ∀ q' ∈ Q, q' ≠ 0 → ‖q‖ ≤ ‖q'‖ := by
  obtain ⟨q0, hq0, hq00⟩ := (Submodule.ne_bot_iff Q).1 hne
  have hcl : IsClosed (Q : Set E) := by
    rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete
  have hfin : (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hcl
  set S := (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)) \ {0} with hS
  have hSfin : S.Finite := hfin.sdiff
  have hq0S : q0 ∈ S := ⟨⟨by simp, hq0⟩, hq00⟩
  obtain ⟨q, hqS, hmin⟩ := Set.exists_min_image S (fun x => ‖x‖) hSfin ⟨q0, hq0S⟩
  refine ⟨q, hqS.1.2, hqS.2, fun q' hq' hq'0 => ?_⟩
  by_cases hle : ‖q'‖ ≤ ‖q0‖
  · exact hmin q' ⟨⟨by simpa using hle, hq'⟩, hq'0⟩
  · exact (hmin q0 hq0S).trans (le_of_lt (not_le.1 hle))
end Formalism.HadamardInequality.P
