-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.equiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:23.832318+00:00
-- url     : https://prove2.me/submissions/9c4e9a29-427e-4fcb-b2b3-067a82e83834

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G : GlW K V n) (h : V) (ψ : G.gS {h} →ₗ[K] V)
    (hψ : ∀ a b x, ψ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (ψ x))
    (h0 : ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0) : ψ = 0 := by
  have key : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker ψ) := by
    refine G.gS_le ?_ ?_
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact Submodule.mem_map.mpr ⟨⟨h, G.subset_gS _ (Set.mem_singleton h)⟩, LinearMap.mem_ker.mpr h0, rfl⟩
    · intro a b y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      refine Submodule.mem_map.mpr ⟨(res G _ (G.gS_stable {h})).E a b z, ?_, rfl⟩
      rw [LinearMap.mem_ker, hψ, LinearMap.mem_ker.mp hz, map_zero]
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp (key x.2)
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx', LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp hz
end Formalism.InvariantFactorPaths.PW
