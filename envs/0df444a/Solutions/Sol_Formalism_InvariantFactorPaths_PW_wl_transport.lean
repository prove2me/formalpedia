-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wl_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:58.934616+00:00
-- url     : https://prove2.me/submissions/6b354791-f27c-4abd-bdb1-644cd46f410e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_ker_le
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_range_Lv
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_tr_E
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable


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
theorem _root_.solution (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin n → ℤ}
    {h h' : V} (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    ∃ θ : G.gS {h} →ₗ[K] V, (∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x)) ∧
      (∀ y, θ y ∈ G.gS {h'}) ∧ ∀ m ∈ G.gS {h'}, ∃ y, θ y = m := by
  have hk := GlX.ker_le G hW hWf hh hh' hhW hh'W h0
  refine ⟨GlX.tr G hk ∘ₗ (LinearEquiv.ofEq _ _ (GlX.range_Lv G h).symm).toLinearMap, fun a b x => ?_, fun y => ?_,
    fun m hm => ?_⟩
  · exact GlX.tr_E G hk a b (LinearEquiv.ofEq _ _ (GlX.range_Lv G h).symm x) _
  · rw [← GlX.range_Lv]
    exact GlX.tr_mem G hk _
  · rw [← GlX.range_Lv] at hm
    obtain ⟨c, rfl⟩ := hm
    refine ⟨⟨GlX.Lv G h c, by rw [← GlX.range_Lv]; exact LinearMap.mem_range_self _ c⟩, ?_⟩
    exact GlX.tr_apply G hk c
end Formalism.InvariantFactorPaths.PW
