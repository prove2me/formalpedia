-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wl_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:51:03.947102+00:00
-- url     : https://prove2.me/submissions/b894270e-d192-4a64-b5cf-d36d6ebcdb5a

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_top_of_mem
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
theorem _root_.solution (G : GlW K V n) {la : Fin n → ℤ} {h : V} (hh : G.IsHW la h) (h0 : h ≠ 0)
    [FiniteDimensional K (G.gS {h})] :
    LinearMap.trace K _ ((res G _ (G.gS_stable {h})).comp la) = 1 := by
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have hp : LinearMap.IsProj (K ∙ (⟨h, hmem⟩ : G.gS {h})) ((res G _ (G.gS_stable {h})).comp la) := by
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · obtain ⟨c, hc⟩ := G.comp_top_of_mem hh x.2
      exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc.symm⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      congr 1
      exact Subtype.ext hh.1
  rw [hp.trace, finrank_span_singleton (fun e => h0 (congrArg Subtype.val e)), Nat.cast_one]
end Formalism.InvariantFactorPaths.PW
