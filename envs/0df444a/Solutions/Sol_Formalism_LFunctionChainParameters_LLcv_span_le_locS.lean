-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.span_le_locS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:26.363716+00:00
-- url     : https://prove2.me/submissions/062f81c2-fa71-4d76-8fd4-4f26eb772090

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (Y : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (Y : Set V)) :
    x ∈ locS (nonZeroDivisors (𝓞 K)) Y := by
  let T : Submodule K V :=
    { carrier := locS (nonZeroDivisors (𝓞 K)) Y
      add_mem' := (locS (nonZeroDivisors (𝓞 K)) Y).add_mem
      zero_mem' := (locS (nonZeroDivisors (𝓞 K)) Y).zero_mem
      smul_mem' := by
        rintro c v ⟨d, hd, hdv⟩
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
        have hb0 : algebraMap (𝓞 K) K b ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        refine ⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩
        have hc : algebraMap (𝓞 K) K b * (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
            algebraMap (𝓞 K) K a := by
          field_simp
        have : (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • v) = a • (d • v) := by
          rw [mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul,
            smul_comm]
        rw [this]
        exact Y.smul_mem a hdv }
  have hle : Submodule.span K (Y : Set V) ≤ T :=
    Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)
  exact hle hx
end Formalism.LFunctionChainParameters.LLcv
