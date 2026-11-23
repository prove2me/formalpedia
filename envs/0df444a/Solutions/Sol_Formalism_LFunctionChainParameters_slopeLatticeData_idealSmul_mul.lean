-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:49.018047+00:00
-- url     : https://prove2.me/submissions/92890efb-6e6c-48bb-b279-a96de2ab234a

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_mem_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_smul_mem_idealSmul

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (I J : Submodule (𝓞 K) K) (L : Submodule (𝓞 K) V) :
    idealSmul (I * J) L = idealSmul I (idealSmul J L) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨c, hc, x, hx, rfl⟩
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro a ha c hc
      rw [SetLike.mem_coe, mul_smul]
      exact mem_idealSmul ha (mem_idealSmul hc hx)
    · intro c d hc hd
      rw [SetLike.mem_coe] at hc hd ⊢
      rw [add_smul]; exact Submodule.add_mem _ hc hd
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, y, hy, rfl⟩
    exact smul_mem_idealSmul a (fun c hc => Submodule.mul_mem_mul ha hc) hy
end Formalism.LFunctionChainParameters.slopeLatticeData
