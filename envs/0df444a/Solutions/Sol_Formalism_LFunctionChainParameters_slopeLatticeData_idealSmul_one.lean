-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:53.951067+00:00
-- url     : https://prove2.me/submissions/9936c682-0a3e-44f4-9041-9933c83d6b36

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_mem_idealSmul

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
theorem _root_.solution (L : Submodule (𝓞 K) V) : idealSmul 1 L = L := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
    rw [SetLike.mem_coe, algebraMap_smul]
    exact Submodule.smul_mem _ r hx
  · intro x hx
    have := mem_idealSmul (I := (1 : Submodule (𝓞 K) K)) (a := 1)
      (Submodule.mem_one.2 ⟨1, map_one _⟩) hx
    rwa [one_smul] at this
end Formalism.LFunctionChainParameters.slopeLatticeData
