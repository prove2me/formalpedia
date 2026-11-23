-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:53.214505+00:00
-- url     : https://prove2.me/submissions/8c7141d3-d5ec-4002-80e5-8ead99c9b165

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_smul_comm_integers_field
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
theorem _root_.solution (c : K) (L : Submodule (𝓞 K) V) :
    idealSmul ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L = L.map (lsm c) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 (FractionalIdeal.mem_coe.1 ha)
    refine ⟨r • x, Submodule.smul_mem _ r hx, ?_⟩
    show c • (r • x) = (r • c) • x
    rw [smul_assoc, smul_comm_integers_field]
  · rintro _ ⟨x, hx, rfl⟩
    show c • x ∈ _
    exact mem_idealSmul (FractionalIdeal.mem_coe.2 (FractionalIdeal.mem_spanSingleton_self _ c)) hx
end Formalism.LFunctionChainParameters.slopeLatticeData
