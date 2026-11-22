-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_coeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:22.251186+00:00
-- url     : https://prove2.me/submissions/c422e8c0-9378-48a0-9ea3-9f64fdcc080c

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
theorem _root_.solution (J : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    idealSmul ((J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L = J • L := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 (FractionalIdeal.mem_coe.1 ha)
    rw [SetLike.mem_coe, algebraMap_smul]
    exact Submodule.smul_mem_smul hr hx
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    rw [← algebraMap_smul K r x]
    exact mem_idealSmul (FractionalIdeal.mem_coe.2 ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩)) hx
end Formalism.LFunctionChainParameters.slopeLatticeData
