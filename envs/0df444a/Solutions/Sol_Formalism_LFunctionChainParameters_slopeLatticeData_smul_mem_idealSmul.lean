-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.smul_mem_idealSmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:53.050222+00:00
-- url     : https://prove2.me/submissions/d8b0d96d-db53-4586-bc2c-5939e952b469

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
theorem _root_.solution {I' J : Submodule (𝓞 K) K} {L : Submodule (𝓞 K) V} (a : K)
    (h : ∀ c ∈ J, a * c ∈ I') {y : V} (hy : y ∈ idealSmul J L) : a • y ∈ idealSmul I' L := by
  refine Submodule.span_induction (p := fun y _ => a • y ∈ idealSmul I' L) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨c, hc, x, hx, rfl⟩
    rw [smul_smul]
    exact mem_idealSmul (h c hc) hx
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [smul_add]; exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [← smul_comm_integers_field]; exact Submodule.smul_mem _ r hx
end Formalism.LFunctionChainParameters.slopeLatticeData
