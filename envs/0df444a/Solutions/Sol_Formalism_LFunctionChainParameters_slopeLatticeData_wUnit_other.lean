-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.wUnit_other
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:24.905797+00:00
-- url     : https://prove2.me/submissions/ce24a389-0dc7-4da5-a898-24f8f7b11e9d

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_coe_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_halfUnit_of_le_one

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
variable {K : Type} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (w w' : FinPl K) (h : w' ≠ w) : WUnit w.1 (w'.1 : FI) := by
  have := w.2.isPrime
  have h0 := finPl_coe_ne_zero w'
  refine ⟨h0, halfUnit_of_le_one w.1 FractionalIdeal.coeIdeal_le_one, ?_⟩
  have hnle : ¬ w'.1 ≤ w.1 := fun hle => h (Subtype.ext (w'.2.eq_of_le w.2.ne_top hle))
  obtain ⟨t, htw', htw⟩ := SetLike.not_le_iff_exists.1 hnle
  refine ⟨t, htw, fun x hx => ?_⟩
  have hmem : algebraMap (𝓞 K) K t * x ∈ (w'.1 : FI) * (w'.1 : FI)⁻¹ :=
    FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨t, htw', rfl⟩) hx
  rw [mul_inv_cancel₀ h0] at hmem
  exact (FractionalIdeal.mem_one_iff _).1 hmem
end Formalism.LFunctionChainParameters.slopeLatticeData
