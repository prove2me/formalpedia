-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.span_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:33.551505+00:00
-- url     : https://prove2.me/submissions/6c3cb8e9-5ddf-4c38-9f76-1c383e764213

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_span_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom


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
theorem _root_.solution {E M : Submodule (𝓞 K) V} (hE : E.FG)
    (h : Submodule.span K (E : Set V) = Submodule.span K (M : Set V)) :
    Submodule.span K ((E ⊓ M : Submodule (𝓞 K) V) : Set V) = Submodule.span K (E : Set V) := by
  have hEM : E ≤ locS (nonZeroDivisors (𝓞 K)) M := fun x hx =>
    span_le_locS M (h ▸ Submodule.subset_span hx)
  obtain ⟨d, hd, hdE⟩ := indexBasic_denom _ E M hE hEM
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  apply le_antisymm
  · exact Submodule.span_mono (fun x hx => hx.1)
  · refine Submodule.span_le.2 fun x hx => ?_
    have h1 : d • x ∈ (E ⊓ M : Submodule (𝓞 K) V) := ⟨E.smul_mem d hx, hdE x hx⟩
    have h2 : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
end Formalism.LFunctionChainParameters.LLcv
