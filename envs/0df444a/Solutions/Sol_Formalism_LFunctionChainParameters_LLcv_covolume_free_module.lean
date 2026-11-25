-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.covolume_free_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:44.491825+00:00
-- url     : https://prove2.me/submissions/a31dad3b-5b32-4ba4-b032-c52628f41cd5

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_log_covolume_slope_mu
import Theorems.Thm_Formalism_HN_HeightGram_rkK_span
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ne_bot_of_rkK_pos


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
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution : LcvFree := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e he hj
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hfin0 : lcvFin e (Submodule.span (𝓞 K) (Set.range e)) = 0 := by
    unfold lcvFin
    have : ∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI := p.2.isPrime;
        lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) (Submodule.span (𝓞 K) (Set.range e))) = 0 := by
      intro p
      unfold lidx
      rw [sub_self]
    simp only [this, Int.cast_zero, mul_zero, finsum_zero]
  have hrk := HeightGram.rkK_span (K := K) e he
  have h0 : Submodule.span (𝓞 K) (Set.range e) ≠ ⊥ := ne_bot_of_rkK_pos (by rw [hrk]; exact hj)
  obtain ⟨-, -, -, -, h1⟩ := log_covolume_slope_mu K V ι b X hX j e _ he
    (Submodule.fg_span (Set.finite_range e)) h0 (Submodule.span_span_of_tower _ _ _)
  refine ⟨hfin0, ?_⟩
  rw [h1, hrk, lcv, hfin0, add_zero]
end Formalism.LFunctionChainParameters.LLcv
