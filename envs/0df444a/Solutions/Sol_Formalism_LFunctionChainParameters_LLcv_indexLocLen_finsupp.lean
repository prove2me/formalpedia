-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.indexLocLen_finsupp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:05:30.723692+00:00
-- url     : https://prove2.me/submissions/3b57820d-e515-4d3e-8f89-32e4237b647f

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_card_pLen

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
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module (𝓞 K) V] (A B : Submodule (𝓞 K) V) (hBA : B ≤ A)
    (h : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ k : {p : Ideal (𝓞 K) // p.IsMaximal} →₀ ℕ,
      (∀ w : {p : Ideal (𝓞 K) // p.IsMaximal},
        (haveI := w.2.isPrime; pLen w.1 A B) = (k w : ℕ∞)) ∧
      Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ∑ w ∈ k.support, Real.log (Ideal.absNorm w.1 : ℝ) * (k w : ℝ) := by
  obtain ⟨k, hk, hc⟩ := card_pLen _ A B hBA rfl h
  refine ⟨k, hk, ?_⟩
  rw [hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Real.log_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply, mul_comm]
  · intro w hw h0
    apply h
    rw [hc, Finsupp.prod]
    exact Finset.prod_eq_zero hw (by exact_mod_cast h0)
end Formalism.LFunctionChainParameters.LLcv
