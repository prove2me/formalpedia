-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.second_term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:27.687315+00:00
-- url     : https://prove2.me/submissions/729b4d5f-ca64-4ba9-aac0-0cde8ef1cdaa

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : SecondLe := by
  intro Ps s cl Sg θ m T a hm hT ha hcl
  rw [← Finset.sum_filter, Finset.mul_sum]
  have hsub : Ps.filter (fun p => cl p = PClass.second) ⊆ s.filter (fun p => θ < Sg p) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact hcl p hp.1 hp.2
  calc ∑ p ∈ Ps.filter (fun p => cl p = PClass.second), 4 * m * T * a * (Real.log p / p)
      ≤ ∑ p ∈ s.filter (fun p => θ < Sg p), 4 * m * T * a * (Real.log p / p) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => ?_)
        have : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
        positivity
    _ = _ := Finset.sum_congr rfl (fun p _ => by ring)
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
