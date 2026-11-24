-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.prime_log_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:20.08314+00:00
-- url     : https://prove2.me/submissions/cd11226f-73b5-4ee4-8b8a-9848b02620ef

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LogFactorialBounds_sum_primesLE_log_div_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
theorem _root_.solution : PrimeLogSum := by
  intro Y s hY hs
  have hN : 1 ≤ ⌊Y⌋₊ := (Nat.one_le_floor_iff Y).mpr hY
  have hsub : s ⊆ Nat.primesLE ⌊Y⌋₊ := by
    intro p hp; rw [Nat.mem_primesLE]; exact ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
  calc ∑ p ∈ s, Real.log p / p ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    _ ≤ Real.log ⌊Y⌋₊ + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hN
    _ ≤ Real.log Y + Real.log 4 := by
        have : Real.log (⌊Y⌋₊ : ℝ) ≤ Real.log Y :=
          Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))
        linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
