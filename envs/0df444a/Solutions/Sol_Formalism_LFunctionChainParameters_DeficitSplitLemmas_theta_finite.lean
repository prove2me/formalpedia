-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.theta_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:51.428948+00:00
-- url     : https://prove2.me/submissions/418387c3-f774-414a-b477-605ed056891a

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma

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
theorem _root_.solution : ThetaFin := by
  intro Y s hY hs
  have hsub : s ⊆ Nat.primesLE ⌊Y⌋₊ := by
    intro p hp; rw [Nat.mem_primesLE]; exact ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
  calc ∑ p ∈ s, Real.log p ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
    _ = Chebyshev.theta (⌊Y⌋₊ : ℝ) := (Chebyshev.theta_eq_sum_primesLE_log _).symm
    _ ≤ Real.log 4 * (⌊Y⌋₊ : ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
    _ ≤ Real.log 4 * Y :=
        mul_le_mul_of_nonneg_left (Nat.floor_le hY) (Real.log_nonneg (by norm_num))
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
