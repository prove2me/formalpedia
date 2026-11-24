-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.nuclear_norm_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:23.393197+00:00
-- url     : https://prove2.me/submissions/232bcd91-8b51-42b5-a3ea-81cd455c905d

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_sum_sq_eigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset Matrix
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.D.NuclearBound := by
  intro N Y hY
  classical
  set μ := hY.eigenvalues
  have hrank : (Y.rank : ℝ) = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) ^ 2 := by
    rw [hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    simp only [ite_pow, one_pow, ne_eq, zero_pow two_ne_zero]
    rw [Finset.sum_boole]
  have hhs : Formalism.NuclearRankWeightBounds.D.hs Y = Real.sqrt (∑ j, |μ j| ^ 2) := by
    unfold Formalism.NuclearRankWeightBounds.D.hs
    rw [← sum_sq_eigenvalues Y hY]
    simp only [sq_abs]
    rfl
  have hsum : ∑ j, |μ j| = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) * |μ j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : μ j = 0 <;> simp [h]
  rw [hrank, hhs, hsum]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
end Formalism.NuclearRankWeightBounds.P
