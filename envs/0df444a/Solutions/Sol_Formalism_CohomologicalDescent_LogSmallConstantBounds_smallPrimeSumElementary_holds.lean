-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.smallPrimeSumElementary_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:50.797356+00:00
-- url     : https://prove2.me/submissions/f4d4aabf-7970-4e66-8f23-8dac2dd480cb

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_subset_primesLe
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_thickTerm_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_eight_lt_lJ
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_lJ_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_mertensReciprocalElementary_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : SumCE := by
  intro P H G ι D hA τ hτ Q hQ
  have hb := b_pos' P
  have hL := G.L_ge
  have h8 := eight_lt_lJ H G
  obtain ⟨hlg1, hlg2⟩ := log_lJ_bounds H G
  have hmbL : 0 ≤ 2 * (P.m : ℝ) * P.b * P.L :=
    mul_nonneg (mul_nonneg (by positivity) hb.le) (by linarith)
  have hsub : Q ⊆ pr P.lJ := subset_primesLe (by linarith) hQ
  have s1 : ∑ l ∈ Q, (1 : ℝ) / (l : ℝ) ≤ ∑ p ∈ pr P.lJ, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have s2 := mertensReciprocalElementary_holds P.lJ (by linarith)
  have hsum : ∑ l ∈ Q, (1 : ℝ) / (l : ℝ) ≤ P.L := by linarith
  calc ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ)
      ≤ ∑ l ∈ Q, 2 * (P.m : ℝ) * P.b * P.L / (l : ℝ) :=
        Finset.sum_le_sum (fun l hl => thickTerm_holds P H G ι D hA τ hτ l (hQ l hl).1 (hQ l hl).2)
    _ = 2 * (P.m : ℝ) * P.b * P.L * ∑ l ∈ Q, (1 : ℝ) / (l : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
    _ ≤ 2 * (P.m : ℝ) * P.b * P.L * P.L := mul_le_mul_of_nonneg_left hsum hmbL
    _ = 2 * (P.m : ℝ) * P.b * P.L ^ 2 := by ring
end Formalism.CohomologicalDescent.LogSmallConstantBounds
