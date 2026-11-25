-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.orthogonal_sum_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:27.820044+00:00
-- url     : https://prove2.me/submissions/fd6790ce-03f7-4e3b-b955-786e1361d4b9

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_degD_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open OrthogonalSumAlt
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : OrthSum := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ A hA horth
  obtain ⟨hfg, hrk, hdeg, hmu⟩ := main b X hX A hA horth Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset S), A i) = ⨆ i, A i := by simp
  rw [hu] at hfg hrk hdeg hmu
  refine ⟨hrk, ?_, ?_⟩
  · rw [degD_eq b X hX _ hfg, hdeg, hrk, Finset.mul_sum]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (degD_eq b X hX _ (hA i)).symm
  · intro c hc hne
    have h := hmu ((c + Real.log 2 - Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2)
      (fun i _ hi => by
        have := hc i hi
        unfold Formalism.HN.muMaxDef at this
        linarith) hne
    unfold Formalism.HN.muMaxDef
    linarith
end Formalism.BranchingDeterminantCap
