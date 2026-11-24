-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.card_filter_rev_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:39.831904+00:00
-- url     : https://prove2.me/submissions/96b7019e-1fca-42c6-acea-e6378f11daa4

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution (k j : ℕ) (p : Fin (k + j) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b).card ≤ k := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b)
    (t := Finset.range k) (fun b => (Fin.rev b).val)
    (by
      intro b hb
      have := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr this))
    (by
      intro a _ b _ hab
      exact Fin.rev_injective (Fin.ext hab))
  simpa using h
end Formalism.CohomologicalDescent.UnitNormBounds
