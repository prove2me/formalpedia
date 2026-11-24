-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.block_height_on_line_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:50.605386+00:00
-- url     : https://prove2.me/submissions/5a20bb13-e4b9-41eb-9d89-6b43301dd87c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_blockTriangular_of_mul_eq_pow_smul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : BlockHeightLine := by
  intro R _ _ π n h Φ Φ' b s hπ hΦ hm hs
  have hΦ' := blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm
  have h2 := congrFun (congrFun hm s) s
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  rw [← h2, Finset.sum_eq_single s]
  · intro j _ hj
    rcases lt_trichotomy (b j) (b s) with h3 | h3 | h3
    · rw [hΦ h3, zero_mul]
    · exact absurd (hs j h3) hj
    · rw [hΦ' h3, mul_zero]
  · intro hs'; exact absurd (Finset.mem_univ s) hs'
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
