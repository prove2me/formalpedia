-- Prove2me | solution 1 for FockRaiseLowGrade.sum_hc_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:58.682096+00:00
-- url     : https://prove2.me/submissions/1514f879-c4ef-454a-b78f-12cb812c62f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowGrade
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowGrade
theorem _root_.solution (P : MvPolynomial σ ℂ) (n : ℕ) (hn : P.totalDegree < n) :
    ∑ i ∈ Finset.range n, homogeneousComponent i P = P := by
  have hsub : Finset.range (P.totalDegree + 1) ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  rw [← Finset.sum_subset hsub ?_]
  · exact sum_homogeneousComponent P
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    apply homogeneousComponent_eq_zero
    omega
end FockRaiseLowGrade
