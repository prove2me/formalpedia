-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.degFl_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:18.060359+00:00
-- url     : https://prove2.me/submissions/5a090ac8-14d3-4703-bc0b-93c0dcbc6d51

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFl_add
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFl_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {α : Type*} (s : Finset α)
    (f : α → MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (∑ a ∈ s, f a) = ∑ a ∈ s, degFl ι N (f a) := by
  classical
  refine Finset.induction_on s (by simp [degFl_zero]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, degFl_add, ih]
end Formalism.DegreeFormula.PPowSum
