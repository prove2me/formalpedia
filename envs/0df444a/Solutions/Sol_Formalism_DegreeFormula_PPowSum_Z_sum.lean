-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.Z_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:13.714258+00:00
-- url     : https://prove2.me/submissions/c3840b32-1146-46a4-a8f2-6387cc5581d4

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFl_sum

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
    (g : α → MvPolynomial (ι × Fin N) ℝ) (h : ∀ a ∈ s, ∀ P, degFl ι N (g a * P) = 0) :
    ∀ P, degFl ι N ((∑ a ∈ s, g a) * P) = 0 := by
  intro P
  rw [Finset.sum_mul, degFl_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha P
end Formalism.DegreeFormula.PPowSum
