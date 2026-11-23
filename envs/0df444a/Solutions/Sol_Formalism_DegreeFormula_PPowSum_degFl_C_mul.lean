-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.degFl_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:54.962908+00:00
-- url     : https://prove2.me/submissions/14bcffdc-f38f-4469-a28b-aa62ad05f690

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (c : ℝ) (P : MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (C c * P) = c * degFl ι N P := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring
end Formalism.DegreeFormula.PPowSum
