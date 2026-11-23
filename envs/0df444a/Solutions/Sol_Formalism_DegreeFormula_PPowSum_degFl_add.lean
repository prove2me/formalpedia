-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.degFl_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:44.690831+00:00
-- url     : https://prove2.me/submissions/6763528f-ef13-4cca-8b26-925afbbc5888

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (P Q : MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (P + Q) = degFl ι N P + degFl ι N Q := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]
end Formalism.DegreeFormula.PPowSum
