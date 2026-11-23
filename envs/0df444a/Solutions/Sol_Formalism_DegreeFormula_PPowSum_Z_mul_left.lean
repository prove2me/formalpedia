-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.Z_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:19.853813+00:00
-- url     : https://prove2.me/submissions/cc24fdeb-9dbc-484a-bd7b-b3d47c8424e6

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {Q : MvPolynomial (ι × Fin N) ℝ}
    (hQ : ∀ P, degFl ι N (Q * P) = 0) (R : MvPolynomial (ι × Fin N) ℝ) :
    ∀ P, degFl ι N ((R * Q) * P) = 0 := by
  intro P
  rw [mul_comm R Q, mul_assoc]
  exact hQ _
end Formalism.DegreeFormula.PPowSum
