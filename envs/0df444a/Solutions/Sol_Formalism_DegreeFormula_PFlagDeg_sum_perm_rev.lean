-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.sum_perm_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:02.601221+00:00
-- url     : https://prove2.me/submissions/1c022b7d-6483-4926-9253-1e86a0907e0a

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
namespace Formalism.DegreeFormula.PFlagDeg
theorem _root_.solution {N : ℕ} (s : Equiv.Perm (Fin N)) :
    ∑ i : Fin N, (N - 1 - ((s i : Fin N) : ℕ)) = ∑ i : Fin N, (i : ℕ) := by
  rw [Equiv.sum_comp s (fun j : Fin N => N - 1 - (j : ℕ))]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  omega
end Formalism.DegreeFormula.PFlagDeg
