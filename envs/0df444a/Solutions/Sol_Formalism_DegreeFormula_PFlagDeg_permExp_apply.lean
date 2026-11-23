-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.permExp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:01.790779+00:00
-- url     : https://prove2.me/submissions/6c3f93d7-fec6-4e7c-b304-4d16b704a3a5

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
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) (x : ι × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by
  simp [permExp]
end Formalism.DegreeFormula.PFlagDeg
