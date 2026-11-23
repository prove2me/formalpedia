-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.mulSingle_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:56.667992+00:00
-- url     : https://prove2.me/submissions/d9886ad5-174c-4c8f-92ac-8ed4ef07959c

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
theorem _root_.solution {ι : Type} [DecidableEq ι] {N : ℕ} (τ : ι) (s : Equiv.Perm (Fin N))
    (σ : ι → Equiv.Perm (Fin N)) (t : ι) (i : Fin N) :
    ((Pi.mulSingle τ s * σ : ι → Equiv.Perm (Fin N)) t) i = if t = τ then s (σ τ i) else σ t i := by
  rw [Pi.mul_apply]
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same, Equiv.Perm.mul_apply]
  · rw [Pi.mulSingle_eq_of_ne h, one_mul]
end Formalism.DegreeFormula.PPowSum
