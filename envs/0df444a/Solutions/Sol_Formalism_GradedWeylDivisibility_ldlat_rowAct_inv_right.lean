-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldlat_rowAct_inv_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:20.513583+00:00
-- url     : https://prove2.me/submissions/ff474534-88e8-4ebd-aad1-354d0c3806e2

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_rowAct_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g⁻¹ (rowAct K g x) = x := by
  rw [← AlgHom.comp_apply, h K k n g⁻¹ g, Matrix.mul_nonsing_inv g hg, ldlat_rowAct_one, AlgHom.id_apply]
end Formalism.GradedWeylDivisibility
