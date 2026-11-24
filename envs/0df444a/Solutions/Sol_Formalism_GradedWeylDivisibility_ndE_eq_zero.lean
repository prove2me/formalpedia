-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ndE_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:48.866705+00:00
-- url     : https://prove2.me/submissions/a641e6ba-1598-4774-88d1-46bb886a74e3

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEv_pderiv_colAddGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_pderiv_none_rename

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
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {l j : Fin n} {f : MvPolynomial (Fin r × Fin n) R}
    (h : colAddGen R l j f = rename some f) : ndE R r n l j f = 0 := by
  rw [← ndEv_pderiv_colAddGen, h, nd_pderiv_none_rename, map_zero]
end Formalism.GradedWeylDivisibility
