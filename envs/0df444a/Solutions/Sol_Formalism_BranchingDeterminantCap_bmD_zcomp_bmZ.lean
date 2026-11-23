-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmD_zcomp_bmZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:14.217154+00:00
-- url     : https://prove2.me/submissions/a41686af-d9f8-493b-8e1d-7a90ab94516d

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_zcomp_bmZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (l j : Fin n) (Y : BP R n) :
    zcomp R n β (bmZ R n l j Y) =
      bmZ R n l j (zcomp R n (β - (Pi.single l 1 - Pi.single j 1)) Y) := by
  have := bm_zcomp_bmZ R n (β - (Pi.single l 1 - Pi.single j 1)) l j Y
  rwa [sub_add_cancel] at this
end Formalism.BranchingDeterminantCap
