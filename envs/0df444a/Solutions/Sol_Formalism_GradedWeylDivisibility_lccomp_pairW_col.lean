-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lccomp_pairW_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:34.508318+00:00
-- url     : https://prove2.me/submissions/cb946b85-859f-48da-a5a3-b91893031ebd

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas

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
theorem _root_.solution {r n : ℕ} (l j : Fin n) (b : Fin r) :
    pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by
  unfold pairW
  split_ifs <;> rfl
end Formalism.GradedWeylDivisibility
