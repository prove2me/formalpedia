-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.bideterminantMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:18.010332+00:00
-- url     : https://prove2.me/submissions/96e42ad3-8b07-4abd-a3f2-55dae3041373

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_initW_eq_shapeDeg
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_of_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem


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
theorem _root_.solution : BideterminantMem := by
  intro R _ r n K sz hsz I
  exact dualWeyl_of_eq
    (dualWeyl_prod Finset.univ (fun k => initW n (sz k))
      (fun k => initMinor R (I k) (hsz k))
      (fun k _ => initMinor_mem (I k) (hsz k)))
    (sum_initW_eq_shapeDeg sz)
end Formalism.GradedWeylDivisibility
