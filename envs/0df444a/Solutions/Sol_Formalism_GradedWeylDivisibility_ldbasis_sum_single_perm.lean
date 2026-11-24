-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldbasis_sum_single_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:13.188142+00:00
-- url     : https://prove2.me/submissions/82d7196f-62fd-4df5-a682-013ae48b9d88

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r s : ℕ} (I : Fin s → Fin r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (I (σ q)) 1 : Fin r → ℕ)) = ∑ p : Fin s, Pi.single (I p) 1 := by
  exact Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))
end Formalism.GradedWeylDivisibility
