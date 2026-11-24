-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_blockAct_blockEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:56.393692+00:00
-- url     : https://prove2.me/submissions/3ab241a8-f5d4-4c21-ae26-9b07581ea369

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BlockActTensor
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_blockAct_comp

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
theorem _root_.solution (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) := by
  exact AlgHom.congr_fun (ldtensor_blockAct_comp K g s) F
end Formalism.GradedWeylDivisibility
