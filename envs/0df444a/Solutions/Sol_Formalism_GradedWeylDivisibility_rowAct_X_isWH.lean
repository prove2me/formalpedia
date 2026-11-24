-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowAct_X_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:02.479183+00:00
-- url     : https://prove2.me/submissions/e0f1bd27-e837-4a4f-ab29-9a23b72af76c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (v : Fin r × Fin n) : IsWeightedHomogeneous (colW r n) (rowAct R g (X v)) (colW r n v) := by
  simp only [rowAct, aeval_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
  convert (isWeightedHomogeneous_C (colW r n) (g v.1 b)).mul
    (isWeightedHomogeneous_X (R := R) (colW r n) (b, v.2)) using 1
  simp [colW]
end Formalism.GradedWeylDivisibility
