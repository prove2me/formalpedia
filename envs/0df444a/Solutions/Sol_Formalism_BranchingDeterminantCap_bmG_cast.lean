-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:22.74588+00:00
-- url     : https://prove2.me/submissions/93fa209c-9ea0-4e52-8fe7-9ce0ed3f66c3

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {lam b lam' b' : Fin n → ℕ}
    {f f' : MvPolynomial (Fin n × Fin n) R} {G G' : BP R n} (h : bmLift R n lam b f G)
    (h1 : lam = lam') (h2 : b = b') (h3 : f = f') (h4 : G = G') : bmLift R n lam' b' f' G' := by
  subst h1 h2 h3 h4
  exact h
end Formalism.BranchingDeterminantCap
