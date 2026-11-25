-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cofactor_vector_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:45.46097+00:00
-- url     : https://prove2.me/submissions/0ac41a39-b8f1-4bc3-9de9-52cde2e7a9a1

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_cofactorVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CofactorVecDual := by
  intro R _ r Z
  refine ⟨fun b => ?_, (Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec R r Z).2⟩
  have := congrFun (congrFun (Matrix.mul_adjugate Z) b) (Fin.last r)
  rw [Matrix.mul_apply] at this
  rw [this]; simp [Matrix.one_apply]
end Formalism.HermitianLatticeCounting.P
