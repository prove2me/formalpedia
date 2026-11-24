-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.orthogonality_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:13.087136+00:00
-- url     : https://prove2.me/submissions/d54573db-9ba5-48cd-b5c9-a7dc3b16b1bf

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DualVectorOrthogonal := by
  intro V _ _ h r y f' b
  have h1 : h (formalDeterminantVector h y f') (f' b) =
      ((Matrix.of fun a b => h (y a) (f' b)).adjugate * (Matrix.of fun a b => h (y a) (f' b))) (Fin.last r) b := by
    simp [formalDeterminantVector, Matrix.mul_apply, map_sum]
  rw [h1, Matrix.adjugate_mul]
  by_cases hb : b = Fin.last r
  · subst hb; simp
  · simp [hb, Ne.symm hb]
end Formalism.HermitianLatticeCounting.P
