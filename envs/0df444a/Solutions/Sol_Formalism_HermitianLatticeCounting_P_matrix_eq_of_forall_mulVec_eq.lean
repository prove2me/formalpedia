-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.matrix_eq_of_forall_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:37.656369+00:00
-- url     : https://prove2.me/submissions/cfa6187e-db77-480d-9db8-54b836f98d6b

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simpa only [Matrix.toLin'_apply] using h x
end Formalism.HermitianLatticeCounting.P
