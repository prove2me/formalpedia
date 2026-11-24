-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_det_map_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:45.004921+00:00
-- url     : https://prove2.me/submissions/0b2235d0-4596-493d-b74e-1f9134e15d81

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (A.map star).det = star A.det := by
  have := (starRingEnd ℂ).map_det A
  rw [show star A.det = (starRingEnd ℂ) A.det from rfl, this]
  rfl
end Formalism.HermitianLatticeCounting.P
