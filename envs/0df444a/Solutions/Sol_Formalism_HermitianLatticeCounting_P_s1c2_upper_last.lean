-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_upper_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:47.09354+00:00
-- url     : https://prove2.me/submissions/27036563-57bb-4103-ad7c-357f502efd7b

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
theorem _root_.solution {r : ℕ} (a : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (ha : IsUpperUnitriangular a) (b : Fin (r + 1)) :
    a (Fin.last r) b = if b = Fin.last r then 1 else 0 := by
  split_ifs with h
  · rw [h]; exact ha.1 _
  · exact ha.2 _ _ (lt_of_le_of_ne (Fin.le_last b) h)
end Formalism.HermitianLatticeCounting.P
