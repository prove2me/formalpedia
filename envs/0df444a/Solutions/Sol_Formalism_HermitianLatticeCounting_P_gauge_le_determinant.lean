-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gauge_le_determinant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:21.554493+00:00
-- url     : https://prove2.me/submissions/f95d4786-3621-4d8e-b72b-d27602eb98c2

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
theorem _root_.solution : GfLeD := by
  intro k r z z' g hT hT'
  unfold Gf
  rw [Complex.normSq_eq_norm_sq]
  have := mul_nonneg (mul_nonneg hT hT') (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))
  linarith
end Formalism.HermitianLatticeCounting.P
