-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:45.92023+00:00
-- url     : https://prove2.me/submissions/8a5455a1-3c94-41de-a28a-8a29319aa2dd

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_bvec_right


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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    herm A (Pi.single j 1) (Pi.single i 1) = A i j := by
  rw [ggHerm_bvec_right]; simp
end Formalism.HermitianLatticeCounting.P
