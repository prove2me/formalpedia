-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:05.305495+00:00
-- url     : https://prove2.me/submissions/aded168b-0fc6-4d2f-8c71-99a3053ca445

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_bvec_right
import Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec_lo


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
theorem _root_.solution (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) x (bvec (eI k r a)) = x (esI k r a) := by
  unfold bvec
  rw [ggHerm_bvec_right, gn_Hpk_mulVec_lo k r x _ a.isLt]
  rfl
end Formalism.HermitianLatticeCounting.P
