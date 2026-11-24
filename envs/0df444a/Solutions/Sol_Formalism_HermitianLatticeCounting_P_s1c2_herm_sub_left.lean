-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:46.122228+00:00
-- url     : https://prove2.me/submissions/8ac5dece-8f6c-45db-8dbc-6f3d57026eaa

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hL_apply

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
theorem _root_.solution {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    herm H (u - v) w = herm H u w - herm H v w := by
  simp only [← s1c2_hL_apply, map_sub, LinearMap.sub_apply]
end Formalism.HermitianLatticeCounting.P
