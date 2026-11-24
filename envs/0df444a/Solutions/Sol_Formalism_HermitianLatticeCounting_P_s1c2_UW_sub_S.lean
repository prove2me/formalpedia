-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_UW_sub_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:44.801854+00:00
-- url     : https://prove2.me/submissions/cdafb7b4-b714-422d-99cd-3833a960c511

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_one


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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one, (Matrix.mul_one h).symm⟩
end Formalism.HermitianLatticeCounting.P
