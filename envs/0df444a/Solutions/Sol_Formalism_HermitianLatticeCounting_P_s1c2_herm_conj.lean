-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:45.583462+00:00
-- url     : https://prove2.me/submissions/3a5d4b6e-c411-488d-8780-7321e671da3d

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
theorem _root_.solution {ι : Type*} [Fintype ι] (H g : Matrix ι ι ℂ) (v w : ι → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
  rw [herm, herm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
end Formalism.HermitianLatticeCounting.P
