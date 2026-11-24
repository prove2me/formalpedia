-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:20.915561+00:00
-- url     : https://prove2.me/submissions/8657b792-67cb-4e7d-85a7-ccce22724f76

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
theorem _root_.solution {ι σ : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (s : Finset σ) (c : σ → ℂ) (a : σ → ι → ℂ)
    (x : ι → ℂ) : herm H x (∑ i ∈ s, c i • a i) = ∑ i ∈ s, star (c i) * herm H x (a i) := by
  simp only [← s1c2_hL_apply, map_sum, map_smulₛₗ, smul_eq_mul]; rfl
end Formalism.HermitianLatticeCounting.P
