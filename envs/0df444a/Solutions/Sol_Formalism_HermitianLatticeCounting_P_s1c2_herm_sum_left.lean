-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:46.495972+00:00
-- url     : https://prove2.me/submissions/7e763064-2155-4152-acff-fd4dce0a5ca7

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
    (y : ι → ℂ) : herm H (∑ i ∈ s, c i • a i) y = ∑ i ∈ s, c i * herm H (a i) y := by
  simp only [← s1c2_hL_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
end Formalism.HermitianLatticeCounting.P
