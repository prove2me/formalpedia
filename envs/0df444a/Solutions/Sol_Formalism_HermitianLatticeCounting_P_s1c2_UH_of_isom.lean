-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_UH_of_isom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:23.168539+00:00
-- url     : https://prove2.me/submissions/e0af6d82-3dd6-4148-b049-c310516b78a3

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_conj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_single

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (H p : Matrix ι ι ℂ)
    (h : ∀ x y, herm H (p *ᵥ x) (p *ᵥ y) = herm H x y) : p ∈ UH H := by
  have : pᴴ * H * p = H := by
    apply Matrix.ext
    intro i j
    rw [← s1c2_herm_single (pᴴ * H * p) i j, ← s1c2_herm_conj, h, s1c2_herm_single]
  exact this
end Formalism.HermitianLatticeCounting.P
