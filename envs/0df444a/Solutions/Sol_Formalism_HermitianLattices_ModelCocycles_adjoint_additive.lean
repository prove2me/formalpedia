-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.adjoint_additive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:29.581365+00:00
-- url     : https://prove2.me/submissions/db73ca63-f628-4071-8c9f-ae190c438103

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : AdjointAdd := by
  intro O M Q _ _ _ _ _ φ hadd α α' h h' a b
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  rw [add_smul, hadd, h, h', star_add, add_smul, symm a (_ + _), hadd, symm a, symm a]
end Formalism.HermitianLattices.ModelCocycles
