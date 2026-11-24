-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.cross_terms_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:30.777357+00:00
-- url     : https://prove2.me/submissions/ffdc4b81-1f5a-49c6-901c-116a6cd95167

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
theorem _root_.solution : CrossTermsVanish := by
  intro M N Q _ _ _ Φ hadd hneg x y
  have z : cob Φ ((0 : M), (0 : N)) (0, y) = 0 := by
    have := hadd ((0 : M), (0 : N)) (0, 0) (0, y); simpa using this
  have h1 : cob Φ (x, 0) (0, y) + cob Φ (-x, 0) (0, y) = 0 := by
    rw [← hadd]; simpa using z
  have h2 : cob Φ (-x, 0) (0, y) = cob Φ (x, 0) (0, y) := by
    unfold cob; simp [hneg]
  rw [h2] at h1; exact h1
end Formalism.HermitianLattices.ModelCocycles
