-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.character_power_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:22.179968+00:00
-- url     : https://prove2.me/submissions/591ef36f-32a2-4f9a-876d-afed6f3f3f7a

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
theorem _root_.solution : ChiPower := by
  intro E _ _ Ψ A _ ι K χ hK hχ t h z k hk ht
  have e : χ t ^ h = χ (ι z) := by rw [← map_pow, ht, map_mul, hK k hk, mul_one]
  rw [← hχ, ← e, Circle.coe_pow]
end Formalism.HermitianLattices.ModelCocycles
