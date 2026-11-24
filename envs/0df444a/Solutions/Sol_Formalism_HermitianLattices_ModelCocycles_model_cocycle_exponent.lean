-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.model_cocycle_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:57.196427+00:00
-- url     : https://prove2.me/submissions/b6956baa-480b-4042-a18f-e51bf7bcf9b2

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
theorem _root_.solution : ModelCocycleExponent := by
  intro E V _ _ _ _ h s hadd hherm hs x y a b ha hb hxy
  have hadd2 : ∀ x y y', h x (y + y') = h x y + h x y' := by
    intro x y y'; rw [hherm, hadd, star_add, ← hherm, ← hherm]
  have hyx : h y x = (a - b * s) / 2 := by
    rw [hherm y x, hxy, star_div₀, star_add, star_mul', ha, hb, hs, star_ofNat]; ring
  rw [hadd, hadd2, hadd2, hxy, hyx]; ring
end Formalism.HermitianLattices.ModelCocycles
