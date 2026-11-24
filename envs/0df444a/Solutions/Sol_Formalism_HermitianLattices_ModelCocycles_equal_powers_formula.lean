-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.equal_powers_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:57.165932+00:00
-- url     : https://prove2.me/submissions/db7287ce-1dc6-4cae-996f-126520220a4b

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
theorem _root_.solution : EqualPowers := by
  intro R _ _ _ σ N f g hN hf hg h
  have hc := (Commute.all f g).mul_geom_sum₂ N
  rw [h, sub_self] at hc
  rcases mul_eq_zero.1 hc with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have := congrArg MvPowerSeries.constantCoeff h1
    simp [map_sum, hf, hg] at this
    omega
end Formalism.HermitianLattices.ModelCocycles
