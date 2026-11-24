-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.is_norm_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:49.726089+00:00
-- url     : https://prove2.me/submissions/52cf6afb-96f4-456b-8121-72c12961ccf0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : IsNormOneIff := by
  intro d N p
  have r1 : (1 : QuadraticAlgebra ℤ (-(((d + 1) / 4 : ℕ) : ℤ)) 1).re = 1 := rfl
  have i1 : (1 : QuadraticAlgebra ℤ (-(((d + 1) / 4 : ℕ) : ℤ)) 1).im = 0 := rfl
  constructor
  · rintro ⟨u, v, ⟨a, ha⟩, ⟨b, hb⟩, h⟩
    refine ⟨⟨u, v⟩, ⟨⟨a, b⟩, ?_⟩, ?_⟩
    · ext
      · simpa [r1] using ha
      · simpa [i1] using hb
    · rw [QuadraticAlgebra.norm_def, h]; ring
  · rintro ⟨π, ⟨w, hw⟩, h⟩
    have h1 := congrArg QuadraticAlgebra.re hw
    have h2 := congrArg QuadraticAlgebra.im hw
    refine ⟨π.re, π.im, ⟨w.re, by simpa [r1] using h1⟩, ⟨w.im, by simpa [i1] using h2⟩, ?_⟩
    rw [← h, QuadraticAlgebra.norm_def]; ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
