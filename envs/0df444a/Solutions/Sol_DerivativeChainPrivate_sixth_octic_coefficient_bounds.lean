-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_coefficient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:18:27.356907+00:00
-- url     : https://prove2.me/submissions/99793206-dfcc-4d0b-b887-ffb1763830ff

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution :
    (38/1000:ℝ)<sixthOcticExpansionCoeffs 0 ∧ sixthOcticExpansionCoeffs 0<39/1000 ∧
      |sixthOcticRationalTailCoeff| ≤ 4213 ∧
      ∀ i : Fin 19, |sixthOcticExpansionCoeffs i| ≤ sixthOcticExpansionBounds i := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤429)
  have hp:=Real.sqrt_nonneg 429
  have hl : (5178078794301994783/250000000000000000:ℝ)≤Real.sqrt 429 := by nlinarith only [hs,hp]
  have hu : Real.sqrt 429≤(20712315177207979133/1000000000000000000:ℝ) := by nlinarith only [hs,hp]
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [sixthOcticExpansionCoeffs]; linarith only [hl,hu]
  · norm_num [sixthOcticExpansionCoeffs]; linarith only [hl,hu]
  · rw [abs_le]; dsimp [sixthOcticRationalTailCoeff]; constructor <;> linarith only [hl,hu]
  · intro i
    fin_cases i <;> norm_num [sixthOcticExpansionCoeffs,sixthOcticExpansionBounds,abs_le] <;>
      constructor <;> linarith only [hl,hu]
