-- Prove2me | solution 1 for D1Bound5.pairLightIndexedCandidateCoveredBool_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:06.714747+00:00
-- url     : https://prove2.me/submissions/e6da4ca4-0bb9-4fad-a8fc-22ada39e1357

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_pairLightCoordinates_eq_iff

section
namespace D1Bound5



















theorem pairLightNorm_eq {tau nu : ℤ} (z : QuadInt tau nu) :
    pairLightNorm tau nu (pairLightCoordinates z) = z.norm := by
  simpa only [pairLightNorm, pairLightCoordinates] using (QuadInt.norm_formula z).symm





















end D1Bound5
end

section
namespace D1Bound5









/-- The identity holds for every list and supplied index, including malformed
indices and the strict outside-bound case. No certificate validity is assumed. -/
theorem _root_.solution {tau nu : ℤ} (bound : ℤ)
    (vertices : List (QuadInt tau nu)) (w : QuadInt tau nu)
    (destination : Option Nat) :
    pairLightIndexedCandidateCoveredBool tau nu bound
      (vertices.map pairLightCoordinates) (pairLightCoordinates w) destination =
      pairIndexedCandidateCoveredBool bound vertices w destination := by
  cases destination with
  | none =>
      simp only [pairLightIndexedCandidateCoveredBool, pairIndexedCandidateCoveredBool,
        pairLightNorm_eq]
  | some i =>
      simp only [pairLightIndexedCandidateCoveredBool, pairIndexedCandidateCoveredBool,
        List.getElem?_map]
      cases h : vertices[i]? with
      | none => rfl
      | some v =>
          simp only [Option.map_some, Option.some.injEq, pairLightCoordinates_eq_iff]





end D1Bound5
end
