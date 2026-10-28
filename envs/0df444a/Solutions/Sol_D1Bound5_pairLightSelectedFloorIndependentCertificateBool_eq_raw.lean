-- Prove2me | solution 1 for D1Bound5.pairLightSelectedFloorIndependentCertificateBool_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:31.959447+00:00
-- url     : https://prove2.me/submissions/050c87af-8f5c-4637-8f89-1b3b82c4581a

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Theorems.Thm_D1Bound5_pairLightCachedCoordinates_signatures_eq
import Theorems.Thm_D1Bound5_pairLightCoordinates_eq_iff
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_eq_raw

section
namespace D1Bound5









theorem pairLightCoordinates_list_eq_iff {tau nu : ℤ}
    (xs ys : List (QuadInt tau nu)) :
    xs.map pairLightCoordinates = ys.map pairLightCoordinates ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp only [List.map_cons, List.cons.injEq,
          pairLightCoordinates_eq_iff, ih]























theorem pairLightCachedCoordinates_coverage_iff {tau nu : ℤ}
    (cached : List (PairResidueVertex tau nu)) (vertices : List (QuadInt tau nu)) :
    (cached.map pairLightCachedCoordinates).map Prod.fst = vertices.map pairLightCoordinates ↔
      cached.map PairResidueVertex.vertex = vertices := by
  have hmap : (cached.map pairLightCachedCoordinates).map Prod.fst =
      (cached.map PairResidueVertex.vertex).map pairLightCoordinates := by
    simp only [List.map_map, Function.comp_def, pairLightCachedCoordinates]
  rw [hmap, pairLightCoordinates_list_eq_iff]



/-- The complete arithmetic-only certificate is exactly the accepted raw
certificate for all parameters and all supplied lists. Ordered vertex coverage
and every canonical signature are preserved, including malformed data. -/
theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu))
    (cached : List (PairResidueVertex tau nu)) (rows : List (ℕ × List ℕ)) :
    pairLightSelectedFloorIndependentCertificateBool tau nu sieve
      (vertices.map pairLightCoordinates) (cached.map pairLightCachedCoordinates) rows =
      pairRawSelectedFloorIndependentCertificateBool sieve vertices cached rows := by
  simp only [pairLightSelectedFloorIndependentCertificateBool,
    pairRawSelectedFloorIndependentCertificateBool, pairLightCachedCoordinates_coverage_iff,
    pairLightCachedCoordinates_signatures_eq, pairLightSelectedFloorIndependentBool_eq_raw]



end D1Bound5
end
