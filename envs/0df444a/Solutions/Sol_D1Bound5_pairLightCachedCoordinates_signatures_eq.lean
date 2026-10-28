-- Prove2me | solution 1 for D1Bound5.pairLightCachedCoordinates_signatures_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:46.259143+00:00
-- url     : https://prove2.me/submissions/d73a9363-1d3e-47be-bd1e-314508c4e33f

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
import Theorems.Thm_D1Bound5_pairLight_intCast_val

section
namespace D1Bound5













theorem pairLightCoordinateResidues_eq {tau nu : ℤ} (k : ℕ) (z : QuadInt tau nu) :
    pairLightCoordinateResidues k (pairLightCoordinates z) = pairCoordinateResidues k z := by
  simp only [pairLightCoordinateResidues, pairLightCoordinates, pairCoordinateResidues,
    pairLight_intCast_val]

theorem pairLightCoordinateSignature_eq {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (z : QuadInt tau nu) :
    pairLightCoordinateSignature sieve (pairLightCoordinates z) =
      pairCoordinateSignature sieve z := by
  simp only [pairLightCoordinateSignature, pairCoordinateSignature,
    pairLightCoordinateResidues_eq]



















theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (cached : List (PairResidueVertex tau nu)) :
    ((cached.map pairLightCachedCoordinates).all fun x =>
      decide (x.2 = pairLightCoordinateSignature sieve x.1)) =
      (cached.all fun x => decide (x.signature = pairCoordinateSignature sieve x.vertex)) := by
  induction cached with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.all_cons, pairLightCachedCoordinates,
        pairLightCoordinateSignature_eq, ih]





end D1Bound5
end
