-- Prove2me | solution 1 for D1Bound5.pairCachedIndependentBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:45.801993+00:00
-- url     : https://prove2.me/submissions/df11fb88-addc-4f2b-b153-638b9ad70fff

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
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_pairCachedCoordinateSieveBool_signatures

section
namespace D1Bound5

















/-- Validated signatures give precisely the original fast square predicate. -/
theorem pairCachedHasSquareRoot_eq {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (x y : PairResidueVertex tau nu)
    (hx : x.signature = pairCoordinateSignature sieve x.vertex)
    (hy : y.signature = pairCoordinateSignature sieve y.vertex) :
    pairCachedHasSquareRoot sieve x y = hasSquareRootFast sieve (x.vertex * y.vertex + 1) := by
  unfold pairCachedHasSquareRoot
  rw [hx, hy, pairCachedCoordinateSieveBool_signatures] <;> rfl



theorem _root_.solution {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (cached : List (PairResidueVertex tau nu))
    (hvalid : ∀ x ∈ cached, x.signature = pairCoordinateSignature sieve x.vertex)
    (hcheck : pairCachedIndependentBool sieve cached = true) :
    pairIndependentBool sieve (cached.map PairResidueVertex.vertex) = true := by
  revert hvalid hcheck
  induction cached with
  | nil =>
      intro hvalid hcheck
      rfl
  | cons x xs ih =>
      intro hvalid hcheck
      have hx := hvalid x (by simp)
      have htail : ∀ y ∈ xs, y.signature = pairCoordinateSignature sieve y.vertex := by
        intro y hy
        exact hvalid y (List.mem_cons.mpr (Or.inr hy))
      have hparts := Bool.and_eq_true_iff.mp hcheck
      change
        ((xs.map PairResidueVertex.vertex).all (fun y =>
          if decide (x.vertex = y) then true else !(hasSquareRootFast sieve (x.vertex * y + 1))) &&
          pairIndependentBool sieve (xs.map PairResidueVertex.vertex)) = true
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply List.all_eq_true.mpr
        intro y hy
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
        have hrow := List.all_eq_true.mp hparts.1 w hw
        have heq := pairCachedHasSquareRoot_eq sieve x w hx (htail w hw)
        simpa only [heq] using hrow
      · exact ih htail hparts.2





end D1Bound5
end
