-- Prove2me | solution 1 for D1Bound5.pairIndependentBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:44:30.40625+00:00
-- url     : https://prove2.me/submissions/2a439006-f3fb-4766-8c8b-53693487cbbd

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

section
namespace D1Bound5
open QuadInt







theorem _root_.solution {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (hcheck : pairIndependentBool sieve vertices = true)
    (x y : QuadInt tau nu) (hx : x ∈ vertices) (hy : y ∈ vertices) (hxy : x ≠ y) :
    hasSquareRootFast sieve (x*y+1) = false := by
  induction vertices with
  | nil => cases hx
  | cons z zs ih =>
      have hh : (zs.all fun w => if decide (z = w) then true
          else !(hasSquareRootFast sieve (z*w+1))) = true ∧
          pairIndependentBool sieve zs = true := by
        simpa only [pairIndependentBool, Bool.and_eq_true] using hcheck
      rcases List.mem_cons.mp hx with hxz | hx
      · subst x
        have hy : y ∈ zs := (List.mem_cons.mp hy).resolve_left (Ne.symm hxy)
        have H := List.all_eq_true.mp hh.1 y hy
        simpa [hxy] using H
      · rcases List.mem_cons.mp hy with hyz | hy
        · subst y
          have H := List.all_eq_true.mp hh.1 x hx
          simpa [Ne.symm hxy, mul_comm] using H
        · exact ih hh.2 hx hy





end D1Bound5
end
