-- Prove2me | solution 1 for D1Bound5.pairClosure_of_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:48.536628+00:00
-- url     : https://prove2.me/submissions/3d25513f-9ced-4738-831f-2e194dad281f

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt





























theorem _root_.solution {tau nu : ℤ} (a b : QuadInt tau nu) (bound : ℤ)
    (vertices : List (QuadInt tau nu)) (hcheck : pairClosureBool a b bound vertices = true)
    {z w : QuadInt tau nu} (hz : z ∈ vertices)
    (hw : w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z)
    (hbound : w.norm ≤ bound) : w ∈ vertices := by
  have hc := List.all_eq_true.mp hcheck z hz
  simp only [Bool.and_eq_true] at hc
  rcases hw with rfl | rfl
  · simpa [hbound] using hc.1
  · simpa [hbound] using hc.2





end D1Bound5
end
