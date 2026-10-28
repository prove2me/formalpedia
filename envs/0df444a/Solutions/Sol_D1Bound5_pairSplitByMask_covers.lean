-- Prove2me | solution 1 for D1Bound5.pairSplitByMask_covers
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:05.841169+00:00
-- url     : https://prove2.me/submissions/b8dbe0cc-0942-4414-81c7-0730a152915d

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
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions

section
namespace D1Bound5
open QuadInt



theorem _root_.solution {α : Type*} (vertices : List α) (colors : ℕ)
    (z : α) (hz : z ∈ vertices) :
    z ∈ (pairSplitByMask vertices colors).1 ∨
      z ∈ (pairSplitByMask vertices colors).2 := by
  induction vertices generalizing colors with
  | nil => cases hz
  | cons x xs ih =>
      rcases List.mem_cons.mp hz with he | ht
      · subst z
        cases hb : colors.testBit 0 <;> simp [pairSplitByMask, hb]
      · rcases ih (colors / 2) ht with hl | hr
        · cases hb : colors.testBit 0 <;> simp [pairSplitByMask, hb, hl]
        · cases hb : colors.testBit 0 <;> simp [pairSplitByMask, hb, hr]









end D1Bound5
end
