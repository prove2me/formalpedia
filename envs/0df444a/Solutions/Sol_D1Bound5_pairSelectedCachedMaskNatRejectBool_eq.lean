-- Prove2me | solution 1 for D1Bound5.pairSelectedCachedMaskNatRejectBool_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:12.412798+00:00
-- url     : https://prove2.me/submissions/038f711b-a30d-41f7-92f3-ecddcf9567da

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_PairResidueMaskNat_Definitions
import Definitions.Def_D1Bound5_PairSelectedCachedMask_Definitions
import Theorems.Thm_D1Bound5_pairResidueMaskNatBool_eq

section
namespace D1Bound5



theorem _root_.solution (tau nu : ℤ)
    (sieve : List (ℕ × ℕ)) (xs ys : List (ℕ × ℕ)) (i : ℕ) :
    pairSelectedCachedMaskNatRejectBool tau nu sieve xs ys i =
      pairSelectedCachedMaskRejectBool tau nu sieve xs ys i := by
  cases hm : sieve[i]? with
  | none =>
      simp only [pairSelectedCachedMaskNatRejectBool, pairSelectedCachedMaskRejectBool, hm]
  | some item =>
      rcases item with ⟨k, mask⟩
      cases hx : xs[i]? <;> cases hy : ys[i]? <;>
        simp only [pairSelectedCachedMaskNatRejectBool, pairSelectedCachedMaskRejectBool,
          hm, hx, hy, pairResidueMaskNatBool_eq]















end D1Bound5
end
