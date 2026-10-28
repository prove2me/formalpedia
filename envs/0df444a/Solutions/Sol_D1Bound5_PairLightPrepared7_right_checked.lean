-- Prove2me | solution 1 for D1Bound5.PairLightPrepared7.right_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:32:08.709484+00:00
-- url     : https://prove2.me/submissions/3e5b327e-0525-46d0-9a4e-3b0d8bbb4858

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
import Mathlib.Data.List.Basic
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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightVertices_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared7_rightVertices_eq
import Theorems.Thm_D1Bound5_PairLightPrepared7_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightPrepared7_right_independent_checked
import Theorems.Thm_D1Bound5_PairLightPrepared7_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared7_sieve_eq
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem right_certificate_checked :
    pairLightSelectedFloorIndependentCertificateBool 0 1 sieve
      rightVertices rightCached rightRows = true := by
  unfold pairLightSelectedFloorIndependentCertificateBool
  exact Bool.and_eq_true_iff.mpr ⟨right_coverage_checked,
    Bool.and_eq_true_iff.mpr ⟨right_signatures_checked, right_independent_checked⟩⟩

end D1Bound5.PairLightPrepared7
end

section
namespace D1Bound5.PairLightPrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0













theorem rightCached_eq :
    rightCached = PairSelectedPrepared7.rightCached.map pairLightCachedCoordinates := by
  rfl

theorem rightRows_eq : rightRows = PairSelectedPrepared7.rightRows := by
  rfl

theorem _root_.solution :
    pairIndependentBool smallPairSieve_0_1 (pairSplitByMask smallPairLarge_7 PairGraphPrepared7.colors).2 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_0_1
    (pairSplitByMask smallPairLarge_7 PairGraphPrepared7.colors).2 PairSelectedPrepared7.rightCached PairSelectedPrepared7.rightRows
  rw [← sieve_eq, ← rightVertices_eq, ← rightCached_eq, ← rightRows_eq]
  exact right_certificate_checked

end D1Bound5.PairLightPrepared7
end
