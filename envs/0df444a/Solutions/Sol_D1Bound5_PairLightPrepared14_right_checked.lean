-- Prove2me | solution 1 for D1Bound5.PairLightPrepared14.right_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:14.790559+00:00
-- url     : https://prove2.me/submissions/d745f083-c8cf-48dd-8913-875fe1453b3f

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightVertices_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared14_rightVertices_eq
import Theorems.Thm_D1Bound5_PairLightPrepared14_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightPrepared14_right_independent_checked
import Theorems.Thm_D1Bound5_PairLightPrepared14_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared14_sieve_eq
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem right_certificate_checked :
    pairLightSelectedFloorIndependentCertificateBool 0 2 sieve
      rightVertices rightCached rightRows = true := by
  unfold pairLightSelectedFloorIndependentCertificateBool
  exact Bool.and_eq_true_iff.mpr ⟨right_coverage_checked,
    Bool.and_eq_true_iff.mpr ⟨right_signatures_checked, right_independent_checked⟩⟩

end D1Bound5.PairLightPrepared14
end

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0













theorem rightCached_eq :
    rightCached = PairSelectedPrepared14.rightCached.map pairLightCachedCoordinates := by
  rfl

theorem rightRows_eq : rightRows = PairSelectedPrepared14.rightRows := by
  rfl

theorem _root_.solution :
    pairIndependentBool smallPairSieve_0_2 (pairSplitByMask smallPairLarge_14 PairGraphPrepared14.colors).2 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_0_2
    (pairSplitByMask smallPairLarge_14 PairGraphPrepared14.colors).2 PairSelectedPrepared14.rightCached PairSelectedPrepared14.rightRows
  rw [← sieve_eq, ← rightVertices_eq, ← rightCached_eq, ← rightRows_eq]
  exact right_certificate_checked

end D1Bound5.PairLightPrepared14
end
